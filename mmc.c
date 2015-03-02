/* mmc.c - mmap cache
**
** Copyright © 1998,2001,2014 by Jef Poskanzer <jef@mail.acme.com>.
** All rights reserved.
**
** Redistribution and use in source and binary forms, with or without
** modification, are permitted provided that the following conditions
** are met:
** 1. Redistributions of source code must retain the above copyright
**    notice, this list of conditions and the following disclaimer.
** 2. Redistributions in binary form must reproduce the above copyright
**    notice, this list of conditions and the following disclaimer in the
**    documentation and/or other materials provided with the distribution.
**
** THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
** ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
** IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
** ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
** FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
** DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
** OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
** HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
** LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
** OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
** SUCH DAMAGE.
*/

#include "config.h"

#include <sys/types.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <time.h>
#include <fcntl.h>
#include <syslog.h>
#include <errno.h>

#ifdef HAVE_MMAP
#include <sys/mman.h>
#endif /* HAVE_MMAP */

#include "mmc.h"
#include "libhttpd.h"

#include "sto/tm.h"
#include "sto/Hashtable.hh"

#ifndef HAVE_INT64T
typedef long long int64_t;
#endif


/* Defines. */
#ifndef DEFAULT_EXPIRE_AGE
#define DEFAULT_EXPIRE_AGE 600
#endif
#ifndef DESIRED_FREE_COUNT
#define DESIRED_FREE_COUNT 100
#endif
#ifndef DESIRED_MAX_MAPPED_FILES
#define DESIRED_MAX_MAPPED_FILES 2000
#endif
#ifndef DESIRED_MAX_MAPPED_BYTES
#define DESIRED_MAX_MAPPED_BYTES 1000000000
#endif
#ifndef INITIAL_HASH_SIZE
#define INITIAL_HASH_SIZE (1 << 10)
#endif

#ifndef MAX
#define MAX(a,b) ((a)>(b)?(a):(b))
#endif
#ifndef MIN
#define MIN(a,b) ((a)<(b)?(a):(b))
#endif


/* The Map struct. */
typedef struct MapStruct {
    ino_t ino;
    dev_t dev;
    off_t size;
    time_t ct;
    int refcount;
    time_t reftime;
    void* addr;
    unsigned int hash;
    int hash_idx;
    struct MapStruct* next;
    } Map;

struct MapKey {
  ino_t ino;
  dev_t dev;
  off_t size;
  time_t ct;
  MapKey(ino_t ino, dev_t dev, off_t size, time_t ct) : ino(ino), dev(dev), size(size), ct(ct) {}
  bool operator==(const MapKey& m2) const {
    return ino == m2.ino && dev == m2.dev && size == m2.size && ct == m2.ct;
  }
};

typedef struct {
  void *addr;
  int refcount;
  time_t reftime;
} MapVal;

/* Globals. */
static Map* maps = (Map*) 0;
static Map* free_maps = (Map*) 0;
static int alloc_count = 0, map_count = 0, free_count = 0;
static Map** hash_table = (Map**) 0;
static int hash_size;
static unsigned int hash_mask;
static time_t expire_age = DEFAULT_EXPIRE_AGE;
static off_t mapped_bytes = 0;

/* Forwards. */
static void panic( void );
static void really_unmap( const MapKey& key, const MapVal& val );
static unsigned int hash( ino_t ino, dev_t dev, off_t size, time_t ct );



class Hasher {
 public:
  size_t operator()(const MapKey& m) {
    return hash( m.ino, m.dev, m.size, m.ct );
  }
};
static Hashtable<MapKey, MapVal, INITIAL_HASH_SIZE, Hasher> hashtable;


void*
mmc_map( char* filename, struct stat* sbP, struct timeval* nowP )
    {
    time_t now;
    struct stat sb;
    Map* m;
    int fd;

    /* Stat the file, if necessary. */
    if ( sbP != (struct stat*) 0 )
        sb = *sbP;
    else
        {
        if ( stat( filename, &sb ) != 0 )
            {
            syslog( LOG_ERR, "stat - %m" );
            return (void*) 0;
            }
        }

    /* Get the current time, if necessary. */
    if ( nowP != (struct timeval*) 0 )
        now = nowP->tv_sec;
    else
        now = time( (time_t*) 0 );

    void *addr_ret = NULL;

    TM_BEGIN();
    auto key = MapKey(sb.st_ino, sb.st_dev, sb.st_size, sb.st_ctime);
    MapVal val;
    // we try inserting first for two (annoying) reasons:
    // *this way if the insert succeeds the rest of the transaction
    //  is guaranteed to also succeed (whereas doing a get first
    //  we can false conflict abort)
    // *we don't have a proper value to insert yet, but if insert
    //  succeeds then we'll have to mmap to get the proper value,
    //  so if we just do the insert now we again can ensure
    //  no aborts and do the mmap() without of leaking it from an abort
    if (!hashtable.transInsert(TM_ARG key, val)) {
      // ugh
      hashtable.transGet(TM_ARG key, val);
      // already have the mmap so increment refcount and we're done
      val.refcount++;
      val.reftime = now;
      hashtable.transUpdate(TM_ARG key, val);
      // TODO: this is kind of a funky workflow that wouldn't fit
      // nicely in an atomic{} block, for instance.
      // what sort of syntax could support this nicely??
      TM_ARG_ALONE.commit();
      return val.addr;
    }

    // didn't find it so need to actually mmap it
    val.refcount = 1;
    val.reftime = now;

    /* Avoid doing anything for zero-length files; some systems don't like
    ** to mmap them, other systems dislike mallocing zero bytes.
    */
    if (key.size == 0) {
      val.addr = (void*) 1; /* arbitrary non-NULL address */
      hashtable.transUpdate(TM_ARG key, val);
      TM_ARG_ALONE.commit();
      return val.addr;
    }

    size_t size_size = (size_t) key.size;        /* loses on files >2GB */
    
    /* Open the file. */
    fd = open( filename, O_RDONLY );
    if ( fd < 0 ) {
      syslog( LOG_ERR, "open - %m" );
      // TODO: similarly, no obvious way to do this nicely syntactically
      // (handling error conditions in a transaction)
      TM_ARG_ALONE.silent_abort();
      return (void*) 0;
    }

#ifdef HAVE_MMAP
    /* Map the file into memory. */
    val.addr = mmap( 0, size_size, PROT_READ, MAP_PRIVATE, fd, 0 );
    if ( val.addr == (void*) -1 && errno == ENOMEM ) {
      /* Ooo, out of address space.  Free all unreferenced maps
      ** and try again.
      */
      panic();
      val.addr = mmap( 0, size_size, PROT_READ, MAP_PRIVATE, fd, 0 );
    }
    if ( val.addr == (void*) -1 ) {
      syslog( LOG_ERR, "mmap - %m" );
      (void) close( fd );
      TM_ARG_ALONE.silent_abort();
      return (void*) 0;
    }
#else /* HAVE_MMAP */
    /* Read the file into memory. */
    val.addr = (void*) malloc( size_size );
    if ( val.addr == (void*) 0 ) {
      /* Ooo, out of memory.  Free all unreferenced maps
      ** and try again.
      */
      // TODO: we should really abort at this point, since panic() does transactions of its own...
      panic();
      val.addr = (void*) malloc( size_size );
    }
    if ( val.addr == (void*) 0 ) {
      syslog( LOG_ERR, "out of memory storing a file" );
      (void) close( fd );
      TM_ARG_ALONE.silent_abort();
      return (void*) 0;
    }
    if ( httpd_read_fully( fd, val.addr, size_size ) != size_size ) {
      syslog( LOG_ERR, "read - %m" );
      (void) close( fd );
      TM_ARG_ALONE.silent_abort();
      return (void*) 0;
    }
#endif /* HAVE_MMAP */
    (void) close( fd );

    // finally have our mmap, we can "update" the value in the hashtable
    hashtable.transUpdate(TM_ARG key, val);

    // need our mmap value to escape past transaction end
    addr_ret = val.addr;

    TM_END();

    /* Update the total byte count. */
    __sync_add_and_fetch(&mapped_bytes, sb.st_size);

    // update map count
    __sync_add_and_fetch(&map_count, 1);

    /* And return the address. */
    return addr_ret;
    }


void
mmc_unmap( void* addr, struct stat* sbP, struct timeval* nowP )
    {
    // we really don't want to iterate through the whole table so we
    // force passing the stat struct
    assert(sbP);
    MapKey key(sbP->st_ino, sbP->st_dev, sbP->st_size, sbP->st_ctime);
    MapVal val;
    TM_BEGIN();
    bool found = hashtable.transGet(TM_ARG key, val);
    if (!found) {
      syslog( LOG_ERR, "mmc_unmap failed to find entry!" );
      TM_ARG_ALONE.silent_abort();
      return;
    }
    if (val.refcount <= 0) {
      syslog( LOG_ERR, "mmc_unmap found zero or negative refcount!" );
      TM_ARG_ALONE.silent_abort();
      return;
    }
    val.refcount--;
    if ( nowP != (struct timeval*) 0 )
      val.reftime = nowP->tv_sec;
    else
      val.reftime = time( (time_t*) 0 );
    hashtable.transUpdate(TM_ARG key, val);
    TM_END();
    }


void
mmc_cleanup( struct timeval* nowP )
    {
    time_t now;

    /* Get the current time, if necessary. */
    if ( nowP != (struct timeval*) 0 )
        now = nowP->tv_sec;
    else
        now = time( (time_t*) 0 );

    /* Really unmap any unreferenced entries older than the age limit. */
    auto end = hashtable.end();
    for (auto it = hashtable.begin(); it != end; ++it) {
      auto pair = *it;
      MapKey key = pair.first;
      MapVal val = pair.second;
      // approximate
      if (val.refcount == 0 && now - val.reftime >= expire_age) {
        bool removed;
        TM_BEGIN();
        removed = false;
        if (hashtable.transGet(TM_ARG key, val)) {
          // make sure these conditions still hold
          if (val.refcount == 0 && now - val.reftime >= expire_age) {
            hashtable.transDelete(TM_ARG key);
            removed = true;
          }
        }
        TM_END();
        if (removed) {
          really_unmap(key, val);
        }
        // TODO: after commit this node might be deallocated, so
        // it's not really safe to just keep iterating from there...
      }
    }

    /* Adjust the age limit if there are too many bytes mapped, or
    ** too many or too few files mapped.
    */
    if ( mapped_bytes > DESIRED_MAX_MAPPED_BYTES )
        expire_age = MAX( ( expire_age * 2 ) / 3, DEFAULT_EXPIRE_AGE / 10 );
    else if ( map_count > DESIRED_MAX_MAPPED_FILES )
        expire_age = MAX( ( expire_age * 2 ) / 3, DEFAULT_EXPIRE_AGE / 10 );
    else if ( map_count < DESIRED_MAX_MAPPED_FILES / 2 )
        expire_age = MIN( ( expire_age * 5 ) / 4, DEFAULT_EXPIRE_AGE * 3 );

    }

static void
panic( void )
    {

    syslog( LOG_ERR, "mmc panic - freeing all unreferenced maps" );

    /* Really unmap all unreferenced entries. */
    auto end = hashtable.end();
    for (auto it = hashtable.begin(); it != end; ++it) {
      auto pair = *it;
      MapKey key = pair.first;
      MapVal val = pair.second;
      // approximate
      if (val.refcount == 0) {
        bool removed;
        TM_BEGIN();
        removed = false;
        if (hashtable.transGet(TM_ARG key, val)) {
          // make sure these conditions still hold
          if (val.refcount == 0) {
            hashtable.transDelete(TM_ARG key);
            removed = true;
          }
        }
        TM_END();
        if (removed) {
          really_unmap(key, val);
        }
        // TODO: after commit this node might be deallocated, so
        // it's not really safe to just keep iterating from there...
      }
    }

    }



static void
really_unmap( const MapKey& key, const MapVal& val )
    {

    if (!key.size)
      return;

#ifdef HAVE_MMAP
    if (munmap(val.addr, key.size) < 0)
      syslog(LOG_ERR, "munmap - %m");
#else
    free(val.addr);
#endif
    
    __sync_add_and_fetch(&mapped_bytes, key.size);

    }


void
mmc_term( void )
    {
      // no way to even destruct a global Hashtable
    }

static unsigned int
hash( ino_t ino, dev_t dev, off_t size, time_t ct )
{
  unsigned int h = 177573;

  h ^= ino;
  h += h << 5;
  h ^= dev;
  h += h << 5;
  h ^= size;
  h += h << 5;
  h ^= ct;

  return h & hash_mask;
}

/* Generate debugging statistics syslog message. */
void
mmc_logstats( long secs )
    {
    syslog(
        LOG_NOTICE, "  map cache - %d allocated, %d active (%lld bytes), %d free; hash size: %d; expire age: %ld",
        map_count/*alloc_count==map_count*/, map_count, (long long) mapped_bytes, free_count, hash_size,
        expire_age );
    if ( map_count + free_count != map_count )
        syslog( LOG_ERR, "map counts don't add up!" );
    }
