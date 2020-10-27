/* mem_track.h
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */


/* The memory tracker overrides the wolfSSL memory callback system and uses a
 * static to track the total, peak and currently allocated bytes.
 *
 * If you are already using the memory callbacks then enabling this will
 * override the memory callbacks and prevent your memory callbacks from
 * working. This assumes malloc() and free() are available. Feel free to
 * customize this for your needs.

 * The enable this feature define the following:
 * #define USE_WOLFSSL_MEMORY
 * #define WOLFSSL_TRACK_MEMORY
 *
 * On startup call:
 * InitMemoryTracker();
 *
 * When ready to dump the memory report call:
 * ShowMemoryTracker();
 *
 * Report example:
 * total   Allocs =       228
 * total   Bytes  =     93442
 * peak    Bytes  =      8840
 * current Bytes  =         0
 *
 *
 * You can also:
 * #define WOLFSSL_DEBUG_MEMORY
 *
 * To print every alloc/free along with the function and line number.
 * Example output:
 * Alloc: 0x7fa14a500010 -> 120 at wc_InitRng:496
 * Free: 0x7fa14a500010 -> 120 at wc_FreeRng:606
 */


#ifndef WOLFSSL_MEM_TRACK_H
#define WOLFSSL_MEM_TRACK_H

#if defined(USE_WOLFSSL_MEMORY) && !defined(WOLFSSL_STATIC_MEMORY)

    #include "wolfssl/wolfcrypt/logging.h"

    #if defined(WOLFSSL_TRACK_MEMORY)
        #define DO_MEM_STATS
        #if defined(__linux__) || defined(__MACH__)
            #define DO_MEM_LIST
        #endif
    #endif


    typedef struct memoryStats {
        long totalAllocs;     /* number of allocations */
        long totalDeallocs;   /* number of deallocations */
        long totalBytes;      /* total number of bytes allocated */
        long peakBytes;       /* concurrent max bytes */
        long currentBytes;    /* total current bytes in use */
    } memoryStats;

    typedef struct memHint {
        size_t thisSize;      /* size of this memory */

    #ifdef DO_MEM_LIST
        struct memHint* next;
        struct memHint* prev;
        #ifdef WOLFSSL_DEBUG_MEMORY
            const char* func;
            unsigned int line;
        #endif
    #endif
        void*  thisMemory;    /* actual memory for user */
    } memHint;

    typedef struct memoryTrack {
        union {
            memHint hint;
            byte    alignit[sizeof(memHint) + ((16-1) & ~(16-1))]; /* make sure we have strong alignment */
        } u;
    } memoryTrack;

#ifdef DO_MEM_LIST
    /* track allocations and report at end */
    typedef struct memoryList {
        memHint* head;
        memHint* tail;
        word32   count;
    } memoryList;
#endif

#if defined(WOLFSSL_TRACK_MEMORY)
    static memoryStats ourMemStats;

    #ifdef DO_MEM_LIST
        #include <pthread.h>
        static memoryList ourMemList;
        static pthread_mutex_t memLock = PTHREAD_MUTEX_INITIALIZER;
    #endif
#endif


    /* if defined to not using inline then declare function prototypes */
    #ifdef NO_INLINE
        #define WC_STATIC
		#ifdef WOLFSSL_DEBUG_MEMORY
			WOLFSSL_LOCAL void* TrackMalloc(size_t sz, const char* func, unsigned int line);
			WOLFSSL_LOCAL void TrackFree(void* ptr, const char* func, unsigned int line);
			WOLFSSL_LOCAL void* TrackRealloc(void* ptr, size_t sz, const char* func, unsigned int line);
		#else
			WOLFSSL_LOCAL void* TrackMalloc(size_t sz);
			WOLFSSL_LOCAL void TrackFree(void* ptr);
			WOLFSSL_LOCAL void* TrackRealloc(void* ptr, size_t sz);
		#endif
        WOLFSSL_LOCAL int InitMemoryTracker(void);
        WOLFSSL_LOCAL void ShowMemoryTracker(void);
    #else
        #define WC_STATIC static
    #endif

#ifdef WOLFSSL_DEBUG_MEMORY
    WC_STATIC WC_INLINE void* TrackMalloc(size_t sz, const char* func, unsigned int line)
#else
    WC_STATIC WC_INLINE void* TrackMalloc(size_t sz)
#endif
    {
        memoryTrack* mt;
        memHint* header;

        if (sz == 0)
            return NULL;

        mt = (memoryTrack*)malloc(sizeof(memoryTrack) + sz);
        if (mt == NULL)
            return NULL;

        header = &mt->u.hint;
        header->thisSize   = sz;
        header->thisMemory = (byte*)mt + sizeof(memoryTrack);

    #ifdef WOLFSSL_DEBUG_MEMORY
    #ifdef WOLFSSL_DEBUG_MEMORY_PRINT
        printf("Alloc: %p -> %u at %s:%d\n", header->thisMemory, (word32)sz, func, line);
    #else
        (void)func;
        (void)line;
    #endif
    #endif

    #ifdef DO_MEM_STATS
        ourMemStats.totalAllocs++;
        ourMemStats.totalBytes   += sz;
        ourMemStats.currentBytes += sz;
        if (ourMemStats.currentBytes > ourMemStats.peakBytes)
            ourMemStats.peakBytes = ourMemStats.currentBytes;
    #endif
    #ifdef DO_MEM_LIST
        if (pthread_mutex_lock(&memLock) == 0) {
        #ifdef WOLFSSL_DEBUG_MEMORY
            header->func = func;
            header->line = line;
        #endif

            /* Setup event */
            header->next = NULL;
            if (ourMemList.tail == NULL)  {
                ourMemList.head = header;
                header->prev = NULL;
            }
            else {
                ourMemList.tail->next = header;
                header->prev = ourMemList.tail;
            }
            ourMemList.tail = header;      /* add to the end either way */
            ourMemList.count++;

            pthread_mutex_unlock(&memLock);
        }
    #endif

        return header->thisMemory;
    }


#ifdef WOLFSSL_DEBUG_MEMORY
    WC_STATIC WC_INLINE void TrackFree(void* ptr, const char* func, unsigned int line)
#else
    WC_STATIC WC_INLINE void TrackFree(void* ptr)
#endif
    {
        memoryTrack* mt;
        memHint* header;
        size_t sz;

        if (ptr == NULL) {
            return;
        }

        mt = (memoryTrack*)((byte*)ptr - sizeof(memoryTrack));
        header = &mt->u.hint;
        sz = header->thisSize;

    #ifdef DO_MEM_LIST
        if (pthread_mutex_lock(&memLock) == 0) 
        {
    #endif

    #ifdef DO_MEM_STATS
            ourMemStats.currentBytes -= header->thisSize;
            ourMemStats.totalDeallocs++;
    #endif

    #ifdef DO_MEM_LIST
            if (header == ourMemList.head && header == ourMemList.tail) {
                ourMemList.head = NULL;
                ourMemList.tail = NULL;
            }
            else if (header == ourMemList.head) {
                ourMemList.head = header->next;
                ourMemList.head->prev = NULL;
            }
            else if (header == ourMemList.tail) {
                ourMemList.tail = header->prev;
                ourMemList.tail->next = NULL;
            }
            else {
                memHint* next = header->next;
                memHint* prev = header->prev;
                if (next)
                    next->prev = prev;
                if (prev)
                    prev->next = next;
            }
            ourMemList.count--;

            pthread_mutex_unlock(&memLock);
        }
    #endif

#ifdef WOLFSSL_DEBUG_MEMORY
#ifdef WOLFSSL_DEBUG_MEMORY_PRINT
        printf("Free: %p -> %u at %s:%d\n", ptr, (word32)sz, func, line);
#else
        (void)func;
        (void)line;
#endif
#endif
        (void)sz;

        free(mt);
    }


#ifdef WOLFSSL_DEBUG_MEMORY
    WC_STATIC WC_INLINE void* TrackRealloc(void* ptr, size_t sz, const char* func, unsigned int line)
#else
    WC_STATIC WC_INLINE void* TrackRealloc(void* ptr, size_t sz)
#endif
    {
    #ifdef WOLFSSL_DEBUG_MEMORY
        void* ret = TrackMalloc(sz, func, line);
    #else
        void* ret = TrackMalloc(sz);
    #endif

        if (ptr) {
            /* if realloc is bigger, don't overread old ptr */
            memoryTrack* mt;
            memHint* header;

            mt = (memoryTrack*)((byte*)ptr - sizeof(memoryTrack));
            header = &mt->u.hint;

            if (header->thisSize < sz)
                sz = header->thisSize;
        }

        if (ret && ptr)
            XMEMCPY(ret, ptr, sz);

        if (ret) {
        #ifdef WOLFSSL_DEBUG_MEMORY
            TrackFree(ptr, func, line);
        #else
            TrackFree(ptr);
        #endif
        }

        return ret;
    }

#ifdef WOLFSSL_TRACK_MEMORY
    static wolfSSL_Malloc_cb mfDefault = NULL;
    static wolfSSL_Free_cb ffDefault = NULL;
    static wolfSSL_Realloc_cb rfDefault = NULL;

    WC_STATIC WC_INLINE int InitMemoryTracker(void)
    {
        int ret;

        ret = wolfSSL_GetAllocators(&mfDefault, &ffDefault, &rfDefault);
        if (ret < 0) {
            printf("wolfSSL GetAllocators failed to get the defaults\n");
        }
        ret = wolfSSL_SetAllocators(TrackMalloc, TrackFree, TrackRealloc);
        if (ret < 0) {
            printf("wolfSSL SetAllocators failed for track memory\n");
            return ret;
        }

    #ifdef DO_MEM_LIST
        if (pthread_mutex_lock(&memLock) == 0)
        {
    #endif

    #ifdef DO_MEM_STATS
        ourMemStats.totalAllocs  = 0;
        ourMemStats.totalDeallocs = 0;
        ourMemStats.totalBytes   = 0;
        ourMemStats.peakBytes    = 0;
        ourMemStats.currentBytes = 0;
    #endif
    
    #ifdef DO_MEM_LIST
        XMEMSET(&ourMemList, 0, sizeof(ourMemList));

        pthread_mutex_unlock(&memLock);
        }
    #endif

        return ret;
    }

    WC_STATIC WC_INLINE void ShowMemoryTracker(void)
    {
    #ifdef DO_MEM_LIST
        if (pthread_mutex_lock(&memLock) == 0)
        {
    #endif

    #ifdef DO_MEM_STATS
        printf("total   Allocs   = %9ld\n", ourMemStats.totalAllocs);
        printf("total   Deallocs = %9ld\n", ourMemStats.totalDeallocs);
        printf("total   Bytes    = %9ld\n", ourMemStats.totalBytes);
        printf("peak    Bytes    = %9ld\n", ourMemStats.peakBytes);
        printf("current Bytes    = %9ld\n", ourMemStats.currentBytes);
    #endif

    #ifdef DO_MEM_LIST
        if (ourMemList.count > 0) {
            /* print list of allocations */
            memHint* header;
            for (header = ourMemList.head; header != NULL; header = header->next) {
                printf("Leak: Ptr %p, Size %u"
                #ifdef WOLFSSL_DEBUG_MEMORY
                    ", Func %s, Line %d"
                #endif
                    "\n",
                    (byte*)header + sizeof(memHint), (unsigned int)header->thisSize
                #ifdef WOLFSSL_DEBUG_MEMORY
                    , header->func, header->line
                #endif
                );
            }
        }

        pthread_mutex_unlock(&memLock);
        }
    #endif
    }

    WC_STATIC WC_INLINE int CleanupMemoryTracker(void)
    {
        /* restore default allocators */
        return wolfSSL_SetAllocators(mfDefault, ffDefault, rfDefault);
    }
#endif

#endif /* USE_WOLFSSL_MEMORY */

#endif /* WOLFSSL_MEM_TRACK_H */

