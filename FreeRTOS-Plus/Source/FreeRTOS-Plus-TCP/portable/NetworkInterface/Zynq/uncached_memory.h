/*
 * uncached_memory.h
 *
 * This module will declare 1 MB of memory and switch off the caching for it.
 *
 * pucGetUncachedMemory( ulSize ) returns a trunc of this memory with a length
 * rounded up to a multiple of 4 KB
 *
 * ucIsCachedMemory( pucBuffer ) returns non-zero if a given pointer is NOT
 * within the range of the 1 MB non-cached memory.
 *
 */

#ifndef UNCACHEMEMORY_H

#define UNCACHEMEMORY_H

uint8_t * pucGetUncachedMemory( uint32_t ulSize );

uint8_t ucIsCachedMemory( const uint8_t * pucBuffer );

#endif /* UNCACHEMEMORY_H */
