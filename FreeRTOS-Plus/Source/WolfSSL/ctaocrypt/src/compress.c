/* compress.c
 *
 * Copyright (C) 2006-2014 wolfSSL Inc.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <cyassl/ctaocrypt/settings.h>

#ifdef HAVE_LIBZ


#include <cyassl/ctaocrypt/compress.h>
#include <cyassl/ctaocrypt/error-crypt.h>
#include <cyassl/ctaocrypt/logging.h>
#ifdef NO_INLINE
    #include <cyassl/ctaocrypt/misc.h>
#else
    #include <ctaocrypt/src/misc.c>
#endif

#include <zlib.h>


/* alloc user allocs to work with zlib */
static void* myAlloc(void* opaque, unsigned int item, unsigned int size)
{
    (void)opaque;
    return XMALLOC(item * size, opaque, DYNAMIC_TYPE_LIBZ);
}


static void myFree(void* opaque, void* memory)
{
    (void)opaque;
    XFREE(memory, opaque, DYNAMIC_TYPE_LIBZ);
}


#ifdef HAVE_MCAPI
    #define DEFLATE_DEFAULT_WINDOWBITS  11
    #define DEFLATE_DEFAULT_MEMLEVEL     1
#else
    #define DEFLATE_DEFAULT_WINDOWBITS 15
    #define DEFLATE_DEFAULT_MEMLEVEL    8
#endif


int Compress(byte* out, word32 outSz, const byte* in, word32 inSz, word32 flags)
/*
 * out - pointer to destination buffer
 * outSz - size of destination buffer
 * in - pointer to source buffer to compress
 * inSz - size of source to compress
 * flags - flags to control how compress operates 
 *
 * return:
 *    negative - error code
 *    positive - bytes stored in out buffer
 * 
 * Note, the output buffer still needs to be larger than the input buffer.
 * The right chunk of data won't compress at all, and the lookup table will
 * add to the size of the output. The libz code says the compressed
 * buffer should be srcSz + 0.1% + 12.
 */
{
    z_stream stream;
    int result = 0;

    stream.next_in = (Bytef*)in;
    stream.avail_in = (uInt)inSz;
#ifdef MAXSEG_64K
    /* Check for source > 64K on 16-bit machine: */
    if ((uLong)stream.avail_in != inSz) return COMPRESS_INIT_E;
#endif
    stream.next_out = out;
    stream.avail_out = (uInt)outSz;
    if ((uLong)stream.avail_out != outSz) return COMPRESS_INIT_E;

    stream.zalloc = (alloc_func)myAlloc;
    stream.zfree = (free_func)myFree;
    stream.opaque = (voidpf)0;

    if (deflateInit2(&stream, Z_DEFAULT_COMPRESSION, Z_DEFLATED,
                     DEFLATE_DEFAULT_WINDOWBITS, DEFLATE_DEFAULT_MEMLEVEL,
                     flags ? Z_FIXED : Z_DEFAULT_STRATEGY) != Z_OK)
        return COMPRESS_INIT_E;

    if (deflate(&stream, Z_FINISH) != Z_STREAM_END) {
        deflateEnd(&stream);
        return COMPRESS_E;
    }

    result = (int)stream.total_out;

    if (deflateEnd(&stream) != Z_OK)
        result = COMPRESS_E;

    return result;
}


int DeCompress(byte* out, word32 outSz, const byte* in, word32 inSz)
/*
 * out - pointer to destination buffer
 * outSz - size of destination buffer
 * in - pointer to source buffer to compress
 * inSz - size of source to compress
 * flags - flags to control how compress operates 
 *
 * return:
 *    negative - error code
 *    positive - bytes stored in out buffer
 */ 
{
    z_stream stream;
    int result = 0;

    stream.next_in = (Bytef*)in;
    stream.avail_in = (uInt)inSz;
    /* Check for source > 64K on 16-bit machine: */
    if ((uLong)stream.avail_in != inSz) return DECOMPRESS_INIT_E;

    stream.next_out = out;
    stream.avail_out = (uInt)outSz;
    if ((uLong)stream.avail_out != outSz) return DECOMPRESS_INIT_E;

    stream.zalloc = (alloc_func)myAlloc;
    stream.zfree = (free_func)myFree;
    stream.opaque = (voidpf)0;

    if (inflateInit2(&stream, DEFLATE_DEFAULT_WINDOWBITS) != Z_OK)
        return DECOMPRESS_INIT_E;

    if (inflate(&stream, Z_FINISH) != Z_STREAM_END) {
        inflateEnd(&stream);
        return DECOMPRESS_E;
    }
    
    result = (int)stream.total_out;

    if (inflateEnd(&stream) != Z_OK)
        result = DECOMPRESS_E;

    return result;
}


#endif /* HAVE_LIBZ */

