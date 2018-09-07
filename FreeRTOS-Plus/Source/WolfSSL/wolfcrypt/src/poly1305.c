/* poly1305.c
 *
 * Copyright (C) 2006-2015 wolfSSL Inc.
 *
 * This file is part of wolfSSL. (formerly known as CyaSSL)
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 *
 * Based off the public domain implementations by Andrew Moon 
 * and Daniel J. Bernstein
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifdef HAVE_POLY1305
#include <wolfssl/wolfcrypt/poly1305.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/logging.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #include <wolfcrypt/src/misc.c>
#endif
#ifdef CHACHA_AEAD_TEST
    #include <stdio.h>
#endif

#ifdef _MSC_VER
    /* 4127 warning constant while(1)  */
    #pragma warning(disable: 4127)
#endif

#if defined(POLY130564)
	
	#if defined(_MSC_VER)
		#define POLY1305_NOINLINE __declspec(noinline)
	#elif defined(__GNUC__)
		#define POLY1305_NOINLINE __attribute__((noinline))
	#else
		#define POLY1305_NOINLINE
	#endif
	
	#if defined(_MSC_VER)
	    #include <intrin.h>
		
	    typedef struct word128 {
			word64 lo;
			word64 hi;
		} word128;
	
		#define MUL(out, x, y) out.lo = _umul128((x), (y), &out.hi)
		#define ADD(out, in) { word64 t = out.lo; out.lo += in.lo;
	                           out.hi += (out.lo < t) + in.hi; }
		#define ADDLO(out, in) { word64 t = out.lo; out.lo += in;
	                             out.hi += (out.lo < t); }
		#define SHR(in, shift) (__shiftright128(in.lo, in.hi, (shift)))
		#define LO(in) (in.lo)
	
	#elif defined(__GNUC__)
		#if defined(__SIZEOF_INT128__)
			typedef unsigned __int128 word128;
		#else
			typedef unsigned word128 __attribute__((mode(TI)));
		#endif
	
		#define MUL(out, x, y) out = ((word128)x * y)
		#define ADD(out, in) out += in
		#define ADDLO(out, in) out += in
		#define SHR(in, shift) (word64)(in >> (shift))
		#define LO(in) (word64)(in)
	#endif
	
	static word64 U8TO64(const byte* p) {
		return
			(((word64)(p[0] & 0xff)      ) |
		     ((word64)(p[1] & 0xff) <<  8) |
	         ((word64)(p[2] & 0xff) << 16) |
	         ((word64)(p[3] & 0xff) << 24) |
			 ((word64)(p[4] & 0xff) << 32) |
			 ((word64)(p[5] & 0xff) << 40) |
			 ((word64)(p[6] & 0xff) << 48) |
			 ((word64)(p[7] & 0xff) << 56));
	}
	
	static void U64TO8(byte* p, word64 v) {
		p[0] = (v      ) & 0xff;
		p[1] = (v >>  8) & 0xff;
		p[2] = (v >> 16) & 0xff;
		p[3] = (v >> 24) & 0xff;
		p[4] = (v >> 32) & 0xff;
		p[5] = (v >> 40) & 0xff;
		p[6] = (v >> 48) & 0xff;
		p[7] = (v >> 56) & 0xff;
	}

#else /* if not 64 bit then use 32 bit */
	
	static word32 U8TO32(const byte *p) {
		return
			(((word32)(p[0] & 0xff)      ) |
		     ((word32)(p[1] & 0xff) <<  8) |
	         ((word32)(p[2] & 0xff) << 16) |
	         ((word32)(p[3] & 0xff) << 24));
	}
	
	static void U32TO8(byte *p, word32 v) {
		p[0] = (v      ) & 0xff;
		p[1] = (v >>  8) & 0xff;
		p[2] = (v >> 16) & 0xff;
		p[3] = (v >> 24) & 0xff;
	}
#endif

static void poly1305_blocks(Poly1305* ctx, const unsigned char *m,
                            size_t bytes) {

#ifdef POLY130564

	const word64 hibit = (ctx->final) ? 0 : ((word64)1 << 40); /* 1 << 128 */
	word64 r0,r1,r2;
	word64 s1,s2;
	word64 h0,h1,h2;
	word64 c;
	word128 d0,d1,d2,d;

#else

    const word32 hibit = (ctx->final) ? 0 : (1 << 24); /* 1 << 128 */
	word32 r0,r1,r2,r3,r4;
	word32 s1,s2,s3,s4;
	word32 h0,h1,h2,h3,h4;
	word64 d0,d1,d2,d3,d4;
	word32 c;

#endif

#ifdef POLY130564

    r0 = ctx->r[0];
	r1 = ctx->r[1];
	r2 = ctx->r[2];

	h0 = ctx->h[0];
	h1 = ctx->h[1];
	h2 = ctx->h[2];

	s1 = r1 * (5 << 2);
	s2 = r2 * (5 << 2);

	while (bytes >= POLY1305_BLOCK_SIZE) {
		word64 t0,t1;

		/* h += m[i] */
		t0 = U8TO64(&m[0]);
		t1 = U8TO64(&m[8]);

		h0 += (( t0                    ) & 0xfffffffffff);
		h1 += (((t0 >> 44) | (t1 << 20)) & 0xfffffffffff);
		h2 += (((t1 >> 24)             ) & 0x3ffffffffff) | hibit;

		/* h *= r */
		MUL(d0, h0, r0); MUL(d, h1, s2); ADD(d0, d); MUL(d, h2, s1); ADD(d0, d);
		MUL(d1, h0, r1); MUL(d, h1, r0); ADD(d1, d); MUL(d, h2, s2); ADD(d1, d);
		MUL(d2, h0, r2); MUL(d, h1, r1); ADD(d2, d); MUL(d, h2, r0); ADD(d2, d);

		/* (partial) h %= p */
		              c = SHR(d0, 44); h0 = LO(d0) & 0xfffffffffff;
		ADDLO(d1, c); c = SHR(d1, 44); h1 = LO(d1) & 0xfffffffffff;
		ADDLO(d2, c); c = SHR(d2, 42); h2 = LO(d2) & 0x3ffffffffff;
		h0  += c * 5; c = (h0 >> 44);  h0 =    h0  & 0xfffffffffff;
		h1  += c;

		m += POLY1305_BLOCK_SIZE;
		bytes -= POLY1305_BLOCK_SIZE;
	}

	ctx->h[0] = h0;
	ctx->h[1] = h1;
	ctx->h[2] = h2;

#else /* if not 64 bit then use 32 bit */
   
	r0 = ctx->r[0];
	r1 = ctx->r[1];
	r2 = ctx->r[2];
	r3 = ctx->r[3];
	r4 = ctx->r[4];

	s1 = r1 * 5;
	s2 = r2 * 5;
	s3 = r3 * 5;
	s4 = r4 * 5;

	h0 = ctx->h[0];
	h1 = ctx->h[1];
	h2 = ctx->h[2];
	h3 = ctx->h[3];
	h4 = ctx->h[4];

	while (bytes >= POLY1305_BLOCK_SIZE) {
		/* h += m[i] */
		h0 += (U8TO32(m+ 0)     ) & 0x3ffffff;
		h1 += (U8TO32(m+ 3) >> 2) & 0x3ffffff;
		h2 += (U8TO32(m+ 6) >> 4) & 0x3ffffff;
		h3 += (U8TO32(m+ 9) >> 6) & 0x3ffffff;
		h4 += (U8TO32(m+12) >> 8) | hibit;

		/* h *= r */
		d0 = ((word64)h0 * r0) + ((word64)h1 * s4) + ((word64)h2 * s3) +
             ((word64)h3 * s2) + ((word64)h4 * s1);
		d1 = ((word64)h0 * r1) + ((word64)h1 * r0) + ((word64)h2 * s4) +
             ((word64)h3 * s3) + ((word64)h4 * s2);
		d2 = ((word64)h0 * r2) + ((word64)h1 * r1) + ((word64)h2 * r0) +
             ((word64)h3 * s4) + ((word64)h4 * s3);
		d3 = ((word64)h0 * r3) + ((word64)h1 * r2) + ((word64)h2 * r1) +
             ((word64)h3 * r0) + ((word64)h4 * s4);
		d4 = ((word64)h0 * r4) + ((word64)h1 * r3) + ((word64)h2 * r2) +
             ((word64)h3 * r1) + ((word64)h4 * r0);

		/* (partial) h %= p */
		              c = (word32)(d0 >> 26); h0 = (word32)d0 & 0x3ffffff;
		d1 += c;      c = (word32)(d1 >> 26); h1 = (word32)d1 & 0x3ffffff;
		d2 += c;      c = (word32)(d2 >> 26); h2 = (word32)d2 & 0x3ffffff;
		d3 += c;      c = (word32)(d3 >> 26); h3 = (word32)d3 & 0x3ffffff;
		d4 += c;      c = (word32)(d4 >> 26); h4 = (word32)d4 & 0x3ffffff;
		h0 += c * 5;  c =  (h0 >> 26); h0 =                h0 & 0x3ffffff;
		h1 += c;

		m += POLY1305_BLOCK_SIZE;
		bytes -= POLY1305_BLOCK_SIZE;
	}

	ctx->h[0] = h0;
	ctx->h[1] = h1;
	ctx->h[2] = h2;
	ctx->h[3] = h3;
	ctx->h[4] = h4;

#endif /* end of 64 bit cpu blocks or 32 bit cpu */
}


int wc_Poly1305SetKey(Poly1305* ctx, const byte* key, word32 keySz) {

#if defined(POLY130564)
    word64 t0,t1;
#endif

#ifdef CHACHA_AEAD_TEST
    word32 k;
    printf("Poly key used:\n");
    for (k = 0; k < keySz; k++) {
        printf("%02x", key[k]);
        if ((k+1) % 8 == 0)
            printf("\n");
    }
	printf("\n");
#endif

    if (keySz != 32 || ctx == NULL)
        return BAD_FUNC_ARG;

#if defined(POLY130564)

	/* r &= 0xffffffc0ffffffc0ffffffc0fffffff */
	t0 = U8TO64(key + 0);
	t1 = U8TO64(key + 8);

	ctx->r[0] = ( t0                    ) & 0xffc0fffffff;
	ctx->r[1] = ((t0 >> 44) | (t1 << 20)) & 0xfffffc0ffff;
	ctx->r[2] = ((t1 >> 24)             ) & 0x00ffffffc0f;

	/* h (accumulator) = 0 */
	ctx->h[0] = 0;
	ctx->h[1] = 0;
	ctx->h[2] = 0;

	/* save pad for later */
	ctx->pad[0] = U8TO64(key + 16);
	ctx->pad[1] = U8TO64(key + 24);

#else /* if not 64 bit then use 32 bit */
	
    /* r &= 0xffffffc0ffffffc0ffffffc0fffffff */
	ctx->r[0] = (U8TO32(key +  0)     ) & 0x3ffffff;
	ctx->r[1] = (U8TO32(key +  3) >> 2) & 0x3ffff03;
	ctx->r[2] = (U8TO32(key +  6) >> 4) & 0x3ffc0ff;
	ctx->r[3] = (U8TO32(key +  9) >> 6) & 0x3f03fff;
	ctx->r[4] = (U8TO32(key + 12) >> 8) & 0x00fffff;

	/* h = 0 */
	ctx->h[0] = 0;
	ctx->h[1] = 0;
	ctx->h[2] = 0;
	ctx->h[3] = 0;
	ctx->h[4] = 0;

	/* save pad for later */
	ctx->pad[0] = U8TO32(key + 16);
	ctx->pad[1] = U8TO32(key + 20);
	ctx->pad[2] = U8TO32(key + 24);
	ctx->pad[3] = U8TO32(key + 28);

#endif

	ctx->leftover = 0;
	ctx->final = 0;

    return 0;
}


int wc_Poly1305Final(Poly1305* ctx, byte* mac) {

#if defined(POLY130564)

    word64 h0,h1,h2,c;
	word64 g0,g1,g2;
	word64 t0,t1;

#else

    word32 h0,h1,h2,h3,h4,c;
	word32 g0,g1,g2,g3,g4;
	word64 f;
	word32 mask;

#endif

    if (ctx == NULL)
        return BAD_FUNC_ARG;

#if defined(POLY130564)

	/* process the remaining block */
	if (ctx->leftover) {
		size_t i = ctx->leftover;
		ctx->buffer[i] = 1;
		for (i = i + 1; i < POLY1305_BLOCK_SIZE; i++)
			ctx->buffer[i] = 0;
		ctx->final = 1;
		poly1305_blocks(ctx, ctx->buffer, POLY1305_BLOCK_SIZE);
	}

	/* fully carry h */
	h0 = ctx->h[0];
	h1 = ctx->h[1];
	h2 = ctx->h[2];

	             c = (h1 >> 44); h1 &= 0xfffffffffff;
	h2 += c;     c = (h2 >> 42); h2 &= 0x3ffffffffff;
	h0 += c * 5; c = (h0 >> 44); h0 &= 0xfffffffffff;
	h1 += c;	 c = (h1 >> 44); h1 &= 0xfffffffffff;
	h2 += c;     c = (h2 >> 42); h2 &= 0x3ffffffffff;
	h0 += c * 5; c = (h0 >> 44); h0 &= 0xfffffffffff;
	h1 += c;

	/* compute h + -p */
	g0 = h0 + 5; c = (g0 >> 44); g0 &= 0xfffffffffff;
	g1 = h1 + c; c = (g1 >> 44); g1 &= 0xfffffffffff;
	g2 = h2 + c - ((word64)1 << 42);

	/* select h if h < p, or h + -p if h >= p */
	c = (g2 >> ((sizeof(word64) * 8) - 1)) - 1;
	g0 &= c;
	g1 &= c;
	g2 &= c;
	c = ~c;
	h0 = (h0 & c) | g0;
	h1 = (h1 & c) | g1;
	h2 = (h2 & c) | g2;

	/* h = (h + pad) */
	t0 = ctx->pad[0];
	t1 = ctx->pad[1];

	h0 += (( t0                    ) & 0xfffffffffff)    ;
    c = (h0 >> 44); h0 &= 0xfffffffffff;
	h1 += (((t0 >> 44) | (t1 << 20)) & 0xfffffffffff) + c;
    c = (h1 >> 44); h1 &= 0xfffffffffff;
	h2 += (((t1 >> 24)             ) & 0x3ffffffffff) + c;
    h2 &= 0x3ffffffffff;

	/* mac = h % (2^128) */
	h0 = ((h0      ) | (h1 << 44));
	h1 = ((h1 >> 20) | (h2 << 24));

	U64TO8(mac + 0, h0);
	U64TO8(mac + 8, h1);

	/* zero out the state */
	ctx->h[0] = 0;
	ctx->h[1] = 0;
	ctx->h[2] = 0;
	ctx->r[0] = 0;
	ctx->r[1] = 0;
	ctx->r[2] = 0;
	ctx->pad[0] = 0;
	ctx->pad[1] = 0;

#else /* if not 64 bit then use 32 bit */
    
	/* process the remaining block */
	if (ctx->leftover) {
		size_t i = ctx->leftover;
		ctx->buffer[i++] = 1;
		for (; i < POLY1305_BLOCK_SIZE; i++)
			ctx->buffer[i] = 0;
		ctx->final = 1;
		poly1305_blocks(ctx, ctx->buffer, POLY1305_BLOCK_SIZE);
	}

	/* fully carry h */
	h0 = ctx->h[0];
	h1 = ctx->h[1];
	h2 = ctx->h[2];
	h3 = ctx->h[3];
	h4 = ctx->h[4];

	             c = h1 >> 26; h1 = h1 & 0x3ffffff;
	h2 +=     c; c = h2 >> 26; h2 = h2 & 0x3ffffff;
	h3 +=     c; c = h3 >> 26; h3 = h3 & 0x3ffffff;
	h4 +=     c; c = h4 >> 26; h4 = h4 & 0x3ffffff;
	h0 += c * 5; c = h0 >> 26; h0 = h0 & 0x3ffffff;
	h1 +=     c;

	/* compute h + -p */
	g0 = h0 + 5; c = g0 >> 26; g0 &= 0x3ffffff;
	g1 = h1 + c; c = g1 >> 26; g1 &= 0x3ffffff;
	g2 = h2 + c; c = g2 >> 26; g2 &= 0x3ffffff;
	g3 = h3 + c; c = g3 >> 26; g3 &= 0x3ffffff;
	g4 = h4 + c - (1 << 26);

	/* select h if h < p, or h + -p if h >= p */
	mask = (g4 >> ((sizeof(word32) * 8) - 1)) - 1;
	g0 &= mask;
	g1 &= mask;
	g2 &= mask;
	g3 &= mask;
	g4 &= mask;
	mask = ~mask;
	h0 = (h0 & mask) | g0;
	h1 = (h1 & mask) | g1;
	h2 = (h2 & mask) | g2;
	h3 = (h3 & mask) | g3;
	h4 = (h4 & mask) | g4;

	/* h = h % (2^128) */
	h0 = ((h0      ) | (h1 << 26)) & 0xffffffff;
	h1 = ((h1 >>  6) | (h2 << 20)) & 0xffffffff;
	h2 = ((h2 >> 12) | (h3 << 14)) & 0xffffffff;
	h3 = ((h3 >> 18) | (h4 <<  8)) & 0xffffffff;

	/* mac = (h + pad) % (2^128) */
	f = (word64)h0 + ctx->pad[0]            ; h0 = (word32)f;
	f = (word64)h1 + ctx->pad[1] + (f >> 32); h1 = (word32)f;
	f = (word64)h2 + ctx->pad[2] + (f >> 32); h2 = (word32)f;
	f = (word64)h3 + ctx->pad[3] + (f >> 32); h3 = (word32)f;

	U32TO8(mac + 0, h0);
	U32TO8(mac + 4, h1);
	U32TO8(mac + 8, h2);
	U32TO8(mac + 12, h3);

	/* zero out the state */
	ctx->h[0] = 0;
	ctx->h[1] = 0;
	ctx->h[2] = 0;
	ctx->h[3] = 0;
	ctx->h[4] = 0;
	ctx->r[0] = 0;
	ctx->r[1] = 0;
	ctx->r[2] = 0;
	ctx->r[3] = 0;
	ctx->r[4] = 0;
	ctx->pad[0] = 0;
	ctx->pad[1] = 0;
	ctx->pad[2] = 0;
	ctx->pad[3] = 0;

#endif

    return 0;
}


int wc_Poly1305Update(Poly1305* ctx, const byte* m, word32 bytes) {

	size_t i;

#ifdef CHACHA_AEAD_TEST
    word32 k;
    printf("Raw input to poly:\n");
    for (k = 0; k < bytes; k++) {
        printf("%02x", m[k]);
        if ((k+1) % 16 == 0)
            printf("\n");
    }
	printf("\n");
#endif
    
    if (ctx == NULL)
        return BAD_FUNC_ARG;

	/* handle leftover */
	if (ctx->leftover) {
		size_t want = (POLY1305_BLOCK_SIZE - ctx->leftover);
		if (want > bytes)
			want = bytes;
		for (i = 0; i < want; i++)
			ctx->buffer[ctx->leftover + i] = m[i];
		bytes -= want;
		m += want;
		ctx->leftover += want;
		if (ctx->leftover < POLY1305_BLOCK_SIZE)
			return 0;
		poly1305_blocks(ctx, ctx->buffer, POLY1305_BLOCK_SIZE);
		ctx->leftover = 0;
	}

	/* process full blocks */
	if (bytes >= POLY1305_BLOCK_SIZE) {
		size_t want = (bytes & ~(POLY1305_BLOCK_SIZE - 1));
		poly1305_blocks(ctx, m, want);
		m += want;
		bytes -= want;
	}

	/* store leftover */
	if (bytes) {
		for (i = 0; i < bytes; i++)
			ctx->buffer[ctx->leftover + i] = m[i];
		ctx->leftover += bytes;
	}
    return 0;
}
#endif /* HAVE_POLY1305 */

