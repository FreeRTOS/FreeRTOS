/* hc128.c
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
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


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifdef HAVE_HC128

#include <wolfssl/wolfcrypt/hc128.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/logging.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/hc128.h>
		#include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif


#ifdef BIG_ENDIAN_ORDER
    #define LITTLE32(x) ByteReverseWord32(x)
#else
    #define LITTLE32(x) (x)
#endif


/*h1 function*/
#define h1(ctx, x, y) {                         \
     byte a,c;                                  \
     a = (byte) (x);                            \
     c = (byte) ((x) >> 16);                    \
     y = (ctx->T[512+a])+(ctx->T[512+256+c]);   \
}

/*h2 function*/
#define h2(ctx, x, y) {                         \
     byte a,c;                                  \
     a = (byte) (x);                            \
     c = (byte) ((x) >> 16);                    \
     y = (ctx->T[a])+(ctx->T[256+c]);           \
}

/*one step of HC-128, update P and generate 32 bits keystream*/
#define step_P(ctx,u,v,a,b,c,d,n){              \
     word32 tem0,tem1,tem2,tem3;                \
     h1((ctx),(ctx->X[(d)]),tem3);              \
     tem0 = rotrFixed((ctx->T[(v)]),23);        \
     tem1 = rotrFixed((ctx->X[(c)]),10);        \
     tem2 = rotrFixed((ctx->X[(b)]),8);         \
     (ctx->T[(u)]) += tem2+(tem0 ^ tem1);       \
     (ctx->X[(a)]) = (ctx->T[(u)]);             \
     (n) = tem3 ^ (ctx->T[(u)]) ;               \
}

/*one step of HC-128, update Q and generate 32 bits keystream*/
#define step_Q(ctx,u,v,a,b,c,d,n){              \
     word32 tem0,tem1,tem2,tem3;                \
     h2((ctx),(ctx->Y[(d)]),tem3);              \
     tem0 = rotrFixed((ctx->T[(v)]),(32-23));   \
     tem1 = rotrFixed((ctx->Y[(c)]),(32-10));   \
     tem2 = rotrFixed((ctx->Y[(b)]),(32-8));    \
     (ctx->T[(u)]) += tem2 + (tem0 ^ tem1);     \
     (ctx->Y[(a)]) = (ctx->T[(u)]);             \
     (n) = tem3 ^ (ctx->T[(u)]) ;               \
}

/*16 steps of HC-128, generate 512 bits keystream*/
static void generate_keystream(HC128* ctx, word32* keystream)
{
   word32 cc,dd;
   cc = ctx->counter1024 & 0x1ff;
   dd = (cc+16)&0x1ff;

   if (ctx->counter1024 < 512)
   {
      ctx->counter1024 = (ctx->counter1024 + 16) & 0x3ff;
      step_P(ctx, cc+0, cc+1, 0, 6, 13,4, keystream[0]);
      step_P(ctx, cc+1, cc+2, 1, 7, 14,5, keystream[1]);
      step_P(ctx, cc+2, cc+3, 2, 8, 15,6, keystream[2]);
      step_P(ctx, cc+3, cc+4, 3, 9, 0, 7, keystream[3]);
      step_P(ctx, cc+4, cc+5, 4, 10,1, 8, keystream[4]);
      step_P(ctx, cc+5, cc+6, 5, 11,2, 9, keystream[5]);
      step_P(ctx, cc+6, cc+7, 6, 12,3, 10,keystream[6]);
      step_P(ctx, cc+7, cc+8, 7, 13,4, 11,keystream[7]);
      step_P(ctx, cc+8, cc+9, 8, 14,5, 12,keystream[8]);
      step_P(ctx, cc+9, cc+10,9, 15,6, 13,keystream[9]);
      step_P(ctx, cc+10,cc+11,10,0, 7, 14,keystream[10]);
      step_P(ctx, cc+11,cc+12,11,1, 8, 15,keystream[11]);
      step_P(ctx, cc+12,cc+13,12,2, 9, 0, keystream[12]);
      step_P(ctx, cc+13,cc+14,13,3, 10,1, keystream[13]);
      step_P(ctx, cc+14,cc+15,14,4, 11,2, keystream[14]);
      step_P(ctx, cc+15,dd+0, 15,5, 12,3, keystream[15]);
   }
   else
   {
	  ctx->counter1024 = (ctx->counter1024 + 16) & 0x3ff;
      step_Q(ctx, 512+cc+0, 512+cc+1, 0, 6, 13,4, keystream[0]);
      step_Q(ctx, 512+cc+1, 512+cc+2, 1, 7, 14,5, keystream[1]);
      step_Q(ctx, 512+cc+2, 512+cc+3, 2, 8, 15,6, keystream[2]);
      step_Q(ctx, 512+cc+3, 512+cc+4, 3, 9, 0, 7, keystream[3]);
      step_Q(ctx, 512+cc+4, 512+cc+5, 4, 10,1, 8, keystream[4]);
      step_Q(ctx, 512+cc+5, 512+cc+6, 5, 11,2, 9, keystream[5]);
      step_Q(ctx, 512+cc+6, 512+cc+7, 6, 12,3, 10,keystream[6]);
      step_Q(ctx, 512+cc+7, 512+cc+8, 7, 13,4, 11,keystream[7]);
      step_Q(ctx, 512+cc+8, 512+cc+9, 8, 14,5, 12,keystream[8]);
      step_Q(ctx, 512+cc+9, 512+cc+10,9, 15,6, 13,keystream[9]);
      step_Q(ctx, 512+cc+10,512+cc+11,10,0, 7, 14,keystream[10]);
      step_Q(ctx, 512+cc+11,512+cc+12,11,1, 8, 15,keystream[11]);
      step_Q(ctx, 512+cc+12,512+cc+13,12,2, 9, 0, keystream[12]);
      step_Q(ctx, 512+cc+13,512+cc+14,13,3, 10,1, keystream[13]);
      step_Q(ctx, 512+cc+14,512+cc+15,14,4, 11,2, keystream[14]);
      step_Q(ctx, 512+cc+15,512+dd+0, 15,5, 12,3, keystream[15]);
   }
}


/* The following defines the initialization functions */
#define f1(x)  (rotrFixed((x),7)  ^ rotrFixed((x),18) ^ ((x) >> 3))
#define f2(x)  (rotrFixed((x),17) ^ rotrFixed((x),19) ^ ((x) >> 10))

/*update table P*/
#define update_P(ctx,u,v,a,b,c,d){                  \
     word32 tem0,tem1,tem2,tem3;                    \
     tem0 = rotrFixed((ctx->T[(v)]),23);            \
     tem1 = rotrFixed((ctx->X[(c)]),10);            \
     tem2 = rotrFixed((ctx->X[(b)]),8);             \
     h1((ctx),(ctx->X[(d)]),tem3);                  \
     (ctx->T[(u)]) = ((ctx->T[(u)]) + tem2+(tem0^tem1)) ^ tem3;     \
     (ctx->X[(a)]) = (ctx->T[(u)]);                 \
}

/*update table Q*/
#define update_Q(ctx,u,v,a,b,c,d){                  \
     word32 tem0,tem1,tem2,tem3;                    \
     tem0 = rotrFixed((ctx->T[(v)]),(32-23));       \
     tem1 = rotrFixed((ctx->Y[(c)]),(32-10));       \
     tem2 = rotrFixed((ctx->Y[(b)]),(32-8));        \
     h2((ctx),(ctx->Y[(d)]),tem3);                  \
     (ctx->T[(u)]) = ((ctx->T[(u)]) + tem2+(tem0^tem1)) ^ tem3;     \
     (ctx->Y[(a)]) = (ctx->T[(u)]);                 \
}

/*16 steps of HC-128, without generating keystream, */
/*but use the outputs to update P and Q*/
static void setup_update(HC128* ctx)  /*each time 16 steps*/
{
   word32 cc,dd;
   cc = ctx->counter1024 & 0x1ff;
   dd = (cc+16)&0x1ff;

   if (ctx->counter1024 < 512)
   {
      ctx->counter1024 = (ctx->counter1024 + 16) & 0x3ff;
      update_P(ctx, cc+0, cc+1, 0, 6, 13, 4);
      update_P(ctx, cc+1, cc+2, 1, 7, 14, 5);
      update_P(ctx, cc+2, cc+3, 2, 8, 15, 6);
      update_P(ctx, cc+3, cc+4, 3, 9, 0,  7);
      update_P(ctx, cc+4, cc+5, 4, 10,1,  8);
      update_P(ctx, cc+5, cc+6, 5, 11,2,  9);
      update_P(ctx, cc+6, cc+7, 6, 12,3,  10);
      update_P(ctx, cc+7, cc+8, 7, 13,4,  11);
      update_P(ctx, cc+8, cc+9, 8, 14,5,  12);
      update_P(ctx, cc+9, cc+10,9, 15,6,  13);
      update_P(ctx, cc+10,cc+11,10,0, 7,  14);
      update_P(ctx, cc+11,cc+12,11,1, 8,  15);
      update_P(ctx, cc+12,cc+13,12,2, 9,  0);
      update_P(ctx, cc+13,cc+14,13,3, 10, 1);
      update_P(ctx, cc+14,cc+15,14,4, 11, 2);
      update_P(ctx, cc+15,dd+0, 15,5, 12, 3);
   }
   else
   {
      ctx->counter1024 = (ctx->counter1024 + 16) & 0x3ff;
      update_Q(ctx, 512+cc+0, 512+cc+1, 0, 6, 13, 4);
      update_Q(ctx, 512+cc+1, 512+cc+2, 1, 7, 14, 5);
      update_Q(ctx, 512+cc+2, 512+cc+3, 2, 8, 15, 6);
      update_Q(ctx, 512+cc+3, 512+cc+4, 3, 9, 0,  7);
      update_Q(ctx, 512+cc+4, 512+cc+5, 4, 10,1,  8);
      update_Q(ctx, 512+cc+5, 512+cc+6, 5, 11,2,  9);
      update_Q(ctx, 512+cc+6, 512+cc+7, 6, 12,3,  10);
      update_Q(ctx, 512+cc+7, 512+cc+8, 7, 13,4,  11);
      update_Q(ctx, 512+cc+8, 512+cc+9, 8, 14,5,  12);
      update_Q(ctx, 512+cc+9, 512+cc+10,9, 15,6,  13);
      update_Q(ctx, 512+cc+10,512+cc+11,10,0, 7,  14);
      update_Q(ctx, 512+cc+11,512+cc+12,11,1, 8,  15);
      update_Q(ctx, 512+cc+12,512+cc+13,12,2, 9,  0);
      update_Q(ctx, 512+cc+13,512+cc+14,13,3, 10, 1);
      update_Q(ctx, 512+cc+14,512+cc+15,14,4, 11, 2);
      update_Q(ctx, 512+cc+15,512+dd+0, 15,5, 12, 3);
   }
}


/* for the 128-bit key:  key[0]...key[15]
*  key[0] is the least significant byte of ctx->key[0] (K_0);
*  key[3] is the most significant byte of ctx->key[0]  (K_0);
*  ...
*  key[12] is the least significant byte of ctx->key[3] (K_3)
*  key[15] is the most significant byte of ctx->key[3]  (K_3)
*
*  for the 128-bit iv:  iv[0]...iv[15]
*  iv[0] is the least significant byte of ctx->iv[0] (IV_0);
*  iv[3] is the most significant byte of ctx->iv[0]  (IV_0);
*  ...
*  iv[12] is the least significant byte of ctx->iv[3] (IV_3)
*  iv[15] is the most significant byte of ctx->iv[3]  (IV_3)
*/



static void Hc128_SetIV(HC128* ctx, const byte* inIv)
{
    word32 i;
    word32 iv[4];

    if (inIv)
        XMEMCPY(iv, inIv, sizeof(iv));
    else
        XMEMSET(iv,    0, sizeof(iv));

	for (i = 0; i < (128 >> 5); i++)
        ctx->iv[i] = LITTLE32(iv[i]);

    for (; i < 8; i++) ctx->iv[i] = ctx->iv[i-4];

    /* expand the key and IV into the table T */
    /* (expand the key and IV into the table P and Q) */

	for (i = 0; i < 8;  i++)   ctx->T[i] = ctx->key[i];
	for (i = 8; i < 16; i++)   ctx->T[i] = ctx->iv[i-8];

    for (i = 16; i < (256+16); i++)
		ctx->T[i] = f2(ctx->T[i-2]) + ctx->T[i-7] + f1(ctx->T[i-15]) +
                                                       ctx->T[i-16]+i;

	for (i = 0; i < 16;  i++)  ctx->T[i] = ctx->T[256+i];

	for (i = 16; i < 1024; i++)
		ctx->T[i] = f2(ctx->T[i-2]) + ctx->T[i-7] + f1(ctx->T[i-15]) +
                                                       ctx->T[i-16]+256+i;

    /* initialize counter1024, X and Y */
	ctx->counter1024 = 0;
	for (i = 0; i < 16; i++) ctx->X[i] = ctx->T[512-16+i];
    for (i = 0; i < 16; i++) ctx->Y[i] = ctx->T[512+512-16+i];

    /* run the cipher 1024 steps before generating the output */
	for (i = 0; i < 64; i++)  setup_update(ctx);
}


static WC_INLINE int DoKey(HC128* ctx, const byte* key, const byte* iv)
{
  word32 i;

  /* Key size in bits 128 */
  for (i = 0; i < (128 >> 5); i++)
      ctx->key[i] = LITTLE32(((word32*)key)[i]);

  for ( ; i < 8 ; i++) ctx->key[i] = ctx->key[i-4];

  Hc128_SetIV(ctx, iv);

  return 0;
}


int wc_Hc128_SetHeap(HC128* ctx, void* heap)
{
    if (ctx == NULL) {
        return BAD_FUNC_ARG;
    }

#ifdef XSTREAM_ALIGN
    ctx->heap = heap;
#endif

    (void)heap;
    return 0;
}

/* Key setup */
int wc_Hc128_SetKey(HC128* ctx, const byte* key, const byte* iv)
{
    if (ctx == NULL || key == NULL) {
        return BAD_FUNC_ARG;
    }

#ifdef XSTREAM_ALIGN
    /* default heap to NULL or heap test value */
    #ifdef WOLFSSL_HEAP_TEST
        ctx->heap = (void*)WOLFSSL_HEAP_TEST;
    #else
        ctx->heap = NULL;
    #endif /* WOLFSSL_HEAP_TEST */

    if ((wolfssl_word)key % 4) {
        int alignKey[4];

        /* iv gets aligned in SetIV */
        WOLFSSL_MSG("Hc128SetKey unaligned key");

        XMEMCPY(alignKey, key, sizeof(alignKey));

        return DoKey(ctx, (const byte*)alignKey, iv);
    }
#endif /* XSTREAM_ALIGN */

    return DoKey(ctx, key, iv);
}



/* The following defines the encryption of data stream */
static WC_INLINE int DoProcess(HC128* ctx, byte* output, const byte* input,
                            word32 msglen)
{
  word32 i, keystream[16];

  for ( ; msglen >= 64; msglen -= 64, input += 64, output += 64)
  {
	  generate_keystream(ctx, keystream);

      /* unroll loop */
	  ((word32*)output)[0]  = ((word32*)input)[0]  ^ LITTLE32(keystream[0]);
	  ((word32*)output)[1]  = ((word32*)input)[1]  ^ LITTLE32(keystream[1]);
	  ((word32*)output)[2]  = ((word32*)input)[2]  ^ LITTLE32(keystream[2]);
	  ((word32*)output)[3]  = ((word32*)input)[3]  ^ LITTLE32(keystream[3]);
	  ((word32*)output)[4]  = ((word32*)input)[4]  ^ LITTLE32(keystream[4]);
	  ((word32*)output)[5]  = ((word32*)input)[5]  ^ LITTLE32(keystream[5]);
	  ((word32*)output)[6]  = ((word32*)input)[6]  ^ LITTLE32(keystream[6]);
	  ((word32*)output)[7]  = ((word32*)input)[7]  ^ LITTLE32(keystream[7]);
	  ((word32*)output)[8]  = ((word32*)input)[8]  ^ LITTLE32(keystream[8]);
	  ((word32*)output)[9]  = ((word32*)input)[9]  ^ LITTLE32(keystream[9]);
	  ((word32*)output)[10] = ((word32*)input)[10] ^ LITTLE32(keystream[10]);
	  ((word32*)output)[11] = ((word32*)input)[11] ^ LITTLE32(keystream[11]);
	  ((word32*)output)[12] = ((word32*)input)[12] ^ LITTLE32(keystream[12]);
	  ((word32*)output)[13] = ((word32*)input)[13] ^ LITTLE32(keystream[13]);
	  ((word32*)output)[14] = ((word32*)input)[14] ^ LITTLE32(keystream[14]);
	  ((word32*)output)[15] = ((word32*)input)[15] ^ LITTLE32(keystream[15]);
  }

  if (msglen > 0)
  {
      XMEMSET(keystream, 0, sizeof(keystream)); /* hush the static analysis */
      generate_keystream(ctx, keystream);

#ifdef BIG_ENDIAN_ORDER
      {
          word32 wordsLeft = msglen / sizeof(word32);
          if (msglen % sizeof(word32)) wordsLeft++;

          ByteReverseWords(keystream, keystream, wordsLeft * sizeof(word32));
      }
#endif

      for (i = 0; i < msglen; i++)
	      output[i] = input[i] ^ ((byte*)keystream)[i];
  }

  return 0;
}


/* Encrypt/decrypt a message of any size */
int wc_Hc128_Process(HC128* ctx, byte* output, const byte* input, word32 msglen)
{
    if (ctx == NULL || output == NULL || input == NULL) {
        return BAD_FUNC_ARG;
    }

#ifdef XSTREAM_ALIGN
    if ((wolfssl_word)input % 4 || (wolfssl_word)output % 4) {
        #ifndef NO_WOLFSSL_ALLOC_ALIGN
            byte* tmp;
            WOLFSSL_MSG("Hc128Process unaligned");

            tmp = (byte*)XMALLOC(msglen, ctx->heap, DYNAMIC_TYPE_TMP_BUFFER);
            if (tmp == NULL) return MEMORY_E;

            XMEMCPY(tmp, input, msglen);
            DoProcess(ctx, tmp, tmp, msglen);
            XMEMCPY(output, tmp, msglen);

            XFREE(tmp, ctx->heap, DYNAMIC_TYPE_TMP_BUFFER);

            return 0;
        #else
            return BAD_ALIGN_E;
        #endif
    }
#endif /* XSTREAM_ALIGN */

    return DoProcess(ctx, output, input, msglen);
}


#else  /* HAVE_HC128 */


#ifdef _MSC_VER
    /* 4206 warning for blank file */
    #pragma warning(disable: 4206)
#endif


#endif /* HAVE_HC128 */
