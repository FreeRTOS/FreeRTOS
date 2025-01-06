/*
* Percepio Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The interface for trace utility functions.
*/

#ifndef TRC_UTILITY_H
#define TRC_UTILITY_H

/* These will align a size up or down to a specific alignment */
#define TRC_ALIGN_CEIL(size, alignment) ((((size) + (alignment) - 1) / (alignment)) * (alignment))
#define TRC_ALIGN_FLOOR(size, alignment) (((size) / (alignment)) * (alignment))

#ifndef TRC_MEMCPY
#define TRC_MEMCPY(dst, src, size) \
    { \
        uint32_t __i; \
        for (__i = 0; __i < size; __i++) { \
            ((uint8_t*)(dst))[__i] = ((uint8_t*)(src))[__i]; \
        } \
    }
#endif

#define TRC_STRCAT(dst, dst_size, pDstLength, src) \
	{ \
		TraceUnsignedBaseType_t uxTRC_STRCAT_INDEX = 0; \
		while (*(pDstLength) < (dst_size)) \
		{ \
			dst[*(pDstLength)] = src[uxTRC_STRCAT_INDEX]; \
			if (dst[*(pDstLength)] == 0) \
				break; \
			(*(pDstLength))++; \
			uxTRC_STRCAT_INDEX++; \
		} \
	}
#if (defined(TRC_CFG_USE_GCC_STATEMENT_EXPR) && TRC_CFG_USE_GCC_STATEMENT_EXPR == 1) || \
	(!defined(TRC_CFG_USE_GCC_STATEMENT_EXPR) && (__GNUC__ || __IAR_SYSTEMS_ICC__ || __TI_ARM__))
	#define TRC_COMMA_EXPR_TO_STATEMENT_EXPR_1(e1)								__extension__({e1;})
	#define TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(e1, e2)							__extension__({e1; e2;})
	#define TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3(e1, e2, e3)						__extension__({e1; e2; e3;})
	#define TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4(e1, e2, e3, e4)					__extension__({e1; e2; e3; e4;})
	#define TRC_COMMA_EXPR_TO_STATEMENT_EXPR_5(e1, e2, e3, e4, e5)				__extension__({e1; e2; e3; e4; e5;})
	#define TRC_COMMA_EXPR_TO_STATEMENT_EXPR_6(e1, e2, e3, e4, e5, e6)			__extension__({e1; e2; e3; e4; e5; e6;})
	#define TRC_COMMA_EXPR_TO_STATEMENT_EXPR_7(e1, e2, e3, e4, e5, e6, e7)		__extension__({e1; e2; e3; e4; e5; e6; e7;})
	#define TRC_COMMA_EXPR_TO_STATEMENT_EXPR_8(e1, e2, e3, e4, e5, e6, e7, e8)	__extension__({e1; e2; e3; e4; e5; e6; e7; e8;})
#else
	#define TRC_COMMA_EXPR_TO_STATEMENT_EXPR_1(e1)								(e1)
	#define TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(e1, e2)							(e1, e2)
	#define TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3(e1, e2, e3)						(e1, e2, e3)
	#define TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4(e1, e2, e3, e4)					(e1, e2, e3, e4)
	#define TRC_COMMA_EXPR_TO_STATEMENT_EXPR_5(e1, e2, e3, e4, e5)				(e1, e2, e3, e4, e5)
	#define TRC_COMMA_EXPR_TO_STATEMENT_EXPR_6(e1, e2, e3, e4, e5, e6)			(e1, e2, e3, e4, e5, e6)
	#define TRC_COMMA_EXPR_TO_STATEMENT_EXPR_7(e1, e2, e3, e4, e5, e6, e7)		(e1, e2, e3, e4, e5, e6, e7)
	#define TRC_COMMA_EXPR_TO_STATEMENT_EXPR_8(e1, e2, e3, e4, e5, e6, e7, e8)	(e1, e2, e3, e4, e5, e6, e7, e8)
#endif

#endif /* TRC_UTILITY_H */
