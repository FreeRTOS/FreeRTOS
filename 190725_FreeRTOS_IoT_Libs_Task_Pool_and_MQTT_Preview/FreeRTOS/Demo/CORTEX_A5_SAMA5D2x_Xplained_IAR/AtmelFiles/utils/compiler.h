#ifndef _COMPILER_H_
#define _COMPILER_H_

#define _CC_PRAGMA(x) _Pragma(#x)

#define PACK_SET(alignment) _CC_PRAGMA(pack(alignment))
#define PACK_RESET()        _CC_PRAGMA(pack())

#if defined(__ICCARM__)
	#define WEAK __weak
	#define CONSTRUCTOR
	#define SECTION(a) _CC_PRAGMA(location = a)
	#define ALIGNED(a) _CC_PRAGMA(data_alignment = a)
#elif defined(__GNUC__)
	#define WEAK __attribute__((weak))
	#define CONSTRUCTOR __attribute__((constructor))
	#define SECTION(a) __attribute__((__section__(a)))
	#define ALIGNED(a) __attribute__((__aligned__(a)))
#else
	#error Unknown compiler!
#endif

#if defined(__ICCARM__)
	#define DMB()  asm("dmb")
	#define DSB()  asm("dsb")
	#define ISB()  asm("isb")
	#define COMPILER_BARRIER()
#elif defined(__GNUC__)
	#define DMB()  asm("dmb":::"memory")
	#define DSB()  asm volatile ("dsb":::"memory")
	#define ISB()  asm volatile ("isb":::"memory")
	#define COMPILER_BARRIER()  asm volatile ("":::"memory")
#else
	#error Unknown compiler!
#endif

#ifndef NULL
	#define NULL ((void*)0)
#endif

#define ROUND_UP_MULT(x,m) (((x) + ((m)-1)) & ~((m)-1))

#define ROUND_INT_DIV(n,d) ((2 * (n) + (d)) / (2 * (d)))

#define ARRAY_SIZE(x) (sizeof ((x)) / sizeof(*(x)))

#define _STRINGY_EXPAND(x) #x
#define STRINGIFY(x) _STRINGY_EXPAND(x)

#if defined(__GNUC__) && \
		(__GNUC__ > 4 || (__GNUC__ == 4 && __GNUC_MINOR__ > 8))
	#define SWAP(a, b) do {		\
		__auto_type _swp = (a);	\
		(a) = (b);		\
		(b) = _swp; } while (0)
#else
	/* The compiler will replace memcpy calls with direct assignations */
	#define SWAP(a, b) do {                                                \
		uint8_t _swp[sizeof(a) == sizeof(b) ? (signed)sizeof(a) : -1]; \
		memcpy(_swp, &(a), sizeof(a));                                 \
		memcpy(&(a), &(b), sizeof(a));                                 \
		memcpy(&(b), _swp, sizeof(a)); } while(0)
#endif

#define BIG_ENDIAN_TO_HOST(x) (((x) & 0xFF) << 24) | (((x) & 0xFF00) << 8) \
		| (((x) & 0xFF0000) >> 8) | (((x) & 0xFF000000) >> 24)

#endif /* _COMPILER_H_ */
