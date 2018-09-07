#ifndef XDEBUG  /* prevent circular inclusions */
#define XDEBUG  /* by using protection macros */

#if defined(DEBUG) && !defined(NDEBUG)

#ifndef XDEBUG_WARNING
#define XDEBUG_WARNING
#warning DEBUG is enabled
#endif

int printf(const char *format, ...);

#define XDBG_DEBUG_ERROR             0x00000001U    /* error  condition messages */
#define XDBG_DEBUG_GENERAL           0x00000002U    /* general debug  messages */
#define XDBG_DEBUG_ALL               0xFFFFFFFFU    /* all debugging data */

#define xdbg_current_types (XDBG_DEBUG_GENERAL)

#define xdbg_stmnt(x)  x

#define xdbg_printf(type, ...) (((type) & xdbg_current_types) ? printf (__VA_ARGS__) : 0)


#else /* defined(DEBUG) && !defined(NDEBUG) */

#define xdbg_stmnt(x)

#define xdbg_printf(...)

#endif /* defined(DEBUG) && !defined(NDEBUG) */

#endif /* XDEBUG */
