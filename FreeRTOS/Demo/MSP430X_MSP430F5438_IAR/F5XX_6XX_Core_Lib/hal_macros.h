/*
 *  This macro is for use by other macros to form a fully valid C statement.
 */
#define st(x)      do { x } while (__LINE__ == -1)
