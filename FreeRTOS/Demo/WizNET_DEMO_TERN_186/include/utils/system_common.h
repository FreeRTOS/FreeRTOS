#ifndef _SYSTEM_COMMON_H_
#define _SYSTEM_COMMON_H_

typedef unsigned char UCHAR8;
typedef unsigned int  UINT16;

#define RETURN_OK                       0    // Non-zero return values are always
                                             // error values.
#define RETURN_ILLEGAL                  1    // Some sort of illegal argument.
#define RETURN_MEM                      2    // Out of memory space.

#endif // _SYSTEM_COMMON_H_