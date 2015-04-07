 #ifndef XIL_PRINTF_H
 #define XIL_PRINTF_H

#ifdef __cplusplus
extern "C" {
#endif

#include <ctype.h>
#include <string.h>
#include <stdarg.h>
#include "xparameters.h"
#include "xil_types.h"

/*----------------------------------------------------*/
/* Use the following parameter passing structure to   */
/* make xil_printf re-entrant.                        */
/*----------------------------------------------------*/

struct params_s;


/*---------------------------------------------------*/
/* The purpose of this routine is to output data the */
/* same as the standard printf function without the  */
/* overhead most run-time libraries involve. Usually */
/* the printf brings in many kilobytes of code and   */
/* that is unacceptable in most embedded systems.    */
/*---------------------------------------------------*/

typedef char* charptr;
typedef int (*func_ptr)(int c);

/*                                                   */
void padding( const int l_flag, struct params_s *par);
void outs( charptr lp, struct params_s *par);
void outnum( const long n, const long base, struct params_s *par);
int getnum( charptr* linep);
void xil_printf( const char *ctrl1, ...);
void print( const char *ptr);
void outbyte (char);
char inbyte(void);

#ifdef __cplusplus
}
#endif

#endif	/* end of protection macro */
