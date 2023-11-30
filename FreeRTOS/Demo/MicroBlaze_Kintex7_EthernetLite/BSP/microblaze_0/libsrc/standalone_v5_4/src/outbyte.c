#include "xparameters.h"
#include "xuartlite_l.h"

#ifdef __cplusplus
extern "C" {
#endif
void outbyte(char c); 

#ifdef __cplusplus
}
#endif 

void outbyte(char c) {
	 XUartLite_SendByte(STDOUT_BASEADDRESS, c);
}
