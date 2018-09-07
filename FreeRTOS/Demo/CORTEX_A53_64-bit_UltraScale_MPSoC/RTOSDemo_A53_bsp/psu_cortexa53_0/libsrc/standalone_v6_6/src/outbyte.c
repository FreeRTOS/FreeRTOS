#include "xparameters.h"
#include "xuartps_hw.h"

#ifdef __cplusplus
extern "C" {
#endif
void outbyte(char c); 

#ifdef __cplusplus
}
#endif 

void outbyte(char c) {
	 XUartPs_SendByte(STDOUT_BASEADDRESS, c);
}
