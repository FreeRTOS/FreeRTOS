#define TESTAPP_GEN

/* $Id: uartlite_intr_header.h,v 1.1 2007/05/15 07:00:27 mta Exp $ */


#include "xbasic_types.h"
#include "xstatus.h"

XStatus UartLiteIntrExample(XIntc* IntcInstancePtr, \
                            XUartLite* UartLiteInstancePtr, \
                            Xuint16 UartLiteDeviceId, \
                            Xuint16 UartLiteIntrId);


