#define TESTAPP_GEN

/* $Id: intc_header.h,v 1.1 2007/05/15 07:08:08 mta Exp $ */


#include "xbasic_types.h"
#include "xstatus.h"

XStatus IntcSelfTestExample(Xuint16 DeviceId);
XStatus IntcInterruptSetup(XIntc *IntcInstancePtr, Xuint16 DeviceId);


