#define TESTAPP_GEN

/* $Id: gpio_header.h,v 1.1 2007/05/15 06:49:42 mta Exp $ */


#include "xbasic_types.h"
#include "xstatus.h"

XStatus GpioOutputExample(Xuint16 DeviceId, Xuint32 GpioWidth);
XStatus GpioInputExample(Xuint16 DeviceId, Xuint32 *DataRead);


