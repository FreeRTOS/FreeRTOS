#
# Copyright (C) 2015 Xilinx, Inc.
#
# This file is part of the FreeRTOS port.
#
# FreeRTOS is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License (version 2) as published by the
# Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.
#
# NOTE: The modification to the GPL is included to allow you to distribute a
# combined work that includes FreeRTOS without being obliged to provide the
# source code for proprietary components outside of the FreeRTOS kernel.
#
# FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
# WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE.  Full license text is available on the following
# link: http://www.freertos.org/a00114.html
#

PARAMETER VERSION = 2.2.0

BEGIN OS
 PARAMETER OS_NAME = freertos822_xilinx
 PARAMETER STDIN =  *
 PARAMETER STDOUT = *
 PARAMETER SYSTMR_SPEC = true
 PARAMETER SYSTMR_DEV = *
 PARAMETER SYSINTC_SPEC = *
END
