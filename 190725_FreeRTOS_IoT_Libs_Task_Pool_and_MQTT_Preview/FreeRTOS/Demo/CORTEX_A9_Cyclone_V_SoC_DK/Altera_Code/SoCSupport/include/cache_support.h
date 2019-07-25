/******************************************************************************
*
* Copyright 2013 Altera Corporation. All Rights Reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*
* 1. Redistributions of source code must retain the above copyright notice,
* this list of conditions and the following disclaimer.
*
* 2. Redistributions in binary form must reproduce the above copyright notice,
* this list of conditions and the following disclaimer in the documentation
* and/or other materials provided with the distribution.
*
* 3. The name of the author may not be used to endorse or promote products
* derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR
* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO
* EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
* OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
* INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
* CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
* IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
* OF SUCH DAMAGE.
*
******************************************************************************/

#ifndef CACHE_SUPPORT_H_
#define CACHE_SUPPORT_H_

#include "hwlib.h"

#define ALT_MPUL2_AUX_CONTROL_OFST          0x104
#define ALT_MPUL2_TAG_RAM_CONTROL_OFST      0x108
#define ALT_MPUL2_DATA_RAM_CONTROL_OFST     0x10c

#define ALT_MPUL2_AUX_CONTROL_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_AUX_CONTROL_OFST))
#define ALT_MPUL2_TAG_RAM_CONTROL_ADDR      ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_TAG_RAM_CONTROL_OFST))
#define ALT_MPUL2_DATA_RAM_CONTROL_ADDR     ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_DATA_RAM_CONTROL_OFST))

#define ALT_MPUL2_TAG_RAM_CONTROL_VALUE      0x00000000
#define ALT_MPUL2_DATA_RAM_CONTROL_VALUE     0x00000010

#define SHARED_ATTRIBUTE_OVERRIDE_ENABLE_MASK 0x00400000

ALT_STATUS_CODE cache_init(void);
ALT_STATUS_CODE cache_uninit(void);
void enable_shared_attribute_override_enable(void);
void configure_L2_ram_latency(void);

#endif /* CACHE_SUPPORT_H_ */
/* md5sum:58fb245f969aec44340df388edf9806b 2013-09-28 20:48:16 */
