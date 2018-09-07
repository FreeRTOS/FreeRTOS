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

#include "alt_cache.h"
#include "socal/hps.h"
#include "socal/socal.h"
#include "cache_support.h"
//#include "boot_support.h"

ALT_STATUS_CODE cache_init(void) {

	ALT_STATUS_CODE status = ALT_E_SUCCESS;

	//
	// The 13.1 release of alt_cache.c does not appear to initialize the L2
	// cache latency registers properly so we'll do that here.
	//
	configure_L2_ram_latency();

	//
	// Enable the shared attribute override enable bit in the L2 aux control register
	//
	enable_shared_attribute_override_enable();

	status = alt_cache_system_enable();
//	BOOT_CHECK_STATUS;

	return status;
}

ALT_STATUS_CODE cache_uninit(void) {

	return alt_cache_system_disable();
}

void enable_shared_attribute_override_enable(void) {

    bool l2_enabled = alt_cache_l2_is_enabled();

    if (l2_enabled)
    {
        alt_cache_l2_disable();
    }

    alt_setbits_word(ALT_MPUL2_AUX_CONTROL_ADDR, SHARED_ATTRIBUTE_OVERRIDE_ENABLE_MASK);

    if (l2_enabled)
    {
        alt_cache_l2_enable();
    }
}

void configure_L2_ram_latency(void) {

    bool l2_enabled = alt_cache_l2_is_enabled();

    if (l2_enabled)
    {
        alt_cache_l2_disable();
    }

	alt_write_word(ALT_MPUL2_TAG_RAM_CONTROL_ADDR, ALT_MPUL2_TAG_RAM_CONTROL_VALUE);
	alt_write_word(ALT_MPUL2_DATA_RAM_CONTROL_ADDR, ALT_MPUL2_DATA_RAM_CONTROL_VALUE);

    if (l2_enabled)
    {
        alt_cache_l2_enable();
    }
}
/* md5sum:ec3ba66ee5cff385248a93a050de2432 2013-09-28 20:48:16 */
