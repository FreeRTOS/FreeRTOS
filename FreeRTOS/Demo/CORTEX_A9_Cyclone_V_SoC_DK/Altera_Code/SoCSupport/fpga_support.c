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

#include "alt_fpga_manager.h"
#include "fpga_support.h"

#define printf( ... )

ALT_STATUS_CODE fpga_init(void) {

	 // Program the FPGA
	uint32_t status = ALT_E_SUCCESS;
	uint32_t i;

	        // This is the symbol name for the SOF file contents linked in.
	        extern char _binary_soc_system_dc_rbf_start;
	        extern char _binary_soc_system_dc_rbf_end;

	        // Use the above symbols to extract the FPGA image information.
	        const char *   fpga_image      = &_binary_soc_system_dc_rbf_start;
	        const uint32_t fpga_image_size = &_binary_soc_system_dc_rbf_end - &_binary_soc_system_dc_rbf_start;

	        // Trace the FPGA image information.
	        printf("INFO: FPGA Image binary at %p.\n", fpga_image);
	        printf("INFO: FPGA Image size is %u bytes.\n", (unsigned int)fpga_image_size);

	        // Try the full configuration a few times.
	        const uint32_t full_config_retry = 5;
	        for (i = 0; i < full_config_retry; ++i)
	        {
	            status = alt_fpga_configure(fpga_image, fpga_image_size);
	            if (status == ALT_E_SUCCESS)
	            {
	                printf("INFO: alt_fpga_configure() successful on the %u of %u retry(s).\n",
	                       (unsigned int)(i + 1),
	                       (unsigned int)full_config_retry);
	                break;
	            }
	        }


	    if (status == ALT_E_SUCCESS)
	    {
	        printf("INFO: Setup of FPGA successful.\n\n");
	    }
	    else
	    {
	        printf("ERROR: Setup of FPGA return non-SUCCESS %d.\n\n", (int)status);
	    }

	    return status;
}
/* md5sum:e268b2157060033c39e9ea2c5068165f 2013-09-28 20:48:16 */
