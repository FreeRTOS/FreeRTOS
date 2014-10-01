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

#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include "alt_16550_uart.h"
#include "uart0_support.h"


static ALT_16550_HANDLE_t g_uart0_handle;

ALT_STATUS_CODE uart0_init(void) {

	ALT_STATUS_CODE status;

    status = alt_16550_init(ALT_16550_DEVICE_SOCFPGA_UART0, 0, 0, &g_uart0_handle);

    status += alt_16550_line_config_set(&g_uart0_handle, ALT_16550_DATABITS_8, ALT_16550_PARITY_DISABLE, ALT_16550_STOPBITS_1);

    status += alt_16550_baudrate_set(&g_uart0_handle, ALT_16550_BAUDRATE_115200);

    status += alt_16550_fifo_enable(&g_uart0_handle);

    status += alt_16550_enable(&g_uart0_handle);

	return status;
}

ALT_STATUS_CODE uart0_uninit(void) {

	ALT_STATUS_CODE status;

	status += alt_16550_disable(&g_uart0_handle);

	status += alt_16550_fifo_disable(&g_uart0_handle);

    status += alt_16550_uninit(&g_uart0_handle);

	return status;
}

ALT_STATUS_CODE uart0_print(const char *in_str) {

	ALT_STATUS_CODE status = ALT_E_SUCCESS;
	int i;
    int len = strlen(in_str);

	uint32_t size_tx;
	if (status == ALT_E_SUCCESS) {
		status = alt_16550_fifo_size_get_tx(&g_uart0_handle, &size_tx);
	}

	for (i = 0; i < 1000; ++i)
	{
		if (status != ALT_E_SUCCESS) {
			break;
		}

		if (len == 0) {
			break;
		}

		// Wait for the THRE line status
		int j = 1000000;
		while (--j) {
			uint32_t line_status = 0;
			status = alt_16550_line_status_get(&g_uart0_handle, &line_status);
			if (status != ALT_E_SUCCESS) {
				break;
			}
			if (line_status & (ALT_16550_LINE_STATUS_THRE | ALT_16550_LINE_STATUS_TEMT)) {
				break;
			}
		}
		if (j == 0) {
			status = ALT_E_TMO;
		}

		uint32_t level_tx;

		if (status == ALT_E_SUCCESS) {
			status = alt_16550_fifo_level_get_tx(&g_uart0_handle, &level_tx);
		}

		if (status == ALT_E_SUCCESS) {
			uint32_t size_write = MIN(len, size_tx - level_tx);
			status = alt_16550_fifo_write(&g_uart0_handle, in_str, size_write);
			if (status == ALT_E_SUCCESS) {
				len -= size_write;
				in_str += size_write;
			}
		}
	}

	return status;
}

int uart0_printf(const char *fmt, ...) {

	ALT_STATUS_CODE status = ALT_E_SUCCESS;
	int len = 0;
	char buffer[1024];

	va_list  vl;
	va_start(vl, fmt);
	len = vsnprintf(buffer, sizeof(buffer), fmt, vl);
	va_end(vl);

	if(len >= sizeof(buffer)) {

		buffer[sizeof(buffer) - 1] = '\0';

		status = uart0_print(buffer);
		if( status != ALT_E_SUCCESS)
			return status;

		status = uart0_print("\r\nERROR: uart0_printf_buffer overflow...\r\n");
		if( status != ALT_E_SUCCESS)
			return status;

	} else {
		status = uart0_print(buffer);
		if( status != ALT_E_SUCCESS)
			return status;
	}

	return len;
}

int uart0_getc(void) {

	ALT_STATUS_CODE status = ALT_E_SUCCESS;
	int ret_val = EOF;

	uint32_t level;
	status = alt_16550_fifo_level_get_rx(&g_uart0_handle, &level);
	if(status != ALT_E_SUCCESS)
		return ret_val;

	if(level > 0) {
		char buffer;
		status = alt_16550_fifo_read(&g_uart0_handle, &buffer, 1);
		if(status != ALT_E_SUCCESS)
			return ret_val;
		else
			return buffer;
	}

	return ret_val;
}
/* md5sum:3086bef986334caa60e4e70a63fba834 2013-09-28 20:48:16 */
