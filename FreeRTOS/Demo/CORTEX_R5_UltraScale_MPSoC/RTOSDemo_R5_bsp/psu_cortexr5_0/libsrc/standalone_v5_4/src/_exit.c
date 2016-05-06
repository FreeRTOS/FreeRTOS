/******************************************************************************
*
* Copyright (C) 2014 - 2015 Xilinx, Inc. All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
* XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/

#include <unistd.h>
#include "xil_types.h"

/*
 * _exit - Does not return.
 *
 * If R5 application runs in lock-step mode, the comparators are enabled by
 * boot code after resetting the debug logic. The debugger does not have access
 * while the R5 application is being run to avoid any intervention. After the
 * application runs, the debug logic need to be taken out of reset for the
 * debugger to gain access. Therefore the debug logic is enabled and
 * comparators are disabled in case of R5 running in lock-step mode with
 * debug logic reset in JTAG boot mode.
 */

#define RPU_GLBL_CNTL_REG	0xFF9A0000U
#define RPU_ERR_INJ_REG		0xFF9A0020U
#define RST_LPD_DBG_REG		0xFF5E0240U
#define BOOT_MODE_USER_REG	0xFF5E0200U

#define lock_step 			0x00000008U
#define fault_log_enable	0x00000101U
#define debug_reset 		0x00000032U
#define jtag_boot			0x0000000FU
__attribute__((weak)) void _exit (sint32 status)
{

	/*
	 * Enables the debug logic and disable the comparators
	 * when in JTAG boot mode and R5 is in lock-step mode
	 * if the fault log is enabled
	 */
	u32 debug_reg, err_inj_reg;
	if((Xil_In32(BOOT_MODE_USER_REG) & jtag_boot) == 0){
		if((Xil_In32(RPU_GLBL_CNTL_REG) & lock_step) == 0){
			if((Xil_In32(RPU_ERR_INJ_REG) & fault_log_enable) != 0) {
				if((Xil_In32(RST_LPD_DBG_REG) & debug_reset) != 0) {
					err_inj_reg = Xil_In32(RPU_ERR_INJ_REG);
					err_inj_reg = err_inj_reg & (~fault_log_enable);
					Xil_Out32(RPU_ERR_INJ_REG, err_inj_reg);

					debug_reg = Xil_In32(RST_LPD_DBG_REG);
					debug_reg = debug_reg & (~debug_reset);
					Xil_Out32(RST_LPD_DBG_REG, debug_reg);
				}
			}
		}
	}

  (void)status;
  while (1)
  {
     __asm__("wfi");
  }
}
