/******************************************************************************
*
* Copyright (C) 2007 - 2014 Xilinx, Inc.  All rights reserved.
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
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
* XILINX CONSORTIUM BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/

#ifndef __XTOPOLOGY_H_
#define __XTOPOLOGY_H_

#ifdef __cplusplus
extern "C" {
#endif

enum xemac_types { xemac_type_unknown = -1, xemac_type_xps_emaclite, xemac_type_xps_ll_temac, xemac_type_axi_ethernet, xemac_type_emacps };

struct xtopology_t {
	unsigned emac_baseaddr;
	enum xemac_types emac_type;
	unsigned intc_baseaddr;
	unsigned intc_emac_intr;	/* valid only for xemac_type_xps_emaclite */
	unsigned scugic_baseaddr; /* valid only for Zynq */
	unsigned scugic_emac_intr; /* valid only for GEM */
};

extern int xtopology_n_emacs;
extern struct xtopology_t xtopology[];

int xtopology_find_index(unsigned base);

#ifdef __cplusplus
}
#endif

#endif
