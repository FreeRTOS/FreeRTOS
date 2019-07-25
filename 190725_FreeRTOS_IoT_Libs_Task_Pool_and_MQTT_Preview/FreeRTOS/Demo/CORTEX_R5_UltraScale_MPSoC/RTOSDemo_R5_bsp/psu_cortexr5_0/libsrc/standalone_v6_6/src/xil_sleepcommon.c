/******************************************************************************
*
* Copyright (C) 2017 Xilinx, Inc.  All rights reserved.
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
/*****************************************************************************/
/**
*
*@file xil_sleepcommon.c
*
* This file contains the sleep API's
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who      Date     Changes
* ----- -------- -------- -----------------------------------------------
* 6.6 	srm  	 11/02/17 First release
* </pre>
******************************************************************************/


/***************************** Include Files *********************************/
#include "xil_io.h"
#include "sleep.h"

/****************************  Constant Definitions  *************************/


/*****************************************************************************/
/**
*
* This API gives delay in sec
*
* @param            seconds - delay time in seconds
*
* @return           none
*
* @note             none
*
*****************************************************************************/
 void sleep(unsigned int seconds)
 {
#if defined (ARMR5)
	sleep_R5(seconds);
#elif defined (__aarch64__) || defined (ARMA53_32)
	sleep_A53(seconds);
#elif defined (__MICROBLAZE__)
	sleep_MB(seconds);
#else
	sleep_A9(seconds);
#endif

 }

/****************************************************************************/
/**
*
* This API gives delay in usec
*
* @param            useconds - delay time in useconds
*
* @return           none
*
* @note             none
*
*****************************************************************************/
 void usleep(unsigned long useconds)
 {
#if defined (ARMR5)
	usleep_R5(useconds);
#elif defined (__aarch64__) || defined (ARMA53_32)
	usleep_A53(useconds);
#elif defined (__MICROBLAZE__)
	usleep_MB(useconds);
#else
	usleep_A9(useconds);
#endif

 }
