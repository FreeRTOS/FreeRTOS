/******************************************************************************
*
* Copyright (C) 2009 - 2014 Xilinx, Inc.  All rights reserved.
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

/* read.c -- read bytes from a input device.
 */

#include "xparameters.h"
#include "xil_printf.h"

#ifdef __cplusplus
extern "C" {
	int _read (int fd, char* buf, int nbytes);
}
#endif

/*
 * read  -- read bytes from the serial port. Ignore fd, since
 *          we only have stdin.
 */
int
read (int fd, char* buf, int nbytes)
{
#ifdef STDIN_BASEADDRESS
  int i = 0;

  (void)fd;
  for (i = 0; i < nbytes; i++) {
    *(buf + i) = inbyte();
    if ((*(buf + i) == '\n' || *(buf + i) == '\r'))
    {
        i++;
        break;
    }
  }

  return (i);
#else
  (void)fd;
  (void)buf;
  (void)nbytes;
  return 0;
#endif
}

int
_read (int fd, char* buf, int nbytes)
{
#ifdef STDIN_BASEADDRESS
  int i = 0;

  (void)fd;
  for (i = 0; i < nbytes; i++) {
    *(buf + i) = inbyte();
    if ((*(buf + i) == '\n' || *(buf + i) == '\r'))
    {
        i++;
        break;
    }
  }

  return (i);
#else
  (void)fd;
  (void)buf;
  (void)nbytes;
  return 0;
#endif
}
