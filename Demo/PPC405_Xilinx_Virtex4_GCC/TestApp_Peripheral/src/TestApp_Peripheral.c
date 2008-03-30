/*
 *
 * Xilinx, Inc.
 * XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION "AS IS" AS A 
 * COURTESY TO YOU.  BY PROVIDING THIS DESIGN, CODE, OR INFORMATION AS
 * ONE POSSIBLE   IMPLEMENTATION OF THIS FEATURE, APPLICATION OR 
 * STANDARD, XILINX IS MAKING NO REPRESENTATION THAT THIS IMPLEMENTATION 
 * IS FREE FROM ANY CLAIMS OF INFRINGEMENT, AND YOU ARE RESPONSIBLE 
 * FOR OBTAINING ANY RIGHTS YOU MAY REQUIRE FOR YOUR IMPLEMENTATION
 * XILINX EXPRESSLY DISCLAIMS ANY WARRANTY WHATSOEVER WITH RESPECT TO 
 * THE ADEQUACY OF THE IMPLEMENTATION, INCLUDING BUT NOT LIMITED TO 
 * ANY WARRANTIES OR REPRESENTATIONS THAT THIS IMPLEMENTATION IS FREE 
 * FROM CLAIMS OF INFRINGEMENT, IMPLIED WARRANTIES OF MERCHANTABILITY 
 * AND FITNESS FOR A PARTICULAR PURPOSE.
 */

/*
 * Xilinx EDK 10.1 EDK_K.15
 *
 * This file is a sample test application
 *
 * This application is intended to test and/or illustrate some 
 * functionality of your system.  The contents of this file may
 * vary depending on the IP in your system and may use existing
 * IP driver functions.  These drivers will be generated in your
 * XPS project when you run the "Generate Libraries" menu item
 * in XPS.
 *
 * Your XPS project directory is at:
 *    C:\E\Dev\FreeRTOS\WorkingCopy2\Demo\PPC405_Xilinx_Virtex4_GCC\
 */


// Located in: ppc405_0/include/xparameters.h
#include "xparameters.h"

#include "xcache_l.h"

#include "xintc.h"
#include "xexception_l.h"
#include "intc_header.h"
#include "xuartlite.h"
#include "uartlite_header.h"
#include "uartlite_intr_header.h"
#include "xbasic_types.h"
#include "xgpio.h"
#include "gpio_header.h"

//====================================================

int main (void) {


   static XIntc intc;

   XCache_EnableICache(0x00000001);
   XCache_EnableDCache(0x00000001);
   static XUartLite RS232_Uart_UartLite;


   {
      XStatus status;
                        
//      status = IntcSelfTestExample(XPAR_XPS_INTC_0_DEVICE_ID);

   } 
	
   {
       XStatus Status;

//       Status = IntcInterruptSetup(&intc, XPAR_XPS_INTC_0_DEVICE_ID);

   }


   {
      XStatus status;
      
 //     status = UartLiteSelfTestExample(XPAR_RS232_UART_DEVICE_ID);
   }
        
   {
      XStatus Status;
//      Status = UartLiteIntrExample(&intc, &RS232_Uart_UartLite, \
//                                  XPAR_RS232_UART_DEVICE_ID, \
//                                  XPAR_XPS_INTC_0_RS232_UART_INTERRUPT_INTR);
   }


   {
      XStatus status;
      
      status = GpioOutputExample(XPAR_LEDS_4BIT_DEVICE_ID,4);
   }


   {
      XStatus status;
      
      status = GpioOutputExample(XPAR_LEDS_POSITIONS_DEVICE_ID,5);
   }

   XCache_DisableDCache();
   XCache_DisableICache();
   return 0;
}

