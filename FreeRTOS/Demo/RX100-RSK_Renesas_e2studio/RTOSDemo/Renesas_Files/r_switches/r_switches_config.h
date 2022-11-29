/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products. No
* other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED. TO THE MAXIMUM
* EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES
* SHALL BE LIABLE FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS
* SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability of
* this software. By using this software, you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2011 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : r_switches_config.c
* Description  : Configures the switches code
************************************************************************************************************************
* History : DD.MM.YYYY Version Description
*         : 17.01.2012 1.00    First Release
*         : 17.02.2012 1.10    Added RSKRX210 support.
*         : 08.03.2012 1.20    Added GetVersion() function (though it's really a macro).
*         : 04.06.2012 1.30    Code can now be interrupt or poll driven.
***********************************************************************************************************************/
#ifndef SWITCHES_CONFIG_HEADER_FILE
#define SWITCHES_CONFIG_HEADER_FILE

/***********************************************************************************************************************
Configuration Options
***********************************************************************************************************************/
/* This macro sets whether interrupts or polling is used for detecting switch presses. The benefit of using interrupts
   is that no extra processing is used for polling and the use of a system timer tick is not a requirement. The downside
   of using interrupts is that callback functions are called from within an interrupt so if your ISR is long then it can
   degrade the real-time response of your system. The benefit of polling is that functions are called at the application
   level and debouncing is supported. The downside to polling is that your system must call the R_SWITCHES_Update() on a
   regular basis which requires extra processing.

   0 = Use interrupts
   1 = Use polling
    */
#define SWITCHES_DETECTION_MODE     (0)

/* The definition for these macros should be the name of the function that you want called when a switch is
   pressed. It is very important that the user recognize that this function will be called from  the interrupt service
   routine. This means that code inside of the function should be kept short to ensure it does not hold up the rest of
   the system.

   Example: If SW1_CALLBACK_FUNCTION is defined to be sw1_callback then the sw1_callback function will be called when
   switch 1 is pressed.
*/
#define SW1_CALLBACK_FUNCTION       (vButtonInterruptCallback)
#define SW2_CALLBACK_FUNCTION       (vButtonInterruptCallback)
#define SW3_CALLBACK_FUNCTION       (vButtonInterruptCallback)

#endif /* SWITCHES_CONFIG_HEADER_FILE */
