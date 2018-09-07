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
* Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.    
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name	   : platform.h
* Description  : The user chooses which MCU and board they are developing for in this file. If the board you are using
*                is not listed below, please add your own or use the default 'User Board'.
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 30.11.2011 1.00     First Release
*         : 13.01.2012 1.10     Moved from having platform defined using macro defintion, to having platform defined
*                               by choosing an include path. This makes this file simpler and cleans up the issue
*                               where HEW shows all header files for all platforms under 'Dependencies'.
*         : 14.02.2012 1.20     Added RX210 BSP.
*         : 18.04.2012 1.30     Updated to v0.70 of FIT S/W Spec and v0.20 of FIT r_bsp Spec. This includes adding
*                               locking.c and locking.h in board folders. Also, r_bsp can now be configured through
*                               r_bsp_config.h.
*         : 26.06.2012 1.40     Added new options such as exception callbacks and the ability to choose your MCU using
*                               its part number in r_bsp_config.h. Moved mcu_info.h to the 'mcu' folder. Made an effort
*                               to remove any extra files that the user would need to touch. Removed the flash_options.c
*                               file and put its contents in vecttbl.c.
*         : 17.07.2012 1.50     Fixed bug with exception callback function names. Added BCLK_OUTPUT and SDCLK_OUTPUT 
*                               macro options in r_bsp_config.h. Added some extra code to handle exceptions in
*                               vecttbl.c. Added vecttbl.h so that user has prototypes for exception callbacks.
*         : 08.11.2012 1.60		Added RX111 BSP
***********************************************************************************************************************/

#ifndef _PLATFORM_H_
#define _PLATFORM_H_

/***********************************************************************************************************************
DEFINE YOUR SYSTEM - UNCOMMENT THE INCLUDE PATH FOR THE PLATFORM YOU ARE USING.
***********************************************************************************************************************/
/* RSKRX610 */
//#include "./board/rskrx610/r_bsp.h"

/* RSKRX62N */
//#include "./board/rskrx62n/r_bsp.h"

/* RSKRX62T */
//#include "./board/rskrx62t/r_bsp.h"

/* RDKRX62N */
//#include "./board/rdkrx62n/r_bsp.h"

/* RSKRX630 */
//#include "./board/rskrx630/r_bsp.h"

/* RSKRX63N */
//#include "./board/rskrx63n/r_bsp.h"

/* RDKRX63N */
//#include "./board/rdkrx63n/r_bsp.h"

/* RSKRX210 */
//#include "./board/rskrx210/r_bsp.h"

/* RSKRX111 */
#include "./board/rskrx111/r_bsp.h"

/* User Board - Define your own board here. */
//#include "./board/user/r_bsp.h"

/***********************************************************************************************************************
MAKE SURE AT LEAST ONE PLATFORM WAS DEFINED - DO NOT EDIT BELOW THIS POINT
***********************************************************************************************************************/
#ifndef PLATFORM_DEFINED
#error  "Error - No platform defined in platform.h!"
#endif

#endif /* _PLATFORM_H_ */

