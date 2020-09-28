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
* File Name    : platform.h
* Description  : The user chooses which MCU and board they are developing for in this file. If the board you are using
*                is not listed below, please add your own or use the default 'User Board'.
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 30.11.2011 1.00     First Release
*         : 13.01.2012 1.10     Moved from having platform defined using macro definition, to having platform defined
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
*         : 09.08.2012 1.60     Added IO_LIB_ENABLE macro to r_bsp_config_reference.h.
*         : 14.11.2012 1.70     Added RSKRX62G, RSKRX63T, and RSKRX111 support.
*         : 28.11.2012 2.00     Updated to be compliant with v1.00 r_bsp specification.
*         : 21.01.2013 2.10     Added RSKRX63T_144PIN support.
*         : 10.05.2013 2.20     Added new packages and memory variants to RX210. All iodefine.h files have been updated
*                               to latest revisions. On reset, all MCUs will now initialize non-bonded out pins to
*                               reduce current draw. r_bsp_common.c and .h files were added to support functionality
*                               common to all BSPs. cpu.c and cpu.h files were added to all MCU groups to support
*                               CPU functions such as enabling/disabling interrupts, setting the IPL, and controlling
*                               register protection. mcu_init.c and mcu_init.h were add to all MCU groups to support
*                               initialization functions that are common to a MCU group such as non-bonded pin init.
*                               Choosing MCU endian has been removed from r_bsp_config.h and is now automatically
*                               set based on compiler macros. RX-C, IAR, and GCC endian macros are supported. RX210
*                               now has support for choosing HOCO frequency. All r_bsp_config.h files now have macro
*                               for defining Vcc which is needed by some FIT modules. IRQ locks were added for all
*                               MCU groups. BSP_PACKAGE_PINS macro was added to mcu_info.h which defines number of pins
*                               for the currently chosen package. RX111 and RX210 now have the option of using the
*                               r_cgc_rx module for clock management based on BSP_CFG_USE_CGC_MODULE macro in
*                               r_bsp_config.h.
*         : 31.05.2013 2.21     Added latest iodefine.h files for RX111 (v0.9a), RX630 (v1,50a), and RX63N (v1.60). Also
*                               added 'doc' folder to root of r_bsp. Currently the only the document in there is the
*                               preliminary version of the r_bsp User's Manual. For RX210, the ability to choose chip
*                               version C was added to its r_bsp_config.h file.
*         : 01.07.2013 2.30     Removed RSPI pin setup in RSKRX111 which caused excess current draw in low power
*                               modes. Changed FIT_NO_PTR and FIT_NO_FUNC macros to 0x10000000 which works for all 
*                               RX MCUs. Added ability for user to use 1 or 2 stacks for RX MCUs. Added new interrupt
*                               handling features which allows for interrupt callback registration. This feature allows
*                               all interrupts that map to the NMI vector to be used and replaces the static callback
*                               definitions that were in r_bsp_config.h previously. RX111 information has been updated
*                               according to v1.00 HW manual. This includes support for 40-pin packages. All compiler
*                               messages and warnings for lowsrc.c have been cleaned up. Non-existent port init has
*                               been moved to end of hardware_setup() to ensure user does not overwrite the settings.
*                               Added blank lines between clock macros in r_bsp_config.h to aid in readability. Added
*                               '(void *)' cast to FIT_NO_PTR to remove compiler warnings. All r_bsp.h files now include
*                               r_bsp_common.h which has common includes (stdint.h, stddef.h, & stdbool.h) and uses
*                               r_typedefs.h when C99 is not available. RX111 and RX210 MCUs have the option of using
*                               the r_cgc_rx module for clock management. When this is used, the clock info macros in 
*                               mcu_info.h (e.g. BSP_ICLK_HZ) will now make calls to the r_cgc_rx module instead of 
*                               providing static info. For debug console output, lowlvl.src was replaced by lowlvl.c
*                               (assembly converted to C source).
*         : 10.02.2014 2.40     Added support for the RSKRX110, RPBRX111, RSKRX220, and HSBRX21AP. Made sure
*                               in hwsetup.c files that the PMR registers are set after the MPC registers. Replaced
*                               use of stdint.h, stdbool.h, and stddef.h with platform.h to remove compiler warnings.
*                               Removed includes for machine.h since it is compiler specific and replaced with
*                               platform.h. Fixed bug in resetprg.c for many boards where LOCO was not being turned off
*                               when it was not being used. RX100 code now uses the oscillation stabilization flags
*                               instead of SW delay loop. Changed size_t to unsigned long. Defined PRC2 in register
*                               protection section for RX111. Fixed bug in non-existent pin setup for RX111. No
*                               platform is chosen by default (used to be the RSKRX111). This makes it easier to
*                               understand the problem when you build a new project and have not selected your platform.
*         : 24.03.2014 2.50     Added support for the RSKRX64M.
*         : 16.06.2014 2.60     Added version control for r_bsp_config.h Two user callback functions may now be 
*                               configured allowing callbacks from PowerON_Reset_PC() for warm start detection.
*                               Stdio charget() and charput() functions may now be redirected to user defined functions.
*                               Added support for RSKRX631 and RDKRX631.
*         : 05.08.2014 2.70     Added support for RSKRX113.
*         : 29.09.2014 2.80     Added support for RSKRX71M.
*         : 22.12.2014 2.90     Added support for RSKRX231.
*         : 30.09.2015 3.00     Added support for RSSKRX23T and RSKRX23T.
*         : 30.09.2015 3.01     Fix for RSKRX231 and RSKRX23T(RSSKRX23T).
*         : 01.12.2015 3.10     Added support for RSKRX130.
*         : 01.02.2016 3.20     Added support for RSKRX24T.
*         : 29.02.2016 3.30     Added support for RSKRX230.
*         : 01.10.2016 3.40     Added support for RSKRX65N.
*         : 22.08.2016 3.50     Added support for RSKRX24U.
*         : 15.05.2017 3.60     Added support for RSKRX65N-2MB.
*                               Added support for GENERIC_RX65N.
*                               Added support for RSKRX130-512KB.
*         : 01.11.2017 3.70     Added support for GENERIC_RX130.
*                               Added support for GENERIC_RX110.
*                               Added support for GENERIC_RX111.
*                               Added support for GENERIC_RX113.
*                               Added support for GENERIC_RX230.
*                               Added support for GENERIC_RX231.
*                               Added support for GENERIC_RX23T.
*                               Added support for GENERIC_RX24T.
*                               Added support for GENERIC_RX24U.
*                               Added support for GENERIC_RX64M.
*                               Added support for GENERIC_RX71M.
*                               Added support for ENVISIONRX65N.
*         : 01.11.2017 3.71     Corrected typo in Rev3.70 BSP.
*         : 01.07.2018 3.80     Added support for TARGETBOARDRX65N.
*                               Added support for TARGETBOARDRX231.
*                               Added support for TARGETBOARDRX130.
*         : 27.07.2018 3.90     Added support for GENERIC_RX66T.
*                               Deleted the below board folders, since other boards can all be substituted with 
*                               GENERIC_RXxxx.
*                               - RSKRX64M, RSKRX65N, RSKRX65N_2MB, TARGETBOARDRX65N, ENVISIONRX65N, RSKRX71M, 
*                                 RSKRX230, RSKRX231, TARGETBOARDRX231, RSKRX110, RSKRX111, RPBRX111, RSKRX113, 
*                                 RSKRX130, RSKRX130_512KB, and TARGETBOARDRX130
*         : 31.10.2018 4.00     Added support for GENERIC_RX72T.
*                               Deleted the below board folders, since other boards can all be substituted with 
*                               GENERIC_RXxxx.
*                               - RSSKRX23T, RSKRX23T, RSKRX24T, and RSKRX24U
*         : 28.02.2019 5.00     Deleted the below board folders.
*                               - RSKRX610, RSKRX62N, RSKRX62T, RSKRX62G, RDKRX62N, RSKRX630, RSKRX631, RSKRX63T_64PIN,
*                                 RSKRX63T_144PIN, RDKRX63N, RDKRX631, RSKRX210, HSBRX21AP and RSKRX220
*         : 29.03.2019 5.10     Added support for GENERIC_RX23W.
*         : 08.04.2019 5.20     Added support for GENERIC_RX72M.
*         : 26.07.2019 5.30     Added support for GENERIC_RX13T.
*         : 31.07.2019 5.40     Added support for GENERIC_RX23E-A.
*         : 08.10.2019 5.50     Added support for GENERIC_RX72N, and GENERIC_RX66N.
*                               Deleted the board folders of RSKRX63N.
***********************************************************************************************************************/

/* Multiple inclusion prevention macro */
#ifndef PLATFORM_H
#define PLATFORM_H

/***********************************************************************************************************************
DEFINE YOUR SYSTEM - UNCOMMENT THE INCLUDE PATH FOR THE PLATFORM YOU ARE USING.
***********************************************************************************************************************/
/* GENERIC_RX64M */
//#include "./board/generic_rx64m/r_bsp.h"

/* GENERIC_RX65N */
//#include "./board/generic_rx65n/r_bsp.h"

/* GENERIC_RX66N */
//#include "./board/generic_rx66n/r_bsp.h"

/* GENERIC_RX66T */
//#include "./board/generic_rx66t/r_bsp.h"

/* GENERIC_RX71M */
//#include "./board/generic_rx71m/r_bsp.h"

/* GENERIC_RX72M */
//#include "./board/generic_rx72m/r_bsp.h"

/* GENERIC_RX72N */
#include "./board/generic_rx72n/r_bsp.h"

/* GENERIC_RX72T */
//#include "./board/generic_rx72t/r_bsp.h"

/* GENERIC_RX230 */
//#include "./board/generic_rx230/r_bsp.h"

/* GENERIC_RX231 */
//#include "./board/generic_rx231/r_bsp.h"

/* GENERIC_RX23E-A */
//#include "./board/generic_rx23e-a/r_bsp.h"

/* GENERIC_RX23T */
//#include "./board/generic_rx23t/r_bsp.h"

/* GENERIC_RX23W */
//#include "./board/generic_rx23w/r_bsp.h"

/* GENERIC_RX24T */
//#include "./board/generic_rx24t/r_bsp.h"

/* GENERIC_RX24U */
//#include "./board/generic_rx24u/r_bsp.h"

/* GENERIC_RX111 */
//#include "./board/generic_rx111/r_bsp.h"

/* GENERIC_RX110 */
//#include "./board/generic_rx110/r_bsp.h"

/* GENERIC_RX113 */
//#include "./board/generic_rx113/r_bsp.h"

/* GENERIC_RX130 */
//#include "./board/generic_rx130/r_bsp.h"

/* GENERIC_RX13T */
//#include "./board/generic_rx13t/r_bsp.h"

/* User Board - Define your own board here. */
//#include "./board/user/r_bsp.h"

/***********************************************************************************************************************
MAKE SURE AT LEAST ONE PLATFORM WAS DEFINED - DO NOT EDIT BELOW THIS POINT
***********************************************************************************************************************/
#ifndef PLATFORM_DEFINED
#error  "Error - No platform defined in platform.h!"
#endif

#endif /* PLATFORM_H */

