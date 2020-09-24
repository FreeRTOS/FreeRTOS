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
* Copyright (C) 2013 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : r_bsp_common.h
* Description  : Implements functions that apply to all r_bsp boards and MCUs.
***********************************************************************************************************************/
/**********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 06.05.2013 1.00     First Release
*         : 25.06.2013 1.10     Now contains standard includes (stdint.h, stdbool.h, etc) as well as include for
*                               r_typedefs.h when needed.
*         : 02.07.2013 1.11     Added #include for machine.h.
*         : 10.02.2014 1.12     Changed minor version to '40'.
*         : 24.03.2014 1.12     Changed minor version to '60'.
*         : 14.04.2014 1.12     Added typedef for fit_callback_t.
*         : 30.09.2015 1.13     Changed Major/Minor version to 3.00
*         : 30.09.2015 1.14     Changed Minor version to 3.01
*         : 01.12.2015 1.15     Changed Minor version to 3.10
*         : 01.02.2016 1.16     Changed Minor version to 3.20
*         : 29.02.2016 1.17     Changed Minor version to 3.30
*         : 13.04.2016 1.18     Changed Minor version to 3.31
*         : 01.10.2016 1.19     Changed Minor version to 3.40
*         : 04.11.2016 1.20     Changed Minor version to 3.50
*         : 15.05.2017 1.21     Changed Minor version to 3.60
*         : 01.11.2017 1.22     Changed Minor version to 3.70
*         : 01.12.2017 1.23     Changed Minor version to 3.71
*         : 01.07.2018 1.24     Changed Minor version to 3.80
*         : 27.07.2018 1.25     Changed Minor version to 3.90.
*         : 31.08.2018 1.26     Changed Minor version to 3.91.
*         : 31.10.2018 1.27     Changed Major/Minor version to 4.00.
*         : 11.01.2019 1.28     Changed Minor version to 4.01.
*         : 28.02.2019 1.29     Changed Major version to 5.00.
*                               Added the following macro definition.
*                                - INTERNAL_NOT_USED(p)
*                               Added support for GNUC and ICCRX.
*                               Fixed coding style.
*         : 29.03.2019 1.30     Changed Minor version to 5.10.
*         : 08.04.2019 1.31     Changed Minor version to 5.20.
*         : 23.07.2019 1.32     Changed Minor version to 5.21.
*         : 26.07.2019 1.33     Changed Minor version to 5.30.
*         : 31.07.2019 1.34     Changed Minor version to 5.40.
*         : 08.10.2019 1.35     Changed Minor version to 5.50.
*         : 10.12.2019 1.36     Changed Minor version to 5.51.
*         : 14.02.2020 1.37     Changed Minor version to 5.52.
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* C99 (or later) is necessary because r_rx_compiler.h uses Pragma operator and variadic macros.
 * This means that r_typedefs.h is not used in any case. */
#if !defined(__cplusplus) && !defined(CPPAPP)
/* All implementation is C99 (or later) */
#if defined(__STDC_VERSION__) && (__STDC_VERSION__ >= 199901L)
#include    <stdint.h>
#include    <stdbool.h>
#include    <stdio.h>
#include    <stddef.h>
#else
#error "This version of FIT needs C99 (or later)."
#endif
#else /* defined(__cplusplus) || defined(CPPAPP) */
/* Interface might be referred from C++ */
#include    <stdint.h>
#include    <stdbool.h>
#include    <stdio.h>
#include    <stddef.h>
#endif /* !defined(__cplusplus) && !defined(CPPAPP) */

#if defined(__CCRX__) || defined(__ICCRX__)
/* Intrinsic functions provided by compiler. */
#include <machine.h>
#elif defined(__GNUC__)
/* No header file for intrinsic functions. */
#else
/* PORT: Use header file for other compiler and port r_rx_compiler.h. */
#endif /* defined(__CCRX__), defined(__GNUC__), defined(__ICCRX__) */

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
/* Multiple inclusion prevention macro */
#ifndef R_BSP_COMMON_H
#define R_BSP_COMMON_H

/* Version Number of r_bsp. */
#define R_BSP_VERSION_MAJOR           (5)
#define R_BSP_VERSION_MINOR           (52)

/* This macro is used to suppress compiler messages about not only a parameter but also a auto variable not being used
 * in a function. The nice thing about using this implementation is that it does not take any extra RAM or ROM.
 * This macro is available for the followings:
 * CC-RX's 'M0520826:Parameter "XXXX" was never referenced'
 * CC-RX's 'W0520550:Variable "XXXX" was set but never used'
 * GNURX's 'unused parameter 'XXXX' [-Wunused-parameter]'
 * GNURX's 'variable 'XXXX' set but not used [-Wunused-but-set-variable]'
 * When the variable is declared as volatile, the '&' can be applied like 'R_INTERNAL_NOT_USED(&volatile_variable);'.
 */
#define INTERNAL_NOT_USED(p)        ((void)(p))

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/
/* Available delay units. */
typedef enum
{
    BSP_DELAY_MICROSECS = 1000000,  // Requested delay amount is in microseconds
    BSP_DELAY_MILLISECS = 1000,     // Requested delay amount is in milliseconds
    BSP_DELAY_SECS = 1              // Requested delay amount is in seconds
} bsp_delay_units_t;

/* Easy to use typedef for FIT module callback functions. */
typedef void (*fit_callback_t)(void *p_args);

/***********************************************************************************************************************
Exported global variables
***********************************************************************************************************************/

/***********************************************************************************************************************
Exported global functions (to be accessed by other files)
***********************************************************************************************************************/
uint32_t R_BSP_GetVersion(void);
bool R_BSP_SoftwareDelay(uint32_t delay, bsp_delay_units_t units);
uint32_t R_BSP_GetIClkFreqHz(void);

/* End of multiple inclusion prevention macro */
#endif  /* R_BSP_COMMON_H */

