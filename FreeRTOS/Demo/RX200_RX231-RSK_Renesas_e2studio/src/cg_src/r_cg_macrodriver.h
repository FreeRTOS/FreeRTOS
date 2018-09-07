/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products.
* No other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIESREGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED
* OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
* NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY
* LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE FOR ANY DIRECT,
* INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR
* ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability
* of this software. By using this software, you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2015 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : r_cg_macrodriver.h
* Version      : Code Generator for RX231 V1.00.00.03 [10 Jul 2015]
* Device(s)    : R5F52318AxFP
* Tool-Chain   : GCCRX
* Description  : This file implements general head file.
* Creation Date: 23/09/2015
***********************************************************************************************************************/
#ifndef MODULEID_H
#define MODULEID_H
/***********************************************************************************************************************
Includes
***********************************************************************************************************************/
#include "../iodefine.h"
#include <machine.h>

/***********************************************************************************************************************
Macro definitions (Register bit)
***********************************************************************************************************************/

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#ifndef __TYPEDEF__

/* Status list definition */
#define MD_STATUSBASE        (0x00U)
#define MD_OK                (MD_STATUSBASE + 0x00U) /* register setting OK */
#define MD_SPT               (MD_STATUSBASE + 0x01U) /* IIC stop */
#define MD_NACK              (MD_STATUSBASE + 0x02U) /* IIC no ACK */
#define MD_BUSY1             (MD_STATUSBASE + 0x03U) /* busy 1 */
#define MD_BUSY2             (MD_STATUSBASE + 0x04U) /* busy 2 */

/* Error list definition */
#define MD_ERRORBASE         (0x80U)
#define MD_ERROR             (MD_ERRORBASE + 0x00U)  /* error */
#define MD_ARGERROR          (MD_ERRORBASE + 0x01U)  /* error argument input error */
#define MD_ERROR1            (MD_ERRORBASE + 0x02U)  /* error 1 */
#define MD_ERROR2            (MD_ERRORBASE + 0x03U)  /* error 2 */
#define MD_ERROR3            (MD_ERRORBASE + 0x04U)  /* error 3 */
#define MD_ERROR4            (MD_ERRORBASE + 0x05U)  /* error 4 */
#define MD_ERROR5            (MD_ERRORBASE + 0x06U)  /* error 5 */

#endif

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/
#ifndef __TYPEDEF__
    #ifndef _STD_USING_INT_TYPES
        #define _SYS_INT_TYPES_H
        #ifndef _STD_USING_BIT_TYPES
            #define __int8_t_defined
            typedef signed char         int8_t;
            typedef signed short        int16_t;
        #endif

        typedef unsigned char       uint8_t;
        typedef unsigned short      uint16_t;
        typedef signed long         int32_t;
        typedef unsigned long       uint32_t;

        typedef signed char         int_least8_t;
        typedef signed short        int_least16_t;
        typedef signed long         int_least32_t;
        typedef unsigned char       uint_least8_t;
        typedef unsigned short      uint_least16_t;
        typedef unsigned long       uint_least32_t;
    #endif

    typedef unsigned short      MD_STATUS;
    #define __TYPEDEF__
#endif



#endif
