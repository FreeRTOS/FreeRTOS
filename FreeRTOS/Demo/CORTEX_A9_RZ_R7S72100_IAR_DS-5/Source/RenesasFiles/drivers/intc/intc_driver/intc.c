/*******************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only
* intended for use with Renesas products. No other uses are authorized. This
* software is owned by Renesas Electronics Corporation and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT
* LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE
* AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
* ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR
* ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE
* BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software
* and to discontinue the availability of this software. By using this software,
* you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.
*******************************************************************************/
/*******************************************************************************
* File Name   : intc.c
* $Rev: 17531 $
* $Date:: 2013-04-10 12:58:44 +0100#$
* Description : Aragon Sample Program - Interrupt process
*******************************************************************************/


/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include "r_typedefs.h"
#include "dev_drv.h"                /* Device Driver common header */
#include "devdrv_intc.h"            /* INTC Driver Header */
#include "iodefine.h"

/******************************************************************************
Typedef definitions
******************************************************************************/


/******************************************************************************
Macro definitions
******************************************************************************/
#define INTC_ICDISR_REG_TOTAL   (((uint16_t)INTC_ID_TOTAL / 32) + 1) /* ICDISR  */
#define INTC_ICDICFR_REG_TOTAL  (((uint16_t)INTC_ID_TOTAL / 16) + 1) /* ICDICFR */
#define INTC_ICDIPR_REG_TOTAL   (((uint16_t)INTC_ID_TOTAL /  4) + 1) /* ICDIPR  */
#define INTC_ICDIPTR_REG_TOTAL  (((uint16_t)INTC_ID_TOTAL /  4) + 1) /* ICDIPTR */
#define INTC_ICDISER_REG_TOTAL  (((uint16_t)INTC_ID_TOTAL / 32) + 1) /* ICDISER */
#define INTC_ICDICER_REG_TOTAL  (((uint16_t)INTC_ID_TOTAL / 32) + 1) /* ICDICER */

/******************************************************************************
Imported global variables and functions (from other files)
******************************************************************************/


/******************************************************************************
Exported global variables and functions (to be accessed by other files)
******************************************************************************/


/******************************************************************************
Private global variables and functions
******************************************************************************/
/* ==== Global variable ==== */
static uint32_t intc_icdicfrn_table[] =
{
    0xAAAAAAAA,            /* ICDICFR0  :  15 -   0 */
    0x00000055,            /* ICDICFR1  :  19 -  16 */
    0xFFFD5555,            /* ICDICFR2  :  47 -  32 */
    0x555FFFFF,            /* ICDICFR3  :  63 -  48 */
    0x55555555,            /* ICDICFR4  :  79 -  64 */
    0x55555555,            /* ICDICFR5  :  95 -  80 */
    0x55555555,            /* ICDICFR6  : 111 -  96 */
    0x55555555,            /* ICDICFR7  : 127 - 112 */
    0x5555F555,            /* ICDICFR8  : 143 - 128 */
    0x55555555,            /* ICDICFR9  : 159 - 144 */
    0x55555555,            /* ICDICFR10 : 175 - 160 */
    0xF5555555,            /* ICDICFR11 : 191 - 176 */
    0xF555F555,            /* ICDICFR12 : 207 - 192 */
    0x5555F555,            /* ICDICFR13 : 223 - 208 */
    0x55555555,            /* ICDICFR14 : 239 - 224 */
    0x55555555,            /* ICDICFR15 : 255 - 240 */
    0x55555555,            /* ICDICFR16 : 271 - 256 */
    0xFD555555,            /* ICDICFR17 : 287 - 272 */
    0x55555557,            /* ICDICFR18 : 303 - 288 */
    0x55555555,            /* ICDICFR19 : 319 - 304 */
    0x55555555,            /* ICDICFR20 : 335 - 320 */
    0x5F555555,            /* ICDICFR21 : 351 - 336 */
    0xFD55555F,            /* ICDICFR22 : 367 - 352 */
    0x55555557,            /* ICDICFR23 : 383 - 368 */
    0x55555555,            /* ICDICFR24 : 399 - 384 */
    0x55555555,            /* ICDICFR25 : 415 - 400 */
    0x55555555,            /* ICDICFR26 : 431 - 416 */
    0x55555555,            /* ICDICFR27 : 447 - 432 */
    0x55555555,            /* ICDICFR28 : 463 - 448 */
    0x55555555,            /* ICDICFR29 : 479 - 464 */
    0x55555555,            /* ICDICFR30 : 495 - 480 */
    0x55555555,            /* ICDICFR31 : 511 - 496 */
    0x55555555,            /* ICDICFR32 : 527 - 512 */
    0x55555555,            /* ICDICFR33 : 543 - 528 */
    0x55555555,            /* ICDICFR34 : 559 - 544 */
    0x55555555,            /* ICDICFR35 : 575 - 560 */
    0x00155555             /* ICDICFR36 : 586 - 576 */
};


/******************************************************************************
* Function Name: R_INTC_RegistIntFunc
* Description  :
* Arguments    : uint16_t int_id
*              : void (* func)(uint32_t)
* Return Value : DEVDRV_SUCCESS
*              : DEVDRV_ERROR
******************************************************************************/
int32_t R_INTC_RegistIntFunc(uint16_t int_id, void (* func)(uint32_t int_sense))
{
    if (int_id >= INTC_ID_TOTAL)
    {
        return DEVDRV_ERROR;
    }

    Userdef_INTC_RegistIntFunc(int_id, func);

    return DEVDRV_SUCCESS;
}

/******************************************************************************
* Function Name: R_INTC_Init
* Description  :
* Arguments    : none
* Return Value : none
******************************************************************************/
void R_INTC_Init(void)
{
    uint16_t offset;
    volatile uint32_t * addr;

    for (offset = 0; offset < INTC_ICDICFR_REG_TOTAL; offset++)
    {
        INTC.ICDICFR.LONG[offset] = intc_icdicfrn_table[offset];
    }

    addr = (volatile uint32_t *)&INTC.ICDIPR0.LONG;
    for (offset = 0; offset < INTC_ICDIPR_REG_TOTAL; offset++)
    {
        *(addr + offset) = 0xF8F8F8F8;
    }

    addr = (volatile uint32_t *)&INTC.ICDIPTR0.LONG;
    for (offset = 8; offset < INTC_ICDIPTR_REG_TOTAL; offset++)
    {
        *(addr + offset) = 0x01010101;
    }

    for (offset = 0; offset < INTC_ICDICER_REG_TOTAL; offset++)
    {
        INTC.ICDICER.LONG[offset] = 0xFFFFFFFF;
    }

    R_INTC_SetMaskLevel(31);

    INTC.ICCBPR.BIT.Binarypoint = 0;

    INTC.ICCICR.LONG = 3;

    /* Distributor Control Register */
    INTC.ICDDCR.BIT.Enable = 1;
}

/******************************************************************************
* Function Name: R_INTC_Enable
* Description  :
* Arguments    : uint16_t int_id
* Return Value : DEVDRV_SUCCESS
*              : DEVDRV_ERROR
******************************************************************************/
int32_t R_INTC_Enable(uint16_t int_id)
{
    uint32_t reg_value;
    uint32_t mask;

    if (int_id >= INTC_ID_TOTAL)
    {
        return DEVDRV_ERROR;
    }

    mask = 1;
    mask = mask << (int_id % 32);

    reg_value = INTC.ICDISER.LONG[int_id / 32];
    reg_value |= mask;
    INTC.ICDISER.LONG[int_id / 32] = reg_value;

    return DEVDRV_SUCCESS;
}

/******************************************************************************
* Function Name: R_INTC_Disable
* Description  :
* Arguments    : uint16_t int_id
* Return Value : DEVDRV_SUCCESS
*              : DEVDRV_ERROR
******************************************************************************/
int32_t R_INTC_Disable(uint16_t int_id)
{
    uint32_t reg_value;
    uint32_t mask;

    if (int_id >= INTC_ID_TOTAL)
    {
        return DEVDRV_ERROR;
    }

    mask = 1;
    mask = mask << (int_id % 32);

    reg_value = INTC.ICDICER.LONG[int_id / 32];
    reg_value |= mask;
    INTC.ICDICER.LONG[int_id / 32] = reg_value;

    return DEVDRV_SUCCESS;
}

/******************************************************************************
* Function Name: R_INTC_SetPriority
* Description  :
* Arguments    : uint16_t int_id
*              : uint8_t priority
* Return Value : DEVDRV_SUCCESS
*              : DEVDRV_ERROR
******************************************************************************/
int32_t R_INTC_SetPriority(uint16_t int_id, uint8_t priority)
{
    uint32_t icdipr;
    uint32_t mask;
    volatile uint32_t * addr;

    if ((int_id >= INTC_ID_TOTAL) || priority >= 32)
    {
        return DEVDRV_ERROR;
    }

    priority = priority << 3;

    addr = (volatile uint32_t *)&INTC.ICDIPR0.LONG;

    icdipr = *(addr + (int_id / 4));

    mask = (uint32_t)0x000000FF;
    mask = mask << ((int_id % 4) * 8);
    icdipr &= ~mask;
    mask = (uint32_t)priority;
    mask = mask << ((int_id % 4) * 8);
    icdipr |= mask;

    *(addr + (int_id / 4)) = icdipr;

    return DEVDRV_SUCCESS;
}

/******************************************************************************
* Function Name: R_INTC_SetMaskLevel
* Description  :
* Arguments    : uint8_t mask_level
* Return Value : DEVDRV_SUCCESS
*              : DEVDRV_ERROR
******************************************************************************/
int32_t R_INTC_SetMaskLevel(uint8_t mask_level)
{
    if (mask_level >= 32)
    {
        return DEVDRV_ERROR;
    }

    mask_level = mask_level << 3;
    INTC.ICCPMR.BIT.Priority = mask_level;

    return DEVDRV_SUCCESS;
}

/******************************************************************************
* Function Name: R_INTC_GetMaskLevel
* Description  :
* Arguments    : uint8_t * mask_level
* Return Value : none
******************************************************************************/
void R_INTC_GetMaskLevel(uint8_t * mask_level)
{
    *mask_level = INTC.ICCPMR.BIT.Priority;
    *mask_level = *mask_level >> 3;
}

/* END of File */

