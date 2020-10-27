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
* Copyright (C) 2019 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : sbrk.h
* Description  : Configures the MCU heap memory.  The size of the heap is defined by the macro HEAPSIZE below.
***********************************************************************************************************************/
/**********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 28.02.2019 1.00     First Release
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include "r_bsp_common.h"
#include "r_bsp_config.h"

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
/* Multiple inclusion prevention macro */
#ifndef SBRK_H
#define SBRK_H

/* Only use this file if heap is enabled in r_bsp_config. */
#if BSP_CFG_HEAP_BYTES > 0

/* When using the user startup program, disable the following code. */
#if BSP_CFG_STARTUP_DISABLE == 0

#if defined(__CCRX__) || defined(__GNUC__)

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/
typedef union
{
    int32_t  dummy;             /* Dummy for 4-byte boundary */
    int8_t heap[BSP_CFG_HEAP_BYTES];    /* Declaration of the area managed by sbrk*/
} u_heap_type_t;

/***********************************************************************************************************************
Exported global variables
***********************************************************************************************************************/

/***********************************************************************************************************************
Exported global functions (to be accessed by other files)
***********************************************************************************************************************/
/* const size_t _sbrk_size=      // Specifies the minimum unit of */
/* the defined heap area */
int8_t *_s1ptr;

/* Memory allocation function prototype declaration (CC-RX and GNURX+NEWLIB) */
int8_t  *sbrk(size_t size);

#if defined(__GNUC__)
/* Memory address function prototype declaration (GNURX+OPTLIB only) */
int8_t  *_top_of_heap(void);
#endif /* defined(__GNUC__) */

#endif /* defined(__CCRX__), defined(__GNUC__) */

#endif /* BSP_CFG_STARTUP_DISABLE == 0 */

#endif /* BSP_CFG_HEAP_BYTES */

#endif  /* SBRK_H */

