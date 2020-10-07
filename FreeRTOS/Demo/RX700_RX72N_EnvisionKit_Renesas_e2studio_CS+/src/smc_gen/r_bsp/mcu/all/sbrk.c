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
* File Name    : sbrk.c
* Description  : Configures the MCU heap memory.  The size of the heap is defined by the macro HEAPSIZE below.
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 28.02.2019 3.00     Merged processing of all devices.
*                               Added support for GNUC and ICCRX.
*                               Fixed coding style.
*         : 26.07.2019 3.01     Fixed coding style.
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include "sbrk.h"

/* Only use this file if heap is enabled in r_bsp_config. */
#if BSP_CFG_HEAP_BYTES > 0

/* When using the user startup program, disable the following code. */
#if BSP_CFG_STARTUP_DISABLE == 0

#if defined(__CCRX__) || defined(__GNUC__)

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Exported global variables (to be accessed by other files)
***********************************************************************************************************************/

/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/
/* Declare memory heap area */
static u_heap_type_t s_heap_area;

/* End address allocated by sbrk (CC-RX and GNURX+NEWLIB) */
static int8_t *sp_brk=(int8_t *)&s_heap_area;

#if defined(__GNUC__)
/* Start address of allocated heap area (GNURX+OPTLIB only) */
int8_t *_heap_of_memory=(int8_t *)&s_heap_area;
/* End address of allocated heap area (GNURX+OPTLIB only) */
int8_t *_last_heap_object=(int8_t *)&s_heap_area;
#endif /* defined(__GNUC__) */

/***********************************************************************************************************************
* Function name: sbrk
* Description  : This function configures MCU memory area allocation. (CC-RX and GNURX+NEWLIB)
* Arguments    : size - 
*                    assigned area size
* Return value : Start address of allocated area (pass)
*                -1 (failure)
***********************************************************************************************************************/
int8_t  *sbrk(size_t size)
{
    int8_t  *p_area;

    if ((sp_brk + size) > (s_heap_area.heap + BSP_CFG_HEAP_BYTES))
    {
        /* Empty area size  */
        p_area = (int8_t *)-1;
    }
    else
    {
        /* Area assignment */
        p_area = sp_brk;

        /* End address update */
        sp_brk += size;
    }

    /* Return result */
    return p_area;
} /* End of function sbrk() */

#if defined(__GNUC__)
/***********************************************************************************************************************
* Function name: _top_of_heap
* Description  : This function returns end address of reserved heap area. (GNURX+OPTLIB only)
* Arguments    : none
* Return value : End address of reserved heap area
***********************************************************************************************************************/
int8_t *_top_of_heap(void)
{
    return (int8_t *)(s_heap_area.heap + BSP_CFG_HEAP_BYTES);
} /* End of function End of function sbrk()() */
#endif /* defined(__GNUC__) */

#endif /* defined(__CCRX__), defined(__GNUC__) */

#endif /* BSP_CFG_STARTUP_DISABLE == 0 */

#endif /* BSP_CFG_HEAP_BYTES */

