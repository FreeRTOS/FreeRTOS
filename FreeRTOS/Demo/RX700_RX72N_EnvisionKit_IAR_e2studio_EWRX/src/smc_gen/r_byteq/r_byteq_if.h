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
* File Name    : r_byteq_if.h
* Description  : Functions for using byte queues/circular buffers 
************************************************************************************************************************
* History : DD.MM.YYYY Version Description
*         : 24.07.2013 1.00    Initial Release
*         : 11.21.2014 1.20    Removed dependency to BSP
*         : 01.22.2015 1.30    Updated version to 1.30 for RX71M release
*         : 04.04.2015 1.40    Updated version to 1.40 for RX231 release
*         : 30.09.2015 1.50    Added dependency to BSP
*         : 29.01.2016 1.60    Updated version to 1.60 for correspondence to RX Family
*         : 01.06.2018 1.70    Updated version to 1.70
*         : 03.12.2018 1.71    Updated version to 1.71 for update of xml file.
*         : 07.02.2019 1.80    Updated version to 1.80.
***********************************************************************************************************************/

#ifndef BYTEQ_IF_H
#define BYTEQ_IF_H

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include "platform.h"

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
/* Version Number of API. */
#define BYTEQ_VERSION_MAJOR (1)
#define BYTEQ_VERSION_MINOR (80)


/*****************************************************************************
Typedef definitions
******************************************************************************/

typedef enum e_byteq_err        // BYTEQ API error codes
{
    BYTEQ_SUCCESS = 0,
    BYTEQ_ERR_NULL_PTR,         // received null ptr; missing required argument
    BYTEQ_ERR_INVALID_ARG,      // argument is not valid for parameter
    BYTEQ_ERR_MALLOC_FAIL,      // can't allocate memory for ctrl block; increase heap
    BYTEQ_ERR_NO_MORE_CTRL_BLKS,  // no more control blocks, increase BYTEQ_MAX_CTRL_BLKS
    BYTEQ_ERR_QUEUE_FULL,       // queue full; cannot add another byte
    BYTEQ_ERR_QUEUE_EMPTY       // queue empty; no byte to fetch
} byteq_err_t;


/* BYTE QUEUE HANDLE */

typedef struct st_byteq_ctrl *  byteq_hdl_t;


/*****************************************************************************
Public Functions
******************************************************************************/
byteq_err_t R_BYTEQ_Open(uint8_t * const        p_buf,
                         uint16_t const         size,
                         byteq_hdl_t * const    p_hdl);

byteq_err_t R_BYTEQ_Close(byteq_hdl_t const hdl);

byteq_err_t R_BYTEQ_Put(byteq_hdl_t const   hdl,
                        uint8_t const       byte);

byteq_err_t R_BYTEQ_Get(byteq_hdl_t const   hdl,
                        uint8_t * const     p_byte);

byteq_err_t R_BYTEQ_Flush(byteq_hdl_t const hdl);

byteq_err_t R_BYTEQ_Used(byteq_hdl_t const  hdl,
                         uint16_t * const   p_cnt);

byteq_err_t R_BYTEQ_Unused(byteq_hdl_t const    hdl,
                           uint16_t * const     p_cnt);

uint32_t R_BYTEQ_GetVersion(void);


#endif /* BYTEQ_IF_H */

