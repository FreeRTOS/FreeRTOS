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
* File Name    : r_private.h
* Description  : Definitions internal to byte queue module 
************************************************************************************************************************
* History : DD.MM.YYYY Version Description   
*         : 24.07.2013 1.0     Initial Release        
*         : 30.09.2015 1.50    Added dependency to BSP
***********************************************************************************************************************/

#ifndef BYTEQ_PRIVATE_H
#define BYTEQ_PRIVATE_H

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include "platform.h"


/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/


/*****************************************************************************
Typedef definitions
******************************************************************************/

/* QUEUE CONTROL BLOCK */

typedef struct st_byteq_ctrl    // Byte Queue Control Block (for handle)
{
    uint8_t     *buffer;        // pointer to buffer
    uint16_t    size;           // buffer size
    uint16_t    count;          // number data bytes in queue
    uint16_t    in_index;       // index used by Put function to add data
    uint16_t    out_index;      // index used by Get function to remove data
} byteq_ctrl_t;


#endif /* BYTEQ_PRIVATE_H */
