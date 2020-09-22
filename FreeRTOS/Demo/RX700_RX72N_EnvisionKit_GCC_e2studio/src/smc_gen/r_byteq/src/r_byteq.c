/*****************************************************************************
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
******************************************************************************/
/*****************************************************************************
* File Name    : r_byteq.c
* Description  : Functions for using byte queues/circular buffers. 
******************************************************************************
* History : DD.MM.YYYY Version Description  
*         : 24.07.2013 1.00     Initial Release
*         : 11.21.2014 1.20     Removed dependency to BSP
*         : 30.09.2015 1.50     Added dependency to BSP
*         : 29.01.2016 1.60     Fixed the initial setting process in the R_LONGQ_Open function.
*                               Fixed a program according to the Renesas coding rules.
*         : 01.06.2018 1.70     Added the comment to while statement.
*         : 07.02.2019 1.80     Deleted the inline expansion of the R_BYTEQ_GetVersion function.
******************************************************************************/

/*****************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
/* Used functions of malloc() and the free() */
#include <stdlib.h>

/* Used the common type */
#include "platform.h"

/* Defines for BYTEQ support */
#include "r_byteq_private.h"
#include "r_byteq_if.h"
#include "r_byteq_config.h"

/*****************************************************************************
Typedef definitions
******************************************************************************/

/*****************************************************************************
Macro definitions
******************************************************************************/

/*****************************************************************************
Private global variables and functions
******************************************************************************/

/* QUEUE CONTROL BLOCK ALLOCATIONS */

#if (BYTEQ_CFG_USE_HEAP_FOR_CTRL_BLKS == 0)
static byteq_ctrl_t     g_qcb[BYTEQ_CFG_MAX_CTRL_BLKS];
#endif


/*****************************************************************************
* Function Name: R_BYTEQ_Open
* Description  : Allocates or assigns a queue control block for the buffer 
*                pointed to by p_buf (see BYTEQ_CFG_USE_HEAP_FOR_CTRL_BLKS in
*                config.h). Initializes the queue to an empty state and 
*                provides a Handle to its control structure in p_hdl which is
*                then used as a queue ID for the other API functions.
* Arguments    : p_buf -
*                    Pointer to byte buffer.
*                size -
*                    Buffer size in bytes.
*                p_hdl -
*                    Pointer to a handle for queue (value set here)
* Return Value : SCI_SUCCESS -
*                    queue initialized successfully
*                BYTEQ_ERR_NULL_PTR
*                    received null ptr; missing required argument
*                BYTEQ_ERR_INVALID_ARG
*                    argument is not valid for parameter
*                BYTEQ_ERR_MALLOC_FAIL
*                    can't allocate memory for ctrl block; increase heap
*                BYTEQ_ERR_NO_MORE_CTRL_BLKS
*                    no more control blocks, increase BYTEQ_CFG_MAX_CTRL_BLKS
******************************************************************************/
byteq_err_t R_BYTEQ_Open(uint8_t * const        p_buf,
                         uint16_t const         size,
                         byteq_hdl_t * const    p_hdl)
{
    byteq_ctrl_t    *p_qcb = 0;
#if (BYTEQ_CFG_USE_HEAP_FOR_CTRL_BLKS == 0)
    uint32_t        i;
    static bool     qcb_init = false;
#endif

    /* CHECK ARGUMENTS */

#if (BYTEQ_CFG_PARAM_CHECKING_ENABLE == 1)
    if (NULL == p_hdl)
    {
        return BYTEQ_ERR_INVALID_ARG;   // return if invalid location
    }
    if (NULL == p_buf)
    {
        return BYTEQ_ERR_NULL_PTR;      // return if no buffer pointer
    }
    if (size < 2)
    {
        return BYTEQ_ERR_INVALID_ARG;   // return insufficient buffer size
    }
#endif

    /* GET QUEUE CONTROL BLOCK */
    
#if BYTEQ_CFG_USE_HEAP_FOR_CTRL_BLKS

    /* allocate memory for a QCB */
    p_qcb = (byteq_ctrl_t *)malloc(sizeof(byteq_ctrl_t));
    if (NULL == p_qcb)
    {
        return BYTEQ_ERR_MALLOC_FAIL;
    }
#else
    /* if first Open call, mark all QCBs as being available */
    if (false == qcb_init)
    {
        /* WAIT_LOOP */
        for (i=0; i < BYTEQ_CFG_MAX_CTRL_BLKS; i++)
        {
            g_qcb[i].buffer = NULL;
        }
        qcb_init = true;
    }

    /* locate first available QCB */
    /* WAIT_LOOP */
    for (i=0; i < BYTEQ_CFG_MAX_CTRL_BLKS; i++)
    {
        if (NULL == g_qcb[i].buffer)
        {
            p_qcb = &g_qcb[i];
            break;
        }
    }
    
    /* return error if none available */
    if (BYTEQ_CFG_MAX_CTRL_BLKS == i)
    {
        return BYTEQ_ERR_NO_MORE_CTRL_BLKS;
    }
#endif


    /* INITIALIZE QCB FIELDS */
    
    p_qcb->buffer = p_buf;
    p_qcb->size = size;
    p_qcb->count = 0;
    p_qcb->in_index = 0;
    p_qcb->out_index = 0;
    
    
    /* SET HANDLE */
    
    *p_hdl = p_qcb;
    return BYTEQ_SUCCESS;
}


/*****************************************************************************
* Function Name: R_BYTEQ_Put
* Description  : This function adds a byte of data to the queue.
*
* NOTE: This function does not disable/enable interrupts. If the queue is
*       accessed from both the interrupt and application level, the app must
*       disable/enable interrupts before/after calling this routine.
*
* Arguments    : hdl - 
*                    Handle for queue.
*                byte -
*                    Byte to add to queue.
* Return Value : BYTEQ_SUCCESS -
*                    Successful; byte sent or queued for transmit
*                BYTEQ_ERR_NULL_PTR -
*                    hdl is NULL
*                BYTEQ_ERR_QUEUE_FULL -
*                    Queue full; cannot add byte to queue.
******************************************************************************/
byteq_err_t R_BYTEQ_Put(byteq_hdl_t const   hdl,
                        uint8_t const       byte)
{
#if (BYTEQ_CFG_PARAM_CHECKING_ENABLE == 1)
    if (NULL == hdl)
    {
        return BYTEQ_ERR_NULL_PTR;          // return if no handle
    }
#endif

    if (hdl->count >= hdl->size)
    {
        return BYTEQ_ERR_QUEUE_FULL;        // return if queue is full
    }

    /* load byte into queue */
    hdl->buffer[hdl->in_index++] = byte;    // add byte
    if (hdl->in_index >= hdl->size)         // adjust index
    {
        hdl->in_index = 0;
    }
    hdl->count++;                           // adjust count
        
    return BYTEQ_SUCCESS;
}


/*****************************************************************************
* Function Name: R_BYTEQ_Get
* Description  : This function removes a byte of data from the queue.
*
* NOTE: This function does not disable/enable interrupts. If the queue is
*       accessed from both the interrupt and application level, the app must
*       disable/enable interrupts before/after calling this routine.
*
* Arguments    : hdl - 
*                    Handle for queue.
*                p_byte -
*                    Pointer to load byte to.
* Return Value : BYTEQ_SUCCESS -
*                    Successful; byte sent or queued for transmit
*                BYTEQ_ERR_NULL_PTR - 
*                    hdl is NULL
*                BYTEQ_ERR_INVALID_ARG - 
*                    p_byte is NULL
*                BYTEQ_ERR_QUEUE_EMPTY -
*                    Queue empty; no data available to fetch
******************************************************************************/
byteq_err_t R_BYTEQ_Get(byteq_hdl_t const   hdl,
                        uint8_t * const     p_byte)
{
#if (BYTEQ_CFG_PARAM_CHECKING_ENABLE == 1)
    if (NULL == hdl)
    {
        return BYTEQ_ERR_NULL_PTR;          // return if no handle
    }
    if (NULL == p_byte)
    {
        return BYTEQ_ERR_INVALID_ARG;       // return if invalid location
    }
#endif

    if (0 == hdl->count)
    {
        return BYTEQ_ERR_QUEUE_EMPTY;       // return if queue empty        
    }

    *p_byte = hdl->buffer[hdl->out_index++]; // get byte
    if (hdl->out_index >= hdl->size)        // adjust index
    {
        hdl->out_index = 0;
    }
    hdl->count--;                           // adjust count

    return BYTEQ_SUCCESS;
}        


/*****************************************************************************
* Function Name: R_BYTEQ_Flush
* Description  : This function resets a queue to an empty state.
*
* NOTE: This function does not disable/enable interrupts. If the queue is
*       accessed from both the interrupt and application level, the app must
*       disable/enable interrupts before/after calling this routine.
*
* Arguments    : hdl - 
*                    Handle for queue.
* Return Value : BYTEQ_SUCCESS -
*                    Successful; queue is reset to en ampty state
*                BYTEQ_ERR_NULL_PTR - 
*                    hdl is NULL
******************************************************************************/
byteq_err_t R_BYTEQ_Flush(byteq_hdl_t const hdl)
{
#if (BYTEQ_CFG_PARAM_CHECKING_ENABLE == 1)
    if (NULL == hdl)
    {
        return BYTEQ_ERR_NULL_PTR;
    }
#endif

    /* RESET QUEUE */
    
    hdl->in_index = 0;
    hdl->out_index = 0;
    hdl->count = 0;

    return BYTEQ_SUCCESS;
}


/*****************************************************************************
* Function Name: R_BYTEQ_Used
* Description  : This function provides the number of data bytes in the queue.
* Arguments    : hdl - 
*                    Handle for queue.
*                p_cnt -
*                    Pointer to load queue data count to.
* Return Value : BYTEQ_SUCCESS -
*                    Successful; *p_cnt loaded with number of bytes in queue
*                BYTEQ_ERR_NULL_PTR - 
*                    hdl is NULL
*                BYTEQ_ERR_INVALID_ARG - 
*                    p_cnt is NULL
******************************************************************************/
byteq_err_t R_BYTEQ_Used(byteq_hdl_t const  hdl,
                         uint16_t * const   p_cnt)
{
#if (BYTEQ_CFG_PARAM_CHECKING_ENABLE == 1)
    if (NULL == hdl)
    {
        return BYTEQ_ERR_NULL_PTR;
    }
    if (NULL == p_cnt)
    {
        return BYTEQ_ERR_INVALID_ARG;       // return if invalid location
    }
#endif

    *p_cnt = hdl->count;
    return BYTEQ_SUCCESS;
}


/*****************************************************************************
* Function Name: R_BYTEQ_Unused
* Description  : This function provides the number of data bytes available 
*                for storage in the queue.
* Arguments    : hdl - 
*                    Handle for queue.
*                p_cnt -
*                    Pointer to load queue unused byte count to.
* Return Value : BYTEQ_SUCCESS -
*                    Successful; *p_cnt loaded with number of bytes available in
*                    queue
*                BYTEQ_ERR_NULL_PTR - 
*                    hdl is NULL
*                BYTEQ_ERR_INVALID_ARG - 
*                    p_cnt is NULL
******************************************************************************/
byteq_err_t R_BYTEQ_Unused(byteq_hdl_t const  hdl,
                           uint16_t * const   p_cnt)
{
#if (BYTEQ_CFG_PARAM_CHECKING_ENABLE == 1)
    if (NULL == hdl)
    {
        return BYTEQ_ERR_NULL_PTR;
    }
    if (NULL == p_cnt)
    {
        return BYTEQ_ERR_INVALID_ARG;       // return if invalid location
    }
#endif

    *p_cnt = (uint16_t) (hdl->size - hdl->count);
    return BYTEQ_SUCCESS;
}


/*****************************************************************************
* Function Name: R_BYTEQ_Close
* Description  : If the control block associated with this Handle was allocated 
*                dynamically at run time (BYTEQ_CFG_USE_HEAP_FOR_CTRL_BLKS set to 1
*                in config.h), then that memory is free()d by this function. If 
*                the control block was statically allocated at compile time 
*                (BYTEQ_CFG_USE_HEAP_FOR_CTRL_BLKS set to 0 in config.h), then this
*                function marks the control block as available for use by another 
*                buffer. Nothing is done to the contents of the buffer referenced 
*                by this Handle.
* Arguments    : hdl - 
*                    handle for queue
* Return Value : BYTEQ_SUCCESS -
*                    Successful; control block freed
*                BYTEQ_ERR_NULL_PTR -
*                    hdl is NULL.
******************************************************************************/
byteq_err_t R_BYTEQ_Close(byteq_hdl_t const hdl)
{
#if (BYTEQ_CFG_PARAM_CHECKING_ENABLE == 1)
    if (NULL == hdl)
    {
        return BYTEQ_ERR_NULL_PTR;
    }
#endif

#if BYTEQ_CFG_USE_HEAP_FOR_CTRL_BLKS
    free(hdl);                          // free QCB memory
#else
    hdl->buffer = NULL;                 // mark QCB as free
#endif
    
    return BYTEQ_SUCCESS;
}


/*****************************************************************************
* Function Name: R_BYTEQ_GetVersion
* Description  : Returns the version of this module. The version number is 
*                encoded such that the top two bytes are the major version
*                number and the bottom two bytes are the minor version number.
* Arguments    : none
* Return Value : version number
******************************************************************************/
uint32_t  R_BYTEQ_GetVersion(void)
{

    uint32_t const version = (BYTEQ_VERSION_MAJOR << 16) | BYTEQ_VERSION_MINOR;
    return version;
}
