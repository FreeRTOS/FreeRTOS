/*******************************************************************************
 * (c) Copyright 2010-2013 Microsemi SoC Products Group.  All rights reserved.
 * 
 * SmartFusion2 MSS HPDMA bare metal driver implementation.
 *
 * SVN $Revision: 5148 $
 * SVN $Date: 2013-02-27 16:42:01 +0000 (Wed, 27 Feb 2013) $
 */
#include "mss_hpdma.h"

/*==============================================================================
 * Design Notes
 *------------------------------------------------------------------------------
  This SmartFusion2 MSS HPDMA driver only makes use of the first HPDMA
  descriptor. The rationale for this choice is that the pause and clear bits of
  each individual descriptor have undocumented side effects to the other
  descriptors in the HPDMA hardware block. This prevents independent operations
  of the descriptors in particular when it comes to error handling where error
  recovery requires clearing a descriptor. An error on one descriptor would
  result in aborting transfers on the other descriptors. Likewise, it is not
  possible to pause individual descriptors. Setting the pause bit in one
  descriptor results in all descriptors being paused.
 */

#ifdef __cplusplus
extern "C" {
#endif 

/*-------------------------------------------------------------------------*//**
 * Constants
 */
#define HPDMA_ENABLE    1u
#define HPDMA_DISABLE   0u
#define NULL_HANDLER    ((mss_hpdma_handler_t)0)

/* 64 K DMA Transfer */
#define MAX_SIZE_PER_DMA_XFR   0x10000u

#define DESC0       0u

/*-------------------------------------------------------------------------*//**
 * Mask Constants
 */
#define HPDMA_SOFT_RESET            0x00020000u
#define HPDMA_XFR_SIZE_MASK         0xFFFF0000u

#define HPDMACR_XFR_CMP_INT_MASK    0x00100000u
#define HPDMACR_XFR_ERR_INT_MASK    0x00200000u
#define HPDMACR_NON_WORD_INT_MASK   0x00400000u

#define HPDMACR_ALL_IRQ_ENABLE_MASK (HPDMACR_XFR_CMP_INT_MASK | HPDMACR_XFR_ERR_INT_MASK | HPDMACR_NON_WORD_INT_MASK)

#define HPDMAICR_CLEAR_ALL_IRQ      0x000000FFu

#define HPDMAEDR_DCP_ERR_MASK           0x00000100u

#define HPDMAEDR_NON_WORD_ERR_MASK      0x00001000u

/*-------------------------------------------------------------------------*//**
  Current transfer state information.
 */
typedef struct hpdma_xfer_info
{
    hpdma_status_t          state;
    mss_hpdma_handler_t     completion_handler;
    uint32_t                src_addr;
    uint32_t                des_addr;
    uint32_t                xfr_size;
    uint8_t                 xfr_dir;
} hpdma_xfer_info_t;

/*-------------------------------------------------------------------------*//**
  Current transfer state information.
 */
static hpdma_xfer_info_t g_transfer;

/*-------------------------------------------------------------------------*//**
  Interrupt service routines function prototypes.
  The name of these interrupt service routines must match the name of the ISRs
  defined in startup_m2sxxx.s distributed as part of the SmartFusion2 CMSIS.
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void HPDMA_Complete_IRQHandler(void);
#else
void HPDMA_Complete_IRQHandler(void);
#endif 

#if defined(__GNUC__)
__attribute__((__interrupt__)) void HPDMA_Error_IRQHandler(void);
#else
void HPDMA_Error_IRQHandler(void);
#endif 

/*-------------------------------------------------------------------------*//**
 * See "mss_hpdma.h" for details of how to use this function.
 */
void
MSS_HPDMA_init
(
    void
)
{
    /* Reset HPDMA block. */
    SYSREG->SOFT_RST_CR |= HPDMA_SOFT_RESET;

    /* Take HPDMA controller out of reset. */
    SYSREG->SOFT_RST_CR &= ~HPDMA_SOFT_RESET;

    /* Initialize data structures. */
    g_transfer.xfr_size = 0u;
    g_transfer.completion_handler = NULL_HANDLER;
    g_transfer.state = HPDMA_COMPLETED;
    
    /* Disable Interrupt. */
    HPDMA->Descriptor[DESC0].HPDMACR_REG &= ~HPDMACR_ALL_IRQ_ENABLE_MASK;

    /* Clear any previously pended MSS HPDMA interrupt. */
    NVIC_ClearPendingIRQ(HPDMA_Error_IRQn);
    NVIC_ClearPendingIRQ(HPDMA_Complete_IRQn);
    
    /* Clear all interrupts. */
    HPDMA->HPDMAICR_REG = HPDMAICR_CLEAR_ALL_IRQ;
}

/*-------------------------------------------------------------------------*//**
 * See "mss_hpdma.h" for details of how to use this function.
 */
void
MSS_HPDMA_start
(
    uint32_t src_addr,
    uint32_t dest_addr,
    uint32_t transfer_size,
    uint8_t transfer_dir
)
{
    /* Pause transfer. */
    HPDMA_BITBAND->Descriptor[DESC0].HPDMACR_DCP_PAUSE = HPDMA_ENABLE;
    
    /*
     * Disable all interrupts for the current descriptor. Treat this function as a
     * critical section. Pausing the descriptor transfer is not sufficient in case
     * of non-aligned errors.
     */
    HPDMA->Descriptor[DESC0].HPDMACR_REG &= ~HPDMACR_ALL_IRQ_ENABLE_MASK;
    
    /* Set descriptor transfer direction */
    HPDMA_BITBAND->Descriptor[DESC0].HPDMACR_DCP_XFR_DIR = transfer_dir;

    /* Store Source and destination Address */
    HPDMA->Descriptor[DESC0].HPDMASAR_REG = src_addr;
    HPDMA->Descriptor[DESC0].HPDMADAR_REG = dest_addr;

    /* Set the transfer size to 64K */
    HPDMA->Descriptor[DESC0].HPDMACR_REG &= HPDMA_XFR_SIZE_MASK;

    g_transfer.state = HPDMA_IN_PROGRESS;
    if(transfer_size <= MAX_SIZE_PER_DMA_XFR)
    {
        /* Set descriptor transfer size */
        HPDMA->Descriptor[DESC0].HPDMACR_REG |= (uint16_t)transfer_size;
        g_transfer.xfr_size = 0u;
    }
    else
    {
        g_transfer.xfr_size = transfer_size - MAX_SIZE_PER_DMA_XFR;
        g_transfer.des_addr = dest_addr + MAX_SIZE_PER_DMA_XFR;
        g_transfer.src_addr = src_addr + MAX_SIZE_PER_DMA_XFR;
        g_transfer.xfr_dir = transfer_dir;
    }

    /* Enable interrupts for the requested descriptor. */
    HPDMA->Descriptor[DESC0].HPDMACR_REG |= HPDMACR_ALL_IRQ_ENABLE_MASK;
    NVIC_EnableIRQ(HPDMA_Complete_IRQn);
    NVIC_EnableIRQ(HPDMA_Error_IRQn);
    
    /* Set valid descriptor to start transfer */
    HPDMA_BITBAND->Descriptor[DESC0].HPDMACR_DCP_VALID = HPDMA_ENABLE;

    /* Start transfer */
    HPDMA_BITBAND->Descriptor[DESC0].HPDMACR_DCP_PAUSE = HPDMA_DISABLE;
}

/*-------------------------------------------------------------------------*//**
 * See "mss_hpdma.h" for details of how to use this function.
 */
void
MSS_HPDMA_pause
(
    void
)
{
    /* Pause transfer */
    HPDMA_BITBAND->Descriptor[DESC0].HPDMACR_DCP_PAUSE = HPDMA_ENABLE;
}

/*-------------------------------------------------------------------------*//**
 * See "mss_hpdma.h" for details of how to use this function.
 */
void
MSS_HPDMA_resume
(
    void
)
{
    /* Resume transfer */
    HPDMA_BITBAND->Descriptor[DESC0].HPDMACR_DCP_PAUSE = HPDMA_DISABLE;
}

/*-------------------------------------------------------------------------*//**
 * See "mss_hpdma.h" for details of how to use this function.
 */
void
MSS_HPDMA_abort
(
    void
)
{
    HPDMA_BITBAND->Descriptor[DESC0].HPDMACR_DCP_CLR = HPDMA_ENABLE;
}

/*-------------------------------------------------------------------------*//**
 * See "mss_hpdma.h" for details of how to use this function.
 */
hpdma_status_t
MSS_HPDMA_get_transfer_status
(
    void
)
{
    return g_transfer.state;
}

/*-------------------------------------------------------------------------*//**
 * See "mss_hpdma.h" for details of how to use this function.
 */
void MSS_HPDMA_set_handler
(
    mss_hpdma_handler_t handler
)
{
    if(handler == NULL_HANDLER)
    {
        g_transfer.completion_handler = NULL_HANDLER;
    }
    else
    {
        g_transfer.completion_handler = handler;
    }
}

/*------------------------------------------------------------------------------
  HPDMA Transfer complete service routine.
  This function will be called as a result of any descriptor transfer
  is completed by HPDMA controller .
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void HPDMA_Complete_IRQHandler(void)
#else
void HPDMA_Complete_IRQHandler(void)
#endif 
{
    /* Clear interrupt */
    HPDMA_BITBAND->HPDMAICR_CLR_XFR_INT[DESC0] = HPDMA_ENABLE;

    if(g_transfer.xfr_size > 0u)
    {
        MSS_HPDMA_start(g_transfer.src_addr,
                        g_transfer.des_addr,
                        g_transfer.xfr_size,
                        g_transfer.xfr_dir);
    }
    else
    {
        g_transfer.state = HPDMA_COMPLETED;
        if(g_transfer.completion_handler != NULL_HANDLER)
        {
            (*(g_transfer.completion_handler))(HPDMA_COMPLETED);
        }
    }
}

/*------------------------------------------------------------------------------
  HPDMA Transfer Error service routine.
  This function will be called as a result of any descriptor transfer
  has an error condition or it there is non word transfer size error.
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void HPDMA_Error_IRQHandler(void)
#else
void HPDMA_Error_IRQHandler(void)
#endif 
{
    uint32_t error_bits;

    /*
     * Handle source/destination errors.
     */
    error_bits = HPDMA->HPDMAEDR_REG & HPDMAEDR_DCP_ERR_MASK;
    if(error_bits != 0u)
    {
        if(g_transfer.completion_handler != NULL_HANDLER)
        {
            if(HPDMA_BITBAND->Descriptor[DESC0].HPDMASR_DCP_SERR)
            {
                g_transfer.state = HPDMA_SOURCE_ERROR;
                (*(g_transfer.completion_handler))(HPDMA_SOURCE_ERROR);
            }
            
            if(HPDMA_BITBAND->Descriptor[DESC0].HPDMASR_DCP_DERR)
            {
                g_transfer.state = HPDMA_DESTINATION_ERROR;
                (*(g_transfer.completion_handler))(HPDMA_DESTINATION_ERROR);
            }
        }
        /* Abort transfer. */
        HPDMA_BITBAND->Descriptor[DESC0].HPDMACR_DCP_CLR = HPDMA_ENABLE;
        /* Clear interrupt. */
        HPDMA_BITBAND->HPDMAICR_CLR_XFR_INT[DESC0] = HPDMA_ENABLE;
    }
    
    /*
     * Handle non word aligned errors.
     */
    error_bits = HPDMA->HPDMAEDR_REG & HPDMAEDR_NON_WORD_ERR_MASK;
    if(error_bits != 0u)
    {
        g_transfer.state = HPDMA_WORD_ALIGN_ERROR;
        /* Call handler. */
        if(g_transfer.completion_handler != NULL_HANDLER)
        {
            (*(g_transfer.completion_handler))(HPDMA_WORD_ALIGN_ERROR);
        }
        /* Abort transfer. */
        HPDMA_BITBAND->Descriptor[DESC0].HPDMACR_DCP_CLR = HPDMA_ENABLE;
        /* Clear interrupt. */
        HPDMA_BITBAND->HPDMAICR_NON_WORD_INT[DESC0] = HPDMA_ENABLE;
    }
}

#ifdef __cplusplus
}
#endif

