/*******************************************************************************
 * (c) Copyright 2008 Actel Corporation.  All rights reserved.
 * 
 * SmartFusion microcontroller subsystem Peripheral DMA bare metal software
 * driver implementation.
 *
 * SVN $Revision: 2110 $
 * SVN $Date: 2010-02-05 15:24:19 +0000 (Fri, 05 Feb 2010) $
 */
#include "mss_pdma.h"
#include "../../CMSIS/mss_assert.h"

#ifdef __cplusplus
extern "C" {
#endif 

#if defined(__GNUC__)
__attribute__((__interrupt__)) void DMA_IRQHandler( void );
#else
void DMA_IRQHandler( void );
#endif

/***************************************************************************//**
  Offset of the posted writes WRITE_ADJ bits in a PDMA channel's configuration
  register.
 */
#define CHANNEL_N_POSTED_WRITE_ADJUST_SHIFT   14

/*-------------------------------------------------------------------------*//**
 * Look-up table use to derice a channel's control register value from the
 * requested source/destination. This table is incexed on the pdma_src_dest_t
 * enumeration.
 */
#define CHANNEL_N_CTRL_PDMA_MASK        (uint32_t)0x00000001
#define CHANNEL_N_PERIPH_SELECT_SHIFT   (uint32_t)23
#define CHANNEL_N_DIRECTION_MASK        (uint32_t)0x00000002

const uint32_t src_dest_to_ctrl_reg_lut[] =
{
    CHANNEL_N_CTRL_PDMA_MASK,                                                                               /* PDMA_FROM_UART_0 */
    CHANNEL_N_CTRL_PDMA_MASK | ( (uint32_t)1 << CHANNEL_N_PERIPH_SELECT_SHIFT) | CHANNEL_N_DIRECTION_MASK,  /* PDMA_TO_UART_0 */
    CHANNEL_N_CTRL_PDMA_MASK | ( (uint32_t)2 << CHANNEL_N_PERIPH_SELECT_SHIFT),                             /* PDMA_FROM_UART_1 */
    CHANNEL_N_CTRL_PDMA_MASK | ( (uint32_t)3 << CHANNEL_N_PERIPH_SELECT_SHIFT) | CHANNEL_N_DIRECTION_MASK,  /* PDMA_TO_UART_1 */
    CHANNEL_N_CTRL_PDMA_MASK | ( (uint32_t)4 << CHANNEL_N_PERIPH_SELECT_SHIFT),                             /* PDMA_FROM_SPI_0 */
    CHANNEL_N_CTRL_PDMA_MASK | ( (uint32_t)5 << CHANNEL_N_PERIPH_SELECT_SHIFT) | CHANNEL_N_DIRECTION_MASK,  /* PDMA_TO_SPI_0 */
    CHANNEL_N_CTRL_PDMA_MASK | ( (uint32_t)6 << CHANNEL_N_PERIPH_SELECT_SHIFT),                             /* PDMA_FROM_SPI_1 */
    CHANNEL_N_CTRL_PDMA_MASK | ( (uint32_t)7 << CHANNEL_N_PERIPH_SELECT_SHIFT) | CHANNEL_N_DIRECTION_MASK,  /* PDMA_TO_SPI_1 */
    CHANNEL_N_CTRL_PDMA_MASK | ( (uint32_t)8 << CHANNEL_N_PERIPH_SELECT_SHIFT),                             /* PDMA_FROM_FPGA_1 */
    CHANNEL_N_CTRL_PDMA_MASK | ( (uint32_t)8 << CHANNEL_N_PERIPH_SELECT_SHIFT) | CHANNEL_N_DIRECTION_MASK,  /* PDMA_TO_FPGA_1 */
    CHANNEL_N_CTRL_PDMA_MASK | ( (uint32_t)9 << CHANNEL_N_PERIPH_SELECT_SHIFT),                             /* PDMA_FROM_FPGA_0 */
    CHANNEL_N_CTRL_PDMA_MASK | ( (uint32_t)9 << CHANNEL_N_PERIPH_SELECT_SHIFT) | CHANNEL_N_DIRECTION_MASK,  /* PDMA_TO_FPGA_0 */
    CHANNEL_N_CTRL_PDMA_MASK | ( (uint32_t)10 << CHANNEL_N_PERIPH_SELECT_SHIFT) | CHANNEL_N_DIRECTION_MASK, /* PDMA_TO_ACE */
    CHANNEL_N_CTRL_PDMA_MASK | ( (uint32_t)11 << CHANNEL_N_PERIPH_SELECT_SHIFT)                             /* PDMA_FROM_ACE */
};

/*-------------------------------------------------------------------------*//**
 *
 */
#define PDMA_MASTER_ENABLE  (uint32_t)0x04
#define PDMA_SOFT_RESET     (uint32_t)0x20

/*-------------------------------------------------------------------------*//**
 *
 */
#define NB_OF_PDMA_CHANNELS     8

#define NEXT_CHANNEL_A      0U
#define NEXT_CHANNEL_B      1U

#define CHANNEL_STOPPED     0U
#define CHANNEL_STARTED     1U

static uint8_t g_pdma_next_channel[NB_OF_PDMA_CHANNELS];
static uint8_t g_pdma_started_a[NB_OF_PDMA_CHANNELS];
static uint8_t g_pdma_started_b[NB_OF_PDMA_CHANNELS];
static pdma_channel_isr_t g_pdma_isr_table[NB_OF_PDMA_CHANNELS];
static const uint16_t g_pdma_status_mask[NB_OF_PDMA_CHANNELS] =
{
    (uint16_t)0x0003, /* PDMA_CHANNEL_0 */
    (uint16_t)0x000C, /* PDMA_CHANNEL_1 */
    (uint16_t)0x0030, /* PDMA_CHANNEL_2 */
    (uint16_t)0x00C0, /* PDMA_CHANNEL_3 */
    (uint16_t)0x0300, /* PDMA_CHANNEL_4 */
    (uint16_t)0x0C00, /* PDMA_CHANNEL_5 */
    (uint16_t)0x3000, /* PDMA_CHANNEL_6 */
    (uint16_t)0xC000, /* PDMA_CHANNEL_7 */
};



/***************************************************************************//**
 * See mss_pdma.h for description of this function.
 */
void PDMA_init( void )
{
    int32_t i;
    
    /* Enable PDMA master access to comms matrix. */
    SYSREG->AHB_MATRIX_CR |= PDMA_MASTER_ENABLE;
    
    /* Reset PDMA block. */
    SYSREG->SOFT_RST_CR |= PDMA_SOFT_RESET;
    
    /* Clear any previously pended MSS PDMA interrupt */
    NVIC_ClearPendingIRQ( DMA_IRQn );
        
    /* Take PDMA controller out of reset*/
    SYSREG->SOFT_RST_CR &= ~PDMA_SOFT_RESET;
    
    /* Initialize channels state information. */
    for ( i = 0; i < NB_OF_PDMA_CHANNELS; ++i )
    {
        g_pdma_next_channel[i] = NEXT_CHANNEL_A;
        g_pdma_started_a[i] = CHANNEL_STOPPED;
        g_pdma_started_b[i] = CHANNEL_STOPPED;
        g_pdma_isr_table[i] = 0;
    }
}

/***************************************************************************//**
 * See mss_pdma.h for description of this function.
 */
#define CHANNEL_RESET_MASK  (uint32_t)0x00000020

void PDMA_configure
(
    pdma_channel_id_t channel_id,
    pdma_src_dest_t src_dest,
    uint32_t channel_cfg,
    uint8_t write_adjust
)
{
    /* Reset the channel. */
    PDMA->CHANNEL[channel_id].CRTL |= CHANNEL_RESET_MASK;
    PDMA->CHANNEL[channel_id].CRTL &= ~CHANNEL_RESET_MASK;

    /* Configure PDMA channel's data source and destination. */
    if ( src_dest != PDMA_MEM_TO_MEM )
    {
        PDMA->CHANNEL[channel_id].CRTL |= src_dest_to_ctrl_reg_lut[src_dest];
    }
    
    /* Configure PDMA channel trnasfer size, priority, source and destination address increment. */
    PDMA->CHANNEL[channel_id].CRTL |= channel_cfg;

    /* Posted write adjust. */
    PDMA->CHANNEL[channel_id].CRTL |= ((uint32_t)write_adjust << CHANNEL_N_POSTED_WRITE_ADJUST_SHIFT);
}

/***************************************************************************//**
 * See mss_pdma.h for description of this function.
 */
#define PAUSE_MASK  (uint32_t)0x00000010

#define BUFFER_B_SELECT_MASK    (uint32_t)0x00000004

#define CLEAR_PORT_A_DONE_MASK      (uint32_t)0x00000080
#define CLEAR_PORT_B_DONE_MASK      (uint32_t)0x00000100

#define PORT_A_COMPLETE_MASK        (uint32_t)0x00000001
#define PORT_B_COMPLETE_MASK        (uint32_t)0x00000002

void PDMA_start
(
    pdma_channel_id_t channel_id,
    uint32_t src_addr,
    uint32_t dest_addr,
    uint16_t transfer_count
)
{
    /* Pause transfer. */
    PDMA->CHANNEL[channel_id].CRTL |= PAUSE_MASK;
    
    /* Clear complete transfers. */
    if ( PDMA->CHANNEL[channel_id].STATUS & PORT_A_COMPLETE_MASK )
    {
        PDMA->CHANNEL[channel_id].CRTL |= CLEAR_PORT_A_DONE_MASK;
        g_pdma_started_a[channel_id] = CHANNEL_STOPPED;
    }
    if ( PDMA->CHANNEL[channel_id].STATUS & PORT_B_COMPLETE_MASK )
    {
        PDMA->CHANNEL[channel_id].CRTL |= CLEAR_PORT_B_DONE_MASK;
        g_pdma_started_b[channel_id] = CHANNEL_STOPPED;
    }
    
    /* Load source, destination and transfer count. */
    if ( PDMA->CHANNEL[channel_id].STATUS & BUFFER_B_SELECT_MASK )
    {
        g_pdma_next_channel[channel_id] = NEXT_CHANNEL_A;
        g_pdma_started_b[channel_id] = CHANNEL_STARTED;
        
        PDMA->CHANNEL[channel_id].BUFFER_B_SRC_ADDR = src_addr;
        PDMA->CHANNEL[channel_id].BUFFER_B_DEST_ADDR = dest_addr;
        PDMA->CHANNEL[channel_id].BUFFER_B_TRANSFER_COUNT = transfer_count;
    }
    else
    {
        g_pdma_next_channel[channel_id] = NEXT_CHANNEL_B;
        g_pdma_started_a[channel_id] = CHANNEL_STARTED;
        
        PDMA->CHANNEL[channel_id].BUFFER_A_SRC_ADDR = src_addr;
        PDMA->CHANNEL[channel_id].BUFFER_A_DEST_ADDR = dest_addr;
        PDMA->CHANNEL[channel_id].BUFFER_A_TRANSFER_COUNT = transfer_count;
    }
    
    /* Start transfer */
    PDMA->CHANNEL[channel_id].CRTL &= ~PAUSE_MASK;
}

/***************************************************************************//**
 * See mss_pdma.h for description of this function.
 */
void PDMA_load_next_buffer
(
    pdma_channel_id_t channel_id,
    uint32_t src_addr,
    uint32_t dest_addr,
    uint16_t transfer_count
)
{
    if ( NEXT_CHANNEL_A == g_pdma_next_channel[channel_id] )
    {
        /* Wait for channel A current transfer completion. */
        if ( CHANNEL_STARTED == g_pdma_started_a[channel_id] )
        {
            uint32_t completed;
            uint32_t channel_mask;
            channel_mask = (uint32_t)1 << ((uint32_t)channel_id * 2U);
            do {
                completed = PDMA->BUFFER_STATUS & channel_mask;
            } while( !completed );
            PDMA->CHANNEL[channel_id].CRTL |= CLEAR_PORT_A_DONE_MASK;
        }
        /* Load source, destination and transfer count. */
        PDMA->CHANNEL[channel_id].BUFFER_A_SRC_ADDR = src_addr;
        PDMA->CHANNEL[channel_id].BUFFER_A_DEST_ADDR = dest_addr;
        PDMA->CHANNEL[channel_id].BUFFER_A_TRANSFER_COUNT = transfer_count;
        
        /* Update channel state information. */
        g_pdma_next_channel[channel_id] = NEXT_CHANNEL_B;
        g_pdma_started_a[channel_id] = CHANNEL_STARTED;
    }
    else
    {
        /* Wait for channel B current transfer completion. */
        if ( CHANNEL_STARTED == g_pdma_started_b[channel_id] )
        {
            uint32_t completed;
            uint32_t channel_mask;
            channel_mask = (uint32_t)1 << (((uint32_t)channel_id * 2U) + 1U);
            do {
                completed = PDMA->BUFFER_STATUS & channel_mask;
            } while( !completed );
            PDMA->CHANNEL[channel_id].CRTL |= CLEAR_PORT_B_DONE_MASK;
        }            
        /* Load source, destination and transfer count. */
        PDMA->CHANNEL[channel_id].BUFFER_B_SRC_ADDR = src_addr;
        PDMA->CHANNEL[channel_id].BUFFER_B_DEST_ADDR = dest_addr;
        PDMA->CHANNEL[channel_id].BUFFER_B_TRANSFER_COUNT = transfer_count;
        
        /* Update channel state information. */
        g_pdma_next_channel[channel_id] = NEXT_CHANNEL_A;
        g_pdma_started_b[channel_id] = CHANNEL_STARTED;
    }
}

/***************************************************************************//**
 * See mss_pdma.h for description of this function.
 */
uint32_t PDMA_status
(
    pdma_channel_id_t  channel_id
)
{
    uint32_t status;
    
    status = PDMA->CHANNEL[channel_id].STATUS & (PORT_A_COMPLETE_MASK | PORT_B_COMPLETE_MASK);
    
    return status;
}

/***************************************************************************//**
 *
 */
#define CHANNEL_0_STATUS_BITS_MASK     (uint16_t)0x0003
#define CHANNEL_1_STATUS_BITS_MASK     (uint16_t)0x000C
#define CHANNEL_2_STATUS_BITS_MASK     (uint16_t)0x0030
#define CHANNEL_3_STATUS_BITS_MASK     (uint16_t)0x00C0
#define CHANNEL_4_STATUS_BITS_MASK     (uint16_t)0x0300
#define CHANNEL_5_STATUS_BITS_MASK     (uint16_t)0x0C00
#define CHANNEL_6_STATUS_BITS_MASK     (uint16_t)0x3000
#define CHANNEL_7_STATUS_BITS_MASK     (uint16_t)0xC000

static pdma_channel_id_t get_channel_id_from_status
(
    uint16_t status
)
{
    pdma_channel_id_t channel_id = PDMA_CHANNEL_0;
    
    if ( status & CHANNEL_0_STATUS_BITS_MASK )
    {
        channel_id = PDMA_CHANNEL_0;
    }
    else if ( status & CHANNEL_1_STATUS_BITS_MASK )
    {
        channel_id = PDMA_CHANNEL_1;
    }
    else if ( status & CHANNEL_2_STATUS_BITS_MASK )
    {
        channel_id = PDMA_CHANNEL_2;
    }
    else if ( status & CHANNEL_3_STATUS_BITS_MASK )
    {
        channel_id = PDMA_CHANNEL_3;
    }
    else if ( status & CHANNEL_4_STATUS_BITS_MASK )
    {
        channel_id = PDMA_CHANNEL_4;
    }
    else if ( status & CHANNEL_5_STATUS_BITS_MASK )
    {
        channel_id = PDMA_CHANNEL_5;
    }
    else if ( status & CHANNEL_6_STATUS_BITS_MASK )
    {
        channel_id = PDMA_CHANNEL_6;
    }
    else if ( status & CHANNEL_7_STATUS_BITS_MASK )
    {
        channel_id = PDMA_CHANNEL_7;
    }
    else
    {
        ASSERT(0);
    }
    return channel_id;
}

/***************************************************************************//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void DMA_IRQHandler( void )
#else
void DMA_IRQHandler( void )
#endif
{
    uint16_t status;
    pdma_channel_id_t channel_id;
    
    status = (uint16_t)PDMA->BUFFER_STATUS;
    
    do {
        channel_id = get_channel_id_from_status( status );
        status &= (uint16_t)~g_pdma_status_mask[channel_id];
        if ( 0 != g_pdma_isr_table[channel_id])
        {
            g_pdma_isr_table[channel_id]();
        }
    } while ( 0U != status );
      
    NVIC_ClearPendingIRQ( DMA_IRQn );
}

/***************************************************************************//**
 * See mss_pdma.h for description of this function.
 */
void PDMA_set_irq_handler
(
    pdma_channel_id_t channel_id,
    pdma_channel_isr_t handler
)
{
    /* Save address of handler function in PDMA driver ISR lookup table. */
    g_pdma_isr_table[channel_id] = handler;
    
    /* Enable PDMA channel's interrupt. */
    PDMA->CHANNEL[channel_id].CRTL |= PDMA_IRQ_ENABLE_MASK;
    
    /* Enable PDMA interrupt in Cortex-M3 NVIC. */
    NVIC_EnableIRQ( DMA_IRQn );
}

/***************************************************************************//**
 * See mss_pdma.h for description of this function.
 */
void PDMA_enable_irq( pdma_channel_id_t channel_id )
{
    PDMA->CHANNEL[channel_id].CRTL |= PDMA_IRQ_ENABLE_MASK;
    NVIC_EnableIRQ( DMA_IRQn );
}

/***************************************************************************//**
 * See mss_pdma.h for description of this function.
 */
void PDMA_clear_irq
(
    pdma_channel_id_t channel_id
)
{
    /* Clear interrupt in PDMA controller. */
    PDMA->CHANNEL[channel_id].CRTL |= CLEAR_PORT_A_DONE_MASK;
    PDMA->CHANNEL[channel_id].CRTL |= CLEAR_PORT_B_DONE_MASK;
    
    /* Clear interrupt in Cortex-M3 NVIC. */
    NVIC_ClearPendingIRQ( DMA_IRQn );
}

#ifdef __cplusplus
}
#endif

