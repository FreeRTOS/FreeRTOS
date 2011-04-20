/*******************************************************************************
 * (c) Copyright 2009 Actel Corporation.  All rights reserved.
 * 
 * SVN $Revision: 2905 $
 * SVN $Date: 2010-08-20 14:03:28 +0100 (Fri, 20 Aug 2010) $
 */
#include "mss_ace.h"
#include "mss_ace_configurator.h"
#include "../../drivers_config/mss_ace/ace_handles.h"
#include "../../drivers_config/mss_ace/ace_config.h"

#include "../../CMSIS/a2fxxxm3.h"
#include "../../CMSIS/mss_assert.h"
#include <string.h>

#ifdef __cplusplus
extern "C" {
#endif 

#define SSE_START       1uL
#define SSE_STOP        0uL

#define NB_OF_ANALOG_BLOCKS     3u
#define SEE_RAM_WORD_SIZE       512

#define TS_ENABLE_MASK          0x01u
#define PPE_ENABLE_MASK         0x01u
#define ADC_RESET_MASK          0x10u
#define ADC_FIFO_CLR_MASK       0x04u
#define PDMA_DATAOUT_CLR_MASK   0x04u


/*-------------------------------------------------------------------------*//**
 *
 */
extern ace_procedure_desc_t g_sse_sequences_desc_table[ACE_NB_OF_SSE_PROCEDURES];
 
/*-------------------------------------------------------------------------*//**
 *
 */
sse_sequence_handle_t
ACE_get_sse_seq_handle
(
    const uint8_t * p_sz_sequence_name
)
{
    uint16_t seq_idx;
    sse_sequence_handle_t handle = INVALID_SSE_SEQ_HANDLE;
    
    for ( seq_idx = 0u;  seq_idx < (uint32_t)ACE_NB_OF_SSE_PROCEDURES; ++seq_idx )
    {
        if ( g_sse_sequences_desc_table[seq_idx].p_sz_proc_name != 0 )
        {
            int32_t diff;
            diff = strncmp( (const char *)p_sz_sequence_name, (const char *)g_sse_sequences_desc_table[seq_idx].p_sz_proc_name, MAX_PROCEDURE_NAME_LENGTH );
            if ( 0 == diff )
            {
                /* channel name found. */
                handle = seq_idx;
                break;
            }
        }
    }
    return handle;
}

/*-------------------------------------------------------------------------*//**
 *
 */
static uint32_t volatile * const sse_pc_ctrl_lut[NB_OF_ANALOG_BLOCKS] =
{
    &ACE->PC0_CTRL,
    &ACE->PC1_CTRL,
    &ACE->PC2_CTRL
};

static uint32_t volatile * const sse_pc_lo_lut[NB_OF_ANALOG_BLOCKS] =
{
    &ACE->PC0_LO,
    &ACE->PC1_LO,
    &ACE->PC2_LO
};

static uint32_t volatile * const sse_pc_hi_lut[NB_OF_ANALOG_BLOCKS] =
{
    &ACE->PC0_HI,
    &ACE->PC1_HI,
    &ACE->PC2_HI
};

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_load_sse
(
    sse_sequence_handle_t  sequence
)
{
    ASSERT( sequence < (sse_sequence_handle_t)ACE_NB_OF_SSE_PROCEDURES );
    
    if ( sequence < (sse_sequence_handle_t)ACE_NB_OF_SSE_PROCEDURES )
    {
        uint16_t i;
        uint16_t offset;
        const uint16_t * p_ucode;
        
        ASSERT( g_sse_sequences_desc_table[sequence].sse_pc_id < NB_OF_ANALOG_BLOCKS );
        
        if ( g_sse_sequences_desc_table[sequence].sse_pc_id < NB_OF_ANALOG_BLOCKS )
        {
            /* Stop relevant program counter. */
            *sse_pc_ctrl_lut[g_sse_sequences_desc_table[sequence].sse_pc_id] = SSE_STOP;
            
            /* Load microcode into SEE RAM.*/
            p_ucode = g_sse_sequences_desc_table[sequence].sse_ucode;
            offset = g_sse_sequences_desc_table[sequence].sse_load_offset;
            
            for ( i = 0u; i < g_sse_sequences_desc_table[sequence].sse_ucode_length; ++i )
            {
                ACE->SSE_RAM_DATA[offset + i] = (uint32_t)*p_ucode;
                ++p_ucode;
            }
        }
    }
}


/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_start_sse
(
    sse_sequence_handle_t  sequence
)
{
    ASSERT( sequence < (sse_sequence_handle_t)ACE_NB_OF_SSE_PROCEDURES );
    
    if ( sequence < (sse_sequence_handle_t)ACE_NB_OF_SSE_PROCEDURES )
    {
        uint16_t pc;
        
        ASSERT( g_sse_sequences_desc_table[sequence].sse_pc_id < NB_OF_ANALOG_BLOCKS );
        ASSERT( g_sse_sequences_desc_table[sequence].sse_load_offset < SEE_RAM_WORD_SIZE );
    
        pc = g_sse_sequences_desc_table[sequence].sse_load_offset;
        
        if ( pc < 256u )
        {
            *sse_pc_lo_lut[g_sse_sequences_desc_table[sequence].sse_pc_id] = pc;
        }
        else
        {
            *sse_pc_hi_lut[g_sse_sequences_desc_table[sequence].sse_pc_id] = pc - 256;
        }
        
        *sse_pc_ctrl_lut[g_sse_sequences_desc_table[sequence].sse_pc_id] = SSE_START;
        
        /* Enable Sample Sequencing Engine in case it was not done as part of
         * system boot. */
        ACE->SSE_TS_CTRL |= TS_ENABLE_MASK;
    }
}

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_restart_sse
(
    sse_sequence_handle_t  sequence
)
{
    ASSERT( sequence < ACE_NB_OF_SSE_PROCEDURES );
    ASSERT( g_sse_sequences_desc_table[sequence].sse_pc_id < NB_OF_ANALOG_BLOCKS );
    ASSERT( g_sse_sequences_desc_table[sequence].sse_load_offset < SEE_RAM_WORD_SIZE );
    
    if ( sequence < (sse_sequence_handle_t)ACE_NB_OF_SSE_PROCEDURES )
    {
        uint16_t pc;
        
        pc = g_sse_sequences_desc_table[sequence].sse_loop_pc;
        
        if ( pc < 256u )
        {
            *sse_pc_lo_lut[g_sse_sequences_desc_table[sequence].sse_pc_id] = pc;
        }
        else
        {
            *sse_pc_hi_lut[g_sse_sequences_desc_table[sequence].sse_pc_id] = pc - 256;
        }
        
        *sse_pc_ctrl_lut[g_sse_sequences_desc_table[sequence].sse_pc_id] = SSE_START;
    }
}

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_stop_sse
(
    sse_sequence_handle_t  sequence
)
{
    ASSERT( sequence < ACE_NB_OF_SSE_PROCEDURES );
    
    if ( sequence < (sse_sequence_handle_t)ACE_NB_OF_SSE_PROCEDURES )
    {
        /* Stop relevant program counter. */
        *sse_pc_ctrl_lut[g_sse_sequences_desc_table[sequence].sse_pc_id] = SSE_STOP;
    }
}

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_resume_sse
(
    sse_sequence_handle_t  sequence
)
{
    ASSERT( sequence < ACE_NB_OF_SSE_PROCEDURES );
    
    if ( sequence < (sse_sequence_handle_t)ACE_NB_OF_SSE_PROCEDURES )
    {
        *sse_pc_ctrl_lut[g_sse_sequences_desc_table[sequence].sse_pc_id] = SSE_START;
    }
}

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_enable_sse_irq
(
	sse_irq_id_t sse_irq_id
)
{
    ASSERT( sse_irq_id < NB_OF_SSE_FLAG_IRQS );
    
    ACE->SSE_IRQ_EN |= 1uL << (uint32_t)sse_irq_id;
}

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_disable_sse_irq
(
	sse_irq_id_t sse_irq_id
)
{
    ASSERT( sse_irq_id < NB_OF_SSE_FLAG_IRQS );
    
    ACE->SSE_IRQ_EN &= (uint32_t)~(1uL << (uint32_t)sse_irq_id);
}

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_clear_sse_irq
(
	sse_irq_id_t sse_irq_id
)
{
    ASSERT( sse_irq_id < NB_OF_SSE_FLAG_IRQS );
    
    ACE->SSE_IRQ_CLR |= 1uL << (uint32_t)sse_irq_id;
}

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_clear_sample_pipeline(void)
{
    uint32_t saved_sse_ctrl;
    uint32_t saved_ppe_ctrl;
    
    /* Pause the Sample Sequencing Engine. */
    saved_sse_ctrl = ACE->SSE_TS_CTRL;
    ACE->SSE_TS_CTRL = ACE->SSE_TS_CTRL & ~((uint32_t)TS_ENABLE_MASK);
    
    /* Pause the Post Processing Engine. */
    saved_ppe_ctrl = ACE->PPE_CTRL;
    ACE->PPE_CTRL = ACE->PPE_CTRL & ~((uint32_t)PPE_ENABLE_MASK);
    
    /* Reset the ADCs */
    ACE->ADC0_MISC_CTRL |= ADC_RESET_MASK;
    ACE->ADC1_MISC_CTRL |= ADC_RESET_MASK;
    ACE->ADC2_MISC_CTRL |= ADC_RESET_MASK;
    
    /* Clear ADC FIFOs */
    ACE->ADC0_FIFO_CTRL |= ADC_FIFO_CLR_MASK;
    ACE->ADC1_FIFO_CTRL |= ADC_FIFO_CLR_MASK;
    ACE->ADC2_FIFO_CTRL |= ADC_FIFO_CLR_MASK;
    
    /* clear DMA FIFOs */
    ACE->PPE_PDMA_CTRL |= PDMA_DATAOUT_CLR_MASK;
    
    /* Unpause the Post Processing Engine. */
    ACE->PPE_CTRL = saved_ppe_ctrl;
    
    /* Unpause the Sample Sequencing Engine. */
    ACE->SSE_TS_CTRL = saved_sse_ctrl;
}

#ifdef __cplusplus
}
#endif

