/*******************************************************************************
 * (c) Copyright 2009 Actel Corporation.  All rights reserved.
 *
 * SVN $Revision: 2905 $
 * SVN $Date: 2010-08-20 14:03:28 +0100 (Fri, 20 Aug 2010) $
 */

#include "mss_ace.h"
#include "mtd_data.h"
#include "envm_layout.h"
#include "mss_ace_configurator.h"
#include "../../CMSIS/a2fxxxm3.h"
#include "../../CMSIS/mss_assert.h"
#include "../../drivers_config/mss_ace/ace_config.h"
#include <string.h>

#ifdef __cplusplus
extern "C" {
#endif

#define START_ADC_CONVERSION    0x80uL


/**/
void ace_init_flags( void );
void ace_init_convert(void);

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
void ACE_init( void )
{
    /* Initialize driver's internal data. */
	#if (ACE_NB_OF_PPE_FLAGS > 0)
	    ace_init_flags();
	#endif

    /* Initialize the data structures used by conversion functions. */
    ace_init_convert();
}

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
void ACE_start_adc
(
	adc_channel_id_t channel_id
)
{
    ACE->ADC0_CONV_CTRL = (uint32_t)channel_id | START_ADC_CONVERSION;
}

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
#define ADC_DATAVALID_MASK    0x00001000uL
#define ADC_RESULT_MASK       0x00000FFFuL

static const uint32_t volatile * const adc_status_reg_lut[NB_OF_ANALOG_MODULES] =
{
    &ACE->ADC0_STATUS,
    &ACE->ADC1_STATUS,
    &ACE->ADC2_STATUS
};

uint16_t ACE_get_adc_result
(
    uint8_t adc_id
)
{
    uint16_t result = 0u;
    uint32_t data_valid;

    ASSERT( adc_id < NB_OF_ANALOG_MODULES );

    if ( adc_id < (uint8_t)NB_OF_ANALOG_MODULES )
    {
        do {
            data_valid = *adc_status_reg_lut[adc_id] & ADC_DATAVALID_MASK;
        } while ( !data_valid );

        result = (uint16_t)(*adc_status_reg_lut[adc_id] & ADC_RESULT_MASK);
    }
    return result;
}

/*==============================================================================
 =========== Sigma Delta Digital to Analog Converters (SDD) Control ============
 =============================================================================*/

#define SDD_ENABLE_MASK     0x20uL
#define SDD_REG_SEL_MASK    0x40uL

#define DAC0_SYNC_EN_MASK   0x10uL
#define DAC1_SYNC_EN_MASK   0x20uL
#define DAC2_SYNC_EN_MASK   0x40uL

#define DAC0_SYNC_UPDATE    0x01uL
#define DAC1_SYNC_UPDATE    0x02uL
#define DAC2_SYNC_UPDATE    0x04uL

/*-------------------------------------------------------------------------*//**
 *
 */
static volatile uint32_t * const dac_ctrl_reg_lut[NB_OF_ANALOG_MODULES] =
{
    &ACE->DAC0_CTRL,
    &ACE->DAC1_CTRL,
    &ACE->DAC1_CTRL
};

static const uint32_t dac_enable_masks_lut[NB_OF_ANALOG_MODULES] =
{
    DAC0_SYNC_EN_MASK,
    DAC1_SYNC_EN_MASK,
    DAC2_SYNC_EN_MASK
};

static volatile uint32_t * const dac_byte01_reg_lut[NB_OF_ANALOG_MODULES] =
{
    &ACE->SSE_DAC0_BYTES01,
    &ACE->SSE_DAC1_BYTES01,
    &ACE->SSE_DAC2_BYTES01,
};

static volatile uint32_t * const dac_byte2_reg_lut[NB_OF_ANALOG_MODULES] =
{
    &ACE->DAC0_BYTE2,
    &ACE->DAC1_BYTE2,
    &ACE->DAC2_BYTE2
};

/*------------------------------------------------------------------------------
 * Pointer to the manufacturing test data containing trimming information
 * generated during manufacturing.
 */
static const mtd_data_t * const p_mtd_data = (mtd_data_t *)MTD_ADDRESS;

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
#define OBD_MODE_MASK       (uint8_t)0x01
#define OBD_CHOPPING_MASK   (uint8_t)0x02

void ACE_configure_sdd
(
	sdd_id_t            sdd_id,
	sdd_resolution_t    resolution,
    uint8_t             mode,
    sdd_update_method_t sync_update
)
{
    ASSERT( sdd_id < NB_OF_SDD );

    if ( sdd_id < NB_OF_SDD )
    {
        const uint8_t sdd_2_quad_lut[NB_OF_SDD] = {0u, 2u, 4u};
        uint8_t quad_id;
        uint8_t obd_mode_idx = 1u;
        uint8_t chopping_mode_idx = 0u;
        uint32_t saved_pc2_ctrl;

        quad_id = sdd_2_quad_lut[sdd_id];

        /* Pause the SSE PC2 while accesses to ACB from APB3 are taking place. */
        saved_pc2_ctrl = ACE->PC2_CTRL;
        ACE->PC2_CTRL = 0u;

        /* Select between voltage/current and RTZ modes.*/
        ACE->ACB_DATA[quad_id].b6 = mode;

        /* Load manufacturing generated trim value. */
        if ( (mode & OBD_MODE_MASK) > 0u )
        {
            obd_mode_idx = 0u;
        }
        if ( (mode & OBD_CHOPPING_MASK) > 0u )
        {
            chopping_mode_idx = 1u;
        }
        ACE->ACB_DATA[quad_id].b4
            = p_mtd_data->odb_trimming[sdd_id][obd_mode_idx][chopping_mode_idx];

        /* Restore SSE PC2 operations since no ACB accesses should take place
         * beyond this point. */
        ACE->PC2_CTRL = saved_pc2_ctrl;

        /* Set SDD resolution. */
        *dac_ctrl_reg_lut[sdd_id] = (uint32_t)resolution;

        /* Update SDD value through SSE_DACn_BYTES01. */
        *dac_ctrl_reg_lut[sdd_id] |= SDD_REG_SEL_MASK;

        /* Synchronous or individual SDD update. */
        if ( INDIVIDUAL_UPDATE == sync_update )
        {
            ACE->DAC_SYNC_CTRL &= ~dac_enable_masks_lut[sdd_id];
        }
        else
        {
            ACE->DAC_SYNC_CTRL |= dac_enable_masks_lut[sdd_id];
        }
    }
}

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
void ACE_enable_sdd
(
	sdd_id_t    sdd_id
)
{
    ASSERT( sdd_id < NB_OF_SDD );

    if ( sdd_id < NB_OF_SDD )
    {
        *dac_ctrl_reg_lut[sdd_id] |= SDD_ENABLE_MASK;
    }
}

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
void ACE_disable_sdd
(
	sdd_id_t    sdd_id
)
{
    ASSERT( sdd_id < NB_OF_SDD );

    if ( sdd_id < NB_OF_SDD )
    {
        *dac_ctrl_reg_lut[sdd_id] &= ~SDD_ENABLE_MASK;
    }
}

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
void ACE_set_sdd_value
(
	sdd_id_t    sdd_id,
	uint32_t    sdd_value
)
{
    ASSERT( sdd_id < NB_OF_SDD );

    if ( sdd_id < NB_OF_SDD )
    {
        *dac_byte2_reg_lut[sdd_id] = sdd_value >> 16;
        *dac_byte01_reg_lut[sdd_id] = sdd_value;
    }
}

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
void ACE_set_sdd_value_sync
(
    uint32_t sdd0_value,
    uint32_t sdd1_value,
    uint32_t sdd2_value
)
{
    uint32_t dac_sync_ctrl;

    dac_sync_ctrl = ACE->DAC_SYNC_CTRL;

    if ( SDD_NO_UPDATE != sdd0_value )
    {
        ACE->DAC0_BYTE2 = sdd0_value >> 16;
        ACE->SSE_DAC0_BYTES01 = sdd0_value;
        dac_sync_ctrl |= DAC0_SYNC_UPDATE;
    }

    if ( SDD_NO_UPDATE != sdd1_value )
    {
        ACE->DAC1_BYTE2 = sdd1_value >> 16;
        ACE->SSE_DAC1_BYTES01 = sdd1_value;
        dac_sync_ctrl |= DAC1_SYNC_UPDATE;
    }

    if ( SDD_NO_UPDATE != sdd2_value )
    {
        ACE->DAC2_BYTE2 = sdd2_value >> 16;
        ACE->DAC2_BYTE1 = sdd2_value >> 8;
        ACE->SSE_DAC2_BYTES01 = sdd2_value;
        dac_sync_ctrl |= DAC2_SYNC_UPDATE;
    }

    ACE->DAC_SYNC_CTRL = dac_sync_ctrl;
}

/*==============================================================================
 ============================ Comparators Control ==============================
 =============================================================================*/

 /*
  * SDD Analog switch mask. ACB byte 10.
  *     0:  TMB comparator reference voltage is an ADC direct input
  *     1:  TMB comparator reference voltage is one of the SDD outputs as
  *         selected by DAC_MUXSEL[1:0]
  */
#define B10_COMP_VREF_SW_MASK   0x20u

/*
 * Comparator reference voltage multiplexer.
 * Used to select which SDD output will be used as reference voltage for TMB
 * comparator. These bits are only meaningful when COMP_VREF_SW is set to 1.
 */
#define B11_DAC_MUXSEL_MASK     0x03u

/*
 * Number of bits to shift a value of type comp_hysteresis_t to get the
 * hysteresis to program into ACB b9 or b10.
 */
#define HYSTERESIS_SHIFT    6u

/*
 * Mask of hysteresis bits within ACB b9 or b10.
 */
#define HYSTERESIS_MASK     0xC0u

/*
 * Mask of the comparator enable bit within ACB b9 and b10.
 */
#define COMPARATOR_ENABLE_MASK  0x10u

/*
 * Comparator ID to Signal Conditioning Block (SCB) lookup table.
 * USe to find which SCB a comparator belongs to.
 */
const uint8_t comp_id_2_scb_lut[NB_OF_COMPARATORS] =
{
    0u,  /* CMP0 */
    0u,  /* CMP1 */
    1u,  /* CMP2 */
    1u,  /* CMP3 */
    2u,  /* CMP4 */
    2u,  /* CMP5 */
    3u,  /* CMP6 */
    3u,  /* CMP7 */
    4u,  /* CMP8 */
    4u,  /* CMP9 */
    5u,  /* CMP10 */
    5u   /* CMP11 */
};

/*-------------------------------------------------------------------------*//**
 * This function is requred to configure comparators included in temperature
 * monitor blocks.
 */
void ACE_set_comp_reference
(
    comparator_id_t     comp_id,
    comp_reference_t    reference
)
{
    uint8_t scb_id;
    uint32_t odd;

    odd = (uint32_t)comp_id & 0x01uL;

    ASSERT( comp_id < NB_OF_COMPARATORS );
    ASSERT( reference < NB_OF_COMP_REF );
    ASSERT( odd );    /* Only Temperature block comparators have configurable reference input. */

    if ( (comp_id < NB_OF_COMPARATORS) && (reference < NB_OF_COMP_REF) && (odd) )
    {
        uint32_t saved_pc2_ctrl;

        scb_id = comp_id_2_scb_lut[comp_id];

        /* Pause the SSE PC2 while accesses to ACB from APB3 are taking place. */
        saved_pc2_ctrl = ACE->PC2_CTRL;
        ACE->PC2_CTRL = 0u;

        if ( ADC_IN_COMP_REF == reference )
        {
            ACE->ACB_DATA[scb_id].b10 &= (uint8_t)~B10_COMP_VREF_SW_MASK;
            ACE->ACB_DATA[scb_id].b11 &= (uint8_t)~B11_DAC_MUXSEL_MASK;
        }
        else
        {
            ACE->ACB_DATA[scb_id].b10 &= (uint8_t)~B10_COMP_VREF_SW_MASK;
            ACE->ACB_DATA[scb_id].b11 = (ACE->ACB_DATA[scb_id].b11 & (uint8_t)~B11_DAC_MUXSEL_MASK) + (uint8_t)reference;
        }

        /* Restore SSE PC2 operations since no ACB accesses should take place
         * beyond this point. */
        ACE->PC2_CTRL = saved_pc2_ctrl;
    }
}

/*-------------------------------------------------------------------------*//**
 * Set analog block comparators hysteresis.
 */
void ACE_set_comp_hysteresis
(
	comparator_id_t     comp_id,
    comp_hysteresis_t   hysteresis
)
{
    uint8_t scb_id;

    ASSERT( comp_id < NB_OF_COMPARATORS );
    ASSERT( hysteresis < NB_OF_HYSTERESIS );

    if ( (comp_id < NB_OF_COMPARATORS) && (hysteresis < NB_OF_HYSTERESIS) )
    {
        uint32_t odd;
        uint32_t saved_pc2_ctrl;

        scb_id = comp_id_2_scb_lut[comp_id];
        odd = (uint32_t)comp_id & 0x01uL;

        /* Pause the SSE PC2 while accesses to ACB from APB3 are taking place. */
        saved_pc2_ctrl = ACE->PC2_CTRL;
        ACE->PC2_CTRL = 0u;

        if ( odd )
        {
            /* Temperature monitor block comparator. */
            ACE->ACB_DATA[scb_id].b10 = (ACE->ACB_DATA[scb_id].b10 & HYSTERESIS_MASK) | (uint8_t)((uint8_t)hysteresis << HYSTERESIS_SHIFT);
        }
        else
        {
            /* Current monitor block comparator. */
            ACE->ACB_DATA[scb_id].b9 = (ACE->ACB_DATA[scb_id].b9 & HYSTERESIS_MASK) | (uint8_t)((uint8_t)hysteresis << HYSTERESIS_SHIFT);
        }

        /* Restore SSE PC2 operations since no ACB accesses should take place
         * beyond this point. */
        ACE->PC2_CTRL = saved_pc2_ctrl;
    }
}

/*-------------------------------------------------------------------------*//**

 */
void ACE_enable_comp
(
	comparator_id_t comp_id
)
{
    uint8_t scb_id;

    ASSERT( comp_id < NB_OF_COMPARATORS );

    if ( comp_id < NB_OF_COMPARATORS )
    {
        uint32_t odd;
        uint32_t saved_pc2_ctrl;

        scb_id = comp_id_2_scb_lut[comp_id];
        odd = (uint32_t)comp_id & 0x01uL;

        /* Pause the SSE PC2 while accesses to ACB from APB3 are taking place. */
        saved_pc2_ctrl = ACE->PC2_CTRL;
        ACE->PC2_CTRL = 0u;

        if ( odd )
        {
            /* Temperature monitor block comparator. */
            ACE->ACB_DATA[scb_id].b10 |= COMPARATOR_ENABLE_MASK;
        }
        else
        {
            /* Current monitor block comparator. */
            ACE->ACB_DATA[scb_id].b9 |= COMPARATOR_ENABLE_MASK;
        }

        /* Restore SSE PC2 operations since no ACB accesses should take place
         * beyond this point. */
        ACE->PC2_CTRL = saved_pc2_ctrl;
    }
}

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_disable_comp
(
	comparator_id_t comp_id
)
{
    uint8_t scb_id;

    ASSERT( comp_id < NB_OF_COMPARATORS );

    if ( comp_id < NB_OF_COMPARATORS )
    {
        uint32_t odd;
        uint32_t saved_pc2_ctrl;

        scb_id = comp_id_2_scb_lut[comp_id];
        odd = (uint32_t)comp_id & 0x01uL;

        /* Pause the SSE PC2 while accesses to ACB from APB3 are taking place. */
        saved_pc2_ctrl = ACE->PC2_CTRL;
        ACE->PC2_CTRL = 0u;

        if ( odd )
        {
            /* Temperature monitor block comparator. */
            ACE->ACB_DATA[scb_id].b10 &= (uint8_t)~COMPARATOR_ENABLE_MASK;
        }
        else
        {
            /* Current monitor block comparator. */
            ACE->ACB_DATA[scb_id].b9 &= (uint8_t)~COMPARATOR_ENABLE_MASK;
        }

        /* Restore SSE PC2 operations since no ACB accesses should take place
         * beyond this point. */
        ACE->PC2_CTRL = saved_pc2_ctrl;
    }
}

/*
 * Bit mask of comparator 0 rise interrupt bit.
 * Shift this value left by the value of the comparator ID to obtain the bit
 * mask used enable/disable/clear rise interrupts from that comparator.
 */
#define FIRST_RISE_IRQ_MASK     0x00000800uL

/*
 * Bit mask of comparator 0 fall interrupt bit.
 * Shift this value left by the value of the comparator ID to obtain the bit
 * mask used enable/disable/clear fall interrupts from that comparator.
 */
#define FIRST_FALL_IRQ_MASK     0x00000001uL

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
void ACE_enable_comp_rise_irq
(
	comparator_id_t comp_id
)
{
    ASSERT( comp_id < NB_OF_COMPARATORS );

    ACE->COMP_IRQ_EN |= (FIRST_RISE_IRQ_MASK << (uint32_t)comp_id);
}

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
void ACE_disable_comp_rise_irq
(
	comparator_id_t comp_id
)
{
    ASSERT( comp_id < NB_OF_COMPARATORS );

    ACE->COMP_IRQ_EN &= ~(FIRST_RISE_IRQ_MASK << (uint32_t)comp_id);
}

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
void ACE_clear_comp_rise_irq
(
	comparator_id_t comp_id
)
{
    ASSERT( comp_id < NB_OF_COMPARATORS );

    ACE->COMP_IRQ_CLR |= (FIRST_RISE_IRQ_MASK << (uint32_t)comp_id);
}

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
void ACE_enable_comp_fall_irq
(
	comparator_id_t comp_id
)
{
    ASSERT( comp_id < NB_OF_COMPARATORS );

    ACE->COMP_IRQ_EN |= (FIRST_FALL_IRQ_MASK << (uint32_t)comp_id);
}

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
void ACE_disable_comp_fall_irq
(
	comparator_id_t comp_id
)
{
    ASSERT( comp_id < NB_OF_COMPARATORS );

    ACE->COMP_IRQ_EN &= ~(FIRST_FALL_IRQ_MASK << (uint32_t)comp_id);
}

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
void ACE_clear_comp_fall_irq
(
	comparator_id_t comp_id
)
{
    ASSERT( comp_id < NB_OF_COMPARATORS );

    ACE->COMP_IRQ_CLR |= (FIRST_FALL_IRQ_MASK << (uint32_t)comp_id);
}

/*-------------------------------------------------------------------------*//**
 * Returns the raw analog quad comparator status.
 */
uint32_t ACE_get_comp_status( void )
{
    return ACE->COMP_IRQ;
}

/*==============================================================================
 ============ Reading Samples from post processing engine (PPE) ================
 =============================================================================*/
extern ace_channel_desc_t g_ace_channel_desc_table[ACE_NB_OF_INPUT_CHANNELS];

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
uint32_t
ACE_get_channel_count
(
    void
)
{
    return (uint32_t)ACE_NB_OF_INPUT_CHANNELS;
}

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
ace_channel_handle_t
ACE_get_first_channel
(
    void
)
{
    ace_channel_handle_t channel_handle;

    channel_handle = (ace_channel_handle_t)0;

    return channel_handle;
}

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
ace_channel_handle_t
ACE_get_next_channel
(
    ace_channel_handle_t channel_handle
)
{
    ++channel_handle;

    if ( channel_handle >= NB_OF_ACE_CHANNEL_HANDLES )
    {
         channel_handle = (ace_channel_handle_t)0;
    }

    return channel_handle;
}

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
ace_channel_handle_t
ACE_get_channel_handle
(
    const uint8_t * p_sz_channel_name
)
{
    uint16_t channel_idx;
    ace_channel_handle_t channel_handle = INVALID_CHANNEL_HANDLE;

    for ( channel_idx = 0u;  channel_idx < (uint16_t)ACE_NB_OF_INPUT_CHANNELS; ++channel_idx )
    {
        if ( g_ace_channel_desc_table[channel_idx].p_sz_channel_name != 0 )
        {
            int32_t diff;
            diff = strncmp( (const char*)p_sz_channel_name, (const char*)g_ace_channel_desc_table[channel_idx].p_sz_channel_name, MAX_CHANNEL_NAME_LENGTH );
            if ( 0 == diff )
            {
                /* channel name found. */
                channel_handle = (ace_channel_handle_t)channel_idx;
                break;
            }
        }
    }
    return channel_handle;
}

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
ace_channel_handle_t
ACE_get_input_channel_handle
(
    adc_channel_id_t    channel_id
)
{
    uint16_t channel_idx;
    ace_channel_handle_t channel_handle = INVALID_CHANNEL_HANDLE;

    for ( channel_idx = 0u;  channel_idx < (uint16_t)ACE_NB_OF_INPUT_CHANNELS; ++channel_idx )
    {
        if ( g_ace_channel_desc_table[channel_idx].signal_id == channel_id )
        {
            /* channel ID found. */
            channel_handle = (ace_channel_handle_t)channel_idx;
            break;
        }
    }
    return channel_handle;
}

/*-------------------------------------------------------------------------*//**
  See "mss_ace.h" for details of how to use this function.
 */
uint16_t
ACE_get_ppe_sample
(
    ace_channel_handle_t channel_handle
)
{
    uint16_t sample;
    uint16_t ppe_offset;

    ppe_offset = g_ace_channel_desc_table[channel_handle].signal_ppe_offset;
    sample = (uint16_t)(ACE->PPE_RAM_DATA[ppe_offset] >> 16u);

    return sample;
}

#ifdef __cplusplus
}
#endif
