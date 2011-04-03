/*******************************************************************************
 * (c) Copyright 2009 Actel Corporation.  All rights reserved.
 * 
 * SVN $Revision: 2840 $
 * SVN $Date: 2010-07-20 17:00:32 +0100 (Tue, 20 Jul 2010) $
 */
#include "mss_ace.h"
#include "mss_ace_configurator.h"
#include "../../CMSIS/a2fxxxm3.h"
#include "../../CMSIS/mss_assert.h"
#include "../../drivers_config/mss_ace/ace_handles.h"
#include "../../drivers_config/mss_ace/ace_config.h"
#include <string.h>

#ifdef __cplusplus
extern "C" {
#endif 

#define MAX_FULL_FLAG_NAME_LENGTH   (MAX_CHANNEL_NAME_LENGTH + MAX_FLAG_NAME_LENGTH + 1)

/*-------------------------------------------------------------------------*//**
 * Number of flag types supported.
 * the supported flag types are:
 *  - BASIC_THRESHOLD_OVER
 *  - BASIC_THRESHOLD_UNDER
 *  - STATE_FILTERED_OVER
 *  - STATE_FILTERED_UNDER
 *  - DUAL_HYSTERESIS_OVER
 *  - DUAL_HYSTERESIS_UNDER
 *  - IPMI_HYSTERESIS_OVER
 *  - IPMI_HYSTERESIS_UNDER
 */
#define NB_OF_FLAG_TYPES    8

/*-------------------------------------------------------------------------*//**
 *
 */
#define THRESHOLD_FLAG0     0u
#define THRESHOLD_FLAG1     1u
#define THRESHOLD_FLAG2     2u
#define THRESHOLD_FLAG3     3u
#define THRESHOLD_FLAG4     4u
#define THRESHOLD_FLAG5     5u
#define THRESHOLD_FLAG6     6u
#define THRESHOLD_FLAG7     7u
#define THRESHOLD_FLAG8     8u
#define THRESHOLD_FLAG9     9u
#define THRESHOLD_FLAG10    10u
#define THRESHOLD_FLAG11    11u
#define THRESHOLD_FLAG12    12u
#define THRESHOLD_FLAG13    13u
#define THRESHOLD_FLAG14    14u
#define THRESHOLD_FLAG15    15u
#define THRESHOLD_FLAG16    16u
#define THRESHOLD_FLAG17    17u
#define THRESHOLD_FLAG18    18u
#define THRESHOLD_FLAG19    19u
#define THRESHOLD_FLAG20    20u
#define THRESHOLD_FLAG21    21u
#define THRESHOLD_FLAG22    22u
#define THRESHOLD_FLAG23    23u
#define THRESHOLD_FLAG24    24u
#define THRESHOLD_FLAG25    25u
#define THRESHOLD_FLAG26    26u
#define THRESHOLD_FLAG27    27u
#define THRESHOLD_FLAG28    28u
#define THRESHOLD_FLAG29    29u
#define THRESHOLD_FLAG30    30u
#define THRESHOLD_FLAG31    31u
#define NB_OF_THRESHOLD_IRQ 32u

/*-------------------------------------------------------------------------*//**
 *
 */
void ace_init_flags( void );

/*-------------------------------------------------------------------------*//**
 * Flag interrupots routines function prototypes
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag0_IRQHandler( void );
#else
void ACE_PPE_Flag0_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag1_IRQHandler( void );
#else
void ACE_PPE_Flag1_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag2_IRQHandler( void );
#else
void ACE_PPE_Flag2_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag3_IRQHandler( void );
#else
void ACE_PPE_Flag3_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag4_IRQHandler( void );
#else
void ACE_PPE_Flag4_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag5_IRQHandler( void );
#else
void ACE_PPE_Flag5_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag6_IRQHandler( void );
#else
void ACE_PPE_Flag6_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag7_IRQHandler( void );
#else
void ACE_PPE_Flag7_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag8_IRQHandler( void );
#else
void ACE_PPE_Flag8_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag9_IRQHandler( void );
#else
void ACE_PPE_Flag9_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag10_IRQHandler( void );
#else
void ACE_PPE_Flag10_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag11_IRQHandler( void );
#else
void ACE_PPE_Flag11_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag12_IRQHandler( void );
#else
void ACE_PPE_Flag12_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag13_IRQHandler( void );
#else
void ACE_PPE_Flag13_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag14_IRQHandler( void );
#else
void ACE_PPE_Flag14_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag15_IRQHandler( void );
#else
void ACE_PPE_Flag15_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag16_IRQHandler( void );
#else
void ACE_PPE_Flag16_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag17_IRQHandler( void );
#else
void ACE_PPE_Flag17_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag18_IRQHandler( void );
#else
void ACE_PPE_Flag18_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag19_IRQHandler( void );
#else
void ACE_PPE_Flag19_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag20_IRQHandler( void );
#else
void ACE_PPE_Flag20_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag21_IRQHandler( void );
#else
void ACE_PPE_Flag21_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag22_IRQHandler( void );
#else
void ACE_PPE_Flag22_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag23_IRQHandler( void );
#else
void ACE_PPE_Flag23_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag24_IRQHandler( void );
#else
void ACE_PPE_Flag24_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag25_IRQHandler( void );
#else
void ACE_PPE_Flag25_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag26_IRQHandler( void );
#else
void ACE_PPE_Flag26_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag27_IRQHandler( void );
#else
void ACE_PPE_Flag27_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag28_IRQHandler( void );
#else
void ACE_PPE_Flag28_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag29_IRQHandler( void );
#else
void ACE_PPE_Flag29_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag30_IRQHandler( void );
#else
void ACE_PPE_Flag30_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag31_IRQHandler( void );
#else
void ACE_PPE_Flag31_IRQHandler( void );
#endif

/*-------------------------------------------------------------------------*//**
 *
 */
#if (ACE_NB_OF_PPE_FLAGS > 0)
extern ppe_flag_desc_t g_ppe_flags_desc_table[ACE_NB_OF_PPE_FLAGS];
#endif

extern ace_channel_desc_t g_ace_channel_desc_table[ACE_NB_OF_INPUT_CHANNELS];

extern ace_adc_config_t g_ace_adc_config[ACE_NB_OF_ADC];

#if (ACE_NB_OF_PPE_FLAGS > 0)
/*-------------------------------------------------------------------------*//**
  Lookup table indexed on flag_id_t of the index of the flag's descriptor index
  in the flag descriptors table g_ppe_flags_desc_table[]
 */
static ace_flag_handle_t g_ppe_flag_handles_lut[NB_OF_PPE_FLAGS];

/*-------------------------------------------------------------------------*//**
 *
 */
static flag_isr_t g_ppe_flags_isr_lut[NB_OF_PPE_FLAGS];

/*-------------------------------------------------------------------------*//**
 *
 */
static global_flag_isr_t g_ppe_global_flags_isr;

/*-------------------------------------------------------------------------*//**
 *
 */
static channel_flag_isr_t g_ppe_channel_flags_isr_lut[ACE_NB_OF_INPUT_CHANNELS];
#endif

/*-------------------------------------------------------------------------*//**
  Intialise the ACE driver's internal data structures used by flag control
  functions.
 */
void ace_init_flags( void )
{
    /* Ensure the generated ACE configuration files are consistent. */
    ASSERT(NB_OF_ACE_FLAG_HANDLES == ACE_NB_OF_PPE_FLAGS);
    
#if (ACE_NB_OF_PPE_FLAGS > 0)    
    {
        uint8_t flag_idx;
        uint8_t channel_idx;
        
        for ( flag_idx = 0u; flag_idx < (uint8_t)NB_OF_PPE_FLAGS; ++flag_idx )
        {
            g_ppe_flags_isr_lut[flag_idx] = 0;
            g_ppe_flag_handles_lut[flag_idx] = INVALID_FLAG_HANDLE;
        }
    
        for ( flag_idx = 0u; flag_idx < (uint8_t)ACE_NB_OF_PPE_FLAGS; ++flag_idx )
        {
            ASSERT( g_ppe_flags_desc_table[flag_idx].flag_id < NB_OF_PPE_FLAGS );
            g_ppe_flag_handles_lut[g_ppe_flags_desc_table[flag_idx].flag_id] = (ace_flag_handle_t)flag_idx;
        }
        
        for ( channel_idx = 0u; channel_idx < (uint8_t)ACE_NB_OF_INPUT_CHANNELS; ++channel_idx )
        {
            g_ppe_channel_flags_isr_lut[channel_idx] = 0;
        }
        
        g_ppe_global_flags_isr = 0u;
    }
#endif
}

/*-------------------------------------------------------------------------*//**
 *
 */
uint32_t ACE_is_hysteresis_flag( ace_flag_handle_t   flag_handle )
{
    uint32_t hysteresis = 0u;
    
#if (ACE_NB_OF_PPE_FLAGS > 0)
    ASSERT( flag_handle < NB_OF_ACE_FLAG_HANDLES );
    
    if ( g_ppe_flags_desc_table[flag_handle].flag_type >= DUAL_HYSTERESIS_OVER )
    {
        hysteresis = 1u;
    }
#endif
    return hysteresis;
}

/*-------------------------------------------------------------------------*//**
 *
 */
uint32_t ACE_is_under_flag
(
    ace_flag_handle_t   flag_handle
)
{
    uint32_t is_under = 0;
    
#if (ACE_NB_OF_PPE_FLAGS > 0)
    const uint32_t flag_type_lut[NB_OF_FLAG_TYPES] =
    {
        0,  /* BASIC_THRESHOLD_OVER */
        1,  /* BASIC_THRESHOLD_UNDER */
        0,  /* STATE_FILTERED_OVER */
        1,  /* STATE_FILTERED_UNDER */
        0,  /* DUAL_HYSTERESIS_OVER */
        1,  /* DUAL_HYSTERESIS_UNDER */
        0,  /* IPMI_HYSTERESIS_OVER */
        1,  /* IPMI_HYSTERESIS_UNDER */
    };
    
    ASSERT(flag_handle < ACE_NB_OF_PPE_FLAGS);
    if (flag_handle < ACE_NB_OF_PPE_FLAGS)
    {
        uint8_t flag_type;
        flag_type = g_ppe_flags_desc_table[flag_handle].flag_type;
        ASSERT(flag_type < NB_OF_FLAG_TYPES);
        if (flag_type < NB_OF_FLAG_TYPES)
        {
            is_under = flag_type_lut[flag_type];
        }
    }
#endif
    return is_under;
}

/*-------------------------------------------------------------------------*//**
  Mask of the threshold value bits within a PPE RAM meory location holding the
  threshold value for a flag.
 */
#define PPE_RAM_THRESHOLD_MASK      0x0000FFFFuL

/*-------------------------------------------------------------------------*//**
 * TODO: handle IPMI hysteresis flags
 */
void ACE_set_flag_threshold
(
    ace_flag_handle_t   flag_handle,
    uint16_t            new_threshold
)
{
#if (ACE_NB_OF_PPE_FLAGS > 0)
    uint16_t ppe_offset;
    
    ASSERT( flag_handle < NB_OF_ACE_FLAG_HANDLES );
    
    if ( flag_handle < NB_OF_ACE_FLAG_HANDLES )
    {
    
        ppe_offset = g_ppe_flags_desc_table[flag_handle].threshold_ppe_offset;
        
        if ( ACE_is_hysteresis_flag( flag_handle ) == 0u )
        {
            ACE->PPE_RAM_DATA[ppe_offset] = (ACE->PPE_RAM_DATA[ppe_offset] & (uint32_t)~PPE_RAM_THRESHOLD_MASK) + new_threshold;
        }
        else
        {
            uint16_t high_threshold;
            uint16_t low_threshold;
            ace_channel_handle_t channel_handle;
            uint16_t hysteresis;
            uint32_t adc_id;
            uint16_t adc_resolution;
            
            high_threshold = (uint16_t)(ACE->PPE_RAM_DATA[ppe_offset] & PPE_RAM_THRESHOLD_MASK);
            low_threshold = (uint16_t)(ACE->PPE_RAM_DATA[ppe_offset + 1u] & PPE_RAM_THRESHOLD_MASK);
            ASSERT(high_threshold > low_threshold);
            hysteresis = (uint16_t)(high_threshold - low_threshold) / 2u;
            
            channel_handle = g_ppe_flags_desc_table[flag_handle].channel_handle;
            adc_id = (uint32_t)(g_ace_channel_desc_table[channel_handle].signal_id) >> 4u;
            ASSERT( adc_id < (uint32_t)ACE_NB_OF_ADC );
            
            if ( adc_id < (uint32_t)ACE_NB_OF_ADC )
            {
                adc_resolution = g_ace_adc_config[adc_id].adc_resolution - 1u;
                
                high_threshold = new_threshold + hysteresis;
                if ( high_threshold > adc_resolution )
                {
                    high_threshold = adc_resolution;
                }
                
                if ( hysteresis > new_threshold )
                {
                    low_threshold = 1u;
                }
                else
                {
                    low_threshold = new_threshold - hysteresis;
                }
                
                ACE->PPE_RAM_DATA[ppe_offset] = (ACE->PPE_RAM_DATA[ppe_offset] & ~PPE_RAM_THRESHOLD_MASK) + high_threshold;
                ACE->PPE_RAM_DATA[ppe_offset + 1u] = (ACE->PPE_RAM_DATA[ppe_offset + 1u] & (uint32_t)~PPE_RAM_THRESHOLD_MASK) + low_threshold;
            }
        }
    }
#endif
}


/*-------------------------------------------------------------------------*//**
 *
 */
#define FLAG_OVER_UNDER_MASK    0x01u
#define FLAG_OVER               0x00u
#define FLAF_UNDER              0x01

void ACE_set_flag_assertion
(
    ace_flag_handle_t   flag_handle,
    uint16_t            assertion_value
)
{
#if (ACE_NB_OF_PPE_FLAGS > 0)
    uint16_t ppe_offset;
    
    ASSERT( flag_handle < NB_OF_ACE_FLAG_HANDLES );
    
    if ( flag_handle < NB_OF_ACE_FLAG_HANDLES )
    {
        if (ACE_is_hysteresis_flag(flag_handle))
        {
            uint8_t flag_direction;
            flag_direction = g_ppe_flags_desc_table[flag_handle].flag_type & FLAG_OVER_UNDER_MASK;
            
            if ( FLAG_OVER == flag_direction )
            {
                ppe_offset = g_ppe_flags_desc_table[flag_handle].threshold_ppe_offset;
            }
            else
            {
                ppe_offset = g_ppe_flags_desc_table[flag_handle].threshold_ppe_offset + 1u;
            }
        }
        else
        {
            ppe_offset = g_ppe_flags_desc_table[flag_handle].threshold_ppe_offset;
        }
        ACE->PPE_RAM_DATA[ppe_offset] = (ACE->PPE_RAM_DATA[ppe_offset] & ~PPE_RAM_THRESHOLD_MASK) + assertion_value;
    }
#endif
}

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_set_flag_deassertion
(
    ace_flag_handle_t   flag_handle,
    uint16_t            assertion_value
)
{
#if (ACE_NB_OF_PPE_FLAGS > 0)
    uint16_t ppe_offset;
    
    ASSERT( flag_handle < NB_OF_ACE_FLAG_HANDLES );
    ASSERT(ACE_is_hysteresis_flag(flag_handle));
    
    if ((flag_handle < NB_OF_ACE_FLAG_HANDLES)  && (ACE_is_hysteresis_flag(flag_handle)))
    {
        uint8_t flag_direction;
        flag_direction = g_ppe_flags_desc_table[flag_handle].flag_type & FLAG_OVER_UNDER_MASK;
        
        if ( FLAG_OVER == flag_direction )
        {
            ppe_offset = g_ppe_flags_desc_table[flag_handle].threshold_ppe_offset + 1u;
        }
        else
        {
            ppe_offset = g_ppe_flags_desc_table[flag_handle].threshold_ppe_offset;
        }
        
        ACE->PPE_RAM_DATA[ppe_offset] = (ACE->PPE_RAM_DATA[ppe_offset] & ~PPE_RAM_THRESHOLD_MASK) + assertion_value;
    }
#endif
}

/*-------------------------------------------------------------------------*//**
 *
 */
void
ACE_set_flag_hysteresis
(
    ace_flag_handle_t   flag_handle,
    uint16_t            adc_hysteresis
)
{
#if (ACE_NB_OF_PPE_FLAGS > 0)
    uint16_t ppe_offset;
    uint32_t high_threshold;
    uint32_t low_threshold;
    uint32_t nominal_threshold;
    uint16_t adc_resolution;
    uint32_t adc_id;
    
    ASSERT( flag_handle < NB_OF_ACE_FLAG_HANDLES );
    ASSERT(ACE_is_hysteresis_flag(flag_handle));
    
    if ( ( flag_handle < NB_OF_ACE_FLAG_HANDLES ) && ( ACE_is_hysteresis_flag( flag_handle ) ) )
    {
        ace_channel_handle_t channel_handle;
        
        ppe_offset = g_ppe_flags_desc_table[flag_handle].threshold_ppe_offset;
        
        high_threshold = ACE->PPE_RAM_DATA[ppe_offset] & PPE_RAM_THRESHOLD_MASK;
        low_threshold = ACE->PPE_RAM_DATA[ppe_offset + 1u] & PPE_RAM_THRESHOLD_MASK;
        ASSERT(high_threshold > low_threshold);
        nominal_threshold = (low_threshold + ((high_threshold - low_threshold) / 2u));
        
        channel_handle = g_ppe_flags_desc_table[flag_handle].channel_handle;
        adc_id = (uint32_t)((uint32_t)g_ace_channel_desc_table[channel_handle].signal_id >> 4u);
        ASSERT( adc_id < (uint32_t)ACE_NB_OF_ADC );
        
        if ( adc_id < (uint32_t)ACE_NB_OF_ADC )
        {
            adc_resolution = g_ace_adc_config[adc_id].adc_resolution;
            
            high_threshold = nominal_threshold + adc_hysteresis;
            if ( high_threshold > adc_resolution )
            {
                high_threshold = (uint32_t)adc_resolution - 1u;
            }
            
            if ( adc_hysteresis > nominal_threshold )
            {
                low_threshold = 1u;
            }
            else
            {
                low_threshold = nominal_threshold - adc_hysteresis;
            }
            
            ACE->PPE_RAM_DATA[ppe_offset] = (ACE->PPE_RAM_DATA[ppe_offset] & ~PPE_RAM_THRESHOLD_MASK) + high_threshold;
            ACE->PPE_RAM_DATA[ppe_offset + 1u] = (ACE->PPE_RAM_DATA[ppe_offset + 1u] & ~PPE_RAM_THRESHOLD_MASK) + low_threshold;
        }
    }
#endif
}


/*-------------------------------------------------------------------------*//**
 *
 */
void
ACE_set_channel_hysteresis
(
    ace_channel_handle_t    channel_handle,
    uint16_t                adc_hysteresis
)
{
#if (ACE_NB_OF_PPE_FLAGS > 0)
    ace_flag_handle_t flag_handle;
    
    ASSERT( channel_handle < NB_OF_ACE_CHANNEL_HANDLES );
    
    if ( channel_handle < NB_OF_ACE_CHANNEL_HANDLES )
    {
        uint16_t i;
        
        for( i = 0u; i < g_ace_channel_desc_table[channel_handle].nb_of_flags; ++i )
        {
            flag_handle = (ace_flag_handle_t)g_ace_channel_desc_table[channel_handle].p_flags_array[i];
            ACE_set_flag_hysteresis( flag_handle, adc_hysteresis );
        }
    }
#endif
}

/*==============================================================================
 *
 */

/*-------------------------------------------------------------------------*//**
  Masking a flag_id with FLAG_BIT_OFFSET_MASK results in the offset of the 
  flag bit within a PPE__FLAGSn register.
 */
#define FLAG_BIT_OFFSET_MASK       0x0000001FuL

/*-------------------------------------------------------------------------*//**
  Shifting right a flag_id by FLAG_PPE_REG_SHIFT results in identifying the
  PPE_FLAGSn or PPE_SFFLAGS the flags belongs to.
 */
#define FLAG_PPE_REG_SHIFT          5u

/*-------------------------------------------------------------------------*//**
  There is a set of 5 PPE flag registers to control and report status of the PPE
  flags resulting in the PPE flags being grouped into 5 separate flag groups at
  the register level. Each register provides status or control for 32 flags.
 */
#define NB_OF_FLAG_GROUPS       5u
#define NB_OF_FLAGS_PER_GROUP   32u

#if (ACE_NB_OF_PPE_FLAGS > 0)
/*-------------------------------------------------------------------------*//**
  Lookup table of the address PPE_FLAGSn registers for fast reading of PPE
  status.
 */
static volatile uint32_t * const g_ppe_flags_regs_lut[NB_OF_FLAG_GROUPS] =
{
    &ACE->PPE_FLAGS0,
    &ACE->PPE_FLAGS1,
    &ACE->PPE_FLAGS2,
    &ACE->PPE_FLAGS3,
    &ACE->PPE_SFFLAGS
};

/*-------------------------------------------------------------------------*//**
  Lookup table of the address of the PPE flags interrupt enable registers.
 */
static uint32_t volatile * const flags_irq_enable_regs_lut[NB_OF_FLAG_GROUPS] =
{
    &ACE->PPE_FLAGS0_IRQ_EN,
    &ACE->PPE_FLAGS1_IRQ_EN,
    &ACE->PPE_FLAGS2_IRQ_EN,
    &ACE->PPE_FLAGS3_IRQ_EN,
    &ACE->PPE_SFFLAGS_IRQ_EN
};

/*-------------------------------------------------------------------------*//**
  Lookup table of the address of the PPE flags interrupt status registers.
 */
static uint32_t volatile const * const flags_irq_status_regs_lut[NB_OF_FLAG_GROUPS] =
{
    &ACE->PPE_FLAGS0_IRQ,
    &ACE->PPE_FLAGS1_IRQ,
    &ACE->PPE_FLAGS2_IRQ,
    &ACE->PPE_FLAGS3_IRQ,
    &ACE->PPE_SFFLAGS_IRQ
};

/*-------------------------------------------------------------------------*//**
  Lookup table of the address of the PPE flags interrupt clearing registers.
 */
static uint32_t volatile * const flags_irq_clear_regs_lut[NB_OF_FLAG_GROUPS] =
{
    &ACE->PPE_FLAGS0_IRQ_CLR,
    &ACE->PPE_FLAGS1_IRQ_CLR,
    &ACE->PPE_FLAGS2_IRQ_CLR,
    &ACE->PPE_FLAGS3_IRQ_CLR,
    &ACE->PPE_SFFLAGS_IRQ_CLR
};

/*-------------------------------------------------------------------------*//**
 *
 */
static const IRQn_Type threshold_irqn_lut[NB_OF_THRESHOLD_IRQ] =
{
    ACE_PPE_Flag0_IRQn,
    ACE_PPE_Flag1_IRQn,
    ACE_PPE_Flag2_IRQn,
    ACE_PPE_Flag3_IRQn,
    ACE_PPE_Flag4_IRQn,
    ACE_PPE_Flag5_IRQn,
    ACE_PPE_Flag6_IRQn,
    ACE_PPE_Flag7_IRQn,
    ACE_PPE_Flag8_IRQn,
    ACE_PPE_Flag9_IRQn,
    ACE_PPE_Flag10_IRQn,
    ACE_PPE_Flag11_IRQn,
    ACE_PPE_Flag12_IRQn,
    ACE_PPE_Flag13_IRQn,
    ACE_PPE_Flag14_IRQn,
    ACE_PPE_Flag15_IRQn,
    ACE_PPE_Flag16_IRQn,
    ACE_PPE_Flag17_IRQn,
    ACE_PPE_Flag18_IRQn,
    ACE_PPE_Flag19_IRQn,
    ACE_PPE_Flag20_IRQn,
    ACE_PPE_Flag21_IRQn,
    ACE_PPE_Flag22_IRQn,
    ACE_PPE_Flag23_IRQn,
    ACE_PPE_Flag24_IRQn,
    ACE_PPE_Flag25_IRQn,
    ACE_PPE_Flag26_IRQn,
    ACE_PPE_Flag27_IRQn,
    ACE_PPE_Flag28_IRQn,
    ACE_PPE_Flag29_IRQn,
    ACE_PPE_Flag30_IRQn,
    ACE_PPE_Flag31_IRQn
};
#endif

/*-------------------------------------------------------------------------*//**
 */
ace_flag_handle_t
ACE_get_flag_handle
(
    const uint8_t * p_sz_full_flag_name
)
{
    ace_flag_handle_t flag_handle = INVALID_FLAG_HANDLE;
#if (ACE_NB_OF_PPE_FLAGS > 0)
    ace_flag_handle_t flag_idx;
    
    for ( flag_idx = (ace_flag_handle_t)0; flag_idx < NB_OF_ACE_FLAG_HANDLES; ++flag_idx )
    {
        if ( g_ppe_flags_desc_table[flag_idx].p_sz_flag_name != 0 )
        {
            int32_t diff;
            diff = strncmp( (const char *)p_sz_full_flag_name, (const char *)g_ppe_flags_desc_table[flag_idx].p_sz_flag_name, (size_t)MAX_FULL_FLAG_NAME_LENGTH );
            if ( 0 == diff )
            {
                /* flag name found. */
                flag_handle = (ace_flag_handle_t)flag_idx;
                break;
            }
        }
    }
#endif
    return flag_handle;
}

/*-------------------------------------------------------------------------*//**
 */
int32_t
ACE_get_flag_status
(
    ace_flag_handle_t   flag_handle
)
{
    int32_t flag_state = UNKNOWN_FLAG;
#if (ACE_NB_OF_PPE_FLAGS > 0)    
    ppe_flag_id_t flag_id;
    
    ASSERT( flag_handle < NB_OF_ACE_FLAG_HANDLES );
    
    if ( flag_handle < NB_OF_ACE_FLAG_HANDLES )
    {
        uint32_t flag_bit_offset;
        uint32_t ppe_flag_group;
        uint32_t flag_id_mask;
        uint32_t flag_status;

        flag_id = g_ppe_flags_desc_table[flag_handle].flag_id;
        
        if ( flag_id < NB_OF_PPE_FLAGS )
        {
            flag_bit_offset = ((uint32_t)flag_id & FLAG_BIT_OFFSET_MASK);
            ppe_flag_group = ((uint32_t)flag_id >> FLAG_PPE_REG_SHIFT);
            flag_id_mask = 1uL << flag_bit_offset;
            flag_status = *(g_ppe_flags_regs_lut[ppe_flag_group]) & flag_id_mask;
            if ( flag_status > 0u )
            {
                flag_state = FLAG_ASSERTED;
            }
            else
            {
                flag_state = FLAG_NOT_ASSERTED;
            }
        }

    }
#endif
    return flag_state;
}


/*-------------------------------------------------------------------------*//**
 */
const uint8_t *
ACE_get_flag_name
(
    ace_flag_handle_t flag_handle
)
{
    const uint8_t * psz_flag_name = 0;
#if (ACE_NB_OF_PPE_FLAGS > 0)    
    ASSERT( flag_handle < NB_OF_ACE_FLAG_HANDLES );
    
    if ( flag_handle < NB_OF_ACE_FLAG_HANDLES )
    {
        psz_flag_name = g_ppe_flags_desc_table[flag_handle].p_sz_flag_name;
    }
#endif
    return psz_flag_name;
}

/*-------------------------------------------------------------------------*//**
 */
ace_channel_handle_t
ACE_get_flag_channel
(
    ace_flag_handle_t flag_handle
)
{
    ace_channel_handle_t channel_handle = INVALID_CHANNEL_HANDLE;
#if (ACE_NB_OF_PPE_FLAGS > 0)
    ASSERT( flag_handle < NB_OF_ACE_FLAG_HANDLES );
    
    if ( flag_handle < NB_OF_ACE_FLAG_HANDLES )
    {
        channel_handle = g_ppe_flags_desc_table[flag_handle].channel_handle;
    }
#endif
    return channel_handle;
}

/*-------------------------------------------------------------------------*//**
 */
uint32_t
ACE_get_channel_flag_count
(
    ace_channel_handle_t    channel_handle
)
{
    uint32_t flag_count = 0;
#if (ACE_NB_OF_PPE_FLAGS > 0)
    ASSERT( channel_handle < ACE_NB_OF_INPUT_CHANNELS );
    if (channel_handle < ACE_NB_OF_INPUT_CHANNELS)
    {
        flag_count = g_ace_channel_desc_table[channel_handle].nb_of_flags;
    }
#endif
    return flag_count;
}

/*-------------------------------------------------------------------------*//**
  
 */
ace_flag_handle_t
ACE_get_channel_first_flag
(
    ace_channel_handle_t    channel_handle,
    uint16_t *              iterator
)
{
    ace_flag_handle_t flag_handle = INVALID_FLAG_HANDLE;
#if (ACE_NB_OF_PPE_FLAGS > 0)
    ASSERT( channel_handle < NB_OF_ACE_CHANNEL_HANDLES);
    
    *iterator = 0u;
    
    if ( channel_handle < NB_OF_ACE_CHANNEL_HANDLES)
    {
        if ( g_ace_channel_desc_table[channel_handle].nb_of_flags > 0u )
        {
            flag_handle = (ace_flag_handle_t)g_ace_channel_desc_table[channel_handle].p_flags_array[*iterator];
        }
    }
#endif    
    return flag_handle;
}

/*-------------------------------------------------------------------------*//**
  
 */
ace_flag_handle_t
ACE_get_channel_next_flag
(
    ace_channel_handle_t    channel_handle,
    uint16_t *              iterator
)
{
    ace_flag_handle_t flag_handle = INVALID_FLAG_HANDLE;
#if (ACE_NB_OF_PPE_FLAGS > 0)    
    ASSERT( channel_handle < NB_OF_ACE_CHANNEL_HANDLES);

    if ( channel_handle < NB_OF_ACE_CHANNEL_HANDLES)
    {
        ++(*iterator);
        
        if ( *iterator >= g_ace_channel_desc_table[channel_handle].nb_of_flags )
        {
            *iterator = 0u;
        }
    
        if ( g_ace_channel_desc_table[channel_handle].nb_of_flags > 0u )
        {
            flag_handle = (ace_flag_handle_t)g_ace_channel_desc_table[channel_handle].p_flags_array[*iterator];
        }
    }
#endif
    return flag_handle;
}


/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_enable_channel_flags_irq
(
    ace_channel_handle_t channel_handle
)
{
#if (ACE_NB_OF_PPE_FLAGS > 0)
    uint32_t flag_idx;
    ace_flag_handle_t flag_handle;
    
    ASSERT( channel_handle < NB_OF_ACE_CHANNEL_HANDLES );
    
    if ( channel_handle < NB_OF_ACE_CHANNEL_HANDLES )
    {
        for ( flag_idx = 0u; flag_idx < g_ace_channel_desc_table[channel_handle].nb_of_flags; ++flag_idx )
        {
            flag_handle = (ace_flag_handle_t)g_ace_channel_desc_table[channel_handle].p_flags_array[flag_idx];
            ACE_enable_flag_irq( flag_handle );
        }
    }
#endif
}

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_disable_channel_flags_irq
(
    ace_channel_handle_t channel_handle
)
{
#if (ACE_NB_OF_PPE_FLAGS > 0)
    uint32_t flag_idx;
    ace_flag_handle_t flag_handle;
    
    ASSERT( channel_handle < NB_OF_ACE_CHANNEL_HANDLES );
    
    if ( channel_handle < NB_OF_ACE_CHANNEL_HANDLES )
    {
        for ( flag_idx = 0u; flag_idx < g_ace_channel_desc_table[channel_handle].nb_of_flags; ++flag_idx )
        {
            flag_handle = (ace_flag_handle_t)g_ace_channel_desc_table[channel_handle].p_flags_array[flag_idx];
            ACE_disable_flag_irq( flag_handle );
        }
    }
#endif
}

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_clear_channel_flags_irq
(
    ace_channel_handle_t channel_handle
)
{
#if (ACE_NB_OF_PPE_FLAGS > 0)
    uint32_t flag_idx;
    ace_flag_handle_t flag_handle;
    
    ASSERT( channel_handle < NB_OF_ACE_CHANNEL_HANDLES );
    
    if ( channel_handle < NB_OF_ACE_CHANNEL_HANDLES )
    {
        for ( flag_idx = 0u; flag_idx < g_ace_channel_desc_table[channel_handle].nb_of_flags; ++flag_idx )
        {
            flag_handle = (ace_flag_handle_t)g_ace_channel_desc_table[channel_handle].p_flags_array[flag_idx];
            ACE_clear_flag_irq( flag_handle );
        }
    }
#endif
}

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_enable_flag_irq
(
    ace_flag_handle_t flag_handle
)
{
#if (ACE_NB_OF_PPE_FLAGS > 0)
    ASSERT( flag_handle < NB_OF_ACE_FLAG_HANDLES );
    
    if ( flag_handle < NB_OF_ACE_FLAG_HANDLES )
    {
        ppe_flag_id_t flag_id;
        uint32_t flag_bit_offset;
        uint32_t ppe_flag_group;
        uint32_t flag_id_mask;
        
        flag_id = g_ppe_flags_desc_table[flag_handle].flag_id;
        
        ASSERT( flag_id < NB_OF_PPE_FLAGS );
    
        flag_bit_offset = ((uint32_t)flag_id & FLAG_BIT_OFFSET_MASK);
        ppe_flag_group = ((uint32_t)flag_id >> FLAG_PPE_REG_SHIFT);
        flag_id_mask = 1uL << flag_bit_offset;
        
        ASSERT( ppe_flag_group < NB_OF_FLAG_GROUPS );
        
        if ( ppe_flag_group < NB_OF_FLAG_GROUPS )
        {
            *(flags_irq_enable_regs_lut[ppe_flag_group]) |= flag_id_mask;
        }
        
        NVIC_EnableIRQ( threshold_irqn_lut[flag_bit_offset] );
    }
#endif
}

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_disable_flag_irq
(
    ace_flag_handle_t flag_handle
)
{
#if (ACE_NB_OF_PPE_FLAGS > 0)
    ASSERT( flag_handle < NB_OF_ACE_FLAG_HANDLES );
    
    if ( flag_handle < NB_OF_ACE_FLAG_HANDLES )
    {
        ppe_flag_id_t flag_id;
        uint32_t flag_bit_offset;
        uint32_t ppe_flag_group;
        uint32_t flag_id_mask;
        
        flag_id = g_ppe_flags_desc_table[flag_handle].flag_id;
        
        ASSERT( flag_id < NB_OF_PPE_FLAGS );
    
        flag_bit_offset = ((uint32_t)flag_id & FLAG_BIT_OFFSET_MASK);
        ppe_flag_group = ((uint32_t)flag_id >> FLAG_PPE_REG_SHIFT);
        flag_id_mask = 1uL << flag_bit_offset;
        
        ASSERT( ppe_flag_group < NB_OF_FLAG_GROUPS );
        
        if ( ppe_flag_group < NB_OF_FLAG_GROUPS )
        {
            *(flags_irq_enable_regs_lut[ppe_flag_group]) &= (uint32_t)~flag_id_mask;
        }
    }
#endif
}

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_clear_flag_irq
(
    ace_flag_handle_t flag_handle
)
{
#if (ACE_NB_OF_PPE_FLAGS > 0)
    ASSERT( flag_handle < NB_OF_ACE_FLAG_HANDLES );
    
    if ( flag_handle < NB_OF_ACE_FLAG_HANDLES )
    {
        ppe_flag_id_t flag_id;
        uint32_t flag_bit_offset;
        uint32_t ppe_flag_group;
        uint32_t flag_id_mask;
        
        flag_id = g_ppe_flags_desc_table[flag_handle].flag_id;
        
        ASSERT( flag_id < NB_OF_PPE_FLAGS );
    
        flag_bit_offset = ((uint32_t)flag_id & FLAG_BIT_OFFSET_MASK);
        ppe_flag_group = ((uint32_t)flag_id >> FLAG_PPE_REG_SHIFT);
        flag_id_mask = 1uL << flag_bit_offset;
        
        ASSERT( ppe_flag_group < NB_OF_FLAG_GROUPS );
        
        if ( ppe_flag_group < NB_OF_FLAG_GROUPS )
        {
            *(flags_irq_clear_regs_lut[ppe_flag_group]) |= flag_id_mask;
        }
    }
#endif
}

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_register_flag_isr
(
    ace_flag_handle_t   flag_handle,
    flag_isr_t          flag_isr
)
{
#if (ACE_NB_OF_PPE_FLAGS > 0)
    ppe_flag_id_t flag_id;
    
    ASSERT( flag_handle < NB_OF_ACE_FLAG_HANDLES );
    
    if ( flag_handle < NB_OF_ACE_FLAG_HANDLES )
    {
        flag_id = g_ppe_flags_desc_table[flag_handle].flag_id;
        
        ASSERT( flag_id < NB_OF_PPE_FLAGS );
        
        if ( flag_id < NB_OF_PPE_FLAGS )
        {
            g_ppe_flags_isr_lut[flag_id] = flag_isr;
        }
    }
#endif
}

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_register_channel_flags_isr
(
    ace_channel_handle_t    channel_handle,
    channel_flag_isr_t      channel_flag_isr
)
{
#if (ACE_NB_OF_PPE_FLAGS > 0)
    ASSERT( channel_handle < NB_OF_ACE_CHANNEL_HANDLES );
    
    if ( channel_handle < NB_OF_ACE_CHANNEL_HANDLES )
    {
        g_ppe_channel_flags_isr_lut[channel_handle] = channel_flag_isr;
    }
#endif
}

/*-------------------------------------------------------------------------*//**
 *
 */
void ACE_register_global_flags_isr
(
    global_flag_isr_t  global_flag_isr
)
{
#if (ACE_NB_OF_PPE_FLAGS > 0)
    g_ppe_global_flags_isr = global_flag_isr;
#endif
}


/*==============================================================================
 *
 */
 
/*-------------------------------------------------------------------------*//**
 * Actual PPE flag interrupt service routines:
 */

static void process_flag_irq( uint8_t threshold_flag_id )
{
#if (ACE_NB_OF_PPE_FLAGS > 0)
    uint8_t flag_group;
    uint32_t threshold_flag_mask;
    ppe_flag_id_t flag_id;
    uint32_t irq_enable_reg;
    uint32_t irq_status_reg;
    uint32_t irq_active;
    
    threshold_flag_mask = 1uL << threshold_flag_id;
    
    
    for ( flag_group = 0u; flag_group < NB_OF_FLAG_GROUPS; ++flag_group )
    {
        irq_enable_reg = *flags_irq_enable_regs_lut[flag_group];
        irq_status_reg = *flags_irq_status_regs_lut[flag_group];
        irq_active = threshold_flag_mask & irq_enable_reg & irq_status_reg;
        
        if ( irq_active )
        {
            ace_flag_handle_t flag_handle;
            ace_channel_handle_t channel_handle;
            
            flag_id = (ppe_flag_id_t)((flag_group * NB_OF_FLAGS_PER_GROUP) + threshold_flag_id);
            flag_handle = g_ppe_flag_handles_lut[flag_id];
            
            /* Call individual flag handler */
            if ( g_ppe_flags_isr_lut[flag_id] != 0 ) 
            {
                g_ppe_flags_isr_lut[flag_id]( flag_handle );
            }
            
            /* Call the channel flag handler. */
            channel_handle = g_ppe_flags_desc_table[flag_handle].channel_handle;
            if ( channel_handle < NB_OF_ACE_CHANNEL_HANDLES )
            {
                if ( g_ppe_channel_flags_isr_lut[channel_handle] != 0 )
                {
                    g_ppe_channel_flags_isr_lut[channel_handle]( flag_handle );
                }
            }
            
            /* Call the global flag handler. */
            if ( g_ppe_global_flags_isr != 0 )
            {
                g_ppe_global_flags_isr( flag_handle, channel_handle );
            }
            
            /* Clear the flag interrupt */
            *flags_irq_clear_regs_lut[flag_group] |= threshold_flag_mask;
        }
    }
#endif
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag0_IRQHandler( void )
#else
void ACE_PPE_Flag0_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG0 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag0_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag1_IRQHandler( void )
#else
void ACE_PPE_Flag1_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG1 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag1_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag2_IRQHandler( void )
#else
void ACE_PPE_Flag2_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG2 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag2_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag3_IRQHandler( void )
#else
void ACE_PPE_Flag3_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG3 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag3_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag4_IRQHandler( void )
#else
void ACE_PPE_Flag4_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG4 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag4_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag5_IRQHandler( void )
#else
void ACE_PPE_Flag5_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG5 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag5_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag6_IRQHandler( void )
#else
void ACE_PPE_Flag6_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG6 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag6_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag7_IRQHandler( void )
#else
void ACE_PPE_Flag7_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG7 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag7_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag8_IRQHandler( void )
#else
void ACE_PPE_Flag8_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG8 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag8_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag9_IRQHandler( void )
#else
void ACE_PPE_Flag9_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG9 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag9_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag10_IRQHandler( void )
#else
void ACE_PPE_Flag10_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG10 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag10_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag11_IRQHandler( void )
#else
void ACE_PPE_Flag11_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG11 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag11_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag12_IRQHandler( void )
#else
void ACE_PPE_Flag12_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG12 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag12_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag13_IRQHandler( void )
#else
void ACE_PPE_Flag13_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG13 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag13_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag14_IRQHandler( void )
#else
void ACE_PPE_Flag14_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG14 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag14_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag15_IRQHandler( void )
#else
void ACE_PPE_Flag15_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG15 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag15_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag16_IRQHandler( void )
#else
void ACE_PPE_Flag16_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG16 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag16_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag17_IRQHandler( void )
#else
void ACE_PPE_Flag17_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG17 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag17_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag18_IRQHandler( void )
#else
void ACE_PPE_Flag18_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG18 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag18_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag19_IRQHandler( void )
#else
void ACE_PPE_Flag19_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG19 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag19_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag20_IRQHandler( void )
#else
void ACE_PPE_Flag20_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG20 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag20_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag21_IRQHandler( void )
#else
void ACE_PPE_Flag21_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG21 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag21_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag22_IRQHandler( void )
#else
void ACE_PPE_Flag22_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG22 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag22_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag23_IRQHandler( void )
#else
void ACE_PPE_Flag23_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG23 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag23_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag24_IRQHandler( void )
#else
void ACE_PPE_Flag24_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG24 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag24_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag25_IRQHandler( void )
#else
void ACE_PPE_Flag25_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG25 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag25_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag26_IRQHandler( void )
#else
void ACE_PPE_Flag26_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG26 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag26_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag27_IRQHandler( void )
#else
void ACE_PPE_Flag27_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG27 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag27_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag28_IRQHandler( void )
#else
void ACE_PPE_Flag28_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG28 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag28_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag29_IRQHandler( void )
#else
void ACE_PPE_Flag29_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG29 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag29_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag30_IRQHandler( void )
#else
void ACE_PPE_Flag30_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG30 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag30_IRQn );
}

/*-------------------------------------------------------------------------*//**
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void ACE_PPE_Flag31_IRQHandler( void )
#else
void ACE_PPE_Flag31_IRQHandler( void )
#endif
{
    process_flag_irq( THRESHOLD_FLAG31 );
    NVIC_ClearPendingIRQ( ACE_PPE_Flag31_IRQn );
}

#ifdef __cplusplus
}
#endif

