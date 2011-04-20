/*******************************************************************************
 * (c) Copyright 2009 Actel Corporation.  All rights reserved.
 * 
 * SVN $Revision: 2905 $
 * SVN $Date: 2010-08-20 14:03:28 +0100 (Fri, 20 Aug 2010) $
 */
#include "mss_ace.h"
#include "mss_ace_configurator.h"
#include "../../CMSIS/a2fxxxm3.h"
#include "../../CMSIS/mss_assert.h"
#include "../../drivers_config/mss_ace/ace_handles.h"
#include "../../drivers_config/mss_ace/ace_config.h"

#ifdef __cplusplus
extern "C" {
#endif 

/*-------------------------------------------------------------------------*//**
 *
 */
extern ace_channel_desc_t g_ace_channel_desc_table[ACE_NB_OF_INPUT_CHANNELS];
extern ace_adc_config_t g_ace_adc_config[ACE_NB_OF_ADC];
extern const uint32_t g_ace_current_resistors[ACE_NB_OF_CURRENT_MONITORS];

/*-------------------------------------------------------------------------*//**
 *
 */
static uint16_t convert_mV_to_ppe_value
(
    ace_channel_handle_t    channel_handle,
    uint32_t                voltage
);

/*-------------------------------------------------------------------------*//**
 *
 */
void ace_init_convert(void);

/*-------------------------------------------------------------------------*//**
 * 
 */
#define VOLTAGE_CHANNEL     0u
#define CURRENT_CHANNEL     1u
#define TEMPERATURE_CHANNEL 2u
#define INVALID_CHANNEL     0xFFu

static const uint8_t channel_type_lut[] =
{
    VOLTAGE_CHANNEL,        /* ADC0_1P5V = 0 */
    VOLTAGE_CHANNEL,        /* ABPS0 = 1 */
    VOLTAGE_CHANNEL,        /* ABPS1 = 2 */
    CURRENT_CHANNEL,        /* CM0 = 3 */
    TEMPERATURE_CHANNEL,    /* TM0 = 4 */
    VOLTAGE_CHANNEL,        /* ABPS2 = 5 */
    VOLTAGE_CHANNEL,        /* ABPS3 = 6 */
    CURRENT_CHANNEL,        /* CM1 = 7 */
    TEMPERATURE_CHANNEL,    /* TM1 = 8 */
    VOLTAGE_CHANNEL,        /* ADC0 = 9 */
    VOLTAGE_CHANNEL,        /* ADC1 = 10 */
    VOLTAGE_CHANNEL,        /* ADC2 = 11 */
    VOLTAGE_CHANNEL,        /* ADC3 = 12 */
    INVALID_CHANNEL,
    INVALID_CHANNEL,
    VOLTAGE_CHANNEL,        /* SDD0_IN = 15 */

    VOLTAGE_CHANNEL,        /* ADC1_1P5V = 16 */
    VOLTAGE_CHANNEL,        /* ABPS4 = 17 */
    VOLTAGE_CHANNEL,        /* ABPS5 = 18 */
    CURRENT_CHANNEL,        /* CM2 = 19 */
    TEMPERATURE_CHANNEL,    /* TM2 = 20 */
    VOLTAGE_CHANNEL,        /* ABPS6 = 21 */
    VOLTAGE_CHANNEL,        /* ABPS7 = 22 */
    CURRENT_CHANNEL,        /* CM3 = 23 */
    TEMPERATURE_CHANNEL,    /* TM3 = 24 */
    VOLTAGE_CHANNEL,        /* ADC4 = 25 */
    VOLTAGE_CHANNEL,        /* ADC5 = 26 */
    VOLTAGE_CHANNEL,        /* ADC6 = 27 */
    VOLTAGE_CHANNEL,        /* ADC7 = 28 */
    INVALID_CHANNEL,
    INVALID_CHANNEL,
    VOLTAGE_CHANNEL,        /* SDD1_IN = 31 */

    VOLTAGE_CHANNEL,        /* ADC2_1P5V = 32 */
    VOLTAGE_CHANNEL,        /* ABPS8 = 33 */
    VOLTAGE_CHANNEL,        /* ABPS9 = 34 */
    CURRENT_CHANNEL,        /* CM4 = 35 */
    TEMPERATURE_CHANNEL,    /* TM4 = 36 */
    VOLTAGE_CHANNEL,        /* ABPS10 = 37 */
    VOLTAGE_CHANNEL,        /* ABPS11 = 38 */
    CURRENT_CHANNEL,        /* CM5 = 39 */
    TEMPERATURE_CHANNEL,    /* TM5 = 40 */
    VOLTAGE_CHANNEL,        /* ADC8 = 41 */
    VOLTAGE_CHANNEL,        /* ADC9 = 42 */
    VOLTAGE_CHANNEL,        /* ADC10 = 43 */
    VOLTAGE_CHANNEL,        /* ADC11 = 44 */
    INVALID_CHANNEL,
    INVALID_CHANNEL,
    VOLTAGE_CHANNEL         /* SDD2_IN = 47 */
};

static const uint8_t channel_quad_lut[] =
{
    0xFFu,   /* ADC0_1P5V = 0 */
    0u,      /* ABPS0 = 1 */
    0u,      /* ABPS1 = 2 */
    0u,      /* CM0 = 3 */
    0u,      /* TM0 = 4 */
    1u,      /* ABPS2 = 5 */
    1u,      /* ABPS3 = 6 */
    1u,      /* CM1 = 7 */
    1u,      /* TM1 = 8 */
    0xFFu,   /* ADC0 = 9 */
    0xFFu,   /* ADC1 = 10 */
    0xFFu,   /* ADC2 = 11 */
    0xFFu,   /* ADC3 = 12 */
    INVALID_CHANNEL,
    INVALID_CHANNEL,
    0xFFu,   /* SDD0_IN = 15 */

    0xFFu,   /* ADC1_1P5V = 16 */
    2u,      /* ABPS4 = 17 */
    2u,      /* ABPS5 = 18 */
    2u,      /* CM2 = 19 */
    2u,      /* TM2 = 20 */
    3u,      /* ABPS6 = 21 */
    3u,      /* ABPS7 = 22 */
    3u,      /* CM3 = 23 */
    3u,      /* TM3 = 24 */
    0xFFu,   /* ADC4 = 25 */
    0xFFu,   /* ADC5 = 26 */
    0xFFu,   /* ADC6 = 27 */
    0xFFu,   /* ADC7 = 28 */
    INVALID_CHANNEL,
    INVALID_CHANNEL,
    0xFFu,   /* SDD1_IN = 31 */

    0xFFu,   /* ADC2_1P5V = 32 */
    4u,      /* ABPS8 = 33 */
    4u,      /* ABPS9 = 34 */
    4u,      /* CM4 = 35 */
    4u,      /* TM4 = 36 */
    5u,      /* ABPS10 = 37 */
    5u,      /* ABPS11 = 38 */
    5u,      /* CM5 = 39 */
    5u,      /* TM5 = 40 */
    0xFFu,   /* ADC8 = 41 */
    0xFFu,   /* ADC9 = 42 */
    0xFFu,   /* ADC10 = 43 */
    0xFFu,   /* ADC11 = 44 */
    INVALID_CHANNEL,
    INVALID_CHANNEL,
    0xFFu    /* SDD2_IN = 47 */
};

/*-------------------------------------------------------------------------*//**
 *
 */
#define NON_ABPS_CHANNEL    0xFFu
#define MAX_NB_OF_APBS      12u

/*-------------------------------------------------------------------------*//**
 * Lookup of the quad to which an ABPS belongs
 */
static const uint8_t abps_channel_lut[] =
{
    NON_ABPS_CHANNEL,   /* ADC0_1P5V = 0 */
    0u,                 /* ABPS0 = 1 */
    0u,                 /* ABPS1 = 2 */
    NON_ABPS_CHANNEL,   /* CM0 = 3 */
    NON_ABPS_CHANNEL,   /* TM0 = 4 */
    1u,                 /* ABPS2 = 5 */
    1u,                 /* ABPS3 = 6 */
    NON_ABPS_CHANNEL,   /* CM1 = 7 */
    NON_ABPS_CHANNEL,   /* TM1 = 8 */
    NON_ABPS_CHANNEL,   /* ADC0 = 9 */
    NON_ABPS_CHANNEL,   /* ADC1 = 10 */
    NON_ABPS_CHANNEL,   /* ADC2 = 11 */
    NON_ABPS_CHANNEL,   /* ADC3 = 12 */
    INVALID_CHANNEL,
    INVALID_CHANNEL,
    NON_ABPS_CHANNEL,   /* SDD0_IN = 15 */

    NON_ABPS_CHANNEL,   /* ADC1_1P5V = 16 */
    2u,                 /* ABPS4 = 17 */
    2u,                 /* ABPS5 = 18 */
    NON_ABPS_CHANNEL,   /* CM2 = 19 */
    NON_ABPS_CHANNEL,   /* TM2 = 20 */
    3u,                 /* ABPS6 = 21 */
    3u,                 /* ABPS7 = 22 */
    NON_ABPS_CHANNEL,   /* CM3 = 23 */
    NON_ABPS_CHANNEL,   /* TM3 = 24 */
    NON_ABPS_CHANNEL,   /* ADC4 = 25 */
    NON_ABPS_CHANNEL,   /* ADC5 = 26 */
    NON_ABPS_CHANNEL,   /* ADC6 = 27 */
    NON_ABPS_CHANNEL,   /* ADC7 = 28 */
    INVALID_CHANNEL,
    INVALID_CHANNEL,
    NON_ABPS_CHANNEL,   /* SDD1_IN = 31 */

    NON_ABPS_CHANNEL,   /* ADC2_1P5V = 32 */
    4u,                 /* ABPS8 = 33 */
    4u,                 /* ABPS9 = 34 */
    NON_ABPS_CHANNEL,   /* CM4 = 35 */
    NON_ABPS_CHANNEL,   /* TM4 = 36 */
    5u,                 /* ABPS10 = 37 */
    5u,                 /* ABPS11 = 38 */
    NON_ABPS_CHANNEL,   /* CM5 = 39 */
    NON_ABPS_CHANNEL,   /* TM5 = 40 */
    NON_ABPS_CHANNEL,   /* ADC8 = 41 */
    NON_ABPS_CHANNEL,   /* ADC9 = 42 */
    NON_ABPS_CHANNEL,   /* ADC10 = 43 */
    NON_ABPS_CHANNEL,   /* ADC11 = 44 */
    INVALID_CHANNEL,
    INVALID_CHANNEL,
    NON_ABPS_CHANNEL    /* SDD2_IN = 47 */
};

static const uint8_t abps_idx_lut[] =
{
    NON_ABPS_CHANNEL,   /* ADC0_1P5V = 0 */
    0u,                 /* ABPS0 = 1 */
    1u,                 /* ABPS1 = 2 */
    NON_ABPS_CHANNEL,   /* CM0 = 3 */
    NON_ABPS_CHANNEL,   /* TM0 = 4 */
    2u,                 /* ABPS2 = 5 */
    3u,                 /* ABPS3 = 6 */
    NON_ABPS_CHANNEL,   /* CM1 = 7 */
    NON_ABPS_CHANNEL,   /* TM1 = 8 */
    NON_ABPS_CHANNEL,   /* ADC0 = 9 */
    NON_ABPS_CHANNEL,   /* ADC1 = 10 */
    NON_ABPS_CHANNEL,   /* ADC2 = 11 */
    NON_ABPS_CHANNEL,   /* ADC3 = 12 */
    INVALID_CHANNEL,
    INVALID_CHANNEL,
    NON_ABPS_CHANNEL,   /* SDD0_IN = 15 */

    NON_ABPS_CHANNEL,   /* ADC1_1P5V = 16 */
    4u,                 /* ABPS4 = 17 */
    5u,                 /* ABPS5 = 18 */
    NON_ABPS_CHANNEL,   /* CM2 = 19 */
    NON_ABPS_CHANNEL,   /* TM2 = 20 */
    6u,                 /* ABPS6 = 21 */
    7u,                 /* ABPS7 = 22 */
    NON_ABPS_CHANNEL,   /* CM3 = 23 */
    NON_ABPS_CHANNEL,   /* TM3 = 24 */
    NON_ABPS_CHANNEL,   /* ADC4 = 25 */
    NON_ABPS_CHANNEL,   /* ADC5 = 26 */
    NON_ABPS_CHANNEL,   /* ADC6 = 27 */
    NON_ABPS_CHANNEL,   /* ADC7 = 28 */
    INVALID_CHANNEL,
    INVALID_CHANNEL,
    NON_ABPS_CHANNEL,   /* SDD1_IN = 31 */

    NON_ABPS_CHANNEL,   /* ADC2_1P5V = 32 */
    8u,                 /* ABPS8 = 33 */
    9u,                 /* ABPS9 = 34 */
    NON_ABPS_CHANNEL,   /* CM4 = 35 */
    NON_ABPS_CHANNEL,   /* TM4 = 36 */
    10u,                 /* ABPS10 = 37 */
    11u,                 /* ABPS11 = 38 */
    NON_ABPS_CHANNEL,   /* CM5 = 39 */
    NON_ABPS_CHANNEL,   /* TM5 = 40 */
    NON_ABPS_CHANNEL,   /* ADC8 = 41 */
    NON_ABPS_CHANNEL,   /* ADC9 = 42 */
    NON_ABPS_CHANNEL,   /* ADC10 = 43 */
    NON_ABPS_CHANNEL,   /* ADC11 = 44 */
    INVALID_CHANNEL,
    INVALID_CHANNEL,
    NON_ABPS_CHANNEL    /* SDD2_IN = 47 */
};

/*-------------------------------------------------------------------------*//**
 *
 */
static const int8_t apbs_gain_lut[] =
{
    12,
    8,
    4,
    2
};

static const int16_t apbs_range[] =
{
    15360,
    10240,
    5120,
    2560
};

static uint8_t g_gdec_lut[MAX_NB_OF_APBS];
static channel_type_t channel_type_lut_h[ACE_NB_OF_INPUT_CHANNELS];


/*-------------------------------------------------------------------------*//**
 *
 */
channel_type_t
ACE_get_channel_type
(
    ace_channel_handle_t    channel_handle
)
{
    channel_type_t channel_type = VOLTAGE;
    
    ASSERT(channel_handle < ACE_NB_OF_INPUT_CHANNELS);
    
    if((int32_t)channel_handle < ACE_NB_OF_INPUT_CHANNELS)
    {
        channel_type = channel_type_lut_h[channel_handle];
    }
    else
    {
        channel_type = VOLTAGE;
    }
    
    return channel_type;
}

/*-------------------------------------------------------------------------*//**
 *
 */
uint32_t ACE_convert_adc_input_to_mV
(
    ace_channel_handle_t    channel_handle,
    uint16_t                sample_value
)
{
    uint32_t voltage;
    adc_channel_id_t channel_id;
    uint8_t adc_id;
    
    channel_id = g_ace_channel_desc_table[channel_handle].signal_id;
    adc_id = (uint8_t)channel_id >> 4u;
    voltage = ( g_ace_adc_config[adc_id].va_ref * (uint32_t)sample_value ) / g_ace_adc_config[adc_id].adc_resolution;
    
    return voltage;
}

/*-------------------------------------------------------------------------*//**
 *
 */
#define PPE_SAMPLES_RESOLUTION    4095u

/*-------------------------------------------------------------------------*//**
 *
 */
void ace_init_convert(void)
{
    uint8_t abps_idx;
    int32_t channel;
    uint32_t saved_pc2_ctrl;
    
    /* Pause the SSE PC2 while accesses to ACB from APB3 are taking place. */
    saved_pc2_ctrl = ACE->PC2_CTRL;
    ACE->PC2_CTRL = 0u;
    
    /* Populate the g_gdec_lut look-up table. */
    for(abps_idx = 0u; abps_idx < MAX_NB_OF_APBS; ++abps_idx)
    {
        uint8_t quad_id;
        uint8_t acb_config_byte;
        uint32_t channel_is_abps2;
        
        quad_id = abps_idx / 2u;
        acb_config_byte = ACE->ACB_DATA[quad_id].b8;
        channel_is_abps2 = abps_idx & 0x01uL;
        if(channel_is_abps2)
        {
            /* ABPS2 */
            g_gdec_lut[abps_idx] = (acb_config_byte >> 5u) & 0x03u;
        }
        else
        {
            /* ABPS1 */
            g_gdec_lut[abps_idx] = (acb_config_byte >> 1u) & 0x03u;
        }
    }
    
    /* Populate the channel_type_lut_h look-up table. */
    for(channel = 0; channel < ACE_NB_OF_INPUT_CHANNELS; ++channel)
    {
        uint8_t quad_id;
        uint8_t acb_config_byte;
        adc_channel_id_t channel_id;
        channel_type_t channel_type;
    
        channel_id = g_ace_channel_desc_table[channel].signal_id;
        quad_id = channel_quad_lut[channel_id];
        
        switch (channel_type_lut[channel_id])
        {
            case VOLTAGE_CHANNEL:
                channel_type = VOLTAGE;
                break;
                
            case CURRENT_CHANNEL:
                ASSERT( quad_id != 0xFFu );
                acb_config_byte = ACE->ACB_DATA[quad_id].b9;
                if ( acb_config_byte & 0x01u )
                {
                    channel_type = VOLTAGE;
                }
                else
                {
                    channel_type = CURRENT;
                }
                break;
            
            case TEMPERATURE_CHANNEL:
                ASSERT( quad_id != 0xFFu );
                acb_config_byte = ACE->ACB_DATA[quad_id].b10;
                if ( acb_config_byte & 0x01u )
                {
                    channel_type = VOLTAGE;
                }
                else
                {
                    channel_type = TEMPERATURE;
                }
                break;
                
            default:
                ASSERT(0);
                channel_type = VOLTAGE;
                break;
        }
        
        channel_type_lut_h[channel] = channel_type;
    }
    
    /* Restore SSE PC2 operations. */
    ACE->PC2_CTRL = saved_pc2_ctrl;
}

/*-------------------------------------------------------------------------*//**
 *
 */
int32_t ACE_convert_to_mV
(
    ace_channel_handle_t    channel_handle,
    uint16_t                sample_value
)
{
    uint32_t adc_voltage;
    int32_t voltage;
    adc_channel_id_t channel_id;
    uint8_t adc_id;
    uint8_t apbs_idx;
    
    channel_id = g_ace_channel_desc_table[channel_handle].signal_id;
    adc_id = (uint8_t)channel_id >> 4u;
    adc_voltage = ( g_ace_adc_config[adc_id].va_ref * (uint32_t)sample_value ) / PPE_SAMPLES_RESOLUTION;
    voltage = (int32_t)adc_voltage;

    apbs_idx = abps_idx_lut[channel_id];
    if ( abps_channel_lut[channel_id] != NON_ABPS_CHANNEL )
    {
        uint8_t gdec;
        gdec = g_gdec_lut[apbs_idx];
        voltage = (voltage * apbs_gain_lut[gdec]) - apbs_range[gdec];
    }
    return voltage;
}

/*-------------------------------------------------------------------------*//**
 *
 */
uint32_t ACE_convert_to_mA
(
    ace_channel_handle_t    channel_handle,
    uint16_t                sample_value
)
{
    uint32_t current = 0u;
    
    ASSERT(channel_handle < ACE_NB_OF_INPUT_CHANNELS);
    
    if((int32_t)channel_handle < ACE_NB_OF_INPUT_CHANNELS)
    {
        adc_channel_id_t channel_id;
        uint8_t current_monitor_idx;
        
        channel_id = g_ace_channel_desc_table[channel_handle].signal_id;
        ASSERT(channel_id < sizeof(channel_type_lut));
        if(CURRENT_CHANNEL == channel_type_lut[channel_id])
        {
            uint32_t resistor;
            uint32_t voltage;
            
            /* Compute index into g_ace_current_resistors[] from the current
             * channel number. This uses bit 2, 4 and 5 of the channel number
             * to derive the index as follows:
             *  channel name : channel number : index
             *       CM0     :       0x03     :   0
             *       CM1     :       0x07     :   1
             *       CM2     :       0x13     :   2
             *       CM3     :       0x17     :   3
             *       CM4     :       0x23     :   4
             *       CM5     :       0x27     :   5
             */
            current_monitor_idx
                = (((uint8_t)channel_id & 0x04u) >> 2u) + (((uint8_t)channel_id & 0x30u) >> 3u);
            
            if(current_monitor_idx < (uint8_t)ACE_NB_OF_CURRENT_MONITORS)
            {
                /* Retrieve the current sensing external resistor value from 
                 * the ACE configuration data generated by the ACE configurator. */
                resistor = g_ace_current_resistors[current_monitor_idx];
                
                /* Compute mA current value taking into account the amplication
                 * factor of 50 used within the current monitor hardware. */
                voltage = ACE_convert_adc_input_to_mV(channel_handle, sample_value);
                current = (voltage * (1000u / 50u)) / resistor;
;
            }
        }
    }
    
    return current;
}

/*-------------------------------------------------------------------------*//**
 *
 */
uint32_t ACE_convert_to_Kelvin
(
    ace_channel_handle_t    channel_handle,
    uint16_t                sample_value
)
{
    uint32_t temperature;
    uint32_t voltage;
    
    voltage = ACE_convert_adc_input_to_mV( channel_handle, sample_value );
    
    /* Tk = (V * 10^3) / 2.5  */
    temperature = (voltage * 10u) / 25u;
    
    return temperature;
}

/*-------------------------------------------------------------------------*//**
 *
 */
int32_t ACE_convert_to_Celsius
(
    ace_channel_handle_t    channel_handle,
    uint16_t                sample_value
)
{
    int32_t temperature;
    int32_t voltage;
    
    voltage = (int32_t)ACE_convert_adc_input_to_mV( channel_handle, sample_value );
    
    /* Tk = (V * 10^3) / 2.5  */
    /* Tc = Tk - 273.15 */
    temperature = (voltage * 4) - 2731;
    
    return temperature;
}

/*-------------------------------------------------------------------------*//**
 *
 */
int32_t ACE_convert_to_Fahrenheit
(
    ace_channel_handle_t    channel_handle,
    uint16_t                sample_value
)
{
    int32_t temperature;
    
    temperature = (int32_t)ACE_convert_to_Kelvin( channel_handle, sample_value );
    
    /* F = (K * 9/5) - 459.67 */
    temperature = ((temperature * 9) / 5) - 459;
    
    return temperature;
}

/*-------------------------------------------------------------------------*//**
 *
 */
const uint8_t * ACE_get_channel_name
(
    ace_channel_handle_t    channel_handle
)
{
    const uint8_t * p_channel_name = 0;
    
    if ( channel_handle < NB_OF_ACE_CHANNEL_HANDLES)
    {
        p_channel_name = g_ace_channel_desc_table[channel_handle].p_sz_channel_name;
    }
    
    return p_channel_name;
}

/*-------------------------------------------------------------------------*//**
 *
 */
uint16_t ACE_convert_mV_to_adc_value
(
    ace_channel_handle_t    channel_handle,
    uint32_t                voltage
)
{
    uint16_t sample_value;
    adc_channel_id_t channel_id;
    uint8_t adc_id;
    
    channel_id = g_ace_channel_desc_table[channel_handle].signal_id;
    adc_id = (uint8_t)channel_id >> 4u;
    
    if (voltage > g_ace_adc_config[adc_id].va_ref)
    {
        sample_value = g_ace_adc_config[adc_id].adc_resolution - 1u;
    }
    else
    {
        sample_value = (uint16_t)((voltage * (g_ace_adc_config[adc_id].adc_resolution - 1)) / g_ace_adc_config[adc_id].va_ref);
    }
    
    return sample_value;
}

/*-------------------------------------------------------------------------*//**
 *
 */
static uint16_t convert_mV_to_ppe_value
(
    ace_channel_handle_t    channel_handle,
    uint32_t                voltage
)
{
    uint16_t sample_value;
    adc_channel_id_t channel_id;
    uint8_t adc_id;
    
    channel_id = g_ace_channel_desc_table[channel_handle].signal_id;
    adc_id = (uint8_t)channel_id >> 4u;
    
    if (voltage > g_ace_adc_config[adc_id].va_ref)
    {
        sample_value = PPE_SAMPLES_RESOLUTION;
    }
    else
    {
        sample_value = (uint16_t)((voltage * PPE_SAMPLES_RESOLUTION) / g_ace_adc_config[adc_id].va_ref);
    }
    
    return sample_value;
}

#define MAX_PPE_SAMPLE_VALUE    0x0FFFu

/*-------------------------------------------------------------------------*//**
 *
 */
uint16_t ACE_convert_from_mV
(
    ace_channel_handle_t    channel_handle,
    int32_t                 voltage
)
{
    uint16_t sample_value;
    adc_channel_id_t channel_id;
    uint8_t adc_id;
    uint32_t adc_voltage;
    
    channel_id = g_ace_channel_desc_table[channel_handle].signal_id;
    adc_id = (uint8_t)channel_id >> 4u;
    
    if ( abps_channel_lut[channel_id] == NON_ABPS_CHANNEL )
    {
        if (voltage > 0)
        {
            adc_voltage = (uint32_t)voltage;
        }
        else
        {
            adc_voltage = 0u;
        }
    }
    else
    {
        uint8_t apbs_idx;
        uint8_t gdec;
        
        apbs_idx = abps_idx_lut[channel_id];
        gdec = g_gdec_lut[apbs_idx];
        voltage = voltage + apbs_range[gdec];
        if (voltage > 0)
        {
	        adc_voltage = (uint32_t)voltage;
	        adc_voltage = adc_voltage / (uint8_t)apbs_gain_lut[gdec];
        }
        else
        {
        	adc_voltage = 0;
        }
    }
    
    sample_value = (uint16_t)((adc_voltage * PPE_SAMPLES_RESOLUTION) / g_ace_adc_config[adc_id].va_ref);
    
    if (sample_value > MAX_PPE_SAMPLE_VALUE)
    {
        sample_value = MAX_PPE_SAMPLE_VALUE;
    }
    return sample_value;
}

/*-------------------------------------------------------------------------*//**
 *
 */
uint16_t ACE_convert_from_mA
(
    ace_channel_handle_t    channel_handle,
    uint32_t                current
)
{
    uint16_t sample_value;
    uint32_t voltage;
    uint32_t resistor = 1u;
    
    voltage = current * 50u * resistor;
    sample_value = convert_mV_to_ppe_value( channel_handle, voltage );
    
    if (sample_value > MAX_PPE_SAMPLE_VALUE)
    {
        sample_value = MAX_PPE_SAMPLE_VALUE;
    }
    return sample_value;
}

/*-------------------------------------------------------------------------*//**
 *
 */
uint16_t ACE_convert_from_Kelvin
(
    ace_channel_handle_t    channel_handle,
    uint32_t                temperature
)
{
    uint16_t sample_value;
    uint32_t voltage;
    
    voltage = (temperature * 25u) / 10u;
    sample_value = convert_mV_to_ppe_value( channel_handle, voltage );
    
    if (sample_value > MAX_PPE_SAMPLE_VALUE)
    {
        sample_value = MAX_PPE_SAMPLE_VALUE;
    }
    return sample_value;
}

/*-------------------------------------------------------------------------*//**
 *
 */
uint16_t ACE_convert_from_Celsius
(
    ace_channel_handle_t    channel_handle,
    int32_t                 temperature
)
{
    uint16_t sample_value;
    uint32_t voltage;
    
    temperature = temperature + 2731;
    voltage = (uint32_t)temperature / 4u;
    sample_value = convert_mV_to_ppe_value( channel_handle, voltage );
    
    if (sample_value > MAX_PPE_SAMPLE_VALUE)
    {
        sample_value = MAX_PPE_SAMPLE_VALUE;
    }
    return sample_value;
}

/*-------------------------------------------------------------------------*//**
 *
 */
uint16_t ACE_convert_from_Fahrenheit
(
    ace_channel_handle_t    channel_handle,
    int32_t                 temperature
)
{
    uint16_t sample_value;
    uint32_t kelvin;
    
    temperature = temperature + 459;
    kelvin = (uint32_t)temperature;
    kelvin = (kelvin * 5u) / 9u;
    
    sample_value = ACE_convert_from_Kelvin( channel_handle, kelvin );
    
    if (sample_value > MAX_PPE_SAMPLE_VALUE)
    {
        sample_value = MAX_PPE_SAMPLE_VALUE;
    }
    return sample_value;
}

/*-------------------------------------------------------------------------*//**
 *
 */
uint16_t ACE_translate_pdma_value
(
    uint32_t            pdma_value,
    adc_channel_id_t *  channel_id
)
{
    uint16_t ppe_value;
      
    ppe_value = (pdma_value >> 8u) & 0xFFFFu;
    if ( channel_id != 0 )
    {
        *channel_id = (adc_channel_id_t)((pdma_value >> 24u) & 0xFFu);
    }
    
    return ppe_value;
}

#ifdef __cplusplus
}
#endif

