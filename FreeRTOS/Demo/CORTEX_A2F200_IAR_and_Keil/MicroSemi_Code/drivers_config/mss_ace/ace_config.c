/*****************************************************************************
* (c) Copyright  Actel Corporation. All rights reserved.
*
*ACE configuration .c file
*Created by Actel MSS_ACE Configurator Fri Dec 17 12:12:19 2010
*
*/

#include "../../drivers/mss_ace/mss_ace_configurator.h"
#include "ace_config.h"
#include "ace_handles.h"

#include <stdint.h>


/*-----------------------------------------------------------------------------
*AB Configuration
*---------------------------------------------------------------------------*/
ace_adc_config_t g_ace_adc_config[ACE_NB_OF_ADC] =
{
	{
        4096,                      /* uint16_t adc_resolution */
        2560                       /* uint16_t va_ref */
	},
	{
        4096,                      /* uint16_t adc_resolution */
        2560                       /* uint16_t va_ref */
	},
	{
        4096,                      /* uint16_t adc_resolution */
        2560                       /* uint16_t va_ref */
	}
};

/*-----------------------------------------------------------------------------
*Current Monitor Resistor Values
*---------------------------------------------------------------------------*/
const uint32_t g_ace_current_resistors[ACE_NB_OF_CURRENT_MONITORS] =
{
	100000,	/*CM0 ( USED AS CURRENT MONITOR ) */
	1,	/*CM1 ( NOT USED AS CURRENT MONITOR ) */
	1,	/*CM2 ( NOT USED AS CURRENT MONITOR ) */
	1,	/*CM3 ( NOT USED AS CURRENT MONITOR ) */
	1	/*CM4 ( NOT USED AS CURRENT MONITOR ) */
};

/*-----------------------------------------------------------------------------
*Analog Channels
*---------------------------------------------------------------------------*/
/* Names*/
const uint8_t g_ace_channel_0_name[] = "CurrentMonitor_0";
const uint8_t g_ace_channel_1_name[] = "VoltageMonitor_0";
const uint8_t g_ace_channel_2_name[] = "TemperatureMonitor_0";

/* Number of Flags per Channel*/
#define CHANNEL_0_NB_OF_FLAGS           0
#define CHANNEL_1_NB_OF_FLAGS           0
#define CHANNEL_2_NB_OF_FLAGS           0

/* Input Channel to Flag Array Association*/

/* Channel Table*/
ace_channel_desc_t g_ace_channel_desc_table[ACE_NB_OF_INPUT_CHANNELS] =
{
	{
        g_ace_channel_0_name,      /* const uint8_t * p_sz_channel_name */
        CM0,                       /* adc_channel_id_t signal_id; */
        14,                        /* uint16_t signal_ppe_offset */
        CHANNEL_0_NB_OF_FLAGS,     /* uint16_t nb_of_flags */
        0                          /* uint16_t * p_flags_array */
	},
	{
        g_ace_channel_1_name,      /* const uint8_t * p_sz_channel_name */
        TM0,                       /* adc_channel_id_t signal_id; */
        23,                        /* uint16_t signal_ppe_offset */
        CHANNEL_1_NB_OF_FLAGS,     /* uint16_t nb_of_flags */
        0                          /* uint16_t * p_flags_array */
	},
	{
        g_ace_channel_2_name,      /* const uint8_t * p_sz_channel_name */
        TM1,                       /* adc_channel_id_t signal_id; */
        32,                        /* uint16_t signal_ppe_offset */
        CHANNEL_2_NB_OF_FLAGS,     /* uint16_t nb_of_flags */
        0                          /* uint16_t * p_flags_array */
	}
};

/*-----------------------------------------------------------------------------
*Threshold Flags
*---------------------------------------------------------------------------*/
/* Flag Names*/
/* Flag Table*/
#if ACE_NB_OF_PPE_FLAGS != 0
	ppe_flag_desc_t g_ppe_flags_desc_table[ACE_NB_OF_PPE_FLAGS] =
	{
	};
#endif

/*-----------------------------------------------------------------------------
*Sequencer Procedures
*---------------------------------------------------------------------------*/
/* Procedure Name and Microcode*/
const uint8_t g_ace_sse_proc_0_name[] = "ADC0_MAIN";
const uint16_t g_ace_sse_proc_0_sequence[] =
{
	0x1705, 0x1601, 0x155c, 0x14c4,
	0x0000, 0x152d, 0x8a0c, 0x1309,
	0x0000, 0x14c3, 0x0000, 0x8a04,
	0x152d, 0x970c, 0x132f, 0x0000,
	0x14c8, 0x0000, 0x9704, 0x1301,
	0x0000, 0x1002
};

const uint8_t g_ace_sse_proc_1_name[] = "ADC1_MAIN";
const uint16_t g_ace_sse_proc_1_sequence[] =
{
	0x2705, 0x2601, 0x2200
};

const uint8_t g_ace_sse_proc_2_name[] = "ADC2_MAIN";
const uint16_t g_ace_sse_proc_2_sequence[] =
{
	0x3705, 0x3601, 0x3200
};



/* Procedure Table*/
ace_procedure_desc_t g_sse_sequences_desc_table[ACE_NB_OF_SSE_PROCEDURES] =
{
	{
        g_ace_sse_proc_0_name,                              /* const uint8_t * p_sz_proc_name */
        2,                                                  /* uint16_t sse_loop_pc */
        0,                                                  /* uint16_t sse_load_offset */
        sizeof(g_ace_sse_proc_0_sequence) / sizeof(uint16_t), /* uint16_t sse_ucode_length */
        g_ace_sse_proc_0_sequence,                          /* const uint16_t * sse_ucode */
        0                                                   /* uint8_t sse_pc_id */
	},
	{
        g_ace_sse_proc_1_name,                              /* const uint8_t * p_sz_proc_name */
        24,                                                 /* uint16_t sse_loop_pc */
        22,                                                 /* uint16_t sse_load_offset */
        sizeof(g_ace_sse_proc_1_sequence) / sizeof(uint16_t), /* uint16_t sse_ucode_length */
        g_ace_sse_proc_1_sequence,                          /* const uint16_t * sse_ucode */
        1                                                   /* uint8_t sse_pc_id */
	},
	{
        g_ace_sse_proc_2_name,                              /* const uint8_t * p_sz_proc_name */
        27,                                                 /* uint16_t sse_loop_pc */
        25,                                                 /* uint16_t sse_load_offset */
        sizeof(g_ace_sse_proc_2_sequence) / sizeof(uint16_t), /* uint16_t sse_ucode_length */
        g_ace_sse_proc_2_sequence,                          /* const uint16_t * sse_ucode */
        2                                                   /* uint8_t sse_pc_id */
	}
};


