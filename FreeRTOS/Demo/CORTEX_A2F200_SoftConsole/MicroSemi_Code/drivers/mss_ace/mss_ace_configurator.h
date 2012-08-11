/*******************************************************************************
 * (c) Copyright 2009 Actel Corporation.  All rights reserved.
 * 
 * SVN $Revision: 2841 $
 * SVN $Date: 2010-07-20 18:10:00 +0100 (Tue, 20 Jul 2010) $
 */

/*=========================================================================*//**
  @mainpage ACE Configurator data provided to ACE Driver.

  @section intro_sec Introduction
  This file contains the definition of data structures used by the ACE
  Configurator software tool for sharing information about the ACE configuration
  with the ACE driver. It also contains the API for accessor functions used by
  the ACE driver to extract relevant information from these data structures.
 *//*=========================================================================*/
#ifndef __MSS_ACE_CONFIGURATOR_H_
#define __MSS_ACE_CONFIGURATOR_H_

#include "mss_ace.h"

#ifdef __cplusplus
extern "C" {
#endif 

/*-------------------------------------------------------------------------*//**
  Post Processing Engine (PPE) flags IDs.
 */
typedef enum
{
    PPE_FLAGS0_0 = 0,
    PPE_FLAGS0_1 = 1,
    PPE_FLAGS0_2 = 2,
    PPE_FLAGS0_3 = 3,
    PPE_FLAGS0_4 = 4,
    PPE_FLAGS0_5 = 5,
    PPE_FLAGS0_6 = 6,
    PPE_FLAGS0_7 = 7,
    PPE_FLAGS0_8 = 8,
    PPE_FLAGS0_9 = 9,
    PPE_FLAGS0_10 = 10,
    PPE_FLAGS0_11 = 11,
    PPE_FLAGS0_12 = 12,
    PPE_FLAGS0_13 = 13,
    PPE_FLAGS0_14 = 14,
    PPE_FLAGS0_15 = 15,
    PPE_FLAGS0_16 = 16,
    PPE_FLAGS0_17 = 17,
    PPE_FLAGS0_18 = 18,
    PPE_FLAGS0_19 = 19,
    PPE_FLAGS0_20 = 20,
    PPE_FLAGS0_21 = 21,
    PPE_FLAGS0_22 = 22,
    PPE_FLAGS0_23 = 23,
    PPE_FLAGS0_24 = 24,
    PPE_FLAGS0_25 = 25,
    PPE_FLAGS0_26 = 26,
    PPE_FLAGS0_27 = 27,
    PPE_FLAGS0_28 = 28,
    PPE_FLAGS0_29 = 29,
    PPE_FLAGS0_30 = 30,
    PPE_FLAGS0_31 = 31,
    PPE_FLAGS1_0 = 32,
    PPE_FLAGS1_1 = 33,
    PPE_FLAGS1_2 = 34,
    PPE_FLAGS1_3 = 35,
    PPE_FLAGS1_4 = 36,
    PPE_FLAGS1_5 = 37,
    PPE_FLAGS1_6 = 38,
    PPE_FLAGS1_7 = 39,
    PPE_FLAGS1_8 = 40,
    PPE_FLAGS1_9 = 41,
    PPE_FLAGS1_10 = 42,
    PPE_FLAGS1_11 = 43,
    PPE_FLAGS1_12 = 44,
    PPE_FLAGS1_13 = 45,
    PPE_FLAGS1_14 = 46,
    PPE_FLAGS1_15 = 47,
    PPE_FLAGS1_16 = 48,
    PPE_FLAGS1_17 = 49,
    PPE_FLAGS1_18 = 50,
    PPE_FLAGS1_19 = 51,
    PPE_FLAGS1_20 = 52,
    PPE_FLAGS1_21 = 53,
    PPE_FLAGS1_22 = 54,
    PPE_FLAGS1_23 = 55,
    PPE_FLAGS1_24 = 56,
    PPE_FLAGS1_25 = 57,
    PPE_FLAGS1_26 = 58,
    PPE_FLAGS1_27 = 59,
    PPE_FLAGS1_28 = 60,
    PPE_FLAGS1_29 = 61,
    PPE_FLAGS1_30 = 62,
    PPE_FLAGS1_31 = 63,
    PPE_FLAGS2_0 = 64,
    PPE_FLAGS2_1 = 65,
    PPE_FLAGS2_2 = 66,
    PPE_FLAGS2_3 = 67,
    PPE_FLAGS2_4 = 68,
    PPE_FLAGS2_5 = 69,
    PPE_FLAGS2_6 = 70,
    PPE_FLAGS2_7 = 71,
    PPE_FLAGS2_8 = 72,
    PPE_FLAGS2_9 = 73,
    PPE_FLAGS2_10 = 74,
    PPE_FLAGS2_11 = 75,
    PPE_FLAGS2_12 = 76,
    PPE_FLAGS2_13 = 77,
    PPE_FLAGS2_14 = 78,
    PPE_FLAGS2_15 = 79,
    PPE_FLAGS2_16 = 80,
    PPE_FLAGS2_17 = 81,
    PPE_FLAGS2_18 = 82,
    PPE_FLAGS2_19 = 83,
    PPE_FLAGS2_20 = 84,
    PPE_FLAGS2_21 = 85,
    PPE_FLAGS2_22 = 86,
    PPE_FLAGS2_23 = 87,
    PPE_FLAGS2_24 = 88,
    PPE_FLAGS2_25 = 89,
    PPE_FLAGS2_26 = 90,
    PPE_FLAGS2_27 = 91,
    PPE_FLAGS2_28 = 92,
    PPE_FLAGS2_29 = 93,
    PPE_FLAGS2_30 = 94,
    PPE_FLAGS2_31 = 95,
    PPE_FLAGS3_0 = 96,
    PPE_FLAGS3_1 = 97,
    PPE_FLAGS3_2 = 98,
    PPE_FLAGS3_3 = 99,
    PPE_FLAGS3_4 = 100,
    PPE_FLAGS3_5 = 101,
    PPE_FLAGS3_6 = 102,
    PPE_FLAGS3_7 = 103,
    PPE_FLAGS3_8 = 104,
    PPE_FLAGS3_9 = 105,
    PPE_FLAGS3_10 = 106,
    PPE_FLAGS3_11 = 107,
    PPE_FLAGS3_12 = 108,
    PPE_FLAGS3_13 = 109,
    PPE_FLAGS3_14 = 110,
    PPE_FLAGS3_15 = 111,
    PPE_FLAGS3_16 = 112,
    PPE_FLAGS3_17 = 113,
    PPE_FLAGS3_18 = 114,
    PPE_FLAGS3_19 = 115,
    PPE_FLAGS3_20 = 116,
    PPE_FLAGS3_21 = 117,
    PPE_FLAGS3_22 = 118,
    PPE_FLAGS3_23 = 119,
    PPE_FLAGS3_24 = 120,
    PPE_FLAGS3_25 = 121,
    PPE_FLAGS3_26 = 122,
    PPE_FLAGS3_27 = 123,
    PPE_FLAGS3_28 = 124,
    PPE_FLAGS3_29 = 125,
    PPE_FLAGS3_30 = 126,
    PPE_FLAGS3_31 = 127,
    PPE_SFFLAGS_0 = 128,
    PPE_SFFLAGS_1 = 129,
    PPE_SFFLAGS_2 = 130,
    PPE_SFFLAGS_3 = 131,
    PPE_SFFLAGS_4 = 132,
    PPE_SFFLAGS_5 = 133,
    PPE_SFFLAGS_6 = 134,
    PPE_SFFLAGS_7 = 135,
    PPE_SFFLAGS_8 = 136,
    PPE_SFFLAGS_9 = 137,
    PPE_SFFLAGS_10 = 138,
    PPE_SFFLAGS_11 = 139,
    PPE_SFFLAGS_12 = 140,
    PPE_SFFLAGS_13 = 141,
    PPE_SFFLAGS_14 = 142,
    PPE_SFFLAGS_15 = 143,
    PPE_SFFLAGS_16 = 144,
    PPE_SFFLAGS_17 = 145,
    PPE_SFFLAGS_18 = 146,
    PPE_SFFLAGS_19 = 147,
    PPE_SFFLAGS_20 = 148,
    PPE_SFFLAGS_21 = 149,
    PPE_SFFLAGS_22 = 150,
    PPE_SFFLAGS_23 = 151,
    PPE_SFFLAGS_24 = 152,
    PPE_SFFLAGS_25 = 153,
    PPE_SFFLAGS_26 = 154,
    PPE_SFFLAGS_27 = 155,
    PPE_SFFLAGS_28 = 156,
    PPE_SFFLAGS_29 = 157,
    PPE_SFFLAGS_30 = 158,
    PPE_SFFLAGS_31 = 159,
    NB_OF_PPE_FLAGS = 160
} ppe_flag_id_t;

/*-------------------------------------------------------------------------*//**
  Flag types.
  The following defines are used to indicate the type of flag selected in the
  ACE configurator.
 */
/**
  A flag configured as BASIC_THRESHOLD_OVER will be asserted when the value of
  the input channel exceeds the value of the flag threshold. The flag will be
  de-asserted once the value of the input channel falls back under the threshold
  value. No hysteresis or state filtering is applied to the flag.
 */
#define BASIC_THRESHOLD_OVER    0u

/**
  A flag configured as BASIC_THRESHOLD_UNDER will be asserted when the value of
  the input channel falls under the value of the flag threshold. The flag will be
  de-asserted once the value of the input channel exceeds the threshold value.
  No hysteresis or state filtering is applied to the flag.
 */
#define BASIC_THRESHOLD_UNDER   1u

/**
  A flag configured as STATE_FILTERED_OVER will be asserted when n consecutive
  samples of the analog input are seen to exceed the value of the flag threshold,
  where n is the number selected in the "assert samples" option of the ACE
  configuration softwaretool flag's configuration.
  The flag will be de-asserted once m consecutive samples as seen below the flag
  threshold value, where m is the number selected in the "deassert samples"
  option of the flag's configuration user interface.
 */
#define STATE_FILTERED_OVER     2u

/**
  A flag configured as STATE_FILTERED_UNDER will be asserted when n consecutive
  samples of the analog input are seen below the value of the flag threshold,
  where n is the number selected in the "assert samples" option of the ACE
  configuration softwaretool flag's configuration.
  The flag will be de-asserted once m consecutive samples as seen to exceed the
  flag threshold value, where m is the number selected in the "deassert samples"
  option of the flag's configuration user interface.
 */
#define STATE_FILTERED_UNDER    3u

/**
  A flag configured as DUAL_HYSTERESIS_OVER will be asserted when the value
  of the input channel exceeds the threshold value plus the hysteresis value.
  The flag will be deasserted when the value of the input channel falls under the
  threshold value minus the hysteresis value.
  */
#define DUAL_HYSTERESIS_OVER    4u

/**
  A flag configured as DUAL_HYSTERESIS_UNDER will be asserted when the value
  of the input channel falls under the threshold value minus the hysteresis value.
  The flag will be deasserted when the value of the input channel exceeds the
  threshold value plus the hysteresis value.
  */
#define DUAL_HYSTERESIS_UNDER   5u

/**
  A flag configured as IPMI_HYSTERESIS_OVER will be asserted when the value
  of the input channel exceeds the threshold value. The flag will be deasserted
  when the value of the input channel falls under the threshold value minus the
  hysteresis value.
  */
#define IPMI_HYSTERESIS_OVER    6u

/**
  A flag configured as IPMI_HYSTERESIS_UNDER will be asserted when the value
  of the input channel falls under the threshold value. The flag will be
  deasserted when the value of the input channel exceeds the threshold value
  plus the hysteresis value.
  */
#define IPMI_HYSTERESIS_UNDER   7u

/*-------------------------------------------------------------------------*//**
  State filtered flag configuration.
 */
typedef struct __state_filtering_cfg
{
    /**
      Number of consecutive samples required for flag assertion.
     */
    uint8_t assert_samples;
    
    /**
      Number of consecutive samples required for flag deassertion.
     */
    uint8_t deassert_samples;
} state_filtering_cfg_t;

/*-------------------------------------------------------------------------*//**
  Post Processing Engine generated flag descriptor.
 */
typedef struct
{
    /**
      Pointer to a zero-terminated string identifying the flag described by this
      structure. This unique flag name is the name selected in the ACE configurator
      software tool when creating a flag.
      The flag unique name contains both the name of the monitored input channel
      and the name of the flag generated based the level of that input separated
      by ":". For example, the unique name for the flag called "CriticalOver"
      raised when the input channel called "MainSupply" reaches a critical level
      would be named "MainSupply:CriticalOver".
     */
    const uint8_t * p_sz_flag_name;
    
    /**
      The flag_id element identifies which PPE hardware flag will be asserted
      when the flag conditions are found to be met by the Post Processing Engine.
      This flag_id is typically used by the ACE driver to determine which ACE
      register is used to enable, disable and clear interrupts on the associated
      flag.
     */
    ppe_flag_id_t flag_id;
    
    /**
      The flag_type element specifies the type of the described flag. It is
      specified using one of the following:
        - BASIC_THRESHOLD_OVER
        - BASIC_THRESHOLD_UNDER
        - STATE_FILTERED_OVER
        - STATE_FILTERED_UNDER
        - DUAL_HYSTERESIS_OVER
        - DUAL_HYSTERESIS_UNDER
        - IPMI_HYSTERESIS_OVER
        - IPMI_HYSTERESIS_UNDER
     */
    uint8_t flag_type;
    
    /**
      PPE RAM offset of flag threshold level.
      This is the 32-bit word offset within the Post Processing Engine RAM where
      the threshold associated with this flag is stored. This is used to allow
      the ACE driver dynamically modifying the threshold beyond which a flag is
      asserted.
      In the case of hysteresis flags, threshold_ppe_offset indicates the
      start location of two consecutive PPE RAM words containing the ADC value
      of the hysteresis low limit followed by the ADC value for the high
      hysteresis limit.
     */
    uint16_t threshold_ppe_offset;

    /**
      The default_threshold element specifies the value of the flag's threshold
      selected in the ACE Configurator. It is the ADC value for which the flag
      would be raised if hysteresis was not applied.
     */
    uint16_t default_threshold;
    
    /**
      The flag_properties takes a different meaning depending whether the flag is
      an hysteresis flag or a state filtered flag.
      
      Hysteresis flags:
        The flag_properties element specifies the ADC value to be applied as
        hysteresis to the threshold value that was selected in the ACE Configurator.
        A non-zero value indicates that an hysteresis must be applied and that
        threshold_ppe_offset refers to the first of the two ADC values defining
        the hysteresis applied to the input signal.
      
      State filtered flags:
        The flag_properties element specifies the number of consecutive samples that
        must be over or under the threshold value for the flag state to change.
     */
    uint16_t flag_properties;
    
    /**
      The channel_handle element specifies the monitored analog input channel.
      It can be used as parameter to a call to function ACE_get_ppe_sample() in
      order to read the current value of the analog input channel which caused
      the flag described by this structure to be raised.
     */
    ace_channel_handle_t channel_handle;
   
} ppe_flag_desc_t;

/*-------------------------------------------------------------------------*//**
  The ace_procedure_desc_t structure is used as a procedure descriptor. It
  contains all information required by the ACE driver to use and manage an ACE
  procedure that was created using the ACE Configurator software tool.
 */
typedef struct
{
    /**
      Pointer to a zero-terminated string identifying an ACE procedure.
      This procedure name is the one selected when created procedures using the
      ACE Configurator software tool.
     */
    const uint8_t * p_sz_proc_name;
    
    /**
      Sample Sequencing Engine procedure loop start program counter value.
     */
    uint16_t sse_loop_pc;
    
    /**
      Sample Sequencing Engine microcode offset.
      This is the 16-bit instruction offset from which the SSE microcode for the
      procedure must be loaded at into the ACE SSE RAM.
      This is also the value that must be writtent into one of the ACE's SSE program
      counter registers in order to start the procedure after having loaded its
      microcode into SSE RAM. The actual program counter register written depends
      on the analog module used by the procedure. It is determined by the value
      of this structure's sse_pc_id element.
     */
    uint16_t sse_load_offset;
    
    /**
      Sample Sequencing Engine microcode length.
      This is the number of 16-bit SSE instructions that must be loaded into
      SSE RAM in order to load the procedure into the ACE.
     */
    uint16_t sse_ucode_length;
    
    /**
      Pointer to ucode.
     */
    const uint16_t * sse_ucode;
    
    /**
      SSE program counter ID.
      This value identifies whether the procedure is used to control analog
      module 0, 1 or 2. It is used to know which SSE program counter should
      be set when starting the procedure.
     */
    uint8_t sse_pc_id;
} ace_procedure_desc_t;

/*-------------------------------------------------------------------------*//**
  The ace_channel_desc_t structure is used as an analog input  channel
  descriptor. It contains the name of a channel as selected in the ACE
  Configurator software tool and the identifier used to identify the ADC channel
  to which the analog input signal is connected.
 */
typedef struct
{
    /**
      Analog input signal name as selected in the ACE Configurator software tool.
     */
    const uint8_t * p_sz_channel_name;
    
    /**
      Analog block input channel connected to the input signal.
     */
    adc_channel_id_t signal_id;
    
    /**
      Offset into Post Processing Engine RAM where the result of post processing
      on sample for the signal will be stored.
     */
    uint16_t signal_ppe_offset;
     
    /**
      Number of PPE generated flags associated with the analog input channel
      described by this structure. The nb_of_flags specifies the number of items
      found in the p_flags_array array.
     */
    uint16_t nb_of_flags;
    
    /**
      The p_flags_array element is a pointer to an array of indexes into the
      g_ppe_flags_desc_table flag descriptors table. The array it points to
      lists the flags generated base don the value of the analog input channel
      described by this structure.
     */
    const uint16_t * p_flags_array;
    
} ace_channel_desc_t;

/*-------------------------------------------------------------------------*//**
  struct ace_config_desc_t
  The ace_config_descr_t structure is used to provide information about the
  configuration of the ACE and analog block. A single instance of this structure
  is intended to be used to inform the ACE driver of the ACE configuration
  seleted using the ACE Configurator software tool and programmed into the ACE
  hardware at system boot time.
 */
typedef struct
{
    /*--------------------------------------------------------------------------
     * Procedures information
     */
    /**
      Procedure descriptors table location.
      This is a pointer to an array of procedure descriptors.
      @see nb_of_procedures
     */
    ace_procedure_desc_t * proc_descr_table;
    
    /**
      Total number of available procedures. This indicates the number of elements
      of the procedure descriptor array.
      @see proc_descr_table
     */
    uint16_t nb_of_procedures;
    
    /**
      Number of procedures loaded into the ACE hardware at system boot time.
      @see boot_loaded_proc_idx_list
     */
    uint16_t nb_boot_loaded_proc;
    /**
      Pointer to list of procedures loaded into the ACE hardware at system boot
      time. That list contains the indexes into the procedure descriptors array
      of the procedures loaded into the ACE hardware.
      @see nb_boot_loaded_proc
     */
    uint16_t * boot_loaded_proc_idx_list;
    
    /*--------------------------------------------------------------------------
     * Analog to Digital Converter signals
     */
    /**
      Total number of configured analog input signals.
      This is the number of analog input signals that were added to the ACE
      configuration using the ACE Configurator software tool. It is also the
      number of elements in the signal descriptor table pointed to by this
      structure's signals_descr_table field.
      @see signals_descr_table
     */
    uint16_t nb_of_signals;
    
    /**
      Signal descriptors table location.
      This is a pointer to an array of signal descriptors describing every
      configured analog input signals.
      @see nb_of_signals
     */
    ace_channel_desc_t * signals_descr_table;
    
    /*--------------------------------------------------------------------------
     * One Bit DACs
     */
    /**
      One Bit DAC (OBD) names as specified in ACE configurator software tool.
      This array is indexed on the analog block number. i.e. sz_obd_names[0]
      contains the name used to identify the OBD contained in analog module 0.
      A value of 0 in this array indicates that no name was assigned to the
      associated OBD.
     */
    const uint8_t * sz_obd_names[3];
    
    /*--------------------------------------------------------------------------
     * PPE generated flags
     */
    /**
      Flag descriptors array location.
      This is a pointer to an array of ppe_flag_desc_t structures describing the
      properties of each of the flags generated by the Post Processing Engine.
      The size of that array is specified by the nb_of_flags element of this
      structure.
     */
    ppe_flag_desc_t * flags_descr_table;

    /**
      Number of flags used in the ACE Configurator generated configuration.
     */
    uint8_t nb_of_flags;
    
    /*--------------------------------------------------------------------------
     * Analog comparators
     */
    /**
     *
     */
} ace_config_desc_t;


/*-------------------------------------------------------------------------*//**
  The ace_adc_config_t data structure is used by the ACE configurator to inform
  the ACE driver of an analog to digital converter's configuration.
 */
typedef struct
{
    /**
      ADC resolution. Values can be 256, 1024 or 4096 depending whether the ADC
      is configured for 8, 10 or 12 bits.
     */
    uint16_t adc_resolution;
    
    /**
      VA_REF value in milli-Volts. This should be set to 2560 if internal VAREF
      is used.
     */
    uint16_t va_ref;
    
} ace_adc_config_t;

/*-------------------------------------------------------------------------*//**
  The ppe_transforms_desc_t data structure is used by the ACE configurator to
  inform the ACE driver of the location of the "m" factor and "c" offset used
  by the PPE to perform a linear transform of the form y = m*x + c. This linear
  transform is used to apply calibration to the ADC samples. It can also include
  a user defined linear transform specified by the user using the ACE
  configurator. The factor and offset of the user defined transform is included
  in the default_m2 and default_c2 items. 
 */
typedef struct
{
    /**
      Offset into Post Processing Engine RAM where the linear transform m factor
      is stored.
     */
    uint16_t    m_ppe_offset;
    
    /**
      Offset into Post Processing Engine RAM where the linear transform c offset
      is stored.
     */
    uint16_t    c_ppe_offset;
    
    /**
      Default value of the user defined linear transform m2 factor.
     */
    int16_t     default_m2;
    
    /**
      Default value of the user defined linear transform c2 offset.
     */
    int16_t     default_c2;
} ppe_transforms_desc_t;

#ifdef __cplusplus
}
#endif

#endif  /* __MSS_ACE_CONFIGURATOR_H_ */
