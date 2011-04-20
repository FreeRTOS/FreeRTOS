/*******************************************************************************
 * (c) Copyright 2009 Actel Corporation.  All rights reserved.
 * 
 * SmartFusion ACE driver public API.
 *
 * SVN $Revision: 2884 $
 * SVN $Date: 2010-08-13 16:16:59 +0100 (Fri, 13 Aug 2010) $
 */

/*=========================================================================*//**
  @mainpage SmartFusion Analog Compute Engine driver public API.

  @section intro_sec Introduction
  The SmartFusion™ microcontroller subsystem (MSS) includes the Analog Compute
  Engine (ACE) which provides access to the analog capabilities of SmartFusion
  from the Cortex™-M3 microcontroller. This driver provides a set of functions
  for controlling the MSS ACE as part of a bare metal system where no operating
  system is available. These drivers can be adapted for use as part of an
  operating system, but the implementation of the adaptation layer between this
  driver and the operating system's driver model is outside the scope of this
  driver. The ACE includes:
    • A Sample Sequencing Engine (SSE) controlling the  operations of up to
      three analog to digital converters (ADC)
    • A Post Processing Engine (PPE) processing the analog inputs samples
      generated as a result of the SSE operations
    • An interface for controlling Sigma Delta DACs (SDD)
    • An interface for controlling high speed comparators

  The Sample Sequencing Engine controls the sampling of the various analog
  inputs based on a predefined sampling sequence without requiring intervention
  from the Cortex-M3. The sampling sequence is defined using the ACE Configurator
  provided as part of the MSS Configurator software tool.
  Available analog inputs are:
    • Active bipolar prescaler inputs (ABPS) allowing to measure voltages within
      four possible ranges:
        o -15V to +15V
        o -10V to +10V
        o -5V to +5V
        o -2.5V to +2.5V
    • Current inputs
    • Temperature inputs
    • Direct ADC inputs allowing to measure a voltage between zero volts and
      the ADC’s reference voltage (VAREF)
  Please refer to the Analog Front End section of the SmartFusion datasheet for
  further details about analog inputs.

  The Post Processing Engine can perform the following operations on the analog
  input samples generated as a result of the SSE operations:
    • Calibration adjustment
    • Averaging
    • Threshold detection
    • DMA transfer of most recent sample result to RAM or FPGA fabric
  The result of analog input sampling is read from the PPE rather than directly
  from the ADC. This ensures more accurate sample results thought the factory
  calibration adjustment performed by the PPE.
  The PPE can be set to generate interrupts when specific threshold values are
  reached on analog inputs through the ACE Configurator software tool. These
  thresholds can also be dynamically adjusted through the ACE driver.

  The ACE provides an interface to the Sigma Delta DACs included within the
  Analog Front End (AFE). This interface allows control of the DAC’s output
  value. Dynamic configuration of the DAC is also possible.

  The ACE provides an interface to the high speed comparators included within
  the Analog Front End. This interface allows dynamic configuration of the
  comparators and controlling interrupts based on the comparators’ state.

  @section theory_op Theory of Operation
  The configuration of the ACE is set though the use of the ACE Configurator
  included in the SmartFusion MSS Configurator software tool provided as part of
  the Libero Integrated Design Environment tool suite. The ACE Configurator
  offers an easy to use graphical method of selecting the configuration of the
  following ACE characteristics:
    • Analog input channels configuration
    • ADC configuration
    • Analog input channels sampling sequence
    • Filtering applied to analog input samples
    • Threshold flags configuration including hysteresis or state filtering properties
    • Selection of post processing results transferred though DMA
    • Sigma Delta DACs configuration
    • Analog comparators configuration
  The selected configuration hardware settings, SSE microcode and PPE microcode
  are stored in the SmartFusion eNVM. This configuration data is used by the
  system boot to configure the ACE after the system come out of reset and before
  control is passed to the application. This results in the ACE being fully
  operational by the time the application starts executing.
  The ACE Configurator also generates a set of C files containing information
  about the ACE’s configuration. These C files must be copied into the
  drivers_config/mss_ace folder of you r software project for consumption by the
  ACE driver. The ACE driver uses the content of these configuration files to
  interact with the configured ACE hardware.

  The ACE driver functions are grouped into the following categories:
    • Initialization
    • Reading analog input channels values and properties
    • Post Processing Engine flags
    • Conversion functions between sample value and real world units
    • Sample Sequencing Engine control
    • Sample Sequencing Engine Interrupts Control
    • Comparators control
    • Sigma Delta Digital to Analog Converters (SDD) control
    • Direct analog block configuration and usage

    
  Initialization
    The ACE driver is initialized through a call to the ACE_init() function. The
    ACE_init() function must be called before any other ACE driver functions can
    be called. It initializes the ACE’s internal data.

    
  Reading analog input channels values and properties
    The ACE driver allows retrieving the most recent post processed sample value
    for each analog input. It also allows retrieving the name of the analog input
    channel assigned in the ACE Configurator and whether the input channel samples
    a voltage, current or temperature.
    Each individual analog input channel is identified using a channel handle which
    is passed as parameter to the ACE input channel driver functions. The channel
    handles are design specific. The list of channel handles is generated by the
    ACE Configurator based on the names given to the input signals. The channel
    handles can be found in the drivers_config\mss_ace\ace_handles.h file.  The
    channel handle can be obtained from the channel name using the ACE_get_channel_handle()
    function. It is also possible to iterate through all the channels using the
    ACE_get_first_channel() and ACE_get_next_channel() functions.

    Reading analog input samples from the post processing engine is done the following function:
        • uint16_t ACE_get_ppe_sample( ace_channel_handle_t channel_handle )

    Information about an input channel can be retrieved using the following functions:
        • const uint8_t * ACE_get_channel_name( ace_channel_handle_t channel_handle )
        • channel_type_t ACE_get_channel_type( ace_channel_handle_t channel_handle )

        
  Post Processing Engine flags
    The SmartFusion ACE Post Processing Engine (PPE) provides the ability to monitor
    the state of analog input channels and detect when certain threshold values are
    crossed. Flags are raised by the PPE when these thresholds are crossed. Interrupts
    can optionally be generated when flags are raised.
    The flags are defined using the ACE Configurator software tool. The flag’s name,
    threshold value and hysteresis settings are specified in the ACE Configurator.
    The ACE Configurator generates microcode based on the selected configuration which
    is executed at system run time by the PPE. The PPE microcode is loaded into the
    ACE at chip boot time by the Actel provided system boot code. No ACE driver
    intervention is required to load up the PPE microcode.
    The ACE driver allows:
        • Retrieving the current state of the post processing engine flags
        • Assigning a handler function to individual flag assertions
        • Assigning a handler function to flags generated based on the value of a
          specific channel
        • Controlling flag interrupts
        • Dynamically modify a flag’s threshold value
        • Dynamically modify a flag’s hysteresis

    Each individual flag is identified using a flag handle which is passed as parameter
    to the ACE driver functions controlling the flags. The flag handles are design
    specific. They are defined in the drivers_config\mss_ace\ace_handles.h file which
    is generated by the ACE Configurator based on the names selected for the signal
    and flag names. A flag handle can be obtained from the driver using the name of
    the flag entered in the ACE Configurator software when the flag was created. A
    flag handle can also be obtained using the functions ACE_get_channel_first_flag()
    and ACE_get_channel_next_flag() when iterating through the flags associated with
    an analog input channel.  The functions available for retrieving flag handles are:
        • ace_flag_handle_t ACE_get_flag_handle (const uint8_t *p_sz_full_flag_name)
        • ace_flag_handle_t ACE_get_channel_first_flag (ace_channel_handle_t channel_handle, uint16_t *iterator)
        • ace_flag_handle_t ACE_get_channel_next_flag (ace_channel_handle_t channel_handle, uint16_t *iterator)
     
    The current status of a flag can be polled using the following function:
        • int32_t ACE_get_flag_status (ace_flag_handle_t flag_handle)

    Interrupt handlers can be registered with the ACE driver to handle individual
    flags. These interrupt handlers will be called by the ACE driver when a specific
    flag is raised. The flag interrupt control functions are:
        • void ACE_register_flag_isr (ace_flag_handle_t flag_handle, flag_isr_t flag_isr)
        • void ACE_enable_flag_irq (ace_flag_handle_t flag_handle)
        • void ACE_disable_flag_irq (ace_flag_handle_t flag_handle)
        • void ACE_clear_flag_irq (ace_flag_handle_t flag_handle)

    Interrupt handlers can be registered with the ACE driver to handle all flags
    associated with one specific analog input channel. These interrupt handlers will
    be called by the ACE driver when one of the flags, generated based on the state of
    the specified analog input channel, is raised. The channel flag interrupt control
    functions are:
        • void ACE_register_channel_flags_isr (ace_channel_handle_t channel_handle, channel_flag_isr_t channel_flag_isr)
        • void ACE_enable_channel_flags_irq (ace_channel_handle_t channel_handle)
        • void ACE_disable_channel_flags_irq (ace_channel_handle_t channel_handle)
        • void ACE_clear_channel_flags_irq (ace_channel_handle_t channel_handle)

    A single global interrupt handler can be registered with the ACE driver. The global
    flag interrupt handler function will be called by the ACE driver when any of the
    interrupt enabled flag is raised. The handle of the flag causing the interrupt and
    the handle of the associated analog input channel is passed as parameter to the
    registered global flag handler.
        • void ACE_register_global_flags_isr (global_flag_isr_t global_flag_isr)

    The configuration of a flag can be dynamically modified using the following functions:
        • void ACE_set_flag_threshold (ace_flag_handle_t flag_handle, uint16_t new_threshold)
        • void ACE_set_flag_hysteresis (ace_flag_handle_t flag_handle, uint16_t adc_hysteresis)
        • void ACE_set_channel_hysteresis (ace_channel_handle_t channel_handle, uint16_t adc_hysteresis)
        • void ACE_set_flag_assertion( ace_flag_handle_t   flag_handle, uint16_t assertion_value )
        • void ACE_set_flag_deassertion( ace_flag_handle_t   flag_handle, uint16_t assertion_value )

    Information about a flag can be retrieved using the following functions once
    the flag handle is known:
        • const uint8_t * ACE_get_flag_name (ace_flag_handle_t flag_handle)
        • ace_channel_handle_t ACE_get_flag_channel (ace_flag_handle_t flag_handle)

        
  Conversion to and from real world units
    The ACE driver provides a set of conversion functions to convert sample values
    read from the post processing engine into real world units:
        • millivolts
        • milliamps
        • Degrees Kelvin
        • Degrees Celsius
        • Degrees Fahrenheit
    Conversion functions are also available to convert from real world units into
    PPE sample values. These functions are typically used for dynamically adjusting
    flags threshold values.

    
  Sample Sequencing Engine control
    The ACE driver provides a set of functions for dynamically controlling the
    Sample Sequencing Engine. These functions are only required for managing multiple
    sampling sequences. The use of these functions is not required for most applications
    since the SSE is already configured and running by the time the application starts.

    
  Sample Sequencing Engine Interrupts Control
    The ACE driver provides a set of functions for managing interrupts generated by
    the Sample Sequencing Engine. These functions allow enabling, disabling and clearing
    interrupt defined as part of the sampling sequence. These functions also allow
    controlling interrupts generated by the ADCs.

    
  Comparators control
    The ACE driver provides a set of functions for managing interrupts generated based
    on the change of state of the high speed comparators. Functions are also provided
    to dynamically modify the comparators configuration.

    
  Sigma Delta Digital to Analog Converters (SDD) control
    The ACE driver provides functions for controlling the output value of the Sigma
    Delta DACs (SDD). Functions are also provided for dynamically adjusting the
    configuration of the SDDs.

 *//*=========================================================================*/
#ifndef __MSS_ACE_H_
#define __MSS_ACE_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif 

#include "../../drivers_config/mss_ace/ace_handles.h"

/*-------------------------------------------------------------------------*//**
  Analog to Digital Converter channel IDs.
  This enumeration is used to identify the ADC's analog inputs. It caters for up
  to three ADCs/Analog Modules as can be found on the larger parts of the
  SmartFusion family. The channel ID numbering is designed to allow easy
  extraction of the ADC number and also the individual ADC input number by simple
  shifting and masking. This enumeration is used as parameter to the
  ACE_get_input_channel_handle() function retrieving the channel handle associated
  with a specific analog input signal.
 */
typedef enum
{
    ADC0_1P5V = 0,        /*!< Analog Module 0, 1.5V/GND */
    ABPS0 = 1,            /*!< Analog Module 0, Quad0 Active Bipolar Pre-Scaler input 1 */
    ABPS1 = 2,            /*!< Analog Module 0, Quad0 Active Bipolar Pre-Scaler input 2 */
    CM0 = 3,              /*!< Analog Module 0, Quad0 Current Monitor Block */
    TM0 = 4,              /*!< Analog Module 0, Quad0 Temperature Monitor Block */
    ABPS2 = 5,            /*!< Analog Module 0, Quad1 Active Bipolar Pre-Scaler input 1 */
    ABPS3 = 6,            /*!< Analog Module 0, Quad1 Active Bipolar Pre-Scaler input 2 */
    CM1 = 7,              /*!< Analog Module 0, Quad1 Current Monitor Block */
    TM1 = 8,              /*!< Analog Module 0, Quad1 Temperature Monitor Block */
    ADC0 = 9,             /*!< Analog Module 0 Direct Input 0 */
    ADC1 = 10,            /*!< Analog Module 0 Direct Input 1 */
    ADC2 = 11,            /*!< Analog Module 0 Direct Input 2 */
    ADC3 = 12,            /*!< Analog Module 0 Direct Input 3 */
    SDD0_IN = 15,         /*!< Analog Module 0 Sigma-Delta DAC output */

    ADC1_1P5V = 16,       /*!< Analog Module 1, 1.5V/GND */
    ABPS4 = 17,           /*!< Analog Module 1, Quad0 Active Bipolar Pre-Scaler input 1 */
    ABPS5 = 18,           /*!< Analog Module 1, Quad0 Active Bipolar Pre-Scaler input 2 */
    CM2 = 19,             /*!< Analog Module 1, Quad0 Current Monitor Block */
    TM2 = 20,             /*!< Analog Module 1, Quad0 Temperature Monitor Block */
    ABPS6 = 21,           /*!< Analog Module 1, Quad1 Active Bipolar Pre-Scaler input 1 */
    ABPS7 = 22,           /*!< Analog Module 1, Quad1 Active Bipolar Pre-Scaler input 2 */
    CM3 = 23,             /*!< Analog Module 1, Quad1 Current Monitor Block */
    TM3 = 24,             /*!< Analog Module 1, Quad1 Temperature Monitor Block */
    ADC4 = 25,            /*!< Analog Module 1 Direct Input 0 */
    ADC5 = 26,            /*!< Analog Module 1 Direct Input 1 */
    ADC6 = 27,            /*!< Analog Module 1 Direct Input 2 */
    ADC7 = 28,            /*!< Analog Module 1 Direct Input 3 */
    SDD1_IN = 31,         /*!< Analog Module 1 Sigma-Delta DAC output */

    ADC2_1P5V = 32,       /*!< Analog Module 2, 1.5V/GND */
    ABPS8 = 33,           /*!< Analog Module 2, Quad0 Active Bipolar Pre-Scaler input 1 */
    ABPS9 = 34,           /*!< Analog Module 2, Quad0 Active Bipolar Pre-Scaler input 2 */
    CM4 = 35,             /*!< Analog Module 2, Quad0 Current Monitor Block */
    TM4 = 36,             /*!< Analog Module 2, Quad0 Temperature Monitor Block */
    ABPS10 = 37,          /*!< Analog Module 2, Quad1 Active Bipolar Pre-Scaler input 1 */
    ABPS11 = 38,          /*!< Analog Module 2, Quad1 Active Bipolar Pre-Scaler input 2 */
    CM5 = 39,             /*!< Analog Module 2, Quad1 Current Monitor Block */
    TM5 = 40,             /*!< Analog Module 2, Quad1 Temperature Monitor Block */
    ADC8 = 41,            /*!< Analog Module 2 Direct Input 0 */
    ADC9 = 42,            /*!< Analog Module 2 Direct Input 1 */
    ADC10 = 43,           /*!< Analog Module 2 Direct Input 2 */
    ADC11 = 44,           /*!< Analog Module 2 Direct Input 3 */
    SDD2_IN = 47,         /*!< Analog Module 2 Sigma-Delta DAC output */
    INVALID_CHANNEL = 255 /*!< Used to indicate errors */
} adc_channel_id_t;


/*-------------------------------------------------------------------------*//**
  The ACE_init() function initializes the SmartFusion MSS ACE driver. It
  initializes the ACE driver’s internal data structures. The ACE_init() function
  must be called before any other MSS ACE driver functions can be called.
 */
void ACE_init( void );


/*==============================================================================
 ============== Direct Analog Block Configuration and Usage ====================
 =============================================================================*/
 
/*=========================================================================*//**
  @defgroup group1 Direct Analog Block Configuration and Usage
  These functions are intended for using the SmartFusion analog block hardware
  without relying on the Sampling Sequence Engine or Post Processing engine.
  @{
 *//*=========================================================================*/

/*-------------------------------------------------------------------------*//**
  The ACE_start_adc() function initiates the sampling of the analog input
  channel identified by the channel_id parameter. This function is provided for
  test purposes. It must not be used while the Sample Sequencing Engine is
  running.
  
  @param channel_id
    The channel_id parameter identifies the analog input channel to sample.
    
  @return
    This function does not return a value.
 */
void ACE_start_adc
(
	adc_channel_id_t channel_id
);

/*-------------------------------------------------------------------------*//**
  The ACE_get_adc_result () function reads the result of the last input channel
  sampling performed by the ADC identified as parameter.
  
  @param adc_id
    The adc_id parameter identifies which of the possible three ADC to read the
    sample result from.
    
  @return
    The ACE_start_adc_sync() function returns the ADC result from the ADC
    specified as parameter.
 */
uint16_t ACE_get_adc_result
(
    uint8_t adc_id
);

/** @} */

/*==============================================================================
 =========== Sigma Delta Digital to Analog Converters (SDD) Control ============
 =============================================================================*/
/*=========================================================================*//**
  @defgroup group2 Sigma Delta Digital to Analog Converters (SDD) Control
  The following functions are used to control the Sigma Delta DACs included
  within the SmartFusion analog block.
  @{
 *//*=========================================================================*/

/*-------------------------------------------------------------------------*//**
  The sdd_id_t enumeration is used to identify the Sigma Delta DACs to the SDD
  control functions, ACE_configure_sdd(), ACE_enable_sdd(), ACE_disable_sdd()
  and ACE_set_sdd_value(). There is one SDD per analog module. 
 */
typedef enum
{
    SDD0_OUT = 0,    /*!< Analog Module 0 Sigma Delta DAC */
    SDD1_OUT = 1,    /*!< Analog Module 1 Sigma Delta DAC */
    SDD2_OUT = 2,    /*!< Analog Module 2 Sigma Delta DAC */
    NB_OF_SDD = 3
} sdd_id_t;

/*-------------------------------------------------------------------------*//**
  The sdd_resolution_t enumeration is used as a parameter to the
  ACE_configure_sdd() function to specify DAC resolution of the Sigma Delta DAC. 
 */
typedef enum
{
    SDD_8_BITS = 0,
    SDD_16_BITS = 4,
    SDD_24_BITS = 8
} sdd_resolution_t;

/*-------------------------------------------------------------------------*//**
  These constant definitions are used as an argument to the ACE_configure_sdd()
  function to specify operating mode of the Sigma Delta DAC.
 */
#define SDD_CURRENT_MODE    1
#define SDD_VOLTAGE_MODE    0
#define SDD_RETURN_TO_ZERO  0
#define SDD_NON_RTZ         2

/*-------------------------------------------------------------------------*//**
  The sdd_update_method_t enumeration is used as a parameter to the
  ACE_configure_sdd() function to specify individual or synchronous updating of
  the Sigma Delta DACs.
 */
typedef enum
{
    INDIVIDUAL_UPDATE = 0,
    SYNC_UPDATE = 1
} sdd_update_method_t;

/*-------------------------------------------------------------------------*//**
  The ACE_configure_sdd() function is used to configure the operating mode of
  the Sigma Delta DAC (SDD) specified as parameter. It allows selecting whether the
  SDD will output a voltage or a current. A current between 0 and 256uA is
  generated in current mode. A voltage between 0 and 2.56V is generated in
  voltage mode.
  This function also allows selecting whether Return To Zero (RTZ) mode is
  enabled or not. Enabling Return To Zero mode improves linearity of the SDD
  output at the detriment of accuracy. This mode should be used if linearity is
  more important than accuracy.
  A call to this function is not required if relying on the configuration
  selected in the ACE configurator being loaded after reset by the system boot.
  
  @param sdd_id
    The sdd_id parameter specifies which Sigma Delta DAC is configured by this
    function. Allowed values are:
        - SDD0_OUT
        - SDD1_OUT
        - SDD2_OUT
  
  @param resolution
    The resolution parameter specifies the desired resolution of the Sigma Delta DAC.
    Allowed values are:
        - SDD_8_BITS
        - SDD_16_BITS
        - SDD_24_BITS
  
  @param mode
    The mode parameter specifies the operating mode of the Sigma Delta DAC. It
    specifies whether a current or voltage should be generated and whether
    Return to Zero mode should be used. It is a logical OR of the following
    defines:
        - SDD_CURRENT_MODE
        - SDD_VOLTAGE_MODE
        - SDD_RETURN_TO_ZERO
        - SDD_NON_RTZ
  
  @param sync_update
    The sync_update parameter specifies whether the SDD output will be updated
    individually though a call to ACE_set_sdd_value() or synchronously with one
    or more other SDD outputs via a call to ACE_set_sdd_value_sync().

  Example
  @code
    ACE_configure_sdd
    (
        SDD1_OUT,
        SDD_24_BITS,
        SDD_VOLTAGE_MODE | SDD_RETURN_TO_ZERO,
        INDIVIDUAL_UPDATE
    );
  @endcode
 */
void ACE_configure_sdd
(
	sdd_id_t            sdd_id,
	sdd_resolution_t    resolution,
    uint8_t             mode,
    sdd_update_method_t sync_update
);

/*-------------------------------------------------------------------------*//**
  The ACE_enable_sdd() function is used to enable a Sigma Delta DAC. 
  
  @param sdd_id
    The sdd_id parameter specifies the Sigma Delta DAC to enable.
 */
void ACE_enable_sdd
(
	sdd_id_t    sdd_id
);

/*-------------------------------------------------------------------------*//**
  The ACE_disable_sdd() function is used to disable a Sigma Delta DAC.
  
  @param sdd_id
    The sdd_id parameter specifies the Sigma Delta DAC to disable.
 */
void ACE_disable_sdd
(
	sdd_id_t    sdd_id
);

/*-------------------------------------------------------------------------*//**
  The ACE_set_sdd_value() function is used to set the value of the output of
  a Sigma Delta DAC. It uses the ACE's phase accumulator to generate the one bit
  input bit stream into the SDD which will in turn define the voltage or
  current generated at the SDD output.
  The SDD output is proportional to the sdd_value passed to this function taking
  the SDD resolution into account. A maximum voltage of 2.56V or a maximum
  current of 256uA will be generated when the sdd_value is set the maximum value
  allowed by the SDD resolution
  
  @param sdd_id
    The sdd_id parameter specifies which Sigma Delta DAC is being set.
  
  @param sdd_value
    The sdd_value parameter specifies the value of the Sigma Delta DAC output.
    It is a fraction of SDD resolution. The voltage/current value generated from
    the sdd_value paramenter can be determined using the following equation where
    sdd_resolution is the resolution of the SDD as set through function
    ACE_configure_sdd() and sdd_rangSDD configuration:
        sdd_output = (sdd_value / sdd_resolution) * sdd_range
 */
void ACE_set_sdd_value
(
	sdd_id_t    sdd_id,
	uint32_t    sdd_value
);


/*-------------------------------------------------------------------------*//**
  This constant definition is used as an argument to the ACE_set_sdd_value_sync()
  function to specify that the output value of SDD0, or SDD1, or SDD2 should not
  be modified.
 */
#define SDD_NO_UPDATE   0xFFFFFFFF

/*-------------------------------------------------------------------------*//**
  The ACE_set_sdd_value_sync() function is used to synchronize the update of
  multiple Sigma Delta DAC outputs.

  @param sdd0_value
    The sdd0_value parameter specifies the value that will be used to set the
    output of SDD0.
    The define SDD_NO_UPDATE can be used to specify that the output value of
    SDD0 should not be modified.

  @param sdd1_value
    The sdd1_value parameter specifies the value that will be used to set the
    output of SDD1.
    The define SDD_NO_UPDATE can be used to specify that the output value of
    SDD1 should not be modified.

  @param sdd2_value
    The sdd2_value parameter specifies the value that will be used to set the
    output of SDD2.
    The define SDD_NO_UPDATE can be used to specify that the output value of
    SDD2 should not be modified.

  For example the code below will change the output value of SDD0 and SDD2 so
  that the voltage/current generate by SDD0 and ADD2 will change at the same
  time. This function call will not affect the output value of SDD1.
  @code
    uint32_t sdd0_value = 0x1234;
    uint32_t sdd2_value = 0x5678;
    ACE_set_sdd_value_sync( sdd0_value, SDD_NO_UPDATE, sdd2_value );
  @endcode
 */

void ACE_set_sdd_value_sync
(
    uint32_t sdd0_value,
    uint32_t sdd1_value,
    uint32_t sdd2_value
);

/** @} */

/*==============================================================================
 ============ Reading Samples from post processing engine (PPE) ================
 =============================================================================*/
/*=========================================================================*//**
  @defgroup group9 Reading Analog Input Channels Values and Properties
  The following functions are used to access analog input channels properties
  and sampled values.
  @{
 *//*=========================================================================*/

/*-------------------------------------------------------------------------*//**
  This constant returned by the ACE_get_flag_channel(), ACE_get_channel_handle()
  and ACE_get_input_channel_handle() functions when the driver can’t find a
  valid handle for the ADC input channel.
 */
#define INVALID_CHANNEL_HANDLE      NB_OF_ACE_CHANNEL_HANDLES

/*-------------------------------------------------------------------------*//**
  The ACE_get_channel_handle() function returns the channel handle associated
  with an analog input channel name. The retrieved channel handle will be
  subsequently used as parameter to function ACE_get_ppe_sample() used to read
  the most recent post processed sample for the analog input identified through
  the channel/service name passed as argument to this function.
  
  @param p_sz_channel_name
    The p_sz_channel_name parameter is a zero-terminated string containing the
    name of the channel/service as entered in the ACE configurator.
    
  @return
    This function returns a channel handle. This channel handle is required as
    parameter to function ACE_get_ppe_sample().
    It will return INVALID_CHANNEL_HANDLE if the channel/service name is not
    recognized.
    
  @code
    uint16_t adc_result;
    ace_channel_handle_t at0;
    at0 = ACE_get_channel_handle("VoltageMonitorAT0");
    adc_result = ACE_get_ppe_sample( at0 );
  @endcode
 */
ace_channel_handle_t
ACE_get_channel_handle
(
    const uint8_t * p_sz_channel_name
);

/*-------------------------------------------------------------------------*//**
  The ACE_get_input_channel_handle() function returns the channel handle for
  the hardware analog input channel specified as parameter.
  
  @param channel_id
    The channel_id parameter identifies a hardware analog input of the ACE.
  
  @return
    This function returns a channel handle. This channel handle is required as
    parameter to other ACE driver functions dealing with analog inputs.
    It will return INVALID_CHANNEL_HANDLE if the channel ID passed as parameter
    is invalid.
 */
ace_channel_handle_t
ACE_get_input_channel_handle
(
    adc_channel_id_t    channel_id
);

/*-------------------------------------------------------------------------*//**
  The ACE_get_ppe_sample() function is used to read the most recent post
  processed sample for the analog input channel associated with the channel
  handle passed as parameter.
  
  @param channel_handle
    The channel_handle parameter identifies the analog input channel for which
    this function will return the most recent ADC conversion result adjusted for
    calibration and user provided coefficients as provided through the ACE
    configurator. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
  
  @return
    This function returns a 16 bit value representing the adjusted value of the
    ADC conversion result for the analog input channel identified by the channel
    handle passed as parameter. The return value is actually a 12, 10 or 8 bits
    number depending on the configuration of the ADC.
    
  @code
    uint16_t adc_result;
    ace_channel_handle_t at0;
    at0 = ACE_get_channel_handle("VoltageMonitorAT0");
    adc_result = ACE_get_ppe_sample( at0 );
  @endcode
 */
uint16_t
ACE_get_ppe_sample
(
    ace_channel_handle_t channel_handle
);

/*-------------------------------------------------------------------------*//**
  The ACE_get_channel_name() function provides the name of the channel
  associated with the channel handle passed as parameter. The channel name is
  the name used in the ACE configurator software tool when adding a service to
  the ACE.
  
  @param channel_handle
    The channel_handle parameter identifies the analog input channel for which
    we want to retrieve the channel name. The available channel handle values can
    be found in the ace_handles.h file located in the ./drivers_config/mss_ace
    subdirectory. The channel handle value can also be retrieved through a call
    to ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @return
    This function returns a pointer to a zero-terminated string containing the
    name of the channel. It returns 0 if the channel handle passed as parameter
    is not recognized.
 */
const uint8_t * ACE_get_channel_name
(
    ace_channel_handle_t    channel_handle
);

/*-------------------------------------------------------------------------*//**
  The channel_type_t enumeration is used to identify the type of quantity
  measured by an analog input channel. It is typically used to figure out the
  type of conversion that must be applied to the ADC value generated from
  sampling a channel in order to yield real world units such millivolts,
  milliamps or degrees.
 */
typedef enum
{
    VOLTAGE,
    CURRENT,
    TEMPERATURE
} channel_type_t;

/*-------------------------------------------------------------------------*//**
  The ACE_get_channel_type() function returns the type of input channel of the
  analog input channel identified by the channel handle passed as parameter.
  This function allows determining whether the quantity measured through the ADC
  is a voltage, current or temperature.
  
  @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the .\drivers_config\mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
  
  @return
    This function returns one of the following values to report the type of
    quantity measure throught the channel:
        - VOLTAGE
        - CURRENT
        - TEMPERATURE
 */
channel_type_t
ACE_get_channel_type
(
    ace_channel_handle_t    channel_handle
);

/*-------------------------------------------------------------------------*//**
  The ACE_get_channel_count() function returns the total number of configured
  analog input channels. It is the number of channels available for use as
  opposed to the theorical number of physical channels supported by the device.
  
  @return
    The ACE_get_channel_count() function returns the total number of input
    channels that were configured in the ACE configurator.
    The ACE_get_channel_count() function returns 0 if no input channels were
    configured.
    
  @code
    uint32_t inc;
    uint32_t nb_of_channels;
    ace_channel_handle_t current_channel;
    
    nb_of_channels = ACE_get_channel_count();
    current_channel = ACE_get_first_channel();
    
    for (inc = 0; inc < nb_of_channels; ++inc)
    {
        adc_result = ACE_get_ppe_sample( current_channel );
        display_value( current_channel, adc_result );
        current_channel = ACE_get_next_channel( current_channel );
    }
  @endcode
 */
uint32_t
ACE_get_channel_count
(
    void
);

/*-------------------------------------------------------------------------*//**
  The ACE_get_first_channel() function returns the channel handle of one of the
  channel controlled by the ACE. This function is used to start iterating though
  the list of analog input channels handled by the ACE.
  
  @return
    The ACE_get_first_channel() function returns the first channel handle found
    in the ACE driver's internal channel handles list or INVALID_CHANNEL_HANDLE
    if there are no channels defined in the ACE configuration.
    
  @code
    uint32_t inc;
    uint32_t nb_of_channels;
    ace_channel_handle_t current_channel;
    
    nb_of_channels = ACE_get_channel_count();
    current_channel = ACE_get_first_channel();
    
    for (inc = 0; inc < nb_of_channels; ++inc)
    {
        adc_result = ACE_get_ppe_sample( current_channel );
        display_value( current_channel, adc_result );
        current_channel = ACE_get_next_channel( current_channel );
    }
  @endcode
 */
ace_channel_handle_t
ACE_get_first_channel
(
    void
);

/*-------------------------------------------------------------------------*//**
  The ACE_get_next_channel() returns the channel handle of the channel following
  the one passed as parameter. This function is used to iterate through the list
  of analog input channels handled by the ACE.
  
  @param channel_handle
    The channel_handle parameter identifies from which channel the driver should
    look in its channel handle list to return the next channel handle. The
    channel_handle parameter would typically be the channel handle returned by a
    call to ACE_get_first_channel() or a previous call to ACE_get_next_channel().
    Note:
      The first call to ACE_get_next_channel() would typically use the
      channel_handle returned by a previous call to ACE_get_first_channel(). The
      second and subsequent calls to ACE_get_next_channel() would typically use
      the channel_handle returned by a previous call to ACE_get_next_channel().
  
  @return
    The ACE_get_next_channel() function returns the channel handle of the channel
    following the one passed as parameter or INVALID_CHANNEL_HANDLE if the end of
    the channels list has been reached.
    
  @code
    uint32_t inc;
    uint32_t nb_of_channels;
    ace_channel_handle_t current_channel;
    
    nb_of_channels = ACE_get_channel_count();
    current_channel = ACE_get_first_channel();
    
    for (inc = 0; inc < nb_of_channels; ++inc)
    {
        adc_result = ACE_get_ppe_sample( current_channel );
        display_value( current_channel, adc_result );
        current_channel = ACE_get_next_channel( current_channel );
    }
  @endcode
 */
ace_channel_handle_t
ACE_get_next_channel
(
    ace_channel_handle_t channel_handle
);

 /** @} */

/*==============================================================================
 =============================== SSE Control ==================================
 =============================================================================*/
/*=========================================================================*//**
  @defgroup group3 Sample Sequencing Engine Control
  Sample Sequencing Engine control.
  @{
 *//*=========================================================================*/

/*-------------------------------------------------------------------------*//**
  The Sample Sequencing Engine control functions use a parameter of this type as
  a handle to identify the Sample Sequencing Engine (SSE) sequences configured
  using the ACE configurator. The ACE_get_sse_seq_handle() function retrieves the
  handle of the SSE sequence identified by the sequence name passed as parameter.
  Note: The ACE configurator generates ACE driver configuration files into the
        .\drivers_config\mss_ace folder of the firmware project. These files
        contain the details of the SSE sequence handles for your ACE configuration.
        The ACE driver automatically includes these files when the
        .\drivers_config\mss_ace folder is present in the firmware project.
 */
typedef uint16_t sse_sequence_handle_t;

/*-------------------------------------------------------------------------*//**
  This constant is returned by the ACE_get_sse_seq_handle() function when the
  driver can’t find a valid handle for the Sample Sequencing Engine (SSE) sequence.
*/
#define INVALID_SSE_SEQ_HANDLE      0xFFFFu

/*-------------------------------------------------------------------------*//**
  The ACE_get_sse_seq_handle() function retrieves the handle of the Sample
  Sequencing Engine sequence identified by the sequence name passed as parameter.
  The sequence handler can then be used as parameter to other SSE sequence control
  functions to identify the sequence to control.
  
  @param p_sz_sequence_name
    The p_sz_sequence_name parameter is a pointer to a zero-terminated string
    containing the name of the sampling sequence for which we want to retrieve
    the handle.
    
  @return
    The ACE_get_sse_seq_handle() function returns the handle used to identify
    the sequence passed as parameter with other ACE driver sampling sequence
    control functions. It returns INVALID_SSE_SEQ_HANDLE if the sequence name
    passed as parameter is not recognized.
    
  @code
    sse_sequence_handle_t sse_seq_handle;
    sse_seq_handle = ACE_get_sse_seq_handle("ProcedureA");
    if ( sse_seq_handle != INVALID_SSE_SEQ_HANDLE )
    {
        ACE_load_sse( sse_seq_handle );
        ACE_start_sse( sse_seq_handle );
    }
  @endcode
 */
sse_sequence_handle_t
ACE_get_sse_seq_handle
(
    const uint8_t * p_sz_sequence_name
);

/*-------------------------------------------------------------------------*//**
  The ACE_load_sse() function loads the ACE Sample Sequencing Engine (SSE) RAM
  with the microcode implementing the sampling sequence identified by the SSE
  sequence handler passed as parameter.
  
  @param sequence
    The sequence parameter is the SSE sequence handler identifying the sampling
    sequence to load into the ACE SSE. The value for this handler is retrieved
    through a call to function ACE_get_sse_seq_handle().
 */
void ACE_load_sse
(
    sse_sequence_handle_t  sequence
);

/*-------------------------------------------------------------------------*//**
  The ACE_start_sse() function causes the Sampling Sequence Engine (SSE) to start
  executing the sequence identified by the sequence handler passed as parameter.
  It causes the initiailization part of the sampling sequence to be executed
  before the loop part of the sequence is started.
  You must ensure that the sampling sequence has been loaded into the ACE's SSE
  before calling this function.
  
  @param sequence
    The sequence parameter is the SSE sequence handler identifying the sampling
    sequence to load into the ACE SSE. The value for this handler is retrieved
    through a call to function ACE_get_sse_seq_handle().
 */
void ACE_start_sse
(
    sse_sequence_handle_t  sequence
);

/*-------------------------------------------------------------------------*//**
  The ACE_restart_sse() function restarts the loop part of the sampling sequence
  loaded into the ACE's Sampling Sequence Engine (SSE). The sampling sequence
  will be restarted from the beginning of the sequence but omiting the
  intialization phase of the sequence.
  This function would typically be called after stopping the sampling sequence
  using the ACE_stop_see() function or with non-repeating sequences.
  
  @param sequence
    The sequence parameter is the SSE sequence handler identifying the sampling
    sequence to load into the ACE SSE. The value for this handler is retrieved
    through a call to function ACE_get_sse_seq_handle().
 */
void ACE_restart_sse
(
    sse_sequence_handle_t  sequence
);

/*-------------------------------------------------------------------------*//**
  The ACE_stop_sse() function stops execution of the Sample Sequencing Engine
  (SSE) sequence indentified by the sequence handle passed as parameter.
  
  @param sequence
    The sequence parameter is the SSE sequence handle identifying the sampling
    sequence to load into the ACE SSE. The value for this handler is retrieved
    through a call to function ACE_get_sse_seq_handle().
 */
void ACE_stop_sse
(
    sse_sequence_handle_t  sequence
);

/*-------------------------------------------------------------------------*//**
  The ACE_resume_sse() function causes the Sampling Sequencing Engine (SSE)
  sampling sequence identified by the sequence handle passed as parameter to
  resume execution. This function is typically used to restart execution of
  a sequence at the point where it was stopped through a call to ACE_stop_sse().
  
  @param sequence
    The sequence parameter is the SSE sequence handler identifying the sampling
    sequence to load into the ACE SSE. The value for this handler is retrieved
    through a call to function ACE_get_sse_seq_handle().
 */
void ACE_resume_sse
(
    sse_sequence_handle_t  sequence
);

/*-------------------------------------------------------------------------*//**
  The ACE_clear_sample_pipeline() function clears the ACE hardware of samples
  being processed. It clear the various stages involved in the production of
  post processed samples within the ACE hardware. It is intended for use when
  switching between sampling sequences and using peripheral DMA. It avoids
  receiving stale samples generated as a result of a previous sampling sequence.
  
  The example below shows how this function can be used to ensure that no sample
  generated as a result of sampling sequence sequence_a will be generated once
  sampling sequence_b is started. Please note that it is important to stop the
  SSE using function ACE_stop_sse() before calling ACE_clear_sample_pipeline()
  to ensure sequence_a is not restarted after the sample pipeline is cleared.
  @code
    ACE_stop_sse(sequence_a);
    ACE_clear_sample_pipeline();
    ACE_start_sse(sequence_b);
  @endcode
    
  The example below shows how to ensure that the first sample read through PDMA
  will be from the first channel in the sampling sequence.
  @code
    ACE_stop_sse(sequence_a);
    ACE_clear_sample_pipeline();
    ACE_restart_sse(sequence_a);
    PDMA_start
      (
        PDMA_CHANNEL_0, 
        PDMA_ACE_PPE_DATAOUT, 
        (uint32_t)g_samples_buffer[g_pdma_buffer_idx], 
        SAMPLES_BUFFER_SIZE
      );
  @endcode
 */
void ACE_clear_sample_pipeline(void);

/** @} */
/*==============================================================================
 ======================== SSE Interrupts Control ===============================
 =============================================================================*/
/*=========================================================================*//**
  @defgroup group4 Sample Sequencing Engine Interrupts Control
  The following functions are used to control interrupts generated from the
  ACE's Sample Sequencing Engine. These interrupts would typically be used to
  detect when valid data is available from the ADCs controlled by the SSE or to
  detect the complete or partial completion of the sampling sequence through the
  insertion of SSE program counter general purpose interrupt assertion as part
  of the sequence.
  @{
 *//*=========================================================================*/

/*-------------------------------------------------------------------------*//**
  The sse_irq_id_t enumeration is used to identify the Sample Sequencing Engine
  (SSE) interrupt sources to the SSE interrupt control functions.
 */
typedef enum
{
    PC0_FLAG0 = 0,
    PC0_FLAG1 = 1,
    PC0_FLAG2 = 2,
    PC0_FLAG3 = 3,
    PC1_FLAG0 = 4,
    PC1_FLAG1 = 5,
    PC1_FLAG2 = 6,
    PC1_FLAG3 = 7,
    PC2_FLAG0 = 8,
    PC2_FLAG1 = 9,
    PC2_FLAG2 = 10,
    PC2_FLAG3 = 11,
    ADC0_DATAVALID = 12,
    ADC1_DATAVALID = 13,
    ADC2_DATAVALID = 14,
    ADC0_CALIBRATION_COMPLETE = 15,
    ADC1_CALIBRATION_COMPLETE = 16,
    ADC2_CALIBRATION_COMPLETE = 17,
    ADC0_CALIBRATION_START = 18,
    ADC1_CALIBRATION_START = 19,
    ADC2_CALIBRATION_START = 20,
    NB_OF_SSE_FLAG_IRQS = 21
} sse_irq_id_t;

/*-------------------------------------------------------------------------*//**
  The ACE_enable_sse_irq() function enables the Sample Sequencing Engine (SSE)
  interrupt source specified as parameter to generate interrupts.
  
  @param sse_irq_id
    The sse_irq_id parameter identifies the SSE interrupt source controlled by
    this function.
 */
void ACE_enable_sse_irq
(
	sse_irq_id_t sse_irq_id
);

/*-------------------------------------------------------------------------*//**
  The ACE_disable_sse_irq() function disables the Sample Sequencing Engine
  (SSE) interrupt source specified as parameter from generating interrupts.
  
  @param sse_irq_id
    The sse_irq_id parameter identifies the SSE interrupt source controlled by
    this function.
 */
void ACE_disable_sse_irq
(
	sse_irq_id_t sse_irq_id
);

/*-------------------------------------------------------------------------*//**
  The ACE_clear_sse_irq() function clears the Sampling Sequencing Engine (SSE)
  interrupt specified as parameter.
  
  @param sse_irq_id
    The sse_irq_id parameter identifies the SSE interrupt source controlled by
    this function.
 */
void ACE_clear_sse_irq
(
	sse_irq_id_t sse_irq_id
);

/** @} */
/*==============================================================================
 ============================ Comparators Control ==============================
 =============================================================================*/
/*=========================================================================*//**
  @defgroup group5 Comparators Control
  The following functions are used to control the analog comparators included
  in the SmartFusion analog block.
  The comparator configuration functions can be used to directly configure the
  comparators. Their use is only required when the ACE is not configured using
  the ACE configurator software tool.
  The comparator interrupt control functions are used regardless of the way the
  ACE was configured to enable, disable and clear interrupts generated when the
  positive input of a comparator rises above or falls below the negative input.
  @{
 *//*=========================================================================*/

/*-------------------------------------------------------------------------*//**
  The comparator_id_t enumeration is used by the comparator control functions
  to identify the analog comparators included in the SmartFusion analog block.
 */
typedef enum
{
    CMP0 = 0,                   /*!< Analog module 0, Quad 0, CMB comparator */
    CMP1 = 1,                   /*!< Analog module 0, Quad 0, TMB comparator */
    CMP2 = 2,                   /*!< Analog module 0, Quad 1, CMB comparator */
    CMP3 = 3,                   /*!< Analog module 0, Quad 1, TMB comparator */
    CMP4 = 4,                   /*!< Analog module 1, Quad 0, CMB comparator */
    CMP5 = 5,                   /*!< Analog module 1, Quad 0, TMB comparator */
    CMP6 = 6,                   /*!< Analog module 1, Quad 1, CMB comparator */
    CMP7 = 7,                   /*!< Analog module 1, Quad 1, TMB comparator */
    CMP8 = 8,                   /*!< Analog module 2, Quad 0, CMB comparator */
    CMP9 = 9,                   /*!< Analog module 2, Quad 0, TMB comparator */
    CMP10 = 10,                 /*!< Analog module 2, Quad 1, CMB comparator */
    CMP11 = 11,                 /*!< Analog module 2, Quad 1, TMB comparator */
    NB_OF_COMPARATORS = 12
} comparator_id_t;

/*-------------------------------------------------------------------------*//**
  The comp_hysteresis_t enumeration is used by the ACE_set_comp_hysteresis()
  function to set the hysteresis of the analog comparators included in the
  SmartFusion analog block. This enumeration provides the allowed values of the
  hysteresis parameter of the ACE_set_comp_hysteresis() function.
 */
typedef enum
{
    NO_HYSTERESIS = 0,
    HYSTERESIS_10_MV = 1,
    HYSTERESIS_30_MV = 2,
    HYSTERESIS_100_MV = 3,
    NB_OF_HYSTERESIS = 4
} comp_hysteresis_t ;

/*-------------------------------------------------------------------------*//**
  The comp_reference_t enumeration is used by the ACE_set_comp_reference()
  function to select the reference input of the odd numbered analog comparators
  included in the SmartFusion analog block. This enumeration provides the allowed
  values of the reference parameter of the ACE_set_comp_reference () function.
 */
typedef enum
{
    SDD0_COMP_REF = 0,
    SDD1_COMP_REF = 1,
    SDD2_COMP_REF = 2,
    ADC_IN_COMP_REF = 3,
    NB_OF_COMP_REF = 4
} comp_reference_t;

/*-------------------------------------------------------------------------*//**
  The ACE_set_comp_reference() function is used to select the reference input
  of a temperature monitor block comparator. The reference input of a temperature
  monitor can be an ADC direct input or one of the SDD's output.
  
  @param comp_id
    The comp_id parameter specifies the comparator for which to select the
    reference input. Since only temperature monitor block comparators have a 
    selectable reference input, allowed values are:
        - CMP1
        - CMP3
        - CMP5
        - CMP7
        - CMP9
        - CMP11
    
  @param reference
    The reference parameter specify the signal that will be used as reference
    by the comparator. Allowed values are:
        - SDD0_COMP_REF
        - SDD1_COMP_REF
        - SDD2_COMP_REF
        - ADC_IN_COMP_REF
 */
void ACE_set_comp_reference
(
    comparator_id_t     comp_id,
    comp_reference_t    reference
);

/*-------------------------------------------------------------------------*//**
  The ACE_set_comp_hysteresis() function is used to set the hysteresis of a
  comparator. There are four possible hystereris settings: no hysteresis,
  +/-10mV, +/-30mV or +/-100mV.
  
  @param comp_id
    The comp_id parameter specifies the comparator for which this function will
    set the hyteresis.
  
  @param hysteresis
    The hysteresis parameter specifies the hysteresis that will be applied to 
    the comparator's input. Allowed values are:
        - NO_HYSTERESIS
        - HYSTERESIS_10_MV
        - HYSTERESIS_30_MV
        - HYSTERESIS_100_MV
  
 */
void ACE_set_comp_hysteresis
(
	comparator_id_t     comp_id,
    comp_hysteresis_t   hysteresis
);

/*-------------------------------------------------------------------------*//**
  The ACE_enable_comp() function is used to enable the comparator specified as
  parameter.
  
  @param comp_id
    The comp_id parameter specifies which comparator will be enabled by a call
    to this function.
 */
void ACE_enable_comp
(
	comparator_id_t comp_id
);

/*-------------------------------------------------------------------------*//**
  The ACE_disable_comp() function is used to disable the comparator specified as
  parameter.
  
  @param comp_id
    The comp_id parameter specifies which comparator will be disabled by a call
    to this function.
 */
void ACE_disable_comp
(
	comparator_id_t comp_id
);

/*-------------------------------------------------------------------------*//**
  The ACE_enable_comp_rise_irq() function is used to enable interrupts to be
  generated when the positive input of the comparator specified as parameter
  rises above the negative input of the comparator.
  The function prototypes for the comparator rise interrupt service routines are:
    - void ACE_Comp0_Rise_IRQHandler( void );
    - void ACE_Comp1_Rise_IRQHandler( void );
    - void ACE_Comp2_Rise_IRQHandler( void );
    - void ACE_Comp3_Rise_IRQHandler( void );
    - void ACE_Comp4_Rise_IRQHandler( void );
    - void ACE_Comp5_Rise_IRQHandler( void );
    - void ACE_Comp6_Rise_IRQHandler( void );
    - void ACE_Comp7_Rise_IRQHandler( void );
    - void ACE_Comp8_Rise_IRQHandler( void );
    - void ACE_Comp9_Rise_IRQHandler( void );
    - void ACE_Comp10_Rise_IRQHandler( void );
    - void ACE_Comp11_Rise_IRQHandler( void );
  
  @param comp_id
    The comp_id parameter specifies which comparator will be enabled to generate
    rising interrupts.
 */
void ACE_enable_comp_rise_irq
(
	comparator_id_t comp_id
);

/*-------------------------------------------------------------------------*//**
  The ACE_disable_comp_rise_irq() function is used to disable interrupts from
  being generated when the positive input of the comparator specified as parameter
  rises above the negative input of the comparator.
  
  @param comp_id
    The comp_id parameter specifies which comparator will be disabled from
    generating rising interrupts.
 */
void ACE_disable_comp_rise_irq
(
	comparator_id_t comp_id
);

/*-------------------------------------------------------------------------*//**
  The ACE_clear_comp_rise_irq() function is used to clear rise interrupts. This
  function is typically called as part of the rise interrupt service routine.
  
  @param comp_id
    The comp_id parameter specifies the comparator for which to clear the rise
    interrupt.
    
  Example:
  @code
    void ACE_Comp1_Rise_IRQHandler( void )
    {
        process_rise_irq();
        ACE_clear_comp_rise_irq( CMP1 );
        NVIC_ClearPendingIRQ( ACE_Comp1_Rise_IRQn );
    }
  @endcode
 */
void ACE_clear_comp_rise_irq
(
	comparator_id_t comp_id
);

/*-------------------------------------------------------------------------*//**
  The ACE_enable_comp_fall_irq() function is used to enable interrupts to be
  generated when the positive input of the comparator specified as parameter
  falls below the negative input of the comparator.
  The function prototypes for the comparator fall interrupt service routines are:
    - void ACE_Comp0_Fall_IRQHandler( void );
    - void ACE_Comp1_Fall_IRQHandler( void );
    - void ACE_Comp2_Fall_IRQHandler( void );
    - void ACE_Comp3_Fall_IRQHandler( void );
    - void ACE_Comp4_Fall_IRQHandler( void );
    - void ACE_Comp5_Fall_IRQHandler( void );
    - void ACE_Comp6_Fall_IRQHandler( void );
    - void ACE_Comp7_Fall_IRQHandler( void );
    - void ACE_Comp8_Fall_IRQHandler( void );
    - void ACE_Comp9_Fall_IRQHandler( void );
    - void ACE_Comp10_Fall_IRQHandler( void );
    - void ACE_Comp11_Fall_IRQHandler( void );
  
  @param comp_id
    The comp_id parameter specifies which comparator will be enabled to generate
    fall interrupts.
 */
void ACE_enable_comp_fall_irq
(
	comparator_id_t comp_id
);

/*-------------------------------------------------------------------------*//**
  The ACE_disable_comp_fall_irq() function is used to disable interrupts from
  being generated when the positive input of the comparator specified as parameter
  falls below the negative input of the comparator.
  
  @param comp_id
    The comp_id parameter specifies which comparator will be disabled from
    generating fall interrupts.
 */
void ACE_disable_comp_fall_irq
(
	comparator_id_t comp_id
);

/*-------------------------------------------------------------------------*//**
  The ACE_clear_comp_fall_irq() function is used to clear fall interrupts. This
  function is typically called as part of the fall interrupt service routine.
  
  @param comp_id
    The comp_id parameter specifies the comparator for which to clear the fall
    interrupt.
    
  Example:
  @code
    void ACE_Comp1_Fall_IRQHandler( void )
    {
        process_fall_irq();
        ACE_clear_comp_fall_irq( CMP1 );
        NVIC_ClearPendingIRQ( ACE_Comp1_Fall_IRQn );
    }
  @endcode
 */
void ACE_clear_comp_fall_irq
(
	comparator_id_t comp_id
);

/*-------------------------------------------------------------------------*//**
  The ACE_get_comp_status() function returns the current comparator interrupt
  status. It returns a 32 bit value indicating which comparators experienced a
  fall and/or rise event. These status bits can be cleared using the
  ACE_clear_comp_rise_irq() and ACE_clear_comp_fall_irq() functions.
  
  @return
    The return value is a 32 bit numnber where bits 0 to 11 indicate which
    comparator experienced a fall event and bits 21 to 23 indicate which
    comparator experienced a rise event.
 */
uint32_t ACE_get_comp_status( void );

/** @} */

/*==============================================================================
 ========================== Controlling Thresholds =============================
 =============================================================================*/
/*=========================================================================*//**
  @defgroup group8 Controlling Flags Thresholds
  The following functions are used to dynamically control Post Processing Engine
  (PPE) flags threshholds.
  @{
 *//*=========================================================================*/

/*-------------------------------------------------------------------------*//**
  The ACE_is_hysteresis_flag() function indicates if an hysteresis is applied
  to the analog input sample value when determining the state of the flag
  identified as parameter.
  
  @param flag_handle
    The flag_handle parameter identifies one of the flags generated based on the
    value of an analog input channel. The available flag handle values can be
    found in the ace_handles.h file located in the .\drivers_config\mss_ace
    subdirectory. The flag handle value can also be retrieved through a call to
    ACE_get_flag_handle() when the name of the flag is known, or by iterating
    though all flags associated with an analog input channel using the
    ACE_get_channel_first_flag() and ACE_get_channel_next_flag().
    
  @return
    This function returns the value one if a hysteresis is applied to the channel
    sample values as part of determining the state of the flag identified as
    parameter. It returns zero if no hysteresis is applied.
 */
uint32_t ACE_is_hysteresis_flag
(
    ace_flag_handle_t   flag_handle
);

/*-------------------------------------------------------------------------*//**
  The ACE_is_under_flag() function indicates whether a flag is triggered when the
  monitored analog input falls below the flag's threshold level or above the
  flag's threshold level.
  
  @param flag_handle
    The flag_handle parameter identifies one of the flags generated based on the
    value of an analog input channel. The available flag handle values can be
    found in the ace_handles.h file located in the .\drivers_config\mss_ace
    subdirectory. The flag handle value can also be retrieved through a call to
    ACE_get_flag_handle() when the name of the flag is known, or by iterating
    though all flags associated with an analog input channel using the
    ACE_get_channel_first_flag() and ACE_get_channel_next_flag().
    
  @return
    This function returns the value one if the flag identified as parameter
    triggers as a result of the monitored input falling below the flag's
    threshold value.
    It returns zero if the flag triggers as a result of the monitored input
    exceeding the flag's threshold value.
 */
uint32_t ACE_is_under_flag
(
    ace_flag_handle_t   flag_handle
);

/*-------------------------------------------------------------------------*//**
  The ACE_set_flag_threshold() function is used to adjust the threshold for a
  specific post processing engine generated flag. The flag is identified through
  the name selected in the ACE configurator software tool.
  This function will set a new flag’s threshold value while preserving the
  hysteresis specified at configuration time or through a call to
  ACE_set_flag_hysteresis(). For example, requesting a 1 volt threshold for an
  over flag configured with a 100 millivolts hysteresis will result in the flag
  being asserted when the voltage reaches 1.1 volts and deasserted when the
  voltage falls below 0.9 volt.
  
  @param flag_handle
    The flag_handle parameter identifies one of the flags generated based on the
    value of an analog input channel. The available flag handle values can be
    found in the ace_handles.h file located in the ./drivers_config/mss_ace
    subdirectory. The flag handle value can also be retrieved through a call to
    ACE_get_flag_handle() when the name of the flag is known, or by iterating
    though all flags associated with an analog input channel using the
    ACE_get_channel_first_flag() and ACE_get_channel_next_flag().
  
  @param new_threshold
    The new_threshold parameter specifies the new threshold level that must be
    reached in order for the flag to be raised. The value of this parameter is
    the sample value resulting from a post processing engine conversion of the
    desired analog input threshold level.
    
  Example:
    The function below sets the threshold of the flag specified as parameter to
    1 volt.
  @code
    void set_threshold_to_1V
    (
        ace_flag_handle_t flag_handle
    )
    {
        uint16_t new_threshold;
        ace_channel_handle_t channel_handle;
    
        channel_handle = ACE_get_flag_channel(flag_handle);
        new_threshold = ACE_convert_from_mV(channel_handle, 1000);
        ACE_set_flag_threshold(flag_handle, new_threshold);
    }
  @endcode
 */
void ACE_set_flag_threshold
(
    ace_flag_handle_t   flag_handle,
    uint16_t            new_threshold
);

/*-------------------------------------------------------------------------*//**
  The ACE_set_flag_hysteresis() function modifies the hysteresis applied to the
  analog input channel sample values used to generate the flag specified as
  parameter.

  @param flag_handle
    The flag_handle parameter identifies one of the flags generated based on the
    value of an analog input channel. The available flag handle values can be
    found in the ace_handles.h file located in the .\drivers_config\mss_ace
    subdirectory. The flag handle value can also be retrieved through a call to
    ACE_get_flag_handle() when the name of the flag is known, or by iterating
    though all flags associated with an analog input channel using the
    ACE_get_channel_first_flag() and ACE_get_channel_next_flag().
    
  @param adc_hysteresis
    The adc_hysteresis parameter is the value to add and subtract to the
    threshold value to obtain the hysteresis high and low limits triggering flag
    assertion and deassertion. The adc_hysteresis parameter is a PPE conversion
    result offset.

  Example
    The example below demonstrates the use of the ACE_set_flag_hysteresis()
    function to set a 100mV hysteresis on the OVER_1V flag of the VoltageMonitor
    input channel. VoltageMonitor and OVER_1V are names selected in the ACE
    configurator for one of the analog inputs and one of the flags associated
    with that input.
    The method used to compute the adc_hysteresis value will work for all
    input types including ABPS inputs where zero Volts is not equivalent to a 
    PPE sample value of zero.
    
  @code
    ace_channel_handle_t channel_handle;
    ace_flag_handle_t flag_handle;
    uint16_t adc_hysteresis;
    uint16_t upper_limit;
    uint16_t lower_limit;
    
    channel_handle = VoltageMonitor;
    flag_handle = VoltageMonitor_OVER_1V;
    
    upper_limit = ACE_convert_from_mV(channel_handle, 100);
    lower_limit = ACE_convert_from_mV(channel_handle, 0);
    
    if (upper_limit > lower_limit)
    {
        adc_hysteresis = upper_limit - lower_limit;
    }
    else
    {
        adc_hysteresis = lower_limit - upper_limit;
    }
    
    ACE_set_flag_hysteresis(flag_handle, adc_hysteresis);
  @endcode
 */
void
ACE_set_flag_hysteresis
(
    ace_flag_handle_t   flag_handle,
    uint16_t            adc_hysteresis
);

/*-------------------------------------------------------------------------*//**
  The ACE_set_flag_assertion() function sets the PPE sample value that must be
  reached in order for the flag specified as parameter to become asserted. It is
  used in conjunction with the ACE_set_flag_deassertion() function as an
  alternative to the ACE_set_flag_threshold() and ACE_set_flag_hysteresis()
  functions to set the hysteresis window of an hysteresis flag.
  The ACE_set_flag_assertion() and ACE_set_flag_deassertion() functions are
  intended to be used where the threshold value is not centered within the
  hysteresis window. They allow specifying the actual threshold values at which
  the flag will be asserted and deasserted.

  @param flag_handle
    The flag_handle parameter identifies one of the flags generated based on the
    value of an analog input channel. The available flag handle values can be
    found in the ace_handles.h file located in the .\drivers_config\mss_ace
    subdirectory. The flag handle value can also be retrieved through a call to
    ACE_get_flag_handle() when the name of the flag is known, or by iterating
    though all flags associated with an analog input channel using the
    ACE_get_channel_first_flag() and ACE_get_channel_next_flag().
    
  @param assertion_value
    The assertion_value parameter is the Post Processing Engine sample value that
    must be reached for the flag, identified through the flag_handle parameter,
    to become asserted. The PPE sample value is always a 12 bits sample value
    regardless of the configuration of the ADC used to sample the input channel.
 */
void ACE_set_flag_assertion
(
    ace_flag_handle_t   flag_handle,
    uint16_t            assertion_value
);

/*-------------------------------------------------------------------------*//**
  The ACE_set_flag_deassertion() function sets the PPE sample value that must be
  reached in order for the flag specified as parameter to become deasserted. It
  is used in conjunction with the ACE_set_flag_assertion() function as an
  alternative to the ACE_set_flag_threshold() and ACE_set_flag_hysteresis()
  functions to set the hysteresis window of an hysteresis flag.
  The ACE_set_flag_assertion() and ACE_set_flag_deassertion() functions are
  intended to be used where the threshold value is not centered within the
  hysteresis window. They allow specifying the actual threshold values at which
  the flag will be asserted and deasserted.
  
  @param flag_handle
    The flag_handle parameter identifies one of the flags generated based on the
    value of an analog input channel. The available flag handle values can be
    found in the ace_handles.h file located in the .\drivers_config\mss_ace
    subdirectory. The flag handle value can also be retrieved through a call to
    ACE_get_flag_handle() when the name of the flag is known, or by iterating
    though all flags associated with an analog input channel using the
    ACE_get_channel_first_flag() and ACE_get_channel_next_flag().
    
  @param assertion_value
    The assertion_value parameter is the Post Processing Engine sample value
    that must be reached for the flag, identified through the flag_handle
    parameter, to become de-asserted. The PPE sample value is always a 12 bits
    sample value regardless of the configuration of the ADC used to sample the
    input channel.
 */
void ACE_set_flag_deassertion
(
    ace_flag_handle_t   flag_handle,
    uint16_t            assertion_value
);

/*-------------------------------------------------------------------------*//**
  The ACE_set_channel_hysteresis() function sets the hysteresis applied to
  analog input channel sample values when generating flags. It sets the
  hysteresis for all flags generated based on the value of the analog input
  channel identified by the channel handle passed as first parameter.
  
  @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in
    the ace_handles.h file located in the .\drivers_config\mss_ace subdirectory.
    The channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().

  @param adc_hysteresis
    The adc_hysteresis parameter is the value to add and subtract to the
    threshold value to obtain the hysteresis high and low limits triggering flag
    assertion and deassertion. The adc_hysteresis parameter is a PPE conversion
    result offset.
 */
void
ACE_set_channel_hysteresis
(
    ace_channel_handle_t    channel_handle,
    uint16_t                adc_hysteresis
);


/** @} */
/*-------------------------------------------------------------------------*//**
 *
 */
 
/*==============================================================================
 ================================== Flags ======================================
 =============================================================================*/
/*=========================================================================*//**
  @defgroup group6 Post Processing Engine Flags
  The following functions are used to control interrupts generated by the ACE's
  Post Processing Engine (PPE) when monitored inputs rise above or fall below
  thresholds specified in the ACE configurator software tool.
  @{
 *//*=========================================================================*/

 /*-------------------------------------------------------------------------*//**
   These constant definitions are the return values of the ACE_get_flag_status()
   function. They specify the status of the Post Processing Engine (PPE) flag.
  */
#define UNKNOWN_FLAG        (int32_t)(-1)
#define FLAG_ASSERTED       (int32_t)1
#define FLAG_NOT_ASSERTED   (int32_t)0

/*-------------------------------------------------------------------------*//**
  This constant is returned by the ACE_get_flag_handle function when the driver
  can’t find a valid handle for the Post Processing Engine (PPE) flag.
 */
#define INVALID_FLAG_HANDLE     NB_OF_ACE_FLAG_HANDLES

/*-------------------------------------------------------------------------*//**
  The ACE_get_flag_handle() function returns the handle of the flag identified
  by the flag name passed as parameter. The flag handle obtained through this
  function is then used as parameter to other flag control functions to identify
  which flag is to be controlled by the called function.
  
  @param p_sz_full_flag_name
    The p_sz_full_flag_name parameter is a pointer to a zero-terminated string
    holding the name of the flag as specified in the ACE configurator. The full
    name of a flag contains both the name of the monitored input channel and the
    name of the flag generated based the level of that input separated by ":".
    For example, the full name for the flag called "CriticalOver" raised when
    the input channel called "MainSupply" reaches a critical level would be
    named "MainSupply:CriticalOver".
    
  @return
    The ACE_get_flag_handle() returns the flag handle associated with the flag
    name passed as parameter. It returns INVALID_FLAG_HANDLE when the flag name
    is invalid and not recognized by the ACE driver.
 */
ace_flag_handle_t
ACE_get_flag_handle
(
    const uint8_t * p_sz_full_flag_name
);

/*-------------------------------------------------------------------------*//**
  The ACE_get_flag_status() function returns the current status of the flag
  specified as parameter. The flag is identified through the name specified in
  the ACE configurator when the flag was created.
  
  @param flag_handle
    The flag_handle parameter identifies one of the flags generated based on the
    value of an analog input channel. The available flag handle values can be
    found in the ace_handles.h file located in the .\drivers_config\mss_ace
    subdirectory. The flag handle value can also be retrieved through a call to
    ACE_get_flag_handle() when the name of the flag is known, or by iterating
    though all flags associated with an analog input channel using the
    ACE_get_channel_first_flag() and ACE_get_channel_next_flag().
    
   @return
    The ACE_get_flag_status() function returns one of the following values
    depending on the current status of the flag:
        - FLAG_ASSERTED if the flag is raised/asserted.
        - FLAG_NOT_ASSERTED if the flag is not asserted.
        - UNKNOWN_FLAG if the flag name is not recognized by the driver.
*/
int32_t
ACE_get_flag_status
(
    ace_flag_handle_t   flag_handle
);

/*-------------------------------------------------------------------------*//**
  The ACE_enable_channel_flags_irq() function enables all flags generated based
  on the value of the analog input channel passed as parameter to generate
  interrupts. Flags used to detect that thresholds are crossed by the value
  sampled on the analog input channel identified as parameter are enabled to
  generate interrupts by this function. It enables flag interrupts both at the
  ACE PEE flag and Cortex-M3 interrupt controller levels.
  
  @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
 */
void ACE_enable_channel_flags_irq
(
    ace_channel_handle_t channel_handle
);

/*-------------------------------------------------------------------------*//**
  The ACE_disable_channel_flags_irq() function disables all flags generated
  based on the value of the analog input channel passed as parameter to generate
  interrupts. Flags used to detect that thresholds are crossed by the value
  sampled on the analog input channel identified as parameter are disabled from
  generating interrupts by this function. The interrupt is only disabled at the
  ACE PPE flag level in order to avoid disabling other cahnnel's flag interrupts
  which may happen to use the same ACE threshold interrupt line.
  
  @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
 */
void ACE_disable_channel_flags_irq
(
    ace_channel_handle_t channel_handle
);

/*-------------------------------------------------------------------------*//**
  The ACE_clear_channel_flags_irq() function clears all interrupts generated by
  flags associated with the analog input channel passed as parameter. Interrupt
  generated by flags used to detect that thresholds are crossed by the value
  sampled on the analog input channel identified as parameter are cleared by
  this function. This function would typically be used before enabling the flag
  interrupts in order to ignore past events.
  
  @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
 */
void ACE_clear_channel_flags_irq
(
    ace_channel_handle_t channel_handle
);

/*-------------------------------------------------------------------------*//**
  The ACE_enable_flag_irq() function enables the ACE post processing engine (PPE)
  generated flags specified as parameter to interrupt the Cortex-M3 processor.
  It enables flag interrupts both at the ACE PPE flag and Cortex-M3 interrupt
  controller levels.
  
  @param flag_handle
    The flag_handle parameter identifies one of the flags generated based on the
    value of an analog input channel. The available flag handle values can be
    found in the ace_handles.h file located in the .\drivers_config\mss_ace
    subdirectory. The flag handle value can also be retrieved through a call to
    ACE_get_flag_handle() when the name of the flag is known, or by iterating
    though all flags associated with an analog input channel using the
    ACE_get_channel_first_flag() and ACE_get_channel_next_flag().
 */
void ACE_enable_flag_irq
(
    ace_flag_handle_t flag_handle
);

/*-------------------------------------------------------------------------*//**
  The ACE_disable_flag_irq() function disables ACE post processing engine (PPE)
  generated flags from interrupting the Cortex-M3. The interrupt is only
  disabled at the ACE PPE flag level in order to avoid disabling other flags
  interrupts which may happen to use the same ACE threshold interrupt line.
  
  @param flag_handle
    The flag_handle parameter identifies one of the flags generated based on the
    value of an analog input channel. The available flag handle values can be
    found in the ace_handles.h file located in the .\drivers_config\mss_ace
    subdirectory. The flag handle value can also be retrieved through a call to
    ACE_get_flag_handle() when the name of the flag is known, or by iterating
    though all flags associated with an analog input channel using the
    ACE_get_channel_first_flag() and ACE_get_channel_next_flag().
 */
void ACE_disable_flag_irq
(
    ace_flag_handle_t flag_handle
);

/*-------------------------------------------------------------------------*//**
  The ACE_clear_flag_irq() function clears the interrupt for the flag specified
  as parameter. This function would typically be used before enabling the flag
  interrupt in order to ignore past events.
  
  @param flag_handle
    The flag_handle parameter identifies one of the flags generated based on the
    value of an analog input channel. The available flag handle values can be
    found in the ace_handles.h file located in the .\drivers_config\mss_ace
    subdirectory. The flag handle value can also be retrieved through a call to
    ACE_get_flag_handle() when the name of the flag is known, or by iterating
    though all flags associated with an analog input channel using the
    ACE_get_channel_first_flag() and ACE_get_channel_next_flag().
 */
void ACE_clear_flag_irq
(
    ace_flag_handle_t flag_handle
);

/*-------------------------------------------------------------------------*//**
  The ACE_get_flag_name() function returns the name of the flag identified by
  the flag handle passed as parameter.
  
  @param flag_handle
    The flag_handle parameter identifies one of the flags generated based on the
    value of an analog input channel. The available flag handle values can be
    found in the ace_handles.h file located in the .\drivers_config\mss_ace
    subdirectory. The flag handle value can also be retrieved through a call to
    ACE_get_flag_handle() when the name of the flag is known, or by iterating
    though all flags associated with an analog input channel using the
    ACE_get_channel_first_flag() and ACE_get_channel_next_flag().
    
  @return
    The ACE_get_flag_name() function returns a pointer to a zero-terminated
    string containing the name of the flag identified by the flag handle passed
    as parameter. It returns 0 if the flag handle passed as parameter is invalid.
 */
const uint8_t *
ACE_get_flag_name
(
    ace_flag_handle_t flag_handle
);

/*-------------------------------------------------------------------------*//**
  The ACE_get_flag_channel() function returns the handle of the channel
  monitored in order to generate the flag identified by the flag handle passed
  as parameter.
  
  @param flag_handle
    The flag_handle parameter identifies one of the flags generated based on the
    value of an analog input channel. The available flag handle values can be
    found in the ace_handles.h file located in the .\drivers_config\mss_ace
    subdirectory. The flag handle value can also be retrieved through a call to
    ACE_get_flag_handle() when the name of the flag is known, or by iterating
    though all flags associated with an analog input channel using the
    ACE_get_channel_first_flag() and ACE_get_channel_next_flag().
    
  @return
    The ACE_get_flag_channel() function returns a channel handle identifying the
    analog input channel monitored by the flag passed as parameter.
 */
ace_channel_handle_t
ACE_get_flag_channel
(
    ace_flag_handle_t flag_handle
);

/*-------------------------------------------------------------------------*//**
  The ACE_get_channel_flag_count() function returns the total number of flags
  associated with the input channel specified by the channel_handle parameter.
  It indicates how many flags are generated based on the value of the specified
  analog input channel.
    
  @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in
    the ace_handles.h file located in the .\drivers_config\mss_ace subdirectory.
    The channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @return
    The ACE_get_channel_flag_count() function returns the total number of flags
    that are generated based on the value of the specified analog input channel.
    The ACE_get_channel_flag_count() function returns 0 if no input channels were
    configured.
  
  Example
  @code
    uint32_t inc;
    uint32_t nb_of_flags;
    uint16_t flag_iterator;
    ace_flag_handle_t current_flag;
    ace_channel_handle_t channel_handle;
    
    nb_of_flags = ACE_get_channel_flag_count(channel_handle);
    current_flag = ACE_get_channel_first_flag(channel_handle, &flag_iterator);
    
    for (inc = 0; inc < nb_of_flags; ++inc)
    {
        current_flag = ACE_get_channel_next_flag(channel_handle, &flag_iterator);
        display_flag_properties(current_flag);
    }
  @endcode
  */
uint32_t
ACE_get_channel_flag_count
(
    ace_channel_handle_t    channel_handle
);

/*-------------------------------------------------------------------------*//**
  The ACE_get_channel_first_flag() function retrieves the handle of the first
  flag associated with the analog input channel identified by the channel handle
  passed as parameter. It also initialises the value of the iterator variable
  pointed to by the second function parameter. The iterator can be used
  subsequently as a parameter to the ACE_get_channel_next_flag() function to
  iterate through all flags associated with the analog input channel.
  
  @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory.
    The channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @param iterator
    The iterator parameter is a pointer to a uint16_t iterator variable. The
    value of the iterator variable will be set by the ACE_get_channel_first_flag()
    functions so that it can be used in subsequent calls to
    ACE_get_channel_next_flag() to keep track of the current location in the
    list of flags associated with the analog input channel.
    
  @return
    The ACE_get_channel_first_flag() function returns a flag handle identifying
    one of the flags generated based on the value of the analog input channel
    identified by the channel_handle parameter. It returns INVALID_FLAG_HANDLE
    if no flags are generated based on the analog input channel input or if the
    channel handle is invalid.
    
  Example
  @code
    uint32_t inc;
    uint32_t nb_of_flags;
    uint16_t flag_iterator;
    ace_flag_handle_t current_flag;
    ace_channel_handle_t channel_handle;
    
    nb_of_flags = ACE_get_channel_flag_count(channel_handle);
    current_flag = ACE_get_channel_first_flag(channel_handle, &flag_iterator);
    
    for (inc = 0; inc < nb_of_flags; ++inc)
    {
        current_flag = ACE_get_channel_next_flag(channel_handle, &flag_iterator);
        display_flag_properties(current_flag);
    }
  @endcode
  */
ace_flag_handle_t
ACE_get_channel_first_flag
(
    ace_channel_handle_t    channel_handle,
    uint16_t *              iterator
);

/*-------------------------------------------------------------------------*//**
  The ACE_get_channel_next_flag() function retrieves the handle of a flag
  associated with the analog input channel identified by the channel handle
  passed as parameter. The retrieved flag handle is the next one in the driver's
  internal flag list based on the iterator parameter.
  
  @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the .\drivers_config\mss_ace subdirectory.
    The channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @param iterator
    The iterator parameter is a pointer to a uint16_t iterator variable. The value
    of the iterator variable will be set by the ACE_get_channel_first_flag()
    functions so that it can be used in subsequent calls to
    ACE_get_channel_next_flag() to keep track of the current location in the list
    of flags associated with the analog input channel.
    
  Example
  @code
    uint32_t inc;
    uint32_t nb_of_flags;
    uint16_t flag_iterator;
    ace_flag_handle_t current_flag;
    ace_channel_handle_t channel_handle;
    
    nb_of_flags = ACE_get_channel_flag_count(channel_handle);
    current_flag = ACE_get_channel_first_flag(channel_handle, &flag_iterator);
    
    for (inc = 0; inc < nb_of_flags; ++inc)
    {
        current_flag = ACE_get_channel_next_flag(channel_handle, &flag_iterator);
        display_flag_properties(current_flag);
    }
  @endcode
 */
ace_flag_handle_t
ACE_get_channel_next_flag
(
    ace_channel_handle_t    channel_handle,
    uint16_t *              iterator
);

/*-------------------------------------------------------------------------*//**
  This defines the function prototype that must be followed by MSS ACE Post
  Processing Engine (PPE) flag handler functions. These functions are registered
  with the ACE driver and associated with a particular flag through the
  ACE_register_flag_isr() function. The ACE driver will call the flag handler
  function when the associated flag is raised.
  
  Declaring and Implementing PPE Flag Handler Functions
  PPE flag handler functions should follow the following prototype:
    void my_flag_handler ( ace_flag_handle_t flag_handle );
  The actual name of the PPE flag handler is unimportant. You can use any name of
  your choice for the PPE flag handler. 
  The flag_handle parameter passes the handle of the raised flag to the flag
  handler function.
 */
typedef void (*flag_isr_t)( ace_flag_handle_t flag_handle );

/*-------------------------------------------------------------------------*//**
  The ACE_register_flag_isr() function is used to register a handler function
  with the ACE driver. The registered function will be called by the ACE driver
  when the associated flag is raised by the ACE post processing engine.
  
  @param flag_handle
    The flag_handle parameter identifies one of the flags generated based on the
    value of an analog input channel. The available flag handle values can be
    found in the ace_handles.h file located in the .\drivers_config\mss_ace
    subdirectory. The flag handle value can also be retrieved through a call to
    ACE_get_flag_handle() when the name of the flag is known, or by iterating
    though all flags associated with an analog input channel using the
    ACE_get_channel_first_flag() and ACE_get_channel_next_flag().
  
  @param flag_isr
    The flag_isr parameter is a pointer to a flag handler function with the
    following prototype: 
        void handler_function_name(ace_flag_handle_t  flag_handle) 
    The flag handler function is called by the ACE driver as part of the relevant
    post processing engine flag interrupt service routine. It does not need to
    handle flag interrupt clearing as this is done by the ACE driver.

  
  @code
    void my_critical_handler( void );
    
    void system_init( void )
    {
        ace_flag_handle_t flag_handle;
        
        flag_handle = ACE_get_flag_handle( "MainSupply:CriticalLevel" );
        ACE_register_flag_isr( flag_handle, my_critical_handler );
        ACE_enable_flag_irq( flag_handle );
    }
    
    void my_critical_handler( ace_flag_handle_t flag_handle  )
    {
        panic( flag_handle );
    }
    
  @endcode
 */
void ACE_register_flag_isr
(
    ace_flag_handle_t   flag_handle,
    flag_isr_t          flag_isr
);

/*-------------------------------------------------------------------------*//**
  This defines the function prototype that must be followed by MSS ACE Post
  Processing Engine (PPE) channel flag handler functions. These functions are
  registered with the ACE driver and associated with a particular ADC input
  channel through the ACE_register_channel_flags_isr() function. The ACE driver
  will call the channel flags handler function when one of the flags for the
  associated ADC input channel is raised.
  
  Declaring and Implementing PPE Channel Flag Handler Functions
  PPE channel flag handler functions should follow the following prototype:
    void my_channel_flag_handler ( ace_flag_handle_t flag_handle );
    The actual name of the PPE channel flag handler is unimportant. You can use
    any name of your choice for the PPE channel flag handler. The flag_handle
    parameter passes the handle of the raised flag to the channel flag handler
    function.
 */
typedef void (*channel_flag_isr_t)( ace_flag_handle_t flag_handle );

/*-------------------------------------------------------------------------*//**
  The ACE_register_channel_flags_isr() function is used to register a flag
  interrupt handler function with the ACE driver. The registered interrupt
  handler will be called by the ACE driver when one of the flag generated based
  on the value of the analog input channel identified by the channel handle
  passed as parameter is asserted.
  
   @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @param channel_flag_isr
    The channel_flag_isr parameter is pointer to a function taking a flag handle
    as parameter. 
        void handler_function_name(ace_flag_handle_t  flag_handle) 
    The flag handler function is called by the ACE driver as part of the relevant
    post processing engine flag interrupt service routine. It does not need to
    handle flag interrupt clearing as this is done by the ACE driver.
  
  Example
    The example below demonstrates the use of the ACE_register_channel_flags_isr()
    function in a system where the ACE is configured to have an analog input
    channels named "MainSupply" with one flag named "Critical" generated based
    on the value of "MainSupply" channel. The names "MainSupply" and "Critical"
    were user selected in the ACE configurator. 
  @code
    void main_supply_handler (ace_flag_handle_t flag_handle);
    
    void system_init(void)
    {
        ACE_register_channel_flag_isr(MainSupply, main_supply_handler);
        ACE_enable_channel_flags_irq(MainSupply);
    }
    
    void main_supply_handler (ace_flag_handle_t flag_handle)
    {
        if (MainSupply_Critical == flag_handle)
        {
            panic(flag_handle);
        }
    }
  
  @endcode
*/
void ACE_register_channel_flags_isr
(
    ace_channel_handle_t    channel_handle,
    channel_flag_isr_t      channel_flag_isr
);

/*-------------------------------------------------------------------------*//**
  This defines the function prototype that must be followed by MSS ACE Post
  Processing Engine (PPE) global flag handler functions. These functions are
  registered with the ACE driver through the ACE_register_global_flags_isr()
  function. The ACE driver will call the global flags handler function when any
  flag for any ADC input channel is raised.
  
  Declaring and Implementing Global Flag Handler Functions
  PPE global flag handler functions should follow the following prototype:
    void my_global_flag_handler( 
        ace_flag_handle_t flag_handle, 
        ace_channel_handle_t channel_handle 
    );
  The actual name of the PPE global flag handler is unimportant. You can use any
  name of your choice for the PPE global flag handler. The flag_handle parameter
  passes the handle of the raised flag to the global flag handler function. The
  channel_handle parameter passes the handle of the channel for which the flag
  was raised to the global flag handler function.

 */
typedef void (*global_flag_isr_t)( ace_flag_handle_t flag_handle, ace_channel_handle_t channel_handle );

/*-------------------------------------------------------------------------*//**
  The ACE_register_global_flags_isr() function is used to register a global
  flag handler function with the ACE driver. The registered global handler will
  be called when any flag interrupt is generated.
  
  @param global_flag_isr
    The global_flag_isr parameter is a pointer to a function taking a flag
    handle and channel handle as parameter.
 */
void ACE_register_global_flags_isr
(
    global_flag_isr_t  global_flag_isr
);

/** @} */

/*=========================================================================*//**
  @defgroup group11 Conversion Functions
  The following functions are used to convert an ADC sample value to a real
  world unit.
  @{
 *//*=========================================================================*/

/*-------------------------------------------------------------------------*//**
  The ACE_convert_adc_input_to_mV() function converts an ADC sample value into
  the value in millivolts of the voltage seen at ADC input. It does not account
  for prescaling taking place before the ADC hardware input.

   @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @param sample_value
    The sample_value parameter is the result of an analog to digital conversion.
  
  @return
    The ACE_convert_adc_input_to_mV() returns the number of millivolts derived
    from the ADC sample value passed as parameter.
 */
uint32_t ACE_convert_adc_input_to_mV
(
    ace_channel_handle_t    channel_handle,
    uint16_t                sample_value
);

/*-------------------------------------------------------------------------*//**
  The ACE_convert_to_mV() function converts a PPE sample value into milli-Volts.
  It handles prescaling adjusments based on ACE configuration for ABPS inputs.
  
   @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @param sample_value
    The sample_value parameter is the result of an analog to digital conversion.
  
  @return
    The ACE_convert_to_mV() returns the number of millivolts derived from the
    PPE sample value passed as parameter. The returned value can be either
    positive or negative since prescaling is accounted for in the conversion.
 */
int32_t ACE_convert_to_mV
(
    ace_channel_handle_t    channel_handle,
    uint16_t                sample_value
);

/*-------------------------------------------------------------------------*//**
  The ACE_convert_to_mA() function converts a PPE sample value into milli-Amps.
  The result of the conversion is only meaningful if the PPE sample value
  results from the conversion of a current monitor input.
  
   @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @param sample_value
    The sample_value parameter is the result of an analog to digital conversion
    of the voltage generated by a current monitor analog block.
  
  @return
    The ACE_convert_to_mA() returns the number of milliamps derived from the
    PPE sample value passed as parameter.
 */
uint32_t ACE_convert_to_mA
(
    ace_channel_handle_t    channel_handle,
    uint16_t                sample_value
);

/*-------------------------------------------------------------------------*//**
  The ACE_convert_to_Kelvin() function converts a PPE sample value into degrees
  Kelvin. The result of the conversion is only meaningful if the PPE sample value
  results from the conversion of a temperature monitor input.
  
   @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @param sample_value
    The sample_value parameter is the result of an analog to digital conversion
    of the voltage generated by a temperature monitor analog block.
  
  @return
    The ACE_convert_to_Kelvin() returns the number of degrees Kelvin derived
    from the PPE sample value passed as parameter.
 */
uint32_t ACE_convert_to_Kelvin
(
    ace_channel_handle_t    channel_handle,
    uint16_t                sample_value
);

/*-------------------------------------------------------------------------*//**
  The ACE_convert_to_Celsius() function converts a PPE sample value into tenths
  of degrees Celsius. The result of the conversion is only meaningful if the PPE
  sample value results from the conversion of a temperature monitor input.
  
   @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @param sample_value
    The sample_value parameter is the result of an analog to digital conversion
    of the voltage generated by a temperature monitor analog block.
  
  @return
    The ACE_convert_to_Celsius() returns the number of tenths of degrees Celsius
    derived from the PPE sample value passed as parameter.
 */
int32_t ACE_convert_to_Celsius
(
    ace_channel_handle_t    channel_handle,
    uint16_t                sample_value
);

/*-------------------------------------------------------------------------*//**
  The ACE_convert_to_Fahrenheit() function converts a PPE sample value into
  degrees Fahrenheit. The result of the conversion is only meaningful if the PPE
  sample value results from the conversion of a temperature monitor input.
  
   @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @param sample_value
    The sample_value parameter is the result of an analog to digital conversion
    of the voltage generated by a temperature monitor analog block.
  
  @return
    The ACE_convert_to_Fahrenheit() returns the number of degrees Fahrenheit
    derived from the PPE sample value passed as parameter.
 */
int32_t ACE_convert_to_Fahrenheit
(
    ace_channel_handle_t    channel_handle,
    uint16_t                sample_value
);

/*-------------------------------------------------------------------------*//**
  The ACE_convert_mV_to_adc_value() function converts a voltage value given in
  milli-Volts into the ADC sample value that would result from sampling this
  voltage value on the analog input channel specified as parameter.
  This function is intended for use when directly controlling the ADC, not when
  using samples read from the PPE. It does not account for prescaling taking
  place before the ADC hardware input.
  
   @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @param voltage
    The voltage parameter is the milli-Volts voltage value for which we want this
    function to return the associated ADC sample result value.
  
  @return
    The ACE_convert_mV_to_adc_value() returns the ADC sample value that would be
    produced if the analog input channel identified by channel_handle was set to
    the voltage value passed as second parameter.
 */
uint16_t ACE_convert_mV_to_adc_value
(
    ace_channel_handle_t    channel_handle,
    uint32_t                voltage
);

/*-------------------------------------------------------------------------*//**
  The ACE_convert_from_mV() function converts a voltage value given in
  milli-Volts into the PPE sample value that would result from sampling this
  voltage value on the analog input channel specified as parameter.
  This function handles prescaling adjusments based on ACE configuration for
  ABPS inputs.
  
   @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @param voltage
    The voltage parameter is the milli-Volts voltage value for which we want this
    function to return the associated PPE sample result value.
  
  @return
    The ACE_convert_from_mV() returns the PPE sample value that would be produced
    if the analog input channel identified by channel_handle was set to the
    voltage value passed as second parameter.
 */
uint16_t ACE_convert_from_mV
(
    ace_channel_handle_t    channel_handle,
    int32_t                 voltage
);

/*-------------------------------------------------------------------------*//**
  The ACE_convert_from_mA() function converts a current value given in
  milli-Amps into the PPE sample value that would result from sampling this
  current value on the analog input channel specified as parameter.
  The result of the conversion is only meaningful if the analog input channel
  specified as parameter is configured as a current monitoring channel.
  
   @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @param current
    The current parameter is the milli-Amps current value for which we want this
    function to return the associated PPE sample result value.
  
  @return
    The ACE_convert_from_mA() returns the PPE sample value that would be produced
    if the analog input channel identified by channel_handle was set to the
    current value passed as second parameter.
 */
uint16_t ACE_convert_from_mA
(
    ace_channel_handle_t    channel_handle,
    uint32_t                current
);

/*-------------------------------------------------------------------------*//**
  The ACE_convert_from_Kelvin() function converts a temperature value given in
  degrees Kelvin into the PPE sample value that would result from sampling this
  temperature value on the analog input channel specified as parameter.
  The result of the conversion is only meaningful if the analog input channel
  specified as parameter is configured as a temperature monitoring channel.
  
   @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @param temperature
    The temperature parameter is the degrees Kelvin temperature value for which
    we want this function to return the associated PPE sample result value.
  
  @return
    The ACE_convert_from_Kelvin() returns the PPE sample value that would be
    produced if the analog input channel identified by channel_handle was set to
    the temperature value passed as second parameter.
 */
uint16_t ACE_convert_from_Kelvin
(
    ace_channel_handle_t    channel_handle,
    uint32_t                temperature
);

/*-------------------------------------------------------------------------*//**
  The ACE_convert_from_Celsius() function converts a temperature value given in
  degrees Celsius into the PPE sample value that would result from sampling this
  temperature value on the analog input channel specified as parameter.
  The result of the conversion is only meaningful if the analog input channel
  specified as parameter is configured as a temperature monitoring channel.
  
   @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @param temperature
    The temperature parameter is the degrees Celsius temperature value for which
    we want this function to return the associated PPE sample result value.
  
  @return
    The ACE_convert_from_Celsius() returns the PPE sample value that would be
    produced if the analog input channel identified by channel_handle was set to
    the temperature value passed as second parameter.
 */
uint16_t ACE_convert_from_Celsius
(
    ace_channel_handle_t    channel_handle,
    int32_t                 temperature
);

/*-------------------------------------------------------------------------*//**
  The ACE_convert_from_Fahrenheit() function converts a temperature value given
  in degrees Fahrenheit into the PPE sample value that would result from sampling
  this temperature value on the analog input channel specified as parameter.
  The result of the conversion is only meaningful if the analog input channel
  specified as parameter is configured as a temperature monitoring channel.
  
   @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in the
    ace_handles.h file located in the ./drivers_config/mss_ace subdirectory. The
    channel handle value can also be retrieved through a call to
    ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @param temperature
    The temperature parameter is the degrees Fahrenheit temperature value for
    which we want this function to return the associated PPE sample result value.
  
  @return
    The ACE_convert_from_Fahrenheit() returns the PPE sample value that would be
    produced if the analog input channel identified by channel_handle was set to
    the temperature value passed as second parameter.
 */
uint16_t ACE_convert_from_Fahrenheit
(
    ace_channel_handle_t    channel_handle,
    int32_t                 temperature
);

/*-------------------------------------------------------------------------*//**
  The ACE_translate_pdma_value() function translates PDMA sampling values,
  received from the ACE via PDMA transfers, into input channel ID and PPE
  sample value.
  The PDMA sampling values are generated by the ACE as a result of selecting
  "Send result to DMA" in the ACE configurator analog input configuration. The
  PDMA sampling values can be either raw ADC values, filtered values or the
  result of a linear transformation.
  The PDMA sampling values are obtained by configuring the PDMA controller to
  transfer data from the ACE into a memory buffer. The ACE_translate_pdma_value()
  function is used to interpret the content of that memory buffer.
  
  Please note that the translation of PDMA data containing raw ADC values from
  ABPS inputs will result in sample values with an unexpected polarity.
  The returned sample value will have the opposite polarity to the actual analog
  value seen on the ABPS input. This is due to the internal characteristics of
  the analog front end that are normally hidden by the PPE processing of ADC raw
  samples. The translation of raw ADC values from analog inputs other than ABPS
  inputs will result in correct sample values.
  
   @param pdma_value
    The pdma_value parameter is a 32-bit value received from the ACE through a
    peripheral DMA transfer. 
    
  @param channel_id
    The channel_id parameter is a pointer to an ADC channel ID variable. It is
    used to return the ID of the ADC channel from which the PPE sample value
    was generated from. This parameter can be set to zero if retrieving the
    channel ID is not required.
  
  @return
    The ACE_translate_pdma_value() returns the PPE sample value extracted from
    the PDMA sampling value.
  
  Example:
  @code
    uint16_t ppe_value;
    uint16_t pdma_value;
    adc_channel_id_t channel_id;
    ace_channel_handle_t channel_handle;
    
    pdma_value = get_next_pdma_ace_sample();
    ppe_value = ACE_translate_pdma_value(pdma_value, &channel_id);
    channel_handle = ACE_get_input_channel_handle(channel_id);
    if (channel_handle != INVALID_CHANNEL_HANDLE)
    {
        display_value(channel_handle, ppe_value);
    }
  @endcode
  
 */
uint16_t ACE_translate_pdma_value
(
    uint32_t            pdma_value,
    adc_channel_id_t *  channel_id
);

/** @} */

/*=========================================================================*//**
  @defgroup group12 Dynamic Linear Transform Control Functions
  The following functions are used to dynamically adjust the linear transform
  applied to analog input samples by the post processing engine:
    - ACE_get_default_m_factor()
    - ACE_get_default_c_offset()
    - ACE_set_linear_transform()
  The post processing engine performs a linear transform on analog input samples
  obtained from the sample sequencing engine. The main purpose of this linear 
  transform is to apply part specific factory calibration to the analog samples
  in order to achieve high accuracy. A second user specified linear transform
  can also be optionally applied to the analog samples. This second linear
  transform can be used to adjust for board level calibration or application
  specific tuning. The functions described in this section apply to the user
  defined transform. Factory calibration will not be affected by the use of the
  ACE_set_linear_transform() function.
  Note:
    The post processing engine actually only performs one single linear
    transform on analog samples. This transform takes into account factory
    calibration and the user defined transform. The applied y = m.x + c
    transform uses an m factor equal to m1.m2.mext and c offset equal to
    (m2.c1.mext) + (c2.mext) where m1 and c1 are the factory calibration factor
    and offset; m2 and c2 are the user defined transform factor and offset; and
    mext is a factory calibration factor depending on the reference voltage
    used by the ADC generating the sample.
  @{
 *//*=========================================================================*/


/*------------------------------------------------------------------------*//**
  The ACE_get_default_m_factor() function retrieves the default value of the m
  factor of the user defined linear transform applied by the post processing
  engine to analog samples. The user defined linear transform m factor default
  value is selected in the ACE configurator tool.
  
  @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in
    the ace_handles.h file located in the .\drivers_config\mss_ace
    subdirectory. The channel handle value can also be retrieved through a call
    to ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
  
  @return
    The ACE_get_default_m_factor() function returns the user transform m factor
    default value. It is a signed 16-bit number representing a factor in the
    range -2 to +1.99993896484375. The value of the m factor is obtained by
    multiplying the return value’s absolute value by 2-14.
 */
int16_t ACE_get_default_m_factor
(
    ace_channel_handle_t channel_handle
);

/*------------------------------------------------------------------------*//**
  The ACE_get_default_c_offset() function retrieves the default value of the c
  offset of the user defined linear transform applied by the post processing
  engine to analog samples. The user defined linear transform c offset default
  value is selected in the ACE configurator tool.
  
  @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in
    the ace_handles.h file located in the .\drivers_config\mss_ace
    subdirectory. The channel handle value can also be retrieved through a call
    to ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @return
    The ACE_get_default_c_offset() function returns the user linear transform’s
    c offset default value. It is a signed 16-bit number representing a factor
    in the range -2 to +1.99993896484375. The value of the c offset is obtained
    by multiplying the return value’s absolute value by 2-14.
 */
int16_t ACE_get_default_c_offset
(
    ace_channel_handle_t channel_handle
);

/*------------------------------------------------------------------------*//**
  The ACE_set_linear_transform() function allows adjusting the user defined
  linear transform applied to analog input samples by the post processing
  engine. The linear transform is of the form y = m.x + b where the m factor
  and c offset are in the range -2 to +1.99993896484375.
   
  @param channel_handle
    The channel_handle parameter identifies one of the analog input channels
    monitored by the ACE. The available channel handle values can be found in
    the ace_handles.h file located in the .\drivers_config\mss_ace
    subdirectory. The channel handle value can also be retrieved through a call
    to ACE_get_channel_handle() when the name of the channel is known, or by
    iterating though all analog input channel using the ACE_get_first_channel()
    and ACE_get_next_channel().
    
  @param m2
    The m2 parameter specifies the user defined transform’s m factor. It is a
    signed 16-bit number representing a factor in the range -2 to
    +1.99993896484375. The value of the m2 factor is obtained by multiplying the
    parameter’s absolute value by 2^-14. For example, a value of 0x7000
    represents a 1.75 factor and a value of 0xE000 represents a -0.5 factor.
    
  @param c2
    The c2 parameter specifies the user defined transform’s c offset. It is a
    signed 16-bit number representing an offset in the range -2 to
    +1.99993896484375. The value of the c2 offset is obtained by multiplying the
    parameter’s absolute value by 2^-14. For example, a value of 0x1000 represents
    a 0.25 offset and a value of 0xB000 represents a -1.25 offset.
    
  @code
    void reset_to_default(ace_channel_handle_t channel_handle)
    {
        int16_t m;
        int16_t c;
        
        m = ACE_get_default_m_factor(channel_handle);
        c = ACE_get_default_c_offset(channel_handle);
        ACE_set_linear_transform(channel_handle, m, c);
    }
  @endcode
 */
void ACE_set_linear_transform
(
    ace_channel_handle_t channel_handle,
	int16_t m2,
	int16_t c2
);

/** @} */
 
#ifdef __cplusplus
}
#endif

#endif	/* __MSS_ACE_H_ */
