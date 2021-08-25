/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 */
/*=========================================================================*//**
  @mainpage PolarFire MSS Frequency Meter Bare Metal Driver.
   The MSS Clock Frequency Meter (CFM) block is used to support test of the
   DLL's within the MSS. All functional clocks are connected to the CFM block.

   The frequency meter can be configured to measure time or frequency, time
   allowing items such as PLL lock times to be tested and frequency to test
   oscillator frequencies.

   Upto 8 circuit counters are implemented.

  @section intro_sec Introduction

 *//*=========================================================================*/
#ifndef __COREPLEX_PLATFORM_CFM_H_
#define __COREPLEX_PLATFORM_CFM_H_

#ifdef __cplusplus
extern "C" {
#endif



/* CFM Register base address. */
#define CFM_REG_BASE 0x20006000

/***************************************************************************//**
  The __cfm_count_id_t enumeration is used to identify the channel used.
 */
typedef enum __cfm_count_id
{
    CFM_COUNT_0 = 0,
    CFM_COUNT_1,
    CFM_COUNT_2,
    CFM_COUNT_3,
    CFM_COUNT_4,
    CFM_COUNT_5,
    CFM_COUNT_6,
    CFM_COUNT_7,
    cfm_lastCH,
} cfm_count_id_t;



/***************************************************************************//**
  The cfm_channel_mode enumeration is used to specify the channel mode.
 */
typedef enum __cfm_channel_mode
{
    CFM_CH_DISABLED = 0,
    CFM_CH_FREQUENCY_MODE,
    CFM_CH_RESERVER,
    CFM_CH_TIMER_MODE,
    CFM_CH_lastmd
} cfm_channel_mode;



typedef enum __cfm_error_id_t
{
    CFM_OK = 0,
    ERROR_INVALID_CLK_SELECTION_GROUP,
    ERROR_INVALID_REF_SEL0,
    ERROR_INVALID_REF_SEL1,
    ERROR_INVALID_CHANNEL_DRIVE_CLK_MONITOR,
    ERROR_INVALID_CFM_BUSY,

    ERROR_NULL_VALUE,

    ERROR_CFMLAST_ID
} cfm_error_id_t;


typedef struct _cfmRegs
{
    __IO uint32_t controlReg;           /* CFM Control Register */
    __IO uint32_t clkselReg;            /* Clock Selection Register */
    __IO uint32_t runtimeReg;           /* Reference Count Value */
    __IO uint32_t modelReg;             /* Sets the measurement mode */

    __I  uint32_t count0;               /* Count x value */
    __I  uint32_t count1;
    __I  uint32_t count2;
    __I  uint32_t count3;
    __I  uint32_t count4;
    __I  uint32_t count5;
    __I  uint32_t count6;
    __I  uint32_t count7;

    __I  uint32_t reserved[4];          /*Reserved registers, padding structure */


}CFM;


#define CFM_REG                       ((CFM *)CFM_REG_BASE)

typedef struct _cfmChannelMode
{
    uint8_t channel0;        /* Channel x mode */
    uint8_t channel1;        /* Channel x mode */
    uint8_t channel2;        /* Channel x mode */
    uint8_t channel3;        /* Channel x mode */
    uint8_t channel4;        /* Channel x mode */
    uint8_t channel5;        /* Channel x mode */
    uint8_t channel6;        /* Channel x mode */
    uint8_t channel7;        /* Channel x mode */

}cfmChannelMode;

#define CFM_CONTROL_REG_BUSY_MASK        0x01U
#define CFM_CONTROL_REG_START_MASK       0x01U
#define CFM_CONTROL_REG_STOP_BITS_SHIFT  0x01U

#define CFM_CLK_SEL_MASK                 0x07U


#define CFM_CLK_REFSEL0_MASK             0x01U
#define CFM_CLK_REFSEL0SHIFT             0x04U


#define CFM_CLK_REFSEL1_MASK             0x01U
#define CFM_CLK_REFSEL1SHIFT             0x05U


#define CFM_CLK_MONSEL_MASK              0x07U
#define CFM_CLK_MONSEL_SHIFT             0x08U



#define CFM_CLK_MONEN_MASK               0x01
#define CFM_CLK_MONEN_SHIFT              11U

#define CFM_RUNTIME_REG_MASK             0xFFFFFFU

#define CFM_CHANNEL_MODE_MASK            0x3U

#define CFM_CH0_SHIFT_MASK           0x00U
#define CFM_CH1_SHIFT_MASK           0x02U
#define CFM_CH2_SHIFT_MASK           0x04U
#define CFM_CH3_SHIFT_MASK           0x06U
#define CFM_CH4_SHIFT_MASK           0x08U
#define CFM_CH5_SHIFT_MASK           0x0AU
#define CFM_CH6_SHIFT_MASK           0x0CU
#define CFM_CH7_SHIFT_MASK           0x0EU



/*****************************************************************************
 * CFM Function Prototypes
 *******************************************************************************
 */
/*-------------------------------------------------------------------------*//**
  The MSS_CFM_control_start() function causes the measurement circuitry
  to start. This state of 'busy' will clear which measurement is complete.


  @param None

   @return
    Busy state

  Example:
  The following call will start the CFM
  @code
  MSS_CFM_control_start(  );
  @endcode
 */
uint8_t MSS_CFM_control_start(void);



/*-------------------------------------------------------------------------*//**
  The MSS_CFM_control_stop() function causes the measurement circuitry
  to stop.


  @param None


  @return uint8_t
   Returns the busy flag.


  Example:
  The following call will stop the CFM
  @code
  MSS_CFM_control_stop(  );
  @endcode
 */
uint8_t MSS_CFM_control_stop(void);





/*-------------------------------------------------------------------------*//**
  The MSS_CLF_clk_configuration() function is used to configure the clock
  selection register.

  @param clkSel
    Selects which group of clock inputs are selected by the channels, control
    the input multiplexer.

  @param refsel0
    Selects the reference input, 0=clkref1 / 1=clkref2

  @param refsel1
    When in timer mode allows ATPG (corners) / clkref3 clock input to clock
    the channel counters. This clock input is expected to be sourced from an
    on-chip PLL to support at-speed testing. This allows the timer to clocked
    off a much higher clock frequency that the reference counter that is limited
    to 100Mhz.

  @param monSEL
    Selects which channel drives the clock monitor output 0-7.


  @param monEN
   Enables the clock monitor output.


   @return
    cfm_error_id_t

  Example:
  The following call will configure clk 0, using clkref1, channel zero drives
  the clock monitor and enable the clock monitor output.
  @code
  MSS_GPIO_config( 0, 0, 0, 0, 1 );
  @endcode
 */
cfm_error_id_t MSS_CLF_clk_configuration(
        uint8_t clkSel,
        uint8_t refsel0,
        uint8_t refsel1,
        uint8_t monSEL,
        uint8_t monEN
    );




/*-------------------------------------------------------------------------*//**
  The MSS_CFM_runtime_register() function is used to set how many reference
  clock cycles the frequency and time measurement should be made.
  The register does NOT change during oepration

  @param refcount
    The reference count value.

 */
void MSS_CFM_runtime_register(
        uint32_t  referenceCount
    );



/*-------------------------------------------------------------------------*//**
  The MSS_CFM_channel_mode() function is used to set the measurement mode for
  the specified channel.
   2'b00: Disabled
   2'b01: Frequency Mode
   2'b11: Timer Mode
   2'b10: Reserved

  @param cfmChannelMode
   Configuration structure for each channel

   @return
    None

 */
void MSS_CFM_channel_mode(cfmChannelMode  chMode);


/*-------------------------------------------------------------------------*//**
  The MSS_CFM_get_count() function is used to get the count value.
  Block must not be busy.

  @param ch
     The channel ID to return the count for.

  @param count
      The count for the channel register.

   @return
    cfm_error_id_t

  Example:
  The following call will return the value in count register. channel 0

  @code
  MSS_CFM_get_count();
  @endcode
 */
cfm_error_id_t MSS_CFM_get_count(cfm_count_id_t ch, uint32_t *count);


#ifdef __cplusplus
}
#endif


#endif  /* __COREPLEX_PLATFORM_CFM_H_ */
