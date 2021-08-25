/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 * @file mss_pll.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief PLL defines
 *
 */

/*=========================================================================*//**
  @page PolarFire SoC MSS Clock Setup
  ==============================================================================
  Introduction
  ==============================================================================
  The PolarFire SoC Microprocessor subsystem (MSS) has three PLL's, the MSS, DDR
  and MSS SGMII's.
  Two CFM IP blocks are used to mux the PLL input and outputs.

  ==============================================================================
  PLL Inputs
  ==============================================================================
  Each of the three PLL's can be configured with the following inputs:
    - VSS ( default on reset )
    - external ref clock in SGMII IO Block
    - SCB Clock (80MHz)
    - North West corner clock mux structure ICB

  There are two bits associated with setting clk source

  Note on North West corner clock mux structure ICB
  The Fabric reference clock inputs source come from the clock mux's in the
  upper  left corner (regular FPGA corner) that provided clocks that can be
  routed in from various places that will include from IOs, from the FPGA
  fabric, etc.



  ==============================================================================
  MSS PLL Outputs
  ==============================================================================
  Each PLL has four outputs. These are generally gated through a mux
  MSS PLL Outputs

    | Output(0-3)   |    Detail     | Mux           | Muxed with  |
    | ------------- |:-------------:|:-------------:| -----------:|
    | msspll_fdr_0  | clk_in_mss    | no            | -           |
    | msspll_fdr_1  | clk_in_crypto | no            | -           |
    | msspll_fdr_2  | clk_in_emmc   | glitch-less   | SCB clk     |
    | msspll_fdr_3  | clk_in_can    | glitch-less   | SCB clk     |

  ==============================================================================
  SCB bus timing
  ==============================================================================
  When the MSS is using the SCB bus, there is a timing relationship.
  The defaults should be OK here. In necessary, the timing used by the MSS SCB
  access is adjusted using the MSS system register TIMER.
  (SCBCFG_REGS->TIMER.TIMER)
      - Bits 15:8 Sets how long SCB request is held active after SCB bus granted.
      - Allows SCB bus master-ship to maintained across multiple SCB access
        cycles
      - Bits 7:0 Set the timeout for an SCB access in CPU cycles.

  ==============================================================================
  eNVM timing
  ==============================================================================
  The clk used by the eNVM is adjusted using the following register:
  SYSREG->ENVM_CR
     [5:0]
     Sets the number of AHB cycles used to generate the PNVM clock,.
     Clock period = (Value+1) * (1000/AHBFREQMHZ)
     Value must be 1 to 63 (0 defaults to 15)
     e.g.
     11 will generate a 40ns period 25MHz clock if the AHB clock is 250MHz
     15 will generate a 40ns period 25MHz clock if the AHB clock is 400MHz

  ==============================================================================
  MSS clocks at reset
  ==============================================================================
  When the MSS comes out of reset, the MSS will be running on the SCB supplied
  80MHz clock.



  ==============================================================================
  MSS clock setup - Use case one - using external reference from SGMII I/O Blk
  ==============================================================================
  Use case one will be used in the majority of cases.
  This is where the MSS PLL reference clk will be supplied from an external
  reference through the external ref clock in SGMII IO Block.


                                                 scb clk
                     01=>ext clk ref             +
                      +----------+   +--------+  |  0=>SCB
                  crn |          |   |  MSS   |  |  1=>PLL
                 +--->|          |   |  PLL   |  | +------+
     +-----+      scb |          |   |        |  +>|      |mss
     |     |     +----           |   |        |    | mux  +-->
     | ext + p        |  mux     +-->|ref0   0+--->|      |clk
     | clk +--------->|          |   |        |    +------+
     | ref | n    vss |          |   |        |     0=>SCB
     |     +---+    ->|          |   |        |     1=>PLL
     |     |   |      |          |   |        |    +------+
     |     |   |      |          |   |        |scb-|      |crypto
     +-----+   |      +----------+   |        |    | mux  +-->
               |                     |       1+--->|      |clk
               |    01=>ext clk ref  |        |    +------+
               |      +----------+   |        |
               |   crn|          |   |        |    +------+
               |  +-->|          |   |        |    |      |
               |   scb|          |   |       2+--->| eMMC +
               |  +-->|          |   |        |    |      |
               |      |  mux     +-->|ref1    |    +------+
               +----->|          |   |        |
                   vss|          |   |        |    +------+
                  +-->|          |   |        |    |      |
                      |          |   |       3+--->| CAN  +
                      |          |   |        |    |      |
                      +----------+   +--------+    +------+

  Steps to setup ext clk:
  1. The external clock reference is setup- In SGMII setup
  2. The input mux is set to take input from ext ref clk
  3. MSS PLL clock is setup with required settings
  4. PLL is checked until locked
  5. MSS PLL output is switched through to MSS ( switch code run from ram )
  6. eNVM clcock is changed as required
  7. return from RAM routine and continue

  ==============================================================================
  MSS clock dividers
  ==============================================================================
  The three dividers generating the MSS master clocks are controllable via the
  system register (CLOCK_CONFIG_CR).
  CPU clock dividers are set in the function  mss_mux_post_mss_pll_config(void)

    | Divider       | Config bits   | Reset      | MAX feq. *  |
    | ------------- |:-------------:|:----------:| -----------:|
    | CPU           | 1:0           | 00         | 625         |
    | AXI           | 3:2           | 01         | 312.5       |
    | AHB/APB       | 5:4           | 10         | 156.25      |

  settings = 00=/1, 01=/2, 01=/4, 01=/8
  * verify MAX feq. setting with particular silicon variant data sheet
   - The CPU clock must not exceed 625MHz
   - The AXI clock  must not exceed 312.5MHz
   - The AHB clock must not exceed 156.25MHz
   - The CPU clock must be greater or equal to the AXI clock
   - The AHB/APB clocks cannot be divided by 1. Divide by 1 will divide the
     clock by 2.
   - The clock divider register may be changed from any value to any value in
     one go.
   - When the USB block is in-use the AHB clock must be greater than 66 MHz.


                          +---------------------+          +-------------+
                          |      +----------+   |          |             |
                          |   +--> /1/2/4/8 +-->+--------->|   CPU cores |
    +-----------+         |   |  +----------+   |          |             |
    |           |         |   |                 |          +-------------+
    |  MSS CLK  |         |   |                 |
    |           |         |   |                 |          +-------------+
    |           +---------+---+  +---------+    |          | dfi_apb_pclk|
    |           |         |   +->|/4/8/16  +--->+---------->             |
    |           |         |   |  +---------+    |          |             |
    |           |         |   |                 |          +-------------+
    +-----------+         |   |                 |
                          |   |                 |
                          |   |                 |          +-------------+
                          |   |  +---------+    |          | MSS AXI     |
                          |   +--> 1/2/4/8 +--->+--------->| Buses and   |
                          |   |  +---------+    |          | peripherals |
                          |   |                 |          +-------------+
                          |   |                 |
                          |   |                 |
                          |   |                 |          +-------------+
                          |   |  +-------+      |          | MSS APB/AHB |
                          |   +->| 2/4/8 +----->+--------->| Buses and
                          |      +-------+      |          | peripherals |
                          +---------------------+          +-------------+


 *//*=========================================================================*/
#ifndef MSS_DDR_SGMII_MSS_PLL_H_
#define MSS_DDR_SGMII_MSS_PLL_H_

#ifdef __cplusplus
extern "C" {
#endif

#define PLL_CTRL_LOCK_BIT ((0x01U) << 25U)
/*
 * bit0 1: This when asserted resets all the non-volatile register  bits
 *         e.g. RW-P bits, the bit self clears i.e. is similar to a W1P bit
 * bit1 1: This when asserted resets all the register  bits apart from the
 *         non-volatile registers,  the bit self clears.  i.e. is similar to a
 *         W1P bit
 */
#define PLL_INIT_AND_OUT_OF_RESET               0x00000003UL

#define PLL_CTRL_REG_POWERDOWN_B_MASK           0x00000001UL

typedef enum RTC_CLK_SOURCE_
{
    SCB_80M_CLOCK                   = 0x00,       /*!< 0 SCB clock source */
    MSS_PLL_CLOCK                   = 0x01,       /*!< 1 MSS PLL clock source */
}   RTC_CLK_SOURCE;

typedef enum REG_LOAD_METHOD_
{
    SCB_UPDATE                   = 0x00,       /*!< 0 SCB direct load */
    RPC_REG_UPDATE               = 0x01,       /*!< 1 RPC -> SCB load */
}   REG_LOAD_METHOD;



/***************************************************************************//**
  ddr_pll_config() configure DDR PLL

  Example:
  @code

      ddr_pll_config();

  @endcode

 */
void ddr_pll_config(REG_LOAD_METHOD option);

/***************************************************************************//**
  ddr_pll_lock_scb() Checks if PLL locked

  @return
    0U if locked

  Example:
  @code
      if (ddr_pvt_calibration() == 0U)
      {
           PLL is locked
      }
  @endcode

 */
uint8_t ddr_pll_lock_scb(void);

/***************************************************************************//**
  sgmii_pll_config_scb() configure sgmii PLL

   @param option 1 => soft reset, load RPC settings
                 0 => write values using SCB

  Example:
  @code

      sgmii_pll_config_scb(1U);

  @endcode

 */
void sgmii_pll_config_scb(uint8_t option);

/***************************************************************************//**
  sgmii_pll_lock_scb() Checks if PLL is locked

   @return
    0U if locked

  Example:
  @code
      if (ddr_pvt_calibration() == 0U)
      {
           PLL is locked
      }
  @endcode

 */
uint8_t sgmii_pll_lock_scb(void);

/***************************************************************************//**
  ddr_pll_config_scb_turn_off() Puts PLL in reset

  Example:
  @code

      ddr_pll_config_scb_turn_off();

  @endcode

 */
void ddr_pll_config_scb_turn_off(void);

/***************************************************************************//**
  set_RTC_divisor() Sets the RTC divisor based on values from Libero
  It is assumed the RTC clock is set to 1MHz
  Example:
  @code

      set_RTC_divisor();

  @endcode

 */
void set_RTC_divisor(void);

/***************************************************************************//**
  sgmii_mux_config_via_scb() configures mux for SGMii

  Example:
  @code

      sgmii_mux_config_via_scb();

  @endcode

 */
void sgmii_mux_config_via_scb(uint8_t option);

/***************************************************************************//**
  pre_configure_sgmii_and_ddr_pll_via_scb()

  @param option 1 => soft reset, load RPC settings
                0 => write values using SCB

  Example:
  @code

      ddr_pvt_calibration(1U);

  @endcode

 */
void pre_configure_sgmii_and_ddr_pll_via_scb(uint8_t option);

/******************************************************************************
 * Public Functions - API                                                      *
 ******************************************************************************/
void mss_pll_config(void);

#ifdef __cplusplus
}
#endif

#endif /* MSS_DDR_SGMII_MSS_PLL_H_ */
