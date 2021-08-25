/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 * @file mss_sgmii.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief SGMII defines
 *
 */

#ifndef SRC_PLATFORM_MPFS_HAL_NWC_MSS_SGMII_H_
#define SRC_PLATFORM_MPFS_HAL_NWC_MSS_SGMII_H_

#ifdef __cplusplus
extern "C" {
#endif


#define REG_RX0_EN_OFFSET   (1U<<5U)
#define REG_RX1_EN_OFFSET   (1U<<7U)
#define TX_RX_CH_EN_MASK    0xFU
#define TX_RX_CH_EN_OFFSET  0x4U
#define REG_CDR_MOVE_STEP   (1U<<22U)   /* delay taps 1 => 3 taps moved, 0 => 2 taps move. */
                                        /* 2 taps best for small PPM values, best results observed. */

#define SHIFT_TO_CH0_N_EYE_VALUE    26U /* 26-28 */
#define SHIFT_TO_CH1_N_EYE_VALUE    29U /* 29-31 */
#define N_EYE_MASK                  0x03FFFFFFUL

#define SHIFT_TO_REG_RX0_EYEWIDTH   21U
#define REG_RX0_EYEWIDTH_P_MASK     (~(0x7U<<SHIFT_TO_REG_RX0_EYEWIDTH))
#define SHIFT_TO_REG_RX1_EYEWIDTH   21U
#define REG_RX1_EYEWIDTH_P_MASK     (~(0x7U<<SHIFT_TO_REG_RX1_EYEWIDTH))

#define REG_RX0_EN_FLAG_N   (1U<<31U)
#define REG_RX1_EN_FLAG_N   (1U<<31U)

#if !defined (LIBERO_SETTING_MIN_DLL_90_CODE_VALUE_INDICATING_TT_PART_REVB)
#define MIN_DLL_90_CODE_VALUE_INDICATING_TT_PART_REVB  13
#endif

#define ARO_REF_PCODE_MASK              0x3FUL
#if !defined (ARO_REF_PCODE_REVC_THRESHOLD)
#define ARO_REF_PCODE_REVC_THRESHOLD    0x40U
#endif

/*
 * For Rev B
 * early (P) = 5/ Late (N) = 6
 *
 * e.g.
 *      Channel control0: 0xB7B07770
 *      Channel control1: 0xB7B07770
 *      Spare control:    0xDB002680
 *
 *  early (P) = 6/ Late (N) = 7
 *
 *  e.g.
 *      Channel control0: 0XB7D07770
 *      Channel control1: 0XB7D07770
 *      Spare control:    0XFF002680
 *
 *  Note: N eye width value set in spare control register
 *              bits 31:29 for CH1,
 *              bits 28:26  for CH0
 *
 *  For Rev C
 *    early (P) = 7/ Late (N) = 6
 */

#if !defined (EARLY_EYE_WIDTH_PART_NOT_DETERMINED)
#define EARLY_EYE_WIDTH_PART_PART_NOT_DETERMINED  6U
#endif
#if !defined (START_EARLY_EYE_WIDTH_PART_REVC_OR_LATER)
#define EARLY_EYE_WIDTH_PART_REVC_OR_LATER  6U
#endif
#if !defined (START_EARLY_EYE_WIDTH_PART_REVC_OR_LATER_PRE_TEST)
#define EARLY_EYE_WIDTH_PART_REVC_OR_LATER_PRE_TEST  7U
#endif
#if !defined (EARLY_EYE_WIDTH_SS_PART_REVB)
#define EARLY_EYE_WIDTH_SS_PART_REVB        5U
#endif
#if !defined (EARLY_TT_PART_REVB)
#define EARLY_TT_PART_REVB                  6U
#endif


#if !defined (LATE_EYE_WIDTH_PART_NOT_DETERMINED)
#define LATE_EYE_WIDTH_PART_NOT_DETERMINED  7U
#endif
#if !defined (LATE_EYE_WIDTH_PART_REVC_OR_LATER)
#define LATE_EYE_WIDTH_PART_REVC_OR_LATER  7U
#endif
#if !defined (LATE_EYE_WIDTH_PART_REVC_OR_LATER_PRE_TEST)
#define LATE_EYE_WIDTH_PART_REVC_OR_LATER_PRE_TEST  6U
#endif
#if !defined (LATE_EYE_WIDTH_SS_PART_REVB)
#define LATE_EYE_WIDTH_SS_PART_REVB        6U
#endif
#if !defined (LATE_TT_PART_REVB)
#define LATE_TT_PART_REVB                  7U
#endif


typedef enum PART_TYPE_
{
    PART_NOT_DETERMINED             = 0x00,       /*!< 0 default setting */
    PART_REVC_OR_LATER              = 0x01,       /*!< 1 rev c or later  */
    SS_PART_REVB                    = 0x02,       /*!< 2 SS part rev. B  */
    TT_PART_REVB                    = 0x03,       /*!< 3 TT part rev. B  */
    PART_TYPE_ARRAY_SIZE            = 0x04,       /*!< 4 array size  */
}   PART_TYPE;

/**
 * \brief bank control sgmii SCB regs
 */
typedef struct IOSCB_BANK_CNTL_SGMII_ {
                                    /* bit0 - This when asserted resets all the non-volatile register bits e.g. RW-P bits, the bit self clears i.e. is similar to a W1P bit */
                                    /* bit1 - This when asserted resets all the register bits apart from the non-volatile registers, the bit self clears. i.e. is similar to a W1P bit */
    __IO uint32_t soft_reset;       /* bit8 - This asserts the functional reset of the block. It is asserted at power up. When written is stays asserted until written to 0.       */

    __IO uint32_t dpc_bits;         /* DPC Bits Register            */
    __IO uint32_t bank_status;      /* Bank Complete Registers      */
} IOSCB_BANK_CNTL_SGMII_STRUCT;


#define IOSCB_BANK_CNTL_SGMII_BASE  0x3E400000UL
#define IOSCB_BANK_CNTL_SGMII  ((volatile IOSCB_BANK_CNTL_SGMII_STRUCT *) IOSCB_BANK_CNTL_SGMII_BASE)


/**
 * \brief dll sgmii SCB regs
 */
typedef struct IOSCB_DLL_SGMII_ {
                                    /* bit0 - This when asserted resets all the non-volatile register bits e.g. RW-P bits, the bit self clears i.e. is similar to a W1P bit */
                                    /* bit1 - This when asserted resets all the register bits apart from the non-volatile registers, the bit self clears. i.e. is similar to a W1P bit */
    __IO uint32_t soft_reset;       /* bit8 - This asserts the functional reset of the block. It is asserted at power up. When written is stays asserted until written to 0.       */

    __IO uint32_t dll_ctrl0;         /* DPC Bits Register            */
    __IO uint32_t dll_ctrl1;         /* DPC Bits Register            */
    __IO uint32_t dll_stat0;         /* DLL control register 0       */
    __IO uint32_t dll_stat1;         /* DLL control register 1       */
    __IO uint32_t dll_stat2;         /* DLL control register 2       */
} IOSCB_DLL_SGMII_STRUCT;


#define IOSCB_DLL_SGMII_BASE  0x3E100000UL
#define IOSCB_DLL_SGMII  ((volatile IOSCB_DLL_SGMII_STRUCT *) IOSCB_DLL_SGMII_BASE)


/**
 * \brief gmiiphy_lanexx
 */
typedef struct SGMIIPHY_LANE01_ {
                                     /* bit0 - This when asserted resets all the non-volatile register bits e.g. RW-P bits, the bit self clears i.e. is similar to a W1P bit */
                                     /* bit1 - This when asserted resets all the register bits apart from the non-volatile registers, the bit self clears. i.e. is similar to a W1P bit */
    __IO uint32_t soft_reset;        /* bit8 - This asserts the functional reset of the block. It is asserted at power up. When written is stays asserted until written to 0.       */

    __IO uint32_t BNK_CLK_SEL;       /*             */
    __IO uint32_t dll_ctrl1;         /*             */
    __IO uint32_t dll_stat0;         /*             */
    __IO uint32_t dll_stat1;         /*             */
    __IO uint32_t dll_stat2;         /*             */
} IOSCB_SGMIIPHY_LANE01_STRUCT;

#define SGMIIPHY_LANE01_BASE  0x36500000UL
#define SGMIIPHY_LANE23_BASE  0x36510000UL
#define SGMIIPHY_LANE01  ((volatile IOSCB_SGMIIPHY_LANE01_STRUCT *) SGMIIPHY_LANE01_BASE)
#define SGMIIPHY_LANE23  ((volatile IOSCB_SGMIIPHY_LANE01_STRUCT *) SGMIIPHY_LANE23_BASE)


/**
 * \brief GEM_A_LO GEM_B_LO
 */
typedef struct IOSCB_GEM_X_LO_STRUCT_ {
    __IO uint32_t network_control;      /* The network configuration register contains functions for setting the mode of operation for the Gigabit Ethernet MAC.  */
    __IO uint32_t network_config;       /*             */
    __IO uint32_t network_status;       /*             */
    __IO uint32_t dma_config;           /*             */
    __IO uint32_t transmit_status;      /*             */
    __IO uint32_t receive_q_ptr;        /*             */
} IOSCB_GEM_X_LO_STRUCT;

#define GEM_A_LO_BASE  0x20110004UL
#define GEM_B_LO_BASE  0x20112004UL
#define GEM_A_LO  ((volatile IOSCB_GEM_X_LO_STRUCT *) GEM_A_LO_BASE)
#define GEM_B_LO  ((volatile IOSCB_GEM_X_LO_STRUCT *) GEM_B_LO_BASE)

/***************************************************************************//**

 */
typedef enum SGMII_TRAINING_SM_
{
    SGMII_SETUP_INIT,                            /*!< SGMII_TRAINING_INIT */
    SGMII_IO_EN,
    SGMII_RAMP_TIMER,
    SGMII_IO_SETUP,
    SGMII_WAIT_FOR_CALIB_COMPLETE,
    SGMII_ASSERT_CALIB_LOCK,
    SGMII_SET_UP_PLL,
    SGMII_WAIT_FOR_MSS_LOCK,
    SGMII_WAIT_FOR_DLL_LOCK,
    SGMII_TURN_ON_MACS,
    SGMII_DETERMINE_SILICON_VARIANT,
    SGMII_RESET_CHANNELS,
    SGMII_WAIT_10MS,
    SGMII_CHECK_REVC_RESULT,
    SGMII_CHANNELS_UP
} SGMII_TRAINING_SM;

#define SGMII_FINISHED_SETUP    0U
#define SGMII_IN_SETUP          1U



/***************************************************************************//**
  sgmii_off_mode() called in sgmii channels are not being used.

  Example:
  @code

      sgmii_off_mode();

  @endcode

 */
void sgmii_off_mode(void);

/***************************************************************************//**
  sgmii_setup() sets up the SGMII using settings from Libero

  Example:
  @code

      sgmii_setup();

  @endcode

 */
uint32_t sgmii_setup(void);

/***************************************************************************//**
  ddr_pvt_calibration() calibrates DDR I/O using the hardware function

  @return
    This function returns status, see DDR_SS_STATUS enum

  Example:
  @code

      ddr_pvt_calibration();

  @endcode

 */
void
ddr_pvt_calibration
(
    void
);

/***************************************************************************//**
  ddr_pvt_recalibration() recalibrates DDR I/O using the hardware function


  Example:
  @code

      ddr_pvt_recalibration();

  @endcode

 */
void ddr_pvt_recalibration(void);

#ifdef __cplusplus
}
#endif

#endif /* SRC_PLATFORM_MPFS_HAL_NWC_MSS_SGMII_H_ */
