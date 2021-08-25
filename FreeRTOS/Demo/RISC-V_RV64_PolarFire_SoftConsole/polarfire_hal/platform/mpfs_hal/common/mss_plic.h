/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 *
 * @file mss_plic.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief PolarFire SoC MSS PLIC and PRCI access data structures and functions.
 *
 * Definitions and functions associated with PLIC interrupts.
 *
 */
#ifndef MSS_PLIC_H
#define MSS_PLIC_H

#include <stdint.h>
#ifndef CONFIG_OPENSBI
#include "encoding.h"
#endif

#include "mss_assert.h"

#ifdef __cplusplus
extern "C" {
#endif

/*
 *Return value from External IRQ handler. This will be used to disable the
 *Return External interrupt.
 */
#define EXT_IRQ_KEEP_ENABLED                                0U
#define EXT_IRQ_DISABLE                                     1U

/*------------------------------------------------------------------------------
 *
 */
#ifndef SIFIVE_HIFIVE_UNLEASHED
uint8_t  Invalid_IRQHandler(void);
uint8_t  l2_metadata_corr_IRQHandler(void);
uint8_t  l2_metadata_uncorr_IRQHandler(void);
uint8_t  l2_data_corr_IRQHandler(void);
uint8_t  l2_data_uncorr_IRQHandler(void);
uint8_t  dma_ch0_DONE_IRQHandler(void);
uint8_t  dma_ch0_ERR_IRQHandler(void);
uint8_t  dma_ch1_DONE_IRQHandler(void);
uint8_t  dma_ch1_ERR_IRQHandler(void);
uint8_t  dma_ch2_DONE_IRQHandler(void);
uint8_t  dma_ch2_ERR_IRQHandler(void);
uint8_t  dma_ch3_DONE_IRQHandler(void);
uint8_t  dma_ch3_ERR_IRQHandler(void);
uint8_t  gpio0_bit0_or_gpio2_bit13_plic_0_IRQHandler(void);
uint8_t  gpio0_bit1_or_gpio2_bit13_plic_1_IRQHandler(void);
uint8_t  gpio0_bit2_or_gpio2_bit13_plic_2_IRQHandler(void);
uint8_t  gpio0_bit3_or_gpio2_bit13_plic_3_IRQHandler(void);
uint8_t  gpio0_bit4_or_gpio2_bit13_plic_4_IRQHandler(void);
uint8_t  gpio0_bit5_or_gpio2_bit13_plic_5_IRQHandler(void);
uint8_t  gpio0_bit6_or_gpio2_bit13_plic_6_IRQHandler(void);
uint8_t  gpio0_bit7_or_gpio2_bit13_plic_7_IRQHandler(void);
uint8_t  gpio0_bit8_or_gpio2_bit13_plic_8_IRQHandler(void);
uint8_t  gpio0_bit9_or_gpio2_bit13_plic_9_IRQHandler(void);
uint8_t  gpio0_bit10_or_gpio2_bit13_plic_10_IRQHandler(void);
uint8_t  gpio0_bit11_or_gpio2_bit13_plic_11_IRQHandler(void);
uint8_t  gpio0_bit12_or_gpio2_bit13_plic_12_IRQHandler(void);

uint8_t  gpio0_bit13_or_gpio2_bit13_plic_13_IRQHandler(void);
uint8_t  gpio1_bit0_or_gpio2_bit14_plic_14_IRQHandler(void);
uint8_t  gpio1_bit1_or_gpio2_bit15_plic_15_IRQHandler(void);
uint8_t  gpio1_bit2_or_gpio2_bit16_plic_16_IRQHandler(void);
uint8_t  gpio1_bit3_or_gpio2_bit17_plic_17_IRQHandler(void);
uint8_t  gpio1_bit4_or_gpio2_bit18_plic_18_IRQHandler(void);
uint8_t  gpio1_bit5_or_gpio2_bit19_plic_19_IRQHandler(void);
uint8_t  gpio1_bit6_or_gpio2_bit20_plic_20_IRQHandler(void);
uint8_t  gpio1_bit7_or_gpio2_bit21_plic_21_IRQHandler(void);
uint8_t  gpio1_bit8_or_gpio2_bit22_plic_22_IRQHandler(void);
uint8_t  gpio1_bit9_or_gpio2_bit23_plic_23_IRQHandler(void);
uint8_t  gpio1_bit10_or_gpio2_bit24_plic_24_IRQHandler(void);
uint8_t  gpio1_bit11_or_gpio2_bit25_plic_25_IRQHandler(void);
uint8_t  gpio1_bit12_or_gpio2_bit26_plic_26_IRQHandler(void);
uint8_t  gpio1_bit13_or_gpio2_bit27_plic_27_IRQHandler(void);

uint8_t  gpio1_bit14_or_gpio2_bit28_plic_28_IRQHandler(void);
uint8_t  gpio1_bit15_or_gpio2_bit29_plic_29_IRQHandler(void);
uint8_t  gpio1_bit16_or_gpio2_bit30_plic_30_IRQHandler(void);
uint8_t  gpio1_bit17_or_gpio2_bit31_plic_31_IRQHandler(void);

uint8_t  gpio1_bit18_plic_32_IRQHandler(void);
uint8_t  gpio1_bit19_plic_33_IRQHandler(void);
uint8_t  gpio1_bit20_plic_34_IRQHandler(void);
uint8_t  gpio1_bit21_plic_35_IRQHandler(void);
uint8_t  gpio1_bit22_plic_36_IRQHandler(void);
uint8_t  gpio1_bit23_plic_37_IRQHandler(void);

uint8_t  gpio0_non_direct_plic_IRQHandler(void);
uint8_t  gpio1_non_direct_plic_IRQHandler(void);
uint8_t  gpio2_non_direct_plic_IRQHandler(void);

uint8_t  spi0_plic_IRQHandler(void);
uint8_t  spi1_plic_IRQHandler(void);
uint8_t  external_can0_plic_IRQHandler(void);
uint8_t  can1_IRQHandler(void);
uint8_t  External_i2c0_main_plic_IRQHandler(void);
uint8_t  External_i2c0_alert_plic_IRQHandler(void);
uint8_t  i2c0_sus_plic_IRQHandler(void);
uint8_t  i2c1_main_plic_IRQHandler(void);
uint8_t  i2c1_alert_plic_IRQHandler(void);
uint8_t  i2c1_sus_plic_IRQHandler(void);
uint8_t  mac0_int_plic_IRQHandler(void);
uint8_t  mac0_queue1_plic_IRQHandler(void);
uint8_t  mac0_queue2_plic_IRQHandler(void);
uint8_t  mac0_queue3_plic_IRQHandler(void);
uint8_t  mac0_emac_plic_IRQHandler(void);
uint8_t  mac0_mmsl_plic_IRQHandler(void);
uint8_t  mac1_int_plic_IRQHandler(void);
uint8_t  mac1_queue1_plic_IRQHandler(void);
uint8_t  mac1_queue2_plic_IRQHandler(void);
uint8_t  mac1_queue3_plic_IRQHandler(void);
uint8_t  mac1_emac_plic_IRQHandler(void);
uint8_t  mac1_mmsl_plic_IRQHandler(void);
uint8_t  ddrc_train_plic_IRQHandler(void);
uint8_t  scb_interrupt_plic_IRQHandler(void);
uint8_t  ecc_error_plic_IRQHandler(void);
uint8_t  ecc_correct_plic_IRQHandler(void);
uint8_t  rtc_wakeup_plic_IRQHandler(void);
uint8_t  rtc_match_plic_IRQHandler(void);
uint8_t  timer1_plic_IRQHandler(void);
uint8_t  timer2_plic_IRQHandler(void);
uint8_t  envm_plic_IRQHandler(void);
uint8_t  qspi_plic_IRQHandler(void);
uint8_t  usb_dma_plic_IRQHandler(void);
uint8_t  usb_mc_plic_IRQHandler(void);
uint8_t  mmc_main_plic_IRQHandler(void);
uint8_t  mmc_wakeup_plic_IRQHandler(void);
uint8_t  mmuart0_plic_77_IRQHandler(void);
uint8_t  mmuart1_plic_IRQHandler(void);
uint8_t  mmuart2_plic_IRQHandler(void);
uint8_t  mmuart3_plic_IRQHandler(void);
uint8_t  mmuart4_plic_IRQHandler(void);
uint8_t  g5c_devrst_plic_IRQHandler(void);
uint8_t  g5c_message_plic_IRQHandler(void);
uint8_t  usoc_vc_interrupt_plic_IRQHandler(void);
uint8_t  usoc_smb_interrupt_plic_IRQHandler(void);
uint8_t  e51_0_Maintence_plic_IRQHandler(void);

uint8_t  wdog0_mvrp_plic_IRQHandler(void);
uint8_t  wdog1_mvrp_plic_IRQHandler(void);
uint8_t  wdog2_mvrp_plic_IRQHandler(void);
uint8_t  wdog3_mvrp_plic_IRQHandler(void);
uint8_t  wdog4_mvrp_plic_IRQHandler(void);
uint8_t  wdog0_tout_plic_IRQHandler(void);
uint8_t  wdog1_tout_plic_IRQHandler(void);
uint8_t  wdog2_tout_plic_IRQHandler(void);
uint8_t  wdog3_tout_plic_IRQHandler(void);
uint8_t  wdog4_tout_plic_IRQHandler(void);
uint8_t  g5c_mss_spi_plic_IRQHandler(void);
uint8_t  volt_temp_alarm_plic_IRQHandler(void);

uint8_t  athena_complete_plic_IRQHandler(void);
uint8_t  athena_alarm_plic_IRQHandler(void);
uint8_t  athena_bus_error_plic_IRQHandler(void);
uint8_t  usoc_axic_us_plic_IRQHandler(void);
uint8_t  usoc_axic_ds_plic_IRQHandler(void);

uint8_t  reserved_104_plic_IRQHandler(void);

uint8_t  fabric_f2h_0_plic_IRQHandler(void);
uint8_t  fabric_f2h_1_plic_IRQHandler(void);
uint8_t  fabric_f2h_2_plic_IRQHandler(void);
uint8_t  fabric_f2h_3_plic_IRQHandler(void);
uint8_t  fabric_f2h_4_plic_IRQHandler(void);
uint8_t  fabric_f2h_5_plic_IRQHandler(void);
uint8_t  fabric_f2h_6_plic_IRQHandler(void);
uint8_t  fabric_f2h_7_plic_IRQHandler(void);
uint8_t  fabric_f2h_8_plic_IRQHandler(void);
uint8_t  fabric_f2h_9_plic_IRQHandler(void);

uint8_t  fabric_f2h_10_plic_IRQHandler(void);
uint8_t  fabric_f2h_11_plic_IRQHandler(void);
uint8_t  fabric_f2h_12_plic_IRQHandler(void);
uint8_t  fabric_f2h_13_plic_IRQHandler(void);
uint8_t  fabric_f2h_14_plic_IRQHandler(void);
uint8_t  fabric_f2h_15_plic_IRQHandler(void);
uint8_t  fabric_f2h_16_plic_IRQHandler(void);
uint8_t  fabric_f2h_17_plic_IRQHandler(void);
uint8_t  fabric_f2h_18_plic_IRQHandler(void);
uint8_t  fabric_f2h_19_plic_IRQHandler(void);

uint8_t  fabric_f2h_20_plic_IRQHandler(void);
uint8_t  fabric_f2h_21_plic_IRQHandler(void);
uint8_t  fabric_f2h_22_plic_IRQHandler(void);
uint8_t  fabric_f2h_23_plic_IRQHandler(void);
uint8_t  fabric_f2h_24_plic_IRQHandler(void);
uint8_t  fabric_f2h_25_plic_IRQHandler(void);
uint8_t  fabric_f2h_26_plic_IRQHandler(void);
uint8_t  fabric_f2h_27_plic_IRQHandler(void);
uint8_t  fabric_f2h_28_plic_IRQHandler(void);
uint8_t  fabric_f2h_29_plic_IRQHandler(void);

uint8_t  fabric_f2h_30_plic_IRQHandler(void);
uint8_t  fabric_f2h_31_plic_IRQHandler(void);

uint8_t  fabric_f2h_32_plic_IRQHandler(void);
uint8_t  fabric_f2h_33_plic_IRQHandler(void);
uint8_t  fabric_f2h_34_plic_IRQHandler(void);
uint8_t  fabric_f2h_35_plic_IRQHandler(void);
uint8_t  fabric_f2h_36_plic_IRQHandler(void);
uint8_t  fabric_f2h_37_plic_IRQHandler(void);
uint8_t  fabric_f2h_38_plic_IRQHandler(void);
uint8_t  fabric_f2h_39_plic_IRQHandler(void);
uint8_t  fabric_f2h_40_plic_IRQHandler(void);
uint8_t  fabric_f2h_41_plic_IRQHandler(void);

uint8_t fabric_f2h_42_plic_IRQHandler(void);
uint8_t fabric_f2h_43_plic_IRQHandler(void);
uint8_t fabric_f2h_44_plic_IRQHandler(void);
uint8_t fabric_f2h_45_plic_IRQHandler(void);
uint8_t fabric_f2h_46_plic_IRQHandler(void);
uint8_t fabric_f2h_47_plic_IRQHandler(void);
uint8_t fabric_f2h_48_plic_IRQHandler(void);
uint8_t fabric_f2h_49_plic_IRQHandler(void);
uint8_t fabric_f2h_50_plic_IRQHandler(void);
uint8_t fabric_f2h_51_plic_IRQHandler(void);

uint8_t fabric_f2h_52_plic_IRQHandler(void);
uint8_t fabric_f2h_53_plic_IRQHandler(void);
uint8_t fabric_f2h_54_plic_IRQHandler(void);
uint8_t fabric_f2h_55_plic_IRQHandler(void);
uint8_t fabric_f2h_56_plic_IRQHandler(void);
uint8_t fabric_f2h_57_plic_IRQHandler(void);
uint8_t fabric_f2h_58_plic_IRQHandler(void);
uint8_t fabric_f2h_59_plic_IRQHandler(void);
uint8_t fabric_f2h_60_plic_IRQHandler(void);
uint8_t fabric_f2h_61_plic_IRQHandler(void);

uint8_t fabric_f2h_62_plic_IRQHandler(void);
uint8_t fabric_f2h_63_plic_IRQHandler(void);

uint8_t bus_error_unit_hart_0_plic_IRQHandler(void);
uint8_t bus_error_unit_hart_1_plic_IRQHandler(void);
uint8_t bus_error_unit_hart_2_plic_IRQHandler(void);
uint8_t bus_error_unit_hart_3_plic_IRQHandler(void);
uint8_t bus_error_unit_hart_4_plic_IRQHandler(void);


#else
uint8_t Invalid_IRQHandler(void);
uint8_t External_1_IRQHandler(void);
uint8_t External_2_IRQHandler(void);
uint8_t External_3_IRQHandler(void);
uint8_t USART0_plic_4_IRQHandler(void);
uint8_t External_5_IRQHandler(void);
uint8_t External_6_IRQHandler(void);
uint8_t External_7_IRQHandler(void);
uint8_t External_8_IRQHandler(void);
uint8_t External_9_IRQHandler(void);
uint8_t External_10_IRQHandler(void);
uint8_t External_11_IRQHandler(void);
uint8_t External_12_IRQHandler(void);
uint8_t External_13_IRQHandler(void);
uint8_t External_14_IRQHandler(void);
uint8_t External_15_IRQHandler(void);
uint8_t External_16_IRQHandler(void);
uint8_t External_17_IRQHandler(void);
uint8_t External_18_IRQHandler(void);
uint8_t External_19_IRQHandler(void);
uint8_t External_20_IRQHandler(void);
uint8_t External_21_IRQHandler(void);
uint8_t External_22_IRQHandler(void);
uint8_t dma_ch0_DONE_IRQHandler(void);
uint8_t dma_ch0_ERR_IRQHandler(void);
uint8_t dma_ch1_DONE_IRQHandler(void);
uint8_t dma_ch1_ERR_IRQHandler(void);
uint8_t dma_ch2_DONE_IRQHandler(void);
uint8_t dma_ch2_ERR_IRQHandler(void);
uint8_t dma_ch3_DONE_IRQHandler(void);
uint8_t dma_ch3_ERR_IRQHandler(void);
uint8_t External_31_IRQHandler(void);
uint8_t External_32_IRQHandler(void);
uint8_t External_33_IRQHandler(void);
uint8_t External_34_IRQHandler(void);
uint8_t External_35_IRQHandler(void);
uint8_t External_36_IRQHandler(void);
uint8_t External_37_IRQHandler(void);
uint8_t External_38_IRQHandler(void);
uint8_t External_39_IRQHandler(void);
uint8_t External_40_IRQHandler(void);
uint8_t External_41_IRQHandler(void);
uint8_t External_42_IRQHandler(void);
uint8_t External_43_IRQHandler(void);
uint8_t External_44_IRQHandler(void);
uint8_t External_45_IRQHandler(void);
uint8_t External_46_IRQHandler(void);
uint8_t External_47_IRQHandler(void);
uint8_t External_48_IRQHandler(void);
uint8_t External_49_IRQHandler(void);
uint8_t External_50_IRQHandler(void);
uint8_t External_51_IRQHandler(void);
uint8_t External_52_IRQHandler(void);
uint8_t MAC0_plic_53_IRQHandler(void);

#endif

/***************************************************************************//**
 * PLIC source Interrupt numbers:
 */
/* See section on PLIC Interrupt Sources in User Guide */
#define OFFSET_TO_MSS_GLOBAL_INTS 13U
typedef enum
{
#ifndef SIFIVE_HIFIVE_UNLEASHED
    INVALID_IRQn                 = 0,
    L2_METADATA_CORR_IRQn        = 1,
    L2_METADAT_UNCORR_IRQn       = 2,
    L2_DATA_CORR_IRQn            = 3,
    L2_DATA_UNCORR_IRQn          = 4,
    DMA_CH0_DONE_IRQn            = 5,
    DMA_CH0_ERR_IRQn             = 6,
    DMA_CH1_DONE_IRQn            = 7,
    DMA_CH1_ERR_IRQn             = 8,
    DMA_CH2_DONE_IRQn            = 9,
    DMA_CH2_ERR_IRQn             = 10,
    DMA_CH3_DONE_IRQn            = 11,
    DMA_CH3_ERR_IRQn             = 12,
    /* see GPIO Interrupt Multiplexing in the User Guide */
    GPIO0_BIT0_or_GPIO2_BIT0_PLIC_0         = 0 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO0_BIT1_or_GPIO2_BIT1_PLIC_1         = 1 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO0_BIT2_or_GPIO2_BIT2_PLIC_2         = 2 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO0_BIT3_or_GPIO2_BIT3_PLIC_3         = 3 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO0_BIT4_or_GPIO2_BIT4_PLIC_4         = 4 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO0_BIT5_or_GPIO2_BIT5_PLIC_5         = 5 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO0_BIT6_or_GPIO2_BIT6_PLIC_6         = 6 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO0_BIT7_or_GPIO2_BIT7_PLIC_7         = 7 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO0_BIT8_or_GPIO2_BIT8_PLIC_8         = 8 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO0_BIT9_or_GPIO2_BIT9_PLIC_9         = 9 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO0_BIT10_or_GPIO2_BIT10_PLIC_10      = 10 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO0_BIT11_or_GPIO2_BIT11_PLIC_11      = 11 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO0_BIT12_or_GPIO2_BIT12_PLIC_12      = 12 + OFFSET_TO_MSS_GLOBAL_INTS,

    GPIO0_BIT13_or_GPIO2_BIT13_PLIC_13      = 13 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT0_or_GPIO2_BIT14_PLIC_14       = 14 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT1_or_GPIO2_BIT15_PLIC_15       = 15 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT2_or_GPIO2_BIT16_PLIC_16       = 16 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT3_or_GPIO2_BIT17_PLIC_17       = 17 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT4_or_GPIO2_BIT18_PLIC_18       = 18 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT5_or_GPIO2_BIT19_PLIC_19       = 19 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT6_or_GPIO2_BIT20_PLIC_20       = 20 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT7_or_GPIO2_BIT21_PLIC_21       = 21 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT8_or_GPIO2_BIT22_PLIC_22       = 22 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT9_or_GPIO2_BIT23_PLIC_23       = 23 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT10_or_GPIO2_BIT24_PLIC_24      = 24 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT11_or_GPIO2_BIT25_PLIC_25      = 25 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT12_or_GPIO2_BIT26_PLIC_26      = 26 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT13_or_GPIO2_BIT27_PLIC_27      = 27 + OFFSET_TO_MSS_GLOBAL_INTS,

    GPIO1_BIT14_or_GPIO2_BIT28_PLIC_28       = 28 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT15_or_GPIO2_BIT29_PLIC_29       = 29 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT16_or_GPIO2_BIT30_PLIC_30       = 30 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT17_or_GPIO2_BIT31_PLIC_31       = 31 + OFFSET_TO_MSS_GLOBAL_INTS,

    GPIO1_BIT18_PLIC_32           = 32 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT19_PLIC_33           = 33 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT20_PLIC_34           = 34 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT21_PLIC_35           = 35 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT22_PLIC_36           = 36 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_BIT23_PLIC_37           = 37 + OFFSET_TO_MSS_GLOBAL_INTS,

    GPIO0_NON_DIRECT_PLIC         = 38 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO1_NON_DIRECT_PLIC         = 39 + OFFSET_TO_MSS_GLOBAL_INTS,
    GPIO2_NON_DIRECT_PLIC         = 40 + OFFSET_TO_MSS_GLOBAL_INTS,

    SPI0_PLIC                    = 41 + OFFSET_TO_MSS_GLOBAL_INTS,
    SPI1_PLIC                    = 42 + OFFSET_TO_MSS_GLOBAL_INTS,
    CAN0_PLIC                    = 43 + OFFSET_TO_MSS_GLOBAL_INTS,
    CAN1_PLIC                    = 44 + OFFSET_TO_MSS_GLOBAL_INTS,
    I2C0_MAIN_PLIC               = 45 + OFFSET_TO_MSS_GLOBAL_INTS,
    I2C0_ALERT_PLIC              = 46 + OFFSET_TO_MSS_GLOBAL_INTS,
    I2C0_SUS_PLIC                = 47 + OFFSET_TO_MSS_GLOBAL_INTS,
    I2C1_MAIN_PLIC               = 48 + OFFSET_TO_MSS_GLOBAL_INTS,
    I2C1_ALERT_PLIC              = 49 + OFFSET_TO_MSS_GLOBAL_INTS,
    I2C1_SUS_PLIC                = 50 + OFFSET_TO_MSS_GLOBAL_INTS,
    MAC0_INT_PLIC                = 51 + OFFSET_TO_MSS_GLOBAL_INTS,
    MAC0_QUEUE1_PLIC             = 52 + OFFSET_TO_MSS_GLOBAL_INTS,
    MAC0_QUEUE2_PLIC             = 53 + OFFSET_TO_MSS_GLOBAL_INTS,
    MAC0_QUEUE3_PLIC             = 54 + OFFSET_TO_MSS_GLOBAL_INTS,
    MAC0_EMAC_PLIC               = 55 + OFFSET_TO_MSS_GLOBAL_INTS,
    MAC0_MMSL_PLIC               = 56 + OFFSET_TO_MSS_GLOBAL_INTS,
    MAC1_INT_PLIC                = 57 + OFFSET_TO_MSS_GLOBAL_INTS,
    MAC1_QUEUE1_PLIC             = 58 + OFFSET_TO_MSS_GLOBAL_INTS,
    MAC1_QUEUE2_PLIC             = 59 + OFFSET_TO_MSS_GLOBAL_INTS,
    MAC1_QUEUE3_PLIC             = 60 + OFFSET_TO_MSS_GLOBAL_INTS,
    MAC1_EMAC_PLIC               = 61 + OFFSET_TO_MSS_GLOBAL_INTS,
    MAC1_MMSL_PLIC               = 62 + OFFSET_TO_MSS_GLOBAL_INTS,
    DDRC_TRAIN_PLIC              = 63 + OFFSET_TO_MSS_GLOBAL_INTS,
    SCB_INTERRUPT_PLIC           = 64 + OFFSET_TO_MSS_GLOBAL_INTS,
    ECC_ERROR_PLIC               = 65 + OFFSET_TO_MSS_GLOBAL_INTS,
    ECC_CORRECT_PLIC             = 66 + OFFSET_TO_MSS_GLOBAL_INTS,
    RTC_WAKEUP_PLIC              = 67 + OFFSET_TO_MSS_GLOBAL_INTS,
    RTC_MATCH_PLIC               = 68 + OFFSET_TO_MSS_GLOBAL_INTS,
    TIMER1_PLIC                  = 69 + OFFSET_TO_MSS_GLOBAL_INTS,
    TIMER2_PLIC                  = 70 + OFFSET_TO_MSS_GLOBAL_INTS,
    ENVM_PLIC                    = 71 + OFFSET_TO_MSS_GLOBAL_INTS,
    QSPI_PLIC                    = 72 + OFFSET_TO_MSS_GLOBAL_INTS,
    USB_DMA_PLIC                 = 73 + OFFSET_TO_MSS_GLOBAL_INTS,
    USB_MC_PLIC                  = 74 + OFFSET_TO_MSS_GLOBAL_INTS,
    MMC_main_PLIC                = 75 + OFFSET_TO_MSS_GLOBAL_INTS,
    MMC_wakeup_PLIC              = 76 + OFFSET_TO_MSS_GLOBAL_INTS,
    MMUART0_PLIC_77              = 77 + OFFSET_TO_MSS_GLOBAL_INTS,
    MMUART1_PLIC                 = 78 + OFFSET_TO_MSS_GLOBAL_INTS,
    MMUART2_PLIC                 = 79 + OFFSET_TO_MSS_GLOBAL_INTS,
    MMUART3_PLIC                 = 80 + OFFSET_TO_MSS_GLOBAL_INTS,
    MMUART4_PLIC                 = 81 + OFFSET_TO_MSS_GLOBAL_INTS,

    G5C_DEVRST_PLIC              = 82 + OFFSET_TO_MSS_GLOBAL_INTS,
    g5c_MESSAGE_PLIC             = 83 + OFFSET_TO_MSS_GLOBAL_INTS,
    USOC_VC_INTERRUPT_PLIC       = 84 + OFFSET_TO_MSS_GLOBAL_INTS,
    USOC_SMB_INTERRUPT_PLIC      = 85 + OFFSET_TO_MSS_GLOBAL_INTS,
    /* contains multiple interrupts- */
    E51_0_MAINTENACE_PLIC        = 86 + OFFSET_TO_MSS_GLOBAL_INTS,

    WDOG0_MRVP_PLIC              = 87 + OFFSET_TO_MSS_GLOBAL_INTS,
    WDOG1_MRVP_PLIC              = 88 + OFFSET_TO_MSS_GLOBAL_INTS,
    WDOG2_MRVP_PLIC              = 89 + OFFSET_TO_MSS_GLOBAL_INTS,
    WDOG3_MRVP_PLIC              = 90 + OFFSET_TO_MSS_GLOBAL_INTS,
    WDOG4_MRVP_PLIC              = 91 + OFFSET_TO_MSS_GLOBAL_INTS,
    WDOG0_TOUT_PLIC              = 92 + OFFSET_TO_MSS_GLOBAL_INTS,
    WDOG1_TOUT_PLIC              = 93 + OFFSET_TO_MSS_GLOBAL_INTS,
    WDOG2_TOUT_PLIC              = 94 + OFFSET_TO_MSS_GLOBAL_INTS,
    WDOG3_TOUT_PLIC              = 95 + OFFSET_TO_MSS_GLOBAL_INTS,
    WDOG4_TOUT_PLIC              = 96 + OFFSET_TO_MSS_GLOBAL_INTS,
    G5C_MSS_SPI_PLIC             = 97 + OFFSET_TO_MSS_GLOBAL_INTS,
    VOLT_TEMP_ALARM_PLIC         = 98 + OFFSET_TO_MSS_GLOBAL_INTS,
    ATHENA_COMPLETE_PLIC         = 99 + OFFSET_TO_MSS_GLOBAL_INTS,
    ATHENA_ALARM_PLIC            = 100 + OFFSET_TO_MSS_GLOBAL_INTS,
    ATHENA_BUS_ERROR_PLIC        = 101 + OFFSET_TO_MSS_GLOBAL_INTS,
    USOC_AXIC_US_PLIC            = 102 + OFFSET_TO_MSS_GLOBAL_INTS,
    USOC_AXIC_DS_PLIC            = 103 + OFFSET_TO_MSS_GLOBAL_INTS,

    FABRIC_F2H_0_PLIC            = 105 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_1_PLIC            = 106 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_2_PLIC            = 107 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_3_PLIC            = 108 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_4_PLIC            = 109 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_5_PLIC            = 110 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_6_PLIC            = 111 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_7_PLIC            = 112 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_8_PLIC            = 113 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_9_PLIC            = 114 + OFFSET_TO_MSS_GLOBAL_INTS,

    FABRIC_F2H_10_PLIC           = 115 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_11_PLIC           = 116 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_12_PLIC           = 117 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_13_PLIC           = 118 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_14_PLIC           = 119 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_15_PLIC           = 120 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_16_PLIC           = 121 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_17_PLIC           = 122 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_18_PLIC           = 123 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_19_PLIC           = 124 + OFFSET_TO_MSS_GLOBAL_INTS,

    FABRIC_F2H_20_PLIC           = 125 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_21_PLIC           = 126 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_22_PLIC           = 127 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_23_PLIC           = 128 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_24_PLIC           = 129 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_25_PLIC           = 130 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_26_PLIC           = 131 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_27_PLIC           = 132 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_28_PLIC           = 133 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_29_PLIC           = 134 + OFFSET_TO_MSS_GLOBAL_INTS,

    FABRIC_F2H_30_PLIC           = 135 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_31_PLIC           = 136 + OFFSET_TO_MSS_GLOBAL_INTS,

    FABRIC_F2H_32_PLIC           = 137 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_33_PLIC           = 138 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_34_PLIC           = 139 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_35_PLIC           = 140 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_36_PLIC           = 141 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_37_PLIC           = 142 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_38_PLIC           = 143 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_39_PLIC           = 144 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_40_PLIC           = 145 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_41_PLIC           = 146 + OFFSET_TO_MSS_GLOBAL_INTS,

    FABRIC_F2H_42_PLIC           = 147 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_43_PLIC           = 148 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_44_PLIC           = 149 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_45_PLIC           = 150 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_46_PLIC           = 151 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_47_PLIC           = 152 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_48_PLIC           = 153 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_49_PLIC           = 154 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_50_PLIC           = 155 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_51_PLIC           = 156 + OFFSET_TO_MSS_GLOBAL_INTS,

    FABRIC_F2H_52_PLIC           = 157 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_53_PLIC           = 158 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_54_PLIC           = 159 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_55_PLIC           = 160 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_56_PLIC           = 161 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_57_PLIC           = 162 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_58_PLIC           = 163 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_59_PLIC           = 164 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_60_PLIC           = 165 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_61_PLIC           = 166 + OFFSET_TO_MSS_GLOBAL_INTS,

    FABRIC_F2H_62_PLIC           = 167 + OFFSET_TO_MSS_GLOBAL_INTS,
    FABRIC_F2H_63_PLIC           = 168 + OFFSET_TO_MSS_GLOBAL_INTS,

    BUS_ERROR_UNIT_HART_0        = 182,
    BUS_ERROR_UNIT_HART_1        = 183,
    BUS_ERROR_UNIT_HART_2        = 184,
    BUS_ERROR_UNIT_HART_3        = 185,
    BUS_ERROR_UNIT_HART_4        = 186

#else
    INVALID_IRQn                 = 0,
    L2Cache_0_PLIC_1             = 1,
    L2Cache_1_PLIC_2             = 2,
    L2Cache_2__PLIC_3            = 3,
    USART0_PLIC_4                = 4,
    USART1_PLIC_5                = 5,
    QSPI_12_PLIC_6               = 6,

    gpio_PLIC_7                  = 7,
    gpio_PLIC_8                  = 8,
    gpio_PLIC_9                  = 9,
    gpio_10                      = 10,
    gpio_11                      = 11,
    gpio_12                      = 12,
    gpio_PLIC_13                 = 13,
    gpio_PLIC_14                 = 14,
    gpio_PLIC_15                 = 15,
    gpio_PLIC_16                 = 16,
    gpio_PLIC_17                 = 17,
    gpio_PLIC_18                 = 18,
    gpio_PLIC_19                 = 19,
    gpio_PLIC_20                 = 20,
    gpio_PLIC_21                 = 21,
    gpio_PLIC_22                 = 22,

    dma_PLIC_23                  = 23,
    dma_PLIC_24                  = 24,
    dma_PLIC_25                  = 25,
    dma_PLIC_26                  = 26,
    dma_PLIC_27                  = 27,
    dma_PLIC_28                  = 28,
    dma_PLIC_29                  = 29,
    dma_PLIC_30                  = 30,

    ddr_subsytem_PLIC_31         = 31,

    chiplink_msi_PLIC_32         = 32,
    chiplink_msi_PLIC_33         = 33,
    chiplink_msi_PLIC_34         = 34,
    chiplink_msi_PLIC_35         = 35,
    chiplink_msi_PLIC_36         = 36,
    chiplink_msi_PLIC_37         = 37,
    chiplink_msi_PLIC_38         = 38,
    chiplink_msi_PLIC_39         = 39,
    chiplink_msi_PLIC_40         = 40,
    chiplink_msi_PLIC_41         = 41,

    pwm0_PLIC_42                 = 42,
    pwm0_PLIC_43                 = 43,
    pwm0_PLIC_44                 = 44,
    pwm0_PLIC_45                 = 45,

    pwm1_PLIC_46                 = 46,
    pwm1_PLIC_47                 = 47,
    pwm1_PLIC_48                 = 48,
    pwm1_PLIC_49                 = 49,

    i2c_PLIC_50                  = 50,
    QSPI0_PLIC_51                = 51,
    QSPI1_PLIC_52                = 52,
    ethernet_PLIC_53             = 53

#endif

} PLIC_IRQn_Type;

#ifndef SIFIVE_HIFIVE_UNLEASHED
#define MAX_PLIC_INT BUS_ERROR_UNIT_HART_4
#else
#define MAX_PLIC_INT ethernet_PLIC_53
#endif

/***************************************************************************//**
 * E51-0 is Maintenance Interrupt, CPU needs to read status register to
 * determine exact cause:
 * This structure added here for clarity, need to replay with status register
 * defines for determining interrupt cause
 */
typedef enum
{
     mpu_fail_plic               =0,
     lp_state_enter_plic         =1,
     lp_state_exit_plic          =2,
     ff_start_plic               =3,
     ff_end_plic                 =4,
     fpga_on_plic                =5,
     fpga_off_plic               =6,
     scb_error_plic              =7,
     scb_fault_plic              =8,
     mesh_fail_plic              =9
} PLIC_IRQ86_Type;

typedef struct
{
    volatile uint32_t PRIORITY_THRESHOLD;
    volatile uint32_t CLAIM_COMPLETE;
    volatile uint32_t reserved[(0x1000/4)-2];
} IRQ_Target_Type;

typedef struct
{
    volatile uint32_t ENABLES[32U];
} Target_Enables_Type;

#ifndef SIFIVE_HIFIVE_UNLEASHED
#define PLIC_SET_UP_REGISTERS 6U
#else
#define PLIC_SET_UP_REGISTERS 2U
#endif

#ifndef SIFIVE_HIFIVE_UNLEASHED
#define PLIC_NUM_SOURCES 187U
#else
#define PLIC_NUM_SOURCES 54U    /* 53 actual, source 0 is not used */
#endif

#define PLIC_NUM_PRIORITIES 7U
#define NUM_CLAIM_REGS      9U


/* The FU540-C000 has 53 interrupt sources. */
 typedef struct
{
    volatile uint32_t RESERVED0;
    /*-------------------- Source Priority --------------------*/
    volatile uint32_t SOURCE_PRIORITY[PLIC_NUM_SOURCES];
    volatile uint32_t RESERVED1[(0x1000 / 4) - (PLIC_NUM_SOURCES + 1)];
    /*-------------------- Pending array --------------------*/
    volatile const uint32_t PENDING_ARRAY[PLIC_SET_UP_REGISTERS];
    volatile uint32_t RESERVED2[(0x1000/4) - PLIC_SET_UP_REGISTERS];

    /*-----------------Hart0 Mode Enables--------------------*/
    volatile uint32_t HART0_MMODE_ENA[PLIC_SET_UP_REGISTERS];
    volatile uint32_t RESERVED3[(0x80/4) - PLIC_SET_UP_REGISTERS];

    /*-----------------Hart1 Mode Enables--------------------*/
    volatile uint32_t HART1_MMODE_ENA[PLIC_SET_UP_REGISTERS];
    volatile uint32_t RESERVED4a[(0x80/4) - PLIC_SET_UP_REGISTERS];
    volatile uint32_t HART1_SMODE_ENA[PLIC_SET_UP_REGISTERS];
    volatile uint32_t RESERVED4[(0x80/4) - PLIC_SET_UP_REGISTERS];

    /*-----------------Hart2 Mode Enables--------------------*/
    volatile uint32_t HART2_MMODE_ENA[PLIC_SET_UP_REGISTERS];
    volatile uint32_t RESERVED5a[(0x80/4) - PLIC_SET_UP_REGISTERS];
    volatile uint32_t HART2_SMODE_ENA[PLIC_SET_UP_REGISTERS];
    volatile uint32_t RESERVED5[(0x80/4) - PLIC_SET_UP_REGISTERS];

    /*-----------------Hart3 Mode Enables--------------------*/
    volatile uint32_t HART3_MMODE_ENA[PLIC_SET_UP_REGISTERS];
    volatile uint32_t RESERVED6a[(0x80/4) - PLIC_SET_UP_REGISTERS];
    volatile uint32_t HART3_SMODE_ENA[PLIC_SET_UP_REGISTERS];
    volatile uint32_t RESERVED6[(0x80/4) - PLIC_SET_UP_REGISTERS];

    /*-----------------Hart4 Mode Enables--------------------*/
    volatile uint32_t HART4_MMODE_ENA[PLIC_SET_UP_REGISTERS];
    volatile uint32_t RESERVED7a[(0x80/4) - PLIC_SET_UP_REGISTERS];
    volatile uint32_t HART4_SMODE_ENA[PLIC_SET_UP_REGISTERS];
    volatile uint32_t RESERVED7[(0x80/4) - PLIC_SET_UP_REGISTERS];

    volatile uint32_t RESERVED8[(0x0C200000 - 0x0C002480)/4];

    /*--- Target Priority threshold and claim/complete---------*/
    IRQ_Target_Type TARGET[NUM_CLAIM_REGS];   /* See PLIC Register Map or
                                                 TARGET_OFFSET defines below
                                                 for offset details */

} PLIC_Type;

#define TARGET_OFFSET_HART0_M 0U
#define TARGET_OFFSET_HART1_M 1U
#define TARGET_OFFSET_HART1_S 2U
#define TARGET_OFFSET_HART2_M 3U
#define TARGET_OFFSET_HART2_S 4U
#define TARGET_OFFSET_HART3_M 5U
#define TARGET_OFFSET_HART3_S 6U
#define TARGET_OFFSET_HART4_M 7U
#define TARGET_OFFSET_HART4_S 8U

extern const unsigned long plic_hart_lookup[5U];

/***************************************************************************//**
 * PLIC: Platform Level Interrupt Controller
 */
#define PLIC_BASE_ADDR 0x0C000000UL

#define PLIC    ((PLIC_Type * const)PLIC_BASE_ADDR)

/*-------------------------------------------------------------------------*//**
 * The function PLIC_init() initializes the PLIC controller and enables the
 * global external interrupt bit.
 */

/*-----------------Hart Mode Enables--------------------*/

static inline void PLIC_init(void)
{
    uint32_t inc;
    uint64_t hart_id  = read_csr(mhartid);

    /* Disable all interrupts for the current hart. */
    switch(hart_id)
    {
        case 0:
            for(inc = 0UL; inc < PLIC_SET_UP_REGISTERS; inc++)
            {
                PLIC->HART0_MMODE_ENA[inc] = 0U;
            }

            /* Set the threshold to zero.
             * PLIC provides context based threshold register for the settings of a
             * interrupt priority threshold of each context. The threshold register
             * is a WARL field. The PLIC will mask all PLIC interrupts of a priority
             * less than or equal to threshold. For example, a threshold value of zero
             * permits all interrupts with non-zero priority.*/

            PLIC->TARGET[TARGET_OFFSET_HART0_M].PRIORITY_THRESHOLD  = 0U;
            break;
        case 1:
            for(inc = 0UL; inc < PLIC_SET_UP_REGISTERS; inc++)
            {
                PLIC->HART1_MMODE_ENA[inc] = 0U;
                PLIC->HART1_SMODE_ENA[inc] = 0U;
            }

            PLIC->TARGET[TARGET_OFFSET_HART1_M].PRIORITY_THRESHOLD  = 0U;
            /* Disable supervisor level */
            PLIC->TARGET[TARGET_OFFSET_HART1_S].PRIORITY_THRESHOLD  = 7U;
            break;
        case 2:
            for(inc = 0UL; inc < PLIC_SET_UP_REGISTERS; inc++)
            {
                PLIC->HART2_MMODE_ENA[inc] = 0U;
                PLIC->HART2_SMODE_ENA[inc] = 0U;
            }

            PLIC->TARGET[TARGET_OFFSET_HART2_M].PRIORITY_THRESHOLD  = 0U;
            /* Disable supervisor level */
            PLIC->TARGET[TARGET_OFFSET_HART2_S].PRIORITY_THRESHOLD  = 7U;
            break;
        case 3:
            for(inc = 0UL; inc < PLIC_SET_UP_REGISTERS; inc++)
            {
                PLIC->HART3_MMODE_ENA[inc] = 0U;
                PLIC->HART3_SMODE_ENA[inc] = 0U;
            }

            PLIC->TARGET[TARGET_OFFSET_HART3_M].PRIORITY_THRESHOLD  = 0U;
            /* Disable supervisor level */
            PLIC->TARGET[TARGET_OFFSET_HART3_S].PRIORITY_THRESHOLD  = 7U;
            break;
        case 4:
            for(inc = 0UL; inc < PLIC_SET_UP_REGISTERS; inc++)
            {
                PLIC->HART4_MMODE_ENA[inc] = 0U;
                PLIC->HART4_SMODE_ENA[inc] = 0U;
            }

            PLIC->TARGET[TARGET_OFFSET_HART4_M].PRIORITY_THRESHOLD  = 0U;
            /* Disable supervisor level */
            PLIC->TARGET[TARGET_OFFSET_HART4_S].PRIORITY_THRESHOLD  = 7U;
            break;
        default:
            break;
    }

    /* Enable machine external interrupts. */
    set_csr(mie, MIP_MEIP);
}



/***************************************************************************//**
 * The function PLIC_EnableIRQ() enables the external interrupt for the
 * interrupt number indicated by the parameter IRQn.
 */
static inline void PLIC_EnableIRQ(PLIC_IRQn_Type IRQn)
{
    uint32_t current;
    uint64_t hart_id  = read_csr(mhartid);

    switch(hart_id)
    {
        case 0:
            current  = PLIC->HART0_MMODE_ENA[IRQn / 32U];
            current |= (uint32_t)1 << (IRQn % 32U);
            PLIC->HART0_MMODE_ENA[IRQn / 32U]  = current;
            break;
        case 1:
            current  = PLIC->HART1_MMODE_ENA[IRQn / 32U];
            current |= (uint32_t)1 << (IRQn % 32U);
            PLIC->HART1_MMODE_ENA[IRQn / 32U]  = current;
            break;
        case 2:
            current  = PLIC->HART2_MMODE_ENA[IRQn / 32U];
            current |= (uint32_t)1 << (IRQn % 32U);
            PLIC->HART2_MMODE_ENA[IRQn / 32U]  = current;
            break;
        case 3:
            current  = PLIC->HART3_MMODE_ENA[IRQn / 32U];
            current |= (uint32_t)1 << (IRQn % 32U);
            PLIC->HART3_MMODE_ENA[IRQn / 32U]  = current;
            break;
        case 4:
            current  = PLIC->HART4_MMODE_ENA[IRQn / 32U];
            current |= (uint32_t)1 << (IRQn % 32U);
            PLIC->HART4_MMODE_ENA[IRQn / 32U]  = current;
            break;
        default:
            break;
    }
}

/***************************************************************************//**
 * The function PLIC_DisableIRQ() disables the external interrupt for the
 * interrupt number indicated by the parameter IRQn.

 * NOTE:
 *     This function can be used to disable the external interrupt from outside
 *     external interrupt handler function.
 *     This function MUST NOT be used from within the External Interrupt
 *     handler.
 *     If you wish to disable the external interrupt while the interrupt handler
 *     for that external interrupt is executing then you must use the return
 *     value EXT_IRQ_DISABLE to return from the extern interrupt handler.
 */
static inline void PLIC_DisableIRQ(PLIC_IRQn_Type IRQn)
{
    uint32_t current;
    uint64_t hart_id  = read_csr(mhartid);

    switch(hart_id)
    {
        case 0:
            current = PLIC->HART0_MMODE_ENA[IRQn / 32U];
            current &= ~((uint32_t)1 << (IRQn % 32U));
            PLIC->HART0_MMODE_ENA[IRQn / 32U] = current;
            break;
        case 1:
            current = PLIC->HART1_MMODE_ENA[IRQn / 32U];
            current &= ~((uint32_t)1 << (IRQn % 32U));
            PLIC->HART1_MMODE_ENA[IRQn / 32U] = current;
            break;
        case 2:
            current = PLIC->HART2_MMODE_ENA[IRQn / 32U];
            current &= ~((uint32_t)1 << (IRQn % 32U));
            PLIC->HART2_MMODE_ENA[IRQn / 32U] = current;
            break;
        case 3:
            current = PLIC->HART3_MMODE_ENA[IRQn / 32U];
            current &= ~((uint32_t)1 << (IRQn % 32U));
            PLIC->HART3_MMODE_ENA[IRQn / 32U] = current;
            break;
        case 4:
            current = PLIC->HART4_MMODE_ENA[IRQn / 32U];
            current &= ~((uint32_t)1 << (IRQn % 32U));
            PLIC->HART4_MMODE_ENA[IRQn / 32U] = current;
            break;
        default:
            break;
    }
}

/***************************************************************************//**
 * The function PLIC_SetPriority() sets the priority for the external interrupt
 * for the interrupt number indicated by the parameter IRQn.
 */
static inline void PLIC_SetPriority(PLIC_IRQn_Type IRQn, uint32_t priority)
{
    if((IRQn > INVALID_IRQn) && (IRQn < PLIC_NUM_SOURCES))
    {
        PLIC->SOURCE_PRIORITY[IRQn-1] = priority;
    }
}

/***************************************************************************//**
 * The function PLIC_GetPriority() returns the priority for the external
 * interrupt for the interrupt number indicated by the parameter IRQn.
 */
static inline uint32_t PLIC_GetPriority(PLIC_IRQn_Type IRQn)
{
    uint32_t ret_val = 0U;

    if((IRQn > INVALID_IRQn) && (IRQn < PLIC_NUM_SOURCES))
    {
        ret_val = PLIC->SOURCE_PRIORITY[IRQn-1];
    }

    return(ret_val);
}


static inline uint32_t PLIC_pending(PLIC_IRQn_Type IRQn)
{
    return (PLIC->PENDING_ARRAY[IRQn/32U] & (0x01U<<(IRQn%32U)));
}

/***************************************************************************//**
 * The function PLIC_ClaimIRQ() claims the interrupt from the PLIC controller.
 */
static inline uint32_t PLIC_ClaimIRQ(void)
{
    uint64_t hart_id  = read_csr(mhartid);

    return (PLIC->TARGET[plic_hart_lookup[hart_id]].CLAIM_COMPLETE);
}

/***************************************************************************//**
 * The function PLIC_CompleteIRQ() indicates to the PLIC controller the
 * interrupt is processed and claim is complete.
 */
static inline void PLIC_CompleteIRQ(uint32_t source)
{
    uint64_t hart_id  = read_csr(mhartid);

    ASSERT(source <= MAX_PLIC_INT);

    PLIC->TARGET[plic_hart_lookup[hart_id]].CLAIM_COMPLETE  = source;
}

/***************************************************************************//**
 *
 * The function PLIC_SetPriority_Threshold() sets the threshold for a particular
 * hart. The default threshold on reset is 0.
 * The PFSoC Core Complex supports setting of an interrupt priority threshold
 * via the threshold register. The threshold is a WARL field, where the PFSoC
 * Core Complex supports a maximum threshold of 7.
 * The PFSoC Core Complex will mask all PLIC interrupts of a priority less than
 * or equal to threshold. For example, a threshold value of zero permits all
 * interrupts with non-zero priority, whereas a value of 7 masks all
 * interrupts.
 */
static inline void PLIC_SetPriority_Threshold(uint32_t threshold)
{
    uint64_t hart_id  = read_csr(mhartid);

    ASSERT(threshold <= 7);

    PLIC->TARGET[plic_hart_lookup[hart_id]].PRIORITY_THRESHOLD  = threshold;
}

/***************************************************************************//**
 *  PLIC_ClearPendingIRQ(void)
 *  This is only called by the startup hart and only once
 *  Clears any pending interrupts as PLIC can be in unknown state on startup
 */
static inline void PLIC_ClearPendingIRQ(void)
{
    volatile uint32_t int_num  = PLIC_ClaimIRQ();
    volatile int32_t wait_possible_int;

    while ( int_num != INVALID_IRQn)
    {
        PLIC_CompleteIRQ(int_num);
        wait_possible_int = 0xFU;
        while (wait_possible_int)
        {
            wait_possible_int--;
        }
        int_num  = PLIC_ClaimIRQ(); /* obtain interrupt, auto clears  */
    }
}

/***************************************************************************//**
 * This function is only called from one hart on startup
 */
static inline void PLIC_init_on_reset(void)
{
    uint32_t inc;

    /* default all priorities so effectively disabled */
    for(inc = 0U; inc < PLIC_NUM_SOURCES; ++inc)
    {
        /* priority must be greater than threshold to be enabled, so setting to
         * 7 disables */
        PLIC->SOURCE_PRIORITY[inc]  = 0U;
    }

    for(inc = 0U; inc < NUM_CLAIM_REGS; ++inc)
    {
        PLIC->TARGET[inc].PRIORITY_THRESHOLD  = 7U;
    }

    /* and clear all the enables */
    for(inc = 0UL; inc < PLIC_SET_UP_REGISTERS; inc++)
    {
        PLIC->HART0_MMODE_ENA[inc] = 0U;
        PLIC->HART1_MMODE_ENA[inc] = 0U;
        PLIC->HART1_SMODE_ENA[inc] = 0U;
        PLIC->HART2_MMODE_ENA[inc] = 0U;
        PLIC->HART2_SMODE_ENA[inc] = 0U;
        PLIC->HART3_MMODE_ENA[inc] = 0U;
        PLIC->HART3_SMODE_ENA[inc] = 0U;
        PLIC->HART4_MMODE_ENA[inc] = 0U;
        PLIC->HART4_SMODE_ENA[inc] = 0U;
    }

    /* clear any pending interrupts- in case already there */
    PLIC_ClearPendingIRQ();
}

#ifdef __cplusplus
}
#endif

#endif  /* MSS_PLIC_H */
