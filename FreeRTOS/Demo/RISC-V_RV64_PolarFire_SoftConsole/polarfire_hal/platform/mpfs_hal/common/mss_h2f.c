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
 * @file mss_h2f.c
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief H2F access data structures and functions.
 *
 */
#include "mss_plic.h"
#include "mss_h2f.h"

#ifdef __cplusplus
extern "C" {
#endif

#ifndef SIFIVE_HIFIVE_UNLEASHED

#define H2F_MAPPING_INVALID 255U

/*==============================================================================
 * H2F_int_mapping, source to H2F output lines
 * The internal interrupt are multiplexed to fabric I/O lines.
 * That is, each line will contain several interrupts.
 */

const uint8_t H2F_int_mapping[BUS_ERROR_UNIT_HART_4]= { \

    H2F_MAPPING_INVALID /*INVALID_IRQn              = 0*/, \
    H2F_MAPPING_INVALID /*L2_METADATA_CORR_IRQn     = 1*/, \
    H2F_MAPPING_INVALID /*L2_METADAT_UNCORR_IRQn    = 2*/, \
    H2F_MAPPING_INVALID /*L2_DATA_CORR_IRQn         = 3*/, \
    H2F_MAPPING_INVALID /*L2_DATA_UNCORR_IRQn       = 4*/, \
    H2F_MAPPING_INVALID /*DMA_CH0_DONE_IRQn         = 5*/, \
    H2F_MAPPING_INVALID /*DMA_CH0_ERR_IRQn          = 6*/, \
    H2F_MAPPING_INVALID /*DMA_CH1_DONE_IRQn         = 7*/, \
    H2F_MAPPING_INVALID /*DMA_CH1_ERR_IRQn          = 8*/, \
    H2F_MAPPING_INVALID /*DMA_CH2_DONE_IRQn         = 9*/, \
    H2F_MAPPING_INVALID /*DMA_CH2_ERR_IRQn          = 10*/, \
    H2F_MAPPING_INVALID /*DMA_CH3_DONE_IRQn         = 11*/, \
    H2F_MAPPING_INVALID /*DMA_CH3_ERR_IRQn          = 12*/, \

    0x00U /*GPIO0_BIT0_or_GPIO2_BIT0_PLIC_0          = 0 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO0_BIT1_or_GPIO2_BIT1_PLIC_1          = 1 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO0_BIT2_or_GPIO2_BIT2_PLIC_2          = 2 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO0_BIT3_or_GPIO2_BIT3_PLIC_3          = 3 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO0_BIT4_or_GPIO2_BIT4_PLIC_4          = 4 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO0_BIT5_or_GPIO2_BIT5_PLIC_5          = 5 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO0_BIT6_or_GPIO2_BIT6_PLIC_6          = 6 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO0_BIT7_or_GPIO2_BIT7_PLIC_7          = 7 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO0_BIT8_or_GPIO2_BIT8_PLIC_8          = 8 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO0_BIT9_or_GPIO2_BIT9_PLIC_9          = 9 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO0_BIT10_or_GPIO2_BIT10_PLIC_10       = 10 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO0_BIT11_or_GPIO2_BIT11_PLIC_11       = 11 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO0_BIT12_or_GPIO2_BIT12_PLIC_12       = 12 + OFFSET_TO_MSS_GLOBAL_INTS*/, \

    0x00U /*GPIO0_BIT14_or_GPIO2_BIT13_PLIC_13       = 13 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT0_or_GPIO2_BIT14_PLIC_14        = 14 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT1_or_GPIO2_BIT15_PLIC_15        = 15 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT2_or_GPIO2_BIT16_PLIC_16        = 16 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT3_or_GPIO2_BIT17_PLIC_17        = 17 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT4_or_GPIO2_BIT18_PLIC_18        = 18 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT5_or_GPIO2_BIT19_PLIC_19        = 19 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT6_or_GPIO2_BIT20_PLIC_20        = 20 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT7_or_GPIO2_BIT21_PLIC_21        = 21 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT8_or_GPIO2_BIT22_PLIC_22        = 22 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT9_or_GPIO2_BIT23_PLIC_23        = 23 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT10_or_GPIO2_BIT24_PLIC_24       = 24 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT11_or_GPIO2_BIT25_PLIC_25       = 25 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT12_or_GPIO2_BIT26_PLIC_26       = 26 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT13_or_GPIO2_BIT27_PLIC_27       = 27 + OFFSET_TO_MSS_GLOBAL_INTS*/, \

    0x00U /*GPIO1_BIT14_or_GPIO2_BIT28_PLIC_28       = 28 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT15_or_GPIO2_BIT29_PLIC_29       = 29 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT16_or_GPIO2_BIT30_PLIC_30       = 30 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT17_or_GPIO2_BIT31_PLIC_31       = 31 + OFFSET_TO_MSS_GLOBAL_INTS*/, \

    0x00U /*GPIO1_BIT18_PLIC_32 = 32 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT19_PLIC_33                      = 33 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT20_PLIC_34                      = 34 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT21_PLIC_35                      = 35 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT22_PLIC_36                      = 36 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_BIT23_PLIC_37                      = 37 + OFFSET_TO_MSS_GLOBAL_INTS*/, \

    0x00U /*GPIO0_NON_DIRECT_PLI                     =38 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO1_NON_DIRECT_PLIC                    =39 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x00U /*GPIO2_NON_DIRECT_PLIC                    =40 + OFFSET_TO_MSS_GLOBAL_INTS*/, \

    0x01U /*SPI0_PLIC                                =41 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x01U /*SPI1_PLIC                                =42 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x01U /*CAN0_PLIC                                =43 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x01U /*CAN1_PLIC                                =44 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x02U /*I2C0_MAIN_PLIC                           =45 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x02U /*I2C0_ALERT_PLIC                          =46 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x02U /*I2C0_SUS_PLIC                            =47 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x02U /*I2C1_MAIN_PLIC                           =48 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x02U /*I2C1_ALERT_PLIC                          =49 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x02U /*I2C1_SUS_PLIC                            =50 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x03U /*MAC0_INT_PLIC                            =51 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x03U /*MAC0_QUEUE1_PLIC                         =52 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x03U /*MAC0_QUEUE2_PLIC                         =53 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x03U /*MAC0_QUEUE3_PLIC                         =54 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x03U /*MAC0_eMAC_PLIC                           =55 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x03U /*MAC0_MMSL_PLIC                           =56 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x04U /*MAC1_int_PLIC                            =57 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x04U /*MAC1_QUEUE1_PLIC                         =58 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x04U /*MAC1_QUEUE2_PLIC                         =59 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x04U /*MAC1_QUEUE3_PLIC                         =60 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x04U /*MAC1_EMAC_PLIC                           =61 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x04U /*MAC1_MMSL_PLIC                           =62 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x09U /*DDRC_TRAIN_PLIC                          =63 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x07U /*SCB_INTERRUPT_PLIC                       =64 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x06U /*ECC_ERROR_PLIC                           =65 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x06U /*ECC_CORRECT_PLIC                         =66 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x0BU /*RTC_WAKEUP_PLIC                          =67 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x0BU /*RTC_MATCH_PLIC                           =68 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x0CU /*TIMER1_PLIC                              =69 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x0CU /*TIMER2_PLIC                              =70 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x0DU /*ENVM_PLIC                                =71 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x0DU /*QSPI_PLIC                                =72 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x0EU /*USB_DMA_PLIC                             =73 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x0EU /*USB_MC_PLIC                              =74 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x0FU /*MMC_main_PLIC                            =75 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x0FU /*MMC_wakeup_PLIC                          =76 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x01U /*MMUART0_PLIC_77                          =77 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x01U /*MMUART1_PLIC                             =78 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x01U /*MMUART2_PLIC                             =79 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x01U /*MMUART3_PLIC                             =80 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x01U /*MMUART4_PLIC                             =81 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x0AU /*G5C_DEVRST_PLIC                          =82 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x08U /*g5c_MESSAGE_PLIC                         =83 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x0BU /*USOC_VC_INTERRUPT_PLIC                   =84 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x0BU /*USOC_SMB_INTERRUPT_PLIC                  =85 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x06U /*E51_0_MAINTENACE_PLIC                    =86 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x05U /*WDOG0_MRVP_PLIC                          =87 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x05U /*WDOG1_MRVP_PLIC                          =88 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x05U /*WDOG2_MRVP_PLIC                          =89 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x05U /*WDOG3_MRVP_PLIC                          =90 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x05U /*WDOG4_MRVP_PLIC                          =91 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x05U /*WDOG0_TOUT_PLIC                          =92 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x05U /*WDOG1_TOUT_PLIC                          =93 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x05U /*WDOG2_TOUT_PLIC                          =94 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x05U /*WDOG3_TOUT_PLIC                          =95 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x05U /*WDOG4_TOUT_PLIC                          =96 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x0DU /*G5C_MSS_SPI_PLIC                         =97 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*VOLT_TEMP_ALARM_PLIC      =98 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*ATHENA_COMPLETE_PLIC      =99 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*ATHENA_ALARM_PLIC         =100 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*ATHENA_BUS_ERROR_PLIC     =101 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x0BU /*USOC_AXIC_US_PLIC                        =102 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    0x0BU /*USOC_AXIC_DS_PLIC                        =103 + OFFSET_TO_MSS_GLOBAL_INTS*/, \

    H2F_MAPPING_INVALID /*FABRIC_F2H_0_PLIC        = 105 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_1_PLIC        = 106 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_2_PLIC        = 107 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_3_PLIC        = 108 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_4_PLIC        = 109 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_5_PLIC        = 110 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_6_PLIC        = 111 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_7_PLIC        = 112 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_8_PLIC        = 113 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_9_PLIC        = 114 + OFFSET_TO_MSS_GLOBAL_INTS*/, \

    H2F_MAPPING_INVALID /*FABRIC_F2H_10_PLIC        = 115 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_11_PLIC        = 116 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_12_PLIC        = 117 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_13_PLIC        = 118 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_14_PLIC        = 119 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_15_PLIC        = 120 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_16_PLIC        = 121 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_17_PLIC        = 122 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_18_PLIC        = 123 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_19_PLIC        = 124 + OFFSET_TO_MSS_GLOBAL_INTS*/, \

    H2F_MAPPING_INVALID /*FABRIC_F2H_20_PLIC        = 125 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_21_PLIC        = 126 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_22_PLIC        = 127 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_23_PLIC        = 128 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_24_PLIC        = 129 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_25_PLIC        = 130 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_26_PLIC        = 131 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_27_PLIC        = 132 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_28_PLIC        = 133 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_29_PLIC        = 134 + OFFSET_TO_MSS_GLOBAL_INTS*/, \

    H2F_MAPPING_INVALID /*FABRIC_F2H_30_PLIC        = 135 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_31_PLIC        = 136 + OFFSET_TO_MSS_GLOBAL_INTS*/, \

    H2F_MAPPING_INVALID /*FABRIC_F2H_32_PLIC        = 137 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_33_PLIC        = 138 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_34_PLIC        = 139 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_35_PLIC        = 140 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_36_PLIC        = 141 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_37_PLIC        = 142 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_38_PLIC        = 143 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_39_PLIC        = 144 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_40_PLIC        = 145 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_41_PLIC        = 146 + OFFSET_TO_MSS_GLOBAL_INTS*/, \

    H2F_MAPPING_INVALID /*FABRIC_F2H_42_PLIC        = 147 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_43_PLIC        = 148 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_44_PLIC        = 149 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_45_PLIC        = 150 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_46_PLIC        = 151 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_47_PLIC        = 152 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_48_PLIC        = 153 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_49_PLIC        = 154 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_50_PLIC        = 155 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_51_PLIC        = 156 + OFFSET_TO_MSS_GLOBAL_INTS*/, \

    H2F_MAPPING_INVALID /*FABRIC_F2H_52_PLIC        = 157 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_53_PLIC        = 158 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_54_PLIC        = 159 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_55_PLIC        = 160 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_56_PLIC        = 161 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_57_PLIC        = 162 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_58_PLIC        = 163 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_59_PLIC        = 164 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_60_PLIC        = 165 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_61_PLIC        = 166 + OFFSET_TO_MSS_GLOBAL_INTS*/, \

    H2F_MAPPING_INVALID /*FABRIC_F2H_62_PLIC        = 167 + OFFSET_TO_MSS_GLOBAL_INTS*/, \
    H2F_MAPPING_INVALID /*FABRIC_F2H_63_PLIC        = 168 + OFFSET_TO_MSS_GLOBAL_INTS*/, \

    H2F_MAPPING_INVALID /*BUS_ERROR_UNIT_HART_0    = 182*/, \
    H2F_MAPPING_INVALID /*BUS_ERROR_UNIT_HART_1    = 183*/, \
    H2F_MAPPING_INVALID /*BUS_ERROR_UNIT_HART_2    = 184*/, \
    H2F_MAPPING_INVALID /*BUS_ERROR_UNIT_HART_3    = 185*/, \
    H2F_MAPPING_INVALID /*BUS_ERROR_UNIT_HART_4    = 186 */

};


/**
 * get source to fabric signal mapping
 * @param source_int
 * @return
 */
static uint32_t get_corresponding_h2f_output(uint32_t source_int)
{
    uint32_t h2f_line = H2F_int_mapping[source_int];

    if(h2f_line < H2F_MAPPING_INVALID) /* if no error */
    {
        return(0x01U << h2f_line);
    }

    return(h2f_line);

}

/**
 * set H2F controller to reset to defaults- disabled
 */
void reset_h2f(void)
{
    uint8_t index = 0U;
    H2F_CONTROLLER->ENABLE = 0U;
    while(index < 4U)
    {
        H2F_CONTROLLER->PLENABLE[index] = 0U;
        index++;
    }
}

/**
 * enables output which will mirror PLIC input. PLIC mapping given above for reference
 * @param source_int
 */
void enable_h2f_int_output(uint32_t source_int)
{

    uint32_t output_signal = get_corresponding_h2f_output(source_int);

    if(output_signal != H2F_MAPPING_INVALID)
    {
        source_int -= OFFSET_TO_MSS_GLOBAL_INTS;

        /* enable the input */
        H2F_CONTROLLER->PLENABLE[source_int/32U] |= (0x01U << (source_int % 32U));

        /* enable the output */
        H2F_CONTROLLER->ENABLE |= ((output_signal<<16U) | 0x01U);
    }
}


/**
 * enables output which will mirror PLIC input. PLIC mapping given above for reference
 * @param source_int
 */
void disable_h2f_int_output(uint32_t source_int)
{
    uint32_t output_signal = get_corresponding_h2f_output(source_int);

    if(output_signal != H2F_MAPPING_INVALID)
    {
        /* enable the input */
        H2F_CONTROLLER->PLENABLE[source_int/32U] &= ~(source_int % 32U);
        /* enable the output */
        H2F_CONTROLLER->ENABLE &= ~(((output_signal<<16U)));
    }
}

#ifdef __cplusplus
}
#endif

#endif



