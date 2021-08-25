/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/**************************************************************************
    *
 * @file mss_sysreg.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief Hardware register definitions.

 *
 */
#ifndef MSS_SYSREG_H
#define MSS_SYSREG_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

 /* IO definitions (access restrictions to peripheral registers) */
 /**
     \defgroup CMSIS_glob_defs CMSIS Global Defines
     <strong>IO Type Qualifiers</strong> are used
     \li to specify the access to peripheral variables.
     \li for automatic generation of peripheral register debug information.

 */
#ifndef __I
 #ifdef __cplusplus
   #define   __I     volatile               /*!< Defines 'read only' permis
    sions */
 #else
   #define   __I     volatile const         /*!< Defines 'read only' permis
    sions */
 #endif
#endif
#ifndef __O
 #define     __O     volatile               /*!< Defines 'write only' permi
    ssions */
#endif
#ifndef __IO
 #define     __IO    volatile               /*!< Defines 'read / write' per
    missions */
#endif
 /* following defines should be used for structure members */
#ifndef __IM
 #define     __IM     volatile const        /*! Defines 'read only' structu
    re member permissions */
#endif
#ifndef __OM
 #define     __OM     volatile              /*! Defines 'write only' struct
    ure member permissions */
#endif
#ifndef __IOM
 #define __IOM volatile                     /*! Defines 'read / write' stru
    cture member permissions */
#endif

/* Defines all Top Register offsets*/
/* Date of Source Revision File: 12-Jul-18*/
/* PROTOCOL=MSS; BASE=32'h20012000*/
/* Hardware Base Address*/
#define BASE32_ADDR_MSS_SYSREG 0x20002000


/*Register for software use*/
#define TEMP0_OFFSET                                             0x0
    /* Scratch register for CPUS*/
    #define TEMP0_DATA_OFFSET                                    0x0
    #define TEMP0_DATA_MASK                                      (0xFFFFFFFF << 0x0)

/*Register for software use*/
#define TEMP1_OFFSET                                             0x4
    /* Scratch register for CPUS*/
    #define TEMP1_DATA_OFFSET                                    0x0
    #define TEMP1_DATA_MASK                                      (0xFFFFFFFF << 0x0)

/*Master clock configuration*/
#define CLOCK_CONFIG_CR_OFFSET                                   0x8
    /* "Sets the master synchronous clock divider bits [1:0] CPU clock divi
    der           (Reset=/1 =0)bits [3:2] AXI clock divider            (Reset=/
    1 =0)bits [5:4] AHB/APB clock divider  (Reset=/2 =1)00=/1   01=/2  10=/4 11
    =/8  (AHB/APB divider may not be set to /1)Note at reset MSS corner clock i
    s 80MHz therefore divider is set to divide by 1"*/
    #define CLOCK_CONFIG_CR_DIVIDER_OFFSET                       0x0
    #define CLOCK_CONFIG_CR_DIVIDER_MASK                         (0x3F << 0x0)
    /* When '1' requests G5_control to enable the 1mHz (2MHz) on-chip oscil
    lator*/
    #define CLOCK_CONFIG_CR_ENABLE_1MHZ_OFFSET                   0x8
    #define CLOCK_CONFIG_CR_ENABLE_1MHZ_MASK                     (0x01 << 0x8)

/*RTC clock divider*/
#define RTC_CLOCK_CR_OFFSET                                      0xC
    /* "Sets the  division ratio to create the internal RTC clock from the
    reference clock. The defaults sets the reference clock to 1MHz assuming the
     reference clock is 100Mhz.If the reference clock is 125MHz then 125 will c
    reate a 1MHz clockMax divider value is 4095 and value must be an integer.RT
    C clock must be less 2X the AXI clock rate."*/
    #define RTC_CLOCK_CR_PERIOD_OFFSET                           0x0
    #define RTC_CLOCK_CR_PERIOD_MASK                             (0xFFF << 0x0)
    /* RTC Clock enable. When chaning the divider the enable should be trur
    ned off first the divider changed and the enable turned back on.*/
    #define RTC_CLOCK_CR_ENABLE_OFFSET                           0x10
    #define RTC_CLOCK_CR_ENABLE_MASK                             (0x01 << 0x10)

/*Fabric Reset mask*/
#define FABRIC_RESET_CR_OFFSET                                   0x10
    /* Blocks the fabric Reset input preventing the fabric reseting the MSS
    */
    #define FABRIC_RESET_CR_ENABLE_OFFSET                        0x0
    #define FABRIC_RESET_CR_ENABLE_MASK                          (0x01 << 0x0)

/**/
#define BOOT_FAIL_CR_OFFSET                                      0x14
    /* Written by firmware to indicate that the boot process failed drives
    the fab_boot_fail signal to the fabric. Is cleared by the fabric asserting
    fab_boot_fail_clear*/
    #define BOOT_FAIL_CR_BOOT_OFFSET                             0x0
    #define BOOT_FAIL_CR_BOOT_MASK                               (0x01 << 0x0)

/*Configuration lock*/
#define CONFIG_LOCK_CR_OFFSET                                    0x1C
    /* When written to '1' will cause all RWC registers to lock until a mas
    ter reset occurs.*/
    #define CONFIG_LOCK_CR_LOCK_OFFSET                           0x0
    #define CONFIG_LOCK_CR_LOCK_MASK                             (0x01 << 0x0)

/*Indicates which reset caused the last reset. After a reset occurs registe
    r should be read and then zero written to allow the next reset event to be
    correctly captured.*/
#define RESET_SR_OFFSET                                          0x20
    /* Reset was caused by the SCB periphery reset signal*/
    #define RESET_SR_SCB_PERIPH_RESET_OFFSET                     0x0
    #define RESET_SR_SCB_PERIPH_RESET_MASK                       (0x01 << 0x0)
    /* Reset was caused by the SCB MSS reset register*/
    #define RESET_SR_SCB_MSS_RESET_OFFSET                        0x1
    #define RESET_SR_SCB_MSS_RESET_MASK                          (0x01 << 0x1)
    /* Reset was caused by the SCB CPU reset register*/
    #define RESET_SR_SCB_CPU_RESET_OFFSET                        0x2
    #define RESET_SR_SCB_CPU_RESET_MASK                          (0x01 << 0x2)
    /* Reset was caused by the Risc-V Debugger*/
    #define RESET_SR_DEBUGER_RESET_OFFSET                        0x3
    #define RESET_SR_DEBUGER_RESET_MASK                          (0x01 << 0x3)
    /* Reset was caused by the fabric*/
    #define RESET_SR_FABRIC_RESET_OFFSET                         0x4
    #define RESET_SR_FABRIC_RESET_MASK                           (0x01 << 0x4)
    /* Reset was caused by the watchdog*/
    #define RESET_SR_WDOG_RESET_OFFSET                           0x5
    #define RESET_SR_WDOG_RESET_MASK                             (0x01 << 0x5)
    /* Indicates that fabric asserted the GPIO reset inputs*/
    #define RESET_SR_GPIO_RESET_OFFSET                           0x6
    #define RESET_SR_GPIO_RESET_MASK                             (0x01 << 0x6)
    /* Indicates that SCB bus reset occurred (which causes warm reset of MS
    S)*/
    #define RESET_SR_SCB_BUS_RESET_OFFSET                        0x7
    #define RESET_SR_SCB_BUS_RESET_MASK                          (0x01 << 0x7)

/*Indicates the device status in particular the state of the FPGA fabric an
    d the MSS IO banks*/
#define DEVICE_STATUS_OFFSET                                     0x24
    /* Indicates the status of the core_up input from G5 Control.*/
    #define DEVICE_STATUS_CORE_UP_OFFSET                         0x0
    #define DEVICE_STATUS_CORE_UP_MASK                           (0x01 << 0x0)
    /* Indicates the status of the lp_state input from G5 Control.*/
    #define DEVICE_STATUS_LP_STATE_OFFSET                        0x1
    #define DEVICE_STATUS_LP_STATE_MASK                          (0x01 << 0x1)
    /* Indicates the status of the ff_in_progress input from G5 Control.*/
    #define DEVICE_STATUS_FF_IN_PROGRESS_OFFSET                  0x2
    #define DEVICE_STATUS_FF_IN_PROGRESS_MASK                    (0x01 << 0x2)
    /* Indicates the status of the flash_valid input from G5 Control.*/
    #define DEVICE_STATUS_FLASH_VALID_OFFSET                     0x3
    #define DEVICE_STATUS_FLASH_VALID_MASK                       (0x01 << 0x3)
    /* Power status of IO bank 2*/
    #define DEVICE_STATUS_IO_BANK_B2_STATUS_OFFSET               0x8
    #define DEVICE_STATUS_IO_BANK_B2_STATUS_MASK                 (0x01 << 0x8)
    /* Power status of IO bank 4*/
    #define DEVICE_STATUS_IO_BANK_B4_STATUS_OFFSET               0x9
    #define DEVICE_STATUS_IO_BANK_B4_STATUS_MASK                 (0x01 << 0x9)
    /* Power status of IO bank 5*/
    #define DEVICE_STATUS_IO_BANK_B5_STATUS_OFFSET               0xA
    #define DEVICE_STATUS_IO_BANK_B5_STATUS_MASK                 (0x01 << 0xA)
    /* Power status of IO bank 6*/
    #define DEVICE_STATUS_IO_BANK_B6_STATUS_OFFSET               0xB
    #define DEVICE_STATUS_IO_BANK_B6_STATUS_MASK                 (0x01 << 0xB)
    /* Indicates the status of the io_en input from G5 Control.*/
    #define DEVICE_STATUS_IO_EN_OFFSET                           0xC
    #define DEVICE_STATUS_IO_EN_MASK                             (0x01 << 0xC)

/*MSS Build Info*/
#define MSS_BUILD_OFFSET                                         0x28
    #define MSS_BUILD_REVISION_OFFSET                            0x0
    #define MSS_BUILD_REVISION_MASK                              (0xFFFFFFFF << 0x0)

/*U54-1 Fabric interrupt enable*/
#define FAB_INTEN_U54_1_OFFSET                                   0x40
    /* Enables the F2H_interrupts[31:0] to interrupt U54_1 directly*/
    #define FAB_INTEN_U54_1_ENABLE_OFFSET                        0x0
    #define FAB_INTEN_U54_1_ENABLE_MASK                          (0xFFFFFFFF << 0x0)

/*U54-2 Fabric interrupt enable*/
#define FAB_INTEN_U54_2_OFFSET                                   0x44
    /* Enables the F2H_interrupts[31:0] to interrupt U54_1 directly*/
    #define FAB_INTEN_U54_2_ENABLE_OFFSET                        0x0
    #define FAB_INTEN_U54_2_ENABLE_MASK                          (0xFFFFFFFF << 0x0)

/*U54-3 Fabric interrupt enable*/
#define FAB_INTEN_U54_3_OFFSET                                   0x48
    /* Enables the F2H_interrupts[31:0] to interrupt U54_1 directly*/
    #define FAB_INTEN_U54_3_ENABLE_OFFSET                        0x0
    #define FAB_INTEN_U54_3_ENABLE_MASK                          (0xFFFFFFFF << 0x0)

/*U54-4 Fabric interrupt enable*/
#define FAB_INTEN_U54_4_OFFSET                                   0x4C
    /* Enables the F2H_interrupts[31:0] to interrupt U54_1 directly*/
    #define FAB_INTEN_U54_4_ENABLE_OFFSET                        0x0
    #define FAB_INTEN_U54_4_ENABLE_MASK                          (0xFFFFFFFF << 0x0)

/*Allows the Ethernat interrupts to be directly routed to the U54 CPUS.*/
#define FAB_INTEN_MISC_OFFSET                                    0x50
    /* Enables the Ethernet MAC0 to interrupt U54_1 directly*/
    #define FAB_INTEN_MISC_MAC0_U54_1_OFFSET                     0x0
    #define FAB_INTEN_MISC_MAC0_U54_1_MASK                       (0x01 << 0x0)
    /* Enables the Ethernet MAC0 to interrupt U54_1 directly*/
    #define FAB_INTEN_MISC_MAC0_U54_2_OFFSET                     0x1
    #define FAB_INTEN_MISC_MAC0_U54_2_MASK                       (0x01 << 0x1)
    /* Enables the Ethernet MAC1 to interrupt U54_1 directly*/
    #define FAB_INTEN_MISC_MAC1_U54_3_OFFSET                     0x2
    #define FAB_INTEN_MISC_MAC1_U54_3_MASK                       (0x01 << 0x2)
    /* Enables the Ethernet MAC1 to interrupt U54_1 directly*/
    #define FAB_INTEN_MISC_MAC1_U54_4_OFFSET                     0x3
    #define FAB_INTEN_MISC_MAC1_U54_4_MASK                       (0x01 << 0x3)

/*Switches GPIO interrupt from PAD to Fabric GPIO*/
#define GPIO_INTERRUPT_FAB_CR_OFFSET                             0x54
    /* Setting these  bits will disable the Pad interrupt and enable the fabric
    GPIO interrupt for bits 31:0. When the bit is set the Pad interrupt will
    be ORED into the GPIO0 & GPIO1  non-direct  interrupts. When the bit is
    not set the Fabric interrupt is ORED into the GPIO2  non-direct interrupt.
    To prevent ORING then the interrupt should not be enabled in the GPIO block
    */
    #define GPIO_INTERRUPT_FAB_CR_SELECT_OFFSET                  0x0
    #define GPIO_INTERRUPT_FAB_CR_SELECT_MASK                    (0xFFFFFFFF << 0x0)

/*"AMP Mode peripheral mapping register. When the register bit is '0' the p
    eripheral is mapped into the 0x2000000 address range using AXI bus 5 from t
    he Coreplex. When the register bit is '1' the peripheral is mapped into the
     0x28000000 address range using AXI bus 6 from the Coreplex."*/
#define APBBUS_CR_OFFSET                                         0x80
    /* */
    #define APBBUS_CR_MMUART0_OFFSET                             0x0
    #define APBBUS_CR_MMUART0_MASK                               (0x01 << 0x0)
    /* */
    #define APBBUS_CR_MMUART1_OFFSET                             0x1
    #define APBBUS_CR_MMUART1_MASK                               (0x01 << 0x1)
    /* */
    #define APBBUS_CR_MMUART2_OFFSET                             0x2
    #define APBBUS_CR_MMUART2_MASK                               (0x01 << 0x2)
    /* */
    #define APBBUS_CR_MMUART3_OFFSET                             0x3
    #define APBBUS_CR_MMUART3_MASK                               (0x01 << 0x3)
    /* */
    #define APBBUS_CR_MMUART4_OFFSET                             0x4
    #define APBBUS_CR_MMUART4_MASK                               (0x01 << 0x4)
    /* */
    #define APBBUS_CR_WDOG0_OFFSET                               0x5
    #define APBBUS_CR_WDOG0_MASK                                 (0x01 << 0x5)
    /* */
    #define APBBUS_CR_WDOG1_OFFSET                               0x6
    #define APBBUS_CR_WDOG1_MASK                                 (0x01 << 0x6)
    /* */
    #define APBBUS_CR_WDOG2_OFFSET                               0x7
    #define APBBUS_CR_WDOG2_MASK                                 (0x01 << 0x7)
    /* */
    #define APBBUS_CR_WDOG3_OFFSET                               0x8
    #define APBBUS_CR_WDOG3_MASK                                 (0x01 << 0x8)
    /* */
    #define APBBUS_CR_WDOG4_OFFSET                               0x9
    #define APBBUS_CR_WDOG4_MASK                                 (0x01 << 0x9)
    /* */
    #define APBBUS_CR_SPI0_OFFSET                                0xA
    #define APBBUS_CR_SPI0_MASK                                  (0x01 << 0xA)
    /* */
    #define APBBUS_CR_SPI1_OFFSET                                0xB
    #define APBBUS_CR_SPI1_MASK                                  (0x01 << 0xB)
    /* */
    #define APBBUS_CR_I2C0_OFFSET                                0xC
    #define APBBUS_CR_I2C0_MASK                                  (0x01 << 0xC)
    /* */
    #define APBBUS_CR_I2C1_OFFSET                                0xD
    #define APBBUS_CR_I2C1_MASK                                  (0x01 << 0xD)
    /* */
    #define APBBUS_CR_CAN0_OFFSET                                0xE
    #define APBBUS_CR_CAN0_MASK                                  (0x01 << 0xE)
    /* */
    #define APBBUS_CR_CAN1_OFFSET                                0xF
    #define APBBUS_CR_CAN1_MASK                                  (0x01 << 0xF)
    /* */
    #define APBBUS_CR_GEM0_OFFSET                                0x10
    #define APBBUS_CR_GEM0_MASK                                  (0x01 << 0x10)
    /* */
    #define APBBUS_CR_GEM1_OFFSET                                0x11
    #define APBBUS_CR_GEM1_MASK                                  (0x01 << 0x11)
    /* */
    #define APBBUS_CR_TIMER_OFFSET                               0x12
    #define APBBUS_CR_TIMER_MASK                                 (0x01 << 0x12)
    /* */
    #define APBBUS_CR_GPIO0_OFFSET                               0x13
    #define APBBUS_CR_GPIO0_MASK                                 (0x01 << 0x13)
    /* */
    #define APBBUS_CR_GPIO1_OFFSET                               0x14
    #define APBBUS_CR_GPIO1_MASK                                 (0x01 << 0x14)
    /* */
    #define APBBUS_CR_GPIO2_OFFSET                               0x15
    #define APBBUS_CR_GPIO2_MASK                                 (0x01 << 0x15)
    /* */
    #define APBBUS_CR_RTC_OFFSET                                 0x16
    #define APBBUS_CR_RTC_MASK                                   (0x01 << 0x16)
    /* */
    #define APBBUS_CR_H2FINT_OFFSET                              0x17
    #define APBBUS_CR_H2FINT_MASK                                (0x01 << 0x17)

/*"Enables the clock to the MSS peripheral. By turning clocks off dynamic power
    can be saved. When the clock is off the peripheral  should not be accessed
    the access may be ignored return unspecified data or result in bus response
    error."*/
#define SUBBLK_CLOCK_CR_OFFSET                                   0x84
    /* */
    #define SUBBLK_CLOCK_CR_ENVM_OFFSET                          0x0
    #define SUBBLK_CLOCK_CR_ENVM_MASK                            (0x01 << 0x0)
    /* */
    #define SUBBLK_CLOCK_CR_MAC0_OFFSET                          0x1
    #define SUBBLK_CLOCK_CR_MAC0_MASK                            (0x01 << 0x1)
    /* */
    #define SUBBLK_CLOCK_CR_MAC1_OFFSET                          0x2
    #define SUBBLK_CLOCK_CR_MAC1_MASK                            (0x01 << 0x2)
    /* */
    #define SUBBLK_CLOCK_CR_MMC_OFFSET                           0x3
    #define SUBBLK_CLOCK_CR_MMC_MASK                             (0x01 << 0x3)
    /* */
    #define SUBBLK_CLOCK_CR_TIMER_OFFSET                         0x4
    #define SUBBLK_CLOCK_CR_TIMER_MASK                           (0x01 << 0x4)
    /* */
    #define SUBBLK_CLOCK_CR_MMUART0_OFFSET                       0x5
    #define SUBBLK_CLOCK_CR_MMUART0_MASK                         (0x01 << 0x5)
    /* */
    #define SUBBLK_CLOCK_CR_MMUART1_OFFSET                       0x6
    #define SUBBLK_CLOCK_CR_MMUART1_MASK                         (0x01 << 0x6)
    /* */
    #define SUBBLK_CLOCK_CR_MMUART2_OFFSET                       0x7
    #define SUBBLK_CLOCK_CR_MMUART2_MASK                         (0x01 << 0x7)
    /* */
    #define SUBBLK_CLOCK_CR_MMUART3_OFFSET                       0x8
    #define SUBBLK_CLOCK_CR_MMUART3_MASK                         (0x01 << 0x8)
    /* */
    #define SUBBLK_CLOCK_CR_MMUART4_OFFSET                       0x9
    #define SUBBLK_CLOCK_CR_MMUART4_MASK                         (0x01 << 0x9)
    /* */
    #define SUBBLK_CLOCK_CR_SPI0_OFFSET                          0xA
    #define SUBBLK_CLOCK_CR_SPI0_MASK                            (0x01 << 0xA)
    /* */
    #define SUBBLK_CLOCK_CR_SPI1_OFFSET                          0xB
    #define SUBBLK_CLOCK_CR_SPI1_MASK                            (0x01 << 0xB)
    /* */
    #define SUBBLK_CLOCK_CR_I2C0_OFFSET                          0xC
    #define SUBBLK_CLOCK_CR_I2C0_MASK                            (0x01 << 0xC)
    /* */
    #define SUBBLK_CLOCK_CR_I2C1_OFFSET                          0xD
    #define SUBBLK_CLOCK_CR_I2C1_MASK                            (0x01 << 0xD)
    /* */
    #define SUBBLK_CLOCK_CR_CAN0_OFFSET                          0xE
    #define SUBBLK_CLOCK_CR_CAN0_MASK                            (0x01 << 0xE)
    /* */
    #define SUBBLK_CLOCK_CR_CAN1_OFFSET                          0xF
    #define SUBBLK_CLOCK_CR_CAN1_MASK                            (0x01 << 0xF)
    /* */
    #define SUBBLK_CLOCK_CR_USB_OFFSET                           0x10
    #define SUBBLK_CLOCK_CR_USB_MASK                             (0x01 << 0x10)
    /* */
    #define SUBBLK_CLOCK_CR_RSVD_OFFSET                          0x11
    #define SUBBLK_CLOCK_CR_RSVD_MASK                            (0x01 << 0x11)
    /* */
    #define SUBBLK_CLOCK_CR_RTC_OFFSET                           0x12
    #define SUBBLK_CLOCK_CR_RTC_MASK                             (0x01 << 0x12)
    /* */
    #define SUBBLK_CLOCK_CR_QSPI_OFFSET                          0x13
    #define SUBBLK_CLOCK_CR_QSPI_MASK                            (0x01 << 0x13)
    /* */
    #define SUBBLK_CLOCK_CR_GPIO0_OFFSET                         0x14
    #define SUBBLK_CLOCK_CR_GPIO0_MASK                           (0x01 << 0x14)
    /* */
    #define SUBBLK_CLOCK_CR_GPIO1_OFFSET                         0x15
    #define SUBBLK_CLOCK_CR_GPIO1_MASK                           (0x01 << 0x15)
    /* */
    #define SUBBLK_CLOCK_CR_GPIO2_OFFSET                         0x16
    #define SUBBLK_CLOCK_CR_GPIO2_MASK                           (0x01 << 0x16)
    /* */
    #define SUBBLK_CLOCK_CR_DDRC_OFFSET                          0x17
    #define SUBBLK_CLOCK_CR_DDRC_MASK                            (0x01 << 0x17)
    /* */
    #define SUBBLK_CLOCK_CR_FIC0_OFFSET                          0x18
    #define SUBBLK_CLOCK_CR_FIC0_MASK                            (0x01 << 0x18)
    /* */
    #define SUBBLK_CLOCK_CR_FIC1_OFFSET                          0x19
    #define SUBBLK_CLOCK_CR_FIC1_MASK                            (0x01 << 0x19)
    /* */
    #define SUBBLK_CLOCK_CR_FIC2_OFFSET                          0x1A
    #define SUBBLK_CLOCK_CR_FIC2_MASK                            (0x01 << 0x1A)
    /* */
    #define SUBBLK_CLOCK_CR_FIC3_OFFSET                          0x1B
    #define SUBBLK_CLOCK_CR_FIC3_MASK                            (0x01 << 0x1B)
    /* */
    #define SUBBLK_CLOCK_CR_ATHENA_OFFSET                        0x1C
    #define SUBBLK_CLOCK_CR_ATHENA_MASK                          (0x01 << 0x1C)
    /* */
    #define SUBBLK_CLOCK_CR_CFM_OFFSET                           0x1D
    #define SUBBLK_CLOCK_CR_CFM_MASK                             (0x01 << 0x1D)

/*"Holds the MSS peripherals in reset. When in reset the peripheral should
    not be accessed the acess may be ignored return unspecified data or result
    in bus response error."*/
#define SOFT_RESET_CR_OFFSET                                     0x88
    /* */
    #define SOFT_RESET_CR_ENVM_OFFSET                            0x0
    #define SOFT_RESET_CR_ENVM_MASK                              (0x01 << 0x0)
    /* */
    #define SOFT_RESET_CR_MAC0_OFFSET                            0x1
    #define SOFT_RESET_CR_MAC0_MASK                              (0x01 << 0x1)
    /* */
    #define SOFT_RESET_CR_MAC1_OFFSET                            0x2
    #define SOFT_RESET_CR_MAC1_MASK                              (0x01 << 0x2)
    /* */
    #define SOFT_RESET_CR_MMC_OFFSET                             0x3
    #define SOFT_RESET_CR_MMC_MASK                               (0x01 << 0x3)
    /* */
    #define SOFT_RESET_CR_TIMER_OFFSET                           0x4
    #define SOFT_RESET_CR_TIMER_MASK                             (0x01 << 0x4)
    /* */
    #define SOFT_RESET_CR_MMUART0_OFFSET                         0x5
    #define SOFT_RESET_CR_MMUART0_MASK                           (0x01 << 0x5)
    /* */
    #define SOFT_RESET_CR_MMUART1_OFFSET                         0x6
    #define SOFT_RESET_CR_MMUART1_MASK                           (0x01 << 0x6)
    /* */
    #define SOFT_RESET_CR_MMUART2_OFFSET                         0x7
    #define SOFT_RESET_CR_MMUART2_MASK                           (0x01 << 0x7)
    /* */
    #define SOFT_RESET_CR_MMUART3_OFFSET                         0x8
    #define SOFT_RESET_CR_MMUART3_MASK                           (0x01 << 0x8)
    /* */
    #define SOFT_RESET_CR_MMUART4_OFFSET                         0x9
    #define SOFT_RESET_CR_MMUART4_MASK                           (0x01 << 0x9)
    /* */
    #define SOFT_RESET_CR_SPI0_OFFSET                            0xA
    #define SOFT_RESET_CR_SPI0_MASK                              (0x01 << 0xA)
    /* */
    #define SOFT_RESET_CR_SPI1_OFFSET                            0xB
    #define SOFT_RESET_CR_SPI1_MASK                              (0x01 << 0xB)
    /* */
    #define SOFT_RESET_CR_I2C0_OFFSET                            0xC
    #define SOFT_RESET_CR_I2C0_MASK                              (0x01 << 0xC)
    /* */
    #define SOFT_RESET_CR_I2C1_OFFSET                            0xD
    #define SOFT_RESET_CR_I2C1_MASK                              (0x01 << 0xD)
    /* */
    #define SOFT_RESET_CR_CAN0_OFFSET                            0xE
    #define SOFT_RESET_CR_CAN0_MASK                              (0x01 << 0xE)
    /* */
    #define SOFT_RESET_CR_CAN1_OFFSET                            0xF
    #define SOFT_RESET_CR_CAN1_MASK                              (0x01 << 0xF)
    /* */
    #define SOFT_RESET_CR_USB_OFFSET                             0x10
    #define SOFT_RESET_CR_USB_MASK                               (0x01 << 0x10)
    /* */
    #define SOFT_RESET_CR_FPGA_OFFSET                            0x11
    #define SOFT_RESET_CR_FPGA_MASK                              (0x01 << 0x11)
    /* */
    #define SOFT_RESET_CR_RTC_OFFSET                             0x12
    #define SOFT_RESET_CR_RTC_MASK                               (0x01 << 0x12)
    /* */
    #define SOFT_RESET_CR_QSPI_OFFSET                            0x13
    #define SOFT_RESET_CR_QSPI_MASK                              (0x01 << 0x13)
    /* */
    #define SOFT_RESET_CR_GPIO0_OFFSET                           0x14
    #define SOFT_RESET_CR_GPIO0_MASK                             (0x01 << 0x14)
    /* */
    #define SOFT_RESET_CR_GPIO1_OFFSET                           0x15
    #define SOFT_RESET_CR_GPIO1_MASK                             (0x01 << 0x15)
    /* */
    #define SOFT_RESET_CR_GPIO2_OFFSET                           0x16
    #define SOFT_RESET_CR_GPIO2_MASK                             (0x01 << 0x16)
    /* */
    #define SOFT_RESET_CR_DDRC_OFFSET                            0x17
    #define SOFT_RESET_CR_DDRC_MASK                              (0x01 << 0x17)
    /* */
    #define SOFT_RESET_CR_FIC0_OFFSET                            0x18
    #define SOFT_RESET_CR_FIC0_MASK                              (0x01 << 0x18)
    /* */
    #define SOFT_RESET_CR_FIC1_OFFSET                            0x19
    #define SOFT_RESET_CR_FIC1_MASK                              (0x01 << 0x19)
    /* */
    #define SOFT_RESET_CR_FIC2_OFFSET                            0x1A
    #define SOFT_RESET_CR_FIC2_MASK                              (0x01 << 0x1A)
    /* */
    #define SOFT_RESET_CR_FIC3_OFFSET                            0x1B
    #define SOFT_RESET_CR_FIC3_MASK                              (0x01 << 0x1B)
    /* */
    #define SOFT_RESET_CR_ATHENA_OFFSET                          0x1C
    #define SOFT_RESET_CR_ATHENA_MASK                            (0x01 << 0x1C)
    /* */
    #define SOFT_RESET_CR_CFM_OFFSET                             0x1D
    #define SOFT_RESET_CR_CFM_MASK                               (0x01 << 0x1D)
    /* Reset to Corner SGMII block*/
    #define SOFT_RESET_CR_SGMII_OFFSET                           0x1E
    #define SOFT_RESET_CR_SGMII_MASK                             (0x01 << 0x1E)

/*Configures how many outstanding transfers the AXI-AHB bridges in front of
    f the USB and Crypto blocks should allow. (See Synopsys AXI-AHB bridge docu
    mentation)*/
#define AHBAXI_CR_OFFSET                                         0x8C
    /* Number of outstanding write transactions to USB block*/
    #define AHBAXI_CR_USB_WBCNT_OFFSET                           0x0
    #define AHBAXI_CR_USB_WBCNT_MASK                             (0x0F << 0x0)
    /* Number of outstanding read transactions to USB block*/
    #define AHBAXI_CR_USB_RBCNT_OFFSET                           0x4
    #define AHBAXI_CR_USB_RBCNT_MASK                             (0x0F << 0x4)
    /* Number of outstanding write transactions to Athena block*/
    #define AHBAXI_CR_ATHENA_WBCNT_OFFSET                        0x8
    #define AHBAXI_CR_ATHENA_WBCNT_MASK                          (0x0F << 0x8)
    /* Number of outstanding read transactions to Athena block*/
    #define AHBAXI_CR_ATHENA_RBCNT_OFFSET                        0xC
    #define AHBAXI_CR_ATHENA_RBCNT_MASK                          (0x0F << 0xC)

/*Configures the two AHB-APB bridges on S5 and S6*/
#define AHBAPB_CR_OFFSET                                         0x90
    /* Enables posted mode on the AHB-APB bridge when set the AHB write cyc
    le will complete before the APB write cycle completes.*/
    #define AHBAPB_CR_APB0_POSTED_OFFSET                         0x0
    #define AHBAPB_CR_APB0_POSTED_MASK                           (0x01 << 0x0)
    /* Enables posted mode on the AHB-APB bridge when set the AHB write cyc
    le will complete before the APB write cycle completes.*/
    #define AHBAPB_CR_APB1_POSTED_OFFSET                         0x1
    #define AHBAPB_CR_APB1_POSTED_MASK                           (0x01 << 0x1)

/*MSS Corner APB interface controls*/
#define DFIAPB_CR_OFFSET                                         0x98
    /* Turns on the APB clock to the MSS Corner is off at reset. Once corne
    r blocks is configured the firmware may turn off the clock but periodically
     should turn back on to allow refresh of TMR registers inside the corner bl
    ock. */
    #define DFIAPB_CR_CLOCKON_OFFSET                             0x0
    #define DFIAPB_CR_CLOCKON_MASK                               (0x01 << 0x0)
    /* Asserts the APB reset to the MSS corner is asserted at MSS reset.*/
    #define DFIAPB_CR_RESET_OFFSET                               0x1
    #define DFIAPB_CR_RESET_MASK                                 (0x01 << 0x1)

/*GPIO Blocks reset control*/
#define GPIO_CR_OFFSET                                           0x9C
    /* "This signal selects whether the associated byte is reset by soft re
    set or the the MSS_GPIO_RESET_N signal from the FPGA fabric. The allowed va
    lues are:* 0: Selects  MSS_GPIO_RESET_N signal from the FPGA fabric.* 1
    : Selects  the GPIO to be reset by the GPIO block soft reset signal .Bit 0
    controls GPIO0 [7:0]  and bit  1 GPIO[15:8]The master MSS reset will also r
    eset the GPIO register if not configured to use fabric reset."*/
    #define GPIO_CR_GPIO0_SOFT_RESET_SELECT_OFFSET               0x0
    #define GPIO_CR_GPIO0_SOFT_RESET_SELECT_MASK                 (0x03 << 0x0)
    /* "Sets the reset value off the GPIO0 per byteBit 0 controls GPIO0 [7:
    0]  and bit  1 GPIO[15:8]"*/
    #define GPIO_CR_GPIO0_DEFAULT_OFFSET                         0x4
    #define GPIO_CR_GPIO0_DEFAULT_MASK                           (0x03 << 0x4)
    /* "This signal selects whether the associated byte is reset by soft re
    set or the the MSS_GPIO_RESET_N signal from the FPGA fabric. The allowed va
    lues are:* 0: Selects  MSS_GPIO_RESET_N signal from the FPGA fabric.* 1
    : Selects  the GPIO to be reset by the GPIO block soft reset signal .Bit 0
    controls GPIO0 [7:0] bit  1 GPIO[15:8] and bit 2 GPIO[23:16]The master MSS
    reset will also reset the GPIO register if not configured to use fabric res
    et."*/
    #define GPIO_CR_GPIO1_SOFT_RESET_SELECT_OFFSET               0x8
    #define GPIO_CR_GPIO1_SOFT_RESET_SELECT_MASK                 (0x07 << 0x8)
    /* "Sets the reset value off the GPIO0 per byteBit 0 controls GPIO0 [7:
    0] bit  1 GPIO[15:8] and bit 2 GPIO[23:16]"*/
    #define GPIO_CR_GPIO1_DEFAULT_OFFSET                         0xC
    #define GPIO_CR_GPIO1_DEFAULT_MASK                           (0x07 << 0xC)
    /* "This signal selects whether the associated byte is reset by soft re
    set or the the MSS_GPIO_RESET_N signal from the FPGA fabric. The allowed va
    lues are:* 0: Selects  MSS_GPIO_RESET_N signal from the FPGA fabric.* 1
    : Selects  the GPIO to be reset by the GPIO block soft reset signal .Bit 0
    controls GPIO0 [7:0] bit  1 GPIO[15:8] and bit 1 GPIO[23:16] and bit 3 GPIO
    [31:24]The master MSS reset will also reset the GPIO register if not config
    ured to use fabric reset."*/
    #define GPIO_CR_GPIO2_SOFT_RESET_SELECT_OFFSET               0x10
    #define GPIO_CR_GPIO2_SOFT_RESET_SELECT_MASK                 (0x0F << 0x10)
    /* "Sets the reset value off the GPIO0 per byteBit 0 controls GPIO0 [7:
    0] bit  1 GPIO[15:8] and bit 1 GPIO[23:16] and bit 3 GPIO[31:24]"*/
    #define GPIO_CR_GPIO2_DEFAULT_OFFSET                         0x14
    #define GPIO_CR_GPIO2_DEFAULT_MASK                           (0x0F << 0x14)

/*MAC0 configuration register*/
#define MAC0_CR_OFFSET                                           0xA4
    /* Current speed mode on the MAC*/
    #define MAC0_CR_SPEED_MODE_OFFSET                            0x0
    #define MAC0_CR_SPEED_MODE_MASK                              (0x0F << 0x0)

/*MAC1 configuration register*/
#define MAC1_CR_OFFSET                                           0xA8
    /* Current speed mode on the MAC*/
    #define MAC1_CR_SPEED_MODE_OFFSET                            0x0
    #define MAC1_CR_SPEED_MODE_MASK                              (0x0F << 0x0)

/*USB Configuration register*/
#define USB_CR_OFFSET                                            0xAC
    /* "Configures USB for Single-Data Rate(SDR) mode or Double-Data Rate(D
    DR) mode. 0 - SDR Mode is selected1 - DDR Mode is selected (Not supported i
    n G5 or G5)"*/
    #define USB_CR_DDR_SELECT_OFFSET                             0x0
    #define USB_CR_DDR_SELECT_MASK                               (0x01 << 0x0)
    /* When '1' will stops the clock to the USB core when the core asserts
    its POWERDOWN output. For G4 compatibility this bit defaults to 0.*/
    #define USB_CR_POWERDOWN_ENABLE_OFFSET                       0x1
    #define USB_CR_POWERDOWN_ENABLE_MASK                         (0x01 << 0x1)
    /* Indicates that the USB CLK may be stopped to save power. Derived fro
    m combination of signals from CLK & XCLK flip-flops AVALID VBUSVALID and LI
    NESTATE. When asserted the USB clock into the core is stopped.*/
    #define USB_CR_POWERDOWN_OFFSET                              0x2
    #define USB_CR_POWERDOWN_MASK                                (0x01 << 0x2)
    /* Set when entry is made into CarKit mode and cleared on exit from Car
    Kit mode.*/
    #define USB_CR_LPI_CARKIT_EN_OFFSET                          0x3
    #define USB_CR_LPI_CARKIT_EN_MASK                            (0x01 << 0x3)

/*Crypto Mesh control and status register*/
#define MESH_CR_OFFSET                                           0xB0
    /* Writing a 1 will start the Mesh System*/
    #define MESH_CR_START_OFFSET                                 0x0
    #define MESH_CR_START_MASK                                   (0x01 << 0x0)
    /* "Sets the amount of time that the mesh is held active for actual hol
    d time includes up to 256 us of random variation.Minimum Time = 1 + 256 * v
    alue   usMaximum Time = 1 +  256 * (1+value)   usValue must be greater than
     0"*/
    #define MESH_CR_HOLD_OFFSET                                  0x1
    #define MESH_CR_HOLD_MASK                                    (0xFFF << 0x1)
    /* When set will inject an error in the mesh*/
    #define MESH_CR_INJECT_ERROR_OFFSET                          0x10
    #define MESH_CR_INJECT_ERROR_MASK                            (0x01 << 0x10)
    /* Indicates that Mesh detected an error. Cleared by writing a '1'*/
    #define MESH_CR_MESH_ERROR_OFFSET                            0x18
    #define MESH_CR_MESH_ERROR_MASK                              (0x01 << 0x18)
    /* Indicates that the Mesh is functioning correctly. Will be set approx
    imately  520 clock cycles after mesh started and stay set as long as the me
    sh is not detecting any errors.*/
    #define MESH_CR_OKAY_OFFSET                                  0x19
    #define MESH_CR_OKAY_MASK                                    (0x01 << 0x19)

/*Crypto mesh seed and update rate*/
#define MESH_SEED_CR_OFFSET                                      0xB4
    /* Sets the mesh seed value any value may be used zero should be avoide
    d*/
    #define MESH_SEED_CR_SEED_OFFSET                             0x0
    #define MESH_SEED_CR_SEED_MASK                               (0x7FFFFF << 0x0)
    /* Sets the rate that the mesh value is changed. Rate = AHBCLK/(clkrate
    +1). Rate must be less than 1MHz setting slower will reduce power consumpti
    on.*/
    #define MESH_SEED_CR_CLKRATE_OFFSET                          0x18
    #define MESH_SEED_CR_CLKRATE_MASK                            (0xFF << 0x18)

/*ENVM AHB Controller setup*/
#define ENVM_CR_OFFSET                                           0xB8
    /* "Sets the number of  AHB cycles used to generate the PNVM clockClock
      period = (Value+1) * (1000/AHBFREQMHZ)         Value must be 1 to 63  (0
    defaults to 15)e.g.11  will generate a 40ns period  25MHz clock if the AHB
    clock is 250MHz15  will generate a 40ns period  25MHz clock if the AHB cloc
    k is 400MHz"*/
    #define ENVM_CR_CLOCK_PERIOD_OFFSET                          0x0
    #define ENVM_CR_CLOCK_PERIOD_MASK                            (0x3F << 0x0)
    /* Indicates the eNVM is running at the configured divider rate. */
    #define ENVM_CR_CLOCK_OKAY_OFFSET                            0x6
    #define ENVM_CR_CLOCK_OKAY_MASK                              (0x01 << 0x6)
    /* When '1' the PNVM clock will be always generated and not stopped bet
    ween access cycles. Setting this will increase access latency but mean that
     the PNVM clock operates at a stable rate.*/
    #define ENVM_CR_CLOCK_CONTINUOUS_OFFSET                      0x8
    #define ENVM_CR_CLOCK_CONTINUOUS_MASK                        (0x01 << 0x8)
    /* When set suppresses clock edge between C-Bus access cycles so that t
    hey appear as consecutive access cycles.*/
    #define ENVM_CR_CLOCK_SUPPRESS_OFFSET                        0x9
    #define ENVM_CR_CLOCK_SUPPRESS_MASK                          (0x01 << 0x9)
    /* "Enables ""read-ahead"" on the ENVM controller. The controller will
    automatically read the next PNVM location as soon as possible ahead of the
    AHB request. This will improve read performance when incrementing though
    memory as the NVM reads and AHB cycles are pipelined. When set non incrementing
    accesses will take longer as the controller may be in the process of reading
    the next address and the PNVM cycle needs to complete prior to starting
    the required read"*/
    #define ENVM_CR_READAHEAD_OFFSET                             0x10
    #define ENVM_CR_READAHEAD_MASK                               (0x01 << 0x10)
    /* When '1' the controller will initiate separate ENVM reads for all reads.
    No buffering or speculative operations will be carried out. When performing
    word reads incrementing through PNVM each location will be read twice
    (intended for test use)*/
    #define ENVM_CR_SLOWREAD_OFFSET                              0x11
    #define ENVM_CR_SLOWREAD_MASK                                (0x01 << 0x11)
    /* Enable the ENVM interrupt*/
    #define ENVM_CR_INTERRUPT_ENABLE_OFFSET                      0x12
    #define ENVM_CR_INTERRUPT_ENABLE_MASK                        (0x01 << 0x12)
    /* "Sets the duration of the timer used to detect a non response of slow
    response from the PNVM on C and R bus accesses.Timer Duration = Value *
    (1000/AHBFREQMHZ)   0x00: Timer disabled. If the timer expires the AHB cycle
    is terminates using the HRESP protocol"*/
    #define ENVM_CR_TIMER_OFFSET                                 0x18
    #define ENVM_CR_TIMER_MASK                                   (0xFF << 0x18)

/*Reserved*/
#define RESERVED_BC_OFFSET                                       0xBC
    /* Reserved register address*/
    #define RESERVED_BC_RESERVED_OFFSET                          0x0
    #define RESERVED_BC_RESERVED_MASK                            (0x01 << 0x0)

/*QOS Athena USB & MMC Configuration*/
#define QOS_PERIPHERAL_CR_OFFSET                                 0xC0
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_PERIPHERAL_CR_ATHENA_READ_OFFSET                 0x0
    #define QOS_PERIPHERAL_CR_ATHENA_READ_MASK                   (0x0F << 0x0)
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_PERIPHERAL_CR_ATHENA_WRITE_OFFSET                0x4
    #define QOS_PERIPHERAL_CR_ATHENA_WRITE_MASK                  (0x0F << 0x4)
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_PERIPHERAL_CR_USB_READ_OFFSET                    0x8
    #define QOS_PERIPHERAL_CR_USB_READ_MASK                      (0x0F << 0x8)
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_PERIPHERAL_CR_USB_WRITE_OFFSET                   0xC
    #define QOS_PERIPHERAL_CR_USB_WRITE_MASK                     (0x0F << 0xC)
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_PERIPHERAL_CR_MMC_READ_OFFSET                    0x10
    #define QOS_PERIPHERAL_CR_MMC_READ_MASK                      (0x0F << 0x10)
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_PERIPHERAL_CR_MMC_WRITE_OFFSET                   0x14
    #define QOS_PERIPHERAL_CR_MMC_WRITE_MASK                     (0x0F << 0x14)
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_PERIPHERAL_CR_TRACE_READ_OFFSET                  0x18
    #define QOS_PERIPHERAL_CR_TRACE_READ_MASK                    (0x0F << 0x18)
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_PERIPHERAL_CR_TRACE_WRITE_OFFSET                 0x1C
    #define QOS_PERIPHERAL_CR_TRACE_WRITE_MASK                   (0x0F << 0x1C)

/*QOS Configuration Coreplex*/
#define QOS_CPLEXIO_CR_OFFSET                                    0xC4
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_CPLEXIO_CR_DEVICE0_READ_OFFSET                   0x0
    #define QOS_CPLEXIO_CR_DEVICE0_READ_MASK                     (0x0F << 0x0)
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_CPLEXIO_CR_DEVICE0_WRITE_OFFSET                  0x4
    #define QOS_CPLEXIO_CR_DEVICE0_WRITE_MASK                    (0x0F << 0x4)
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_CPLEXIO_CR_DEVICE1_READ_OFFSET                   0x8
    #define QOS_CPLEXIO_CR_DEVICE1_READ_MASK                     (0x0F << 0x8)
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_CPLEXIO_CR_DEVICE1_WRITE_OFFSET                  0xC
    #define QOS_CPLEXIO_CR_DEVICE1_WRITE_MASK                    (0x0F << 0xC)
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_CPLEXIO_CR_FABRIC0_READ_OFFSET                   0x10
    #define QOS_CPLEXIO_CR_FABRIC0_READ_MASK                     (0x0F << 0x10)
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_CPLEXIO_CR_FABRIC0_WRITE_OFFSET                  0x14
    #define QOS_CPLEXIO_CR_FABRIC0_WRITE_MASK                    (0x0F << 0x14)
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_CPLEXIO_CR_FABRIC1_READ_OFFSET                   0x18
    #define QOS_CPLEXIO_CR_FABRIC1_READ_MASK                     (0x0F << 0x18)
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_CPLEXIO_CR_FABRIC1_WRITE_OFFSET                  0x1C
    #define QOS_CPLEXIO_CR_FABRIC1_WRITE_MASK                    (0x0F << 0x1C)

/*QOS configuration DDRC*/
#define QOS_CPLEXDDR_CR_OFFSET                                   0xC8
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_CPLEXDDR_CR_CACHE_READ_OFFSET                    0x0
    #define QOS_CPLEXDDR_CR_CACHE_READ_MASK                      (0x0F << 0x0)
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_CPLEXDDR_CR_CACHE_WRITE_OFFSET                   0x4
    #define QOS_CPLEXDDR_CR_CACHE_WRITE_MASK                     (0x0F << 0x4)
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_CPLEXDDR_CR_NCACHE_READ_OFFSET                   0x8
    #define QOS_CPLEXDDR_CR_NCACHE_READ_MASK                     (0x0F << 0x8)
    /* Sets the QOS value from the specified device into the switch*/
    #define QOS_CPLEXDDR_CR_NCACHE_WRITE_OFFSET                  0xC
    #define QOS_CPLEXDDR_CR_NCACHE_WRITE_MASK                    (0x0F << 0xC)

/*Indicates that a master caused a MPU violation. Interrupts via maintenanc
    e interrupt.*/
#define MPU_VIOLATION_SR_OFFSET                                  0xF0
    /* Bit is set on violation. Cleared by writing '1'*/
    #define MPU_VIOLATION_SR_FIC0_OFFSET                         0x0
    #define MPU_VIOLATION_SR_FIC0_MASK                           (0x01 << 0x0)
    /* Bit is set on violation. Cleared by writing '1'*/
    #define MPU_VIOLATION_SR_FIC1_OFFSET                         0x1
    #define MPU_VIOLATION_SR_FIC1_MASK                           (0x01 << 0x1)
    /* Bit is set on violation. Cleared by writing '1'*/
    #define MPU_VIOLATION_SR_FIC2_OFFSET                         0x2
    #define MPU_VIOLATION_SR_FIC2_MASK                           (0x01 << 0x2)
    /* Bit is set on violation. Cleared by writing '1'*/
    #define MPU_VIOLATION_SR_ATHENA_OFFSET                       0x3
    #define MPU_VIOLATION_SR_ATHENA_MASK                         (0x01 << 0x3)
    /* Bit is set on violation. Cleared by writing '1'*/
    #define MPU_VIOLATION_SR_GEM0_OFFSET                         0x4
    #define MPU_VIOLATION_SR_GEM0_MASK                           (0x01 << 0x4)
    /* Bit is set on violation. Cleared by writing '1'*/
    #define MPU_VIOLATION_SR_GEM1_OFFSET                         0x5
    #define MPU_VIOLATION_SR_GEM1_MASK                           (0x01 << 0x5)
    /* Bit is set on violation. Cleared by writing '1'*/
    #define MPU_VIOLATION_SR_USB_OFFSET                          0x6
    #define MPU_VIOLATION_SR_USB_MASK                            (0x01 << 0x6)
    /* Bit is set on violation. Cleared by writing '1'*/
    #define MPU_VIOLATION_SR_MMC_OFFSET                          0x7
    #define MPU_VIOLATION_SR_MMC_MASK                            (0x01 << 0x7)
    /* Bit is set on violation. Cleared by writing '1'*/
    #define MPU_VIOLATION_SR_SCB_OFFSET                          0x8
    #define MPU_VIOLATION_SR_SCB_MASK                            (0x01 << 0x8)
    /* Bit is set on violation. Cleared by writing '1'*/
    #define MPU_VIOLATION_SR_TRACE_OFFSET                        0x9
    #define MPU_VIOLATION_SR_TRACE_MASK                          (0x01 << 0x9)

/*Enables interrupts on MPU violations*/
#define MPU_VIOLATION_INTEN_CR_OFFSET                            0xF4
    /* Enables the interrupt*/
    #define MPU_VIOLATION_INTEN_CR_FIC0_OFFSET                   0x0
    #define MPU_VIOLATION_INTEN_CR_FIC0_MASK                     (0x01 << 0x0)
    /* Enables the interrupt*/
    #define MPU_VIOLATION_INTEN_CR_FIC1_OFFSET                   0x1
    #define MPU_VIOLATION_INTEN_CR_FIC1_MASK                     (0x01 << 0x1)
    /* Enables the interrupt*/
    #define MPU_VIOLATION_INTEN_CR_FIC2_OFFSET                   0x2
    #define MPU_VIOLATION_INTEN_CR_FIC2_MASK                     (0x01 << 0x2)
    /* Enables the interrupt*/
    #define MPU_VIOLATION_INTEN_CR_ATHENA_OFFSET                 0x3
    #define MPU_VIOLATION_INTEN_CR_ATHENA_MASK                   (0x01 << 0x3)
    /* Enables the interrupt*/
    #define MPU_VIOLATION_INTEN_CR_GEM0_OFFSET                   0x4
    #define MPU_VIOLATION_INTEN_CR_GEM0_MASK                     (0x01 << 0x4)
    /* Enables the interrupt*/
    #define MPU_VIOLATION_INTEN_CR_GEM1_OFFSET                   0x5
    #define MPU_VIOLATION_INTEN_CR_GEM1_MASK                     (0x01 << 0x5)
    /* Enables the interrupt*/
    #define MPU_VIOLATION_INTEN_CR_USB_OFFSET                    0x6
    #define MPU_VIOLATION_INTEN_CR_USB_MASK                      (0x01 << 0x6)
    /* Enables the interrupt*/
    #define MPU_VIOLATION_INTEN_CR_MMC_OFFSET                    0x7
    #define MPU_VIOLATION_INTEN_CR_MMC_MASK                      (0x01 << 0x7)
    /* Enables the interrupt*/
    #define MPU_VIOLATION_INTEN_CR_SCB_OFFSET                    0x8
    #define MPU_VIOLATION_INTEN_CR_SCB_MASK                      (0x01 << 0x8)
    /* Enables the interrupt*/
    #define MPU_VIOLATION_INTEN_CR_TRACE_OFFSET                  0x9
    #define MPU_VIOLATION_INTEN_CR_TRACE_MASK                    (0x01 << 0x9)

/*AXI switch decode fail*/
#define SW_FAIL_ADDR0_CR_OFFSET                                  0xF8
    /* The address (bits 31:0) that failed. Reading this address as 64-bits
     will return the 38-bit address in a single read combined with additional i
    nformation in the next register*/
    #define SW_FAIL_ADDR0_CR_ADDR_OFFSET                         0x0
    #define SW_FAIL_ADDR0_CR_ADDR_MASK                           (0xFFFFFFFF << 0x0)

/*AXI switch decode fail*/
#define SW_FAIL_ADDR1_CR_OFFSET                                  0xFC
    /* Upper 6 bits off address [37:32]*/
    #define SW_FAIL_ADDR1_CR_ADDR_OFFSET                         0x0
    #define SW_FAIL_ADDR1_CR_ADDR_MASK                           (0x3F << 0x0)
    /* AXI ID off failure*/
    #define SW_FAIL_ADDR1_CR_ID_OFFSET                           0x8
    #define SW_FAIL_ADDR1_CR_ID_MASK                             (0xFF << 0x8)
    /* AXI write=1 or read=0*/
    #define SW_FAIL_ADDR1_CR_WRITE_OFFSET                        0x10
    #define SW_FAIL_ADDR1_CR_WRITE_MASK                          (0x01 << 0x10)
    /* */
    #define SW_FAIL_ADDR1_CR_FAILED_OFFSET                       0x11
    #define SW_FAIL_ADDR1_CR_FAILED_MASK                         (0x01 << 0x11)

/*Set when an ECC event happens*/
#define EDAC_SR_OFFSET                                           0x100
    /* */
    #define EDAC_SR_MMC_1E_OFFSET                                0x0
    #define EDAC_SR_MMC_1E_MASK                                  (0x01 << 0x0)
    /* */
    #define EDAC_SR_MMC_2E_OFFSET                                0x1
    #define EDAC_SR_MMC_2E_MASK                                  (0x01 << 0x1)
    /* */
    #define EDAC_SR_DDRC_1E_OFFSET                               0x2
    #define EDAC_SR_DDRC_1E_MASK                                 (0x01 << 0x2)
    /* */
    #define EDAC_SR_DDRC_2E_OFFSET                               0x3
    #define EDAC_SR_DDRC_2E_MASK                                 (0x01 << 0x3)
    /* */
    #define EDAC_SR_MAC0_1E_OFFSET                               0x4
    #define EDAC_SR_MAC0_1E_MASK                                 (0x01 << 0x4)
    /* */
    #define EDAC_SR_MAC0_2E_OFFSET                               0x5
    #define EDAC_SR_MAC0_2E_MASK                                 (0x01 << 0x5)
    /* */
    #define EDAC_SR_MAC1_1E_OFFSET                               0x6
    #define EDAC_SR_MAC1_1E_MASK                                 (0x01 << 0x6)
    /* */
    #define EDAC_SR_MAC1_2E_OFFSET                               0x7
    #define EDAC_SR_MAC1_2E_MASK                                 (0x01 << 0x7)
    /* */
    #define EDAC_SR_USB_1E_OFFSET                                0x8
    #define EDAC_SR_USB_1E_MASK                                  (0x01 << 0x8)
    /* */
    #define EDAC_SR_USB_2E_OFFSET                                0x9
    #define EDAC_SR_USB_2E_MASK                                  (0x01 << 0x9)
    /* */
    #define EDAC_SR_CAN0_1E_OFFSET                               0xA
    #define EDAC_SR_CAN0_1E_MASK                                 (0x01 << 0xA)
    /* */
    #define EDAC_SR_CAN0_2E_OFFSET                               0xB
    #define EDAC_SR_CAN0_2E_MASK                                 (0x01 << 0xB)
    /* */
    #define EDAC_SR_CAN1_1E_OFFSET                               0xC
    #define EDAC_SR_CAN1_1E_MASK                                 (0x01 << 0xC)
    /* */
    #define EDAC_SR_CAN1_2E_OFFSET                               0xD
    #define EDAC_SR_CAN1_2E_MASK                                 (0x01 << 0xD)

/*Enables ECC interrupt on event*/
#define EDAC_INTEN_CR_OFFSET                                     0x104
    /* */
    #define EDAC_INTEN_CR_MMC_1E_OFFSET                          0x0
    #define EDAC_INTEN_CR_MMC_1E_MASK                            (0x01 << 0x0)
    /* */
    #define EDAC_INTEN_CR_MMC_2E_OFFSET                          0x1
    #define EDAC_INTEN_CR_MMC_2E_MASK                            (0x01 << 0x1)
    /* */
    #define EDAC_INTEN_CR_DDRC_1E_OFFSET                         0x2
    #define EDAC_INTEN_CR_DDRC_1E_MASK                           (0x01 << 0x2)
    /* */
    #define EDAC_INTEN_CR_DDRC_2E_OFFSET                         0x3
    #define EDAC_INTEN_CR_DDRC_2E_MASK                           (0x01 << 0x3)
    /* */
    #define EDAC_INTEN_CR_MAC0_1E_OFFSET                         0x4
    #define EDAC_INTEN_CR_MAC0_1E_MASK                           (0x01 << 0x4)
    /* */
    #define EDAC_INTEN_CR_MAC0_2E_OFFSET                         0x5
    #define EDAC_INTEN_CR_MAC0_2E_MASK                           (0x01 << 0x5)
    /* */
    #define EDAC_INTEN_CR_MAC1_1E_OFFSET                         0x6
    #define EDAC_INTEN_CR_MAC1_1E_MASK                           (0x01 << 0x6)
    /* */
    #define EDAC_INTEN_CR_MAC1_2E_OFFSET                         0x7
    #define EDAC_INTEN_CR_MAC1_2E_MASK                           (0x01 << 0x7)
    /* */
    #define EDAC_INTEN_CR_USB_1E_OFFSET                          0x8
    #define EDAC_INTEN_CR_USB_1E_MASK                            (0x01 << 0x8)
    /* */
    #define EDAC_INTEN_CR_USB_2E_OFFSET                          0x9
    #define EDAC_INTEN_CR_USB_2E_MASK                            (0x01 << 0x9)
    /* */
    #define EDAC_INTEN_CR_CAN0_1E_OFFSET                         0xA
    #define EDAC_INTEN_CR_CAN0_1E_MASK                           (0x01 << 0xA)
    /* */
    #define EDAC_INTEN_CR_CAN0_2E_OFFSET                         0xB
    #define EDAC_INTEN_CR_CAN0_2E_MASK                           (0x01 << 0xB)
    /* */
    #define EDAC_INTEN_CR_CAN1_1E_OFFSET                         0xC
    #define EDAC_INTEN_CR_CAN1_1E_MASK                           (0x01 << 0xC)
    /* */
    #define EDAC_INTEN_CR_CAN1_2E_OFFSET                         0xD
    #define EDAC_INTEN_CR_CAN1_2E_MASK                           (0x01 << 0xD)

/*Count off single bit errors*/
#define EDAC_CNT_MMC_OFFSET                                      0x108
    /* */
    #define EDAC_CNT_MMC_COUNT_OFFSET                            0x0
    #define EDAC_CNT_MMC_COUNT_MASK                              (0x3FF << 0x0)

/*Count off single bit errors*/
#define EDAC_CNT_DDRC_OFFSET                                     0x10C
    /* */
    #define EDAC_CNT_DDRC_COUNT_OFFSET                           0x0
    #define EDAC_CNT_DDRC_COUNT_MASK                             (0x3FF << 0x0)

/*Count off single bit errors*/
#define EDAC_CNT_MAC0_OFFSET                                     0x110
    /* */
    #define EDAC_CNT_MAC0_COUNT_OFFSET                           0x0
    #define EDAC_CNT_MAC0_COUNT_MASK                             (0x3FF << 0x0)

/*Count off single bit errors*/
#define EDAC_CNT_MAC1_OFFSET                                     0x114
    /* */
    #define EDAC_CNT_MAC1_COUNT_OFFSET                           0x0
    #define EDAC_CNT_MAC1_COUNT_MASK                             (0x3FF << 0x0)

/*Count off single bit errors*/
#define EDAC_CNT_USB_OFFSET                                      0x118
    /* */
    #define EDAC_CNT_USB_COUNT_OFFSET                            0x0
    #define EDAC_CNT_USB_COUNT_MASK                              (0x3FF << 0x0)

/*Count off single bit errors*/
#define EDAC_CNT_CAN0_OFFSET                                     0x11C
    /* */
    #define EDAC_CNT_CAN0_COUNT_OFFSET                           0x0
    #define EDAC_CNT_CAN0_COUNT_MASK                             (0x3FF << 0x0)

/*Count off single bit errors*/
#define EDAC_CNT_CAN1_OFFSET                                     0x120
    /* */
    #define EDAC_CNT_CAN1_COUNT_OFFSET                           0x0
    #define EDAC_CNT_CAN1_COUNT_MASK                             (0x3FF << 0x0)

/*"Will Corrupt write data to rams 1E corrupts bit 0 2E bits 1 and 2.Inject
    s Errors into all RAMS in the block as long as the bits are set. Setting 1E
     and 2E will inject a 3-bit error"*/
#define EDAC_INJECT_CR_OFFSET                                    0x124
    /* */
    #define EDAC_INJECT_CR_MMC_1E_OFFSET                         0x0
    #define EDAC_INJECT_CR_MMC_1E_MASK                           (0x01 << 0x0)
    /* */
    #define EDAC_INJECT_CR_MMC_2E_OFFSET                         0x1
    #define EDAC_INJECT_CR_MMC_2E_MASK                           (0x01 << 0x1)
    /* */
    #define EDAC_INJECT_CR_DDRC_1E_OFFSET                        0x2
    #define EDAC_INJECT_CR_DDRC_1E_MASK                          (0x01 << 0x2)
    /* */
    #define EDAC_INJECT_CR_DDRC_2E_OFFSET                        0x3
    #define EDAC_INJECT_CR_DDRC_2E_MASK                          (0x01 << 0x3)
    /* */
    #define EDAC_INJECT_CR_MAC0_1E_OFFSET                        0x4
    #define EDAC_INJECT_CR_MAC0_1E_MASK                          (0x01 << 0x4)
    /* */
    #define EDAC_INJECT_CR_MAC0_2E_OFFSET                        0x5
    #define EDAC_INJECT_CR_MAC0_2E_MASK                          (0x01 << 0x5)
    /* */
    #define EDAC_INJECT_CR_MAC1_1E_OFFSET                        0x6
    #define EDAC_INJECT_CR_MAC1_1E_MASK                          (0x01 << 0x6)
    /* */
    #define EDAC_INJECT_CR_MAC1_2E_OFFSET                        0x7
    #define EDAC_INJECT_CR_MAC1_2E_MASK                          (0x01 << 0x7)
    /* */
    #define EDAC_INJECT_CR_USB_1E_OFFSET                         0x8
    #define EDAC_INJECT_CR_USB_1E_MASK                           (0x01 << 0x8)
    /* */
    #define EDAC_INJECT_CR_USB_2E_OFFSET                         0x9
    #define EDAC_INJECT_CR_USB_2E_MASK                           (0x01 << 0x9)
    /* */
    #define EDAC_INJECT_CR_CAN0_1E_OFFSET                        0xA
    #define EDAC_INJECT_CR_CAN0_1E_MASK                          (0x01 << 0xA)
    /* */
    #define EDAC_INJECT_CR_CAN0_2E_OFFSET                        0xB
    #define EDAC_INJECT_CR_CAN0_2E_MASK                          (0x01 << 0xB)
    /* */
    #define EDAC_INJECT_CR_CAN1_1E_OFFSET                        0xC
    #define EDAC_INJECT_CR_CAN1_1E_MASK                          (0x01 << 0xC)
    /* */
    #define EDAC_INJECT_CR_CAN1_2E_OFFSET                        0xD
    #define EDAC_INJECT_CR_CAN1_2E_MASK                          (0x01 << 0xD)

/*Maintenance Interrupt Enable.*/
#define MAINTENANCE_INTEN_CR_OFFSET                              0x140
    /* Enables interrupt on a PLL event PLL_STATUS_INTEN_CR should also be
    set*/
    #define MAINTENANCE_INTEN_CR_PLL_OFFSET                      0x0
    #define MAINTENANCE_INTEN_CR_PLL_MASK                        (0x01 << 0x0)
    /* Enables interrupt on a MPU access violation */
    #define MAINTENANCE_INTEN_CR_MPU_OFFSET                      0x1
    #define MAINTENANCE_INTEN_CR_MPU_MASK                        (0x01 << 0x1)
    /* Enables interrupt on a AXI switch decode error*/
    #define MAINTENANCE_INTEN_CR_DECODE_OFFSET                   0x2
    #define MAINTENANCE_INTEN_CR_DECODE_MASK                     (0x01 << 0x2)
    /* Enables interrupt as lp_state goes high*/
    #define MAINTENANCE_INTEN_CR_LP_STATE_ENTER_OFFSET           0x3
    #define MAINTENANCE_INTEN_CR_LP_STATE_ENTER_MASK             (0x01 << 0x3)
    /* Enables interrupt as lp_state goes low*/
    #define MAINTENANCE_INTEN_CR_LP_STATE_EXIT_OFFSET            0x4
    #define MAINTENANCE_INTEN_CR_LP_STATE_EXIT_MASK              (0x01 << 0x4)
    /* Enables interrupt as flash_freeze goes high*/
    #define MAINTENANCE_INTEN_CR_FF_START_OFFSET                 0x5
    #define MAINTENANCE_INTEN_CR_FF_START_MASK                   (0x01 << 0x5)
    /* Enables interrupt as flash_freeze goes low*/
    #define MAINTENANCE_INTEN_CR_FF_END_OFFSET                   0x6
    #define MAINTENANCE_INTEN_CR_FF_END_MASK                     (0x01 << 0x6)
    /* Enables interrupt when FPGA turned on*/
    #define MAINTENANCE_INTEN_CR_FPGA_ON_OFFSET                  0x7
    #define MAINTENANCE_INTEN_CR_FPGA_ON_MASK                    (0x01 << 0x7)
    /* Enables interrupt when FPGA turned off*/
    #define MAINTENANCE_INTEN_CR_FPGA_OFF_OFFSET                 0x8
    #define MAINTENANCE_INTEN_CR_FPGA_OFF_MASK                   (0x01 << 0x8)
    /* Enables interrupt on SCB error*/
    #define MAINTENANCE_INTEN_CR_SCB_ERROR_OFFSET                0x9
    #define MAINTENANCE_INTEN_CR_SCB_ERROR_MASK                  (0x01 << 0x9)
    /* Enables interrupt on SCB failure*/
    #define MAINTENANCE_INTEN_CR_SCB_FAULT_OFFSET                0xA
    #define MAINTENANCE_INTEN_CR_SCB_FAULT_MASK                  (0x01 << 0xA)
    /* Enables interrupt on Mesh violation detection */
    #define MAINTENANCE_INTEN_CR_MESH_ERROR_OFFSET               0xB
    #define MAINTENANCE_INTEN_CR_MESH_ERROR_MASK                 (0x01 << 0xB)
    /* Enables interrupt on bank2 powered on*/
    #define MAINTENANCE_INTEN_CR_IO_BANK_B2_ON_OFFSET            0xC
    #define MAINTENANCE_INTEN_CR_IO_BANK_B2_ON_MASK              (0x01 << 0xC)
    /* Enables interrupt on bank4 powered on*/
    #define MAINTENANCE_INTEN_CR_IO_BANK_B4_ON_OFFSET            0xD
    #define MAINTENANCE_INTEN_CR_IO_BANK_B4_ON_MASK              (0x01 << 0xD)
    /* Enables interrupt on bank5 powered on*/
    #define MAINTENANCE_INTEN_CR_IO_BANK_B5_ON_OFFSET            0xE
    #define MAINTENANCE_INTEN_CR_IO_BANK_B5_ON_MASK              (0x01 << 0xE)
    /* Enables interrupt on bank6 powered on*/
    #define MAINTENANCE_INTEN_CR_IO_BANK_B6_ON_OFFSET            0xF
    #define MAINTENANCE_INTEN_CR_IO_BANK_B6_ON_MASK              (0x01 << 0xF)
    /* Enables interrupt on bank2 powered off*/
    #define MAINTENANCE_INTEN_CR_IO_BANK_B2_OFF_OFFSET           0x10
    #define MAINTENANCE_INTEN_CR_IO_BANK_B2_OFF_MASK             (0x01 << 0x10)
    /* Enables interrupt on bank4 powered off*/
    #define MAINTENANCE_INTEN_CR_IO_BANK_B4_OFF_OFFSET           0x11
    #define MAINTENANCE_INTEN_CR_IO_BANK_B4_OFF_MASK             (0x01 << 0x11)
    /* Enables interrupt on bank5 powered off*/
    #define MAINTENANCE_INTEN_CR_IO_BANK_B5_OFF_OFFSET           0x12
    #define MAINTENANCE_INTEN_CR_IO_BANK_B5_OFF_MASK             (0x01 << 0x12)
    /* Enables interrupt on bank6 powered off*/
    #define MAINTENANCE_INTEN_CR_IO_BANK_B6_OFF_OFFSET           0x13
    #define MAINTENANCE_INTEN_CR_IO_BANK_B6_OFF_MASK             (0x01 << 0x13)
    /* Enables interrupt on a DLL event DLL_STATUS_INTEN_CR should also be
    set*/
    #define MAINTENANCE_INTEN_CR_DLL_OFFSET                      0x14
    #define MAINTENANCE_INTEN_CR_DLL_MASK                        (0x01 << 0x14)

/*PLL Status interrupt enables*/
#define PLL_STATUS_INTEN_CR_OFFSET                               0x144
    /* Enables interrupt on CPU PLL locking*/
    #define PLL_STATUS_INTEN_CR_CPU_LOCK_OFFSET                  0x0
    #define PLL_STATUS_INTEN_CR_CPU_LOCK_MASK                    (0x01 << 0x0)
    /* Enables interrupt on DFT PLL locking*/
    #define PLL_STATUS_INTEN_CR_DFI_LOCK_OFFSET                  0x1
    #define PLL_STATUS_INTEN_CR_DFI_LOCK_MASK                    (0x01 << 0x1)
    /* Enables interrupt on SGMII PLL locking*/
    #define PLL_STATUS_INTEN_CR_SGMII_LOCK_OFFSET                0x2
    #define PLL_STATUS_INTEN_CR_SGMII_LOCK_MASK                  (0x01 << 0x2)
    /* Enables interrupt on CPU PLL unlocking*/
    #define PLL_STATUS_INTEN_CR_CPU_UNLOCK_OFFSET                0x4
    #define PLL_STATUS_INTEN_CR_CPU_UNLOCK_MASK                  (0x01 << 0x4)
    /* Enables interrupt on DFT PLL unlocking*/
    #define PLL_STATUS_INTEN_CR_DFI_UNLOCK_OFFSET                0x5
    #define PLL_STATUS_INTEN_CR_DFI_UNLOCK_MASK                  (0x01 << 0x5)
    /* Enables interrupt on SGMII PLL unlocking*/
    #define PLL_STATUS_INTEN_CR_SGMII_UNLOCK_OFFSET              0x6
    #define PLL_STATUS_INTEN_CR_SGMII_UNLOCK_MASK                (0x01 << 0x6)

/*Maintenance interrupt indicates fault and status events.*/
#define MAINTENANCE_INT_SR_OFFSET                                0x148
    /* Indicates that one off the PLLs whent into the lock or unlock state.
     Cleared via PLL status register*/
    #define MAINTENANCE_INT_SR_PLL_OFFSET                        0x0
    #define MAINTENANCE_INT_SR_PLL_MASK                          (0x01 << 0x0)
    /* Indicates that one off the MPUS signaled a MPU violation. Cleared vi
    a MPU Violation Register*/
    #define MAINTENANCE_INT_SR_MPU_OFFSET                        0x1
    #define MAINTENANCE_INT_SR_MPU_MASK                          (0x01 << 0x1)
    /* Indicates that the AXI switch detected an illegal address. Cleared w
    hen SREG.SW_FAIL.ADDR1_CR_FAILED is cleared.*/
    #define MAINTENANCE_INT_SR_DECODE_OFFSET                     0x2
    #define MAINTENANCE_INT_SR_DECODE_MASK                       (0x01 << 0x2)
    /* Indicates the device has entered the lower power state cleared by wr
    iting '1'*/
    #define MAINTENANCE_INT_SR_LP_STATE_ENTER_OFFSET             0x3
    #define MAINTENANCE_INT_SR_LP_STATE_ENTER_MASK               (0x01 << 0x3)
    /* Indicates the device has exited the lower power state cleared by wri
    ting '1'*/
    #define MAINTENANCE_INT_SR_LP_STATE_EXIT_OFFSET              0x4
    #define MAINTENANCE_INT_SR_LP_STATE_EXIT_MASK                (0x01 << 0x4)
    /* Indicates the device has entered the flash freezer state cleared by
    writing '1'*/
    #define MAINTENANCE_INT_SR_FF_START_OFFSET                   0x5
    #define MAINTENANCE_INT_SR_FF_START_MASK                     (0x01 << 0x5)
    /* Indicates the device has exited the flash freezer state cleared by w
    riting '1'*/
    #define MAINTENANCE_INT_SR_FF_END_OFFSET                     0x6
    #define MAINTENANCE_INT_SR_FF_END_MASK                       (0x01 << 0x6)
    /* Indicates that the FPGA array has been turned on cleared by writing
    a '1'*/
    #define MAINTENANCE_INT_SR_FPGA_ON_OFFSET                    0x7
    #define MAINTENANCE_INT_SR_FPGA_ON_MASK                      (0x01 << 0x7)
    /* Indicates that the FPGA array has been turned off cleared by writing
     a '1'*/
    #define MAINTENANCE_INT_SR_FPGA_OFF_OFFSET                   0x8
    #define MAINTENANCE_INT_SR_FPGA_OFF_MASK                     (0x01 << 0x8)
    /* Indicates that the SCB slave reported an error cleared via SCB contr
    oller*/
    #define MAINTENANCE_INT_SR_SCB_ERROR_OFFSET                  0x9
    #define MAINTENANCE_INT_SR_SCB_ERROR_MASK                    (0x01 << 0x9)
    /* Indicates that the SCB bus fault occurred cleared via SCB controller
    */
    #define MAINTENANCE_INT_SR_SCB_FAULT_OFFSET                  0xA
    #define MAINTENANCE_INT_SR_SCB_FAULT_MASK                    (0x01 << 0xA)
    /* Indicates that the mesh over the Crypto triggered cleared via Mesh s
    ystem error*/
    #define MAINTENANCE_INT_SR_MESH_ERROR_OFFSET                 0xB
    #define MAINTENANCE_INT_SR_MESH_ERROR_MASK                   (0x01 << 0xB)
    /* Indicates that IO bank 2 has turned on cleared by writing a '1'*/
    #define MAINTENANCE_INT_SR_IO_BANK_B2_ON_OFFSET              0xC
    #define MAINTENANCE_INT_SR_IO_BANK_B2_ON_MASK                (0x01 << 0xC)
    /* Indicates that IO bank 4 has turned on cleared by writing a '1'*/
    #define MAINTENANCE_INT_SR_IO_BANK_B4_ON_OFFSET              0xD
    #define MAINTENANCE_INT_SR_IO_BANK_B4_ON_MASK                (0x01 << 0xD)
    /* Indicates that IO bank 5  has turned on cleared by writing a '1'*/
    #define MAINTENANCE_INT_SR_IO_BANK_B5_ON_OFFSET              0xE
    #define MAINTENANCE_INT_SR_IO_BANK_B5_ON_MASK                (0x01 << 0xE)
    /* Indicates that IO bank 6  has turned on cleared by writing a '1'*/
    #define MAINTENANCE_INT_SR_IO_BANK_B6_ON_OFFSET              0xF
    #define MAINTENANCE_INT_SR_IO_BANK_B6_ON_MASK                (0x01 << 0xF)
    /* Indicates that IO bank 2 has turned off cleared by writing a '1'*/
    #define MAINTENANCE_INT_SR_IO_BANK_B2_OFF_OFFSET             0x10
    #define MAINTENANCE_INT_SR_IO_BANK_B2_OFF_MASK               (0x01 << 0x10)
    /* Indicates that IO bank 4 has turned off cleared by writing a '1'*/
    #define MAINTENANCE_INT_SR_IO_BANK_B4_OFF_OFFSET             0x11
    #define MAINTENANCE_INT_SR_IO_BANK_B4_OFF_MASK               (0x01 << 0x11)
    /* Indicates that IO bank 5  has turned off cleared by writing a '1'*/
    #define MAINTENANCE_INT_SR_IO_BANK_B5_OFF_OFFSET             0x12
    #define MAINTENANCE_INT_SR_IO_BANK_B5_OFF_MASK               (0x01 << 0x12)
    /* Indicates that one off the DLLs when into the lock or unlock state.
    Cleared via DLL status register*/
    #define MAINTENANCE_INT_SR_IO_BANK_B6_OFF_OFFSET             0x13
    #define MAINTENANCE_INT_SR_IO_BANK_B6_OFF_MASK               (0x01 << 0x13)
    /* Indicates that IO bank 6  has turned off cleared by writing a '1'*/
    #define MAINTENANCE_INT_SR_DLL_OFFSET                        0x14
    #define MAINTENANCE_INT_SR_DLL_MASK                          (0x01 << 0x14)

/*PLL interrupt register*/
#define PLL_STATUS_SR_OFFSET                                     0x14C
    /* Indicates that the CPU PLL has locked cleared by writing a '1'*/
    #define PLL_STATUS_SR_CPU_LOCK_OFFSET                        0x0
    #define PLL_STATUS_SR_CPU_LOCK_MASK                          (0x01 << 0x0)
    /* Indicates that the DFI PLL has locked cleared by writing a '1'*/
    #define PLL_STATUS_SR_DFI_LOCK_OFFSET                        0x1
    #define PLL_STATUS_SR_DFI_LOCK_MASK                          (0x01 << 0x1)
    /* Indicates that the SGMII PLL has locked cleared by writing a '1'*/
    #define PLL_STATUS_SR_SGMII_LOCK_OFFSET                      0x2
    #define PLL_STATUS_SR_SGMII_LOCK_MASK                        (0x01 << 0x2)
    /* Indicates that the CPU PLL has unlocked cleared by writing a '1'*/
    #define PLL_STATUS_SR_CPU_UNLOCK_OFFSET                      0x4
    #define PLL_STATUS_SR_CPU_UNLOCK_MASK                        (0x01 << 0x4)
    /* Indicates that the DFI PLL has unlocked cleared by writing a '1'*/
    #define PLL_STATUS_SR_DFI_UNLOCK_OFFSET                      0x5
    #define PLL_STATUS_SR_DFI_UNLOCK_MASK                        (0x01 << 0x5)
    /* Indicates that the SGMII PLL has unlocked cleared by writing a '1'*/
    #define PLL_STATUS_SR_SGMII_UNLOCK_OFFSET                    0x6
    #define PLL_STATUS_SR_SGMII_UNLOCK_MASK                      (0x01 << 0x6)
    /* Current state off CPU PLL locked signal*/
    #define PLL_STATUS_SR_CPU_LOCK_NOW_OFFSET                    0x8
    #define PLL_STATUS_SR_CPU_LOCK_NOW_MASK                      (0x01 << 0x8)
    /* Current state off DFI PLL locked signal*/
    #define PLL_STATUS_SR_DFI_LOCK_NOW_OFFSET                    0x9
    #define PLL_STATUS_SR_DFI_LOCK_NOW_MASK                      (0x01 << 0x9)
    /* Current state off SGMII PLL locked signal*/
    #define PLL_STATUS_SR_SGMII_LOCK_NOW_OFFSET                  0xA
    #define PLL_STATUS_SR_SGMII_LOCK_NOW_MASK                    (0x01 << 0xA)

/*Enable to CFM Timer */
#define CFM_TIMER_CR_OFFSET                                      0x150
    /* When set and the CFM channel is in timer mode and CFM channel is set
     to 2 (Group C) this register allows the timet to count. Allows software to
     start and stop the timers.*/
    #define CFM_TIMER_CR_ENABLE_OFFSET                           0x0
    #define CFM_TIMER_CR_ENABLE_MASK                             (0x1F << 0x0)

/*Miscellaneous Register*/
#define MISC_SR_OFFSET                                           0x154
    /* Indicates that Interrupt from the G5C MSS SCB SPI controller is acti
    ve*/
    #define MISC_SR_CONT_SPI_INTERRUPT_OFFSET                    0x0
    #define MISC_SR_CONT_SPI_INTERRUPT_MASK                      (0x01 << 0x0)
    /* Indicates that the user voltage or temperature detectors are signali
    ng an alarm condition.*/
    #define MISC_SR_VOLT_TEMP_ALARM_OFFSET                       0x1
    #define MISC_SR_VOLT_TEMP_ALARM_MASK                         (0x01 << 0x1)

/*DLL Interrupt enables*/
#define DLL_STATUS_CR_OFFSET                                     0x158
    /* Enables the DLL0 lock interrupt*/
    #define DLL_STATUS_CR_FIC0_LOCK_OFFSET                       0x0
    #define DLL_STATUS_CR_FIC0_LOCK_MASK                         (0x01 << 0x0)
    /* Enables the DLL1 lock interrupt*/
    #define DLL_STATUS_CR_FIC1_LOCK_OFFSET                       0x1
    #define DLL_STATUS_CR_FIC1_LOCK_MASK                         (0x01 << 0x1)
    /* Enables the DLL2 lock interrupt*/
    #define DLL_STATUS_CR_FIC2_LOCK_OFFSET                       0x2
    #define DLL_STATUS_CR_FIC2_LOCK_MASK                         (0x01 << 0x2)
    /* Enables the DLL3 lock interrupt*/
    #define DLL_STATUS_CR_FIC3_LOCK_OFFSET                       0x4
    #define DLL_STATUS_CR_FIC3_LOCK_MASK                         (0x01 << 0x4)
    /* Enables the DLL4 (Crypto) lock interrupt*/
    #define DLL_STATUS_CR_FIC4_LOCK_OFFSET                       0x5
    #define DLL_STATUS_CR_FIC4_LOCK_MASK                         (0x01 << 0x5)
    /* Enables the DLL0 unlock interrupt*/
    #define DLL_STATUS_CR_FIC0_UNLOCK_OFFSET                     0x8
    #define DLL_STATUS_CR_FIC0_UNLOCK_MASK                       (0x01 << 0x8)
    /* Enables the DLL1 unlock interrupt*/
    #define DLL_STATUS_CR_FIC1_UNLOCK_OFFSET                     0x9
    #define DLL_STATUS_CR_FIC1_UNLOCK_MASK                       (0x01 << 0x9)
    /* Enables the DLL2 unlock interrupt*/
    #define DLL_STATUS_CR_FIC2_UNLOCK_OFFSET                     0xA
    #define DLL_STATUS_CR_FIC2_UNLOCK_MASK                       (0x01 << 0xA)
    /* Enables the DLL3 unlock interrupt*/
    #define DLL_STATUS_CR_FIC3_UNLOCK_OFFSET                     0xB
    #define DLL_STATUS_CR_FIC3_UNLOCK_MASK                       (0x01 << 0xB)
    /* Enables the DLL4 (crypto) unlock interrupt*/
    #define DLL_STATUS_CR_FIC4_UNLOCK_OFFSET                     0xC
    #define DLL_STATUS_CR_FIC4_UNLOCK_MASK                       (0x01 << 0xC)

/*DLL interrupt register*/
#define DLL_STATUS_SR_OFFSET                                     0x15C
    /* Indicates that the FIC0 DLL has locked cleared by writing a '1'*/
    #define DLL_STATUS_SR_FIC0_LOCK_OFFSET                       0x0
    #define DLL_STATUS_SR_FIC0_LOCK_MASK                         (0x01 << 0x0)
    /* Indicates that the FIC1 DLL has locked cleared by writing a '1'*/
    #define DLL_STATUS_SR_FIC1_LOCK_OFFSET                       0x1
    #define DLL_STATUS_SR_FIC1_LOCK_MASK                         (0x01 << 0x1)
    /* Indicates that the FIC2 DLL has locked cleared by writing a '1'*/
    #define DLL_STATUS_SR_FIC2_LOCK_OFFSET                       0x2
    #define DLL_STATUS_SR_FIC2_LOCK_MASK                         (0x01 << 0x2)
    /* Indicates that the FIC3 DLL has locked cleared by writing a '1'*/
    #define DLL_STATUS_SR_FIC3_LOCK_OFFSET                       0x4
    #define DLL_STATUS_SR_FIC3_LOCK_MASK                         (0x01 << 0x4)
    /* Indicates that the FIC4 (Crypto) DLL has locked cleared by writing a
     '1'*/
    #define DLL_STATUS_SR_FIC4_LOCK_OFFSET                       0x5
    #define DLL_STATUS_SR_FIC4_LOCK_MASK                         (0x01 << 0x5)
    /* Indicates that the FIC0 DLL has unlocked cleared by writing a '1'*/
    #define DLL_STATUS_SR_FIC0_UNLOCK_OFFSET                     0x8
    #define DLL_STATUS_SR_FIC0_UNLOCK_MASK                       (0x01 << 0x8)
    /* Indicates that the FIC1 DLL has unlocked cleared by writing a '1'*/
    #define DLL_STATUS_SR_FIC1_UNLOCK_OFFSET                     0x9
    #define DLL_STATUS_SR_FIC1_UNLOCK_MASK                       (0x01 << 0x9)
    /* Indicates that the FIC2 DLL has unlocked cleared by writing a '1'*/
    #define DLL_STATUS_SR_FIC2_UNLOCK_OFFSET                     0xA
    #define DLL_STATUS_SR_FIC2_UNLOCK_MASK                       (0x01 << 0xA)
    /* Indicates that the FIC3 DLL has unlocked cleared by writing a '1'*/
    #define DLL_STATUS_SR_FIC3_UNLOCK_OFFSET                     0xB
    #define DLL_STATUS_SR_FIC3_UNLOCK_MASK                       (0x01 << 0xB)
    /* Indicates that the FIC4 (Crypto) DLL has unlocked cleared by writing
     a '1'*/
    #define DLL_STATUS_SR_FIC4_UNLOCK_OFFSET                     0xC
    #define DLL_STATUS_SR_FIC4_UNLOCK_MASK                       (0x01 << 0xC)
    /* Current state off FIC0 DLL locked signal*/
    #define DLL_STATUS_SR_FIC0_LOCK_NOW_OFFSET                   0x10
    #define DLL_STATUS_SR_FIC0_LOCK_NOW_MASK                     (0x01 << 0x10)
    /* Current state off FIC1 DLL locked signal*/
    #define DLL_STATUS_SR_FIC1_LOCK_NOW_OFFSET                   0x11
    #define DLL_STATUS_SR_FIC1_LOCK_NOW_MASK                     (0x01 << 0x11)
    /* Current state off FIC2 DLL locked signal*/
    #define DLL_STATUS_SR_FIC2_LOCK_NOW_OFFSET                   0x12
    #define DLL_STATUS_SR_FIC2_LOCK_NOW_MASK                     (0x01 << 0x12)
    /* Current state off FIC3 DLL locked signal*/
    #define DLL_STATUS_SR_FIC3_LOCK_NOW_OFFSET                   0x13
    #define DLL_STATUS_SR_FIC3_LOCK_NOW_MASK                     (0x01 << 0x13)
    /* Current state off FIC4 DLL locked signal*/
    #define DLL_STATUS_SR_FIC4_LOCK_NOW_OFFSET                   0x14
    #define DLL_STATUS_SR_FIC4_LOCK_NOW_MASK                     (0x01 << 0x14)

/*Puts all the RAMS in that block into low leakage mode. RAM contents and Q
     value preserved.*/
#define RAM_LIGHTSLEEP_CR_OFFSET                                 0x168
    /* */
    #define RAM_LIGHTSLEEP_CR_CAN0_OFFSET                        0x0
    #define RAM_LIGHTSLEEP_CR_CAN0_MASK                          (0x01 << 0x0)
    /* */
    #define RAM_LIGHTSLEEP_CR_CAN1_OFFSET                        0x1
    #define RAM_LIGHTSLEEP_CR_CAN1_MASK                          (0x01 << 0x1)
    /* */
    #define RAM_LIGHTSLEEP_CR_USB_OFFSET                         0x2
    #define RAM_LIGHTSLEEP_CR_USB_MASK                           (0x01 << 0x2)
    /* */
    #define RAM_LIGHTSLEEP_CR_GEM0_OFFSET                        0x3
    #define RAM_LIGHTSLEEP_CR_GEM0_MASK                          (0x01 << 0x3)
    /* */
    #define RAM_LIGHTSLEEP_CR_GEM1_OFFSET                        0x4
    #define RAM_LIGHTSLEEP_CR_GEM1_MASK                          (0x01 << 0x4)
    /* */
    #define RAM_LIGHTSLEEP_CR_MMC_OFFSET                         0x5
    #define RAM_LIGHTSLEEP_CR_MMC_MASK                           (0x01 << 0x5)
    /* */
    #define RAM_LIGHTSLEEP_CR_ATHENA_OFFSET                      0x6
    #define RAM_LIGHTSLEEP_CR_ATHENA_MASK                        (0x01 << 0x6)
    /* */
    #define RAM_LIGHTSLEEP_CR_DDRC_OFFSET                        0x7
    #define RAM_LIGHTSLEEP_CR_DDRC_MASK                          (0x01 << 0x7)
    /* */
    #define RAM_LIGHTSLEEP_CR_E51_OFFSET                         0x8
    #define RAM_LIGHTSLEEP_CR_E51_MASK                           (0x01 << 0x8)
    /* */
    #define RAM_LIGHTSLEEP_CR_U54_1_OFFSET                       0x9
    #define RAM_LIGHTSLEEP_CR_U54_1_MASK                         (0x01 << 0x9)
    /* */
    #define RAM_LIGHTSLEEP_CR_U54_2_OFFSET                       0xA
    #define RAM_LIGHTSLEEP_CR_U54_2_MASK                         (0x01 << 0xA)
    /* */
    #define RAM_LIGHTSLEEP_CR_U54_3_OFFSET                       0xB
    #define RAM_LIGHTSLEEP_CR_U54_3_MASK                         (0x01 << 0xB)
    /* */
    #define RAM_LIGHTSLEEP_CR_U54_4_OFFSET                       0xC
    #define RAM_LIGHTSLEEP_CR_U54_4_MASK                         (0x01 << 0xC)
    /* */
    #define RAM_LIGHTSLEEP_CR_L2_OFFSET                          0xD
    #define RAM_LIGHTSLEEP_CR_L2_MASK                            (0x01 << 0xD)

/*Puts all the RAMS in that block into deep sleep mode. RAM contents preser
    ved. Powers down the periphery circuits.*/
#define RAM_DEEPSLEEP_CR_OFFSET                                  0x16C
    /* */
    #define RAM_DEEPSLEEP_CR_CAN0_OFFSET                         0x0
    #define RAM_DEEPSLEEP_CR_CAN0_MASK                           (0x01 << 0x0)
    /* */
    #define RAM_DEEPSLEEP_CR_CAN1_OFFSET                         0x1
    #define RAM_DEEPSLEEP_CR_CAN1_MASK                           (0x01 << 0x1)
    /* */
    #define RAM_DEEPSLEEP_CR_USB_OFFSET                          0x2
    #define RAM_DEEPSLEEP_CR_USB_MASK                            (0x01 << 0x2)
    /* */
    #define RAM_DEEPSLEEP_CR_GEM0_OFFSET                         0x3
    #define RAM_DEEPSLEEP_CR_GEM0_MASK                           (0x01 << 0x3)
    /* */
    #define RAM_DEEPSLEEP_CR_GEM1_OFFSET                         0x4
    #define RAM_DEEPSLEEP_CR_GEM1_MASK                           (0x01 << 0x4)
    /* */
    #define RAM_DEEPSLEEP_CR_MMC_OFFSET                          0x5
    #define RAM_DEEPSLEEP_CR_MMC_MASK                            (0x01 << 0x5)
    /* */
    #define RAM_DEEPSLEEP_CR_ATHENA_OFFSET                       0x6
    #define RAM_DEEPSLEEP_CR_ATHENA_MASK                         (0x01 << 0x6)
    /* */
    #define RAM_DEEPSLEEP_CR_DDRC_OFFSET                         0x7
    #define RAM_DEEPSLEEP_CR_DDRC_MASK                           (0x01 << 0x7)
    /* */
    #define RAM_DEEPSLEEP_CR_E51_OFFSET                          0x8
    #define RAM_DEEPSLEEP_CR_E51_MASK                            (0x01 << 0x8)
    /* */
    #define RAM_DEEPSLEEP_CR_U54_1_OFFSET                        0x9
    #define RAM_DEEPSLEEP_CR_U54_1_MASK                          (0x01 << 0x9)
    /* */
    #define RAM_DEEPSLEEP_CR_U54_2_OFFSET                        0xA
    #define RAM_DEEPSLEEP_CR_U54_2_MASK                          (0x01 << 0xA)
    /* */
    #define RAM_DEEPSLEEP_CR_U54_3_OFFSET                        0xB
    #define RAM_DEEPSLEEP_CR_U54_3_MASK                          (0x01 << 0xB)
    /* */
    #define RAM_DEEPSLEEP_CR_U54_4_OFFSET                        0xC
    #define RAM_DEEPSLEEP_CR_U54_4_MASK                          (0x01 << 0xC)
    /* */
    #define RAM_DEEPSLEEP_CR_L2_OFFSET                           0xD
    #define RAM_DEEPSLEEP_CR_L2_MASK                             (0x01 << 0xD)

/*Puts all the RAMS in that block into shut down mode. RAM contents not pre
    served.  Powers down the RAM and periphery circuits.*/
#define RAM_SHUTDOWN_CR_OFFSET                                   0x170
    /* */
    #define RAM_SHUTDOWN_CR_CAN0_OFFSET                          0x0
    #define RAM_SHUTDOWN_CR_CAN0_MASK                            (0x01 << 0x0)
    /* */
    #define RAM_SHUTDOWN_CR_CAN1_OFFSET                          0x1
    #define RAM_SHUTDOWN_CR_CAN1_MASK                            (0x01 << 0x1)
    /* */
    #define RAM_SHUTDOWN_CR_USB_OFFSET                           0x2
    #define RAM_SHUTDOWN_CR_USB_MASK                             (0x01 << 0x2)
    /* */
    #define RAM_SHUTDOWN_CR_GEM0_OFFSET                          0x3
    #define RAM_SHUTDOWN_CR_GEM0_MASK                            (0x01 << 0x3)
    /* */
    #define RAM_SHUTDOWN_CR_GEM1_OFFSET                          0x4
    #define RAM_SHUTDOWN_CR_GEM1_MASK                            (0x01 << 0x4)
    /* */
    #define RAM_SHUTDOWN_CR_MMC_OFFSET                           0x5
    #define RAM_SHUTDOWN_CR_MMC_MASK                             (0x01 << 0x5)
    /* */
    #define RAM_SHUTDOWN_CR_ATHENA_OFFSET                        0x6
    #define RAM_SHUTDOWN_CR_ATHENA_MASK                          (0x01 << 0x6)
    /* */
    #define RAM_SHUTDOWN_CR_DDRC_OFFSET                          0x7
    #define RAM_SHUTDOWN_CR_DDRC_MASK                            (0x01 << 0x7)
    /* */
    #define RAM_SHUTDOWN_CR_E51_OFFSET                           0x8
    #define RAM_SHUTDOWN_CR_E51_MASK                             (0x01 << 0x8)
    /* */
    #define RAM_SHUTDOWN_CR_U54_1_OFFSET                         0x9
    #define RAM_SHUTDOWN_CR_U54_1_MASK                           (0x01 << 0x9)
    /* */
    #define RAM_SHUTDOWN_CR_U54_2_OFFSET                         0xA
    #define RAM_SHUTDOWN_CR_U54_2_MASK                           (0x01 << 0xA)
    /* */
    #define RAM_SHUTDOWN_CR_U54_3_OFFSET                         0xB
    #define RAM_SHUTDOWN_CR_U54_3_MASK                           (0x01 << 0xB)
    /* */
    #define RAM_SHUTDOWN_CR_U54_4_OFFSET                         0xC
    #define RAM_SHUTDOWN_CR_U54_4_MASK                           (0x01 << 0xC)
    /* */
    #define RAM_SHUTDOWN_CR_L2_OFFSET                            0xD
    #define RAM_SHUTDOWN_CR_L2_MASK                              (0x01 << 0xD)

/*Allows each bank of the L2 Cache to be powered down ORed with global shut
    down */
#define L2_SHUTDOWN_CR_OFFSET                                    0x174
    /* */
    #define L2_SHUTDOWN_CR_L2_RAMS_OFFSET                        0x0
    #define L2_SHUTDOWN_CR_L2_RAMS_MASK                          (0x0F << 0x0)

/*Selects whether the peripheral is connected to the Fabric or IOMUX struct
    ure.*/
#define IOMUX0_CR_OFFSET                                         0x200
    /* */
    #define IOMUX0_CR_SPI0_FABRIC_OFFSET                         0x0
    #define IOMUX0_CR_SPI0_FABRIC_MASK                           (0x01 << 0x0)
    /* */
    #define IOMUX0_CR_SPI1_FABRIC_OFFSET                         0x1
    #define IOMUX0_CR_SPI1_FABRIC_MASK                           (0x01 << 0x1)
    /* */
    #define IOMUX0_CR_I2C0_FABRIC_OFFSET                         0x2
    #define IOMUX0_CR_I2C0_FABRIC_MASK                           (0x01 << 0x2)
    /* */
    #define IOMUX0_CR_I2C1_FABRIC_OFFSET                         0x3
    #define IOMUX0_CR_I2C1_FABRIC_MASK                           (0x01 << 0x3)
    /* */
    #define IOMUX0_CR_CAN0_FABRIC_OFFSET                         0x4
    #define IOMUX0_CR_CAN0_FABRIC_MASK                           (0x01 << 0x4)
    /* */
    #define IOMUX0_CR_CAN1_FABRIC_OFFSET                         0x5
    #define IOMUX0_CR_CAN1_FABRIC_MASK                           (0x01 << 0x5)
    /* */
    #define IOMUX0_CR_QSPI_FABRIC_OFFSET                         0x6
    #define IOMUX0_CR_QSPI_FABRIC_MASK                           (0x01 << 0x6)
    /* */
    #define IOMUX0_CR_MMUART0_FABRIC_OFFSET                      0x7
    #define IOMUX0_CR_MMUART0_FABRIC_MASK                        (0x01 << 0x7)
    /* */
    #define IOMUX0_CR_MMUART1_FABRIC_OFFSET                      0x8
    #define IOMUX0_CR_MMUART1_FABRIC_MASK                        (0x01 << 0x8)
    /* */
    #define IOMUX0_CR_MMUART2_FABRIC_OFFSET                      0x9
    #define IOMUX0_CR_MMUART2_FABRIC_MASK                        (0x01 << 0x9)
    /* */
    #define IOMUX0_CR_MMUART3_FABRIC_OFFSET                      0xA
    #define IOMUX0_CR_MMUART3_FABRIC_MASK                        (0x01 << 0xA)
    /* */
    #define IOMUX0_CR_MMUART4_FABRIC_OFFSET                      0xB
    #define IOMUX0_CR_MMUART4_FABRIC_MASK                        (0x01 << 0xB)
    /* */
    #define IOMUX0_CR_MDIO0_FABRIC_OFFSET                        0xC
    #define IOMUX0_CR_MDIO0_FABRIC_MASK                          (0x01 << 0xC)
    /* */
    #define IOMUX0_CR_MDIO1_FABRIC_OFFSET                        0xD
    #define IOMUX0_CR_MDIO1_FABRIC_MASK                          (0x01 << 0xD)

/*Configures the IO Mux structure for each IO pad. See the MSS MAS specific
    ation for for description.*/
#define IOMUX1_CR_OFFSET                                         0x204
    /* */
    #define IOMUX1_CR_PAD0_OFFSET                                0x0
    #define IOMUX1_CR_PAD0_MASK                                  (0x0F << 0x0)
    /* */
    #define IOMUX1_CR_PAD1_OFFSET                                0x4
    #define IOMUX1_CR_PAD1_MASK                                  (0x0F << 0x4)
    /* */
    #define IOMUX1_CR_PAD2_OFFSET                                0x8
    #define IOMUX1_CR_PAD2_MASK                                  (0x0F << 0x8)
    /* */
    #define IOMUX1_CR_PAD3_OFFSET                                0xC
    #define IOMUX1_CR_PAD3_MASK                                  (0x0F << 0xC)
    /* */
    #define IOMUX1_CR_PAD4_OFFSET                                0x10
    #define IOMUX1_CR_PAD4_MASK                                  (0x0F << 0x10)
    /* */
    #define IOMUX1_CR_PAD5_OFFSET                                0x14
    #define IOMUX1_CR_PAD5_MASK                                  (0x0F << 0x14)
    /* */
    #define IOMUX1_CR_PAD6_OFFSET                                0x18
    #define IOMUX1_CR_PAD6_MASK                                  (0x0F << 0x18)
    /* */
    #define IOMUX1_CR_PAD7_OFFSET                                0x1C
    #define IOMUX1_CR_PAD7_MASK                                  (0x0F << 0x1C)

/*Configures the IO Mux structure for each IO pad. See the MSS MAS specific
    ation for for description.*/
#define IOMUX2_CR_OFFSET                                         0x208
    /* */
    #define IOMUX2_CR_PAD8_OFFSET                                0x0
    #define IOMUX2_CR_PAD8_MASK                                  (0x0F << 0x0)
    /* */
    #define IOMUX2_CR_PAD9_OFFSET                                0x4
    #define IOMUX2_CR_PAD9_MASK                                  (0x0F << 0x4)
    /* */
    #define IOMUX2_CR_PAD10_OFFSET                               0x8
    #define IOMUX2_CR_PAD10_MASK                                 (0x0F << 0x8)
    /* */
    #define IOMUX2_CR_PAD11_OFFSET                               0xC
    #define IOMUX2_CR_PAD11_MASK                                 (0x0F << 0xC)
    /* */
    #define IOMUX2_CR_PAD12_OFFSET                               0x10
    #define IOMUX2_CR_PAD12_MASK                                 (0x0F << 0x10)
    /* */
    #define IOMUX2_CR_PAD13_OFFSET                               0x14
    #define IOMUX2_CR_PAD13_MASK                                 (0x0F << 0x14)

/*Configures the IO Mux structure for each IO pad. See the MSS MAS specific
    ation for for description.*/
#define IOMUX3_CR_OFFSET                                         0x20C
    /* */
    #define IOMUX3_CR_PAD14_OFFSET                               0x0
    #define IOMUX3_CR_PAD14_MASK                                 (0x0F << 0x0)
    /* */
    #define IOMUX3_CR_PAD15_OFFSET                               0x4
    #define IOMUX3_CR_PAD15_MASK                                 (0x0F << 0x4)
    /* */
    #define IOMUX3_CR_PAD16_OFFSET                               0x8
    #define IOMUX3_CR_PAD16_MASK                                 (0x0F << 0x8)
    /* */
    #define IOMUX3_CR_PAD17_OFFSET                               0xC
    #define IOMUX3_CR_PAD17_MASK                                 (0x0F << 0xC)
    /* */
    #define IOMUX3_CR_PAD18_OFFSET                               0x10
    #define IOMUX3_CR_PAD18_MASK                                 (0x0F << 0x10)
    /* */
    #define IOMUX3_CR_PAD19_OFFSET                               0x14
    #define IOMUX3_CR_PAD19_MASK                                 (0x0F << 0x14)
    /* */
    #define IOMUX3_CR_PAD20_OFFSET                               0x18
    #define IOMUX3_CR_PAD20_MASK                                 (0x0F << 0x18)
    /* */
    #define IOMUX3_CR_PAD21_OFFSET                               0x1C
    #define IOMUX3_CR_PAD21_MASK                                 (0x0F << 0x1C)

/*Configures the IO Mux structure for each IO pad. See the MSS MAS specific
    ation for for description.*/
#define IOMUX4_CR_OFFSET                                         0x210
    /* */
    #define IOMUX4_CR_PAD22_OFFSET                               0x0
    #define IOMUX4_CR_PAD22_MASK                                 (0x0F << 0x0)
    /* */
    #define IOMUX4_CR_PAD23_OFFSET                               0x4
    #define IOMUX4_CR_PAD23_MASK                                 (0x0F << 0x4)
    /* */
    #define IOMUX4_CR_PAD24_OFFSET                               0x8
    #define IOMUX4_CR_PAD24_MASK                                 (0x0F << 0x8)
    /* */
    #define IOMUX4_CR_PAD25_OFFSET                               0xC
    #define IOMUX4_CR_PAD25_MASK                                 (0x0F << 0xC)
    /* */
    #define IOMUX4_CR_PAD26_OFFSET                               0x10
    #define IOMUX4_CR_PAD26_MASK                                 (0x0F << 0x10)
    /* */
    #define IOMUX4_CR_PAD27_OFFSET                               0x14
    #define IOMUX4_CR_PAD27_MASK                                 (0x0F << 0x14)
    /* */
    #define IOMUX4_CR_PAD28_OFFSET                               0x18
    #define IOMUX4_CR_PAD28_MASK                                 (0x0F << 0x18)
    /* */
    #define IOMUX4_CR_PAD29_OFFSET                               0x1C
    #define IOMUX4_CR_PAD29_MASK                                 (0x0F << 0x1C)

/*Configures the IO Mux structure for each IO pad. See the MSS MAS specific
    ation for for description.*/
#define IOMUX5_CR_OFFSET                                         0x214
    /* */
    #define IOMUX5_CR_PAD30_OFFSET                               0x0
    #define IOMUX5_CR_PAD30_MASK                                 (0x0F << 0x0)
    /* */
    #define IOMUX5_CR_PAD31_OFFSET                               0x4
    #define IOMUX5_CR_PAD31_MASK                                 (0x0F << 0x4)
    /* */
    #define IOMUX5_CR_PAD32_OFFSET                               0x8
    #define IOMUX5_CR_PAD32_MASK                                 (0x0F << 0x8)
    /* */
    #define IOMUX5_CR_PAD33_OFFSET                               0xC
    #define IOMUX5_CR_PAD33_MASK                                 (0x0F << 0xC)
    /* */
    #define IOMUX5_CR_PAD34_OFFSET                               0x10
    #define IOMUX5_CR_PAD34_MASK                                 (0x0F << 0x10)
    /* */
    #define IOMUX5_CR_PAD35_OFFSET                               0x14
    #define IOMUX5_CR_PAD35_MASK                                 (0x0F << 0x14)
    /* */
    #define IOMUX5_CR_PAD36_OFFSET                               0x18
    #define IOMUX5_CR_PAD36_MASK                                 (0x0F << 0x18)
    /* */
    #define IOMUX5_CR_PAD37_OFFSET                               0x1C
    #define IOMUX5_CR_PAD37_MASK                                 (0x0F << 0x1C)

/*Sets whether the MMC/SD Voltage select lines are inverted on entry to the
     IOMUX structure*/
#define IOMUX6_CR_OFFSET                                         0x218
    /* */
    #define IOMUX6_CR_VLT_SEL_OFFSET                             0x0
    #define IOMUX6_CR_VLT_SEL_MASK                               (0x01 << 0x0)
    /* */
    #define IOMUX6_CR_VLT_EN_OFFSET                              0x1
    #define IOMUX6_CR_VLT_EN_MASK                                (0x01 << 0x1)
    /* */
    #define IOMUX6_CR_VLT_CMD_DIR_OFFSET                         0x2
    #define IOMUX6_CR_VLT_CMD_DIR_MASK                           (0x01 << 0x2)
    /* */
    #define IOMUX6_CR_VLT_DIR_0_OFFSET                           0x3
    #define IOMUX6_CR_VLT_DIR_0_MASK                             (0x01 << 0x3)
    /* */
    #define IOMUX6_CR_VLT_DIR_1_3_OFFSET                         0x4
    #define IOMUX6_CR_VLT_DIR_1_3_MASK                           (0x01 << 0x4)
    /* */
    #define IOMUX6_CR_SD_LED_OFFSET                              0x5
    #define IOMUX6_CR_SD_LED_MASK                                (0x01 << 0x5)
    /* */
    #define IOMUX6_CR_SD_VOLT_0_OFFSET                           0x6
    #define IOMUX6_CR_SD_VOLT_0_MASK                             (0x01 << 0x6)
    /* */
    #define IOMUX6_CR_SD_VOLT_1_OFFSET                           0x7
    #define IOMUX6_CR_SD_VOLT_1_MASK                             (0x01 << 0x7)
    /* */
    #define IOMUX6_CR_SD_VOLT_2_OFFSET                           0x8
    #define IOMUX6_CR_SD_VOLT_2_MASK                             (0x01 << 0x8)

/*Configures the MSSIO block*/
#define MSSIO_BANK4_CFG_CR_OFFSET                                0x230
    /* Sets the PCODE value*/
    #define MSSIO_BANK4_CFG_CR_BANK_PCODE_OFFSET                 0x0
    #define MSSIO_BANK4_CFG_CR_BANK_PCODE_MASK                   (0x3F << 0x0)
    /* Sets the NCODE value*/
    #define MSSIO_BANK4_CFG_CR_BANK_NCODE_OFFSET                 0x6
    #define MSSIO_BANK4_CFG_CR_BANK_NCODE_MASK                   (0x3F << 0x6)
    /* Sets the voltage controls.*/
    #define MSSIO_BANK4_CFG_CR_VS_OFFSET                         0xC
    #define MSSIO_BANK4_CFG_CR_VS_MASK                           (0x0F << 0xC)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK4_IO_CFG_0_1_CR_OFFSET                         0x234
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_IBUFMD_0_OFFSET              0x0
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_IBUFMD_0_MASK                (0x01 << 0x0)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_IBUFMD_1_OFFSET              0x1
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_IBUFMD_1_MASK                (0x01 << 0x1)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_IBUFMD_2_OFFSET              0x2
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_IBUFMD_2_MASK                (0x01 << 0x2)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_DRV_0_OFFSET                 0x3
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_DRV_0_MASK                   (0x01 << 0x3)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_DRV_1_OFFSET                 0x4
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_DRV_1_MASK                   (0x01 << 0x4)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_DRV_2_OFFSET                 0x5
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_DRV_2_MASK                   (0x01 << 0x5)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_DRV_3_OFFSET                 0x6
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_DRV_3_MASK                   (0x01 << 0x6)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_CLAMP_OFFSET                 0x7
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_CLAMP_MASK                   (0x01 << 0x7)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_ENHYST_OFFSET                0x8
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_ENHYST_MASK                  (0x01 << 0x8)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_LOCKDN_EN_OFFSET             0x9
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_LOCKDN_EN_MASK               (0x01 << 0x9)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_WPD_OFFSET                   0xA
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_WPD_MASK                     (0x01 << 0xA)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_WPU_OFFSET                   0xB
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_WPU_MASK                     (0x01 << 0xB)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_ATP_EN_OFFSET                0xC
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_ATP_EN_MASK                  (0x01 << 0xC)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_LP_PERSIST_EN_OFFSET         0xD
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_LP_PERSIST_EN_MASK           (0x01 << 0xD)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_LP_BYPASS_EN_OFFSET          0xE
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_0_LP_BYPASS_EN_MASK            (0x01 << 0xE)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_IBUFMD_0_OFFSET              0x10
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_IBUFMD_0_MASK                (0x01 << 0x10)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_IBUFMD_1_OFFSET              0x11
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_IBUFMD_1_MASK                (0x01 << 0x11)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_IBUFMD_2_OFFSET              0x12
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_IBUFMD_2_MASK                (0x01 << 0x12)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_DRV_0_OFFSET                 0x13
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_DRV_0_MASK                   (0x01 << 0x13)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_DRV_1_OFFSET                 0x14
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_DRV_1_MASK                   (0x01 << 0x14)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_DRV_2_OFFSET                 0x15
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_DRV_2_MASK                   (0x01 << 0x15)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_DRV_3_OFFSET                 0x16
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_DRV_3_MASK                   (0x01 << 0x16)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_CLAMP_OFFSET                 0x17
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_CLAMP_MASK                   (0x01 << 0x17)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_ENHYST_OFFSET                0x18
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_ENHYST_MASK                  (0x01 << 0x18)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_LOCKDN_EN_OFFSET             0x19
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_LOCKDN_EN_MASK               (0x01 << 0x19)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_WPD_OFFSET                   0x1A
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_WPD_MASK                     (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_WPU_OFFSET                   0x1B
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_WPU_MASK                     (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_ATP_EN_OFFSET                0x1C
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_ATP_EN_MASK                  (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_LP_PERSIST_EN_OFFSET         0x1D
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_LP_PERSIST_EN_MASK           (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_LP_BYPASS_EN_OFFSET          0x1E
    #define MSSIO_BANK4_IO_CFG_0_1_CR_RPC_IO_CFG_1_LP_BYPASS_EN_MASK            (0x01 << 0x1E)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK4_IO_CFG_2_3_CR_OFFSET                         0x238
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_IBUFMD_0_OFFSET              0x0
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_IBUFMD_0_MASK                (0x01 << 0x0)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_IBUFMD_1_OFFSET              0x1
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_IBUFMD_1_MASK                (0x01 << 0x1)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_IBUFMD_2_OFFSET              0x2
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_IBUFMD_2_MASK                (0x01 << 0x2)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_DRV_0_OFFSET                 0x3
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_DRV_0_MASK                   (0x01 << 0x3)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_DRV_1_OFFSET                 0x4
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_DRV_1_MASK                   (0x01 << 0x4)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_DRV_2_OFFSET                 0x5
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_DRV_2_MASK                   (0x01 << 0x5)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_DRV_3_OFFSET                 0x6
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_DRV_3_MASK                   (0x01 << 0x6)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_CLAMP_OFFSET                 0x7
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_CLAMP_MASK                   (0x01 << 0x7)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_ENHYST_OFFSET                0x8
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_ENHYST_MASK                  (0x01 << 0x8)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_LOCKDN_EN_OFFSET             0x9
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_LOCKDN_EN_MASK               (0x01 << 0x9)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_WPD_OFFSET                   0xA
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_WPD_MASK                     (0x01 << 0xA)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_WPU_OFFSET                   0xB
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_WPU_MASK                     (0x01 << 0xB)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_ATP_EN_OFFSET                0xC
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_ATP_EN_MASK                  (0x01 << 0xC)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_LP_PERSIST_EN_OFFSET         0xD
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_LP_PERSIST_EN_MASK           (0x01 << 0xD)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_LP_BYPASS_EN_OFFSET          0xE
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_2_LP_BYPASS_EN_MASK            (0x01 << 0xE)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_IBUFMD_0_OFFSET              0x10
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_IBUFMD_0_MASK                (0x01 << 0x10)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_IBUFMD_1_OFFSET              0x11
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_IBUFMD_1_MASK                (0x01 << 0x11)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_IBUFMD_2_OFFSET              0x12
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_IBUFMD_2_MASK                (0x01 << 0x12)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_DRV_0_OFFSET                 0x13
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_DRV_0_MASK                   (0x01 << 0x13)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_DRV_1_OFFSET                 0x14
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_DRV_1_MASK                   (0x01 << 0x14)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_DRV_2_OFFSET                 0x15
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_DRV_2_MASK                   (0x01 << 0x15)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_DRV_3_OFFSET                 0x16
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_DRV_3_MASK                   (0x01 << 0x16)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_CLAMP_OFFSET                 0x17
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_CLAMP_MASK                   (0x01 << 0x17)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_ENHYST_OFFSET                0x18
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_ENHYST_MASK                  (0x01 << 0x18)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_LOCKDN_EN_OFFSET             0x19
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_LOCKDN_EN_MASK               (0x01 << 0x19)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_WPD_OFFSET                   0x1A
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_WPD_MASK                     (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_WPU_OFFSET                   0x1B
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_WPU_MASK                     (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_ATP_EN_OFFSET                0x1C
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_ATP_EN_MASK                  (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_LP_PERSIST_EN_OFFSET         0x1D
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_LP_PERSIST_EN_MASK           (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_LP_BYPASS_EN_OFFSET          0x1E
    #define MSSIO_BANK4_IO_CFG_2_3_CR_RPC_IO_CFG_3_LP_BYPASS_EN_MASK            (0x01 << 0x1E)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK4_IO_CFG_4_5_CR_OFFSET                         0x23C
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_IBUFMD_0_OFFSET              0x0
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_IBUFMD_0_MASK                (0x01 << 0x0)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_IBUFMD_1_OFFSET              0x1
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_IBUFMD_1_MASK                (0x01 << 0x1)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_IBUFMD_2_OFFSET              0x2
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_IBUFMD_2_MASK                (0x01 << 0x2)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_DRV_0_OFFSET                 0x3
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_DRV_0_MASK                   (0x01 << 0x3)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_DRV_1_OFFSET                 0x4
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_DRV_1_MASK                   (0x01 << 0x4)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_DRV_2_OFFSET                 0x5
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_DRV_2_MASK                   (0x01 << 0x5)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_DRV_3_OFFSET                 0x6
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_DRV_3_MASK                   (0x01 << 0x6)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_CLAMP_OFFSET                 0x7
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_CLAMP_MASK                   (0x01 << 0x7)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_ENHYST_OFFSET                0x8
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_ENHYST_MASK                  (0x01 << 0x8)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_LOCKDN_EN_OFFSET             0x9
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_LOCKDN_EN_MASK               (0x01 << 0x9)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_WPD_OFFSET                   0xA
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_WPD_MASK                     (0x01 << 0xA)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_WPU_OFFSET                   0xB
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_WPU_MASK                     (0x01 << 0xB)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_ATP_EN_OFFSET                0xC
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_ATP_EN_MASK                  (0x01 << 0xC)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_LP_PERSIST_EN_OFFSET         0xD
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_LP_PERSIST_EN_MASK           (0x01 << 0xD)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_LP_BYPASS_EN_OFFSET          0xE
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_4_LP_BYPASS_EN_MASK            (0x01 << 0xE)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_IBUFMD_0_OFFSET              0x10
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_IBUFMD_0_MASK                (0x01 << 0x10)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_IBUFMD_1_OFFSET              0x11
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_IBUFMD_1_MASK                (0x01 << 0x11)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_IBUFMD_2_OFFSET              0x12
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_IBUFMD_2_MASK                (0x01 << 0x12)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_DRV_0_OFFSET                 0x13
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_DRV_0_MASK                   (0x01 << 0x13)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_DRV_1_OFFSET                 0x14
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_DRV_1_MASK                   (0x01 << 0x14)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_DRV_2_OFFSET                 0x15
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_DRV_2_MASK                   (0x01 << 0x15)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_DRV_3_OFFSET                 0x16
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_DRV_3_MASK                   (0x01 << 0x16)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_CLAMP_OFFSET                 0x17
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_CLAMP_MASK                   (0x01 << 0x17)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_ENHYST_OFFSET                0x18
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_ENHYST_MASK                  (0x01 << 0x18)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_LOCKDN_EN_OFFSET             0x19
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_LOCKDN_EN_MASK               (0x01 << 0x19)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_WPD_OFFSET                   0x1A
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_WPD_MASK                     (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_WPU_OFFSET                   0x1B
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_WPU_MASK                     (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_ATP_EN_OFFSET                0x1C
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_ATP_EN_MASK                  (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_LP_PERSIST_EN_OFFSET         0x1D
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_LP_PERSIST_EN_MASK           (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_LP_BYPASS_EN_OFFSET          0x1E
    #define MSSIO_BANK4_IO_CFG_4_5_CR_RPC_IO_CFG_5_LP_BYPASS_EN_MASK            (0x01 << 0x1E)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK4_IO_CFG_6_7_CR_OFFSET                         0x240
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_IBUFMD_0_OFFSET              0x0
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_IBUFMD_0_MASK                (0x01 << 0x0)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_IBUFMD_1_OFFSET              0x1
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_IBUFMD_1_MASK                (0x01 << 0x1)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_IBUFMD_2_OFFSET              0x2
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_IBUFMD_2_MASK                (0x01 << 0x2)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_DRV_0_OFFSET                 0x3
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_DRV_0_MASK                   (0x01 << 0x3)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_DRV_1_OFFSET                 0x4
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_DRV_1_MASK                   (0x01 << 0x4)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_DRV_2_OFFSET                 0x5
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_DRV_2_MASK                   (0x01 << 0x5)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_DRV_3_OFFSET                 0x6
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_DRV_3_MASK                   (0x01 << 0x6)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_CLAMP_OFFSET                 0x7
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_CLAMP_MASK                   (0x01 << 0x7)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_ENHYST_OFFSET                0x8
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_ENHYST_MASK                  (0x01 << 0x8)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_LOCKDN_EN_OFFSET             0x9
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_LOCKDN_EN_MASK               (0x01 << 0x9)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_WPD_OFFSET                   0xA
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_WPD_MASK                     (0x01 << 0xA)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_WPU_OFFSET                   0xB
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_WPU_MASK                     (0x01 << 0xB)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_ATP_EN_OFFSET                0xC
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_ATP_EN_MASK                  (0x01 << 0xC)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_LP_PERSIST_EN_OFFSET         0xD
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_LP_PERSIST_EN_MASK           (0x01 << 0xD)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_LP_BYPASS_EN_OFFSET          0xE
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_6_LP_BYPASS_EN_MASK            (0x01 << 0xE)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_IBUFMD_0_OFFSET              0x10
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_IBUFMD_0_MASK                (0x01 << 0x10)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_IBUFMD_1_OFFSET              0x11
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_IBUFMD_1_MASK                (0x01 << 0x11)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_IBUFMD_2_OFFSET              0x12
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_IBUFMD_2_MASK                (0x01 << 0x12)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_DRV_0_OFFSET                 0x13
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_DRV_0_MASK                   (0x01 << 0x13)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_DRV_1_OFFSET                 0x14
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_DRV_1_MASK                   (0x01 << 0x14)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_DRV_2_OFFSET                 0x15
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_DRV_2_MASK                   (0x01 << 0x15)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_DRV_3_OFFSET                 0x16
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_DRV_3_MASK                   (0x01 << 0x16)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_CLAMP_OFFSET                 0x17
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_CLAMP_MASK                   (0x01 << 0x17)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_ENHYST_OFFSET                0x18
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_ENHYST_MASK                  (0x01 << 0x18)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_LOCKDN_EN_OFFSET             0x19
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_LOCKDN_EN_MASK               (0x01 << 0x19)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_WPD_OFFSET                   0x1A
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_WPD_MASK                     (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_WPU_OFFSET                   0x1B
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_WPU_MASK                     (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_ATP_EN_OFFSET                0x1C
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_ATP_EN_MASK                  (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_LP_PERSIST_EN_OFFSET         0x1D
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_LP_PERSIST_EN_MASK           (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_LP_BYPASS_EN_OFFSET          0x1E
    #define MSSIO_BANK4_IO_CFG_6_7_CR_RPC_IO_CFG_7_LP_BYPASS_EN_MASK            (0x01 << 0x1E)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK4_IO_CFG_8_9_CR_OFFSET                         0x244
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_IBUFMD_0_OFFSET              0x0
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_IBUFMD_0_MASK                (0x01 << 0x0)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_IBUFMD_1_OFFSET              0x1
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_IBUFMD_1_MASK                (0x01 << 0x1)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_IBUFMD_2_OFFSET              0x2
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_IBUFMD_2_MASK                (0x01 << 0x2)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_DRV_0_OFFSET                 0x3
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_DRV_0_MASK                   (0x01 << 0x3)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_DRV_1_OFFSET                 0x4
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_DRV_1_MASK                   (0x01 << 0x4)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_DRV_2_OFFSET                 0x5
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_DRV_2_MASK                   (0x01 << 0x5)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_DRV_3_OFFSET                 0x6
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_DRV_3_MASK                   (0x01 << 0x6)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_CLAMP_OFFSET                 0x7
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_CLAMP_MASK                   (0x01 << 0x7)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_ENHYST_OFFSET                0x8
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_ENHYST_MASK                  (0x01 << 0x8)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_LOCKDN_EN_OFFSET             0x9
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_LOCKDN_EN_MASK               (0x01 << 0x9)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_WPD_OFFSET                   0xA
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_WPD_MASK                     (0x01 << 0xA)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_WPU_OFFSET                   0xB
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_WPU_MASK                     (0x01 << 0xB)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_ATP_EN_OFFSET                0xC
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_ATP_EN_MASK                  (0x01 << 0xC)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_LP_PERSIST_EN_OFFSET         0xD
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_LP_PERSIST_EN_MASK           (0x01 << 0xD)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_LP_BYPASS_EN_OFFSET          0xE
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_8_LP_BYPASS_EN_MASK            (0x01 << 0xE)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_IBUFMD_0_OFFSET              0x10
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_IBUFMD_0_MASK                (0x01 << 0x10)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_IBUFMD_1_OFFSET              0x11
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_IBUFMD_1_MASK                (0x01 << 0x11)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_IBUFMD_2_OFFSET              0x12
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_IBUFMD_2_MASK                (0x01 << 0x12)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_DRV_0_OFFSET                 0x13
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_DRV_0_MASK                   (0x01 << 0x13)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_DRV_1_OFFSET                 0x14
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_DRV_1_MASK                   (0x01 << 0x14)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_DRV_2_OFFSET                 0x15
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_DRV_2_MASK                   (0x01 << 0x15)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_DRV_3_OFFSET                 0x16
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_DRV_3_MASK                   (0x01 << 0x16)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_CLAMP_OFFSET                 0x17
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_CLAMP_MASK                   (0x01 << 0x17)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_ENHYST_OFFSET                0x18
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_ENHYST_MASK                  (0x01 << 0x18)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_LOCKDN_EN_OFFSET             0x19
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_LOCKDN_EN_MASK               (0x01 << 0x19)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_WPD_OFFSET                   0x1A
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_WPD_MASK                     (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_WPU_OFFSET                   0x1B
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_WPU_MASK                     (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_ATP_EN_OFFSET                0x1C
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_ATP_EN_MASK                  (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_LP_PERSIST_EN_OFFSET         0x1D
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_LP_PERSIST_EN_MASK           (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_LP_BYPASS_EN_OFFSET          0x1E
    #define MSSIO_BANK4_IO_CFG_8_9_CR_RPC_IO_CFG_9_LP_BYPASS_EN_MASK            (0x01 << 0x1E)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK4_IO_CFG_10_11_CR_OFFSET                       0x248
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_IBUFMD_0_OFFSET           0x0
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_IBUFMD_0_MASK             (0x01 << 0x0)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_IBUFMD_1_OFFSET           0x1
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_IBUFMD_1_MASK             (0x01 << 0x1)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_IBUFMD_2_OFFSET           0x2
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_IBUFMD_2_MASK             (0x01 << 0x2)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_DRV_0_OFFSET              0x3
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_DRV_0_MASK                (0x01 << 0x3)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_DRV_1_OFFSET              0x4
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_DRV_1_MASK                (0x01 << 0x4)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_DRV_2_OFFSET              0x5
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_DRV_2_MASK                (0x01 << 0x5)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_DRV_3_OFFSET              0x6
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_DRV_3_MASK                (0x01 << 0x6)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_CLAMP_OFFSET              0x7
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_CLAMP_MASK                (0x01 << 0x7)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_ENHYST_OFFSET             0x8
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_ENHYST_MASK               (0x01 << 0x8)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_LOCKDN_EN_OFFSET          0x9
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_LOCKDN_EN_MASK            (0x01 << 0x9)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_WPD_OFFSET                0xA
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_WPD_MASK                  (0x01 << 0xA)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_WPU_OFFSET                0xB
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_WPU_MASK                  (0x01 << 0xB)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_ATP_EN_OFFSET             0xC
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_ATP_EN_MASK               (0x01 << 0xC)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_LP_PERSIST_EN_OFFSET      0xD
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_LP_PERSIST_EN_MASK        (0x01 << 0xD)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_LP_BYPASS_EN_OFFSET       0xE
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_10_LP_BYPASS_EN_MASK         (0x01 << 0xE)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_IBUFMD_0_OFFSET           0x10
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_IBUFMD_0_MASK             (0x01 << 0x10)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_IBUFMD_1_OFFSET           0x11
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_IBUFMD_1_MASK             (0x01 << 0x11)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_IBUFMD_2_OFFSET           0x12
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_IBUFMD_2_MASK             (0x01 << 0x12)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_DRV_0_OFFSET              0x13
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_DRV_0_MASK                (0x01 << 0x13)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_DRV_1_OFFSET              0x14
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_DRV_1_MASK                (0x01 << 0x14)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_DRV_2_OFFSET              0x15
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_DRV_2_MASK                (0x01 << 0x15)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_DRV_3_OFFSET              0x16
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_DRV_3_MASK                (0x01 << 0x16)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_CLAMP_OFFSET              0x17
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_CLAMP_MASK                (0x01 << 0x17)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_ENHYST_OFFSET             0x18
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_ENHYST_MASK               (0x01 << 0x18)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_LOCKDN_EN_OFFSET          0x19
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_LOCKDN_EN_MASK            (0x01 << 0x19)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_WPD_OFFSET                0x1A
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_WPD_MASK                  (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_WPU_OFFSET                0x1B
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_WPU_MASK                  (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_ATP_EN_OFFSET             0x1C
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_ATP_EN_MASK               (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_LP_PERSIST_EN_OFFSET      0x1D
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_LP_PERSIST_EN_MASK        (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_LP_BYPASS_EN_OFFSET       0x1E
    #define MSSIO_BANK4_IO_CFG_10_11_CR_RPC_IO_CFG_11_LP_BYPASS_EN_MASK         (0x01 << 0x1E)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK4_IO_CFG_12_13_CR_OFFSET                       0x24C
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_IBUFMD_0_OFFSET           0x0
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_IBUFMD_0_MASK             (0x01 << 0x0)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_IBUFMD_1_OFFSET           0x1
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_IBUFMD_1_MASK             (0x01 << 0x1)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_IBUFMD_2_OFFSET           0x2
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_IBUFMD_2_MASK             (0x01 << 0x2)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_DRV_0_OFFSET              0x3
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_DRV_0_MASK                (0x01 << 0x3)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_DRV_1_OFFSET              0x4
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_DRV_1_MASK                (0x01 << 0x4)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_DRV_2_OFFSET              0x5
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_DRV_2_MASK                (0x01 << 0x5)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_DRV_3_OFFSET              0x6
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_DRV_3_MASK                (0x01 << 0x6)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_CLAMP_OFFSET              0x7
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_CLAMP_MASK                (0x01 << 0x7)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_ENHYST_OFFSET             0x8
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_ENHYST_MASK               (0x01 << 0x8)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_LOCKDN_EN_OFFSET          0x9
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_LOCKDN_EN_MASK            (0x01 << 0x9)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_WPD_OFFSET                0xA
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_WPD_MASK                  (0x01 << 0xA)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_WPU_OFFSET                0xB
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_WPU_MASK                  (0x01 << 0xB)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_ATP_EN_OFFSET             0xC
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_ATP_EN_MASK               (0x01 << 0xC)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_LP_PERSIST_EN_OFFSET      0xD
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_LP_PERSIST_EN_MASK        (0x01 << 0xD)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_LP_BYPASS_EN_OFFSET       0xE
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_12_LP_BYPASS_EN_MASK         (0x01 << 0xE)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_IBUFMD_0_OFFSET           0x10
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_IBUFMD_0_MASK             (0x01 << 0x10)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_IBUFMD_1_OFFSET           0x11
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_IBUFMD_1_MASK             (0x01 << 0x11)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_IBUFMD_2_OFFSET           0x12
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_IBUFMD_2_MASK             (0x01 << 0x12)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_DRV_0_OFFSET              0x13
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_DRV_0_MASK                (0x01 << 0x13)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_DRV_1_OFFSET              0x14
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_DRV_1_MASK                (0x01 << 0x14)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_DRV_2_OFFSET              0x15
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_DRV_2_MASK                (0x01 << 0x15)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_DRV_3_OFFSET              0x16
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_DRV_3_MASK                (0x01 << 0x16)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_CLAMP_OFFSET              0x17
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_CLAMP_MASK                (0x01 << 0x17)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_ENHYST_OFFSET             0x18
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_ENHYST_MASK               (0x01 << 0x18)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_LOCKDN_EN_OFFSET          0x19
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_LOCKDN_EN_MASK            (0x01 << 0x19)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_WPD_OFFSET                0x1A
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_WPD_MASK                  (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_WPU_OFFSET                0x1B
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_WPU_MASK                  (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_ATP_EN_OFFSET             0x1C
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_ATP_EN_MASK               (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_LP_PERSIST_EN_OFFSET      0x1D
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_LP_PERSIST_EN_MASK        (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_LP_BYPASS_EN_OFFSET       0x1E
    #define MSSIO_BANK4_IO_CFG_12_13_CR_RPC_IO_CFG_13_LP_BYPASS_EN_MASK         (0x01 << 0x1E)

/*Configures the MSSIO block*/
#define MSSIO_BANK2_CFG_CR_OFFSET                                0x250
    /* Sets the PCODE value*/
    #define MSSIO_BANK2_CFG_CR_BANK_PCODE_OFFSET                 0x0
    #define MSSIO_BANK2_CFG_CR_BANK_PCODE_MASK                   (0x3F << 0x0)
    /* Sets the NCODE value*/
    #define MSSIO_BANK2_CFG_CR_BANK_NCODE_OFFSET                 0x6
    #define MSSIO_BANK2_CFG_CR_BANK_NCODE_MASK                   (0x3F << 0x6)
    /* Sets the voltage controls.*/
    #define MSSIO_BANK2_CFG_CR_VS_OFFSET                         0xC
    #define MSSIO_BANK2_CFG_CR_VS_MASK                           (0x0F << 0xC)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK2_IO_CFG_0_1_CR_OFFSET                         0x254
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_IBUFMD_0_OFFSET              0x0
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_IBUFMD_0_MASK                (0x01 << 0x0)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_IBUFMD_1_OFFSET              0x1
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_IBUFMD_1_MASK                (0x01 << 0x1)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_IBUFMD_2_OFFSET              0x2
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_IBUFMD_2_MASK                (0x01 << 0x2)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_DRV_0_OFFSET                 0x3
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_DRV_0_MASK                   (0x01 << 0x3)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_DRV_1_OFFSET                 0x4
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_DRV_1_MASK                   (0x01 << 0x4)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_DRV_2_OFFSET                 0x5
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_DRV_2_MASK                   (0x01 << 0x5)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_DRV_3_OFFSET                 0x6
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_DRV_3_MASK                   (0x01 << 0x6)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_CLAMP_OFFSET                 0x7
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_CLAMP_MASK                   (0x01 << 0x7)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_ENHYST_OFFSET                0x8
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_ENHYST_MASK                  (0x01 << 0x8)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_LOCKDN_EN_OFFSET             0x9
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_LOCKDN_EN_MASK               (0x01 << 0x9)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_WPD_OFFSET                   0xA
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_WPD_MASK                     (0x01 << 0xA)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_WPU_OFFSET                   0xB
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_WPU_MASK                     (0x01 << 0xB)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_ATP_EN_OFFSET                0xC
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_ATP_EN_MASK                  (0x01 << 0xC)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_LP_PERSIST_EN_OFFSET         0xD
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_LP_PERSIST_EN_MASK           (0x01 << 0xD)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_LP_BYPASS_EN_OFFSET          0xE
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_0_LP_BYPASS_EN_MASK            (0x01 << 0xE)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_IBUFMD_0_OFFSET              0x10
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_IBUFMD_0_MASK                (0x01 << 0x10)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_IBUFMD_1_OFFSET              0x11
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_IBUFMD_1_MASK                (0x01 << 0x11)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_IBUFMD_2_OFFSET              0x12
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_IBUFMD_2_MASK                (0x01 << 0x12)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_DRV_0_OFFSET                 0x13
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_DRV_0_MASK                   (0x01 << 0x13)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_DRV_1_OFFSET                 0x14
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_DRV_1_MASK                   (0x01 << 0x14)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_DRV_2_OFFSET                 0x15
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_DRV_2_MASK                   (0x01 << 0x15)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_DRV_3_OFFSET                 0x16
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_DRV_3_MASK                   (0x01 << 0x16)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_CLAMP_OFFSET                 0x17
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_CLAMP_MASK                   (0x01 << 0x17)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_ENHYST_OFFSET                0x18
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_ENHYST_MASK                  (0x01 << 0x18)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_LOCKDN_EN_OFFSET             0x19
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_LOCKDN_EN_MASK               (0x01 << 0x19)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_WPD_OFFSET                   0x1A
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_WPD_MASK                     (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_WPU_OFFSET                   0x1B
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_WPU_MASK                     (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_ATP_EN_OFFSET                0x1C
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_ATP_EN_MASK                  (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_LP_PERSIST_EN_OFFSET         0x1D
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_LP_PERSIST_EN_MASK           (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_LP_BYPASS_EN_OFFSET          0x1E
    #define MSSIO_BANK2_IO_CFG_0_1_CR_RPC_IO_CFG_1_LP_BYPASS_EN_MASK            (0x01 << 0x1E)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK2_IO_CFG_2_3_CR_OFFSET                         0x258
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_IBUFMD_0_OFFSET              0x0
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_IBUFMD_0_MASK                (0x01 << 0x0)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_IBUFMD_1_OFFSET              0x1
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_IBUFMD_1_MASK                (0x01 << 0x1)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_IBUFMD_2_OFFSET              0x2
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_IBUFMD_2_MASK                (0x01 << 0x2)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_DRV_0_OFFSET                 0x3
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_DRV_0_MASK                   (0x01 << 0x3)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_DRV_1_OFFSET                 0x4
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_DRV_1_MASK                   (0x01 << 0x4)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_DRV_2_OFFSET                 0x5
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_DRV_2_MASK                   (0x01 << 0x5)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_DRV_3_OFFSET                 0x6
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_DRV_3_MASK                   (0x01 << 0x6)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_CLAMP_OFFSET                 0x7
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_CLAMP_MASK                   (0x01 << 0x7)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_ENHYST_OFFSET                0x8
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_ENHYST_MASK                  (0x01 << 0x8)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_LOCKDN_EN_OFFSET             0x9
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_LOCKDN_EN_MASK               (0x01 << 0x9)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_WPD_OFFSET                   0xA
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_WPD_MASK                     (0x01 << 0xA)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_WPU_OFFSET                   0xB
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_WPU_MASK                     (0x01 << 0xB)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_ATP_EN_OFFSET                0xC
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_ATP_EN_MASK                  (0x01 << 0xC)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_LP_PERSIST_EN_OFFSET         0xD
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_LP_PERSIST_EN_MASK           (0x01 << 0xD)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_LP_BYPASS_EN_OFFSET          0xE
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_2_LP_BYPASS_EN_MASK            (0x01 << 0xE)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_IBUFMD_0_OFFSET              0x10
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_IBUFMD_0_MASK                (0x01 << 0x10)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_IBUFMD_1_OFFSET              0x11
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_IBUFMD_1_MASK                (0x01 << 0x11)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_IBUFMD_2_OFFSET              0x12
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_IBUFMD_2_MASK                (0x01 << 0x12)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_DRV_0_OFFSET                 0x13
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_DRV_0_MASK                   (0x01 << 0x13)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_DRV_1_OFFSET                 0x14
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_DRV_1_MASK                   (0x01 << 0x14)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_DRV_2_OFFSET                 0x15
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_DRV_2_MASK                   (0x01 << 0x15)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_DRV_3_OFFSET                 0x16
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_DRV_3_MASK                   (0x01 << 0x16)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_CLAMP_OFFSET                 0x17
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_CLAMP_MASK                   (0x01 << 0x17)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_ENHYST_OFFSET                0x18
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_ENHYST_MASK                  (0x01 << 0x18)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_LOCKDN_EN_OFFSET             0x19
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_LOCKDN_EN_MASK               (0x01 << 0x19)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_WPD_OFFSET                   0x1A
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_WPD_MASK                     (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_WPU_OFFSET                   0x1B
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_WPU_MASK                     (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_ATP_EN_OFFSET                0x1C
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_ATP_EN_MASK                  (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_LP_PERSIST_EN_OFFSET         0x1D
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_LP_PERSIST_EN_MASK           (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_LP_BYPASS_EN_OFFSET          0x1E
    #define MSSIO_BANK2_IO_CFG_2_3_CR_RPC_IO_CFG_3_LP_BYPASS_EN_MASK            (0x01 << 0x1E)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK2_IO_CFG_4_5_CR_OFFSET                         0x25C
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_IBUFMD_0_OFFSET              0x0
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_IBUFMD_0_MASK                (0x01 << 0x0)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_IBUFMD_1_OFFSET              0x1
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_IBUFMD_1_MASK                (0x01 << 0x1)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_IBUFMD_2_OFFSET              0x2
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_IBUFMD_2_MASK                (0x01 << 0x2)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_DRV_0_OFFSET                 0x3
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_DRV_0_MASK                   (0x01 << 0x3)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_DRV_1_OFFSET                 0x4
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_DRV_1_MASK                   (0x01 << 0x4)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_DRV_2_OFFSET                 0x5
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_DRV_2_MASK                   (0x01 << 0x5)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_DRV_3_OFFSET                 0x6
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_DRV_3_MASK                   (0x01 << 0x6)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_CLAMP_OFFSET                 0x7
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_CLAMP_MASK                   (0x01 << 0x7)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_ENHYST_OFFSET                0x8
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_ENHYST_MASK                  (0x01 << 0x8)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_LOCKDN_EN_OFFSET             0x9
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_LOCKDN_EN_MASK               (0x01 << 0x9)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_WPD_OFFSET                   0xA
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_WPD_MASK                     (0x01 << 0xA)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_WPU_OFFSET                   0xB
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_WPU_MASK                     (0x01 << 0xB)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_ATP_EN_OFFSET                0xC
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_ATP_EN_MASK                  (0x01 << 0xC)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_LP_PERSIST_EN_OFFSET         0xD
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_LP_PERSIST_EN_MASK           (0x01 << 0xD)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_LP_BYPASS_EN_OFFSET          0xE
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_4_LP_BYPASS_EN_MASK            (0x01 << 0xE)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_IBUFMD_0_OFFSET              0x10
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_IBUFMD_0_MASK                (0x01 << 0x10)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_IBUFMD_1_OFFSET              0x11
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_IBUFMD_1_MASK                (0x01 << 0x11)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_IBUFMD_2_OFFSET              0x12
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_IBUFMD_2_MASK                (0x01 << 0x12)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_DRV_0_OFFSET                 0x13
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_DRV_0_MASK                   (0x01 << 0x13)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_DRV_1_OFFSET                 0x14
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_DRV_1_MASK                   (0x01 << 0x14)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_DRV_2_OFFSET                 0x15
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_DRV_2_MASK                   (0x01 << 0x15)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_DRV_3_OFFSET                 0x16
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_DRV_3_MASK                   (0x01 << 0x16)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_CLAMP_OFFSET                 0x17
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_CLAMP_MASK                   (0x01 << 0x17)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_ENHYST_OFFSET                0x18
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_ENHYST_MASK                  (0x01 << 0x18)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_LOCKDN_EN_OFFSET             0x19
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_LOCKDN_EN_MASK               (0x01 << 0x19)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_WPD_OFFSET                   0x1A
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_WPD_MASK                     (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_WPU_OFFSET                   0x1B
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_WPU_MASK                     (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_ATP_EN_OFFSET                0x1C
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_ATP_EN_MASK                  (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_LP_PERSIST_EN_OFFSET         0x1D
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_LP_PERSIST_EN_MASK           (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_LP_BYPASS_EN_OFFSET          0x1E
    #define MSSIO_BANK2_IO_CFG_4_5_CR_RPC_IO_CFG_5_LP_BYPASS_EN_MASK            (0x01 << 0x1E)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK2_IO_CFG_6_7_CR_OFFSET                         0x260
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_IBUFMD_0_OFFSET              0x0
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_IBUFMD_0_MASK                (0x01 << 0x0)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_IBUFMD_1_OFFSET              0x1
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_IBUFMD_1_MASK                (0x01 << 0x1)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_IBUFMD_2_OFFSET              0x2
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_IBUFMD_2_MASK                (0x01 << 0x2)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_DRV_0_OFFSET                 0x3
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_DRV_0_MASK                   (0x01 << 0x3)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_DRV_1_OFFSET                 0x4
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_DRV_1_MASK                   (0x01 << 0x4)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_DRV_2_OFFSET                 0x5
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_DRV_2_MASK                   (0x01 << 0x5)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_DRV_3_OFFSET                 0x6
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_DRV_3_MASK                   (0x01 << 0x6)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_CLAMP_OFFSET                 0x7
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_CLAMP_MASK                   (0x01 << 0x7)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_ENHYST_OFFSET                0x8
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_ENHYST_MASK                  (0x01 << 0x8)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_LOCKDN_EN_OFFSET             0x9
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_LOCKDN_EN_MASK               (0x01 << 0x9)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_WPD_OFFSET                   0xA
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_WPD_MASK                     (0x01 << 0xA)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_WPU_OFFSET                   0xB
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_WPU_MASK                     (0x01 << 0xB)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_ATP_EN_OFFSET                0xC
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_ATP_EN_MASK                  (0x01 << 0xC)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_LP_PERSIST_EN_OFFSET         0xD
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_LP_PERSIST_EN_MASK           (0x01 << 0xD)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_LP_BYPASS_EN_OFFSET          0xE
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_6_LP_BYPASS_EN_MASK            (0x01 << 0xE)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_IBUFMD_0_OFFSET              0x10
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_IBUFMD_0_MASK                (0x01 << 0x10)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_IBUFMD_1_OFFSET              0x11
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_IBUFMD_1_MASK                (0x01 << 0x11)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_IBUFMD_2_OFFSET              0x12
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_IBUFMD_2_MASK                (0x01 << 0x12)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_DRV_0_OFFSET                 0x13
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_DRV_0_MASK                   (0x01 << 0x13)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_DRV_1_OFFSET                 0x14
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_DRV_1_MASK                   (0x01 << 0x14)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_DRV_2_OFFSET                 0x15
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_DRV_2_MASK                   (0x01 << 0x15)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_DRV_3_OFFSET                 0x16
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_DRV_3_MASK                   (0x01 << 0x16)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_CLAMP_OFFSET                 0x17
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_CLAMP_MASK                   (0x01 << 0x17)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_ENHYST_OFFSET                0x18
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_ENHYST_MASK                  (0x01 << 0x18)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_LOCKDN_EN_OFFSET             0x19
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_LOCKDN_EN_MASK               (0x01 << 0x19)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_WPD_OFFSET                   0x1A
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_WPD_MASK                     (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_WPU_OFFSET                   0x1B
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_WPU_MASK                     (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_ATP_EN_OFFSET                0x1C
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_ATP_EN_MASK                  (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_LP_PERSIST_EN_OFFSET         0x1D
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_LP_PERSIST_EN_MASK           (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_LP_BYPASS_EN_OFFSET          0x1E
    #define MSSIO_BANK2_IO_CFG_6_7_CR_RPC_IO_CFG_7_LP_BYPASS_EN_MASK            (0x01 << 0x1E)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK2_IO_CFG_8_9_CR_OFFSET                         0x264
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_IBUFMD_0_OFFSET              0x0
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_IBUFMD_0_MASK                (0x01 << 0x0)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_IBUFMD_1_OFFSET              0x1
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_IBUFMD_1_MASK                (0x01 << 0x1)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_IBUFMD_2_OFFSET              0x2
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_IBUFMD_2_MASK                (0x01 << 0x2)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_DRV_0_OFFSET                 0x3
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_DRV_0_MASK                   (0x01 << 0x3)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_DRV_1_OFFSET                 0x4
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_DRV_1_MASK                   (0x01 << 0x4)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_DRV_2_OFFSET                 0x5
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_DRV_2_MASK                   (0x01 << 0x5)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_DRV_3_OFFSET                 0x6
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_DRV_3_MASK                   (0x01 << 0x6)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_CLAMP_OFFSET                 0x7
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_CLAMP_MASK                   (0x01 << 0x7)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_ENHYST_OFFSET                0x8
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_ENHYST_MASK                  (0x01 << 0x8)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_LOCKDN_EN_OFFSET             0x9
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_LOCKDN_EN_MASK               (0x01 << 0x9)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_WPD_OFFSET                   0xA
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_WPD_MASK                     (0x01 << 0xA)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_WPU_OFFSET                   0xB
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_WPU_MASK                     (0x01 << 0xB)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_ATP_EN_OFFSET                0xC
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_ATP_EN_MASK                  (0x01 << 0xC)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_LP_PERSIST_EN_OFFSET         0xD
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_LP_PERSIST_EN_MASK           (0x01 << 0xD)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_LP_BYPASS_EN_OFFSET          0xE
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_8_LP_BYPASS_EN_MASK            (0x01 << 0xE)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_IBUFMD_0_OFFSET              0x10
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_IBUFMD_0_MASK                (0x01 << 0x10)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_IBUFMD_1_OFFSET              0x11
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_IBUFMD_1_MASK                (0x01 << 0x11)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_IBUFMD_2_OFFSET              0x12
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_IBUFMD_2_MASK                (0x01 << 0x12)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_DRV_0_OFFSET                 0x13
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_DRV_0_MASK                   (0x01 << 0x13)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_DRV_1_OFFSET                 0x14
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_DRV_1_MASK                   (0x01 << 0x14)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_DRV_2_OFFSET                 0x15
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_DRV_2_MASK                   (0x01 << 0x15)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_DRV_3_OFFSET                 0x16
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_DRV_3_MASK                   (0x01 << 0x16)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_CLAMP_OFFSET                 0x17
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_CLAMP_MASK                   (0x01 << 0x17)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_ENHYST_OFFSET                0x18
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_ENHYST_MASK                  (0x01 << 0x18)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_LOCKDN_EN_OFFSET             0x19
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_LOCKDN_EN_MASK               (0x01 << 0x19)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_WPD_OFFSET                   0x1A
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_WPD_MASK                     (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_WPU_OFFSET                   0x1B
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_WPU_MASK                     (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_ATP_EN_OFFSET                0x1C
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_ATP_EN_MASK                  (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_LP_PERSIST_EN_OFFSET         0x1D
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_LP_PERSIST_EN_MASK           (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_LP_BYPASS_EN_OFFSET          0x1E
    #define MSSIO_BANK2_IO_CFG_8_9_CR_RPC_IO_CFG_9_LP_BYPASS_EN_MASK            (0x01 << 0x1E)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK2_IO_CFG_10_11_CR_OFFSET                       0x268
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_IBUFMD_0_OFFSET           0x0
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_IBUFMD_0_MASK             (0x01 << 0x0)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_IBUFMD_1_OFFSET           0x1
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_IBUFMD_1_MASK             (0x01 << 0x1)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_IBUFMD_2_OFFSET           0x2
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_IBUFMD_2_MASK             (0x01 << 0x2)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_DRV_0_OFFSET              0x3
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_DRV_0_MASK                (0x01 << 0x3)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_DRV_1_OFFSET              0x4
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_DRV_1_MASK                (0x01 << 0x4)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_DRV_2_OFFSET              0x5
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_DRV_2_MASK                (0x01 << 0x5)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_DRV_3_OFFSET              0x6
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_DRV_3_MASK                (0x01 << 0x6)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_CLAMP_OFFSET              0x7
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_CLAMP_MASK                (0x01 << 0x7)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_ENHYST_OFFSET             0x8
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_ENHYST_MASK               (0x01 << 0x8)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_LOCKDN_EN_OFFSET          0x9
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_LOCKDN_EN_MASK            (0x01 << 0x9)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_WPD_OFFSET                0xA
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_WPD_MASK                  (0x01 << 0xA)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_WPU_OFFSET                0xB
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_WPU_MASK                  (0x01 << 0xB)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_ATP_EN_OFFSET             0xC
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_ATP_EN_MASK               (0x01 << 0xC)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_LP_PERSIST_EN_OFFSET      0xD
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_LP_PERSIST_EN_MASK        (0x01 << 0xD)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_LP_BYPASS_EN_OFFSET       0xE
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_10_LP_BYPASS_EN_MASK         (0x01 << 0xE)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_IBUFMD_0_OFFSET           0x10
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_IBUFMD_0_MASK             (0x01 << 0x10)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_IBUFMD_1_OFFSET           0x11
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_IBUFMD_1_MASK             (0x01 << 0x11)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_IBUFMD_2_OFFSET           0x12
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_IBUFMD_2_MASK             (0x01 << 0x12)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_DRV_0_OFFSET              0x13
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_DRV_0_MASK                (0x01 << 0x13)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_DRV_1_OFFSET              0x14
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_DRV_1_MASK                (0x01 << 0x14)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_DRV_2_OFFSET              0x15
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_DRV_2_MASK                (0x01 << 0x15)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_DRV_3_OFFSET              0x16
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_DRV_3_MASK                (0x01 << 0x16)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_CLAMP_OFFSET              0x17
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_CLAMP_MASK                (0x01 << 0x17)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_ENHYST_OFFSET             0x18
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_ENHYST_MASK               (0x01 << 0x18)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_LOCKDN_EN_OFFSET          0x19
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_LOCKDN_EN_MASK            (0x01 << 0x19)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_WPD_OFFSET                0x1A
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_WPD_MASK                  (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_WPU_OFFSET                0x1B
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_WPU_MASK                  (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_ATP_EN_OFFSET             0x1C
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_ATP_EN_MASK               (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_LP_PERSIST_EN_OFFSET      0x1D
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_LP_PERSIST_EN_MASK        (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_LP_BYPASS_EN_OFFSET       0x1E
    #define MSSIO_BANK2_IO_CFG_10_11_CR_RPC_IO_CFG_11_LP_BYPASS_EN_MASK         (0x01 << 0x1E)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK2_IO_CFG_12_13_CR_OFFSET                       0x26C
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_IBUFMD_0_OFFSET           0x0
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_IBUFMD_0_MASK             (0x01 << 0x0)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_IBUFMD_1_OFFSET           0x1
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_IBUFMD_1_MASK             (0x01 << 0x1)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_IBUFMD_2_OFFSET           0x2
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_IBUFMD_2_MASK             (0x01 << 0x2)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_DRV_0_OFFSET              0x3
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_DRV_0_MASK                (0x01 << 0x3)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_DRV_1_OFFSET              0x4
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_DRV_1_MASK                (0x01 << 0x4)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_DRV_2_OFFSET              0x5
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_DRV_2_MASK                (0x01 << 0x5)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_DRV_3_OFFSET              0x6
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_DRV_3_MASK                (0x01 << 0x6)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_CLAMP_OFFSET              0x7
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_CLAMP_MASK                (0x01 << 0x7)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_ENHYST_OFFSET             0x8
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_ENHYST_MASK               (0x01 << 0x8)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_LOCKDN_EN_OFFSET          0x9
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_LOCKDN_EN_MASK            (0x01 << 0x9)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_WPD_OFFSET                0xA
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_WPD_MASK                  (0x01 << 0xA)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_WPU_OFFSET                0xB
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_WPU_MASK                  (0x01 << 0xB)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_ATP_EN_OFFSET             0xC
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_ATP_EN_MASK               (0x01 << 0xC)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_LP_PERSIST_EN_OFFSET      0xD
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_LP_PERSIST_EN_MASK        (0x01 << 0xD)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_LP_BYPASS_EN_OFFSET       0xE
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_12_LP_BYPASS_EN_MASK         (0x01 << 0xE)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_IBUFMD_0_OFFSET           0x10
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_IBUFMD_0_MASK             (0x01 << 0x10)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_IBUFMD_1_OFFSET           0x11
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_IBUFMD_1_MASK             (0x01 << 0x11)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_IBUFMD_2_OFFSET           0x12
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_IBUFMD_2_MASK             (0x01 << 0x12)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_DRV_0_OFFSET              0x13
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_DRV_0_MASK                (0x01 << 0x13)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_DRV_1_OFFSET              0x14
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_DRV_1_MASK                (0x01 << 0x14)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_DRV_2_OFFSET              0x15
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_DRV_2_MASK                (0x01 << 0x15)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_DRV_3_OFFSET              0x16
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_DRV_3_MASK                (0x01 << 0x16)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_CLAMP_OFFSET              0x17
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_CLAMP_MASK                (0x01 << 0x17)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_ENHYST_OFFSET             0x18
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_ENHYST_MASK               (0x01 << 0x18)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_LOCKDN_EN_OFFSET          0x19
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_LOCKDN_EN_MASK            (0x01 << 0x19)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_WPD_OFFSET                0x1A
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_WPD_MASK                  (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_WPU_OFFSET                0x1B
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_WPU_MASK                  (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_ATP_EN_OFFSET             0x1C
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_ATP_EN_MASK               (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_LP_PERSIST_EN_OFFSET      0x1D
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_LP_PERSIST_EN_MASK        (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_LP_BYPASS_EN_OFFSET       0x1E
    #define MSSIO_BANK2_IO_CFG_12_13_CR_RPC_IO_CFG_13_LP_BYPASS_EN_MASK         (0x01 << 0x1E)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK2_IO_CFG_14_15_CR_OFFSET                       0x270
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_IBUFMD_0_OFFSET           0x0
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_IBUFMD_0_MASK             (0x01 << 0x0)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_IBUFMD_1_OFFSET           0x1
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_IBUFMD_1_MASK             (0x01 << 0x1)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_IBUFMD_2_OFFSET           0x2
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_IBUFMD_2_MASK             (0x01 << 0x2)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_DRV_0_OFFSET              0x3
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_DRV_0_MASK                (0x01 << 0x3)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_DRV_1_OFFSET              0x4
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_DRV_1_MASK                (0x01 << 0x4)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_DRV_2_OFFSET              0x5
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_DRV_2_MASK                (0x01 << 0x5)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_DRV_3_OFFSET              0x6
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_DRV_3_MASK                (0x01 << 0x6)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_CLAMP_OFFSET              0x7
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_CLAMP_MASK                (0x01 << 0x7)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_ENHYST_OFFSET             0x8
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_ENHYST_MASK               (0x01 << 0x8)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_LOCKDN_EN_OFFSET          0x9
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_LOCKDN_EN_MASK            (0x01 << 0x9)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_WPD_OFFSET                0xA
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_WPD_MASK                  (0x01 << 0xA)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_WPU_OFFSET                0xB
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_WPU_MASK                  (0x01 << 0xB)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_ATP_EN_OFFSET             0xC
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_ATP_EN_MASK               (0x01 << 0xC)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_LP_PERSIST_EN_OFFSET      0xD
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_LP_PERSIST_EN_MASK        (0x01 << 0xD)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_LP_BYPASS_EN_OFFSET       0xE
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_14_LP_BYPASS_EN_MASK         (0x01 << 0xE)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_IBUFMD_0_OFFSET           0x10
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_IBUFMD_0_MASK             (0x01 << 0x10)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_IBUFMD_1_OFFSET           0x11
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_IBUFMD_1_MASK             (0x01 << 0x11)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_IBUFMD_2_OFFSET           0x12
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_IBUFMD_2_MASK             (0x01 << 0x12)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_DRV_0_OFFSET              0x13
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_DRV_0_MASK                (0x01 << 0x13)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_DRV_1_OFFSET              0x14
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_DRV_1_MASK                (0x01 << 0x14)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_DRV_2_OFFSET              0x15
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_DRV_2_MASK                (0x01 << 0x15)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_DRV_3_OFFSET              0x16
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_DRV_3_MASK                (0x01 << 0x16)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_CLAMP_OFFSET              0x17
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_CLAMP_MASK                (0x01 << 0x17)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_ENHYST_OFFSET             0x18
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_ENHYST_MASK               (0x01 << 0x18)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_LOCKDN_EN_OFFSET          0x19
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_LOCKDN_EN_MASK            (0x01 << 0x19)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_WPD_OFFSET                0x1A
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_WPD_MASK                  (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_WPU_OFFSET                0x1B
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_WPU_MASK                  (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_ATP_EN_OFFSET             0x1C
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_ATP_EN_MASK               (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_LP_PERSIST_EN_OFFSET      0x1D
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_LP_PERSIST_EN_MASK        (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_LP_BYPASS_EN_OFFSET       0x1E
    #define MSSIO_BANK2_IO_CFG_14_15_CR_RPC_IO_CFG_15_LP_BYPASS_EN_MASK         (0x01 << 0x1E)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK2_IO_CFG_16_17_CR_OFFSET                       0x274
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_IBUFMD_0_OFFSET           0x0
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_IBUFMD_0_MASK             (0x01 << 0x0)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_IBUFMD_1_OFFSET           0x1
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_IBUFMD_1_MASK             (0x01 << 0x1)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_IBUFMD_2_OFFSET           0x2
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_IBUFMD_2_MASK             (0x01 << 0x2)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_DRV_0_OFFSET              0x3
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_DRV_0_MASK                (0x01 << 0x3)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_DRV_1_OFFSET              0x4
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_DRV_1_MASK                (0x01 << 0x4)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_DRV_2_OFFSET              0x5
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_DRV_2_MASK                (0x01 << 0x5)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_DRV_3_OFFSET              0x6
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_DRV_3_MASK                (0x01 << 0x6)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_CLAMP_OFFSET              0x7
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_CLAMP_MASK                (0x01 << 0x7)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_ENHYST_OFFSET             0x8
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_ENHYST_MASK               (0x01 << 0x8)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_LOCKDN_EN_OFFSET          0x9
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_LOCKDN_EN_MASK            (0x01 << 0x9)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_WPD_OFFSET                0xA
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_WPD_MASK                  (0x01 << 0xA)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_WPU_OFFSET                0xB
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_WPU_MASK                  (0x01 << 0xB)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_ATP_EN_OFFSET             0xC
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_ATP_EN_MASK               (0x01 << 0xC)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_LP_PERSIST_EN_OFFSET      0xD
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_LP_PERSIST_EN_MASK        (0x01 << 0xD)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_LP_BYPASS_EN_OFFSET       0xE
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_16_LP_BYPASS_EN_MASK         (0x01 << 0xE)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_IBUFMD_0_OFFSET           0x10
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_IBUFMD_0_MASK             (0x01 << 0x10)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_IBUFMD_1_OFFSET           0x11
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_IBUFMD_1_MASK             (0x01 << 0x11)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_IBUFMD_2_OFFSET           0x12
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_IBUFMD_2_MASK             (0x01 << 0x12)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_DRV_0_OFFSET              0x13
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_DRV_0_MASK                (0x01 << 0x13)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_DRV_1_OFFSET              0x14
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_DRV_1_MASK                (0x01 << 0x14)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_DRV_2_OFFSET              0x15
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_DRV_2_MASK                (0x01 << 0x15)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_DRV_3_OFFSET              0x16
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_DRV_3_MASK                (0x01 << 0x16)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_CLAMP_OFFSET              0x17
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_CLAMP_MASK                (0x01 << 0x17)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_ENHYST_OFFSET             0x18
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_ENHYST_MASK               (0x01 << 0x18)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_LOCKDN_EN_OFFSET          0x19
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_LOCKDN_EN_MASK            (0x01 << 0x19)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_WPD_OFFSET                0x1A
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_WPD_MASK                  (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_WPU_OFFSET                0x1B
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_WPU_MASK                  (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_ATP_EN_OFFSET             0x1C
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_ATP_EN_MASK               (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_LP_PERSIST_EN_OFFSET      0x1D
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_LP_PERSIST_EN_MASK        (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_LP_BYPASS_EN_OFFSET       0x1E
    #define MSSIO_BANK2_IO_CFG_16_17_CR_RPC_IO_CFG_17_LP_BYPASS_EN_MASK         (0x01 << 0x1E)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK2_IO_CFG_18_19_CR_OFFSET                       0x278
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_IBUFMD_0_OFFSET           0x0
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_IBUFMD_0_MASK             (0x01 << 0x0)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_IBUFMD_1_OFFSET           0x1
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_IBUFMD_1_MASK             (0x01 << 0x1)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_IBUFMD_2_OFFSET           0x2
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_IBUFMD_2_MASK             (0x01 << 0x2)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_DRV_0_OFFSET              0x3
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_DRV_0_MASK                (0x01 << 0x3)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_DRV_1_OFFSET              0x4
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_DRV_1_MASK                (0x01 << 0x4)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_DRV_2_OFFSET              0x5
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_DRV_2_MASK                (0x01 << 0x5)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_DRV_3_OFFSET              0x6
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_DRV_3_MASK                (0x01 << 0x6)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_CLAMP_OFFSET              0x7
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_CLAMP_MASK                (0x01 << 0x7)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_ENHYST_OFFSET             0x8
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_ENHYST_MASK               (0x01 << 0x8)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_LOCKDN_EN_OFFSET          0x9
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_LOCKDN_EN_MASK            (0x01 << 0x9)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_WPD_OFFSET                0xA
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_WPD_MASK                  (0x01 << 0xA)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_WPU_OFFSET                0xB
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_WPU_MASK                  (0x01 << 0xB)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_ATP_EN_OFFSET             0xC
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_ATP_EN_MASK               (0x01 << 0xC)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_LP_PERSIST_EN_OFFSET      0xD
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_LP_PERSIST_EN_MASK        (0x01 << 0xD)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_LP_BYPASS_EN_OFFSET       0xE
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_18_LP_BYPASS_EN_MASK         (0x01 << 0xE)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_IBUFMD_0_OFFSET           0x10
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_IBUFMD_0_MASK             (0x01 << 0x10)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_IBUFMD_1_OFFSET           0x11
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_IBUFMD_1_MASK             (0x01 << 0x11)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_IBUFMD_2_OFFSET           0x12
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_IBUFMD_2_MASK             (0x01 << 0x12)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_DRV_0_OFFSET              0x13
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_DRV_0_MASK                (0x01 << 0x13)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_DRV_1_OFFSET              0x14
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_DRV_1_MASK                (0x01 << 0x14)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_DRV_2_OFFSET              0x15
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_DRV_2_MASK                (0x01 << 0x15)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_DRV_3_OFFSET              0x16
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_DRV_3_MASK                (0x01 << 0x16)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_CLAMP_OFFSET              0x17
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_CLAMP_MASK                (0x01 << 0x17)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_ENHYST_OFFSET             0x18
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_ENHYST_MASK               (0x01 << 0x18)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_LOCKDN_EN_OFFSET          0x19
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_LOCKDN_EN_MASK            (0x01 << 0x19)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_WPD_OFFSET                0x1A
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_WPD_MASK                  (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_WPU_OFFSET                0x1B
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_WPU_MASK                  (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_ATP_EN_OFFSET             0x1C
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_ATP_EN_MASK               (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_LP_PERSIST_EN_OFFSET      0x1D
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_LP_PERSIST_EN_MASK        (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_LP_BYPASS_EN_OFFSET       0x1E
    #define MSSIO_BANK2_IO_CFG_18_19_CR_RPC_IO_CFG_19_LP_BYPASS_EN_MASK         (0x01 << 0x1E)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK2_IO_CFG_20_21_CR_OFFSET                       0x27C
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_IBUFMD_0_OFFSET           0x0
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_IBUFMD_0_MASK             (0x01 << 0x0)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_IBUFMD_1_OFFSET           0x1
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_IBUFMD_1_MASK             (0x01 << 0x1)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_IBUFMD_2_OFFSET           0x2
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_IBUFMD_2_MASK             (0x01 << 0x2)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_DRV_0_OFFSET              0x3
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_DRV_0_MASK                (0x01 << 0x3)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_DRV_1_OFFSET              0x4
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_DRV_1_MASK                (0x01 << 0x4)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_DRV_2_OFFSET              0x5
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_DRV_2_MASK                (0x01 << 0x5)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_DRV_3_OFFSET              0x6
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_DRV_3_MASK                (0x01 << 0x6)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_CLAMP_OFFSET              0x7
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_CLAMP_MASK                (0x01 << 0x7)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_ENHYST_OFFSET             0x8
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_ENHYST_MASK               (0x01 << 0x8)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_LOCKDN_EN_OFFSET          0x9
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_LOCKDN_EN_MASK            (0x01 << 0x9)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_WPD_OFFSET                0xA
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_WPD_MASK                  (0x01 << 0xA)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_WPU_OFFSET                0xB
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_WPU_MASK                  (0x01 << 0xB)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_ATP_EN_OFFSET             0xC
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_ATP_EN_MASK               (0x01 << 0xC)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_LP_PERSIST_EN_OFFSET      0xD
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_LP_PERSIST_EN_MASK        (0x01 << 0xD)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_LP_BYPASS_EN_OFFSET       0xE
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_20_LP_BYPASS_EN_MASK         (0x01 << 0xE)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_IBUFMD_0_OFFSET           0x10
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_IBUFMD_0_MASK             (0x01 << 0x10)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_IBUFMD_1_OFFSET           0x11
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_IBUFMD_1_MASK             (0x01 << 0x11)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_IBUFMD_2_OFFSET           0x12
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_IBUFMD_2_MASK             (0x01 << 0x12)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_DRV_0_OFFSET              0x13
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_DRV_0_MASK                (0x01 << 0x13)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_DRV_1_OFFSET              0x14
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_DRV_1_MASK                (0x01 << 0x14)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_DRV_2_OFFSET              0x15
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_DRV_2_MASK                (0x01 << 0x15)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_DRV_3_OFFSET              0x16
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_DRV_3_MASK                (0x01 << 0x16)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_CLAMP_OFFSET              0x17
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_CLAMP_MASK                (0x01 << 0x17)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_ENHYST_OFFSET             0x18
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_ENHYST_MASK               (0x01 << 0x18)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_LOCKDN_EN_OFFSET          0x19
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_LOCKDN_EN_MASK            (0x01 << 0x19)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_WPD_OFFSET                0x1A
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_WPD_MASK                  (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_WPU_OFFSET                0x1B
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_WPU_MASK                  (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_ATP_EN_OFFSET             0x1C
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_ATP_EN_MASK               (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_LP_PERSIST_EN_OFFSET      0x1D
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_LP_PERSIST_EN_MASK        (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_LP_BYPASS_EN_OFFSET       0x1E
    #define MSSIO_BANK2_IO_CFG_20_21_CR_RPC_IO_CFG_21_LP_BYPASS_EN_MASK         (0x01 << 0x1E)

/*IO electrical configuration for MSSIO pad*/
#define MSSIO_BANK2_IO_CFG_22_23_CR_OFFSET                       0x280
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_IBUFMD_0_OFFSET           0x0
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_IBUFMD_0_MASK             (0x01 << 0x0)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_IBUFMD_1_OFFSET           0x1
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_IBUFMD_1_MASK             (0x01 << 0x1)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_IBUFMD_2_OFFSET           0x2
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_IBUFMD_2_MASK             (0x01 << 0x2)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_DRV_0_OFFSET              0x3
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_DRV_0_MASK                (0x01 << 0x3)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_DRV_1_OFFSET              0x4
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_DRV_1_MASK                (0x01 << 0x4)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_DRV_2_OFFSET              0x5
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_DRV_2_MASK                (0x01 << 0x5)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_DRV_3_OFFSET              0x6
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_DRV_3_MASK                (0x01 << 0x6)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_CLAMP_OFFSET              0x7
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_CLAMP_MASK                (0x01 << 0x7)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_ENHYST_OFFSET             0x8
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_ENHYST_MASK               (0x01 << 0x8)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_LOCKDN_EN_OFFSET          0x9
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_LOCKDN_EN_MASK            (0x01 << 0x9)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_WPD_OFFSET                0xA
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_WPD_MASK                  (0x01 << 0xA)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_WPU_OFFSET                0xB
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_WPU_MASK                  (0x01 << 0xB)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_ATP_EN_OFFSET             0xC
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_ATP_EN_MASK               (0x01 << 0xC)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_LP_PERSIST_EN_OFFSET      0xD
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_LP_PERSIST_EN_MASK        (0x01 << 0xD)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_LP_BYPASS_EN_OFFSET       0xE
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_22_LP_BYPASS_EN_MASK         (0x01 << 0xE)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_IBUFMD_0_OFFSET           0x10
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_IBUFMD_0_MASK             (0x01 << 0x10)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_IBUFMD_1_OFFSET           0x11
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_IBUFMD_1_MASK             (0x01 << 0x11)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_IBUFMD_2_OFFSET           0x12
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_IBUFMD_2_MASK             (0x01 << 0x12)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_DRV_0_OFFSET              0x13
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_DRV_0_MASK                (0x01 << 0x13)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_DRV_1_OFFSET              0x14
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_DRV_1_MASK                (0x01 << 0x14)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_DRV_2_OFFSET              0x15
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_DRV_2_MASK                (0x01 << 0x15)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_DRV_3_OFFSET              0x16
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_DRV_3_MASK                (0x01 << 0x16)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_CLAMP_OFFSET              0x17
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_CLAMP_MASK                (0x01 << 0x17)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_ENHYST_OFFSET             0x18
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_ENHYST_MASK               (0x01 << 0x18)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_LOCKDN_EN_OFFSET          0x19
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_LOCKDN_EN_MASK            (0x01 << 0x19)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_WPD_OFFSET                0x1A
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_WPD_MASK                  (0x01 << 0x1A)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_WPU_OFFSET                0x1B
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_WPU_MASK                  (0x01 << 0x1B)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_ATP_EN_OFFSET             0x1C
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_ATP_EN_MASK               (0x01 << 0x1C)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_LP_PERSIST_EN_OFFSET      0x1D
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_LP_PERSIST_EN_MASK        (0x01 << 0x1D)
    /* */
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_LP_BYPASS_EN_OFFSET       0x1E
    #define MSSIO_BANK2_IO_CFG_22_23_CR_RPC_IO_CFG_23_LP_BYPASS_EN_MASK         (0x01 << 0x1E)

/*Sets H2F [31:0] Spares out signals*/
#define MSS_SPARE0_CR_OFFSET                                     0x2A8
    /* See MSS MAS specification for full description*/
    #define MSS_SPARE0_CR_DATA_OFFSET                            0x0
    #define MSS_SPARE0_CR_DATA_MASK                              (0xFFFFFFFF << 0x0)

/*Sets H2F [37:32] Spares out signals*/
#define MSS_SPARE1_CR_OFFSET                                     0x2AC
    /* See MSS MAS specification for full description*/
    #define MSS_SPARE1_CR_DATA_OFFSET                            0x0
    #define MSS_SPARE1_CR_DATA_MASK                              (0x3F << 0x0)

/*Read H2F [31:0] Spares out signals*/
#define MSS_SPARE0_SR_OFFSET                                     0x2B0
    /* See MSS MAS specification for full description*/
    #define MSS_SPARE0_SR_DATA_OFFSET                            0x0
    #define MSS_SPARE0_SR_DATA_MASK                              (0xFFFFFFFF << 0x0)

/*Read H2F [37:32] Spares out signals*/
#define MSS_SPARE1_SR_OFFSET                                     0x2B4
    /* See MSS MAS specification for full description*/
    #define MSS_SPARE1_SR_DATA_OFFSET                            0x0
    #define MSS_SPARE1_SR_DATA_MASK                              (0x3F << 0x0)

/*Read F2H [31:0] Spares in1 signals*/
#define MSS_SPARE2_SR_OFFSET                                     0x2B8
    /* See MSS MAS specification for full description*/
    #define MSS_SPARE2_SR_DATA_OFFSET                            0x0
    #define MSS_SPARE2_SR_DATA_MASK                              (0xFFFFFFFF << 0x0)

/*Read F2H [37:32] Spares in1 signals*/
#define MSS_SPARE3_SR_OFFSET                                     0x2BC
    /* See MSS MAS specification for full description*/
    #define MSS_SPARE3_SR_DATA_OFFSET                            0x0
    #define MSS_SPARE3_SR_DATA_MASK                              (0x3F << 0x0)

/*Read F2H [31:0] Spares in2 signals*/
#define MSS_SPARE4_SR_OFFSET                                     0x2C0
    /* See MSS MAS specification for full description*/
    #define MSS_SPARE4_SR_DATA_OFFSET                            0x0
    #define MSS_SPARE4_SR_DATA_MASK                              (0xFFFFFFFF << 0x0)

/*Read F2H [37:32] Spares in2 signals*/
#define MSS_SPARE5_SR_OFFSET                                     0x2C4
    /* See MSS MAS specification for full description*/
    #define MSS_SPARE5_SR_DATA_OFFSET                            0x0
    #define MSS_SPARE5_SR_DATA_MASK                              (0x3F << 0x0)

/*Register for ECO usage*/
#define SPARE_REGISTER_RW_OFFSET                                 0x2D0
    /* No function provided for future ECO use*/
    #define SPARE_REGISTER_RW_DATA_OFFSET                        0x0
    #define SPARE_REGISTER_RW_DATA_MASK                          (0xFF << 0x0)

/*Register for ECO usage*/
#define SPARE_REGISTER_W1P_OFFSET                                0x2D4
    /* No function provided for future ECO use*/
    #define SPARE_REGISTER_W1P_DATA_OFFSET                       0x0
    #define SPARE_REGISTER_W1P_DATA_MASK                         (0xFF << 0x0)

/*Register for ECO usage*/
#define SPARE_REGISTER_RO_OFFSET                                 0x2D8
    /* Provides read-back of { W1P RW } registers. No function provided for
     future ECO use.*/
    #define SPARE_REGISTER_RO_DATA_OFFSET                        0x0
    #define SPARE_REGISTER_RO_DATA_MASK                          (0xFFFF << 0x0)

/*Spare signal back to G5C*/
#define SPARE_PERIM_RW_OFFSET                                    0x2DC
    /* Allows the MSS to control the perim_spare_out bits [2] & [6]. No fun
    ction provided for future ECO use.*/
    #define SPARE_PERIM_RW_DATA_OFFSET                           0x0
    #define SPARE_PERIM_RW_DATA_MASK                             (0x03 << 0x0)

/*Unused FIC resets*/
#define SPARE_FIC_OFFSET                                         0x2E0
    /* Connected to spare FIC 0-3 Reset inputs to provide simple RO bits. N
    o defined use*/
    #define SPARE_FIC_RESET_OFFSET                               0x0
    #define SPARE_FIC_RESET_MASK                                 (0x0F << 0x0)
/**************************************************************************
    *******
********************TOP LEVEL REGISTER STRUCTURE***************************
    *******
***************************************************************************
    *******/

typedef struct _mss_sysreg
{
    /*Register for software use*/
    __IO uint32_t TEMP0;

    /*Register for software use*/
     __IO uint32_t TEMP1;

    /*Master clock configuration*/
     __IO uint32_t CLOCK_CONFIG_CR;

    /*RTC clock divider*/
     __IO uint32_t RTC_CLOCK_CR;

    /*Fabric Reset mask*/
     __IO uint32_t FABRIC_RESET_CR;

    /**/
     __IO uint32_t BOOT_FAIL_CR;

    /* Allows the CPU to fully reset the MSS.
       When written to 16'hDEAD will cause a full MSS reset. The Reset wil clear
       this register. The register may be writtent to any value but only a value
       off 16'hDEAD will cause the reset to happen */
     __IO uint32_t MSS_RESET_CR;

    /*Configuration lock*/
     __IO uint32_t CONFIG_LOCK_CR;

    /*Indicates which reset caused the last reset. After a reset occurs reg
    ister should be read and then zero written to allow the next reset event to
     be correctly captured.*/
     __IO uint32_t RESET_SR;

    /*Indicates the device status in particular the state of the FPGA fabri
    c and the MSS IO banks*/
     __IO uint32_t DEVICE_STATUS ;

    /*MSS Build Info*/
     __I uint32_t MSS_BUILD;

    /* Padding reserved 32-bit registers.*/
     __I uint32_t RESERVEDREG32B_1;
     __I uint32_t RESERVEDREG32B_2;
     __I uint32_t RESERVEDREG32B_3;
     __I uint32_t RESERVEDREG32B_4;
     __I uint32_t RESERVEDREG32B_5;

    /*U54-1 Fabric interrupt enable*/
     __IO uint32_t FAB_INTEN_U54_1;

    /*U54-2 Fabric interrupt enable*/
     __IO uint32_t FAB_INTEN_U54_2;

    /*U54-3 Fabric interrupt enable*/
     __IO uint32_t FAB_INTEN_U54_3;

    /*U54-4 Fabric interrupt enable*/
     __IO uint32_t FAB_INTEN_U54_4;

    /*Allows the Ethernet interrupts to be directly routed to the U54 CPUS.
    */
     __IO uint32_t FAB_INTEN_MISC;
    /* Enables the Ethernet MAC0 to interrupt U54_1 directly  */
    #define FAB_INTEN_MAC0_U54_1_EN_OFFSET      0x01U
    /* Enables the Ethernet MAC0 to interrupt U54_2 directly  */
    #define FAB_INTEN_MAC0_U54_2_EN_OFFSET      0x02U
    /* Enables the Ethernet MAC1 to interrupt U54_3 directly  */
    #define FAB_INTEN_MAC1_U54_3_EN_OFFSET      0x03U
    /* Enables the Ethernet MAC1 to interrupt U54_4 directly  */
    #define FAB_INTEN_MAC1_U54_4_EN_OFFSET      0x04U
    #define FAB_INTEN_MAC0_U54_1_EN_MASK        0x01U
    #define FAB_INTEN_MAC0_U54_2_EN_MASK        0x02U
    #define FAB_INTEN_MAC1_U54_3_EN_MASK        0x04U
    #define FAB_INTEN_MAC1_U54_4_EN_MASK        0x08U

    /*Switches GPIO interrupt from PAD to Fabric GPIO*/
     __IO uint32_t GPIO_INTERRUPT_FAB_CR;

    /* Padding reserved 32-bit registers.*/
     __I uint32_t RESERVEDREG32B_6;
     __I uint32_t RESERVEDREG32B_7;
     __I uint32_t RESERVEDREG32B_8;
     __I uint32_t RESERVEDREG32B_9;
     __I uint32_t RESERVEDREG32B_10;
     __I uint32_t RESERVEDREG32B_11;
     __I uint32_t RESERVEDREG32B_12;
     __I uint32_t RESERVEDREG32B_13;
     __I uint32_t RESERVEDREG32B_14;
     __I uint32_t RESERVEDREG32B_15;

    /*"AMP Mode peripheral mapping register. When the register bit is '0' t
    he peripheral is mapped into the 0x2000000 address range using AXI bus 5 fr
    om the Coreplex. When the register bit is '1' the peripheral is mapped into
     the 0x28000000 address range using AXI bus 6 from the Coreplex."*/
     __IO uint32_t APBBUS_CR;

    /*"Enables the clock to the MSS peripheral. By turning clocks off dynam
    ic power can be saved. When the clock is off the peripheral  should not be
    accessed*/
     __IO uint32_t SUBBLK_CLOCK_CR;

    /*"Holds the MSS peripherals in reset. When in reset the peripheral sho
    uld not be accessed*/
     __IO uint32_t SOFT_RESET_CR;

    /*Configures how many outstanding transfers the AXI-AHB bridges in fron
    t off the USB and Crypto blocks should allow. (See Synopsys AXI-AHB bridge
    documentation)*/
     __IO uint32_t AHBAXI_CR;

    /*Configures the two AHB-APB bridges on S5 and S6*/
     __IO uint32_t AHBAPB_CR;

    /* Padding reserved 32-bit registers.*/
     uint32_t reservedReg32b_16;

    /*MSS Corner APB interface controls*/
     __IO uint32_t DFIAPB_CR;

    /*GPIO Blocks reset control*/
     __IO uint32_t GPIO_CR;

    /* Padding reserved 32-bit registers.*/
     uint32_t reservedReg32b_17;

    /*MAC0 configuration register*/
     __IO uint32_t MAC0_CR;

    /*MAC1 configuration register*/
     __IO uint32_t MAC1_CR;

    /*USB Configuration register*/
     __IO uint32_t USB_CR;

    /*Crypto Mesh control and status register*/
     __IO uint32_t MESH_CR;

    /*Crypto mesh seed and update rate*/
     __IO uint32_t MESH_SEED_CR;

    /*ENVM AHB Controller setup*/
     __IO uint32_t ENVM_CR;

    /*Reserved*/
     __I uint32_t RESERVED_BC;

    /*QOS Athena USB & MMC Configuration*/
     __IO uint32_t QOS_PERIPHERAL_CR;

    /*QOS Configuration Coreplex*/
     __IO uint32_t QOS_CPLEXIO_CR;

    /*QOS configuration DDRC*/
     __IO uint32_t QOS_CPLEXDDR_CR;

    /* Padding reserved 32-bit registers.*/
     __I uint32_t RESERVEDREG32B_18;
     __I uint32_t RESERVEDREG32B_19;
     __I uint32_t RESERVEDREG32B_20;
     __I uint32_t RESERVEDREG32B_21;
     __I uint32_t RESERVEDREG32B_22;
     __I uint32_t RESERVEDREG32B_23;
     __I uint32_t RESERVEDREG32B_24;
     __I uint32_t RESERVEDREG32B_25;
     __I uint32_t RESERVEDREG32B_26;

    /*Indicates that a master caused a MPU violation. Interrupts via mainte
    nance interrupt.*/
     __IO uint32_t MPU_VIOLATION_SR;

    /*Enables interrupts on MPU violations*/
     __IO uint32_t MPU_VIOLATION_INTEN_CR;

    /*AXI switch decode fail*/
     __IO uint32_t SW_FAIL_ADDR0_CR;

    /*AXI switch decode fail*/
     __IO uint32_t SW_FAIL_ADDR1_CR;

    /*Set when an ECC event happens*/
     __IO uint32_t EDAC_SR;

    /*Enables ECC interrupt on event*/
     __IO uint32_t EDAC_INTEN_CR;

    /*Count off single bit errors*/
     __IO uint32_t EDAC_CNT_MMC;

    /*Count off single bit errors*/
     __IO uint32_t EDAC_CNT_DDRC;

    /*Count off single bit errors*/
     __IO uint32_t EDAC_CNT_MAC0;

    /*Count off single bit errors*/
     __IO uint32_t EDAC_CNT_MAC1;

    /*Count off single bit errors*/
     __IO uint32_t EDAC_CNT_USB;

    /*Count off single bit errors*/
     __IO uint32_t EDAC_CNT_CAN0;

    /*Count off single bit errors*/
     __IO uint32_t EDAC_CNT_CAN1;

    /*"Will Corrupt write data to rams 1E corrupts bit 0 2E bits 1 and 2.In
    jects Errors into all RAMS in the block as long as the bits are set. Settin
    g 1E and 2E will inject a 3-bit error"*/
     __IO uint32_t EDAC_INJECT_CR;

    /* Padding reserved 32-bit registers.*/
     __I uint32_t RESERVEDREG32B_27;
     __I uint32_t RESERVEDREG32B_28;
     __I uint32_t RESERVEDREG32B_29;
     __I uint32_t RESERVEDREG32B_30;
     __I uint32_t RESERVEDREG32B_31;
     __I uint32_t RESERVEDREG32B_32;

    /*Maintenance Interrupt Enable.*/
     __IO uint32_t MAINTENANCE_INTEN_CR;

    /*PLL Status interrupt enables*/
     __IO uint32_t PLL_STATUS_INTEN_CR;

    /*Maintenance interrupt indicates fault and status events.*/
     __IO uint32_t MAINTENANCE_INT_SR;

    /*PLL interrupt register*/
     __IO uint32_t PLL_STATUS_SR;

    /*Enable to CFM Timer */
     __IO uint32_t CFM_TIMER_CR;

    /*Miscellaneous Register*/
     uint32_t MISC_SR;

    /*DLL Interrupt enables*/
     __IO uint32_t DLL_STATUS_CR;

    /*DLL interrupt register*/
     __IO uint32_t DLL_STATUS_SR;

    /* Padding reserved 32-bit registers.*/
     __I uint32_t RESERVEDREG32B_33;
     __I uint32_t RESERVEDREG32B_34;

    /*Puts all the RAMS in that block into low leakage mode. RAM contents a
    nd Q value preserved.*/
     __IO uint32_t RAM_LIGHTSLEEP_CR;

    /*Puts all the RAMS in that block into deep sleep mode. RAM contents pr
    eserved. Powers down the periphery circuits.*/
     __IO uint32_t RAM_DEEPSLEEP_CR;

    /*Puts all the RAMS in that block into shut down mode. RAM contents not
     preserved.  Powers down the RAM and periphery circuits.*/
     __IO uint32_t RAM_SHUTDOWN_CR;

    /*Allows each bank of the L2 Cache to be powered down ORed with global
    shutdown */
     __IO uint32_t L2_SHUTDOWN_CR;

    /* Padding reserved 32-bit registers.*/
     __I uint32_t RESERVEDREG32B_35;
     __I uint32_t RESERVEDREG32B_36;
     __I uint32_t RESERVEDREG32B_37;
     __I uint32_t RESERVEDREG32B_38;
     __I uint32_t RESERVEDREG32B_39;
     __I uint32_t RESERVEDREG32B_40;
     __I uint32_t RESERVEDREG32B_41;
     __I uint32_t RESERVEDREG32B_42;
     __I uint32_t RESERVEDREG32B_43;
     __I uint32_t RESERVEDREG32B_44;
     __I uint32_t RESERVEDREG32B_45;
     __I uint32_t RESERVEDREG32B_46;
     __I uint32_t RESERVEDREG32B_47;
     __I uint32_t RESERVEDREG32B_48;
     __I uint32_t RESERVEDREG32B_49;
     __I uint32_t RESERVEDREG32B_50;
     __I uint32_t RESERVEDREG32B_51;
     __I uint32_t RESERVEDREG32B_52;
     __I uint32_t RESERVEDREG32B_53;
     __I uint32_t RESERVEDREG32B_54;
     __I uint32_t RESERVEDREG32B_55;
     __I uint32_t RESERVEDREG32B_56;
     __I uint32_t RESERVEDREG32B_57;
     __I uint32_t RESERVEDREG32B_58;
     __I uint32_t RESERVEDREG32B_59;
     __I uint32_t RESERVEDREG32B_60;
     __I uint32_t RESERVEDREG32B_61;
     __I uint32_t RESERVEDREG32B_62;
     __I uint32_t RESERVEDREG32B_63;
     __I uint32_t RESERVEDREG32B_64;
     __I uint32_t RESERVEDREG32B_65;
     __I uint32_t RESERVEDREG32B_66;
     __I uint32_t RESERVEDREG32B_67;
     __I uint32_t RESERVEDREG32B_68;

    /*Selects whether the peripheral is connected to the Fabric or IOMUX st
    ructure.*/
     __IO uint32_t IOMUX0_CR;

    /*Configures the IO Mux structure for each IO pad. See the MSS MAS spec
    ification for for description.*/
     __IO uint32_t IOMUX1_CR;

    /*Configures the IO Mux structure for each IO pad. See the MSS MAS spec
    ification for for description.*/
     __IO uint32_t IOMUX2_CR;

    /*Configures the IO Mux structure for each IO pad. See the MSS MAS spec
    ification for for description.*/
     __IO uint32_t IOMUX3_CR;

    /*Configures the IO Mux structure for each IO pad. See the MSS MAS spec
    ification for for description.*/
     __IO uint32_t IOMUX4_CR;

    /*Configures the IO Mux structure for each IO pad. See the MSS MAS spec
    ification for for description.*/
     __IO uint32_t IOMUX5_CR;

    /*Sets whether the MMC/SD Voltage select lines are inverted on entry to
     the IOMUX structure*/
     __IO uint32_t IOMUX6_CR;

    /* Padding reserved 32-bit registers.*/
     __I uint32_t RESERVEDREG32B_69;
     __I uint32_t RESERVEDREG32B_70;
     __I uint32_t RESERVEDREG32B_71;
     __I uint32_t RESERVEDREG32B_72;
     __I uint32_t RESERVEDREG32B_73;

    /*Configures the MSSIO block*/
     __IO uint32_t MSSIO_BANK4_CFG_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK4_IO_CFG_0_1_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK4_IO_CFG_2_3_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK4_IO_CFG_4_5_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK4_IO_CFG_6_7_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK4_IO_CFG_8_9_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK4_IO_CFG_10_11_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK4_IO_CFG_12_13_CR;

    /*Configures the MSSIO block*/
     __IO uint32_t MSSIO_BANK2_CFG_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK2_IO_CFG_0_1_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK2_IO_CFG_2_3_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK2_IO_CFG_4_5_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK2_IO_CFG_6_7_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK2_IO_CFG_8_9_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK2_IO_CFG_10_11_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK2_IO_CFG_12_13_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK2_IO_CFG_14_15_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK2_IO_CFG_16_17_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK2_IO_CFG_18_19_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK2_IO_CFG_20_21_CR;

    /*IO electrical configuration for MSSIO pad*/
     __IO uint32_t MSSIO_BANK2_IO_CFG_22_23_CR;

    /* Padding reserved 32-bit registers.*/
     __I uint32_t RESERVEDREG32B_74;
     __I uint32_t RESERVEDREG32B_75;
     __I uint32_t RESERVEDREG32B_76;
     __I uint32_t RESERVEDREG32B_77;
     __I uint32_t RESERVEDREG32B_78;
     __I uint32_t RESERVEDREG32B_79;
     __I uint32_t RESERVEDREG32B_80;
     __I uint32_t RESERVEDREG32B_81;
     __I uint32_t RESERVEDREG32B_82;

    /*Sets H2F [31:0] Spares out signals*/
     __IO uint32_t MSS_SPARE0_CR;

    /*Sets H2F [37:32] Spares out signals*/
     __IO uint32_t MSS_SPARE1_CR;

    /*Read H2F [31:0] Spares out signals*/
     __IO uint32_t MSS_SPARE0_SR;

    /*Read H2F [37:32] Spares out signals*/
     __IO uint32_t MSS_SPARE1_SR;

    /*Read F2H [31:0] Spares in1 signals*/
     __IO uint32_t MSS_SPARE2_SR;

    /*Read F2H [37:32] Spares in1 signals*/
     __IO uint32_t MSS_SPARE3_SR;

    /*Read F2H [31:0] Spares in2 signals*/
     __IO uint32_t MSS_SPARE4_SR;

    /*Read F2H [37:32] Spares in2 signals*/
     __IO uint32_t MSS_SPARE5_SR;

    /* Padding reserved 32-bit registers.*/
     __I uint32_t RESERVEDREG32B_83;
     __I uint32_t RESERVEDREG32B_84;

    /*Register for ECO usage*/
     __IO uint32_t SPARE_REGISTER_RW;

    /*Register for ECO usage*/
     __IO uint32_t SPARE_REGISTER_W1P;

    /*Register for ECO usage*/
     __I uint32_t SPARE_REGISTER_RO;

    /*Spare signal back to G5C*/
     __IO uint32_t SPARE_PERIM_RW;

    /*Unused FIC resets*/
     __I uint32_t SPARE_FIC;
} mss_sysreg_t;

#define SYSREG_ATHENACR_RESET       (1U << 0U)
#define SYSREG_ATHENACR_PURGE       (1U << 1U)
#define SYSREG_ATHENACR_GO          (1U << 2U)
#define SYSREG_ATHENACR_RINGOSCON   (1U << 3U)
#define SYSREG_ATHENACR_COMPLETE    (1U << 8U)
#define SYSREG_ATHENACR_ALARM       (1U << 9U)
#define SYSREG_ATHENACR_BUSERROR    (1U << 10U)
#define SYSREG_SOFTRESET_ENVM       (1U << 0U)
#define SYSREG_SOFTRESET_TIMER      (1U << 4U)
#define SYSREG_SOFTRESET_MMUART0    (1U << 5U)
#define SYSREG_SOFTRESET_DDRC       (1U << 23U)
#define SYSREG_SOFTRESET_FIC3       (1U << 27U)
#define SYSREG_SOFTRESET_ATHENA     (1U << 28U)

#define SYSREG   ((volatile mss_sysreg_t * const) BASE32_ADDR_MSS_SYSREG)

#ifdef __cplusplus
}
#endif

#endif /*MSS_SYSREG_H*/
