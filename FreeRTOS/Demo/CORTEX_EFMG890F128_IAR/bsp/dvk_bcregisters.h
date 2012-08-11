/**************************************************************************//**
 * @file
 * @brief Board Control register definitions
 * @author Energy Micro AS
 * @version 1.0.1
 ******************************************************************************
 * @section License
 * <b>(C) Copyright 2009 Energy Micro AS, http://www.energymicro.com</b>
 ******************************************************************************
 *
 * This source code is the property of Energy Micro AS. The source and compiled
 * code may only be used on Energy Micro "EFM32" microcontrollers.
 *
 * This copyright notice may not be removed from the source code nor changed.
 *
 * DISCLAIMER OF WARRANTY/LIMITATION OF REMEDIES: Energy Micro AS has no
 * obligation to support this Software. Energy Micro AS is providing the
 * Software "AS IS", with no express or implied warranties of any kind,
 * including, but not limited to, any implied warranties of merchantability
 * or fitness for any particular purpose or warranties against infringement
 * of any proprietary rights of a third party.
 *
 * Energy Micro AS will not be liable for any consequential, incidental, or
 * special damages, or any other relief, or for any claim by any third party,
 * arising from your use of this Software.
 *
 *****************************************************************************/

#ifndef __DVK_BCREGISTERS_H
#define __DVK_BCREGISTERS_H

#include <stdint.h>

/**************************************************************************//**
 * Defines FPGA register bank for Energy Micro Development Kit (DVK) board,
 * i.e. board control registers
 *****************************************************************************/
#define BC_REGISTER_BASE             0x8c000000

#define BC_CFG                       ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x00))
#define BC_EM                        ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x01))
#define BC_MAGIC                     ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x02))
#define BC_LED                       ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x03))
#define BC_PUSHBUTTON                ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x04))
#define BC_DIPSWITCH                 ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x05))
#define BC_JOYSTICK                  ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x06))
#define BC_AEM                       ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x07))
#define BC_DISPLAY_CTRL              ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x08))
#define BC_EBI_CFG                   ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x09))
#define BC_BUS_CFG                   ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x0a))
#define BC_PERCTRL                   ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x0c))
#define BC_AEMSTATE                  ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x0d))
#define BC_SPI_CFG                   ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x0e))
#define BC_RESET                     ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x0f))
#define BC_ADC_START                 ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x10))
#define BC_ADC_STATUS                ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x11))
#define BC_ADC_DATA                  ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x12))
#define BC_HW_VERSION                ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x14))
#define BC_FW_BUILDNO                ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x15))
#define BC_FW_VERSION                ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x16))
#define BC_SCRATCH_COMMON            ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x17))
#define BC_SCRATCH_EFM0              ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x18))
#define BC_SCRATCH_EFM1              ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x19))
#define BC_SCRATCH_EFM2              ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x1A))
#define BC_SCRATCH_EFM3              ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x1B))
#define BC_SCRATCH_BC0               ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x1C))
#define BC_SCRATCH_BC1               ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x1D))
#define BC_SCRATCH_BC2               ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x1E))
#define BC_SCRATCH_BC3               ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x1f))
#define BC_INTFLAG                   ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x20))
#define BC_INTEN                     ((volatile uint16_t *)(BC_REGISTER_BASE + sizeof(uint16_t) * 0x21))

/**************************************************************************//**
 * Defines bit fields for board control registers
 *****************************************************************************/
#define BC_PERCTRL_ACCEL             (1 << 0)
#define BC_PERCTRL_AMBIENT           (1 << 1)
#define BC_PERCTRL_POTMETER          (1 << 2)
#define BC_PERCTRL_RS232A            (1 << 3)
#define BC_PERCTRL_RS232B            (1 << 4)
#define BC_PERCTRL_SPI               (1 << 5)
#define BC_PERCTRL_I2C               (1 << 6)
#define BC_PERCTRL_IRDA              (1 << 7)
#define BC_PERCTRL_ANALOG_SE         (1 << 8)
#define BC_PERCTRL_ANALOG_DIFF       (1 << 9)
#define BC_PERCTRL_AUDIO_OUT         (1 << 10)
#define BC_PERCTRL_AUDIO_IN          (1 << 11)
#define BC_PERCTRL_ACCEL_GSEL        (1 << 12)
#define BC_PERCTRL_ACCEL_SELFTEST    (1 << 13)
#define BC_PERCTRL_RS232_SHUTDOWN    (1 << 14)
#define BC_PERCTRL_IRDA_SHUTDOWN     (1 << 15)

#define BC_INTEN_PB                  (1 << 0)
#define BC_INTEN_DIP                 (1 << 1)
#define BC_INTEN_JOYSTICK            (1 << 2)
#define BC_INTEN_AEM                 (1 << 3)

#define BC_CFG_SPI                   (0)
#define BC_CFG_EBI                   (1)

#define BC_MAGIC_VALUE               (0xef32)

#endif
