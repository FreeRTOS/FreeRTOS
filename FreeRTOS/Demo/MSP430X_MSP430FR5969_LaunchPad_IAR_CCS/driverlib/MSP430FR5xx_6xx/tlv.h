/* --COPYRIGHT--,BSD
 * Copyright (c) 2014, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * --/COPYRIGHT--*/
//*****************************************************************************
//
// tlv.h - Driver for the TLV Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_TLV_H__
#define __MSP430WARE_TLV_H__

#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_TLV__

//*****************************************************************************
//
// If building with a C++ compiler, make all of the definitions in this header
// have a C binding.
//
//*****************************************************************************
#ifdef __cplusplus
extern "C"
{
#endif

#include "inc/hw_regaccess.h"
//******************************************************************************
//
// TLV Data Types
//
//******************************************************************************
struct s_TLV_Die_Record
{
    uint32_t wafer_id;
    uint16_t die_x_position;
    uint16_t die_y_position;
    uint16_t test_results;
};

struct s_TLV_ADC_Cal_Data
{
    uint16_t adc_gain_factor;
    int16_t adc_offset;
    uint16_t adc_ref15_30_temp;
    uint16_t adc_ref15_85_temp;
    uint16_t adc_ref20_30_temp;
    uint16_t adc_ref20_85_temp;
    uint16_t adc_ref25_30_temp;
    uint16_t adc_ref25_85_temp;
};

struct s_TLV_Timer_D_Cal_Data
{
    uint16_t TDH0CTL1_64;
    uint16_t TDH0CTL1_128;
    uint16_t TDH0CTL1_200;
    uint16_t TDH0CTL1_256;
};

struct s_TLV_REF_Cal_Data
{
    uint16_t ref_ref15;
    uint16_t ref_ref20;
    uint16_t ref_ref25;
};

struct s_Peripheral_Memory_Data
{
    uint16_t memory_1;
    uint16_t memory_2;
    uint16_t memory_3;
    uint16_t memory_4;
};

//*****************************************************************************
//
// The following are values that can be passed to the tag parameter for
// functions: TLV_getInfo().
//
//*****************************************************************************
#define TLV_TAG_LDTAG                                                 TLV_LDTAG
#define TLV_TAG_PDTAG                                                 TLV_PDTAG
#define TLV_TAG_Reserved3                                         TLV_Reserved3
#define TLV_TAG_Reserved4                                         TLV_Reserved4
#define TLV_TAG_BLANK                                                 TLV_BLANK
#define TLV_TAG_Reserved6                                         TLV_Reserved6
#define TLV_TAG_Reserved7                                         TLV_Reserved7
#define TLV_TAG_TAGEND                                               TLV_TAGEND
#define TLV_TAG_TAGEXT                                               TLV_TAGEXT
#define TLV_TAG_TIMER_D_CAL                                       TLV_TIMERDCAL
#define TLV_DEVICE_ID_0                                                  0x1A04
#define TLV_DEVICE_ID_1                                                  0x1A05
#define TLV_TAG_DIERECORD                                         TLV_DIERECORD
#define TLV_TAG_ADCCAL                                               TLV_ADCCAL
#define TLV_TAG_ADC12CAL                                           TLV_ADC12CAL
#define TLV_TAG_ADC10CAL                                           TLV_ADC10CAL
#define TLV_TAG_REFCAL                                               TLV_REFCAL

//*****************************************************************************
//
// The following are values that can be passed to the tag parameter for
// functions: TLV_getPeripheral().
//
//*****************************************************************************
#define TLV_PID_NO_MODULE                                                (0x00)
#define TLV_PID_PORTMAPPING                                              (0x10)
#define TLV_PID_MSP430CPUXV2                                             (0x23)
#define TLV_PID_JTAG                                                     (0x09)
#define TLV_PID_SBW                                                      (0x0F)
#define TLV_PID_EEM_XS                                                   (0x02)
#define TLV_PID_EEM_S                                                    (0x03)
#define TLV_PID_EEM_M                                                    (0x04)
#define TLV_PID_EEM_L                                                    (0x05)
#define TLV_PID_PMM                                                      (0x30)
#define TLV_PID_PMM_FR                                                   (0x32)
#define TLV_PID_FCTL                                                     (0x39)
#define TLV_PID_CRC16                                                    (0x3C)
#define TLV_PID_CRC16_RB                                                 (0x3D)
#define TLV_PID_WDT_A                                                    (0x40)
#define TLV_PID_SFR                                                      (0x41)
#define TLV_PID_SYS                                                      (0x42)
#define TLV_PID_RAMCTL                                                   (0x44)
#define TLV_PID_DMA_1                                                    (0x46)
#define TLV_PID_DMA_3                                                    (0x47)
#define TLV_PID_UCS                                                      (0x48)
#define TLV_PID_DMA_6                                                    (0x4A)
#define TLV_PID_DMA_2                                                    (0x4B)
#define TLV_PID_PORT1_2                                                  (0x51)
#define TLV_PID_PORT3_4                                                  (0x52)
#define TLV_PID_PORT5_6                                                  (0x53)
#define TLV_PID_PORT7_8                                                  (0x54)
#define TLV_PID_PORT9_10                                                 (0x55)
#define TLV_PID_PORT11_12                                                (0x56)
#define TLV_PID_PORTU                                                    (0x5E)
#define TLV_PID_PORTJ                                                    (0x5F)
#define TLV_PID_TA2                                                      (0x60)
#define TLV_PID_TA3                                                      (0x61)
#define TLV_PID_TA5                                                      (0x62)
#define TLV_PID_TA7                                                      (0x63)
#define TLV_PID_TB3                                                      (0x65)
#define TLV_PID_TB5                                                      (0x66)
#define TLV_PID_TB7                                                      (0x67)
#define TLV_PID_RTC                                                      (0x68)
#define TLV_PID_BT_RTC                                                   (0x69)
#define TLV_PID_BBS                                                      (0x6A)
#define TLV_PID_RTC_B                                                    (0x6B)
#define TLV_PID_TD2                                                      (0x6C)
#define TLV_PID_TD3                                                      (0x6D)
#define TLV_PID_TD5                                                      (0x6E)
#define TLV_PID_TD7                                                      (0x6F)
#define TLV_PID_TEC                                                      (0x70)
#define TLV_PID_RTC_C                                                    (0x71)
#define TLV_PID_AES                                                      (0x80)
#define TLV_PID_MPY16                                                    (0x84)
#define TLV_PID_MPY32                                                    (0x85)
#define TLV_PID_MPU                                                      (0x86)
#define TLV_PID_USCI_AB                                                  (0x90)
#define TLV_PID_USCI_A                                                   (0x91)
#define TLV_PID_USCI_B                                                   (0x92)
#define TLV_PID_EUSCI_A                                                  (0x94)
#define TLV_PID_EUSCI_B                                                  (0x95)
#define TLV_PID_REF                                                      (0xA0)
#define TLV_PID_COMP_B                                                   (0xA8)
#define TLV_PID_COMP_D                                                   (0xA9)
#define TLV_PID_USB                                                      (0x98)
#define TLV_PID_LCD_B                                                    (0xB1)
#define TLV_PID_LCD_C                                                    (0xB2)
#define TLV_PID_DAC12_A                                                  (0xC0)
#define TLV_PID_SD16_B_1                                                 (0xC8)
#define TLV_PID_SD16_B_2                                                 (0xC9)
#define TLV_PID_SD16_B_3                                                 (0xCA)
#define TLV_PID_SD16_B_4                                                 (0xCB)
#define TLV_PID_SD16_B_5                                                 (0xCC)
#define TLV_PID_SD16_B_6                                                 (0xCD)
#define TLV_PID_SD16_B_7                                                 (0xCE)
#define TLV_PID_SD16_B_8                                                 (0xCF)
#define TLV_PID_ADC12_A                                                  (0xD1)
#define TLV_PID_ADC10_A                                                  (0xD3)
#define TLV_PID_ADC10_B                                                  (0xD4)
#define TLV_PID_SD16_A                                                   (0xD8)
#define TLV_PID_TI_BSL                                                   (0xFC)

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Gets TLV Info
//!
//! The TLV structure uses a tag or base address to identify segments of the
//! table where information is stored. Some examples of TLV tags are Peripheral
//! Descriptor, Interrupts, Info Block and Die Record. This function retrieves
//! the value of a tag and the length of the tag.
//!
//! \param tag represents the tag for which the information needs to be
//!        retrieved.
//!        Valid values are:
//!        - \b TLV_TAG_LDTAG
//!        - \b TLV_TAG_PDTAG
//!        - \b TLV_TAG_Reserved3
//!        - \b TLV_TAG_Reserved4
//!        - \b TLV_TAG_BLANK
//!        - \b TLV_TAG_Reserved6
//!        - \b TLV_TAG_Reserved7
//!        - \b TLV_TAG_TAGEND
//!        - \b TLV_TAG_TAGEXT
//!        - \b TLV_TAG_TIMER_D_CAL
//!        - \b TLV_DEVICE_ID_0
//!        - \b TLV_DEVICE_ID_1
//!        - \b TLV_TAG_DIERECORD
//!        - \b TLV_TAG_ADCCAL
//!        - \b TLV_TAG_ADC12CAL
//!        - \b TLV_TAG_ADC10CAL
//!        - \b TLV_TAG_REFCAL
//! \param instance In some cases a specific tag may have more than one
//!        instance. For example there may be multiple instances of timer
//!        calibration data present under a single Timer Cal tag. This variable
//!        specifies the instance for which information is to be retrieved (0,
//!        1, etc.). When only one instance exists; 0 is passed.
//! \param length Acts as a return through indirect reference. The function
//!        retrieves the value of the TLV tag length. This value is pointed to
//!        by *length and can be used by the application level once the
//!        function is called. If the specified tag is not found then the
//!        pointer is null 0.
//! \param data_address acts as a return through indirect reference. Once the
//!        function is called data_address points to the pointer that holds the
//!        value retrieved from the specified TLV tag. If the specified tag is
//!        not found then the pointer is null 0.
//!
//! \return None
//
//*****************************************************************************
extern void TLV_getInfo(uint8_t tag,
                        uint8_t instance,
                        uint8_t *length,
                        uint16_t **data_address);

//*****************************************************************************
//
//! \brief Retrieves the unique device ID from the TLV structure.
//!
//!
//! \return The device ID is returned as type uint16_t.
//
//*****************************************************************************
extern uint16_t TLV_getDeviceType(void);

//*****************************************************************************
//
//! \brief Gets memory information
//!
//! The Peripheral Descriptor tag is split into two portions a list of the
//! available flash memory blocks followed by a list of available peripherals.
//! This function is used to parse through the first portion and calculate the
//! total flash memory available in a device. The typical usage is to call the
//! TLV_getMemory which returns a non-zero value until the entire memory list
//! has been parsed. When a zero is returned, it indicates that all the memory
//! blocks have been counted and the next address holds the beginning of the
//! device peripheral list.
//!
//! \param instance In some cases a specific tag may have more than one
//!        instance. This variable specifies the instance for which information
//!        is to be retrieved (0, 1 etc). When only one instance exists; 0 is
//!        passed.
//!
//! \return The returned value is zero if the end of the memory list is
//!         reached.
//
//*****************************************************************************
extern uint16_t TLV_getMemory(uint8_t instance);

//*****************************************************************************
//
//! \brief Gets peripheral information from the TLV
//!
//! he Peripheral Descriptor tag is split into two portions a list of the
//! available flash memory blocks followed by a list of available peripherals.
//! This function is used to parse through the second portion and can be used
//! to check if a specific peripheral is present in a device. The function
//! calls TLV_getPeripheral() recursively until the end of the memory list and
//! consequently the beginning of the peripheral list is reached. <
//!
//! \param tag represents represents the tag for a specific peripheral for
//!        which the information needs to be retrieved. In the header file tlv.
//!        h specific peripheral tags are pre-defined, for example USCIA_B and
//!        TA0 are defined as TLV_PID_USCI_AB and TLV_PID_TA2 respectively.
//!        Valid values are:
//!        - \b TLV_PID_NO_MODULE - No Module
//!        - \b TLV_PID_PORTMAPPING - Port Mapping
//!        - \b TLV_PID_MSP430CPUXV2 - MSP430CPUXV2
//!        - \b TLV_PID_JTAG - JTAG
//!        - \b TLV_PID_SBW - SBW
//!        - \b TLV_PID_EEM_XS - EEM X-Small
//!        - \b TLV_PID_EEM_S - EEM Small
//!        - \b TLV_PID_EEM_M - EEM Medium
//!        - \b TLV_PID_EEM_L - EEM Large
//!        - \b TLV_PID_PMM - PMM
//!        - \b TLV_PID_PMM_FR - PMM FRAM
//!        - \b TLV_PID_FCTL - Flash
//!        - \b TLV_PID_CRC16 - CRC16
//!        - \b TLV_PID_CRC16_RB - CRC16 Reverse
//!        - \b TLV_PID_WDT_A - WDT_A
//!        - \b TLV_PID_SFR - SFR
//!        - \b TLV_PID_SYS - SYS
//!        - \b TLV_PID_RAMCTL - RAMCTL
//!        - \b TLV_PID_DMA_1 - DMA 1
//!        - \b TLV_PID_DMA_3 - DMA 3
//!        - \b TLV_PID_UCS - UCS
//!        - \b TLV_PID_DMA_6 - DMA 6
//!        - \b TLV_PID_DMA_2 - DMA 2
//!        - \b TLV_PID_PORT1_2 - Port 1 + 2 / A
//!        - \b TLV_PID_PORT3_4 - Port 3 + 4 / B
//!        - \b TLV_PID_PORT5_6 - Port 5 + 6 / C
//!        - \b TLV_PID_PORT7_8 - Port 7 + 8 / D
//!        - \b TLV_PID_PORT9_10 - Port 9 + 10 / E
//!        - \b TLV_PID_PORT11_12 - Port 11 + 12 / F
//!        - \b TLV_PID_PORTU - Port U
//!        - \b TLV_PID_PORTJ - Port J
//!        - \b TLV_PID_TA2 - Timer A2
//!        - \b TLV_PID_TA3 - Timer A1
//!        - \b TLV_PID_TA5 - Timer A5
//!        - \b TLV_PID_TA7 - Timer A7
//!        - \b TLV_PID_TB3 - Timer B3
//!        - \b TLV_PID_TB5 - Timer B5
//!        - \b TLV_PID_TB7 - Timer B7
//!        - \b TLV_PID_RTC - RTC
//!        - \b TLV_PID_BT_RTC - BT + RTC
//!        - \b TLV_PID_BBS - Battery Backup Switch
//!        - \b TLV_PID_RTC_B - RTC_B
//!        - \b TLV_PID_TD2 - Timer D2
//!        - \b TLV_PID_TD3 - Timer D1
//!        - \b TLV_PID_TD5 - Timer D5
//!        - \b TLV_PID_TD7 - Timer D7
//!        - \b TLV_PID_TEC - Timer Event Control
//!        - \b TLV_PID_RTC_C - RTC_C
//!        - \b TLV_PID_AES - AES
//!        - \b TLV_PID_MPY16 - MPY16
//!        - \b TLV_PID_MPY32 - MPY32
//!        - \b TLV_PID_MPU - MPU
//!        - \b TLV_PID_USCI_AB - USCI_AB
//!        - \b TLV_PID_USCI_A - USCI_A
//!        - \b TLV_PID_USCI_B - USCI_B
//!        - \b TLV_PID_EUSCI_A - eUSCI_A
//!        - \b TLV_PID_EUSCI_B - eUSCI_B
//!        - \b TLV_PID_REF - Shared Reference
//!        - \b TLV_PID_COMP_B - COMP_B
//!        - \b TLV_PID_COMP_D - COMP_D
//!        - \b TLV_PID_USB - USB
//!        - \b TLV_PID_LCD_B - LCD_B
//!        - \b TLV_PID_LCD_C - LCD_C
//!        - \b TLV_PID_DAC12_A - DAC12_A
//!        - \b TLV_PID_SD16_B_1 - SD16_B 1 Channel
//!        - \b TLV_PID_SD16_B_2 - SD16_B 2 Channel
//!        - \b TLV_PID_SD16_B_3 - SD16_B 3 Channel
//!        - \b TLV_PID_SD16_B_4 - SD16_B 4 Channel
//!        - \b TLV_PID_SD16_B_5 - SD16_B 5 Channel
//!        - \b TLV_PID_SD16_B_6 - SD16_B 6 Channel
//!        - \b TLV_PID_SD16_B_7 - SD16_B 7 Channel
//!        - \b TLV_PID_SD16_B_8 - SD16_B 8 Channel
//!        - \b TLV_PID_ADC12_A - ADC12_A
//!        - \b TLV_PID_ADC10_A - ADC10_A
//!        - \b TLV_PID_ADC10_B - ADC10_B
//!        - \b TLV_PID_SD16_A - SD16_A
//!        - \b TLV_PID_TI_BSL - BSL
//! \param instance In some cases a specific tag may have more than one
//!        instance. For example a device may have more than a single USCI
//!        module, each of which is defined by an instance number 0, 1, 2, etc.
//!        When only one instance exists; 0 is passed.
//!
//! \return The returned value is zero if the specified tag value (peripheral)
//!         is not available in the device.
//
//*****************************************************************************
extern uint16_t TLV_getPeripheral(uint8_t tag,
                                  uint8_t instance);

//*****************************************************************************
//
//! \brief Get interrupt information from the TLV
//!
//! This function is used to retrieve information on available interrupt
//! vectors. It allows the user to check if a specific interrupt vector is
//! defined in a given device.
//!
//! \param tag represents the tag for the interrupt vector. Interrupt vector
//!        tags number from 0 to N depending on the number of available
//!        interrupts. Refer to the device datasheet for a list of available
//!        interrupts.
//!
//! \return The returned value is zero is the specified interrupt vector is not
//!         defined.
//
//*****************************************************************************
extern uint8_t TLV_getInterrupt(uint8_t tag);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_TLV_H__
