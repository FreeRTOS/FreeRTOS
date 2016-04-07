/*******************************************************************************
* © 2013 Microchip Technology Inc. and its subsidiaries.
* You may use this software and any derivatives exclusively with
* Microchip products.
* THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS".
* NO WARRANTIES, WHETHER EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE,
* INCLUDING ANY IMPLIED WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY,
* AND FITNESS FOR A PARTICULAR PURPOSE, OR ITS INTERACTION WITH MICROCHIP
* PRODUCTS, COMBINATION WITH ANY OTHER PRODUCTS, OR USE IN ANY APPLICATION.
* IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
* INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
* WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
* BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE.
* TO THE FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL
* CLAIMS IN ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF
* FEES, IF ANY, THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
* MICROCHIP PROVIDES THIS SOFTWARE CONDITIONALLY UPON YOUR ACCEPTANCE
* OF THESE TERMS.
********************************************************************************

Version Control Information (Perforce)
$File: //depot_pcs/FWEng/Release/projects/CEC1302_CLIB/release2/Source/hw_blks/common/include/MEC1322.h $
********************************************************************************
$Revision: #1 $
$DateTime: 2015/12/23 15:37:58 $
$Author: akrishnan $
 Change Description:  Initial revision for MEC1322
******************************************************************************/
/** @file smscmmcr.h
*  brief the mmcr definitions
* 
******************************************************************************/
#ifndef SMSCMMCR_H_
#define SMSCMMCR_H_

//NOTE: Please Don't edit this File, this is extrated from the Spread sheet 
//    : //depotAE/projects/MEC1322/docs/MMCRs/MEC1322_FPGA1_Query_All_Addressing_ResultSet.csv
typedef volatile unsigned char      VUINT8;
typedef volatile unsigned short int VUINT16;
typedef volatile unsigned long int  VUINT32;

/***************************************************************
*                            PWM
***************************************************************/
#define ADDR_PWM_0_COUNTER_ON_TIME                               0x40005800
#define MMCR_PWM_0_COUNTER_ON_TIME                               (*(VUINT32 *)(ADDR_PWM_0_COUNTER_ON_TIME))

#define ADDR_PWM_0_COUNTER_OFF_TIME                              0x40005804
#define MMCR_PWM_0_COUNTER_OFF_TIME                              (*(VUINT32 *)(ADDR_PWM_0_COUNTER_OFF_TIME))

#define ADDR_PWM_0_CONFIGURATION                                 0x40005808
#define MMCR_PWM_0_CONFIGURATION                                 (*(VUINT32 *)(ADDR_PWM_0_CONFIGURATION))

#define ADDR_PWM_1_COUNTER_ON_TIME                               0x40005810
#define MMCR_PWM_1_COUNTER_ON_TIME                               (*(VUINT32 *)(ADDR_PWM_1_COUNTER_ON_TIME))

#define ADDR_PWM_1_COUNTER_OFF_TIME                              0x40005814
#define MMCR_PWM_1_COUNTER_OFF_TIME                              (*(VUINT32 *)(ADDR_PWM_1_COUNTER_OFF_TIME))

#define ADDR_PWM_1_CONFIGURATION                                 0x40005818
#define MMCR_PWM_1_CONFIGURATION                                 (*(VUINT32 *)(ADDR_PWM_1_CONFIGURATION))

#define ADDR_PWM_2_COUNTER_ON_TIME                               0x40005820
#define MMCR_PWM_2_COUNTER_ON_TIME                               (*(VUINT32 *)(ADDR_PWM_2_COUNTER_ON_TIME))

#define ADDR_PWM_2_COUNTER_OFF_TIME                              0x40005824
#define MMCR_PWM_2_COUNTER_OFF_TIME                              (*(VUINT32 *)(ADDR_PWM_2_COUNTER_OFF_TIME))

#define ADDR_PWM_2_CONFIGURATION                                 0x40005828
#define MMCR_PWM_2_CONFIGURATION                                 (*(VUINT32 *)(ADDR_PWM_2_CONFIGURATION))

#define ADDR_PWM_3_COUNTER_ON_TIME                               0x40005830
#define MMCR_PWM_3_COUNTER_ON_TIME                               (*(VUINT32 *)(ADDR_PWM_3_COUNTER_ON_TIME))

#define ADDR_PWM_3_COUNTER_OFF_TIME                              0x40005834
#define MMCR_PWM_3_COUNTER_OFF_TIME                              (*(VUINT32 *)(ADDR_PWM_3_COUNTER_OFF_TIME))

#define ADDR_PWM_3_CONFIGURATION                                 0x40005838
#define MMCR_PWM_3_CONFIGURATION                                 (*(VUINT32 *)(ADDR_PWM_3_CONFIGURATION))

/***************************************************************
*                            PECI
***************************************************************/
#define ADDR_PECI_WRITE_DATA                                     0x40006400
#define MMCR_PECI_WRITE_DATA                                     (*(VUINT32 *)(ADDR_PECI_WRITE_DATA))

#define ADDR_PECI_READ_DATA                                      0x40006404
#define MMCR_PECI_READ_DATA                                      (*(VUINT32 *)(ADDR_PECI_READ_DATA))

#define ADDR_PECI_CONTROL                                        0x40006408
#define MMCR_PECI_CONTROL                                        (*(VUINT32 *)(ADDR_PECI_CONTROL))

#define ADDR_PECI_STATUS_1                                       0x4000640C
#define MMCR_PECI_STATUS_1                                       (*(VUINT32 *)(ADDR_PECI_STATUS_1))

#define ADDR_PECI_STATUS_2                                       0x40006410
#define MMCR_PECI_STATUS_2                                       (*(VUINT32 *)(ADDR_PECI_STATUS_2))

#define ADDR_PECI_ERROR                                          0x40006414
#define MMCR_PECI_ERROR                                          (*(VUINT32 *)(ADDR_PECI_ERROR))

#define ADDR_PECI_INTERRUPT_ENABLE_1                             0x40006418
#define MMCR_PECI_INTERRUPT_ENABLE_1                             (*(VUINT32 *)(ADDR_PECI_INTERRUPT_ENABLE_1))

#define ADDR_PECI_INTERRUPT_ENABLE_2                             0x4000641C
#define MMCR_PECI_INTERRUPT_ENABLE_2                             (*(VUINT32 *)(ADDR_PECI_INTERRUPT_ENABLE_2))

#define ADDR_PECI_OPTIMAL_BIT_TIME_LOW_BYTE                      0x40006420
#define MMCR_PECI_OPTIMAL_BIT_TIME_LOW_BYTE                      (*(VUINT32 *)(ADDR_PECI_OPTIMAL_BIT_TIME_LOW_BYTE))

#define ADDR_PECI_OPTIMAL_BIT_TIME_HIGH_BYTE                     0x40006424
#define MMCR_PECI_OPTIMAL_BIT_TIME_HIGH_BYTE                     (*(VUINT32 *)(ADDR_PECI_OPTIMAL_BIT_TIME_HIGH_BYTE))

#define ADDR_PECI_REQUEST_TIMER_LOW_BYTE                         0x40006428
#define MMCR_PECI_REQUEST_TIMER_LOW_BYTE                         (*(VUINT32 *)(ADDR_PECI_REQUEST_TIMER_LOW_BYTE))

#define ADDR_PECI_REQUEST_TIMER_HIGH_BYTE                        0x4000642C
#define MMCR_PECI_REQUEST_TIMER_HIGH_BYTE                        (*(VUINT32 *)(ADDR_PECI_REQUEST_TIMER_HIGH_BYTE))

#define ADDR_PECI_BLOCK_ID                                       0x40006440
#define MMCR_PECI_BLOCK_ID                                       (*(VUINT32 *)(ADDR_PECI_BLOCK_ID))

#define ADDR_PECI_BLOCK_REVISION                                 0x40006444
#define MMCR_PECI_BLOCK_REVISION                                 (*(VUINT32 *)(ADDR_PECI_BLOCK_REVISION))

/***************************************************************
*                            ACPI EC Interface 
***************************************************************/
#define ADDR_ACPI_0_EC2OS_DATA_EC_BYTE_0                         0x400F0D00
#define MMCR_ACPI_0_EC2OS_DATA_EC_BYTE_0                         (*(VUINT8 *)(ADDR_ACPI_0_EC2OS_DATA_EC_BYTE_0))

#define ADDR_ACPI_0_EC2OS_DATA_EC_BYTE_1                         0x400F0D01
#define MMCR_ACPI_0_EC2OS_DATA_EC_BYTE_1                         (*(VUINT8 *)(ADDR_ACPI_0_EC2OS_DATA_EC_BYTE_1))

#define ADDR_ACPI_0_EC2OS_DATA_EC_BYTE_2                         0x400F0D02
#define MMCR_ACPI_0_EC2OS_DATA_EC_BYTE_2                         (*(VUINT8 *)(ADDR_ACPI_0_EC2OS_DATA_EC_BYTE_2))

#define ADDR_ACPI_0_EC2OS_DATA_EC_BYTE_3                         0x400F0D03
#define MMCR_ACPI_0_EC2OS_DATA_EC_BYTE_3                         (*(VUINT8 *)(ADDR_ACPI_0_EC2OS_DATA_EC_BYTE_3))

#define ADDR_ACPI_0_STATUS_EC                                    0x400F0D04
#define MMCR_ACPI_0_STATUS_EC                                    (*(VUINT8 *)(ADDR_ACPI_0_STATUS_EC))

#define ADDR_ACPI_0_BYTE_CONTROL_EC                              0x400F0D05
#define MMCR_ACPI_0_BYTE_CONTROL_EC                              (*(VUINT8 *)(ADDR_ACPI_0_BYTE_CONTROL_EC))

#define ADDR_ACPI_0_OS2EC_DATA_EC_BYTE_0                         0x400F0D08
#define MMCR_ACPI_0_OS2EC_DATA_EC_BYTE_0                         (*(VUINT8 *)(ADDR_ACPI_0_OS2EC_DATA_EC_BYTE_0))

#define ADDR_ACPI_0_OS2EC_DATA_EC_BYTE_0                         0x400F0D08
#define MMCR_ACPI_0_OS2EC_DATA_EC_BYTE_0                         (*(VUINT8 *)(ADDR_ACPI_0_OS2EC_DATA_EC_BYTE_0))

#define ADDR_ACPI_0_OS2EC_DATA_EC_BYTE_1                         0x400F0D09
#define MMCR_ACPI_0_OS2EC_DATA_EC_BYTE_1                         (*(VUINT8 *)(ADDR_ACPI_0_OS2EC_DATA_EC_BYTE_1))

#define ADDR_ACPI_0_OS2EC_DATA_EC_BYTE_2                         0x400F0D0A
#define MMCR_ACPI_0_OS2EC_DATA_EC_BYTE_2                         (*(VUINT8 *)(ADDR_ACPI_0_OS2EC_DATA_EC_BYTE_2))

#define ADDR_ACPI_0_OS2EC_DATA_EC_BYTE_3                         0x400F0D0B
#define MMCR_ACPI_0_OS2EC_DATA_EC_BYTE_3                         (*(VUINT8 *)(ADDR_ACPI_0_OS2EC_DATA_EC_BYTE_3))

#define ADDR_ACPI_1_EC2OS_DATA_EC_BYTE_0                         0x400F1100
#define MMCR_ACPI_1_EC2OS_DATA_EC_BYTE_0                         (*(VUINT8 *)(ADDR_ACPI_1_EC2OS_DATA_EC_BYTE_0))

#define ADDR_ACPI_1_EC2OS_DATA_EC_BYTE_1                         0x400F1101
#define MMCR_ACPI_1_EC2OS_DATA_EC_BYTE_1                         (*(VUINT8 *)(ADDR_ACPI_1_EC2OS_DATA_EC_BYTE_1))

#define ADDR_ACPI_1_EC2OS_DATA_EC_BYTE_2                         0x400F1102
#define MMCR_ACPI_1_EC2OS_DATA_EC_BYTE_2                         (*(VUINT8 *)(ADDR_ACPI_1_EC2OS_DATA_EC_BYTE_2))

#define ADDR_ACPI_1_EC2OS_DATA_EC_BYTE_3                         0x400F1103
#define MMCR_ACPI_1_EC2OS_DATA_EC_BYTE_3                         (*(VUINT8 *)(ADDR_ACPI_1_EC2OS_DATA_EC_BYTE_3))

#define ADDR_ACPI_1_STATUS_EC                                    0x400F1104
#define MMCR_ACPI_1_STATUS_EC                                    (*(VUINT8 *)(ADDR_ACPI_1_STATUS_EC))

#define ADDR_ACPI_1_BYTE_CONTROL_EC                              0x400F1105
#define MMCR_ACPI_1_BYTE_CONTROL_EC                              (*(VUINT8 *)(ADDR_ACPI_1_BYTE_CONTROL_EC))

#define ADDR_ACPI_1_OS2EC_DATA_EC_BYTE_0                         0x400F1108
#define MMCR_ACPI_1_OS2EC_DATA_EC_BYTE_0                         (*(VUINT8 *)(ADDR_ACPI_1_OS2EC_DATA_EC_BYTE_0))

#define ADDR_ACPI_1_OS2EC_DATA_EC_BYTE_0                         0x400F1108
#define MMCR_ACPI_1_OS2EC_DATA_EC_BYTE_0                         (*(VUINT8 *)(ADDR_ACPI_1_OS2EC_DATA_EC_BYTE_0))

#define ADDR_ACPI_1_OS2EC_DATA_EC_BYTE_1                         0x400F1109
#define MMCR_ACPI_1_OS2EC_DATA_EC_BYTE_1                         (*(VUINT8 *)(ADDR_ACPI_1_OS2EC_DATA_EC_BYTE_1))

#define ADDR_ACPI_1_OS2EC_DATA_EC_BYTE_2                         0x400F110A
#define MMCR_ACPI_1_OS2EC_DATA_EC_BYTE_2                         (*(VUINT8 *)(ADDR_ACPI_1_OS2EC_DATA_EC_BYTE_2))

#define ADDR_ACPI_1_OS2EC_DATA_EC_BYTE_3                         0x400F110B
#define MMCR_ACPI_1_OS2EC_DATA_EC_BYTE_3                         (*(VUINT8 *)(ADDR_ACPI_1_OS2EC_DATA_EC_BYTE_3))

/***************************************************************
*                            Keyboard Matrix Scan Support
***************************************************************/
#define ADDR_KEYBOARD_KSO_SELECT                                 0x40009C04
#define MMCR_KEYBOARD_KSO_SELECT                                 (*(VUINT32 *)(ADDR_KEYBOARD_KSO_SELECT))

#define ADDR_KEYBOARD_KSI_INPUT                                  0x40009C08
#define MMCR_KEYBOARD_KSI_INPUT                                  (*(VUINT32 *)(ADDR_KEYBOARD_KSI_INPUT))

#define ADDR_KEYBOARD_KSI_STATUS                                 0x40009C0C
#define MMCR_KEYBOARD_KSI_STATUS                                 (*(VUINT32 *)(ADDR_KEYBOARD_KSI_STATUS))

#define ADDR_KEYBOARD_KSI_INTERRUPT_ENABLE                       0x40009C10
#define MMCR_KEYBOARD_KSI_INTERRUPT_ENABLE                       (*(VUINT32 *)(ADDR_KEYBOARD_KSI_INTERRUPT_ENABLE))

#define ADDR_KEYBOARD_KEYSCAN_EXTENDED_CONTROL                   0x40009C14
#define MMCR_KEYBOARD_KEYSCAN_EXTENDED_CONTROL                   (*(VUINT32 *)(ADDR_KEYBOARD_KEYSCAN_EXTENDED_CONTROL))

/***************************************************************
*                            PS/2 Device Interface
***************************************************************/
#define ADDR_PS2_3_STATUS                                        0x400090C8
#define MMCR_PS2_3_STATUS                                        (*(VUINT8 *)(ADDR_PS2_3_STATUS))

#define ADDR_PS2_3_CONTROL                                       0x400090C4
#define MMCR_PS2_3_CONTROL                                       (*(VUINT8 *)(ADDR_PS2_3_CONTROL))

#define ADDR_PS2_3_RECEIVE_BUFFER                                0x400090C0
#define MMCR_PS2_3_RECEIVE_BUFFER                                (*(VUINT8 *)(ADDR_PS2_3_RECEIVE_BUFFER))

#define ADDR_PS2_3_TRANSMIT_BUFFER                               0x400090C0
#define MMCR_PS2_3_TRANSMIT_BUFFER                               (*(VUINT8 *)(ADDR_PS2_3_TRANSMIT_BUFFER))

#define ADDR_PS2_0_TRANSMIT_BUFFER                               0x40009000
#define MMCR_PS2_0_TRANSMIT_BUFFER                               (*(VUINT8 *)(ADDR_PS2_0_TRANSMIT_BUFFER))

#define ADDR_PS2_0_RECEIVE_BUFFER                                0x40009000
#define MMCR_PS2_0_RECEIVE_BUFFER                                (*(VUINT8 *)(ADDR_PS2_0_RECEIVE_BUFFER))

#define ADDR_PS2_0_CONTROL                                       0x40009004
#define MMCR_PS2_0_CONTROL                                       (*(VUINT8 *)(ADDR_PS2_0_CONTROL))

#define ADDR_PS2_0_STATUS                                        0x40009008
#define MMCR_PS2_0_STATUS                                        (*(VUINT8 *)(ADDR_PS2_0_STATUS))

#define ADDR_PS2_1_TRANSMIT_BUFFER                               0x40009040
#define MMCR_PS2_1_TRANSMIT_BUFFER                               (*(VUINT8 *)(ADDR_PS2_1_TRANSMIT_BUFFER))

#define ADDR_PS2_1_RECEIVE_BUFFER                                0x40009040
#define MMCR_PS2_1_RECEIVE_BUFFER                                (*(VUINT8 *)(ADDR_PS2_1_RECEIVE_BUFFER))

#define ADDR_PS2_1_CONTROL                                       0x40009044
#define MMCR_PS2_1_CONTROL                                       (*(VUINT8 *)(ADDR_PS2_1_CONTROL))

#define ADDR_PS2_1_STATUS                                        0x40009048
#define MMCR_PS2_1_STATUS                                        (*(VUINT8 *)(ADDR_PS2_1_STATUS))

#define ADDR_PS2_2_RECEIVE_BUFFER                                0x40009080
#define MMCR_PS2_2_RECEIVE_BUFFER                                (*(VUINT8 *)(ADDR_PS2_2_RECEIVE_BUFFER))

#define ADDR_PS2_2_TRANSMIT_BUFFER                               0x40009080
#define MMCR_PS2_2_TRANSMIT_BUFFER                               (*(VUINT8 *)(ADDR_PS2_2_TRANSMIT_BUFFER))

#define ADDR_PS2_2_CONTROL                                       0x40009084
#define MMCR_PS2_2_CONTROL                                       (*(VUINT8 *)(ADDR_PS2_2_CONTROL))

#define ADDR_PS2_2_STATUS                                        0x40009088
#define MMCR_PS2_2_STATUS                                        (*(VUINT8 *)(ADDR_PS2_2_STATUS))

/***************************************************************
*                            8042 Host Interface
***************************************************************/
#define ADDR_8042_ACTIVATE                                       0x400F0730
#define MMCR_8042_ACTIVATE                                       (*(VUINT8 *)(ADDR_8042_ACTIVATE))

#define ADDR_8042_HOST_EC_DATACMD                                0x400F0500
#define MMCR_8042_HOST_EC_DATACMD                                (*(VUINT8 *)(ADDR_8042_HOST_EC_DATACMD))

#define ADDR_8042_EC_HOST_DATA                                   0x400F0500
#define MMCR_8042_EC_HOST_DATA                                   (*(VUINT8 *)(ADDR_8042_EC_HOST_DATA))

#define ADDR_8042_KEYBOARD_STATUS_READ                           0x400F0504
#define MMCR_8042_KEYBOARD_STATUS_READ                           (*(VUINT8 *)(ADDR_8042_KEYBOARD_STATUS_READ))

#define ADDR_8042_KEYBOARD_CONTROL                               0x400F0508
#define MMCR_8042_KEYBOARD_CONTROL                               (*(VUINT8 *)(ADDR_8042_KEYBOARD_CONTROL))

#define ADDR_8042_EC_HOST_AUX                                    0x400F050C
#define MMCR_8042_EC_HOST_AUX                                    (*(VUINT8 *)(ADDR_8042_EC_HOST_AUX))

#define ADDR_8042_PCOBF                                          0x400F0514
#define MMCR_8042_PCOBF                                          (*(VUINT8 *)(ADDR_8042_PCOBF))

#define ADDR_8042_PORT92_ENABLE                                  0x400F1B30
#define MMCR_8042_PORT92_ENABLE                                  (*(VUINT8 *)(ADDR_8042_PORT92_ENABLE))

#define ADDR_8042_GATEA20_CONTROL                                0x400F1900
#define MMCR_8042_GATEA20_CONTROL                                (*(VUINT8 *)(ADDR_8042_GATEA20_CONTROL))

#define ADDR_8042_SETGA20L                                       0x400F1908
#define MMCR_8042_SETGA20L                                       (*(VUINT8 *)(ADDR_8042_SETGA20L))

#define ADDR_8042_RSTGA20L                                       0x400F190C
#define MMCR_8042_RSTGA20L                                       (*(VUINT8 *)(ADDR_8042_RSTGA20L))

/***************************************************************
*                            SMBus
***************************************************************/
#define ADDR_SMB_3_DEBUG_FSM_SMB                                 0x4000B45C
#define MMCR_SMB_3_DEBUG_FSM_SMB                                 (*(VUINT32 *)(ADDR_SMB_3_DEBUG_FSM_SMB))

#define ADDR_SMB_3_DEBUG_FSM_I2C                                 0x4000B458
#define MMCR_SMB_3_DEBUG_FSM_I2C                                 (*(VUINT32 *)(ADDR_SMB_3_DEBUG_FSM_I2C))

#define ADDR_SMBUS_3_MASTER_RECEIVE_BUFFER                       0x4000B454
#define MMCR_SMBUS_3_MASTER_RECEIVE_BUFFER                       (*(VUINT8 *)(ADDR_SMBUS_3_MASTER_RECEIVE_BUFFER))

#define ADDR_SMBUS_3_MASTER_TRANSMIT_BUFER                       0x4000B450
#define MMCR_SMBUS_3_MASTER_TRANSMIT_BUFER                       (*(VUINT8 *)(ADDR_SMBUS_3_MASTER_TRANSMIT_BUFER))

#define ADDR_SMBUS_3_SLAVE_RECEIVE_BUFFER                        0x4000B44C
#define MMCR_SMBUS_3_SLAVE_RECEIVE_BUFFER                        (*(VUINT8 *)(ADDR_SMBUS_3_SLAVE_RECEIVE_BUFFER))

#define ADDR_SMBUS_3_SLAVE_TRANSMIT_BUFFER                       0x4000B448
#define MMCR_SMBUS_3_SLAVE_TRANSMIT_BUFFER                       (*(VUINT8 *)(ADDR_SMBUS_3_SLAVE_TRANSMIT_BUFFER))

#define ADDR_SMB_3_TIME_OUT_SCALING                              0x4000B444
#define MMCR_SMB_3_TIME_OUT_SCALING                              (*(VUINT32 *)(ADDR_SMB_3_TIME_OUT_SCALING))

#define ADDR_SMB_3_DATA_TIMING                                   0x4000B440
#define MMCR_SMB_3_DATA_TIMING                                   (*(VUINT32 *)(ADDR_SMB_3_DATA_TIMING))

#define ADDR_SMB_3_CLOCK_SYNC                                    0x4000B43C
#define MMCR_SMB_3_CLOCK_SYNC                                    (*(VUINT32 *)(ADDR_SMB_3_CLOCK_SYNC))

#define ADDR_SMB_3_BIT_BANG_CONTROL                              0x4000B438
#define MMCR_SMB_3_BIT_BANG_CONTROL                              (*(VUINT8 *)(ADDR_SMB_3_BIT_BANG_CONTROL))

#define ADDR_SMB_3_REVISION                                      0x4000B434
#define MMCR_SMB_3_REVISION                                      (*(VUINT8 *)(ADDR_SMB_3_REVISION))

#define ADDR_SMB_3_BLOCK_ID                                      0x4000B430
#define MMCR_SMB_3_BLOCK_ID                                      (*(VUINT8 *)(ADDR_SMB_3_BLOCK_ID))

#define ADDR_SMB_3_BUS_CLOCK                                     0x4000B42C
#define MMCR_SMB_3_BUS_CLOCK                                     (*(VUINT16 *)(ADDR_SMB_3_BUS_CLOCK))

#define ADDR_SMB_3_CONFIGURATION                                 0x4000B428
#define MMCR_SMB_3_CONFIGURATION                                 (*(VUINT32 *)(ADDR_SMB_3_CONFIGURATION))

#define ADDR_SMB_3_IDLE_SCALING                                  0x4000B424
#define MMCR_SMB_3_IDLE_SCALING                                  (*(VUINT32 *)(ADDR_SMB_3_IDLE_SCALING))

#define ADDR_SMB_3_COMPLETION                                    0x4000B420
#define MMCR_SMB_3_COMPLETION                                    (*(VUINT32 *)(ADDR_SMB_3_COMPLETION))

#define ADDR_SMB_3_DATA_TIMING2                                  0x4000B418
#define MMCR_SMB_3_DATA_TIMING2                                  (*(VUINT8 *)(ADDR_SMB_3_DATA_TIMING2))

#define ADDR_SMB_3_PEC                                           0x4000B414
#define MMCR_SMB_3_PEC                                           (*(VUINT8 *)(ADDR_SMB_3_PEC))

#define ADDR_SMBUS_3_SLAVE_COMMAND                               0x4000B410
#define MMCR_SMBUS_3_SLAVE_COMMAND                               (*(VUINT32 *)(ADDR_SMBUS_3_SLAVE_COMMAND))

#define ADDR_SMBUS_3_MASTER_COMMAND                              0x4000B40C
#define MMCR_SMBUS_3_MASTER_COMMAND                              (*(VUINT32 *)(ADDR_SMBUS_3_MASTER_COMMAND))

#define ADDR_SMB_3_DATA                                          0x4000B408
#define MMCR_SMB_3_DATA                                          (*(VUINT8 *)(ADDR_SMB_3_DATA))

#define ADDR_SMB_3_OWN_ADDRESS                                   0x4000B404
#define MMCR_SMB_3_OWN_ADDRESS                                   (*(VUINT16 *)(ADDR_SMB_3_OWN_ADDRESS))

#define ADDR_SMB_3_STATUS                                        0x4000B400
#define MMCR_SMB_3_STATUS                                        (*(VUINT8 *)(ADDR_SMB_3_STATUS))

#define ADDR_SMB_3_CONTROL                                       0x4000B400
#define MMCR_SMB_3_CONTROL                                       (*(VUINT8 *)(ADDR_SMB_3_CONTROL))

#define ADDR_SMB_2_CONTROL                                       0x4000B000
#define MMCR_SMB_2_CONTROL                                       (*(VUINT8 *)(ADDR_SMB_2_CONTROL))

#define ADDR_SMB_2_STATUS                                        0x4000B000
#define MMCR_SMB_2_STATUS                                        (*(VUINT8 *)(ADDR_SMB_2_STATUS))

#define ADDR_SMB_2_OWN_ADDRESS                                   0x4000B004
#define MMCR_SMB_2_OWN_ADDRESS                                   (*(VUINT16 *)(ADDR_SMB_2_OWN_ADDRESS))

#define ADDR_SMB_2_DATA                                          0x4000B008
#define MMCR_SMB_2_DATA                                          (*(VUINT8 *)(ADDR_SMB_2_DATA))

#define ADDR_SMBUS_2_MASTER_COMMAND                              0x4000B00C
#define MMCR_SMBUS_2_MASTER_COMMAND                              (*(VUINT32 *)(ADDR_SMBUS_2_MASTER_COMMAND))

#define ADDR_SMBUS_2_SLAVE_COMMAND                               0x4000B010
#define MMCR_SMBUS_2_SLAVE_COMMAND                               (*(VUINT32 *)(ADDR_SMBUS_2_SLAVE_COMMAND))

#define ADDR_SMB_2_PEC                                           0x4000B014
#define MMCR_SMB_2_PEC                                           (*(VUINT8 *)(ADDR_SMB_2_PEC))

#define ADDR_SMB_2_DATA_TIMING2                                  0x4000B018
#define MMCR_SMB_2_DATA_TIMING2                                  (*(VUINT8 *)(ADDR_SMB_2_DATA_TIMING2))

#define ADDR_SMB_2_COMPLETION                                    0x4000B020
#define MMCR_SMB_2_COMPLETION                                    (*(VUINT32 *)(ADDR_SMB_2_COMPLETION))

#define ADDR_SMB_2_IDLE_SCALING                                  0x4000B024
#define MMCR_SMB_2_IDLE_SCALING                                  (*(VUINT32 *)(ADDR_SMB_2_IDLE_SCALING))

#define ADDR_SMB_2_CONFIGURATION                                 0x4000B028
#define MMCR_SMB_2_CONFIGURATION                                 (*(VUINT32 *)(ADDR_SMB_2_CONFIGURATION))

#define ADDR_SMB_2_BUS_CLOCK                                     0x4000B02C
#define MMCR_SMB_2_BUS_CLOCK                                     (*(VUINT16 *)(ADDR_SMB_2_BUS_CLOCK))

#define ADDR_SMB_2_BLOCK_ID                                      0x4000B030
#define MMCR_SMB_2_BLOCK_ID                                      (*(VUINT8 *)(ADDR_SMB_2_BLOCK_ID))

#define ADDR_SMB_2_REVISION                                      0x4000B034
#define MMCR_SMB_2_REVISION                                      (*(VUINT8 *)(ADDR_SMB_2_REVISION))

#define ADDR_SMB_2_BIT_BANG_CONTROL                              0x4000B038
#define MMCR_SMB_2_BIT_BANG_CONTROL                              (*(VUINT8 *)(ADDR_SMB_2_BIT_BANG_CONTROL))

#define ADDR_SMB_2_CLOCK_SYNC                                    0x4000B03C
#define MMCR_SMB_2_CLOCK_SYNC                                    (*(VUINT32 *)(ADDR_SMB_2_CLOCK_SYNC))

#define ADDR_SMB_2_DATA_TIMING                                   0x4000B040
#define MMCR_SMB_2_DATA_TIMING                                   (*(VUINT32 *)(ADDR_SMB_2_DATA_TIMING))

#define ADDR_SMB_2_TIME_OUT_SCALING                              0x4000B044
#define MMCR_SMB_2_TIME_OUT_SCALING                              (*(VUINT32 *)(ADDR_SMB_2_TIME_OUT_SCALING))

#define ADDR_SMBUS_2_SLAVE_TRANSMIT_BUFFER                       0x4000B048
#define MMCR_SMBUS_2_SLAVE_TRANSMIT_BUFFER                       (*(VUINT8 *)(ADDR_SMBUS_2_SLAVE_TRANSMIT_BUFFER))

#define ADDR_SMBUS_2_SLAVE_RECEIVE_BUFFER                        0x4000B04C
#define MMCR_SMBUS_2_SLAVE_RECEIVE_BUFFER                        (*(VUINT8 *)(ADDR_SMBUS_2_SLAVE_RECEIVE_BUFFER))

#define ADDR_SMBUS_2_MASTER_TRANSMIT_BUFER                       0x4000B050
#define MMCR_SMBUS_2_MASTER_TRANSMIT_BUFER                       (*(VUINT8 *)(ADDR_SMBUS_2_MASTER_TRANSMIT_BUFER))

#define ADDR_SMBUS_2_MASTER_RECEIVE_BUFFER                       0x4000B054
#define MMCR_SMBUS_2_MASTER_RECEIVE_BUFFER                       (*(VUINT8 *)(ADDR_SMBUS_2_MASTER_RECEIVE_BUFFER))

#define ADDR_SMB_2_DEBUG_FSM_I2C                                 0x4000B058
#define MMCR_SMB_2_DEBUG_FSM_I2C                                 (*(VUINT32 *)(ADDR_SMB_2_DEBUG_FSM_I2C))

#define ADDR_SMB_2_DEBUG_FSM_SMB                                 0x4000B05C
#define MMCR_SMB_2_DEBUG_FSM_SMB                                 (*(VUINT32 *)(ADDR_SMB_2_DEBUG_FSM_SMB))

#define ADDR_SMB_1_CONTROL                                       0x4000AC00
#define MMCR_SMB_1_CONTROL                                       (*(VUINT8 *)(ADDR_SMB_1_CONTROL))

#define ADDR_SMB_1_STATUS                                        0x4000AC00
#define MMCR_SMB_1_STATUS                                        (*(VUINT8 *)(ADDR_SMB_1_STATUS))

#define ADDR_SMB_1_OWN_ADDRESS                                   0x4000AC04
#define MMCR_SMB_1_OWN_ADDRESS                                   (*(VUINT16 *)(ADDR_SMB_1_OWN_ADDRESS))

#define ADDR_SMB_1_DATA                                          0x4000AC08
#define MMCR_SMB_1_DATA                                          (*(VUINT8 *)(ADDR_SMB_1_DATA))

#define ADDR_SMBUS_1_MASTER_COMMAND                              0x4000AC0C
#define MMCR_SMBUS_1_MASTER_COMMAND                              (*(VUINT32 *)(ADDR_SMBUS_1_MASTER_COMMAND))

#define ADDR_SMBUS_1_SLAVE_COMMAND                               0x4000AC10
#define MMCR_SMBUS_1_SLAVE_COMMAND                               (*(VUINT32 *)(ADDR_SMBUS_1_SLAVE_COMMAND))

#define ADDR_SMB_1_PEC                                           0x4000AC14
#define MMCR_SMB_1_PEC                                           (*(VUINT8 *)(ADDR_SMB_1_PEC))

#define ADDR_SMB_1_DATA_TIMING2                                  0x4000AC18
#define MMCR_SMB_1_DATA_TIMING2                                  (*(VUINT8 *)(ADDR_SMB_1_DATA_TIMING2))

#define ADDR_SMB_1_COMPLETION                                    0x4000AC20
#define MMCR_SMB_1_COMPLETION                                    (*(VUINT32 *)(ADDR_SMB_1_COMPLETION))

#define ADDR_SMB_1_IDLE_SCALING                                  0x4000AC24
#define MMCR_SMB_1_IDLE_SCALING                                  (*(VUINT32 *)(ADDR_SMB_1_IDLE_SCALING))

#define ADDR_SMB_1_CONFIGURATION                                 0x4000AC28
#define MMCR_SMB_1_CONFIGURATION                                 (*(VUINT32 *)(ADDR_SMB_1_CONFIGURATION))

#define ADDR_SMB_1_BUS_CLOCK                                     0x4000AC2C
#define MMCR_SMB_1_BUS_CLOCK                                     (*(VUINT16 *)(ADDR_SMB_1_BUS_CLOCK))

#define ADDR_SMB_1_BLOCK_ID                                      0x4000AC30
#define MMCR_SMB_1_BLOCK_ID                                      (*(VUINT8 *)(ADDR_SMB_1_BLOCK_ID))

#define ADDR_SMB_1_REVISION                                      0x4000AC34
#define MMCR_SMB_1_REVISION                                      (*(VUINT8 *)(ADDR_SMB_1_REVISION))

#define ADDR_SMB_1_BIT_BANG_CONTROL                              0x4000AC38
#define MMCR_SMB_1_BIT_BANG_CONTROL                              (*(VUINT8 *)(ADDR_SMB_1_BIT_BANG_CONTROL))

#define ADDR_SMB_1_CLOCK_SYNC                                    0x4000AC3C
#define MMCR_SMB_1_CLOCK_SYNC                                    (*(VUINT32 *)(ADDR_SMB_1_CLOCK_SYNC))

#define ADDR_SMB_1_DATA_TIMING                                   0x4000AC40
#define MMCR_SMB_1_DATA_TIMING                                   (*(VUINT32 *)(ADDR_SMB_1_DATA_TIMING))

#define ADDR_SMB_1_TIME_OUT_SCALING                              0x4000AC44
#define MMCR_SMB_1_TIME_OUT_SCALING                              (*(VUINT32 *)(ADDR_SMB_1_TIME_OUT_SCALING))

#define ADDR_SMBUS_1_SLAVE_TRANSMIT_BUFFER                       0x4000AC48
#define MMCR_SMBUS_1_SLAVE_TRANSMIT_BUFFER                       (*(VUINT8 *)(ADDR_SMBUS_1_SLAVE_TRANSMIT_BUFFER))

#define ADDR_SMBUS_1_SLAVE_RECEIVE_BUFFER                        0x4000AC4C
#define MMCR_SMBUS_1_SLAVE_RECEIVE_BUFFER                        (*(VUINT8 *)(ADDR_SMBUS_1_SLAVE_RECEIVE_BUFFER))

#define ADDR_SMBUS_1_MASTER_TRANSMIT_BUFER                       0x4000AC50
#define MMCR_SMBUS_1_MASTER_TRANSMIT_BUFER                       (*(VUINT8 *)(ADDR_SMBUS_1_MASTER_TRANSMIT_BUFER))

#define ADDR_SMBUS_1_MASTER_RECEIVE_BUFFER                       0x4000AC54
#define MMCR_SMBUS_1_MASTER_RECEIVE_BUFFER                       (*(VUINT8 *)(ADDR_SMBUS_1_MASTER_RECEIVE_BUFFER))

#define ADDR_SMB_1_DEBUG_FSM_I2C                                 0x4000AC58
#define MMCR_SMB_1_DEBUG_FSM_I2C                                 (*(VUINT32 *)(ADDR_SMB_1_DEBUG_FSM_I2C))

#define ADDR_SMB_1_DEBUG_FSM_SMB                                 0x4000AC5C
#define MMCR_SMB_1_DEBUG_FSM_SMB                                 (*(VUINT32 *)(ADDR_SMB_1_DEBUG_FSM_SMB))

#define ADDR_SMB_0_STATUS                                        0x40001800
#define MMCR_SMB_0_STATUS                                        (*(VUINT8 *)(ADDR_SMB_0_STATUS))

#define ADDR_SMB_0_CONTROL                                       0x40001800
#define MMCR_SMB_0_CONTROL                                       (*(VUINT8 *)(ADDR_SMB_0_CONTROL))

#define ADDR_SMB_0_OWN_ADDRESS                                   0x40001804
#define MMCR_SMB_0_OWN_ADDRESS                                   (*(VUINT16 *)(ADDR_SMB_0_OWN_ADDRESS))

#define ADDR_SMB_0_DATA                                          0x40001808
#define MMCR_SMB_0_DATA                                          (*(VUINT8 *)(ADDR_SMB_0_DATA))

#define ADDR_SMBUS_0_MASTER_COMMAND                              0x4000180C
#define MMCR_SMBUS_0_MASTER_COMMAND                              (*(VUINT32 *)(ADDR_SMBUS_0_MASTER_COMMAND))

#define ADDR_SMBUS_0_SLAVE_COMMAND                               0x40001810
#define MMCR_SMBUS_0_SLAVE_COMMAND                               (*(VUINT32 *)(ADDR_SMBUS_0_SLAVE_COMMAND))

#define ADDR_SMB_0_PEC                                           0x40001814
#define MMCR_SMB_0_PEC                                           (*(VUINT8 *)(ADDR_SMB_0_PEC))

#define ADDR_SMB_0_DATA_TIMING2                                  0x40001818
#define MMCR_SMB_0_DATA_TIMING2                                  (*(VUINT8 *)(ADDR_SMB_0_DATA_TIMING2))

#define ADDR_SMB_0_COMPLETION                                    0x40001820
#define MMCR_SMB_0_COMPLETION                                    (*(VUINT32 *)(ADDR_SMB_0_COMPLETION))

#define ADDR_SMB_0_IDLE_SCALING                                  0x40001824
#define MMCR_SMB_0_IDLE_SCALING                                  (*(VUINT32 *)(ADDR_SMB_0_IDLE_SCALING))

#define ADDR_SMB_0_CONFIGURATION                                 0x40001828
#define MMCR_SMB_0_CONFIGURATION                                 (*(VUINT32 *)(ADDR_SMB_0_CONFIGURATION))

#define ADDR_SMB_0_BUS_CLOCK                                     0x4000182C
#define MMCR_SMB_0_BUS_CLOCK                                     (*(VUINT16 *)(ADDR_SMB_0_BUS_CLOCK))

#define ADDR_SMB_0_BLOCK_ID                                      0x40001830
#define MMCR_SMB_0_BLOCK_ID                                      (*(VUINT8 *)(ADDR_SMB_0_BLOCK_ID))

#define ADDR_SMB_0_REVISION                                      0x40001834
#define MMCR_SMB_0_REVISION                                      (*(VUINT8 *)(ADDR_SMB_0_REVISION))

#define ADDR_SMB_0_BIT_BANG_CONTROL                              0x40001838
#define MMCR_SMB_0_BIT_BANG_CONTROL                              (*(VUINT8 *)(ADDR_SMB_0_BIT_BANG_CONTROL))

#define ADDR_SMB_0_CLOCK_SYNC                                    0x4000183C
#define MMCR_SMB_0_CLOCK_SYNC                                    (*(VUINT32 *)(ADDR_SMB_0_CLOCK_SYNC))

#define ADDR_SMB_0_DATA_TIMING                                   0x40001840
#define MMCR_SMB_0_DATA_TIMING                                   (*(VUINT32 *)(ADDR_SMB_0_DATA_TIMING))

#define ADDR_SMB_0_TIME_OUT_SCALING                              0x40001844
#define MMCR_SMB_0_TIME_OUT_SCALING                              (*(VUINT32 *)(ADDR_SMB_0_TIME_OUT_SCALING))

#define ADDR_SMBUS_0_SLAVE_TRANSMIT_BUFFER                       0x40001848
#define MMCR_SMBUS_0_SLAVE_TRANSMIT_BUFFER                       (*(VUINT8 *)(ADDR_SMBUS_0_SLAVE_TRANSMIT_BUFFER))

#define ADDR_SMBUS_0_SLAVE_RECEIVE_BUFFER                        0x4000184C
#define MMCR_SMBUS_0_SLAVE_RECEIVE_BUFFER                        (*(VUINT8 *)(ADDR_SMBUS_0_SLAVE_RECEIVE_BUFFER))

#define ADDR_SMBUS_0_MASTER_TRANSMIT_BUFER                       0x40001850
#define MMCR_SMBUS_0_MASTER_TRANSMIT_BUFER                       (*(VUINT8 *)(ADDR_SMBUS_0_MASTER_TRANSMIT_BUFER))

#define ADDR_SMBUS_0_MASTER_RECEIVE_BUFFER                       0x40001854
#define MMCR_SMBUS_0_MASTER_RECEIVE_BUFFER                       (*(VUINT8 *)(ADDR_SMBUS_0_MASTER_RECEIVE_BUFFER))

#define ADDR_SMB_0_DEBUG_FSM_I2C                                 0x40001858
#define MMCR_SMB_0_DEBUG_FSM_I2C                                 (*(VUINT32 *)(ADDR_SMB_0_DEBUG_FSM_I2C))

#define ADDR_SMB_0_DEBUG_FSM_SMB                                 0x4000185C
#define MMCR_SMB_0_DEBUG_FSM_SMB                                 (*(VUINT32 *)(ADDR_SMB_0_DEBUG_FSM_SMB))

/***************************************************************
*                            Watchdog Timer Interface
***************************************************************/
#define ADDR_WATCHDOG_WDT_LOAD                                   0x40000400
#define MMCR_WATCHDOG_WDT_LOAD                                   (*(VUINT16 *)(ADDR_WATCHDOG_WDT_LOAD))

#define ADDR_WATCHDOG_WDT_CONTROL                                0x40000404
#define MMCR_WATCHDOG_WDT_CONTROL                                (*(VUINT8 *)(ADDR_WATCHDOG_WDT_CONTROL))

#define ADDR_WATCHDOG_WDT_KICK                                   0x40000408
#define MMCR_WATCHDOG_WDT_KICK                                   (*(VUINT8 *)(ADDR_WATCHDOG_WDT_KICK))

#define ADDR_WATCHDOG_WDT_COUNT                                  0x4000040C
#define MMCR_WATCHDOG_WDT_COUNT                                  (*(VUINT16 *)(ADDR_WATCHDOG_WDT_COUNT))

/***************************************************************
*                            ACPI PM1
***************************************************************/
#define ADDR_ACPI_0_PM1_STATUS_1                                 0x400F1500
#define MMCR_ACPI_0_PM1_STATUS_1                                 (*(VUINT8 *)(ADDR_ACPI_0_PM1_STATUS_1))

#define ADDR_ACPI_0_PM1_STATUS_2                                 0x400F1501
#define MMCR_ACPI_0_PM1_STATUS_2                                 (*(VUINT8 *)(ADDR_ACPI_0_PM1_STATUS_2))

#define ADDR_ACPI_0_PM1_ENABLE_1                                 0x400F1502
#define MMCR_ACPI_0_PM1_ENABLE_1                                 (*(VUINT8 *)(ADDR_ACPI_0_PM1_ENABLE_1))

#define ADDR_ACPI_0_PM1_ENABLE_2                                 0x400F1503
#define MMCR_ACPI_0_PM1_ENABLE_2                                 (*(VUINT8 *)(ADDR_ACPI_0_PM1_ENABLE_2))

#define ADDR_ACPI_0_PM1_CONTROL_1                                0x400F1504
#define MMCR_ACPI_0_PM1_CONTROL_1                                (*(VUINT8 *)(ADDR_ACPI_0_PM1_CONTROL_1))

#define ADDR_ACPI_0_PM1_CONTROL_2                                0x400F1505
#define MMCR_ACPI_0_PM1_CONTROL_2                                (*(VUINT8 *)(ADDR_ACPI_0_PM1_CONTROL_2))

#define ADDR_ACPI_0_PM2_CONTROL_1                                0x400F1506
#define MMCR_ACPI_0_PM2_CONTROL_1                                (*(VUINT8 *)(ADDR_ACPI_0_PM2_CONTROL_1))

#define ADDR_ACPI_0_PM2_CONTROL_2                                0x400F1507
#define MMCR_ACPI_0_PM2_CONTROL_2                                (*(VUINT8 *)(ADDR_ACPI_0_PM2_CONTROL_2))

#define ADDR_ACPI_0_PM1_EC_PM_STATUS                             0x400F1510
#define MMCR_ACPI_0_PM1_EC_PM_STATUS                             (*(VUINT8 *)(ADDR_ACPI_0_PM1_EC_PM_STATUS))

/***************************************************************
*                            EC GP-SPI
***************************************************************/
#define ADDR_EC_1_SPI_CLOCK_GENERATOR                            0x40009498
#define MMCR_EC_1_SPI_CLOCK_GENERATOR                            (*(VUINT32 *)(ADDR_EC_1_SPI_CLOCK_GENERATOR))

#define ADDR_EC_1_SPI_CLOCK_CONTROL                              0x40009494
#define MMCR_EC_1_SPI_CLOCK_CONTROL                              (*(VUINT32 *)(ADDR_EC_1_SPI_CLOCK_CONTROL))

#define ADDR_EC_1_SPI_RX_DATA                                    0x40009490
#define MMCR_EC_1_SPI_RX_DATA                                    (*(VUINT32 *)(ADDR_EC_1_SPI_RX_DATA))

#define ADDR_EC_1_SPI_TX_DATA                                    0x4000948C
#define MMCR_EC_1_SPI_TX_DATA                                    (*(VUINT32 *)(ADDR_EC_1_SPI_TX_DATA))

#define ADDR_EC_1_SPI_STATUS                                     0x40009488
#define MMCR_EC_1_SPI_STATUS                                     (*(VUINT32 *)(ADDR_EC_1_SPI_STATUS))

#define ADDR_EC_1_SPI_CONTROL                                    0x40009484
#define MMCR_EC_1_SPI_CONTROL                                    (*(VUINT32 *)(ADDR_EC_1_SPI_CONTROL))

#define ADDR_EC_1_SPI_ENABLE                                     0x40009480
#define MMCR_EC_1_SPI_ENABLE                                     (*(VUINT32 *)(ADDR_EC_1_SPI_ENABLE))

#define ADDR_EC_0_SPI_ENABLE                                     0x40009400
#define MMCR_EC_0_SPI_ENABLE                                     (*(VUINT32 *)(ADDR_EC_0_SPI_ENABLE))

#define ADDR_EC_0_SPI_CONTROL                                    0x40009404
#define MMCR_EC_0_SPI_CONTROL                                    (*(VUINT32 *)(ADDR_EC_0_SPI_CONTROL))

#define ADDR_EC_0_SPI_STATUS                                     0x40009408
#define MMCR_EC_0_SPI_STATUS                                     (*(VUINT32 *)(ADDR_EC_0_SPI_STATUS))

#define ADDR_EC_0_SPI_TX_DATA                                    0x4000940C
#define MMCR_EC_0_SPI_TX_DATA                                    (*(VUINT32 *)(ADDR_EC_0_SPI_TX_DATA))

#define ADDR_EC_0_SPI_RX_DATA                                    0x40009410
#define MMCR_EC_0_SPI_RX_DATA                                    (*(VUINT32 *)(ADDR_EC_0_SPI_RX_DATA))

#define ADDR_EC_0_SPI_CLOCK_CONTROL                              0x40009414
#define MMCR_EC_0_SPI_CLOCK_CONTROL                              (*(VUINT32 *)(ADDR_EC_0_SPI_CLOCK_CONTROL))

#define ADDR_EC_0_SPI_CLOCK_GENERATOR                            0x40009418
#define MMCR_EC_0_SPI_CLOCK_GENERATOR                            (*(VUINT32 *)(ADDR_EC_0_SPI_CLOCK_GENERATOR))

/***************************************************************
*                            Mailbox Registers Interface
***************************************************************/
#define ADDR_MAILBOX_HOST_TO_EC_MAILBOX                          0x400F2500
#define MMCR_MAILBOX_HOST_TO_EC_MAILBOX                          (*(VUINT32 *)(ADDR_MAILBOX_HOST_TO_EC_MAILBOX))

#define ADDR_MAILBOX_EC_TO_HOST_MAILBOX                          0x400F2504
#define MMCR_MAILBOX_EC_TO_HOST_MAILBOX                          (*(VUINT32 *)(ADDR_MAILBOX_EC_TO_HOST_MAILBOX))

#define ADDR_MAILBOX_SMI_INTERRUPT_SOURCE                        0x400F2508
#define MMCR_MAILBOX_SMI_INTERRUPT_SOURCE                        (*(VUINT32 *)(ADDR_MAILBOX_SMI_INTERRUPT_SOURCE))

#define ADDR_MAILBOX_SMI_INTERRUPT_MASK                          0x400F250C
#define MMCR_MAILBOX_SMI_INTERRUPT_MASK                          (*(VUINT32 *)(ADDR_MAILBOX_SMI_INTERRUPT_MASK))

#define ADDR_MAILBOX_3_0                                         0x400F2510
#define MMCR_MAILBOX_3_0                                         (*(VUINT32 *)(ADDR_MAILBOX_3_0))

#define ADDR_MAILBOX_7_4                                         0x400F2514
#define MMCR_MAILBOX_7_4                                         (*(VUINT32 *)(ADDR_MAILBOX_7_4))

#define ADDR_MAILBOX_BH_8                                        0x400F2518
#define MMCR_MAILBOX_BH_8                                        (*(VUINT32 *)(ADDR_MAILBOX_BH_8))

#define ADDR_MAILBOX_FH_CH                                       0x400F251C
#define MMCR_MAILBOX_FH_CH                                       (*(VUINT32 *)(ADDR_MAILBOX_FH_CH))

#define ADDR_MAILBOX_13H_10H                                     0x400F2520
#define MMCR_MAILBOX_13H_10H                                     (*(VUINT32 *)(ADDR_MAILBOX_13H_10H))

#define ADDR_MAILBOX_17H_14H                                     0x400F2524
#define MMCR_MAILBOX_17H_14H                                     (*(VUINT32 *)(ADDR_MAILBOX_17H_14H))

#define ADDR_MAILBOX_1BH_18H                                     0x400F2528
#define MMCR_MAILBOX_1BH_18H                                     (*(VUINT32 *)(ADDR_MAILBOX_1BH_18H))

#define ADDR_MAILBOX_1FH_1CH                                     0x400F252C
#define MMCR_MAILBOX_1FH_1CH                                     (*(VUINT32 *)(ADDR_MAILBOX_1FH_1CH))

/***************************************************************
*                            Hibernation Timer
***************************************************************/
#define ADDR_HIBERNATION_0_HTIMER_X_PRELOAD                      0x40009800
#define MMCR_HIBERNATION_0_HTIMER_X_PRELOAD                      (*(VUINT16 *)(ADDR_HIBERNATION_0_HTIMER_X_PRELOAD))

#define ADDR_HIBERNATION_0_TIMER_X_CONTROL                       0x40009804
#define MMCR_HIBERNATION_0_TIMER_X_CONTROL                       (*(VUINT16 *)(ADDR_HIBERNATION_0_TIMER_X_CONTROL))

#define ADDR_HIBERNATION_0_TIMER_X_COUNT                         0x40009808
#define MMCR_HIBERNATION_0_TIMER_X_COUNT                         (*(VUINT16 *)(ADDR_HIBERNATION_0_TIMER_X_COUNT))

/***************************************************************
*                            UART
***************************************************************/
#define ADDR_M16C550A_UART_ACTIVATE                              0x400F1F30
#define MMCR_M16C550A_UART_ACTIVATE                              (*(VUINT8 *)(ADDR_M16C550A_UART_ACTIVATE))

#define ADDR_M16C550A_UART_CONFIG_SELECT                         0x400F1FF0
#define MMCR_M16C550A_UART_CONFIG_SELECT                         (*(VUINT8 *)(ADDR_M16C550A_UART_CONFIG_SELECT))

#define ADDR_M16C550A_UART_PROGRAMMABLE_BAUD_RATE_GENERATOR_LSB  0x400F1D00
#define MMCR_M16C550A_UART_PROGRAMMABLE_BAUD_RATE_GENERATOR_LSB  (*(VUINT8 *)(ADDR_M16C550A_UART_PROGRAMMABLE_BAUD_RATE_GENERATOR_LSB))

#define ADDR_M16C550A_UART_RECEIVE_BUFFER                        0x400F1D00
#define MMCR_M16C550A_UART_RECEIVE_BUFFER                        (*(VUINT8 *)(ADDR_M16C550A_UART_RECEIVE_BUFFER))

#define ADDR_M16C550A_UART_TRANSMIT_BUFFER                       0x400F1D00
#define MMCR_M16C550A_UART_TRANSMIT_BUFFER                       (*(VUINT8 *)(ADDR_M16C550A_UART_TRANSMIT_BUFFER))

#define ADDR_M16C550A_UART_PROGRAMMABLE_BAUD_RATE_GENERATOR_MSB  0x400F1D01
#define MMCR_M16C550A_UART_PROGRAMMABLE_BAUD_RATE_GENERATOR_MSB  (*(VUINT8 *)(ADDR_M16C550A_UART_PROGRAMMABLE_BAUD_RATE_GENERATOR_MSB))

#define ADDR_M16C550A_UART_INTERRUPT_ENABLE                      0x400F1D01
#define MMCR_M16C550A_UART_INTERRUPT_ENABLE                      (*(VUINT8 *)(ADDR_M16C550A_UART_INTERRUPT_ENABLE))

#define ADDR_M16C550A_UART_FIFO_CONTROL                          0x400F1D02
#define MMCR_M16C550A_UART_FIFO_CONTROL                          (*(VUINT8 *)(ADDR_M16C550A_UART_FIFO_CONTROL))

#define ADDR_M16C550A_UART_INTERRUPT_IDENTIFICATION              0x400F1D02
#define MMCR_M16C550A_UART_INTERRUPT_IDENTIFICATION              (*(VUINT8 *)(ADDR_M16C550A_UART_INTERRUPT_IDENTIFICATION))

#define ADDR_M16C550A_UART_LINE_CONTROL                          0x400F1D03
#define MMCR_M16C550A_UART_LINE_CONTROL                          (*(VUINT8 *)(ADDR_M16C550A_UART_LINE_CONTROL))

#define ADDR_M16C550A_UART_MODEM_CONTROL                         0x400F1D04
#define MMCR_M16C550A_UART_MODEM_CONTROL                         (*(VUINT8 *)(ADDR_M16C550A_UART_MODEM_CONTROL))

#define ADDR_M16C550A_UART_LINE_STATUS                           0x400F1D05
#define MMCR_M16C550A_UART_LINE_STATUS                           (*(VUINT8 *)(ADDR_M16C550A_UART_LINE_STATUS))

#define ADDR_M16C550A_UART_MODEM_STATUS                          0x400F1D06
#define MMCR_M16C550A_UART_MODEM_STATUS                          (*(VUINT8 *)(ADDR_M16C550A_UART_MODEM_STATUS))

#define ADDR_M16C550A_UART_SCRATCHPAD                            0x400F1D07
#define MMCR_M16C550A_UART_SCRATCHPAD                            (*(VUINT8 *)(ADDR_M16C550A_UART_SCRATCHPAD))

/***************************************************************
*                            TACH
***************************************************************/
#define ADDR_TACH_0_CONTROL                                      0x40006000
#define MMCR_TACH_0_CONTROL                                      (*(VUINT32 *)(ADDR_TACH_0_CONTROL))

#define ADDR_TACH_0_STATUS                                       0x40006004
#define MMCR_TACH_0_STATUS                                       (*(VUINT32 *)(ADDR_TACH_0_STATUS))

#define ADDR_TACH_0_HIGH_LIMIT                                   0x40006008
#define MMCR_TACH_0_HIGH_LIMIT                                   (*(VUINT32 *)(ADDR_TACH_0_HIGH_LIMIT))

#define ADDR_TACH_0_LOW_LIMIT                                    0x4000600C
#define MMCR_TACH_0_LOW_LIMIT                                    (*(VUINT32 *)(ADDR_TACH_0_LOW_LIMIT))

#define ADDR_TACH_1_CONTROL                                      0x40006010
#define MMCR_TACH_1_CONTROL                                      (*(VUINT32 *)(ADDR_TACH_1_CONTROL))

#define ADDR_TACH_1_STATUS                                       0x40006014
#define MMCR_TACH_1_STATUS                                       (*(VUINT32 *)(ADDR_TACH_1_STATUS))

#define ADDR_TACH_1_HIGH_LIMIT                                   0x40006018
#define MMCR_TACH_1_HIGH_LIMIT                                   (*(VUINT32 *)(ADDR_TACH_1_HIGH_LIMIT))

#define ADDR_TACH_1_LOW_LIMIT                                    0x4000601C
#define MMCR_TACH_1_LOW_LIMIT                                    (*(VUINT32 *)(ADDR_TACH_1_LOW_LIMIT))

/***************************************************************
*                            Global Config Regs Basic
***************************************************************/
#define ADDR_GLOBAL_LOGICAL_DEVICE_NUMBER                        0x400FFF07
#define MMCR_GLOBAL_LOGICAL_DEVICE_NUMBER                        (*(VUINT8 *)(ADDR_GLOBAL_LOGICAL_DEVICE_NUMBER))

#define ADDR_GLOBAL_DEVICE_ID                                    0x400FFF20
#define MMCR_GLOBAL_DEVICE_ID                                    (*(VUINT8 *)(ADDR_GLOBAL_DEVICE_ID))

#define ADDR_GLOBAL_DEVICE_REVISION_HARD_WIRED                   0x400FFF21
#define MMCR_GLOBAL_DEVICE_REVISION_HARD_WIRED                   (*(VUINT8 *)(ADDR_GLOBAL_DEVICE_REVISION_HARD_WIRED))

#define ADDR_GLOBAL_GCR_BUILD                                    0x400FFF28
#define MMCR_GLOBAL_GCR_BUILD                                    (*(VUINT16 *)(ADDR_GLOBAL_GCR_BUILD))

#define ADDR_GLOBAL_GCR_SCRATCH                                  0x400FFF2C
#define MMCR_GLOBAL_GCR_SCRATCH                                  (*(VUINT32 *)(ADDR_GLOBAL_GCR_SCRATCH))

/***************************************************************
*                            Trace FIFO Debug Port
***************************************************************/
#define ADDR_TRACE_DATA                                          0x40008C00
#define MMCR_TRACE_DATA                                          (*(VUINT32 *)(ADDR_TRACE_DATA))

#define ADDR_TRACE_CONTROL                                       0x40008C04
#define MMCR_TRACE_CONTROL                                       (*(VUINT32 *)(ADDR_TRACE_CONTROL))

/***************************************************************
*                            STAP
***************************************************************/
#define ADDR_STAP_MESSAGE_OBF                                    0x40080000
#define MMCR_STAP_MESSAGE_OBF                                    (*(VUINT32 *)(ADDR_STAP_MESSAGE_OBF))

#define ADDR_STAP_MESSAGE_IBF                                    0x40080004
#define MMCR_STAP_MESSAGE_IBF                                    (*(VUINT32 *)(ADDR_STAP_MESSAGE_IBF))

#define ADDR_STAP_OBF_STATUS                                     0x40080008
#define MMCR_STAP_OBF_STATUS                                     (*(VUINT8 *)(ADDR_STAP_OBF_STATUS))

#define ADDR_STAP_IBF_STATUS                                     0x40080009
#define MMCR_STAP_IBF_STATUS                                     (*(VUINT8 *)(ADDR_STAP_IBF_STATUS))

#define ADDR_STAP_DBG_CTRL                                       0x4008000C
#define MMCR_STAP_DBG_CTRL                                       (*(VUINT8 *)(ADDR_STAP_DBG_CTRL))

/***************************************************************
*                            EMI
***************************************************************/
#define ADDR_IMAP_EMI_HOST_TO_EC_MAILBOX                         0x400F0100
#define MMCR_IMAP_EMI_HOST_TO_EC_MAILBOX                         (*(VUINT8 *)(ADDR_IMAP_EMI_HOST_TO_EC_MAILBOX))

#define ADDR_IMAP_EC_TO_HOST_MAILBOX                             0x400F0101
#define MMCR_IMAP_EC_TO_HOST_MAILBOX                             (*(VUINT8 *)(ADDR_IMAP_EC_TO_HOST_MAILBOX))

#define ADDR_IMAP_MEMORY_BASE_ADDRESS_0                          0x400F0104
#define MMCR_IMAP_MEMORY_BASE_ADDRESS_0                          (*(VUINT32 *)(ADDR_IMAP_MEMORY_BASE_ADDRESS_0))

#define ADDR_IMAP_MEMORY_READ_LIMIT_0                            0x400F0108
#define MMCR_IMAP_MEMORY_READ_LIMIT_0                            (*(VUINT16 *)(ADDR_IMAP_MEMORY_READ_LIMIT_0))

#define ADDR_IMAP_MEMORY_WRITE_LIMIT_0                           0x400F010A
#define MMCR_IMAP_MEMORY_WRITE_LIMIT_0                           (*(VUINT16 *)(ADDR_IMAP_MEMORY_WRITE_LIMIT_0))

#define ADDR_IMAP_MEMORY_BASE_ADDRESS_1                          0x400F010C
#define MMCR_IMAP_MEMORY_BASE_ADDRESS_1                          (*(VUINT32 *)(ADDR_IMAP_MEMORY_BASE_ADDRESS_1))

#define ADDR_IMAP_MEMORY_READ_LIMIT_1                            0x400F0110
#define MMCR_IMAP_MEMORY_READ_LIMIT_1                            (*(VUINT16 *)(ADDR_IMAP_MEMORY_READ_LIMIT_1))

#define ADDR_IMAP_MEMORY_WRITE_LIMIT_1                           0x400F0112
#define MMCR_IMAP_MEMORY_WRITE_LIMIT_1                           (*(VUINT16 *)(ADDR_IMAP_MEMORY_WRITE_LIMIT_1))

#define ADDR_IMAP_INTERRUPT_SET                                  0x400F0114
#define MMCR_IMAP_INTERRUPT_SET                                  (*(VUINT16 *)(ADDR_IMAP_INTERRUPT_SET))

#define ADDR_IMAP_HOST_CLEAR_ENABLE                              0x400F0116
#define MMCR_IMAP_HOST_CLEAR_ENABLE                              (*(VUINT16 *)(ADDR_IMAP_HOST_CLEAR_ENABLE))

/***************************************************************
*                            Blinking/Breathing PWM
***************************************************************/
#define ADDR_LED_3_UPDATE_INTERVAL                               0x4000BB10
#define MMCR_LED_3_UPDATE_INTERVAL                               (*(VUINT32 *)(ADDR_LED_3_UPDATE_INTERVAL))

#define ADDR_LED_3_UPDATE_STEPSIZE                               0x4000BB0C
#define MMCR_LED_3_UPDATE_STEPSIZE                               (*(VUINT32 *)(ADDR_LED_3_UPDATE_STEPSIZE))

#define ADDR_LED_3_DELAY                                         0x4000BB08
#define MMCR_LED_3_DELAY                                         (*(VUINT32 *)(ADDR_LED_3_DELAY))

#define ADDR_LED_3_LIMITS                                        0x4000BB04
#define MMCR_LED_3_LIMITS                                        (*(VUINT32 *)(ADDR_LED_3_LIMITS))

#define ADDR_LED_3_CONFIGURATION                                 0x4000BB00
#define MMCR_LED_3_CONFIGURATION                                 (*(VUINT32 *)(ADDR_LED_3_CONFIGURATION))

#define ADDR_LED_2_UPDATE_INTERVAL                               0x4000BA10
#define MMCR_LED_2_UPDATE_INTERVAL                               (*(VUINT32 *)(ADDR_LED_2_UPDATE_INTERVAL))

#define ADDR_LED_2_UPDATE_STEPSIZE                               0x4000BA0C
#define MMCR_LED_2_UPDATE_STEPSIZE                               (*(VUINT32 *)(ADDR_LED_2_UPDATE_STEPSIZE))

#define ADDR_LED_2_DELAY                                         0x4000BA08
#define MMCR_LED_2_DELAY                                         (*(VUINT32 *)(ADDR_LED_2_DELAY))

#define ADDR_LED_2_LIMITS                                        0x4000BA04
#define MMCR_LED_2_LIMITS                                        (*(VUINT32 *)(ADDR_LED_2_LIMITS))

#define ADDR_LED_2_CONFIGURATION                                 0x4000BA00
#define MMCR_LED_2_CONFIGURATION                                 (*(VUINT32 *)(ADDR_LED_2_CONFIGURATION))

#define ADDR_LED_1_CONFIGURATION                                 0x4000B900
#define MMCR_LED_1_CONFIGURATION                                 (*(VUINT32 *)(ADDR_LED_1_CONFIGURATION))

#define ADDR_LED_1_LIMITS                                        0x4000B904
#define MMCR_LED_1_LIMITS                                        (*(VUINT32 *)(ADDR_LED_1_LIMITS))

#define ADDR_LED_1_DELAY                                         0x4000B908
#define MMCR_LED_1_DELAY                                         (*(VUINT32 *)(ADDR_LED_1_DELAY))

#define ADDR_LED_1_UPDATE_STEPSIZE                               0x4000B90C
#define MMCR_LED_1_UPDATE_STEPSIZE                               (*(VUINT32 *)(ADDR_LED_1_UPDATE_STEPSIZE))

#define ADDR_LED_1_UPDATE_INTERVAL                               0x4000B910
#define MMCR_LED_1_UPDATE_INTERVAL                               (*(VUINT32 *)(ADDR_LED_1_UPDATE_INTERVAL))

#define ADDR_LED_0_CONFIGURATION                                 0x4000B800
#define MMCR_LED_0_CONFIGURATION                                 (*(VUINT32 *)(ADDR_LED_0_CONFIGURATION))

#define ADDR_LED_0_LIMITS                                        0x4000B804
#define MMCR_LED_0_LIMITS                                        (*(VUINT32 *)(ADDR_LED_0_LIMITS))

#define ADDR_LED_0_DELAY                                         0x4000B808
#define MMCR_LED_0_DELAY                                         (*(VUINT32 *)(ADDR_LED_0_DELAY))

#define ADDR_LED_0_UPDATE_STEPSIZE                               0x4000B80C
#define MMCR_LED_0_UPDATE_STEPSIZE                               (*(VUINT32 *)(ADDR_LED_0_UPDATE_STEPSIZE))

#define ADDR_LED_0_UPDATE_INTERVAL                               0x4000B810
#define MMCR_LED_0_UPDATE_INTERVAL                               (*(VUINT32 *)(ADDR_LED_0_UPDATE_INTERVAL))

/***************************************************************
*                            SMSC BC-Link Master
***************************************************************/
#define ADDR_BC_LINK_STATUS                                      0x4000BC00
#define MMCR_BC_LINK_STATUS                                      (*(VUINT8 *)(ADDR_BC_LINK_STATUS))

#define ADDR_BC_LINK_ADDRESS                                     0x4000BC04
#define MMCR_BC_LINK_ADDRESS                                     (*(VUINT8 *)(ADDR_BC_LINK_ADDRESS))

#define ADDR_BC_LINK_DATA                                        0x4000BC08
#define MMCR_BC_LINK_DATA                                        (*(VUINT8 *)(ADDR_BC_LINK_DATA))

#define ADDR_BC_LINK_CLOCK_SELECT                                0x4000BC0C
#define MMCR_BC_LINK_CLOCK_SELECT                                (*(VUINT8 *)(ADDR_BC_LINK_CLOCK_SELECT))

/***************************************************************
*                            Basic Timer
***************************************************************/
#define ADDR_BASIC_0_TIMER_COUNT                                 0x40000C00
#define MMCR_BASIC_0_TIMER_COUNT                                 (*(VUINT32 *)(ADDR_BASIC_0_TIMER_COUNT))

#define ADDR_BASIC_0_TIMER_PRELOAD                               0x40000C04
#define MMCR_BASIC_0_TIMER_PRELOAD                               (*(VUINT32 *)(ADDR_BASIC_0_TIMER_PRELOAD))

#define ADDR_BASIC_0_TIMER_STATUS                                0x40000C08
#define MMCR_BASIC_0_TIMER_STATUS                                (*(VUINT32 *)(ADDR_BASIC_0_TIMER_STATUS))

#define ADDR_BASIC_0_TIMER_INTERRUPT_ENABLE                      0x40000C0C
#define MMCR_BASIC_0_TIMER_INTERRUPT_ENABLE                      (*(VUINT32 *)(ADDR_BASIC_0_TIMER_INTERRUPT_ENABLE))

#define ADDR_BASIC_0_TIMER_CONTROL                               0x40000C10
#define MMCR_BASIC_0_TIMER_CONTROL                               (*(VUINT32 *)(ADDR_BASIC_0_TIMER_CONTROL))

#define ADDR_BASIC_1_TIMER_COUNT                                 0x40000C20
#define MMCR_BASIC_1_TIMER_COUNT                                 (*(VUINT32 *)(ADDR_BASIC_1_TIMER_COUNT))

#define ADDR_BASIC_1_TIMER_PRELOAD                               0x40000C24
#define MMCR_BASIC_1_TIMER_PRELOAD                               (*(VUINT32 *)(ADDR_BASIC_1_TIMER_PRELOAD))

#define ADDR_BASIC_1_TIMER_STATUS                                0x40000C28
#define MMCR_BASIC_1_TIMER_STATUS                                (*(VUINT32 *)(ADDR_BASIC_1_TIMER_STATUS))

#define ADDR_BASIC_1_TIMER_INTERRUPT_ENABLE                      0x40000C2C
#define MMCR_BASIC_1_TIMER_INTERRUPT_ENABLE                      (*(VUINT32 *)(ADDR_BASIC_1_TIMER_INTERRUPT_ENABLE))

#define ADDR_BASIC_1_TIMER_CONTROL                               0x40000C30
#define MMCR_BASIC_1_TIMER_CONTROL                               (*(VUINT32 *)(ADDR_BASIC_1_TIMER_CONTROL))

#define ADDR_BASIC_2_TIMER_COUNT                                 0x40000C40
#define MMCR_BASIC_2_TIMER_COUNT                                 (*(VUINT32 *)(ADDR_BASIC_2_TIMER_COUNT))

#define ADDR_BASIC_2_TIMER_PRELOAD                               0x40000C44
#define MMCR_BASIC_2_TIMER_PRELOAD                               (*(VUINT32 *)(ADDR_BASIC_2_TIMER_PRELOAD))

#define ADDR_BASIC_2_TIMER_STATUS                                0x40000C48
#define MMCR_BASIC_2_TIMER_STATUS                                (*(VUINT32 *)(ADDR_BASIC_2_TIMER_STATUS))

#define ADDR_BASIC_2_TIMER_INTERRUPT_ENABLE                      0x40000C4C
#define MMCR_BASIC_2_TIMER_INTERRUPT_ENABLE                      (*(VUINT32 *)(ADDR_BASIC_2_TIMER_INTERRUPT_ENABLE))

#define ADDR_BASIC_2_TIMER_CONTROL                               0x40000C50
#define MMCR_BASIC_2_TIMER_CONTROL                               (*(VUINT32 *)(ADDR_BASIC_2_TIMER_CONTROL))

#define ADDR_BASIC_3_TIMER_COUNT                                 0x40000C60
#define MMCR_BASIC_3_TIMER_COUNT                                 (*(VUINT32 *)(ADDR_BASIC_3_TIMER_COUNT))

#define ADDR_BASIC_3_TIMER_PRELOAD                               0x40000C64
#define MMCR_BASIC_3_TIMER_PRELOAD                               (*(VUINT32 *)(ADDR_BASIC_3_TIMER_PRELOAD))

#define ADDR_BASIC_3_TIMER_STATUS                                0x40000C68
#define MMCR_BASIC_3_TIMER_STATUS                                (*(VUINT32 *)(ADDR_BASIC_3_TIMER_STATUS))

#define ADDR_BASIC_3_TIMER_INTERRUPT_ENABLE                      0x40000C6C
#define MMCR_BASIC_3_TIMER_INTERRUPT_ENABLE                      (*(VUINT32 *)(ADDR_BASIC_3_TIMER_INTERRUPT_ENABLE))

#define ADDR_BASIC_3_TIMER_CONTROL                               0x40000C70
#define MMCR_BASIC_3_TIMER_CONTROL                               (*(VUINT32 *)(ADDR_BASIC_3_TIMER_CONTROL))

#define ADDR_BASIC_4_TIMER_COUNT                                 0x40000C80
#define MMCR_BASIC_4_TIMER_COUNT                                 (*(VUINT32 *)(ADDR_BASIC_4_TIMER_COUNT))

#define ADDR_BASIC_4_TIMER_PRELOAD                               0x40000C84
#define MMCR_BASIC_4_TIMER_PRELOAD                               (*(VUINT32 *)(ADDR_BASIC_4_TIMER_PRELOAD))

#define ADDR_BASIC_4_TIMER_STATUS                                0x40000C88
#define MMCR_BASIC_4_TIMER_STATUS                                (*(VUINT32 *)(ADDR_BASIC_4_TIMER_STATUS))

#define ADDR_BASIC_4_TIMER_INTERRUPT_ENABLE                      0x40000C8C
#define MMCR_BASIC_4_TIMER_INTERRUPT_ENABLE                      (*(VUINT32 *)(ADDR_BASIC_4_TIMER_INTERRUPT_ENABLE))

#define ADDR_BASIC_4_TIMER_CONTROL                               0x40000C90
#define MMCR_BASIC_4_TIMER_CONTROL                               (*(VUINT32 *)(ADDR_BASIC_4_TIMER_CONTROL))

#define ADDR_BASIC_5_TIMER_COUNT                                 0x40000CA0
#define MMCR_BASIC_5_TIMER_COUNT                                 (*(VUINT32 *)(ADDR_BASIC_5_TIMER_COUNT))

#define ADDR_BASIC_5_TIMER_PRELOAD                               0x40000CA4
#define MMCR_BASIC_5_TIMER_PRELOAD                               (*(VUINT32 *)(ADDR_BASIC_5_TIMER_PRELOAD))

#define ADDR_BASIC_5_TIMER_STATUS                                0x40000CA8
#define MMCR_BASIC_5_TIMER_STATUS                                (*(VUINT32 *)(ADDR_BASIC_5_TIMER_STATUS))

#define ADDR_BASIC_5_TIMER_INTERRUPT_ENABLE                      0x40000CAC
#define MMCR_BASIC_5_TIMER_INTERRUPT_ENABLE                      (*(VUINT32 *)(ADDR_BASIC_5_TIMER_INTERRUPT_ENABLE))

#define ADDR_BASIC_5_TIMER_CONTROL                               0x40000CB0
#define MMCR_BASIC_5_TIMER_CONTROL                               (*(VUINT32 *)(ADDR_BASIC_5_TIMER_CONTROL))

/***************************************************************
*                            INTS
***************************************************************/
#define ADDR_EC_GIRQ8_SOURCE                                     0x4000C000
#define MMCR_EC_GIRQ8_SOURCE                                     (*(VUINT32 *)(ADDR_EC_GIRQ8_SOURCE))

#define ADDR_EC_GIRQ8_ENABLE_SET                                 0x4000C004
#define MMCR_EC_GIRQ8_ENABLE_SET                                 (*(VUINT32 *)(ADDR_EC_GIRQ8_ENABLE_SET))

#define ADDR_EC_GIRQ8_RESULT                                     0x4000C008
#define MMCR_EC_GIRQ8_RESULT                                     (*(VUINT32 *)(ADDR_EC_GIRQ8_RESULT))

#define ADDR_EC_GIRQ8_ENABLE_CLEAR                               0x4000C00C
#define MMCR_EC_GIRQ8_ENABLE_CLEAR                               (*(VUINT32 *)(ADDR_EC_GIRQ8_ENABLE_CLEAR))

#define ADDR_EC_GIRQ9_SOURCE                                     0x4000C014
#define MMCR_EC_GIRQ9_SOURCE                                     (*(VUINT32 *)(ADDR_EC_GIRQ9_SOURCE))

#define ADDR_EC_GIRQ9_ENABLE_SET                                 0x4000C018
#define MMCR_EC_GIRQ9_ENABLE_SET                                 (*(VUINT32 *)(ADDR_EC_GIRQ9_ENABLE_SET))

#define ADDR_EC_GIRQ9_RESULT                                     0x4000C01C
#define MMCR_EC_GIRQ9_RESULT                                     (*(VUINT32 *)(ADDR_EC_GIRQ9_RESULT))

#define ADDR_EC_GIRQ9_ENABLE_CLEAR                               0x4000C020
#define MMCR_EC_GIRQ9_ENABLE_CLEAR                               (*(VUINT32 *)(ADDR_EC_GIRQ9_ENABLE_CLEAR))

#define ADDR_EC_GIRQ10_SOURCE                                    0x4000C028
#define MMCR_EC_GIRQ10_SOURCE                                    (*(VUINT32 *)(ADDR_EC_GIRQ10_SOURCE))

#define ADDR_EC_GIRQ10_ENABLE_SET                                0x4000C02C
#define MMCR_EC_GIRQ10_ENABLE_SET                                (*(VUINT32 *)(ADDR_EC_GIRQ10_ENABLE_SET))

#define ADDR_EC_GIRQ10_RESULT                                    0x4000C030
#define MMCR_EC_GIRQ10_RESULT                                    (*(VUINT32 *)(ADDR_EC_GIRQ10_RESULT))

#define ADDR_EC_GIRQ10_ENABLE_CLEAR                              0x4000C034
#define MMCR_EC_GIRQ10_ENABLE_CLEAR                              (*(VUINT32 *)(ADDR_EC_GIRQ10_ENABLE_CLEAR))

#define ADDR_EC_GIRQ11_SOURCE                                    0x4000C03C
#define MMCR_EC_GIRQ11_SOURCE                                    (*(VUINT32 *)(ADDR_EC_GIRQ11_SOURCE))

#define ADDR_EC_GIRQ11_ENABLE_SET                                0x4000C040
#define MMCR_EC_GIRQ11_ENABLE_SET                                (*(VUINT32 *)(ADDR_EC_GIRQ11_ENABLE_SET))

#define ADDR_EC_GIRQ11_RESULT                                    0x4000C044
#define MMCR_EC_GIRQ11_RESULT                                    (*(VUINT32 *)(ADDR_EC_GIRQ11_RESULT))

#define ADDR_EC_GIRQ11_ENABLE_CLEAR                              0x4000C048
#define MMCR_EC_GIRQ11_ENABLE_CLEAR                              (*(VUINT32 *)(ADDR_EC_GIRQ11_ENABLE_CLEAR))

#define ADDR_EC_GIRQ12_SOURCE                                    0x4000C050
#define MMCR_EC_GIRQ12_SOURCE                                    (*(VUINT32 *)(ADDR_EC_GIRQ12_SOURCE))

#define ADDR_EC_GIRQ12_ENABLE_SET                                0x4000C054
#define MMCR_EC_GIRQ12_ENABLE_SET                                (*(VUINT32 *)(ADDR_EC_GIRQ12_ENABLE_SET))

#define ADDR_EC_GIRQ12_RESULT                                    0x4000C058
#define MMCR_EC_GIRQ12_RESULT                                    (*(VUINT32 *)(ADDR_EC_GIRQ12_RESULT))

#define ADDR_EC_GIRQ12_ENABLE_CLEAR                              0x4000C05C
#define MMCR_EC_GIRQ12_ENABLE_CLEAR                              (*(VUINT32 *)(ADDR_EC_GIRQ12_ENABLE_CLEAR))

#define ADDR_EC_GIRQ13_SOURCE                                    0x4000C064
#define MMCR_EC_GIRQ13_SOURCE                                    (*(VUINT32 *)(ADDR_EC_GIRQ13_SOURCE))

#define ADDR_EC_GIRQ13_ENABLE_SET                                0x4000C068
#define MMCR_EC_GIRQ13_ENABLE_SET                                (*(VUINT32 *)(ADDR_EC_GIRQ13_ENABLE_SET))

#define ADDR_EC_GIRQ13_RESULT                                    0x4000C06C
#define MMCR_EC_GIRQ13_RESULT                                    (*(VUINT32 *)(ADDR_EC_GIRQ13_RESULT))

#define ADDR_EC_GIRQ13_ENABLE_CLEAR                              0x4000C070
#define MMCR_EC_GIRQ13_ENABLE_CLEAR                              (*(VUINT32 *)(ADDR_EC_GIRQ13_ENABLE_CLEAR))

#define ADDR_EC_GIRQ14_SOURCE                                    0x4000C078
#define MMCR_EC_GIRQ14_SOURCE                                    (*(VUINT32 *)(ADDR_EC_GIRQ14_SOURCE))

#define ADDR_EC_GIRQ14_ENABLE_SET                                0x4000C07C
#define MMCR_EC_GIRQ14_ENABLE_SET                                (*(VUINT32 *)(ADDR_EC_GIRQ14_ENABLE_SET))

#define ADDR_EC_GIRQ14_RESULT                                    0x4000C080
#define MMCR_EC_GIRQ14_RESULT                                    (*(VUINT32 *)(ADDR_EC_GIRQ14_RESULT))

#define ADDR_EC_GIRQ14_ENABLE_CLEAR                              0x4000C084
#define MMCR_EC_GIRQ14_ENABLE_CLEAR                              (*(VUINT32 *)(ADDR_EC_GIRQ14_ENABLE_CLEAR))

#define ADDR_EC_GIRQ15_SOURCE                                    0x4000C08C
#define MMCR_EC_GIRQ15_SOURCE                                    (*(VUINT32 *)(ADDR_EC_GIRQ15_SOURCE))

#define ADDR_EC_GIRQ15_ENABLE_SET                                0x4000C090
#define MMCR_EC_GIRQ15_ENABLE_SET                                (*(VUINT32 *)(ADDR_EC_GIRQ15_ENABLE_SET))

#define ADDR_EC_GIRQ15_RESULT                                    0x4000C094
#define MMCR_EC_GIRQ15_RESULT                                    (*(VUINT32 *)(ADDR_EC_GIRQ15_RESULT))

#define ADDR_EC_GIRQ15_ENABLE_CLEAR                              0x4000C098
#define MMCR_EC_GIRQ15_ENABLE_CLEAR                              (*(VUINT32 *)(ADDR_EC_GIRQ15_ENABLE_CLEAR))

#define ADDR_EC_GIRQ16_SOURCE                                    0x4000C0A0
#define MMCR_EC_GIRQ16_SOURCE                                    (*(VUINT32 *)(ADDR_EC_GIRQ16_SOURCE))

#define ADDR_EC_GIRQ16_ENABLE_SET                                0x4000C0A4
#define MMCR_EC_GIRQ16_ENABLE_SET                                (*(VUINT32 *)(ADDR_EC_GIRQ16_ENABLE_SET))

#define ADDR_EC_GIRQ16_RESULT                                    0x4000C0A8
#define MMCR_EC_GIRQ16_RESULT                                    (*(VUINT32 *)(ADDR_EC_GIRQ16_RESULT))

#define ADDR_EC_GIRQ16_ENABLE_CLEAR                              0x4000C0AC
#define MMCR_EC_GIRQ16_ENABLE_CLEAR                              (*(VUINT32 *)(ADDR_EC_GIRQ16_ENABLE_CLEAR))

#define ADDR_EC_GIRQ17_SOURCE                                    0x4000C0B4
#define MMCR_EC_GIRQ17_SOURCE                                    (*(VUINT32 *)(ADDR_EC_GIRQ17_SOURCE))

#define ADDR_EC_GIRQ17_ENABLE_SET                                0x4000C0B8
#define MMCR_EC_GIRQ17_ENABLE_SET                                (*(VUINT32 *)(ADDR_EC_GIRQ17_ENABLE_SET))

#define ADDR_EC_GIRQ17_RESULT                                    0x4000C0BC
#define MMCR_EC_GIRQ17_RESULT                                    (*(VUINT32 *)(ADDR_EC_GIRQ17_RESULT))

#define ADDR_EC_GIRQ17_ENABLE_CLEAR                              0x4000C0C0
#define MMCR_EC_GIRQ17_ENABLE_CLEAR                              (*(VUINT32 *)(ADDR_EC_GIRQ17_ENABLE_CLEAR))

#define ADDR_EC_GIRQ18_SOURCE                                    0x4000C0C8
#define MMCR_EC_GIRQ18_SOURCE                                    (*(VUINT32 *)(ADDR_EC_GIRQ18_SOURCE))

#define ADDR_EC_GIRQ18_ENABLE_SET                                0x4000C0CC
#define MMCR_EC_GIRQ18_ENABLE_SET                                (*(VUINT32 *)(ADDR_EC_GIRQ18_ENABLE_SET))

#define ADDR_EC_GIRQ18_RESULT                                    0x4000C0D0
#define MMCR_EC_GIRQ18_RESULT                                    (*(VUINT32 *)(ADDR_EC_GIRQ18_RESULT))

#define ADDR_EC_GIRQ18_ENABLE_CLEAR                              0x4000C0D4
#define MMCR_EC_GIRQ18_ENABLE_CLEAR                              (*(VUINT32 *)(ADDR_EC_GIRQ18_ENABLE_CLEAR))

#define ADDR_EC_GIRQ19_SOURCE                                    0x4000C0DC
#define MMCR_EC_GIRQ19_SOURCE                                    (*(VUINT32 *)(ADDR_EC_GIRQ19_SOURCE))

#define ADDR_EC_GIRQ19_ENABLE_SET                                0x4000C0E0
#define MMCR_EC_GIRQ19_ENABLE_SET                                (*(VUINT32 *)(ADDR_EC_GIRQ19_ENABLE_SET))

#define ADDR_EC_GIRQ19_RESULT                                    0x4000C0E4
#define MMCR_EC_GIRQ19_RESULT                                    (*(VUINT32 *)(ADDR_EC_GIRQ19_RESULT))

#define ADDR_EC_GIRQ19_ENABLE_CLEAR                              0x4000C0E8
#define MMCR_EC_GIRQ19_ENABLE_CLEAR                              (*(VUINT32 *)(ADDR_EC_GIRQ19_ENABLE_CLEAR))

#define ADDR_EC_GIRQ20_SOURCE                                    0x4000C0F0
#define MMCR_EC_GIRQ20_SOURCE                                    (*(VUINT32 *)(ADDR_EC_GIRQ20_SOURCE))

#define ADDR_EC_GIRQ20_ENABLE_SET                                0x4000C0F4
#define MMCR_EC_GIRQ20_ENABLE_SET                                (*(VUINT32 *)(ADDR_EC_GIRQ20_ENABLE_SET))

#define ADDR_EC_GIRQ20_RESULT                                    0x4000C0F8
#define MMCR_EC_GIRQ20_RESULT                                    (*(VUINT32 *)(ADDR_EC_GIRQ20_RESULT))

#define ADDR_EC_GIRQ20_ENABLE_CLEAR                              0x4000C0FC
#define MMCR_EC_GIRQ20_ENABLE_CLEAR                              (*(VUINT32 *)(ADDR_EC_GIRQ20_ENABLE_CLEAR))

#define ADDR_EC_GIRQ21_SOURCE                                    0x4000C104
#define MMCR_EC_GIRQ21_SOURCE                                    (*(VUINT32 *)(ADDR_EC_GIRQ21_SOURCE))

#define ADDR_EC_GIRQ21_ENABLE_SET                                0x4000C108
#define MMCR_EC_GIRQ21_ENABLE_SET                                (*(VUINT32 *)(ADDR_EC_GIRQ21_ENABLE_SET))

#define ADDR_EC_GIRQ21_RESULT                                    0x4000C10C
#define MMCR_EC_GIRQ21_RESULT                                    (*(VUINT32 *)(ADDR_EC_GIRQ21_RESULT))

#define ADDR_EC_GIRQ21_ENABLE_CLEAR                              0x4000C110
#define MMCR_EC_GIRQ21_ENABLE_CLEAR                              (*(VUINT32 *)(ADDR_EC_GIRQ21_ENABLE_CLEAR))

#define ADDR_EC_GIRQ22_SOURCE                                    0x4000C118
#define MMCR_EC_GIRQ22_SOURCE                                    (*(VUINT32 *)(ADDR_EC_GIRQ22_SOURCE))

#define ADDR_EC_GIRQ22_ENABLE_SET                                0x4000C11C
#define MMCR_EC_GIRQ22_ENABLE_SET                                (*(VUINT32 *)(ADDR_EC_GIRQ22_ENABLE_SET))

#define ADDR_EC_GIRQ22_RESULT                                    0x4000C120
#define MMCR_EC_GIRQ22_RESULT                                    (*(VUINT32 *)(ADDR_EC_GIRQ22_RESULT))

#define ADDR_EC_GIRQ22_ENABLE_CLEAR                              0x4000C124
#define MMCR_EC_GIRQ22_ENABLE_CLEAR                              (*(VUINT32 *)(ADDR_EC_GIRQ22_ENABLE_CLEAR))

#define ADDR_EC_GIRQ23_SOURCE                                    0x4000C12C
#define MMCR_EC_GIRQ23_SOURCE                                    (*(VUINT32 *)(ADDR_EC_GIRQ23_SOURCE))

#define ADDR_EC_GIRQ23_ENABLE_SET                                0x4000C130
#define MMCR_EC_GIRQ23_ENABLE_SET                                (*(VUINT32 *)(ADDR_EC_GIRQ23_ENABLE_SET))

#define ADDR_EC_GIRQ23_RESULT                                    0x4000C134
#define MMCR_EC_GIRQ23_RESULT                                    (*(VUINT32 *)(ADDR_EC_GIRQ23_RESULT))

#define ADDR_EC_GIRQ23_ENABLE_CLEAR                              0x4000C138
#define MMCR_EC_GIRQ23_ENABLE_CLEAR                              (*(VUINT32 *)(ADDR_EC_GIRQ23_ENABLE_CLEAR))

#define ADDR_EC_BLOCK_ENABLE_SET                                 0x4000C200
#define MMCR_EC_BLOCK_ENABLE_SET                                 (*(VUINT32 *)(ADDR_EC_BLOCK_ENABLE_SET))

#define ADDR_EC_BLOCK_ENABLE_CLEAR                               0x4000C204
#define MMCR_EC_BLOCK_ENABLE_CLEAR                               (*(VUINT32 *)(ADDR_EC_BLOCK_ENABLE_CLEAR))

#define ADDR_EC_BLOCK_IRQ_VECTOR                                 0x4000C208
#define MMCR_EC_BLOCK_IRQ_VECTOR                                 (*(VUINT32 *)(ADDR_EC_BLOCK_IRQ_VECTOR))

/***************************************************************
*                            RPM Fan Control
***************************************************************/
#define ADDR_RPM_FAN_SETTING                                     0x4000A000
#define MMCR_RPM_FAN_SETTING                                     (*(VUINT8 *)(ADDR_RPM_FAN_SETTING))

#define ADDR_RPM_PWM_DIVIDE                                      0x4000A001
#define MMCR_RPM_PWM_DIVIDE                                      (*(VUINT8 *)(ADDR_RPM_PWM_DIVIDE))

#define ADDR_RPM_FAN_CONFIGURATION_1                             0x4000A002
#define MMCR_RPM_FAN_CONFIGURATION_1                             (*(VUINT8 *)(ADDR_RPM_FAN_CONFIGURATION_1))

#define ADDR_RPM_FAN_CONFIGURATION_2                             0x4000A003
#define MMCR_RPM_FAN_CONFIGURATION_2                             (*(VUINT8 *)(ADDR_RPM_FAN_CONFIGURATION_2))

#define ADDR_RPM_GAIN                                            0x4000A005
#define MMCR_RPM_GAIN                                            (*(VUINT8 *)(ADDR_RPM_GAIN))

#define ADDR_RPM_FAN_SPIN_UP_CONFIGURATION                       0x4000A006
#define MMCR_RPM_FAN_SPIN_UP_CONFIGURATION                       (*(VUINT8 *)(ADDR_RPM_FAN_SPIN_UP_CONFIGURATION))

#define ADDR_RPM_FAN_STEP                                        0x4000A007
#define MMCR_RPM_FAN_STEP                                        (*(VUINT8 *)(ADDR_RPM_FAN_STEP))

#define ADDR_RPM_FAN_MINIMUM_DRIVE                               0x4000A008
#define MMCR_RPM_FAN_MINIMUM_DRIVE                               (*(VUINT8 *)(ADDR_RPM_FAN_MINIMUM_DRIVE))

#define ADDR_RPM_VALID_TACH_COUNT                                0x4000A009
#define MMCR_RPM_VALID_TACH_COUNT                                (*(VUINT8 *)(ADDR_RPM_VALID_TACH_COUNT))

#define ADDR_RPM_FAN_DRIVE_FAIL_BAND_LOW_BYTE                    0x4000A00A
#define MMCR_RPM_FAN_DRIVE_FAIL_BAND_LOW_BYTE                    (*(VUINT8 *)(ADDR_RPM_FAN_DRIVE_FAIL_BAND_LOW_BYTE))

#define ADDR_RPM_FAN_DRIVE_FAIL_BAND_HIGH_BYTE                   0x4000A00B
#define MMCR_RPM_FAN_DRIVE_FAIL_BAND_HIGH_BYTE                   (*(VUINT8 *)(ADDR_RPM_FAN_DRIVE_FAIL_BAND_HIGH_BYTE))

#define ADDR_RPM_TACH_TARGET_LOW_BYTE                            0x4000A00C
#define MMCR_RPM_TACH_TARGET_LOW_BYTE                            (*(VUINT8 *)(ADDR_RPM_TACH_TARGET_LOW_BYTE))

#define ADDR_RPM_TACH_TARGET_HIGH_BYTE                           0x4000A00D
#define MMCR_RPM_TACH_TARGET_HIGH_BYTE                           (*(VUINT8 *)(ADDR_RPM_TACH_TARGET_HIGH_BYTE))

#define ADDR_RPM_TACH_READING_LOW_BYTE                           0x4000A00E
#define MMCR_RPM_TACH_READING_LOW_BYTE                           (*(VUINT8 *)(ADDR_RPM_TACH_READING_LOW_BYTE))

#define ADDR_RPM_TACH_READING_HIGH_BYTE                          0x4000A00F
#define MMCR_RPM_TACH_READING_HIGH_BYTE                          (*(VUINT8 *)(ADDR_RPM_TACH_READING_HIGH_BYTE))

#define ADDR_RPM_PWM_DRIVER_BASE_FREQUENCY                       0x4000A010
#define MMCR_RPM_PWM_DRIVER_BASE_FREQUENCY                       (*(VUINT8 *)(ADDR_RPM_PWM_DRIVER_BASE_FREQUENCY))

#define ADDR_RPM_FAN_STATUS                                      0x4000A011
#define MMCR_RPM_FAN_STATUS                                      (*(VUINT8 *)(ADDR_RPM_FAN_STATUS))

#define ADDR_RPM_FAN_TEST                                        0x4000A014
#define MMCR_RPM_FAN_TEST                                        (*(VUINT8 *)(ADDR_RPM_FAN_TEST))

#define ADDR_RPM_FAN_TEST1                                       0x4000A015
#define MMCR_RPM_FAN_TEST1                                       (*(VUINT8 *)(ADDR_RPM_FAN_TEST1))

#define ADDR_RPM_FAN_TEST2                                       0x4000A016
#define MMCR_RPM_FAN_TEST2                                       (*(VUINT8 *)(ADDR_RPM_FAN_TEST2))

#define ADDR_RPM_FAN_TEST3                                       0x4000A017
#define MMCR_RPM_FAN_TEST3                                       (*(VUINT8 *)(ADDR_RPM_FAN_TEST3))

/***************************************************************
*                            V2P (HP ckt#1) 32bit_aligned
***************************************************************/
#define ADDR_V2P_ADC2PWM_OUTPUT_FREQUENCY                        0x40007C80
#define MMCR_V2P_ADC2PWM_OUTPUT_FREQUENCY                        (*(VUINT32 *)(ADDR_V2P_ADC2PWM_OUTPUT_FREQUENCY))

#define ADDR_V2P_ADC2PWM_VOLTAGE_THRESHOLD_LOW                   0x40007C84
#define MMCR_V2P_ADC2PWM_VOLTAGE_THRESHOLD_LOW                   (*(VUINT32 *)(ADDR_V2P_ADC2PWM_VOLTAGE_THRESHOLD_LOW))

#define ADDR_V2P_ADC2PWM_VOLTAGE_THRESHOLD_HIGH                  0x40007C88
#define MMCR_V2P_ADC2PWM_VOLTAGE_THRESHOLD_HIGH                  (*(VUINT32 *)(ADDR_V2P_ADC2PWM_VOLTAGE_THRESHOLD_HIGH))

#define ADDR_V2P_ADC2PWM_DUTY_CYCLE_QUANTA                       0x40007C8C
#define MMCR_V2P_ADC2PWM_DUTY_CYCLE_QUANTA                       (*(VUINT32 *)(ADDR_V2P_ADC2PWM_DUTY_CYCLE_QUANTA))

#define ADDR_V2P_ADC2PWM_DUTY_CYCLE_STATUS                       0x40007C90
#define MMCR_V2P_ADC2PWM_DUTY_CYCLE_STATUS                       (*(VUINT32 *)(ADDR_V2P_ADC2PWM_DUTY_CYCLE_STATUS))

#define ADDR_V2P_ADC2PWM_NOTIFICATION_LIMIT_1                    0x40007C94
#define MMCR_V2P_ADC2PWM_NOTIFICATION_LIMIT_1                    (*(VUINT32 *)(ADDR_V2P_ADC2PWM_NOTIFICATION_LIMIT_1))

#define ADDR_V2P_ADC2PWM_NOTIFICATION_LIMIT_2                    0x40007C98
#define MMCR_V2P_ADC2PWM_NOTIFICATION_LIMIT_2                    (*(VUINT32 *)(ADDR_V2P_ADC2PWM_NOTIFICATION_LIMIT_2))

#define ADDR_V2P_ADC2PWM_CONTROL                                 0x40007C9C
#define MMCR_V2P_ADC2PWM_CONTROL                                 (*(VUINT32 *)(ADDR_V2P_ADC2PWM_CONTROL))

#define ADDR_V2P_LPF_CUT_OFF_FREQUENCY                           0x40007CA0
#define MMCR_V2P_LPF_CUT_OFF_FREQUENCY                           (*(VUINT32 *)(ADDR_V2P_LPF_CUT_OFF_FREQUENCY))

#define ADDR_V2P_TEST                                            0x40007CA4
#define MMCR_V2P_TEST                                            (*(VUINT32 *)(ADDR_V2P_TEST))

#define ADDR_V2P_NOTICE_DATA                                     0x40007CA8
#define MMCR_V2P_NOTICE_DATA                                     (*(VUINT32 *)(ADDR_V2P_NOTICE_DATA))

#define ADDR_V2P_TEST_DATA                                       0x40007CAC
#define MMCR_V2P_TEST_DATA                                       (*(VUINT32 *)(ADDR_V2P_TEST_DATA))

#define ADDR_V2P_COUNTER_START                                   0x40007CB0
#define MMCR_V2P_COUNTER_START                                   (*(VUINT32 *)(ADDR_V2P_COUNTER_START))

#define ADDR_V2P_HYSTERESIS                                      0x40007CB4
#define MMCR_V2P_HYSTERESIS                                      (*(VUINT32 *)(ADDR_V2P_HYSTERESIS))

#define ADDR_V2P_BIAS                                            0x40007CB8
#define MMCR_V2P_BIAS                                            (*(VUINT32 *)(ADDR_V2P_BIAS))

#define ADDR_V2P_INTERRUPT_CONTROL                               0x40007CBC
#define MMCR_V2P_INTERRUPT_CONTROL                               (*(VUINT32 *)(ADDR_V2P_INTERRUPT_CONTROL))

/***************************************************************
*                            VBAT_REGS (1322)
***************************************************************/
#define ADDR_VBAT_POWER_FAIL_AND_RESET_STATUS                    0x4000A400
#define MMCR_VBAT_POWER_FAIL_AND_RESET_STATUS                    (*(VUINT8 *)(ADDR_VBAT_POWER_FAIL_AND_RESET_STATUS))

#define ADDR_VBAT_CONTROL                                        0x4000A404
#define MMCR_VBAT_CONTROL                                        (*(VUINT8 *)(ADDR_VBAT_CONTROL))

#define ADDR_VBAT_CLOCK_ENABLE                                   0x4000A408
#define MMCR_VBAT_CLOCK_ENABLE                                   (*(VUINT8 *)(ADDR_VBAT_CLOCK_ENABLE))

/***************************************************************
*                            EC_REG_BANK (1322)
***************************************************************/
#define ADDR_EC_REG_BANK_AHB_ERROR_ADDRESS                       0x4000FC04
#define MMCR_EC_REG_BANK_AHB_ERROR_ADDRESS                       (*(VUINT32 *)(ADDR_EC_REG_BANK_AHB_ERROR_ADDRESS))

#define ADDR_EC_REG_BANK_INPUT_MUX0                              0x4000FC08
#define MMCR_EC_REG_BANK_INPUT_MUX0                              (*(VUINT32 *)(ADDR_EC_REG_BANK_INPUT_MUX0))

#define ADDR_EC_REG_BANK_INPUT_MUX1                              0x4000FC0C
#define MMCR_EC_REG_BANK_INPUT_MUX1                              (*(VUINT32 *)(ADDR_EC_REG_BANK_INPUT_MUX1))

#define ADDR_EC_REG_BANK_ID                                      0x4000FC10
#define MMCR_EC_REG_BANK_ID                                      (*(VUINT8 *)(ADDR_EC_REG_BANK_ID))

#define ADDR_EC_REG_BANK_AHB_ERROR_CONTROL                       0x4000FC14
#define MMCR_EC_REG_BANK_AHB_ERROR_CONTROL                       (*(VUINT8 *)(ADDR_EC_REG_BANK_AHB_ERROR_CONTROL))

#define ADDR_EC_REG_BANK_INTERRUPT_CONTROL                       0x4000FC18
#define MMCR_EC_REG_BANK_INTERRUPT_CONTROL                       (*(VUINT32 *)(ADDR_EC_REG_BANK_INTERRUPT_CONTROL))

#define ADDR_EC_REG_BANK_ETM_TRACE                               0x4000FC1C
#define MMCR_EC_REG_BANK_ETM_TRACE                               (*(VUINT32 *)(ADDR_EC_REG_BANK_ETM_TRACE))

#define ADDR_EC_REG_BANK_JTAG_ENABLE                             0x4000FC20
#define MMCR_EC_REG_BANK_JTAG_ENABLE                             (*(VUINT32 *)(ADDR_EC_REG_BANK_JTAG_ENABLE))

#define ADDR_EC_REG_BANK_PRIVATE_KEY_LOCK                        0x4000FC24
#define MMCR_EC_REG_BANK_PRIVATE_KEY_LOCK                        (*(VUINT32 *)(ADDR_EC_REG_BANK_PRIVATE_KEY_LOCK))

#define ADDR_EC_REG_BANK_WDT_COUNT                               0x4000FC28
#define MMCR_EC_REG_BANK_WDT_COUNT                               (*(VUINT32 *)(ADDR_EC_REG_BANK_WDT_COUNT))

#define ADDR_EC_REG_BANK_AES_HASH_BYTE_SWAP_CONTROL              0x4000FC2C
#define MMCR_EC_REG_BANK_AES_HASH_BYTE_SWAP_CONTROL              (*(VUINT32 *)(ADDR_EC_REG_BANK_AES_HASH_BYTE_SWAP_CONTROL))

#define ADDR_EC_REG_BANK_ADC_VREF_TRIM                           0x4000FC30
#define MMCR_EC_REG_BANK_ADC_VREF_TRIM                           (*(VUINT32 *)(ADDR_EC_REG_BANK_ADC_VREF_TRIM))

#define ADDR_EC_REG_BANK_REGULATOR_TRIM                          0x4000FC34
#define MMCR_EC_REG_BANK_REGULATOR_TRIM                          (*(VUINT32 *)(ADDR_EC_REG_BANK_REGULATOR_TRIM))

#define ADDR_EC_REG_BANK_ADC_VREF_PD                             0x4000FC38
#define MMCR_EC_REG_BANK_ADC_VREF_PD                             (*(VUINT32 *)(ADDR_EC_REG_BANK_ADC_VREF_PD))

#define ADDR_EC_REG_BANK_ADC_COMP_BIAS_CURRENT_ADJUST            0x4000FC3C
#define MMCR_EC_REG_BANK_ADC_COMP_BIAS_CURRENT_ADJUST            (*(VUINT32 *)(ADDR_EC_REG_BANK_ADC_COMP_BIAS_CURRENT_ADJUST))

#define ADDR_EC_REG_BANK_MISC_TRIM                               0x4000FC40
#define MMCR_EC_REG_BANK_MISC_TRIM                               (*(VUINT8 *)(ADDR_EC_REG_BANK_MISC_TRIM))

/***************************************************************
*                            PCR
***************************************************************/
#define ADDR_PCR_CHIP_SLEEP_ENABLE                               0x40080100
#define MMCR_PCR_CHIP_SLEEP_ENABLE                               (*(VUINT32 *)(ADDR_PCR_CHIP_SLEEP_ENABLE))

#define ADDR_PCR_CHIP_CLOCK_REQUIRED                             0x40080104
#define MMCR_PCR_CHIP_CLOCK_REQUIRED                             (*(VUINT32 *)(ADDR_PCR_CHIP_CLOCK_REQUIRED))

#define ADDR_PCR_EC_SLEEP_ENABLES                                0x40080108
#define MMCR_PCR_EC_SLEEP_ENABLES                                (*(VUINT32 *)(ADDR_PCR_EC_SLEEP_ENABLES))

#define ADDR_PCR_EC_CLOCK_REQUIRED_STATUS                        0x4008010C
#define MMCR_PCR_EC_CLOCK_REQUIRED_STATUS                        (*(VUINT32 *)(ADDR_PCR_EC_CLOCK_REQUIRED_STATUS))

#define ADDR_PCR_HOST_SLEEP_ENABLES                              0x40080110
#define MMCR_PCR_HOST_SLEEP_ENABLES                              (*(VUINT32 *)(ADDR_PCR_HOST_SLEEP_ENABLES))

#define ADDR_PCR_HOST_CLOCK_REQUIRED_STATUS                      0x40080114
#define MMCR_PCR_HOST_CLOCK_REQUIRED_STATUS                      (*(VUINT32 *)(ADDR_PCR_HOST_CLOCK_REQUIRED_STATUS))

#define ADDR_PCR_CHIP_PCR_ADDR_SYS_SLEEP_CTRL_0                  0x40080118
#define MMCR_PCR_CHIP_PCR_ADDR_SYS_SLEEP_CTRL_0                  (*(VUINT32 *)(ADDR_PCR_CHIP_PCR_ADDR_SYS_SLEEP_CTRL_0))

#define ADDR_PCR_PROCESSOR_CLOCK_CONTROL                         0x40080120
#define MMCR_PCR_PROCESSOR_CLOCK_CONTROL                         (*(VUINT32 *)(ADDR_PCR_PROCESSOR_CLOCK_CONTROL))

#define ADDR_PCR_EC_SLEEP_ENABLE_2                               0x40080124
#define MMCR_PCR_EC_SLEEP_ENABLE_2                               (*(VUINT32 *)(ADDR_PCR_EC_SLEEP_ENABLE_2))

#define ADDR_PCR_EC_CLOCK_REQUIRED_2_STATUS                      0x40080128
#define MMCR_PCR_EC_CLOCK_REQUIRED_2_STATUS                      (*(VUINT32 *)(ADDR_PCR_EC_CLOCK_REQUIRED_2_STATUS))

#define ADDR_PCR_SLOW_CLOCK_CONTROL                              0x4008012C
#define MMCR_PCR_SLOW_CLOCK_CONTROL                              (*(VUINT32 *)(ADDR_PCR_SLOW_CLOCK_CONTROL))

#define ADDR_PCR_OSCILLATOR_ID                                   0x40080130
#define MMCR_PCR_OSCILLATOR_ID                                   (*(VUINT32 *)(ADDR_PCR_OSCILLATOR_ID))

#define ADDR_PCR_CHIP_RESET_ENABLE                               0x40080138
#define MMCR_PCR_CHIP_RESET_ENABLE                               (*(VUINT32 *)(ADDR_PCR_CHIP_RESET_ENABLE))

#define ADDR_PCR_HOST_RESET_ENABLE                               0x4008013C
#define MMCR_PCR_HOST_RESET_ENABLE                               (*(VUINT32 *)(ADDR_PCR_HOST_RESET_ENABLE))

#define ADDR_PCR_EC_RESET_ENABLE                                 0x40080140
#define MMCR_PCR_EC_RESET_ENABLE                                 (*(VUINT32 *)(ADDR_PCR_EC_RESET_ENABLE))

#define ADDR_PCR_EC_RESET_ENABLE_2                               0x40080144
#define MMCR_PCR_EC_RESET_ENABLE_2                               (*(VUINT32 *)(ADDR_PCR_EC_RESET_ENABLE_2))

#define ADDR_PCR_CLOCK_RESET_CONTROL                             0x40080148
#define MMCR_PCR_CLOCK_RESET_CONTROL                             (*(VUINT32 *)(ADDR_PCR_CLOCK_RESET_CONTROL))

/***************************************************************
*                            Public Key Crypto Engine
***************************************************************/
#define ADDR_PUBLIC_PK_CONFIGREG                                 0x4000BD00
#define MMCR_PUBLIC_PK_CONFIGREG                                 (*(VUINT32 *)(ADDR_PUBLIC_PK_CONFIGREG))

#define ADDR_PUBLIC_PK_COMMANDREG                                0x4000BD04
#define MMCR_PUBLIC_PK_COMMANDREG                                (*(VUINT32 *)(ADDR_PUBLIC_PK_COMMANDREG))

#define ADDR_PUBLIC_PK_CONTROLREG                                0x4000BD08
#define MMCR_PUBLIC_PK_CONTROLREG                                (*(VUINT32 *)(ADDR_PUBLIC_PK_CONTROLREG))

#define ADDR_PUBLIC_PK_STATUSREG                                 0x4000BD0C
#define MMCR_PUBLIC_PK_STATUSREG                                 (*(VUINT32 *)(ADDR_PUBLIC_PK_STATUSREG))

#define ADDR_PUBLIC_PK_VERSIONREG                                0x4000BD10
#define MMCR_PUBLIC_PK_VERSIONREG                                (*(VUINT32 *)(ADDR_PUBLIC_PK_VERSIONREG))

#define ADDR_PUBLIC_PK_LOADMICROCODEREG                          0x4000BD14
#define MMCR_PUBLIC_PK_LOADMICROCODEREG                          (*(VUINT32 *)(ADDR_PUBLIC_PK_LOADMICROCODEREG))

/***************************************************************
*                            Non Deterministic Random Number Generator
***************************************************************/
#define ADDR_NON_CONTROLREG                                      0x4000BE00
#define MMCR_NON_CONTROLREG                                      (*(VUINT32 *)(ADDR_NON_CONTROLREG))

#define ADDR_NON_FIFOLEVELREG                                    0x4000BE04
#define MMCR_NON_FIFOLEVELREG                                    (*(VUINT32 *)(ADDR_NON_FIFOLEVELREG))

#define ADDR_NON_VERSIONREG                                      0x4000BE08
#define MMCR_NON_VERSIONREG                                      (*(VUINT32 *)(ADDR_NON_VERSIONREG))

/***************************************************************
*                            RTC
***************************************************************/
#define ADDR_RTC_SECONDS                                         0x400F2800
#define MMCR_RTC_SECONDS                                         (*(VUINT8 *)(ADDR_RTC_SECONDS))

#define ADDR_RTC_SECONDS_ALARM                                   0x400F2801
#define MMCR_RTC_SECONDS_ALARM                                   (*(VUINT8 *)(ADDR_RTC_SECONDS_ALARM))

#define ADDR_RTC_MINUTES                                         0x400F2802
#define MMCR_RTC_MINUTES                                         (*(VUINT8 *)(ADDR_RTC_MINUTES))

#define ADDR_RTC_MINUTES_ALARM                                   0x400F2803
#define MMCR_RTC_MINUTES_ALARM                                   (*(VUINT8 *)(ADDR_RTC_MINUTES_ALARM))

#define ADDR_RTC_HOURS                                           0x400F2804
#define MMCR_RTC_HOURS                                           (*(VUINT8 *)(ADDR_RTC_HOURS))

#define ADDR_RTC_HOURS_ALARM                                     0x400F2805
#define MMCR_RTC_HOURS_ALARM                                     (*(VUINT8 *)(ADDR_RTC_HOURS_ALARM))

#define ADDR_RTC_DAY_OF_WEEK                                     0x400F2806
#define MMCR_RTC_DAY_OF_WEEK                                     (*(VUINT8 *)(ADDR_RTC_DAY_OF_WEEK))

#define ADDR_RTC_DAY_OF_MONTH                                    0x400F2807
#define MMCR_RTC_DAY_OF_MONTH                                    (*(VUINT8 *)(ADDR_RTC_DAY_OF_MONTH))

#define ADDR_RTC_MONTH                                           0x400F2808
#define MMCR_RTC_MONTH                                           (*(VUINT8 *)(ADDR_RTC_MONTH))

#define ADDR_RTC_YEAR                                            0x400F2809
#define MMCR_RTC_YEAR                                            (*(VUINT8 *)(ADDR_RTC_YEAR))

#define ADDR_RTC_A                                               0x400F280A
#define MMCR_RTC_A                                               (*(VUINT8 *)(ADDR_RTC_A))

#define ADDR_RTC_B                                               0x400F280B
#define MMCR_RTC_B                                               (*(VUINT8 *)(ADDR_RTC_B))

#define ADDR_RTC_C                                               0x400F280C
#define MMCR_RTC_C                                               (*(VUINT8 *)(ADDR_RTC_C))

#define ADDR_RTC_D                                               0x400F280D
#define MMCR_RTC_D                                               (*(VUINT8 *)(ADDR_RTC_D))

#define ADDR_RTC_CONTROL                                         0x400F2810
#define MMCR_RTC_CONTROL                                         (*(VUINT8 *)(ADDR_RTC_CONTROL))

#define ADDR_RTC_WEEK_ALARM                                      0x400F2814
#define MMCR_RTC_WEEK_ALARM                                      (*(VUINT8 *)(ADDR_RTC_WEEK_ALARM))

#define ADDR_RTC_DAYLIGHT_SAVINGS_FORWARD                        0x400F2818
#define MMCR_RTC_DAYLIGHT_SAVINGS_FORWARD                        (*(VUINT32 *)(ADDR_RTC_DAYLIGHT_SAVINGS_FORWARD))

#define ADDR_RTC_DAYLIGHT_SAVINGS_BACKWARD                       0x400F281C
#define MMCR_RTC_DAYLIGHT_SAVINGS_BACKWARD                       (*(VUINT32 *)(ADDR_RTC_DAYLIGHT_SAVINGS_BACKWARD))

#define ADDR_RTC_TEST_MODE                                       0x400F2820
#define MMCR_RTC_TEST_MODE                                       (*(VUINT8 *)(ADDR_RTC_TEST_MODE))

/***************************************************************
*                            Analog to Digital Converter (ADC)
***************************************************************/
#define ADDR_ADC_CONTROL                                         0x40007C00
#define MMCR_ADC_CONTROL                                         (*(VUINT32 *)(ADDR_ADC_CONTROL))

#define ADDR_ADC_DELAY                                           0x40007C04
#define MMCR_ADC_DELAY                                           (*(VUINT32 *)(ADDR_ADC_DELAY))

#define ADDR_ADC_STATUS                                          0x40007C08
#define MMCR_ADC_STATUS                                          (*(VUINT32 *)(ADDR_ADC_STATUS))

#define ADDR_ADC_SINGLE                                          0x40007C0C
#define MMCR_ADC_SINGLE                                          (*(VUINT32 *)(ADDR_ADC_SINGLE))

#define ADDR_ADC_REPEAT                                          0x40007C10
#define MMCR_ADC_REPEAT                                          (*(VUINT32 *)(ADDR_ADC_REPEAT))

#define ADDR_ADC_CHANNEL_0_READINGS                              0x40007C14
#define MMCR_ADC_CHANNEL_0_READINGS                              (*(VUINT32 *)(ADDR_ADC_CHANNEL_0_READINGS))

#define ADDR_ADC_CHANNEL_1_READINGS                              0x40007C18
#define MMCR_ADC_CHANNEL_1_READINGS                              (*(VUINT32 *)(ADDR_ADC_CHANNEL_1_READINGS))

#define ADDR_ADC_CHANNEL_2_READINGS                              0x40007C1C
#define MMCR_ADC_CHANNEL_2_READINGS                              (*(VUINT32 *)(ADDR_ADC_CHANNEL_2_READINGS))

#define ADDR_ADC_CHANNEL_3_READINGS                              0x40007C20
#define MMCR_ADC_CHANNEL_3_READINGS                              (*(VUINT32 *)(ADDR_ADC_CHANNEL_3_READINGS))

#define ADDR_ADC_CHANNEL_4_READINGS                              0x40007C24
#define MMCR_ADC_CHANNEL_4_READINGS                              (*(VUINT32 *)(ADDR_ADC_CHANNEL_4_READINGS))

#define ADDR_ADC_DEBUG_FPGA_TEST_MODE                            0x40007C54
#define MMCR_ADC_DEBUG_FPGA_TEST_MODE                            (*(VUINT32 *)(ADDR_ADC_DEBUG_FPGA_TEST_MODE))

#define ADDR_ADC_TEST                                            0x40007C78
#define MMCR_ADC_TEST                                            (*(VUINT32 *)(ADDR_ADC_TEST))

#define ADDR_ADC_CONFIGURATION                                   0x40007C7C
#define MMCR_ADC_CONFIGURATION                                   (*(VUINT32 *)(ADDR_ADC_CONFIGURATION))

/***************************************************************
*                            eFUSE
***************************************************************/
#define ADDR_EFUSE_CONTROL                                       0x40082000
#define MMCR_EFUSE_CONTROL                                       (*(VUINT8 *)(ADDR_EFUSE_CONTROL))

#define ADDR_EFUSE_MANUAL_CONTROL                                0x40082004
#define MMCR_EFUSE_MANUAL_CONTROL                                (*(VUINT8 *)(ADDR_EFUSE_MANUAL_CONTROL))

#define ADDR_EFUSE_MANUAL_MODE_ADDRESS                           0x40082006
#define MMCR_EFUSE_MANUAL_MODE_ADDRESS                           (*(VUINT16 *)(ADDR_EFUSE_MANUAL_MODE_ADDRESS))

#define ADDR_EFUSE_MANUAL_MODE_DATA                              0x4008200C
#define MMCR_EFUSE_MANUAL_MODE_DATA                              (*(VUINT16 *)(ADDR_EFUSE_MANUAL_MODE_DATA))

/***************************************************************
*                            AES Crypto Engine & Hash Function
***************************************************************/
#define ADDR_AES_CONFIGREG                                       0x4000D200
#define MMCR_AES_CONFIGREG                                       (*(VUINT32 *)(ADDR_AES_CONFIGREG))

#define ADDR_AES_COMMANDREG                                      0x4000D204
#define MMCR_AES_COMMANDREG                                      (*(VUINT32 *)(ADDR_AES_COMMANDREG))

#define ADDR_AES_CONTROLREG                                      0x4000D208
#define MMCR_AES_CONTROLREG                                      (*(VUINT32 *)(ADDR_AES_CONTROLREG))

#define ADDR_AES_STATUSREG                                       0x4000D20C
#define MMCR_AES_STATUSREG                                       (*(VUINT32 *)(ADDR_AES_STATUSREG))

#define ADDR_AES_VERSIONREG                                      0x4000D210
#define MMCR_AES_VERSIONREG                                      (*(VUINT32 *)(ADDR_AES_VERSIONREG))

#define ADDR_AES_NBHEADERREG                                     0x4000D214
#define MMCR_AES_NBHEADERREG                                     (*(VUINT32 *)(ADDR_AES_NBHEADERREG))

#define ADDR_AES_LASTHEADERREG                                   0x4000D218
#define MMCR_AES_LASTHEADERREG                                   (*(VUINT32 *)(ADDR_AES_LASTHEADERREG))

#define ADDR_AES_NBBLOCKREG                                      0x4000D21C
#define MMCR_AES_NBBLOCKREG                                      (*(VUINT32 *)(ADDR_AES_NBBLOCKREG))

#define ADDR_AES_LASTBLOCKREG                                    0x4000D220
#define MMCR_AES_LASTBLOCKREG                                    (*(VUINT32 *)(ADDR_AES_LASTBLOCKREG))

#define ADDR_AES_DMAINREG                                        0x4000D224
#define MMCR_AES_DMAINREG                                        (*(VUINT32 *)(ADDR_AES_DMAINREG))

#define ADDR_AES_DMAOUTREG                                       0x4000D228
#define MMCR_AES_DMAOUTREG                                       (*(VUINT32 *)(ADDR_AES_DMAOUTREG))

#define ADDR_AES_SHAMODE_REGISTER                                0x4000D000
#define MMCR_AES_SHAMODE_REGISTER                                (*(VUINT32 *)(ADDR_AES_SHAMODE_REGISTER))

#define ADDR_AES_NBBLOCK_REGISTER                                0x4000D004
#define MMCR_AES_NBBLOCK_REGISTER                                (*(VUINT32 *)(ADDR_AES_NBBLOCK_REGISTER))

#define ADDR_AES_CONTROL                                         0x4000D008
#define MMCR_AES_CONTROL                                         (*(VUINT32 *)(ADDR_AES_CONTROL))

#define ADDR_AES_STATUS                                          0x4000D00C
#define MMCR_AES_STATUS                                          (*(VUINT32 *)(ADDR_AES_STATUS))

#define ADDR_AES_VERSION                                         0x4000D010
#define MMCR_AES_VERSION                                         (*(VUINT32 *)(ADDR_AES_VERSION))

#define ADDR_AES_GENERICVALUE_REGISTER                           0x4000D014
#define MMCR_AES_GENERICVALUE_REGISTER                           (*(VUINT32 *)(ADDR_AES_GENERICVALUE_REGISTER))

#define ADDR_AES_INITIAL_HASH_SOURCE_ADDRESS                     0x4000D018
#define MMCR_AES_INITIAL_HASH_SOURCE_ADDRESS                     (*(VUINT32 *)(ADDR_AES_INITIAL_HASH_SOURCE_ADDRESS))

#define ADDR_AES_DATA_SOURCE_ADDRESS                             0x4000D01C
#define MMCR_AES_DATA_SOURCE_ADDRESS                             (*(VUINT32 *)(ADDR_AES_DATA_SOURCE_ADDRESS))

#define ADDR_AES_HASH_RESULT_DESTINATION_ADDRESS                 0x4000D020
#define MMCR_AES_HASH_RESULT_DESTINATION_ADDRESS                 (*(VUINT32 *)(ADDR_AES_HASH_RESULT_DESTINATION_ADDRESS))

/***************************************************************
*                            LPC
***************************************************************/
#define ADDR_LPC_ACTIVATE                                        0x400F3330
#define MMCR_LPC_ACTIVATE                                        (*(VUINT8 *)(ADDR_LPC_ACTIVATE))

#define ADDR_LPC_SIRQ0_INTERRUPT_CONFIGURATION                   0x400F3340
#define MMCR_LPC_SIRQ0_INTERRUPT_CONFIGURATION                   (*(VUINT8 *)(ADDR_LPC_SIRQ0_INTERRUPT_CONFIGURATION))

#define ADDR_LPC_SIRQ1_INTERRUPT_CONFIGURATION                   0x400F3341
#define MMCR_LPC_SIRQ1_INTERRUPT_CONFIGURATION                   (*(VUINT8 *)(ADDR_LPC_SIRQ1_INTERRUPT_CONFIGURATION))

#define ADDR_LPC_SIRQ2_INTERRUPT_CONFIGURATION                   0x400F3342
#define MMCR_LPC_SIRQ2_INTERRUPT_CONFIGURATION                   (*(VUINT8 *)(ADDR_LPC_SIRQ2_INTERRUPT_CONFIGURATION))

#define ADDR_LPC_SIRQ3_INTERRUPT_CONFIGURATION                   0x400F3343
#define MMCR_LPC_SIRQ3_INTERRUPT_CONFIGURATION                   (*(VUINT8 *)(ADDR_LPC_SIRQ3_INTERRUPT_CONFIGURATION))

#define ADDR_LPC_SIRQ4_INTERRUPT_CONFIGURATION                   0x400F3344
#define MMCR_LPC_SIRQ4_INTERRUPT_CONFIGURATION                   (*(VUINT8 *)(ADDR_LPC_SIRQ4_INTERRUPT_CONFIGURATION))

#define ADDR_LPC_SIRQ5_INTERRUPT_CONFIGURATION                   0x400F3345
#define MMCR_LPC_SIRQ5_INTERRUPT_CONFIGURATION                   (*(VUINT8 *)(ADDR_LPC_SIRQ5_INTERRUPT_CONFIGURATION))

#define ADDR_LPC_SIRQ6_INTERRUPT_CONFIGURATION                   0x400F3346
#define MMCR_LPC_SIRQ6_INTERRUPT_CONFIGURATION                   (*(VUINT8 *)(ADDR_LPC_SIRQ6_INTERRUPT_CONFIGURATION))

#define ADDR_LPC_SIRQ7_INTERRUPT_CONFIGURATION                   0x400F3347
#define MMCR_LPC_SIRQ7_INTERRUPT_CONFIGURATION                   (*(VUINT8 *)(ADDR_LPC_SIRQ7_INTERRUPT_CONFIGURATION))

#define ADDR_LPC_SIRQ8_INTERRUPT_CONFIGURATION                   0x400F3348
#define MMCR_LPC_SIRQ8_INTERRUPT_CONFIGURATION                   (*(VUINT8 *)(ADDR_LPC_SIRQ8_INTERRUPT_CONFIGURATION))

#define ADDR_LPC_SIRQ9_INTERRUPT_CONFIGURATION                   0x400F3349
#define MMCR_LPC_SIRQ9_INTERRUPT_CONFIGURATION                   (*(VUINT8 *)(ADDR_LPC_SIRQ9_INTERRUPT_CONFIGURATION))

#define ADDR_LPC_SIRQ10_INTERRUPT_CONFIGURATION                  0x400F334A
#define MMCR_LPC_SIRQ10_INTERRUPT_CONFIGURATION                  (*(VUINT8 *)(ADDR_LPC_SIRQ10_INTERRUPT_CONFIGURATION))

#define ADDR_LPC_SIRQ11_INTERRUPT_CONFIGURATION                  0x400F334B
#define MMCR_LPC_SIRQ11_INTERRUPT_CONFIGURATION                  (*(VUINT8 *)(ADDR_LPC_SIRQ11_INTERRUPT_CONFIGURATION))

#define ADDR_LPC_SIRQ12_INTERRUPT_CONFIGURATION                  0x400F334C
#define MMCR_LPC_SIRQ12_INTERRUPT_CONFIGURATION                  (*(VUINT8 *)(ADDR_LPC_SIRQ12_INTERRUPT_CONFIGURATION))

#define ADDR_LPC_SIRQ13_INTERRUPT_CONFIGURATION                  0x400F334D
#define MMCR_LPC_SIRQ13_INTERRUPT_CONFIGURATION                  (*(VUINT8 *)(ADDR_LPC_SIRQ13_INTERRUPT_CONFIGURATION))

#define ADDR_LPC_SIRQ14_INTERRUPT_CONFIGURATION                  0x400F334E
#define MMCR_LPC_SIRQ14_INTERRUPT_CONFIGURATION                  (*(VUINT8 *)(ADDR_LPC_SIRQ14_INTERRUPT_CONFIGURATION))

#define ADDR_LPC_SIRQ15_INTERRUPT_CONFIGURATION                  0x400F334F
#define MMCR_LPC_SIRQ15_INTERRUPT_CONFIGURATION                  (*(VUINT8 *)(ADDR_LPC_SIRQ15_INTERRUPT_CONFIGURATION))

#define ADDR_LPC_INTERFACE_BAR                                   0x400F3360
#define MMCR_LPC_INTERFACE_BAR                                   (*(VUINT32 *)(ADDR_LPC_INTERFACE_BAR))

#define ADDR_LPC_EM_INTERFACE_0_BAR                              0x400F3364
#define MMCR_LPC_EM_INTERFACE_0_BAR                              (*(VUINT32 *)(ADDR_LPC_EM_INTERFACE_0_BAR))

#define ADDR_LPC_UART_0_BAR                                      0x400F3368
#define MMCR_LPC_UART_0_BAR                                      (*(VUINT32 *)(ADDR_LPC_UART_0_BAR))

#define ADDR_LPC_KEYBOARD_CONTROLLER_BAR                         0x400F3378
#define MMCR_LPC_KEYBOARD_CONTROLLER_BAR                         (*(VUINT32 *)(ADDR_LPC_KEYBOARD_CONTROLLER_BAR))

#define ADDR_LPC_ACPI_EC_INTERFACE_0_BAR                         0x400F3388
#define MMCR_LPC_ACPI_EC_INTERFACE_0_BAR                         (*(VUINT32 *)(ADDR_LPC_ACPI_EC_INTERFACE_0_BAR))

#define ADDR_LPC_ACPI_EC_INTERFACE_1_BAR                         0x400F338C
#define MMCR_LPC_ACPI_EC_INTERFACE_1_BAR                         (*(VUINT32 *)(ADDR_LPC_ACPI_EC_INTERFACE_1_BAR))

#define ADDR_LPC_ACPI_PM1_INTERFACE_BAR                          0x400F3390
#define MMCR_LPC_ACPI_PM1_INTERFACE_BAR                          (*(VUINT32 *)(ADDR_LPC_ACPI_PM1_INTERFACE_BAR))

#define ADDR_LPC_LEGACY_GATEA20_INTERFACE_BAR                    0x400F3394
#define MMCR_LPC_LEGACY_GATEA20_INTERFACE_BAR                    (*(VUINT32 *)(ADDR_LPC_LEGACY_GATEA20_INTERFACE_BAR))

#define ADDR_LPC_MAILBOXS_INTERFACE_BAR                          0x400F3398
#define MMCR_LPC_MAILBOXS_INTERFACE_BAR                          (*(VUINT32 *)(ADDR_LPC_MAILBOXS_INTERFACE_BAR))

#define ADDR_LPC_BUS_MONITOR                                     0x400F3104
#define MMCR_LPC_BUS_MONITOR                                     (*(VUINT32 *)(ADDR_LPC_BUS_MONITOR))

#define ADDR_LPC_HOST_BUS_ERROR                                  0x400F3108
#define MMCR_LPC_HOST_BUS_ERROR                                  (*(VUINT32 *)(ADDR_LPC_HOST_BUS_ERROR))

#define ADDR_LPC_EC_SERIRQ                                       0x400F310C
#define MMCR_LPC_EC_SERIRQ                                       (*(VUINT32 *)(ADDR_LPC_EC_SERIRQ))

#define ADDR_LPC_EC_CLOCK_CONTROL                                0x400F3110
#define MMCR_LPC_EC_CLOCK_CONTROL                                (*(VUINT32 *)(ADDR_LPC_EC_CLOCK_CONTROL))

#define ADDR_LPC_BAR_INHIBIT                                     0x400F3120
#define MMCR_LPC_BAR_INHIBIT                                     (*(VUINT32 *)(ADDR_LPC_BAR_INHIBIT))

#define ADDR_LPC_BAR_INIT                                        0x400F3130
#define MMCR_LPC_BAR_INIT                                        (*(VUINT16 *)(ADDR_LPC_BAR_INIT))

#define ADDR_LPC_MEMORY_HOST_CONFIGURATION                       0x400F31FC
#define MMCR_LPC_MEMORY_HOST_CONFIGURATION                       (*(VUINT32 *)(ADDR_LPC_MEMORY_HOST_CONFIGURATION))

/***************************************************************
*                            GPIO
***************************************************************/
#define ADDR_GPIO000_PIN_CONTROL                                 0x40081000
#define MMCR_GPIO000_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO000_PIN_CONTROL))

#define ADDR_GPIO001_PIN_CONTROL                                 0x40081004
#define MMCR_GPIO001_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO001_PIN_CONTROL))

#define ADDR_GPIO002_PIN_CONTROL                                 0x40081008
#define MMCR_GPIO002_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO002_PIN_CONTROL))

#define ADDR_GPIO003_PIN_CONTROL                                 0x4008100C
#define MMCR_GPIO003_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO003_PIN_CONTROL))

#define ADDR_GPIO004_PIN_CONTROL                                 0x40081010
#define MMCR_GPIO004_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO004_PIN_CONTROL))

#define ADDR_GPIO005_PIN_CONTROL                                 0x40081014
#define MMCR_GPIO005_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO005_PIN_CONTROL))

#define ADDR_GPIO006_PIN_CONTROL                                 0x40081018
#define MMCR_GPIO006_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO006_PIN_CONTROL))

#define ADDR_GPIO007_PIN_CONTROL                                 0x4008101C
#define MMCR_GPIO007_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO007_PIN_CONTROL))

#define ADDR_GPIO010_PIN_CONTROL                                 0x40081020
#define MMCR_GPIO010_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO010_PIN_CONTROL))

#define ADDR_GPIO011_PIN_CONTROL                                 0x40081024
#define MMCR_GPIO011_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO011_PIN_CONTROL))

#define ADDR_GPIO012_PIN_CONTROL                                 0x40081028
#define MMCR_GPIO012_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO012_PIN_CONTROL))

#define ADDR_GPIO013_PIN_CONTROL                                 0x4008102C
#define MMCR_GPIO013_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO013_PIN_CONTROL))

#define ADDR_GPIO014_PIN_CONTROL                                 0x40081030
#define MMCR_GPIO014_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO014_PIN_CONTROL))

#define ADDR_GPIO015_PIN_CONTROL                                 0x40081034
#define MMCR_GPIO015_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO015_PIN_CONTROL))

#define ADDR_GPIO016_PIN_CONTROL                                 0x40081038
#define MMCR_GPIO016_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO016_PIN_CONTROL))

#define ADDR_GPIO017_PIN_CONTROL                                 0x4008103C
#define MMCR_GPIO017_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO017_PIN_CONTROL))

#define ADDR_GPIO020_PIN_CONTROL                                 0x40081040
#define MMCR_GPIO020_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO020_PIN_CONTROL))

#define ADDR_GPIO021_PIN_CONTROL                                 0x40081044
#define MMCR_GPIO021_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO021_PIN_CONTROL))

#define ADDR_GPIO022_PIN_CONTROL                                 0x40081048
#define MMCR_GPIO022_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO022_PIN_CONTROL))

#define ADDR_GPIO023_PIN_CONTROL                                 0x4008104C
#define MMCR_GPIO023_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO023_PIN_CONTROL))

#define ADDR_GPIO024_PIN_CONTROL                                 0x40081050
#define MMCR_GPIO024_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO024_PIN_CONTROL))

#define ADDR_GPIO025_PIN_CONTROL                                 0x40081054
#define MMCR_GPIO025_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO025_PIN_CONTROL))

#define ADDR_GPIO026_PIN_CONTROL                                 0x40081058
#define MMCR_GPIO026_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO026_PIN_CONTROL))

#define ADDR_GPIO027_PIN_CONTROL                                 0x4008105C
#define MMCR_GPIO027_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO027_PIN_CONTROL))

#define ADDR_GPIO030_PIN_CONTROL                                 0x40081060
#define MMCR_GPIO030_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO030_PIN_CONTROL))

#define ADDR_GPIO031_PIN_CONTROL                                 0x40081064
#define MMCR_GPIO031_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO031_PIN_CONTROL))

#define ADDR_GPIO032_PIN_CONTROL                                 0x40081068
#define MMCR_GPIO032_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO032_PIN_CONTROL))

#define ADDR_GPIO033_PIN_CONTROL                                 0x4008106C
#define MMCR_GPIO033_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO033_PIN_CONTROL))

#define ADDR_GPIO034_PIN_CONTROL                                 0x40081070
#define MMCR_GPIO034_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO034_PIN_CONTROL))

#define ADDR_GPIO035_PIN_CONTROL                                 0x40081074
#define MMCR_GPIO035_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO035_PIN_CONTROL))

#define ADDR_GPIO036_PIN_CONTROL                                 0x40081078
#define MMCR_GPIO036_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO036_PIN_CONTROL))

#define ADDR_GPIO040_PIN_CONTROL                                 0x40081080
#define MMCR_GPIO040_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO040_PIN_CONTROL))

#define ADDR_GPIO041_PIN_CONTROL                                 0x40081084
#define MMCR_GPIO041_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO041_PIN_CONTROL))

#define ADDR_GPIO042_PIN_CONTROL                                 0x40081088
#define MMCR_GPIO042_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO042_PIN_CONTROL))

#define ADDR_GPIO043_PIN_CONTROL                                 0x4008108C
#define MMCR_GPIO043_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO043_PIN_CONTROL))

#define ADDR_GPIO044_PIN_CONTROL                                 0x40081090
#define MMCR_GPIO044_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO044_PIN_CONTROL))

#define ADDR_GPIO045_PIN_CONTROL                                 0x40081094
#define MMCR_GPIO045_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO045_PIN_CONTROL))

#define ADDR_GPIO046_PIN_CONTROL                                 0x40081098
#define MMCR_GPIO046_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO046_PIN_CONTROL))

#define ADDR_GPIO047_PIN_CONTROL                                 0x4008109C
#define MMCR_GPIO047_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO047_PIN_CONTROL))

#define ADDR_GPIO050_PIN_CONTROL                                 0x400810A0
#define MMCR_GPIO050_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO050_PIN_CONTROL))

#define ADDR_GPIO051_PIN_CONTROL                                 0x400810A4
#define MMCR_GPIO051_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO051_PIN_CONTROL))

#define ADDR_GPIO052_PIN_CONTROL                                 0x400810A8
#define MMCR_GPIO052_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO052_PIN_CONTROL))

#define ADDR_GPIO053_PIN_CONTROL                                 0x400810AC
#define MMCR_GPIO053_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO053_PIN_CONTROL))

#define ADDR_GPIO054_PIN_CONTROL                                 0x400810B0
#define MMCR_GPIO054_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO054_PIN_CONTROL))

#define ADDR_GPIO055_PIN_CONTROL                                 0x400810B4
#define MMCR_GPIO055_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO055_PIN_CONTROL))

#define ADDR_GPIO056_PIN_CONTROL                                 0x400810B8
#define MMCR_GPIO056_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO056_PIN_CONTROL))

#define ADDR_GPIO057_PIN_CONTROL                                 0x400810BC
#define MMCR_GPIO057_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO057_PIN_CONTROL))

#define ADDR_GPIO060_PIN_CONTROL                                 0x400810C0
#define MMCR_GPIO060_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO060_PIN_CONTROL))

#define ADDR_GPIO061_PIN_CONTROL                                 0x400810C4
#define MMCR_GPIO061_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO061_PIN_CONTROL))

#define ADDR_GPIO062_PIN_CONTROL                                 0x400810C8
#define MMCR_GPIO062_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO062_PIN_CONTROL))

#define ADDR_GPIO063_PIN_CONTROL                                 0x400810CC
#define MMCR_GPIO063_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO063_PIN_CONTROL))

#define ADDR_GPIO064_PIN_CONTROL                                 0x400810D0
#define MMCR_GPIO064_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO064_PIN_CONTROL))

#define ADDR_GPIO065_PIN_CONTROL                                 0x400810D4
#define MMCR_GPIO065_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO065_PIN_CONTROL))

#define ADDR_GPIO066_PIN_CONTROL                                 0x400810D8
#define MMCR_GPIO066_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO066_PIN_CONTROL))

#define ADDR_GPIO067_PIN_CONTROL                                 0x400810DC
#define MMCR_GPIO067_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO067_PIN_CONTROL))

#define ADDR_GPIO100_PIN_CONTROL                                 0x40081100
#define MMCR_GPIO100_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO100_PIN_CONTROL))

#define ADDR_GPIO101_PIN_CONTROL                                 0x40081104
#define MMCR_GPIO101_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO101_PIN_CONTROL))

#define ADDR_GPIO102_PIN_CONTROL                                 0x40081108
#define MMCR_GPIO102_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO102_PIN_CONTROL))

#define ADDR_GPIO103_PIN_CONTROL                                 0x4008110C
#define MMCR_GPIO103_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO103_PIN_CONTROL))

#define ADDR_GPIO104_PIN_CONTROL                                 0x40081110
#define MMCR_GPIO104_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO104_PIN_CONTROL))

#define ADDR_GPIO105_PIN_CONTROL                                 0x40081114
#define MMCR_GPIO105_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO105_PIN_CONTROL))

#define ADDR_GPIO106_PIN_CONTROL                                 0x40081118
#define MMCR_GPIO106_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO106_PIN_CONTROL))

#define ADDR_GPIO107_PIN_CONTROL                                 0x4008111C
#define MMCR_GPIO107_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO107_PIN_CONTROL))

#define ADDR_GPIO110_PIN_CONTROL                                 0x40081120
#define MMCR_GPIO110_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO110_PIN_CONTROL))

#define ADDR_GPIO111_PIN_CONTROL                                 0x40081124
#define MMCR_GPIO111_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO111_PIN_CONTROL))

#define ADDR_GPIO112_PIN_CONTROL                                 0x40081128
#define MMCR_GPIO112_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO112_PIN_CONTROL))

#define ADDR_GPIO113_PIN_CONTROL                                 0x4008112C
#define MMCR_GPIO113_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO113_PIN_CONTROL))

#define ADDR_GPIO114_PIN_CONTROL                                 0x40081130
#define MMCR_GPIO114_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO114_PIN_CONTROL))

#define ADDR_GPIO115_PIN_CONTROL                                 0x40081134
#define MMCR_GPIO115_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO115_PIN_CONTROL))

#define ADDR_GPIO116_PIN_CONTROL                                 0x40081138
#define MMCR_GPIO116_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO116_PIN_CONTROL))

#define ADDR_GPIO117_PIN_CONTROL                                 0x4008113C
#define MMCR_GPIO117_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO117_PIN_CONTROL))

#define ADDR_GPIO120_PIN_CONTROL                                 0x40081140
#define MMCR_GPIO120_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO120_PIN_CONTROL))

#define ADDR_GPIO121_PIN_CONTROL                                 0x40081144
#define MMCR_GPIO121_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO121_PIN_CONTROL))

#define ADDR_GPIO122_PIN_CONTROL                                 0x40081148
#define MMCR_GPIO122_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO122_PIN_CONTROL))

#define ADDR_GPIO123_PIN_CONTROL                                 0x4008114C
#define MMCR_GPIO123_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO123_PIN_CONTROL))

#define ADDR_GPIO124_PIN_CONTROL                                 0x40081150
#define MMCR_GPIO124_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO124_PIN_CONTROL))

#define ADDR_GPIO125_PIN_CONTROL                                 0x40081154
#define MMCR_GPIO125_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO125_PIN_CONTROL))

#define ADDR_GPIO126_PIN_CONTROL                                 0x40081158
#define MMCR_GPIO126_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO126_PIN_CONTROL))

#define ADDR_GPIO127_PIN_CONTROL                                 0x4008115C
#define MMCR_GPIO127_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO127_PIN_CONTROL))

#define ADDR_GPIO130_PIN_CONTROL                                 0x40081160
#define MMCR_GPIO130_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO130_PIN_CONTROL))

#define ADDR_GPIO131_PIN_CONTROL                                 0x40081164
#define MMCR_GPIO131_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO131_PIN_CONTROL))

#define ADDR_GPIO132_PIN_CONTROL                                 0x40081168
#define MMCR_GPIO132_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO132_PIN_CONTROL))

#define ADDR_GPIO133_PIN_CONTROL                                 0x4008116C
#define MMCR_GPIO133_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO133_PIN_CONTROL))

#define ADDR_GPIO134_PIN_CONTROL                                 0x40081170
#define MMCR_GPIO134_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO134_PIN_CONTROL))

#define ADDR_GPIO135_PIN_CONTROL                                 0x40081174
#define MMCR_GPIO135_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO135_PIN_CONTROL))

#define ADDR_GPIO136_PIN_CONTROL                                 0x40081178
#define MMCR_GPIO136_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO136_PIN_CONTROL))

#define ADDR_GPIO140_PIN_CONTROL                                 0x40081180
#define MMCR_GPIO140_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO140_PIN_CONTROL))

#define ADDR_GPIO141_PIN_CONTROL                                 0x40081184
#define MMCR_GPIO141_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO141_PIN_CONTROL))

#define ADDR_GPIO142_PIN_CONTROL                                 0x40081188
#define MMCR_GPIO142_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO142_PIN_CONTROL))

#define ADDR_GPIO143_PIN_CONTROL                                 0x4008118C
#define MMCR_GPIO143_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO143_PIN_CONTROL))

#define ADDR_GPIO144_PIN_CONTROL                                 0x40081190
#define MMCR_GPIO144_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO144_PIN_CONTROL))

#define ADDR_GPIO145_PIN_CONTROL                                 0x40081194
#define MMCR_GPIO145_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO145_PIN_CONTROL))

#define ADDR_GPIO146_PIN_CONTROL                                 0x40081198
#define MMCR_GPIO146_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO146_PIN_CONTROL))

#define ADDR_GPIO147_PIN_CONTROL                                 0x4008119C
#define MMCR_GPIO147_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO147_PIN_CONTROL))

#define ADDR_GPIO150_PIN_CONTROL                                 0x400811A0
#define MMCR_GPIO150_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO150_PIN_CONTROL))

#define ADDR_GPIO151_PIN_CONTROL                                 0x400811A4
#define MMCR_GPIO151_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO151_PIN_CONTROL))

#define ADDR_GPIO152_PIN_CONTROL                                 0x400811A8
#define MMCR_GPIO152_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO152_PIN_CONTROL))

#define ADDR_GPIO153_PIN_CONTROL                                 0x400811AC
#define MMCR_GPIO153_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO153_PIN_CONTROL))

#define ADDR_GPIO154_PIN_CONTROL                                 0x400811B0
#define MMCR_GPIO154_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO154_PIN_CONTROL))

#define ADDR_GPIO155_PIN_CONTROL                                 0x400811B4
#define MMCR_GPIO155_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO155_PIN_CONTROL))

#define ADDR_GPIO156_PIN_CONTROL                                 0x400811B8
#define MMCR_GPIO156_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO156_PIN_CONTROL))

#define ADDR_GPIO157_PIN_CONTROL                                 0x400811BC
#define MMCR_GPIO157_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO157_PIN_CONTROL))

#define ADDR_GPIO160_PIN_CONTROL                                 0x400811C0
#define MMCR_GPIO160_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO160_PIN_CONTROL))

#define ADDR_GPIO161_PIN_CONTROL                                 0x400811C4
#define MMCR_GPIO161_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO161_PIN_CONTROL))

#define ADDR_GPIO162_PIN_CONTROL                                 0x400811C8
#define MMCR_GPIO162_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO162_PIN_CONTROL))

#define ADDR_GPIO163_PIN_CONTROL                                 0x400811CC
#define MMCR_GPIO163_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO163_PIN_CONTROL))

#define ADDR_GPIO164_PIN_CONTROL                                 0x400811D0
#define MMCR_GPIO164_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO164_PIN_CONTROL))

#define ADDR_GPIO165_PIN_CONTROL                                 0x400811D4
#define MMCR_GPIO165_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO165_PIN_CONTROL))

#define ADDR_GPIO200_PIN_CONTROL                                 0x40081200
#define MMCR_GPIO200_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO200_PIN_CONTROL))

#define ADDR_GPIO201_PIN_CONTROL                                 0x40081204
#define MMCR_GPIO201_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO201_PIN_CONTROL))

#define ADDR_GPIO202_PIN_CONTROL                                 0x40081208
#define MMCR_GPIO202_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO202_PIN_CONTROL))

#define ADDR_GPIO203_PIN_CONTROL                                 0x4008120C
#define MMCR_GPIO203_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO203_PIN_CONTROL))

#define ADDR_GPIO204_PIN_CONTROL                                 0x40081210
#define MMCR_GPIO204_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO204_PIN_CONTROL))

#define ADDR_GPIO206_PIN_CONTROL                                 0x40081218
#define MMCR_GPIO206_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO206_PIN_CONTROL))

#define ADDR_GPIO210_PIN_CONTROL                                 0x40081220
#define MMCR_GPIO210_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO210_PIN_CONTROL))

#define ADDR_GPIO211_PIN_CONTROL                                 0x40081224
#define MMCR_GPIO211_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO211_PIN_CONTROL))

#define ADDR_GPIO212_PIN_CONTROL                                 0x40081228
#define MMCR_GPIO212_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO212_PIN_CONTROL))

#define ADDR_GPIO213_PIN_CONTROL                                 0x4008122C
#define MMCR_GPIO213_PIN_CONTROL                                 (*(VUINT32 *)(ADDR_GPIO213_PIN_CONTROL))

#define ADDR_GPIO_OUTPUT_GPIO_000_036                            0x40081280
#define MMCR_GPIO_OUTPUT_GPIO_000_036                            (*(VUINT32 *)(ADDR_GPIO_OUTPUT_GPIO_000_036))

#define ADDR_GPIO_OUTPUT_GPIO_040_076                            0x40081284
#define MMCR_GPIO_OUTPUT_GPIO_040_076                            (*(VUINT32 *)(ADDR_GPIO_OUTPUT_GPIO_040_076))

#define ADDR_GPIO_OUTPUT_GPIO_100_136                            0x40081288
#define MMCR_GPIO_OUTPUT_GPIO_100_136                            (*(VUINT32 *)(ADDR_GPIO_OUTPUT_GPIO_100_136))

#define ADDR_GPIO_OUTPUT_GPIO_140_176                            0x4008128C
#define MMCR_GPIO_OUTPUT_GPIO_140_176                            (*(VUINT32 *)(ADDR_GPIO_OUTPUT_GPIO_140_176))

#define ADDR_GPIO_OUTPUT_GPIO_200_236                            0x40081290
#define MMCR_GPIO_OUTPUT_GPIO_200_236                            (*(VUINT32 *)(ADDR_GPIO_OUTPUT_GPIO_200_236))

#define ADDR_GPIO_INPUT_GPIO_000_036                             0x40081300
#define MMCR_GPIO_INPUT_GPIO_000_036                             (*(VUINT32 *)(ADDR_GPIO_INPUT_GPIO_000_036))

#define ADDR_GPIO_INPUT_GPIO_040_076                             0x40081304
#define MMCR_GPIO_INPUT_GPIO_040_076                             (*(VUINT32 *)(ADDR_GPIO_INPUT_GPIO_040_076))

#define ADDR_GPIO_INPUT_GPIO_100_136                             0x40081308
#define MMCR_GPIO_INPUT_GPIO_100_136                             (*(VUINT32 *)(ADDR_GPIO_INPUT_GPIO_100_136))

#define ADDR_GPIO_INPUT_GPIO_140_176                             0x4008130C
#define MMCR_GPIO_INPUT_GPIO_140_176                             (*(VUINT32 *)(ADDR_GPIO_INPUT_GPIO_140_176))

#define ADDR_GPIO_INPUT_GPIO_200_236                             0x40081310
#define MMCR_GPIO_INPUT_GPIO_200_236                             (*(VUINT32 *)(ADDR_GPIO_INPUT_GPIO_200_236))

#define ADDR_GPIO_LOCK_4                                         0x400813EC
#define MMCR_GPIO_LOCK_4                                         (*(VUINT32 *)(ADDR_GPIO_LOCK_4))

#define ADDR_GPIO_LOCK_3                                         0x400813F0
#define MMCR_GPIO_LOCK_3                                         (*(VUINT32 *)(ADDR_GPIO_LOCK_3))

#define ADDR_GPIO_LOCK_2                                         0x400813F4
#define MMCR_GPIO_LOCK_2                                         (*(VUINT32 *)(ADDR_GPIO_LOCK_2))

#define ADDR_GPIO_LOCK_1                                         0x400813F8
#define MMCR_GPIO_LOCK_1                                         (*(VUINT32 *)(ADDR_GPIO_LOCK_1))

#define ADDR_GPIO_LOCK_0                                         0x400813FC
#define MMCR_GPIO_LOCK_0                                         (*(VUINT32 *)(ADDR_GPIO_LOCK_0))

#define ADDR_GPIO000_PIN_CONTROL_2                               0x40081500
#define MMCR_GPIO000_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO000_PIN_CONTROL_2))

#define ADDR_GPIO001_PIN_CONTROL_2                               0x40081504
#define MMCR_GPIO001_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO001_PIN_CONTROL_2))

#define ADDR_GPIO002_PIN_CONTROL_2                               0x40081508
#define MMCR_GPIO002_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO002_PIN_CONTROL_2))

#define ADDR_GPIO003_PIN_CONTROL_2                               0x4008150C
#define MMCR_GPIO003_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO003_PIN_CONTROL_2))

#define ADDR_GPIO004_PIN_CONTROL_2                               0x40081510
#define MMCR_GPIO004_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO004_PIN_CONTROL_2))

#define ADDR_GPIO005_PIN_CONTROL_2                               0x40081514
#define MMCR_GPIO005_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO005_PIN_CONTROL_2))

#define ADDR_GPIO006_PIN_CONTROL_2                               0x40081518
#define MMCR_GPIO006_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO006_PIN_CONTROL_2))

#define ADDR_GPIO007_PIN_CONTROL_2                               0x4008151C
#define MMCR_GPIO007_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO007_PIN_CONTROL_2))

#define ADDR_GPIO010_PIN_CONTROL_2                               0x40081520
#define MMCR_GPIO010_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO010_PIN_CONTROL_2))

#define ADDR_GPIO011_PIN_CONTROL_2                               0x40081524
#define MMCR_GPIO011_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO011_PIN_CONTROL_2))

#define ADDR_GPIO012_PIN_CONTROL_2                               0x40081528
#define MMCR_GPIO012_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO012_PIN_CONTROL_2))

#define ADDR_GPIO013_PIN_CONTROL_2                               0x4008152C
#define MMCR_GPIO013_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO013_PIN_CONTROL_2))

#define ADDR_GPIO014_PIN_CONTROL_2                               0x40081530
#define MMCR_GPIO014_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO014_PIN_CONTROL_2))

#define ADDR_GPIO015_PIN_CONTROL_2                               0x40081534
#define MMCR_GPIO015_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO015_PIN_CONTROL_2))

#define ADDR_GPIO016_PIN_CONTROL_2                               0x40081538
#define MMCR_GPIO016_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO016_PIN_CONTROL_2))

#define ADDR_GPIO017_PIN_CONTROL_2                               0x4008153C
#define MMCR_GPIO017_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO017_PIN_CONTROL_2))

#define ADDR_GPIO020_PIN_CONTROL_2                               0x40081540
#define MMCR_GPIO020_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO020_PIN_CONTROL_2))

#define ADDR_GPIO021_PIN_CONTROL_2                               0x40081544
#define MMCR_GPIO021_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO021_PIN_CONTROL_2))

#define ADDR_GPIO022_PIN_CONTROL_2                               0x40081548
#define MMCR_GPIO022_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO022_PIN_CONTROL_2))

#define ADDR_GPIO023_PIN_CONTROL_2                               0x4008154C
#define MMCR_GPIO023_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO023_PIN_CONTROL_2))

#define ADDR_GPIO024_PIN_CONTROL_2                               0x40081550
#define MMCR_GPIO024_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO024_PIN_CONTROL_2))

#define ADDR_GPIO025_PIN_CONTROL_2                               0x40081554
#define MMCR_GPIO025_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO025_PIN_CONTROL_2))

#define ADDR_GPIO026_PIN_CONTROL_2                               0x40081558
#define MMCR_GPIO026_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO026_PIN_CONTROL_2))

#define ADDR_GPIO027_PIN_CONTROL_2                               0x4008155C
#define MMCR_GPIO027_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO027_PIN_CONTROL_2))

#define ADDR_GPIO030_PIN_CONTROL_2                               0x40081560
#define MMCR_GPIO030_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO030_PIN_CONTROL_2))

#define ADDR_GPIO031_PIN_CONTROL_2                               0x40081564
#define MMCR_GPIO031_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO031_PIN_CONTROL_2))

#define ADDR_GPIO032_PIN_CONTROL_2                               0x40081568
#define MMCR_GPIO032_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO032_PIN_CONTROL_2))

#define ADDR_GPIO033_PIN_CONTROL_2                               0x4008156C
#define MMCR_GPIO033_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO033_PIN_CONTROL_2))

#define ADDR_GPIO034_PIN_CONTROL_2                               0x40081570
#define MMCR_GPIO034_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO034_PIN_CONTROL_2))

#define ADDR_GPIO035_PIN_CONTROL_2                               0x40081574
#define MMCR_GPIO035_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO035_PIN_CONTROL_2))

#define ADDR_GPIO036_PIN_CONTROL_2                               0x40081578
#define MMCR_GPIO036_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO036_PIN_CONTROL_2))

#define ADDR_GPIO040_PIN_CONTROL_2                               0x40081580
#define MMCR_GPIO040_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO040_PIN_CONTROL_2))

#define ADDR_GPIO041_PIN_CONTROL_2                               0x40081584
#define MMCR_GPIO041_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO041_PIN_CONTROL_2))

#define ADDR_GPIO042_PIN_CONTROL_2                               0x40081588
#define MMCR_GPIO042_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO042_PIN_CONTROL_2))

#define ADDR_GPIO043_PIN_CONTROL_2                               0x4008158C
#define MMCR_GPIO043_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO043_PIN_CONTROL_2))

#define ADDR_GPIO044_PIN_CONTROL_2                               0x40081590
#define MMCR_GPIO044_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO044_PIN_CONTROL_2))

#define ADDR_GPIO045_PIN_CONTROL_2                               0x40081594
#define MMCR_GPIO045_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO045_PIN_CONTROL_2))

#define ADDR_GPIO046_PIN_CONTROL_2                               0x40081598
#define MMCR_GPIO046_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO046_PIN_CONTROL_2))

#define ADDR_GPIO047_PIN_CONTROL_2                               0x4008159C
#define MMCR_GPIO047_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO047_PIN_CONTROL_2))

#define ADDR_GPIO050_PIN_CONTROL_2                               0x400815A0
#define MMCR_GPIO050_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO050_PIN_CONTROL_2))

#define ADDR_GPIO051_PIN_CONTROL_2                               0x400815A4
#define MMCR_GPIO051_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO051_PIN_CONTROL_2))

#define ADDR_GPIO052_PIN_CONTROL_2                               0x400815A8
#define MMCR_GPIO052_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO052_PIN_CONTROL_2))

#define ADDR_GPIO053_PIN_CONTROL_2                               0x400815AC
#define MMCR_GPIO053_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO053_PIN_CONTROL_2))

#define ADDR_GPIO054_PIN_CONTROL_2                               0x400815B0
#define MMCR_GPIO054_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO054_PIN_CONTROL_2))

#define ADDR_GPIO055_PIN_CONTROL_2                               0x400815B4
#define MMCR_GPIO055_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO055_PIN_CONTROL_2))

#define ADDR_GPIO056_PIN_CONTROL_2                               0x400815B8
#define MMCR_GPIO056_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO056_PIN_CONTROL_2))

#define ADDR_GPIO057_PIN_CONTROL_2                               0x400815BC
#define MMCR_GPIO057_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO057_PIN_CONTROL_2))

#define ADDR_GPIO060_PIN_CONTROL_2                               0x400815C0
#define MMCR_GPIO060_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO060_PIN_CONTROL_2))

#define ADDR_GPIO061_PIN_CONTROL_2                               0x400815C4
#define MMCR_GPIO061_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO061_PIN_CONTROL_2))

#define ADDR_GPIO062_PIN_CONTROL_2                               0x400815C8
#define MMCR_GPIO062_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO062_PIN_CONTROL_2))

#define ADDR_GPIO063_PIN_CONTROL_2                               0x400815CC
#define MMCR_GPIO063_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO063_PIN_CONTROL_2))

#define ADDR_GPIO064_PIN_CONTROL_2                               0x400815D0
#define MMCR_GPIO064_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO064_PIN_CONTROL_2))

#define ADDR_GPIO065_PIN_CONTROL_2                               0x400815D4
#define MMCR_GPIO065_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO065_PIN_CONTROL_2))

#define ADDR_GPIO066_PIN_CONTROL_2                               0x400815D8
#define MMCR_GPIO066_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO066_PIN_CONTROL_2))

#define ADDR_GPIO067_PIN_CONTROL_2                               0x400815DC
#define MMCR_GPIO067_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO067_PIN_CONTROL_2))

#define ADDR_GPIO100_PIN_CONTROL_2                               0x400815E0
#define MMCR_GPIO100_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO100_PIN_CONTROL_2))

#define ADDR_GPIO101_PIN_CONTROL_2                               0x400815E4
#define MMCR_GPIO101_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO101_PIN_CONTROL_2))

#define ADDR_GPIO102_PIN_CONTROL_2                               0x400815E8
#define MMCR_GPIO102_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO102_PIN_CONTROL_2))

#define ADDR_GPIO103_PIN_CONTROL_2                               0x400815EC
#define MMCR_GPIO103_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO103_PIN_CONTROL_2))

#define ADDR_GPIO104_PIN_CONTROL_2                               0x400815F0
#define MMCR_GPIO104_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO104_PIN_CONTROL_2))

#define ADDR_GPIO105_PIN_CONTROL_2                               0x400815F4
#define MMCR_GPIO105_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO105_PIN_CONTROL_2))

#define ADDR_GPIO106_PIN_CONTROL_2                               0x400815F8
#define MMCR_GPIO106_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO106_PIN_CONTROL_2))

#define ADDR_GPIO107_PIN_CONTROL_2                               0x400815FC
#define MMCR_GPIO107_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO107_PIN_CONTROL_2))

#define ADDR_GPIO110_PIN_CONTROL_2                               0x40081600
#define MMCR_GPIO110_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO110_PIN_CONTROL_2))

#define ADDR_GPIO111_PIN_CONTROL_2                               0x40081604
#define MMCR_GPIO111_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO111_PIN_CONTROL_2))

#define ADDR_GPIO112_PIN_CONTROL_2                               0x40081608
#define MMCR_GPIO112_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO112_PIN_CONTROL_2))

#define ADDR_GPIO113_PIN_CONTROL_2                               0x4008160C
#define MMCR_GPIO113_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO113_PIN_CONTROL_2))

#define ADDR_GPIO114_PIN_CONTROL_2                               0x40081610
#define MMCR_GPIO114_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO114_PIN_CONTROL_2))

#define ADDR_GPIO115_PIN_CONTROL_2                               0x40081614
#define MMCR_GPIO115_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO115_PIN_CONTROL_2))

#define ADDR_GPIO116_PIN_CONTROL_2                               0x40081618
#define MMCR_GPIO116_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO116_PIN_CONTROL_2))

#define ADDR_GPIO117_PIN_CONTROL_2                               0x4008161C
#define MMCR_GPIO117_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO117_PIN_CONTROL_2))

#define ADDR_GPIO120_PIN_CONTROL_2                               0x40081620
#define MMCR_GPIO120_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO120_PIN_CONTROL_2))

#define ADDR_GPIO121_PIN_CONTROL_2                               0x40081624
#define MMCR_GPIO121_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO121_PIN_CONTROL_2))

#define ADDR_GPIO122_PIN_CONTROL_2                               0x40081628
#define MMCR_GPIO122_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO122_PIN_CONTROL_2))

#define ADDR_GPIO123_PIN_CONTROL_2                               0x4008162C
#define MMCR_GPIO123_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO123_PIN_CONTROL_2))

#define ADDR_GPIO124_PIN_CONTROL_2                               0x40081630
#define MMCR_GPIO124_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO124_PIN_CONTROL_2))

#define ADDR_GPIO125_PIN_CONTROL_2                               0x40081634
#define MMCR_GPIO125_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO125_PIN_CONTROL_2))

#define ADDR_GPIO126_PIN_CONTROL_2                               0x40081638
#define MMCR_GPIO126_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO126_PIN_CONTROL_2))

#define ADDR_GPIO127_PIN_CONTROL_2                               0x4008163C
#define MMCR_GPIO127_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO127_PIN_CONTROL_2))

#define ADDR_GPIO130_PIN_CONTROL_2                               0x40081640
#define MMCR_GPIO130_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO130_PIN_CONTROL_2))

#define ADDR_GPIO131_PIN_CONTROL_2                               0x40081644
#define MMCR_GPIO131_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO131_PIN_CONTROL_2))

#define ADDR_GPIO132_PIN_CONTROL_2                               0x40081648
#define MMCR_GPIO132_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO132_PIN_CONTROL_2))

#define ADDR_GPIO133_PIN_CONTROL_2                               0x4008164C
#define MMCR_GPIO133_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO133_PIN_CONTROL_2))

#define ADDR_GPIO134_PIN_CONTROL_2                               0x40081650
#define MMCR_GPIO134_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO134_PIN_CONTROL_2))

#define ADDR_GPIO135_PIN_CONTROL_2                               0x40081654
#define MMCR_GPIO135_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO135_PIN_CONTROL_2))

#define ADDR_GPIO136_PIN_CONTROL_2                               0x40081658
#define MMCR_GPIO136_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO136_PIN_CONTROL_2))

#define ADDR_GPIO140_PIN_CONTROL_2                               0x40081660
#define MMCR_GPIO140_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO140_PIN_CONTROL_2))

#define ADDR_GPIO141_PIN_CONTROL_2                               0x40081664
#define MMCR_GPIO141_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO141_PIN_CONTROL_2))

#define ADDR_GPIO142_PIN_CONTROL_2                               0x40081668
#define MMCR_GPIO142_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO142_PIN_CONTROL_2))

#define ADDR_GPIO143_PIN_CONTROL_2                               0x4008166C
#define MMCR_GPIO143_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO143_PIN_CONTROL_2))

#define ADDR_GPIO144_PIN_CONTROL_2                               0x40081670
#define MMCR_GPIO144_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO144_PIN_CONTROL_2))

#define ADDR_GPIO145_PIN_CONTROL_2                               0x40081674
#define MMCR_GPIO145_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO145_PIN_CONTROL_2))

#define ADDR_GPIO146_PIN_CONTROL_2                               0x40081678
#define MMCR_GPIO146_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO146_PIN_CONTROL_2))

#define ADDR_GPIO147_PIN_CONTROL_2                               0x4008167C
#define MMCR_GPIO147_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO147_PIN_CONTROL_2))

#define ADDR_GPIO150_PIN_CONTROL_2                               0x40081680
#define MMCR_GPIO150_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO150_PIN_CONTROL_2))

#define ADDR_GPIO151_PIN_CONTROL_2                               0x40081684
#define MMCR_GPIO151_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO151_PIN_CONTROL_2))

#define ADDR_GPIO152_PIN_CONTROL_2                               0x40081688
#define MMCR_GPIO152_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO152_PIN_CONTROL_2))

#define ADDR_GPIO153_PIN_CONTROL_2                               0x4008168C
#define MMCR_GPIO153_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO153_PIN_CONTROL_2))

#define ADDR_GPIO154_PIN_CONTROL_2                               0x40081690
#define MMCR_GPIO154_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO154_PIN_CONTROL_2))

#define ADDR_GPIO155_PIN_CONTROL_2                               0x40081694
#define MMCR_GPIO155_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO155_PIN_CONTROL_2))

#define ADDR_GPIO156_PIN_CONTROL_2                               0x40081698
#define MMCR_GPIO156_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO156_PIN_CONTROL_2))

#define ADDR_GPIO157_PIN_CONTROL_2                               0x4008169C
#define MMCR_GPIO157_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO157_PIN_CONTROL_2))

#define ADDR_GPIO160_PIN_CONTROL_2                               0x400816A0
#define MMCR_GPIO160_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO160_PIN_CONTROL_2))

#define ADDR_GPIO161_PIN_CONTROL_2                               0x400816A4
#define MMCR_GPIO161_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO161_PIN_CONTROL_2))

#define ADDR_GPIO162_PIN_CONTROL_2                               0x400816A8
#define MMCR_GPIO162_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO162_PIN_CONTROL_2))

#define ADDR_GPIO163_PIN_CONTROL_2                               0x400816AC
#define MMCR_GPIO163_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO163_PIN_CONTROL_2))

#define ADDR_GPIO164_PIN_CONTROL_2                               0x400816B0
#define MMCR_GPIO164_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO164_PIN_CONTROL_2))

#define ADDR_GPIO165_PIN_CONTROL_2                               0x400816B4
#define MMCR_GPIO165_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO165_PIN_CONTROL_2))

#define ADDR_GPIO200_PIN_CONTROL_2                               0x40081720
#define MMCR_GPIO200_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO200_PIN_CONTROL_2))

#define ADDR_GPIO201_PIN_CONTROL_2                               0x40081724
#define MMCR_GPIO201_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO201_PIN_CONTROL_2))

#define ADDR_GPIO202_PIN_CONTROL_2                               0x40081728
#define MMCR_GPIO202_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO202_PIN_CONTROL_2))

#define ADDR_GPIO203_PIN_CONTROL_2                               0x4008172C
#define MMCR_GPIO203_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO203_PIN_CONTROL_2))

#define ADDR_GPIO204_PIN_CONTROL_2                               0x40081730
#define MMCR_GPIO204_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO204_PIN_CONTROL_2))

#define ADDR_GPIO206_PIN_CONTROL_2                               0x40081738
#define MMCR_GPIO206_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO206_PIN_CONTROL_2))

#define ADDR_GPIO210_PIN_CONTROL_2                               0x40081740
#define MMCR_GPIO210_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO210_PIN_CONTROL_2))

#define ADDR_GPIO211_PIN_CONTROL_2                               0x40081744
#define MMCR_GPIO211_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO211_PIN_CONTROL_2))

#define ADDR_GPIO212_PIN_CONTROL_2                               0x40081748
#define MMCR_GPIO212_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO212_PIN_CONTROL_2))

#define ADDR_GPIO213_PIN_CONTROL_2                               0x4008174C
#define MMCR_GPIO213_PIN_CONTROL_2                               (*(VUINT32 *)(ADDR_GPIO213_PIN_CONTROL_2))

/***************************************************************
*                            DMA
***************************************************************/
#define ADDR_DMA_MAIN_CONTROL                                    0x40002400
#define MMCR_DMA_MAIN_CONTROL                                    (*(VUINT8 *)(ADDR_DMA_MAIN_CONTROL))

#define ADDR_DMA_AFIFO_DATA                                      0x40002404
#define MMCR_DMA_AFIFO_DATA                                      (*(VUINT32 *)(ADDR_DMA_AFIFO_DATA))

#define ADDR_DMA_MAIN_DEBUG                                      0x40002408
#define MMCR_DMA_MAIN_DEBUG                                      (*(VUINT8 *)(ADDR_DMA_MAIN_DEBUG))

#define ADDR_DMA_CH0_ACTIVATE                                    0x40002410
#define MMCR_DMA_CH0_ACTIVATE                                    (*(VUINT32 *)(ADDR_DMA_CH0_ACTIVATE))

#define ADDR_DMA_CH0_MEMORY_START_ADDRESS                        0x40002414
#define MMCR_DMA_CH0_MEMORY_START_ADDRESS                        (*(VUINT32 *)(ADDR_DMA_CH0_MEMORY_START_ADDRESS))

#define ADDR_DMA_CH0_MEMORY_END_ADDRESS                          0x40002418
#define MMCR_DMA_CH0_MEMORY_END_ADDRESS                          (*(VUINT32 *)(ADDR_DMA_CH0_MEMORY_END_ADDRESS))

#define ADDR_DMA_CH0_AHB_ADDRESS                                 0x4000241C
#define MMCR_DMA_CH0_AHB_ADDRESS                                 (*(VUINT32 *)(ADDR_DMA_CH0_AHB_ADDRESS))

#define ADDR_DMA_CH0_CONTROL                                     0x40002420
#define MMCR_DMA_CH0_CONTROL                                     (*(VUINT32 *)(ADDR_DMA_CH0_CONTROL))

#define ADDR_DMA_CH0_CHANNEL_INTERRUPT_STATUS                    0x40002424
#define MMCR_DMA_CH0_CHANNEL_INTERRUPT_STATUS                    (*(VUINT32 *)(ADDR_DMA_CH0_CHANNEL_INTERRUPT_STATUS))

#define ADDR_DMA_CH0_CHANNEL_INTERRUPT_ENABLE                    0x40002428
#define MMCR_DMA_CH0_CHANNEL_INTERRUPT_ENABLE                    (*(VUINT32 *)(ADDR_DMA_CH0_CHANNEL_INTERRUPT_ENABLE))

#define ADDR_DMA_CH0_TEST                                        0x4000242C
#define MMCR_DMA_CH0_TEST                                        (*(VUINT32 *)(ADDR_DMA_CH0_TEST))

#define ADDR_DMA_CH1_ACTIVATE                                    0x40002430
#define MMCR_DMA_CH1_ACTIVATE                                    (*(VUINT32 *)(ADDR_DMA_CH1_ACTIVATE))

#define ADDR_DMA_CH1_MEMORY_START_ADDRESS                        0x40002434
#define MMCR_DMA_CH1_MEMORY_START_ADDRESS                        (*(VUINT32 *)(ADDR_DMA_CH1_MEMORY_START_ADDRESS))

#define ADDR_DMA_CH1_MEMORY_END_ADDRESS                          0x40002438
#define MMCR_DMA_CH1_MEMORY_END_ADDRESS                          (*(VUINT32 *)(ADDR_DMA_CH1_MEMORY_END_ADDRESS))

#define ADDR_DMA_CH1_AHB_ADDRESS                                 0x4000243C
#define MMCR_DMA_CH1_AHB_ADDRESS                                 (*(VUINT32 *)(ADDR_DMA_CH1_AHB_ADDRESS))

#define ADDR_DMA_CH1_CONTROL                                     0x40002440
#define MMCR_DMA_CH1_CONTROL                                     (*(VUINT32 *)(ADDR_DMA_CH1_CONTROL))

#define ADDR_DMA_CH1_CHANNEL_INTERRUPT_STATUS                    0x40002444
#define MMCR_DMA_CH1_CHANNEL_INTERRUPT_STATUS                    (*(VUINT32 *)(ADDR_DMA_CH1_CHANNEL_INTERRUPT_STATUS))

#define ADDR_DMA_CH1_CHANNEL_INTERRUPT_ENABLE                    0x40002448
#define MMCR_DMA_CH1_CHANNEL_INTERRUPT_ENABLE                    (*(VUINT32 *)(ADDR_DMA_CH1_CHANNEL_INTERRUPT_ENABLE))

#define ADDR_DMA_CH1_TEST                                        0x4000244C
#define MMCR_DMA_CH1_TEST                                        (*(VUINT32 *)(ADDR_DMA_CH1_TEST))

#define ADDR_DMA_CH10_ACTIVATE                                   0x40002550
#define MMCR_DMA_CH10_ACTIVATE                                   (*(VUINT32 *)(ADDR_DMA_CH10_ACTIVATE))

#define ADDR_DMA_CH10_MEMORY_START_ADDRESS                       0x40002554
#define MMCR_DMA_CH10_MEMORY_START_ADDRESS                       (*(VUINT32 *)(ADDR_DMA_CH10_MEMORY_START_ADDRESS))

#define ADDR_DMA_CH10_MEMORY_END_ADDRESS                         0x40002558
#define MMCR_DMA_CH10_MEMORY_END_ADDRESS                         (*(VUINT32 *)(ADDR_DMA_CH10_MEMORY_END_ADDRESS))

#define ADDR_DMA_CH10_AHB_ADDRESS                                0x4000255C
#define MMCR_DMA_CH10_AHB_ADDRESS                                (*(VUINT32 *)(ADDR_DMA_CH10_AHB_ADDRESS))

#define ADDR_DMA_CH10_CONTROL                                    0x40002560
#define MMCR_DMA_CH10_CONTROL                                    (*(VUINT32 *)(ADDR_DMA_CH10_CONTROL))

#define ADDR_DMA_CH10_CHANNEL_INTERRUPT_STATUS                   0x40002564
#define MMCR_DMA_CH10_CHANNEL_INTERRUPT_STATUS                   (*(VUINT32 *)(ADDR_DMA_CH10_CHANNEL_INTERRUPT_STATUS))

#define ADDR_DMA_CH10_CHANNEL_INTERRUPT_ENABLE                   0x40002568
#define MMCR_DMA_CH10_CHANNEL_INTERRUPT_ENABLE                   (*(VUINT32 *)(ADDR_DMA_CH10_CHANNEL_INTERRUPT_ENABLE))

#define ADDR_DMA_CH10_TEST                                       0x4000256C
#define MMCR_DMA_CH10_TEST                                       (*(VUINT32 *)(ADDR_DMA_CH10_TEST))

#define ADDR_DMA_CH11_ACTIVATE                                   0x40002570
#define MMCR_DMA_CH11_ACTIVATE                                   (*(VUINT32 *)(ADDR_DMA_CH11_ACTIVATE))

#define ADDR_DMA_CH11_MEMORY_START_ADDRESS                       0x40002574
#define MMCR_DMA_CH11_MEMORY_START_ADDRESS                       (*(VUINT32 *)(ADDR_DMA_CH11_MEMORY_START_ADDRESS))

#define ADDR_DMA_CH11_MEMORY_END_ADDRESS                         0x40002578
#define MMCR_DMA_CH11_MEMORY_END_ADDRESS                         (*(VUINT32 *)(ADDR_DMA_CH11_MEMORY_END_ADDRESS))

#define ADDR_DMA_CH11_AHB_ADDRESS                                0x4000257C
#define MMCR_DMA_CH11_AHB_ADDRESS                                (*(VUINT32 *)(ADDR_DMA_CH11_AHB_ADDRESS))

#define ADDR_DMA_CH11_CONTROL                                    0x40002580
#define MMCR_DMA_CH11_CONTROL                                    (*(VUINT32 *)(ADDR_DMA_CH11_CONTROL))

#define ADDR_DMA_CH11_CHANNEL_INTERRUPT_STATUS                   0x40002584
#define MMCR_DMA_CH11_CHANNEL_INTERRUPT_STATUS                   (*(VUINT32 *)(ADDR_DMA_CH11_CHANNEL_INTERRUPT_STATUS))

#define ADDR_DMA_CH11_CHANNEL_INTERRUPT_ENABLE                   0x40002588
#define MMCR_DMA_CH11_CHANNEL_INTERRUPT_ENABLE                   (*(VUINT32 *)(ADDR_DMA_CH11_CHANNEL_INTERRUPT_ENABLE))

#define ADDR_DMA_CH11_TEST                                       0x4000258C
#define MMCR_DMA_CH11_TEST                                       (*(VUINT32 *)(ADDR_DMA_CH11_TEST))

#define ADDR_DMA_CH2_ACTIVATE                                    0x40002450
#define MMCR_DMA_CH2_ACTIVATE                                    (*(VUINT32 *)(ADDR_DMA_CH2_ACTIVATE))

#define ADDR_DMA_CH2_MEMORY_START_ADDRESS                        0x40002454
#define MMCR_DMA_CH2_MEMORY_START_ADDRESS                        (*(VUINT32 *)(ADDR_DMA_CH2_MEMORY_START_ADDRESS))

#define ADDR_DMA_CH2_MEMORY_END_ADDRESS                          0x40002458
#define MMCR_DMA_CH2_MEMORY_END_ADDRESS                          (*(VUINT32 *)(ADDR_DMA_CH2_MEMORY_END_ADDRESS))

#define ADDR_DMA_CH2_AHB_ADDRESS                                 0x4000245C
#define MMCR_DMA_CH2_AHB_ADDRESS                                 (*(VUINT32 *)(ADDR_DMA_CH2_AHB_ADDRESS))

#define ADDR_DMA_CH2_CONTROL                                     0x40002460
#define MMCR_DMA_CH2_CONTROL                                     (*(VUINT32 *)(ADDR_DMA_CH2_CONTROL))

#define ADDR_DMA_CH2_CHANNEL_INTERRUPT_STATUS                    0x40002464
#define MMCR_DMA_CH2_CHANNEL_INTERRUPT_STATUS                    (*(VUINT32 *)(ADDR_DMA_CH2_CHANNEL_INTERRUPT_STATUS))

#define ADDR_DMA_CH2_CHANNEL_INTERRUPT_ENABLE                    0x40002468
#define MMCR_DMA_CH2_CHANNEL_INTERRUPT_ENABLE                    (*(VUINT32 *)(ADDR_DMA_CH2_CHANNEL_INTERRUPT_ENABLE))

#define ADDR_DMA_CH2_TEST                                        0x4000246C
#define MMCR_DMA_CH2_TEST                                        (*(VUINT32 *)(ADDR_DMA_CH2_TEST))

#define ADDR_DMA_CH3_ACTIVATE                                    0x40002470
#define MMCR_DMA_CH3_ACTIVATE                                    (*(VUINT32 *)(ADDR_DMA_CH3_ACTIVATE))

#define ADDR_DMA_CH3_MEMORY_START_ADDRESS                        0x40002474
#define MMCR_DMA_CH3_MEMORY_START_ADDRESS                        (*(VUINT32 *)(ADDR_DMA_CH3_MEMORY_START_ADDRESS))

#define ADDR_DMA_CH3_MEMORY_END_ADDRESS                          0x40002478
#define MMCR_DMA_CH3_MEMORY_END_ADDRESS                          (*(VUINT32 *)(ADDR_DMA_CH3_MEMORY_END_ADDRESS))

#define ADDR_DMA_CH3_AHB_ADDRESS                                 0x4000247C
#define MMCR_DMA_CH3_AHB_ADDRESS                                 (*(VUINT32 *)(ADDR_DMA_CH3_AHB_ADDRESS))

#define ADDR_DMA_CH3_CONTROL                                     0x40002480
#define MMCR_DMA_CH3_CONTROL                                     (*(VUINT32 *)(ADDR_DMA_CH3_CONTROL))

#define ADDR_DMA_CH3_CHANNEL_INTERRUPT_STATUS                    0x40002484
#define MMCR_DMA_CH3_CHANNEL_INTERRUPT_STATUS                    (*(VUINT32 *)(ADDR_DMA_CH3_CHANNEL_INTERRUPT_STATUS))

#define ADDR_DMA_CH3_CHANNEL_INTERRUPT_ENABLE                    0x40002488
#define MMCR_DMA_CH3_CHANNEL_INTERRUPT_ENABLE                    (*(VUINT32 *)(ADDR_DMA_CH3_CHANNEL_INTERRUPT_ENABLE))

#define ADDR_DMA_CH3_TEST                                        0x4000248C
#define MMCR_DMA_CH3_TEST                                        (*(VUINT32 *)(ADDR_DMA_CH3_TEST))

#define ADDR_DMA_CH4_ACTIVATE                                    0x40002490
#define MMCR_DMA_CH4_ACTIVATE                                    (*(VUINT32 *)(ADDR_DMA_CH4_ACTIVATE))

#define ADDR_DMA_CH4_MEMORY_START_ADDRESS                        0x40002494
#define MMCR_DMA_CH4_MEMORY_START_ADDRESS                        (*(VUINT32 *)(ADDR_DMA_CH4_MEMORY_START_ADDRESS))

#define ADDR_DMA_CH4_MEMORY_END_ADDRESS                          0x40002498
#define MMCR_DMA_CH4_MEMORY_END_ADDRESS                          (*(VUINT32 *)(ADDR_DMA_CH4_MEMORY_END_ADDRESS))

#define ADDR_DMA_CH4_AHB_ADDRESS                                 0x4000249C
#define MMCR_DMA_CH4_AHB_ADDRESS                                 (*(VUINT32 *)(ADDR_DMA_CH4_AHB_ADDRESS))

#define ADDR_DMA_CH4_CONTROL                                     0x400024A0
#define MMCR_DMA_CH4_CONTROL                                     (*(VUINT32 *)(ADDR_DMA_CH4_CONTROL))

#define ADDR_DMA_CH4_CHANNEL_INTERRUPT_STATUS                    0x400024A4
#define MMCR_DMA_CH4_CHANNEL_INTERRUPT_STATUS                    (*(VUINT32 *)(ADDR_DMA_CH4_CHANNEL_INTERRUPT_STATUS))

#define ADDR_DMA_CH4_CHANNEL_INTERRUPT_ENABLE                    0x400024A8
#define MMCR_DMA_CH4_CHANNEL_INTERRUPT_ENABLE                    (*(VUINT32 *)(ADDR_DMA_CH4_CHANNEL_INTERRUPT_ENABLE))

#define ADDR_DMA_CH4_TEST                                        0x400024AC
#define MMCR_DMA_CH4_TEST                                        (*(VUINT32 *)(ADDR_DMA_CH4_TEST))

#define ADDR_DMA_CH5_ACTIVATE                                    0x400024B0
#define MMCR_DMA_CH5_ACTIVATE                                    (*(VUINT32 *)(ADDR_DMA_CH5_ACTIVATE))

#define ADDR_DMA_CH5_MEMORY_START_ADDRESS                        0x400024B4
#define MMCR_DMA_CH5_MEMORY_START_ADDRESS                        (*(VUINT32 *)(ADDR_DMA_CH5_MEMORY_START_ADDRESS))

#define ADDR_DMA_CH5_MEMORY_END_ADDRESS                          0x400024B8
#define MMCR_DMA_CH5_MEMORY_END_ADDRESS                          (*(VUINT32 *)(ADDR_DMA_CH5_MEMORY_END_ADDRESS))

#define ADDR_DMA_CH5_AHB_ADDRESS                                 0x400024BC
#define MMCR_DMA_CH5_AHB_ADDRESS                                 (*(VUINT32 *)(ADDR_DMA_CH5_AHB_ADDRESS))

#define ADDR_DMA_CH5_CONTROL                                     0x400024C0
#define MMCR_DMA_CH5_CONTROL                                     (*(VUINT32 *)(ADDR_DMA_CH5_CONTROL))

#define ADDR_DMA_CH5_CHANNEL_INTERRUPT_STATUS                    0x400024C4
#define MMCR_DMA_CH5_CHANNEL_INTERRUPT_STATUS                    (*(VUINT32 *)(ADDR_DMA_CH5_CHANNEL_INTERRUPT_STATUS))

#define ADDR_DMA_CH5_CHANNEL_INTERRUPT_ENABLE                    0x400024C8
#define MMCR_DMA_CH5_CHANNEL_INTERRUPT_ENABLE                    (*(VUINT32 *)(ADDR_DMA_CH5_CHANNEL_INTERRUPT_ENABLE))

#define ADDR_DMA_CH5_TEST                                        0x400024CC
#define MMCR_DMA_CH5_TEST                                        (*(VUINT32 *)(ADDR_DMA_CH5_TEST))

#define ADDR_DMA_CH6_ACTIVATE                                    0x400024D0
#define MMCR_DMA_CH6_ACTIVATE                                    (*(VUINT32 *)(ADDR_DMA_CH6_ACTIVATE))

#define ADDR_DMA_CH6_MEMORY_START_ADDRESS                        0x400024D4
#define MMCR_DMA_CH6_MEMORY_START_ADDRESS                        (*(VUINT32 *)(ADDR_DMA_CH6_MEMORY_START_ADDRESS))

#define ADDR_DMA_CH6_MEMORY_END_ADDRESS                          0x400024D8
#define MMCR_DMA_CH6_MEMORY_END_ADDRESS                          (*(VUINT32 *)(ADDR_DMA_CH6_MEMORY_END_ADDRESS))

#define ADDR_DMA_CH6_AHB_ADDRESS                                 0x400024DC
#define MMCR_DMA_CH6_AHB_ADDRESS                                 (*(VUINT32 *)(ADDR_DMA_CH6_AHB_ADDRESS))

#define ADDR_DMA_CH6_CONTROL                                     0x4.00E+05
#define MMCR_DMA_CH6_CONTROL                                     (*(VUINT32 *)(ADDR_DMA_CH6_CONTROL))

#define ADDR_DMA_CH6_CHANNEL_INTERRUPT_STATUS                    0x4.00E+09
#define MMCR_DMA_CH6_CHANNEL_INTERRUPT_STATUS                    (*(VUINT32 *)(ADDR_DMA_CH6_CHANNEL_INTERRUPT_STATUS))

#define ADDR_DMA_CH6_CHANNEL_INTERRUPT_ENABLE                    0x4.00E+13
#define MMCR_DMA_CH6_CHANNEL_INTERRUPT_ENABLE                    (*(VUINT32 *)(ADDR_DMA_CH6_CHANNEL_INTERRUPT_ENABLE))

#define ADDR_DMA_CH6_TEST                                        0x400024EC
#define MMCR_DMA_CH6_TEST                                        (*(VUINT32 *)(ADDR_DMA_CH6_TEST))

#define ADDR_DMA_CH7_ACTIVATE                                    0x400024F0
#define MMCR_DMA_CH7_ACTIVATE                                    (*(VUINT32 *)(ADDR_DMA_CH7_ACTIVATE))

#define ADDR_DMA_CH7_MEMORY_START_ADDRESS                        0x400024F4
#define MMCR_DMA_CH7_MEMORY_START_ADDRESS                        (*(VUINT32 *)(ADDR_DMA_CH7_MEMORY_START_ADDRESS))

#define ADDR_DMA_CH7_MEMORY_END_ADDRESS                          0x400024F8
#define MMCR_DMA_CH7_MEMORY_END_ADDRESS                          (*(VUINT32 *)(ADDR_DMA_CH7_MEMORY_END_ADDRESS))

#define ADDR_DMA_CH7_AHB_ADDRESS                                 0x400024FC
#define MMCR_DMA_CH7_AHB_ADDRESS                                 (*(VUINT32 *)(ADDR_DMA_CH7_AHB_ADDRESS))

#define ADDR_DMA_CH7_CONTROL                                     0x40002500
#define MMCR_DMA_CH7_CONTROL                                     (*(VUINT32 *)(ADDR_DMA_CH7_CONTROL))

#define ADDR_DMA_CH7_CHANNEL_INTERRUPT_STATUS                    0x40002504
#define MMCR_DMA_CH7_CHANNEL_INTERRUPT_STATUS                    (*(VUINT32 *)(ADDR_DMA_CH7_CHANNEL_INTERRUPT_STATUS))

#define ADDR_DMA_CH7_CHANNEL_INTERRUPT_ENABLE                    0x40002508
#define MMCR_DMA_CH7_CHANNEL_INTERRUPT_ENABLE                    (*(VUINT32 *)(ADDR_DMA_CH7_CHANNEL_INTERRUPT_ENABLE))

#define ADDR_DMA_CH7_TEST                                        0x4000250C
#define MMCR_DMA_CH7_TEST                                        (*(VUINT32 *)(ADDR_DMA_CH7_TEST))

#define ADDR_DMA_CH8_ACTIVATE                                    0x40002510
#define MMCR_DMA_CH8_ACTIVATE                                    (*(VUINT32 *)(ADDR_DMA_CH8_ACTIVATE))

#define ADDR_DMA_CH8_MEMORY_START_ADDRESS                        0x40002514
#define MMCR_DMA_CH8_MEMORY_START_ADDRESS                        (*(VUINT32 *)(ADDR_DMA_CH8_MEMORY_START_ADDRESS))

#define ADDR_DMA_CH8_MEMORY_END_ADDRESS                          0x40002518
#define MMCR_DMA_CH8_MEMORY_END_ADDRESS                          (*(VUINT32 *)(ADDR_DMA_CH8_MEMORY_END_ADDRESS))

#define ADDR_DMA_CH8_AHB_ADDRESS                                 0x4000251C
#define MMCR_DMA_CH8_AHB_ADDRESS                                 (*(VUINT32 *)(ADDR_DMA_CH8_AHB_ADDRESS))

#define ADDR_DMA_CH8_CONTROL                                     0x40002520
#define MMCR_DMA_CH8_CONTROL                                     (*(VUINT32 *)(ADDR_DMA_CH8_CONTROL))

#define ADDR_DMA_CH8_CHANNEL_INTERRUPT_STATUS                    0x40002524
#define MMCR_DMA_CH8_CHANNEL_INTERRUPT_STATUS                    (*(VUINT32 *)(ADDR_DMA_CH8_CHANNEL_INTERRUPT_STATUS))

#define ADDR_DMA_CH8_CHANNEL_INTERRUPT_ENABLE                    0x40002528
#define MMCR_DMA_CH8_CHANNEL_INTERRUPT_ENABLE                    (*(VUINT32 *)(ADDR_DMA_CH8_CHANNEL_INTERRUPT_ENABLE))

#define ADDR_DMA_CH8_TEST                                        0x4000252C
#define MMCR_DMA_CH8_TEST                                        (*(VUINT32 *)(ADDR_DMA_CH8_TEST))

#define ADDR_DMA_CH9_ACTIVATE                                    0x40002530
#define MMCR_DMA_CH9_ACTIVATE                                    (*(VUINT32 *)(ADDR_DMA_CH9_ACTIVATE))

#define ADDR_DMA_CH9_MEMORY_START_ADDRESS                        0x40002534
#define MMCR_DMA_CH9_MEMORY_START_ADDRESS                        (*(VUINT32 *)(ADDR_DMA_CH9_MEMORY_START_ADDRESS))

#define ADDR_DMA_CH9_MEMORY_END_ADDRESS                          0x40002538
#define MMCR_DMA_CH9_MEMORY_END_ADDRESS                          (*(VUINT32 *)(ADDR_DMA_CH9_MEMORY_END_ADDRESS))

#define ADDR_DMA_CH9_AHB_ADDRESS                                 0x4000253C
#define MMCR_DMA_CH9_AHB_ADDRESS                                 (*(VUINT32 *)(ADDR_DMA_CH9_AHB_ADDRESS))

#define ADDR_DMA_CH9_CONTROL                                     0x40002540
#define MMCR_DMA_CH9_CONTROL                                     (*(VUINT32 *)(ADDR_DMA_CH9_CONTROL))

#define ADDR_DMA_CH9_CHANNEL_INTERRUPT_STATUS                    0x40002544
#define MMCR_DMA_CH9_CHANNEL_INTERRUPT_STATUS                    (*(VUINT32 *)(ADDR_DMA_CH9_CHANNEL_INTERRUPT_STATUS))

#define ADDR_DMA_CH9_CHANNEL_INTERRUPT_ENABLE                    0x40002548
#define MMCR_DMA_CH9_CHANNEL_INTERRUPT_ENABLE                    (*(VUINT32 *)(ADDR_DMA_CH9_CHANNEL_INTERRUPT_ENABLE))

#define ADDR_DMA_CH9_TEST                                        0x4000254C
#define MMCR_DMA_CH9_TEST                                        (*(VUINT32 *)(ADDR_DMA_CH9_TEST))

#endif /*SMSCMMCR_H_*/
