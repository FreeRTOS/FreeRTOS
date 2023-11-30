//*****************************************************************************
//
// hw_can.h - Defines and macros used when accessing the can.
//
// Copyright (c) 2006-2008 Luminary Micro, Inc.  All rights reserved.
// 
// Software License Agreement
// 
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's microcontroller products.
// 
// The software is owned by LMI and/or its suppliers, and is protected under
// applicable copyright laws.  All rights are reserved.  You may not combine
// this software with "viral" open-source software in order to form a larger
// program.  Any use in violation of the foregoing restrictions may subject
// the user to criminal sanctions under applicable laws, as well as to civil
// liability for the breach of the terms and conditions of this license.
// 
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
// 
// This is part of revision 2523 of the Stellaris Peripheral Driver Library.
//
//*****************************************************************************

#ifndef __HW_CAN_H__
#define __HW_CAN_H__

//*****************************************************************************
//
// The following are defines for the CAN register offsets.
//
//*****************************************************************************
#define CAN_O_CTL               0x00000000  // Control register
#define CAN_O_STS               0x00000004  // Status register
#define CAN_O_ERR               0x00000008  // Error register
#define CAN_O_BIT               0x0000000C  // Bit Timing register
#define CAN_O_INT               0x00000010  // Interrupt register
#define CAN_O_TST               0x00000014  // Test register
#define CAN_O_BRPE              0x00000018  // Baud Rate Prescaler register
#define CAN_O_IF1CRQ            0x00000020  // Interface 1 Command Request reg.
#define CAN_O_IF1CMSK           0x00000024  // Interface 1 Command Mask reg.
#define CAN_O_IF1MSK1           0x00000028  // Interface 1 Mask 1 register
#define CAN_O_IF1MSK2           0x0000002C  // Interface 1 Mask 2 register
#define CAN_O_IF1ARB1           0x00000030  // Interface 1 Arbitration 1 reg.
#define CAN_O_IF1ARB2           0x00000034  // Interface 1 Arbitration 2 reg.
#define CAN_O_IF1MCTL           0x00000038  // Interface 1 Message Control reg.
#define CAN_O_IF1DA1            0x0000003C  // Interface 1 DataA 1 register
#define CAN_O_IF1DA2            0x00000040  // Interface 1 DataA 2 register
#define CAN_O_IF1DB1            0x00000044  // Interface 1 DataB 1 register
#define CAN_O_IF1DB2            0x00000048  // Interface 1 DataB 2 register
#define CAN_O_IF2CRQ            0x00000080  // Interface 2 Command Request reg.
#define CAN_O_IF2CMSK           0x00000084  // Interface 2 Command Mask reg.
#define CAN_O_IF2MSK1           0x00000088  // Interface 2 Mask 1 register
#define CAN_O_IF2MSK2           0x0000008C  // Interface 2 Mask 2 register
#define CAN_O_IF2ARB1           0x00000090  // Interface 2 Arbitration 1 reg.
#define CAN_O_IF2ARB2           0x00000094  // Interface 2 Arbitration 2 reg.
#define CAN_O_IF2MCTL           0x00000098  // Interface 2 Message Control reg.
#define CAN_O_IF2DA1            0x0000009C  // Interface 2 DataA 1 register
#define CAN_O_IF2DA2            0x000000A0  // Interface 2 DataA 2 register
#define CAN_O_IF2DB1            0x000000A4  // Interface 2 DataB 1 register
#define CAN_O_IF2DB2            0x000000A8  // Interface 2 DataB 2 register
#define CAN_O_TXRQ1             0x00000100  // Transmission Request 1 register
#define CAN_O_TXRQ2             0x00000104  // Transmission Request 2 register
#define CAN_O_NWDA1             0x00000120  // New Data 1 register
#define CAN_O_NWDA2             0x00000124  // New Data 2 register
#define CAN_O_MSG1INT           0x00000140  // CAN Message 1 Interrupt Pending
#define CAN_O_MSG2INT           0x00000144  // CAN Message 2 Interrupt Pending
#define CAN_O_MSG1VAL           0x00000160  // CAN Message 1 Valid
#define CAN_O_MSG2VAL           0x00000164  // CAN Message 2 Valid

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_CTL register.
//
//*****************************************************************************
#define CAN_CTL_TEST            0x00000080  // Test mode enable
#define CAN_CTL_CCE             0x00000040  // Configuration change enable
#define CAN_CTL_DAR             0x00000020  // Disable automatic retransmission
#define CAN_CTL_EIE             0x00000008  // Error interrupt enable
#define CAN_CTL_SIE             0x00000004  // Status change interrupt enable
#define CAN_CTL_IE              0x00000002  // Module interrupt enable
#define CAN_CTL_INIT            0x00000001  // Initialization

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_STS register.
//
//*****************************************************************************
#define CAN_STS_BOFF            0x00000080  // Bus Off status
#define CAN_STS_EWARN           0x00000040  // Error Warning status
#define CAN_STS_EPASS           0x00000020  // Error Passive status
#define CAN_STS_RXOK            0x00000010  // Received Message Successful
#define CAN_STS_TXOK            0x00000008  // Transmitted Message Successful
#define CAN_STS_LEC_M           0x00000007  // Last Error Code
#define CAN_STS_LEC_NONE        0x00000000  // No error
#define CAN_STS_LEC_STUFF       0x00000001  // Stuff error
#define CAN_STS_LEC_FORM        0x00000002  // Form(at) error
#define CAN_STS_LEC_ACK         0x00000003  // Ack error
#define CAN_STS_LEC_BIT1        0x00000004  // Bit 1 error
#define CAN_STS_LEC_BIT0        0x00000005  // Bit 0 error
#define CAN_STS_LEC_CRC         0x00000006  // CRC error
#define CAN_STS_LEC_NOEVENT     0x00000007  // Unused

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_ERR register.
//
//*****************************************************************************
#define CAN_ERR_RP              0x00008000  // Receive error passive status
#define CAN_ERR_REC_M           0x00007F00  // Receive Error Counter.
#define CAN_ERR_TEC_M           0x000000FF  // Transmit Error Counter.
#define CAN_ERR_REC_S           8           // Receive error counter bit pos
#define CAN_ERR_TEC_S           0           // Transmit error counter bit pos

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_BIT register.
//
//*****************************************************************************
#define CAN_BIT_TSEG2_M         0x00007000  // Time Segment after Sample Point.
#define CAN_BIT_TSEG1_M         0x00000F00  // Time Segment Before Sample
                                            // Point.
#define CAN_BIT_SJW_M           0x000000C0  // (Re)Synchronization Jump Width.
#define CAN_BIT_BRP_M           0x0000003F  // Baud Rate Prescalar.
#define CAN_BIT_TSEG2_S         12
#define CAN_BIT_TSEG1_S         8
#define CAN_BIT_SJW_S           6
#define CAN_BIT_BRP_S           0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_INT register.
//
//*****************************************************************************
#define CAN_INT_INTID_M         0x0000FFFF  // Interrupt Identifier.
#define CAN_INT_INTID_NONE      0x00000000  // No Interrupt Pending
#define CAN_INT_INTID_STATUS    0x00008000  // Status Interrupt

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_TST register.
//
//*****************************************************************************
#define CAN_TST_RX              0x00000080  // CAN_RX pin status
#define CAN_TST_TX_M            0x00000060  // Overide control of CAN_TX pin
#define CAN_TST_TX_CANCTL       0x00000000  // CAN core controls CAN_TX
#define CAN_TST_TX_SAMPLE       0x00000020  // Sample Point on CAN_TX
#define CAN_TST_TX_DOMINANT     0x00000040  // Dominant value on CAN_TX
#define CAN_TST_TX_RECESSIVE    0x00000060  // Recessive value on CAN_TX
#define CAN_TST_LBACK           0x00000010  // Loop back mode
#define CAN_TST_SILENT          0x00000008  // Silent mode
#define CAN_TST_BASIC           0x00000004  // Basic mode

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_BRPE register.
//
//*****************************************************************************
#define CAN_BRPE_BRPE_M         0x0000000F  // Baud Rate Prescalar Extension.
#define CAN_BRPE_BRPE_S         0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_TXRQ1 register.
//
//*****************************************************************************
#define CAN_TXRQ1_TXRQST_M      0x0000FFFF  // Transmission Request Bits.
#define CAN_TXRQ1_TXRQST_S      0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_TXRQ2 register.
//
//*****************************************************************************
#define CAN_TXRQ2_TXRQST_M      0x0000FFFF  // Transmission Request Bits.
#define CAN_TXRQ2_TXRQST_S      0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_NWDA1 register.
//
//*****************************************************************************
#define CAN_NWDA1_NEWDAT_M      0x0000FFFF  // New Data Bits.
#define CAN_NWDA1_NEWDAT_S      0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_NWDA2 register.
//
//*****************************************************************************
#define CAN_NWDA2_NEWDAT_M      0x0000FFFF  // New Data Bits.
#define CAN_NWDA2_NEWDAT_S      0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF1CRQ register.
//
//*****************************************************************************
#define CAN_IF1CRQ_BUSY         0x00008000  // Busy Flag.
#define CAN_IF1CRQ_MNUM_M       0x0000003F  // Message Number.
#define CAN_IF1CRQ_MNUM_RSVD    0x00000000  // 0 is not a valid message number;
                                            // it is interpreted as 0x20, or
                                            // object 32.

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF1CMSK register.
//
//*****************************************************************************
#define CAN_IF1CMSK_WRNRD       0x00000080  // Write, Not Read.
#define CAN_IF1CMSK_MASK        0x00000040  // Access Mask Bits.
#define CAN_IF1CMSK_ARB         0x00000020  // Access Arbitration Bits.
#define CAN_IF1CMSK_CONTROL     0x00000010  // Access Control Bits.
#define CAN_IF1CMSK_CLRINTPND   0x00000008  // Clear Interrupt Pending Bit.
#define CAN_IF1CMSK_NEWDAT      0x00000004  // Access New Data.
#define CAN_IF1CMSK_TXRQST      0x00000004  // Access Transmission Request.
#define CAN_IF1CMSK_DATAA       0x00000002  // Access Data Byte 0 to 3.
#define CAN_IF1CMSK_DATAB       0x00000001  // Access Data Byte 4 to 7.

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF1MSK1 register.
//
//*****************************************************************************
#define CAN_IF1MSK1_IDMSK_M     0x0000FFFF  // Identifier Mask.
#define CAN_IF1MSK1_IDMSK_S     0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF1MSK2 register.
//
//*****************************************************************************
#define CAN_IF1MSK2_MXTD        0x00008000  // Mask Extended Identifier.
#define CAN_IF1MSK2_MDIR        0x00004000  // Mask Message Direction.
#define CAN_IF1MSK2_IDMSK_M     0x00001FFF  // Identifier Mask.
#define CAN_IF1MSK2_IDMSK_S     0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF1ARB1 register.
//
//*****************************************************************************
#define CAN_IF1ARB1_ID_M        0x0000FFFF  // Message Identifier.
#define CAN_IF1ARB1_ID_S        0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF1ARB2 register.
//
//*****************************************************************************
#define CAN_IF1ARB2_MSGVAL      0x00008000  // Message Valid.
#define CAN_IF1ARB2_XTD         0x00004000  // Extended Identifier.
#define CAN_IF1ARB2_DIR         0x00002000  // Message Direction.
#define CAN_IF1ARB2_ID_M        0x00001FFF  // Message Identifier.
#define CAN_IF1ARB2_ID_S        0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF1MCTL register.
//
//*****************************************************************************
#define CAN_IF1MCTL_NEWDAT      0x00008000  // New Data.
#define CAN_IF1MCTL_MSGLST      0x00004000  // Message Lost.
#define CAN_IF1MCTL_INTPND      0x00002000  // Interrupt Pending.
#define CAN_IF1MCTL_UMASK       0x00001000  // Use Acceptance Mask.
#define CAN_IF1MCTL_TXIE        0x00000800  // Transmit Interrupt Enable.
#define CAN_IF1MCTL_RXIE        0x00000400  // Receive Interrupt Enable.
#define CAN_IF1MCTL_RMTEN       0x00000200  // Remote Enable.
#define CAN_IF1MCTL_TXRQST      0x00000100  // Transmit Request.
#define CAN_IF1MCTL_EOB         0x00000080  // End of Buffer.
#define CAN_IF1MCTL_DLC_M       0x0000000F  // Data Length Code.
#define CAN_IF1MCTL_DLC_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF1DA1 register.
//
//*****************************************************************************
#define CAN_IF1DA1_DATA_M       0x0000FFFF  // Data.
#define CAN_IF1DA1_DATA_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF1DA2 register.
//
//*****************************************************************************
#define CAN_IF1DA2_DATA_M       0x0000FFFF  // Data.
#define CAN_IF1DA2_DATA_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF1DB1 register.
//
//*****************************************************************************
#define CAN_IF1DB1_DATA_M       0x0000FFFF  // Data.
#define CAN_IF1DB1_DATA_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF1DB2 register.
//
//*****************************************************************************
#define CAN_IF1DB2_DATA_M       0x0000FFFF  // Data.
#define CAN_IF1DB2_DATA_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF2CRQ register.
//
//*****************************************************************************
#define CAN_IF2CRQ_BUSY         0x00008000  // Busy Flag.
#define CAN_IF2CRQ_MNUM_M       0x0000003F  // Message Number.
#define CAN_IF2CRQ_MNUM_RSVD    0x00000000  // 0 is not a valid message number;
                                            // it is interpreted as 0x20, or
                                            // object 32.

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF2CMSK register.
//
//*****************************************************************************
#define CAN_IF2CMSK_WRNRD       0x00000080  // Write, Not Read.
#define CAN_IF2CMSK_MASK        0x00000040  // Access Mask Bits.
#define CAN_IF2CMSK_ARB         0x00000020  // Access Arbitration Bits.
#define CAN_IF2CMSK_CONTROL     0x00000010  // Access Control Bits.
#define CAN_IF2CMSK_CLRINTPND   0x00000008  // Clear Interrupt Pending Bit.
#define CAN_IF2CMSK_NEWDAT      0x00000004  // Access New Data.
#define CAN_IF2CMSK_TXRQST      0x00000004  // Access Transmission Request.
#define CAN_IF2CMSK_DATAA       0x00000002  // Access Data Byte 0 to 3.
#define CAN_IF2CMSK_DATAB       0x00000001  // Access Data Byte 4 to 7.

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF2MSK1 register.
//
//*****************************************************************************
#define CAN_IF2MSK1_IDMSK_M     0x0000FFFF  // Identifier Mask.
#define CAN_IF2MSK1_IDMSK_S     0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF2MSK2 register.
//
//*****************************************************************************
#define CAN_IF2MSK2_MXTD        0x00008000  // Mask Extended Identifier.
#define CAN_IF2MSK2_MDIR        0x00004000  // Mask Message Direction.
#define CAN_IF2MSK2_IDMSK_M     0x00001FFF  // Identifier Mask.
#define CAN_IF2MSK2_IDMSK_S     0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF2ARB1 register.
//
//*****************************************************************************
#define CAN_IF2ARB1_ID_M        0x0000FFFF  // Message Identifier.
#define CAN_IF2ARB1_ID_S        0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF2ARB2 register.
//
//*****************************************************************************
#define CAN_IF2ARB2_MSGVAL      0x00008000  // Message Valid.
#define CAN_IF2ARB2_XTD         0x00004000  // Extended Identifier.
#define CAN_IF2ARB2_DIR         0x00002000  // Message Direction.
#define CAN_IF2ARB2_ID_M        0x00001FFF  // Message Identifier.
#define CAN_IF2ARB2_ID_S        0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF2MCTL register.
//
//*****************************************************************************
#define CAN_IF2MCTL_NEWDAT      0x00008000  // New Data.
#define CAN_IF2MCTL_MSGLST      0x00004000  // Message Lost.
#define CAN_IF2MCTL_INTPND      0x00002000  // Interrupt Pending.
#define CAN_IF2MCTL_UMASK       0x00001000  // Use Acceptance Mask.
#define CAN_IF2MCTL_TXIE        0x00000800  // Transmit Interrupt Enable.
#define CAN_IF2MCTL_RXIE        0x00000400  // Receive Interrupt Enable.
#define CAN_IF2MCTL_RMTEN       0x00000200  // Remote Enable.
#define CAN_IF2MCTL_TXRQST      0x00000100  // Transmit Request.
#define CAN_IF2MCTL_EOB         0x00000080  // End of Buffer.
#define CAN_IF2MCTL_DLC_M       0x0000000F  // Data Length Code.
#define CAN_IF2MCTL_DLC_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF2DA1 register.
//
//*****************************************************************************
#define CAN_IF2DA1_DATA_M       0x0000FFFF  // Data.
#define CAN_IF2DA1_DATA_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF2DA2 register.
//
//*****************************************************************************
#define CAN_IF2DA2_DATA_M       0x0000FFFF  // Data.
#define CAN_IF2DA2_DATA_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF2DB1 register.
//
//*****************************************************************************
#define CAN_IF2DB1_DATA_M       0x0000FFFF  // Data.
#define CAN_IF2DB1_DATA_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_IF2DB2 register.
//
//*****************************************************************************
#define CAN_IF2DB2_DATA_M       0x0000FFFF  // Data.
#define CAN_IF2DB2_DATA_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_MSG1INT register.
//
//*****************************************************************************
#define CAN_MSG1INT_INTPND_M    0x0000FFFF  // Interrupt Pending Bits.
#define CAN_MSG1INT_INTPND_S    0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_MSG2INT register.
//
//*****************************************************************************
#define CAN_MSG2INT_INTPND_M    0x0000FFFF  // Interrupt Pending Bits.
#define CAN_MSG2INT_INTPND_S    0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_MSG1VAL register.
//
//*****************************************************************************
#define CAN_MSG1VAL_MSGVAL_M    0x0000FFFF  // Message Valid Bits.
#define CAN_MSG1VAL_MSGVAL_S    0

//*****************************************************************************
//
// The following are defines for the bit fields in the CAN_O_MSG2VAL register.
//
//*****************************************************************************
#define CAN_MSG2VAL_MSGVAL_M    0x0000FFFF  // Message Valid Bits.
#define CAN_MSG2VAL_MSGVAL_S    0

//*****************************************************************************
//
// The following definitions are deprecated.
//
//*****************************************************************************
#ifndef DEPRECATED

//*****************************************************************************
//
// The following are deprecated defines for the CAN register offsets.
//
//*****************************************************************************
#define CAN_O_MSGINT1           0x00000140  // Intr. Pending in Msg Obj 1 reg.
#define CAN_O_MSGINT2           0x00000144  // Intr. Pending in Msg Obj 2 reg.
#define CAN_O_MSGVAL1           0x00000160  // Message Valid in Msg Obj 1 reg.
#define CAN_O_MSGVAL2           0x00000164  // Message Valid in Msg Obj 2 reg.

//*****************************************************************************
//
// The following are deprecated defines for the reset values of the can
// registers.
//
//*****************************************************************************
#define CAN_RV_IF1MSK2          0x0000FFFF
#define CAN_RV_IF1MSK1          0x0000FFFF
#define CAN_RV_IF2MSK1          0x0000FFFF
#define CAN_RV_IF2MSK2          0x0000FFFF
#define CAN_RV_BIT              0x00002301
#define CAN_RV_CTL              0x00000001
#define CAN_RV_IF1CRQ           0x00000001
#define CAN_RV_IF2CRQ           0x00000001
#define CAN_RV_TXRQ2            0x00000000
#define CAN_RV_IF2DB1           0x00000000
#define CAN_RV_INT              0x00000000
#define CAN_RV_IF1DB2           0x00000000
#define CAN_RV_BRPE             0x00000000
#define CAN_RV_IF2DA2           0x00000000
#define CAN_RV_MSGVAL2          0x00000000
#define CAN_RV_TXRQ1            0x00000000
#define CAN_RV_IF1MCTL          0x00000000
#define CAN_RV_IF1DB1           0x00000000
#define CAN_RV_STS              0x00000000
#define CAN_RV_MSGINT1          0x00000000
#define CAN_RV_IF1DA2           0x00000000
#define CAN_RV_TST              0x00000000
#define CAN_RV_IF1ARB1          0x00000000
#define CAN_RV_IF1ARB2          0x00000000
#define CAN_RV_NWDA2            0x00000000
#define CAN_RV_IF2CMSK          0x00000000
#define CAN_RV_NWDA1            0x00000000
#define CAN_RV_IF1DA1           0x00000000
#define CAN_RV_IF2DA1           0x00000000
#define CAN_RV_IF2MCTL          0x00000000
#define CAN_RV_MSGVAL1          0x00000000
#define CAN_RV_IF1CMSK          0x00000000
#define CAN_RV_ERR              0x00000000
#define CAN_RV_IF2ARB2          0x00000000
#define CAN_RV_MSGINT2          0x00000000
#define CAN_RV_IF2ARB1          0x00000000
#define CAN_RV_IF2DB2           0x00000000

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_STS
// register.
//
//*****************************************************************************
#define CAN_STS_LEC_MSK         0x00000007  // Last Error Code

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_ERR
// register.
//
//*****************************************************************************
#define CAN_ERR_REC_MASK        0x00007F00  // Receive error counter status
#define CAN_ERR_TEC_MASK        0x000000FF  // Transmit error counter status
#define CAN_ERR_REC_SHIFT       8           // Receive error counter bit pos
#define CAN_ERR_TEC_SHIFT       0           // Transmit error counter bit pos

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_BIT
// register.
//
//*****************************************************************************
#define CAN_BIT_TSEG2           0x00007000  // Time segment after sample point
#define CAN_BIT_TSEG1           0x00000F00  // Time segment before sample point
#define CAN_BIT_SJW             0x000000C0  // (Re)Synchronization jump width
#define CAN_BIT_BRP             0x0000003F  // Baud rate prescaler

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_INT
// register.
//
//*****************************************************************************
#define CAN_INT_INTID_MSK       0x0000FFFF  // Interrupt Identifier

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_TST
// register.
//
//*****************************************************************************
#define CAN_TST_TX_MSK          0x00000060  // Overide control of CAN_TX pin

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_BRPE
// register.
//
//*****************************************************************************
#define CAN_BRPE_BRPE           0x0000000F  // Baud rate prescaler extension

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_IF1CRQ
// and CAN_IF1CRQ registers.
// Note: All bits may not be available in all registers
//
//*****************************************************************************
#define CAN_IFCRQ_BUSY          0x00008000  // Busy flag status
#define CAN_IFCRQ_MNUM_MSK      0x0000003F  // Message Number

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_IF1CMSK
// and CAN_IF2CMSK registers.
// Note: All bits may not be available in all registers
//
//*****************************************************************************
#define CAN_IFCMSK_WRNRD        0x00000080  // Write, not Read
#define CAN_IFCMSK_MASK         0x00000040  // Access Mask Bits
#define CAN_IFCMSK_ARB          0x00000020  // Access Arbitration Bits
#define CAN_IFCMSK_CONTROL      0x00000010  // Access Control Bits
#define CAN_IFCMSK_CLRINTPND    0x00000008  // Clear interrupt pending Bit
#define CAN_IFCMSK_TXRQST       0x00000004  // Access Tx request bit (WRNRD=1)
#define CAN_IFCMSK_NEWDAT       0x00000004  // Access New Data bit (WRNRD=0)
#define CAN_IFCMSK_DATAA        0x00000002  // DataA access - bytes 0 to 3
#define CAN_IFCMSK_DATAB        0x00000001  // DataB access - bytes 4 to 7

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_IF1MSK1
// and CAN_IF2MSK1 registers.
// Note: All bits may not be available in all registers
//
//*****************************************************************************
#define CAN_IFMSK1_MSK          0x0000FFFF  // Identifier Mask

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_IF1MSK2
// and CAN_IF2MSK2 registers.
// Note: All bits may not be available in all registers
//
//*****************************************************************************
#define CAN_IFMSK2_MXTD         0x00008000  // Mask extended identifier
#define CAN_IFMSK2_MDIR         0x00004000  // Mask message direction
#define CAN_IFMSK2_MSK          0x00001FFF  // Mask identifier

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_IF1ARB1
// and CAN_IF2ARB1 registers.
// Note: All bits may not be available in all registers
//
//*****************************************************************************
#define CAN_IFARB1_ID           0x0000FFFF  // Identifier

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_IF1ARB2
// and CAN_IF2ARB2 registers.
// Note: All bits may not be available in all registers
//
//*****************************************************************************
#define CAN_IFARB2_MSGVAL       0x00008000  // Message valid
#define CAN_IFARB2_XTD          0x00004000  // Extended identifier
#define CAN_IFARB2_DIR          0x00002000  // Message direction
#define CAN_IFARB2_ID           0x00001FFF  // Message identifier

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_IF1MCTL
// and CAN_IF2MCTL registers.
// Note: All bits may not be available in all registers
//
//*****************************************************************************
#define CAN_IFMCTL_NEWDAT       0x00008000  // New Data
#define CAN_IFMCTL_MSGLST       0x00004000  // Message lost
#define CAN_IFMCTL_INTPND       0x00002000  // Interrupt pending
#define CAN_IFMCTL_UMASK        0x00001000  // Use acceptance mask
#define CAN_IFMCTL_TXIE         0x00000800  // Transmit interrupt enable
#define CAN_IFMCTL_RXIE         0x00000400  // Receive interrupt enable
#define CAN_IFMCTL_RMTEN        0x00000200  // Remote enable
#define CAN_IFMCTL_TXRQST       0x00000100  // Transmit request
#define CAN_IFMCTL_EOB          0x00000080  // End of buffer
#define CAN_IFMCTL_DLC          0x0000000F  // Data length code

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_IF1DA1
// and CAN_IF2DA1 registers.
// Note: All bits may not be available in all registers
//
//*****************************************************************************
#define CAN_IFDA1_DATA          0x0000FFFF  // Data - bytes 1 and 0

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_IF1DA2
// and CAN_IF2DA2 registers.
// Note: All bits may not be available in all registers
//
//*****************************************************************************
#define CAN_IFDA2_DATA          0x0000FFFF  // Data - bytes 3 and 2

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_IF1DB1
// and CAN_IF2DB1 registers.
// Note: All bits may not be available in all registers
//
//*****************************************************************************
#define CAN_IFDB1_DATA          0x0000FFFF  // Data - bytes 5 and 4

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_IF1DB2
// and CAN_IF2DB2 registers.
// Note: All bits may not be available in all registers
//
//*****************************************************************************
#define CAN_IFDB2_DATA          0x0000FFFF  // Data - bytes 7 and 6

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_TXRQ1
// register.
//
//*****************************************************************************
#define CAN_TXRQ1_TXRQST        0x0000FFFF  // Transmission Request Bits

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_TXRQ2
// register.
//
//*****************************************************************************
#define CAN_TXRQ2_TXRQST        0x0000FFFF  // Transmission Request Bits

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_NWDA1
// register.
//
//*****************************************************************************
#define CAN_NWDA1_NEWDATA       0x0000FFFF  // New Data Bits

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_NWDA2
// register.
//
//*****************************************************************************
#define CAN_NWDA2_NEWDATA       0x0000FFFF  // New Data Bits

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_MSGINT1
// register.
//
//*****************************************************************************
#define CAN_MSGINT1_INTPND      0x0000FFFF  // Interrupt Pending Bits

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_MSGINT2
// register.
//
//*****************************************************************************
#define CAN_MSGINT2_INTPND      0x0000FFFF  // Interrupt Pending Bits

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_MSGVAL1
// register.
//
//*****************************************************************************
#define CAN_MSGVAL1_MSGVAL      0x0000FFFF  // Message Valid Bits

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the CAN_MSGVAL2
// register.
//
//*****************************************************************************
#define CAN_MSGVAL2_MSGVAL      0x0000FFFF  // Message Valid Bits

#endif

#endif // __HW_CAN_H__
