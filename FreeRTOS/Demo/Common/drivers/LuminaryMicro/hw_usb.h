//*****************************************************************************
//
// hw_usb.h - Macros for use in accessing the USB registers.
//
// Copyright (c) 2007-2008 Luminary Micro, Inc.  All rights reserved.
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

#ifndef __HW_USB_H__
#define __HW_USB_H__

//*****************************************************************************
//
// The following are defines for the Univeral Serial Bus (USB) Controller
// offsets.
//
//*****************************************************************************
#define USB_O_FADDR             0x00000000  // USB Device Functional Address
#define USB_O_POWER             0x00000001  // USB Power
#define USB_O_TXIS              0x00000002  // USB Transmit Interrupt Status
#define USB_O_RXIS              0x00000004  // USB Receive Interrupt Status
#define USB_O_TXIE              0x00000006  // USB Transmit Interrupt Enable
#define USB_O_RXIE              0x00000008  // USB Receive Interrupt Enable
#define USB_O_IS                0x0000000A  // USB General Interrupt Status
#define USB_O_IE                0x0000000B  // USB Interrupt Enable
#define USB_O_FRAME             0x0000000C  // USB Frame Value
#define USB_O_EPIDX             0x0000000E  // USB Endpoint Index
#define USB_O_TEST              0x0000000F  // USB Test Mode
#define USB_O_FIFO0             0x00000020  // USB FIFO Endpoint 0
#define USB_O_FIFO1             0x00000024  // USB FIFO Endpoint 1
#define USB_O_FIFO2             0x00000028  // USB FIFO Endpoint 2
#define USB_O_FIFO3             0x0000002C  // USB FIFO Endpoint 3
#define USB_O_DEVCTL            0x00000060  // USB Device Control
#define USB_O_TXFIFOSZ          0x00000062  // USB Transmit Dynamic FIFO Sizing
#define USB_O_RXFIFOSZ          0x00000063  // USB Receive Dynamic FIFO Sizing
#define USB_O_TXFIFOADD         0x00000064  // USB Transmit FIFO Start Address
#define USB_O_RXFIFOADD         0x00000066  // USB Receive FIFO Start Address
#define USB_O_CONTIM            0x0000007A  // USB Connect Timing
#define USB_O_VPLEN             0x0000007B  // USB OTG VBus Pulse Timing
#define USB_O_FSEOF             0x0000007D  // USB Full-Speed Last Transaction
                                            // to End of Frame Timing
#define USB_O_LSEOF             0x0000007E  // USB Low-Speed Last Transaction
                                            // to End of Frame Timing
#define USB_O_TXFUNCADDR0       0x00000080  // USB Transmit Functional Address
                                            // Endpoint 0
#define USB_O_TXHUBADDR0        0x00000082  // USB Transmit Hub Address
                                            // Endpoint 0
#define USB_O_TXHUBPORT0        0x00000083  // USB Transmit Hub Port Endpoint 0
#define USB_O_TXFUNCADDR1       0x00000088  // USB Transmit Functional Address
                                            // Endpoint 1
#define USB_O_TXHUBADDR1        0x0000008A  // USB Transmit Hub Address
                                            // Endpoint 1
#define USB_O_TXHUBPORT1        0x0000008B  // USB Transmit Hub Port Endpoint 1
#define USB_O_RXFUNCADDR1       0x0000008C  // USB Receive Functional Address
                                            // Endpoint 1
#define USB_O_RXHUBADDR1        0x0000008E  // USB Receive Hub Address Endpoint
                                            // 1
#define USB_O_RXHUBPORT1        0x0000008F  // USB Receive Hub Port Endpoint 1
#define USB_O_TXFUNCADDR2       0x00000090  // USB Transmit Functional Address
                                            // Endpoint 2
#define USB_O_TXHUBADDR2        0x00000092  // USB Transmit Hub Address
                                            // Endpoint 2
#define USB_O_TXHUBPORT2        0x00000093  // USB Transmit Hub Port Endpoint 2
#define USB_O_RXFUNCADDR2       0x00000094  // USB Receive Functional Address
                                            // Endpoint 2
#define USB_O_RXHUBADDR2        0x00000096  // USB Receive Hub Address Endpoint
                                            // 2
#define USB_O_RXHUBPORT2        0x00000097  // USB Receive Hub Port Endpoint 2
#define USB_O_TXFUNCADDR3       0x00000098  // USB Transmit Functional Address
                                            // Endpoint 3
#define USB_O_TXHUBADDR3        0x0000009A  // USB Transmit Hub Address
                                            // Endpoint 3
#define USB_O_TXHUBPORT3        0x0000009B  // USB Transmit Hub Port Endpoint 3
#define USB_O_RXFUNCADDR3       0x0000009C  // USB Receive Functional Address
                                            // Endpoint 3
#define USB_O_RXHUBADDR3        0x0000009E  // USB Receive Hub Address Endpoint
                                            // 3
#define USB_O_RXHUBPORT3        0x0000009F  // USB Receive Hub Port Endpoint 3
#define USB_O_CSRL0             0x00000102  // USB Control and Status Endpoint
                                            // 0 Low
#define USB_O_CSRH0             0x00000103  // USB Control and Status Endpoint
                                            // 0 High
#define USB_O_COUNT0            0x00000108  // USB Receive Byte Count Endpoint
                                            // 0
#define USB_O_TYPE0             0x0000010A  // USB Type Endpoint 0
#define USB_O_NAKLMT            0x0000010B  // USB NAK Limit
#define USB_O_TXMAXP1           0x00000110  // USB Maximum Transmit Data
                                            // Endpoint 1
#define USB_O_TXCSRL1           0x00000112  // USB Transmit Control and Status
                                            // Endpoint 1 Low
#define USB_O_TXCSRH1           0x00000113  // USB Transmit Control and Status
                                            // Endpoint 1 High
#define USB_O_RXMAXP1           0x00000114  // USB Maximum Receive Data
                                            // Endpoint 1
#define USB_O_RXCSRL1           0x00000116  // USB Receive Control and Status
                                            // Endpoint 1 Low
#define USB_O_RXCSRH1           0x00000117  // USB Receive Control and Status
                                            // Endpoint 1 High
#define USB_O_RXCOUNT1          0x00000118  // USB Receive Byte Count Endpoint
                                            // 1
#define USB_O_TXTYPE1           0x0000011A  // USB Host Transmit Configure Type
                                            // Endpoint 1
#define USB_O_TXINTERVAL1       0x0000011B  // USB Host Transmit Interval
                                            // Endpoint 1
#define USB_O_RXTYPE1           0x0000011C  // USB Host Configure Receive Type
                                            // Endpoint 1
#define USB_O_RXINTERVAL1       0x0000011D  // USB Host Receive Polling
                                            // Interval Endpoint 1
#define USB_O_TXMAXP2           0x00000120  // USB Maximum Transmit Data
                                            // Endpoint 2
#define USB_O_TXCSRL2           0x00000122  // USB Transmit Control and Status
                                            // Endpoint 2 Low
#define USB_O_TXCSRH2           0x00000123  // USB Transmit Control and Status
                                            // Endpoint 2 High
#define USB_O_RXMAXP2           0x00000124  // USB Maximum Receive Data
                                            // Endpoint 2
#define USB_O_RXCSRL2           0x00000126  // USB Receive Control and Status
                                            // Endpoint 2 Low
#define USB_O_RXCSRH2           0x00000127  // USB Receive Control and Status
                                            // Endpoint 2 High
#define USB_O_RXCOUNT2          0x00000128  // USB Receive Byte Count Endpoint
                                            // 2
#define USB_O_TXTYPE2           0x0000012A  // USB Host Transmit Configure Type
                                            // Endpoint 2
#define USB_O_TXINTERVAL2       0x0000012B  // USB Host Transmit Interval
                                            // Endpoint 2
#define USB_O_RXTYPE2           0x0000012C  // USB Host Configure Receive Type
                                            // Endpoint 2
#define USB_O_RXINTERVAL2       0x0000012D  // USB Host Receive Polling
                                            // Interval Endpoint 2
#define USB_O_TXMAXP3           0x00000130  // USB Maximum Transmit Data
                                            // Endpoint 3
#define USB_O_TXCSRL3           0x00000132  // USB Transmit Control and Status
                                            // Endpoint 3 Low
#define USB_O_TXCSRH3           0x00000133  // USB Transmit Control and Status
                                            // Endpoint 3 High
#define USB_O_RXMAXP3           0x00000134  // USB Maximum Receive Data
                                            // Endpoint 3
#define USB_O_RXCSRL3           0x00000136  // USB Receive Control and Status
                                            // Endpoint 3 Low
#define USB_O_RXCSRH3           0x00000137  // USB Receive Control and Status
                                            // Endpoint 3 High
#define USB_O_RXCOUNT3          0x00000138  // USB Receive Byte Count Endpoint
                                            // 3
#define USB_O_TXTYPE3           0x0000013A  // USB Host Transmit Configure Type
                                            // Endpoint 3
#define USB_O_TXINTERVAL3       0x0000013B  // USB Host Transmit Interval
                                            // Endpoint 3
#define USB_O_RXTYPE3           0x0000013C  // USB Host Configure Receive Type
                                            // Endpoint 3
#define USB_O_RXINTERVAL3       0x0000013D  // USB Host Receive Polling
                                            // Interval Endpoint 3
#define USB_O_RQPKTCOUNT1       0x00000304  // USB Request Packet Count in
                                            // Block Transfer Endpoint 1
#define USB_O_RQPKTCOUNT2       0x00000308  // USB Request Packet Count in
                                            // Block Transfer Endpoint 2
#define USB_O_RQPKTCOUNT3       0x0000030C  // USB Request Packet Count in
                                            // Block Transfer Endpoint 3
#define USB_O_RXDPKTBUFDIS      0x00000340  // USB Receive Double Packet Buffer
                                            // Disable
#define USB_O_TXDPKTBUFDIS      0x00000342  // USB Transmit Double Packet
                                            // Buffer Disable
#define USB_O_EPC               0x00000400  // USB External Power Control
#define USB_O_EPCRIS            0x00000404  // USB External Power Control Raw
                                            // Interrupt Status
#define USB_O_EPCIM             0x00000408  // USB External Power Control
                                            // Interrupt Mask
#define USB_O_EPCISC            0x0000040C  // USB External Power Control
                                            // Interrupt Status and Clear
#define USB_O_DRRIS             0x00000410  // USB Device Resume Raw Interrupt
                                            // Status
#define USB_O_DRIM              0x00000414  // USB Device Resume Interrupt Mask
#define USB_O_DRISC             0x00000418  // USB Device Resume Interrupt
                                            // Status and Clear
#define USB_O_GPCS              0x0000041C  // USB General-Purpose Control and
                                            // Status

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_FADDR register.
//
//*****************************************************************************
#define USB_FADDR_M             0x0000007F  // Function Address.
#define USB_FADDR_S             0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_POWER register.
//
//*****************************************************************************
#define USB_POWER_ISOUP         0x00000080  // ISO Update.
#define USB_POWER_SOFTCONN      0x00000040  // Soft Connect/Disconnect.
#define USB_POWER_RESET         0x00000008  // Reset.
#define USB_POWER_RESUME        0x00000004  // Resume Signaling.
#define USB_POWER_SUSPEND       0x00000002  // Suspend Mode.
#define USB_POWER_PWRDNPHY      0x00000001  // Power Down PHY.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXIS register.
//
//*****************************************************************************
#define USB_TXIS_EP3            0x00000008  // TX Endpoint 3 Interrupt.
#define USB_TXIS_EP2            0x00000004  // TX Endpoint 2 Interrupt.
#define USB_TXIS_EP1            0x00000002  // TX Endpoint 1 Interrupt.
#define USB_TXIS_EP0            0x00000001  // TX and RX Endpoint 0 Interrupt.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXIS register.
//
//*****************************************************************************
#define USB_RXIS_EP3            0x00000008  // RX Endpoint 3 Interrupt.
#define USB_RXIS_EP2            0x00000004  // RX Endpoint 2 Interrupt.
#define USB_RXIS_EP1            0x00000002  // RX Endpoint 1 Interrupt.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXIE register.
//
//*****************************************************************************
#define USB_TXIE_EP3            0x00000008  // TX Endpoint 3 Interrupt Enable.
#define USB_TXIE_EP2            0x00000004  // TX Endpoint 2 Interrupt Enable.
#define USB_TXIE_EP1            0x00000002  // TX Endpoint 1 Interrupt Enable.
#define USB_TXIE_EP0            0x00000001  // TX and RX Endpoint 0 Interrupt
                                            // Enable.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXIE register.
//
//*****************************************************************************
#define USB_RXIE_EP3            0x00000008  // RX Endpoint 3 Interrupt Enable.
#define USB_RXIE_EP2            0x00000004  // RX Endpoint 2 Interrupt Enable.
#define USB_RXIE_EP1            0x00000002  // RX Endpoint 1 Interrupt Enable.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_IS register.
//
//*****************************************************************************
#define USB_IS_VBUSERR          0x00000080  // VBus Error.
#define USB_IS_SESREQ           0x00000040  // Session Request.
#define USB_IS_DISCON           0x00000020  // Session Disconnect.
#define USB_IS_CONN             0x00000010  // Session Connect.
#define USB_IS_SOF              0x00000008  // Start of Frame.
#define USB_IS_BABBLE           0x00000004  // Babble Detected.
#define USB_IS_RESET            0x00000004  // Reset Signal Detected.
#define USB_IS_RESUME           0x00000002  // Resume Signal Detected.
#define USB_IS_SUSPEND          0x00000001  // Suspend Signal Detected.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_IE register.
//
//*****************************************************************************
#define USB_IE_VBUSERR          0x00000080  // Enable VBUS Error Interrupt.
#define USB_IE_SESREQ           0x00000040  // Enable Session Request
                                            // Interrupt.
#define USB_IE_DISCON           0x00000020  // Enable Disconnect Interrupt.
#define USB_IE_CONN             0x00000010  // Enable Connect Interrupt.
#define USB_IE_SOF              0x00000008  // Enable Start-of-Frame Interrupt.
#define USB_IE_BABBLE           0x00000004  // Enable Babble Interrupt.
#define USB_IE_RESET            0x00000004  // Enable Reset Interrupt.
#define USB_IE_RESUME           0x00000002  // Enable Resume Interrupt.
#define USB_IE_SUSPND           0x00000001  // Enable Suspend Interrupt.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_FRAME register.
//
//*****************************************************************************
#define USB_FRAME_M             0x000007FF  // Frame Number.
#define USB_FRAME_S             0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_EPIDX register.
//
//*****************************************************************************
#define USB_EPIDX_EPIDX_M       0x0000000F  // Endpoint Index.
#define USB_EPIDX_EPIDX_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TEST register.
//
//*****************************************************************************
#define USB_TEST_FORCEH         0x00000080  // Force Host Mode.
#define USB_TEST_FIFOACC        0x00000040  // FIFO Access.
#define USB_TEST_FORCEFS        0x00000020  // Force Full Speed.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_FIFO0 register.
//
//*****************************************************************************
#define USB_FIFO0_EPDATA_M      0xFFFFFFFF  // Endpoint Data.
#define USB_FIFO0_EPDATA_S      0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_FIFO1 register.
//
//*****************************************************************************
#define USB_FIFO1_EPDATA_M      0xFFFFFFFF  // Endpoint Data.
#define USB_FIFO1_EPDATA_S      0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_FIFO2 register.
//
//*****************************************************************************
#define USB_FIFO2_EPDATA_M      0xFFFFFFFF  // Endpoint Data.
#define USB_FIFO2_EPDATA_S      0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_FIFO3 register.
//
//*****************************************************************************
#define USB_FIFO3_EPDATA_M      0xFFFFFFFF  // Endpoint Data.
#define USB_FIFO3_EPDATA_S      0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_DEVCTL register.
//
//*****************************************************************************
#define USB_DEVCTL_DEV          0x00000080  // Device Mode.
#define USB_DEVCTL_FSDEV        0x00000040  // Full-Speed Device Detected.
#define USB_DEVCTL_LSDEV        0x00000020  // Low-Speed Device Detected.
#define USB_DEVCTL_VBUS_M       0x00000018  // VBus Level.
#define USB_DEVCTL_VBUS_NONE    0x00000000  // Below SessionEnd
#define USB_DEVCTL_VBUS_SEND    0x00000008  // Above SessionEnd, below AValid
#define USB_DEVCTL_VBUS_AVALID  0x00000010  // Above AValid, below VBusValid
#define USB_DEVCTL_VBUS_VALID   0x00000018  // Above VBusValid
#define USB_DEVCTL_HOST         0x00000004  // Host Mode.
#define USB_DEVCTL_HOSTREQ      0x00000002  // Host Request.
#define USB_DEVCTL_SESSION      0x00000001  // Session Start/End.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXFIFOSZ register.
//
//*****************************************************************************
#define USB_TXFIFOSZ_DPB        0x00000010  // Double Packet Buffer Support.
#define USB_TXFIFOSZ_SIZE_M     0x0000000F  // Max Packet Size.
#define USB_TXFIFOSZ_SIZE_8     0x00000000  // 8
#define USB_TXFIFOSZ_SIZE_16    0x00000001  // 16
#define USB_TXFIFOSZ_SIZE_32    0x00000002  // 32
#define USB_TXFIFOSZ_SIZE_64    0x00000003  // 64
#define USB_TXFIFOSZ_SIZE_128   0x00000004  // 128
#define USB_TXFIFOSZ_SIZE_256   0x00000005  // 256
#define USB_TXFIFOSZ_SIZE_512   0x00000006  // 512
#define USB_TXFIFOSZ_SIZE_1024  0x00000007  // 1024
#define USB_TXFIFOSZ_SIZE_2048  0x00000008  // 2048

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXFIFOSZ register.
//
//*****************************************************************************
#define USB_RXFIFOSZ_DPB        0x00000010  // Double Packet Buffer Support.
#define USB_RXFIFOSZ_SIZE_M     0x0000000F  // Max Packet Size.
#define USB_RXFIFOSZ_SIZE_8     0x00000000  // 8
#define USB_RXFIFOSZ_SIZE_16    0x00000001  // 16
#define USB_RXFIFOSZ_SIZE_32    0x00000002  // 32
#define USB_RXFIFOSZ_SIZE_64    0x00000003  // 64
#define USB_RXFIFOSZ_SIZE_128   0x00000004  // 128
#define USB_RXFIFOSZ_SIZE_256   0x00000005  // 256
#define USB_RXFIFOSZ_SIZE_512   0x00000006  // 512
#define USB_RXFIFOSZ_SIZE_1024  0x00000007  // 1024
#define USB_RXFIFOSZ_SIZE_2048  0x00000008  // 2048

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXFIFOADD
// register.
//
//*****************************************************************************
#define USB_TXFIFOADD_ADDR_M    0x00001FFF  // Transmit/Receive Start Address.
#define USB_TXFIFOADD_ADDR_0    0x00000000  // 0
#define USB_TXFIFOADD_ADDR_8    0x00000001  // 8
#define USB_TXFIFOADD_ADDR_16   0x00000002  // 16
#define USB_TXFIFOADD_ADDR_32   0x00000003  // 32
#define USB_TXFIFOADD_ADDR_64   0x00000004  // 64
#define USB_TXFIFOADD_ADDR_128  0x00000005  // 128
#define USB_TXFIFOADD_ADDR_256  0x00000006  // 256
#define USB_TXFIFOADD_ADDR_512  0x00000007  // 512
#define USB_TXFIFOADD_ADDR_1024 0x00000008  // 1024
#define USB_TXFIFOADD_ADDR_2048 0x00000009  // 2048

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXFIFOADD
// register.
//
//*****************************************************************************
#define USB_RXFIFOADD_ADDR_M    0x00001FFF  // Transmit/Receive Start Address.
#define USB_RXFIFOADD_ADDR_0    0x00000000  // 0
#define USB_RXFIFOADD_ADDR_8    0x00000001  // 8
#define USB_RXFIFOADD_ADDR_16   0x00000002  // 16
#define USB_RXFIFOADD_ADDR_32   0x00000003  // 32
#define USB_RXFIFOADD_ADDR_64   0x00000004  // 64
#define USB_RXFIFOADD_ADDR_128  0x00000005  // 128
#define USB_RXFIFOADD_ADDR_256  0x00000006  // 256
#define USB_RXFIFOADD_ADDR_512  0x00000007  // 512
#define USB_RXFIFOADD_ADDR_1024 0x00000008  // 1024
#define USB_RXFIFOADD_ADDR_2048 0x00000009  // 2048

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_CONTIM register.
//
//*****************************************************************************
#define USB_CONTIM_WTCON_M      0x000000F0  // Connect Wait.
#define USB_CONTIM_WTID_M       0x0000000F  // Wait ID.
#define USB_CONTIM_WTCON_S      4
#define USB_CONTIM_WTID_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_FSEOF register.
//
//*****************************************************************************
#define USB_FSEOF_FSEOFG_M      0x000000FF  // Full-Speed End-of-Frame Gap.
#define USB_FSEOF_FSEOFG_S      0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_LSEOF register.
//
//*****************************************************************************
#define USB_LSEOF_LSEOFG_M      0x000000FF  // Low-Speed End-of-Frame Gap.
#define USB_LSEOF_LSEOFG_S      0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXFUNCADDR0
// register.
//
//*****************************************************************************
#define USB_TXFUNCADDR0_ADDR_M  0x0000007F  // Device Address.
#define USB_TXFUNCADDR0_ADDR_S  0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXHUBADDR0
// register.
//
//*****************************************************************************
#define USB_TXHUBADDR0_MULTTRAN 0x00000080  // Multiple Translators.
#define USB_TXHUBADDR0_ADDR_M   0x0000007F  // Hub Address.
#define USB_TXHUBADDR0_ADDR_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXHUBPORT0
// register.
//
//*****************************************************************************
#define USB_TXHUBPORT0_PORT_M   0x0000007F  // Hub Port.
#define USB_TXHUBPORT0_PORT_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXFUNCADDR1
// register.
//
//*****************************************************************************
#define USB_TXFUNCADDR1_ADDR_M  0x0000007F  // Device Address.
#define USB_TXFUNCADDR1_ADDR_S  0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXHUBADDR1
// register.
//
//*****************************************************************************
#define USB_TXHUBADDR1_MULTTRAN 0x00000080  // Multiple Translators.
#define USB_TXHUBADDR1_ADDR_M   0x0000007F  // Hub Address.
#define USB_TXHUBADDR1_ADDR_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXHUBPORT1
// register.
//
//*****************************************************************************
#define USB_TXHUBPORT1_PORT_M   0x0000007F  // Hub Port.
#define USB_TXHUBPORT1_PORT_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXFUNCADDR1
// register.
//
//*****************************************************************************
#define USB_RXFUNCADDR1_ADDR_M  0x0000007F  // Device Address.
#define USB_RXFUNCADDR1_ADDR_S  0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXHUBADDR1
// register.
//
//*****************************************************************************
#define USB_RXHUBADDR1_MULTTRAN 0x00000080  // Multiple Translators.
#define USB_RXHUBADDR1_ADDR_M   0x0000007F  // Hub Address.
#define USB_RXHUBADDR1_ADDR_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXHUBPORT1
// register.
//
//*****************************************************************************
#define USB_RXHUBPORT1_PORT_M   0x0000007F  // Hub Port.
#define USB_RXHUBPORT1_PORT_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXFUNCADDR2
// register.
//
//*****************************************************************************
#define USB_TXFUNCADDR2_ADDR_M  0x0000007F  // Device Address.
#define USB_TXFUNCADDR2_ADDR_S  0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXHUBADDR2
// register.
//
//*****************************************************************************
#define USB_TXHUBADDR2_MULTTRAN 0x00000080  // Multiple Translators.
#define USB_TXHUBADDR2_ADDR_M   0x0000007F  // Hub Address.
#define USB_TXHUBADDR2_ADDR_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXHUBPORT2
// register.
//
//*****************************************************************************
#define USB_TXHUBPORT2_PORT_M   0x0000007F  // Hub Port.
#define USB_TXHUBPORT2_PORT_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXFUNCADDR2
// register.
//
//*****************************************************************************
#define USB_RXFUNCADDR2_ADDR_M  0x0000007F  // Device Address.
#define USB_RXFUNCADDR2_ADDR_S  0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXHUBADDR2
// register.
//
//*****************************************************************************
#define USB_RXHUBADDR2_MULTTRAN 0x00000080  // Multiple Translators.
#define USB_RXHUBADDR2_ADDR_M   0x0000007F  // Hub Address.
#define USB_RXHUBADDR2_ADDR_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXHUBPORT2
// register.
//
//*****************************************************************************
#define USB_RXHUBPORT2_PORT_M   0x0000007F  // Hub Port.
#define USB_RXHUBPORT2_PORT_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXFUNCADDR3
// register.
//
//*****************************************************************************
#define USB_TXFUNCADDR3_ADDR_M  0x0000007F  // Device Address.
#define USB_TXFUNCADDR3_ADDR_S  0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXHUBADDR3
// register.
//
//*****************************************************************************
#define USB_TXHUBADDR3_MULTTRAN 0x00000080  // Multiple Translators.
#define USB_TXHUBADDR3_ADDR_M   0x0000007F  // Hub Address.
#define USB_TXHUBADDR3_ADDR_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXHUBPORT3
// register.
//
//*****************************************************************************
#define USB_TXHUBPORT3_PORT_M   0x0000007F  // Hub Port.
#define USB_TXHUBPORT3_PORT_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXFUNCADDR3
// register.
//
//*****************************************************************************
#define USB_RXFUNCADDR3_ADDR_M  0x0000007F  // Device Address.
#define USB_RXFUNCADDR3_ADDR_S  0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXHUBADDR3
// register.
//
//*****************************************************************************
#define USB_RXHUBADDR3_MULTTRAN 0x00000080  // Multiple Translators.
#define USB_RXHUBADDR3_ADDR_M   0x0000007F  // Hub Address.
#define USB_RXHUBADDR3_ADDR_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXHUBPORT3
// register.
//
//*****************************************************************************
#define USB_RXHUBPORT3_PORT_M   0x0000007F  // Hub Port.
#define USB_RXHUBPORT3_PORT_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_CSRL0 register.
//
//*****************************************************************************
#define USB_CSRL0_NAKTO         0x00000080  // NAK Timeout.
#define USB_CSRL0_SETENDC       0x00000080  // Setup End Clear.
#define USB_CSRL0_STATUS        0x00000040  // Status Packet.
#define USB_CSRL0_RXRDYC        0x00000040  // RXRDY Clear.
#define USB_CSRL0_REQPKT        0x00000020  // Request Packet.
#define USB_CSRL0_STALL         0x00000020  // Send Stall.
#define USB_CSRL0_SETEND        0x00000010  // Setup End.
#define USB_CSRL0_ERROR         0x00000010  // Error.
#define USB_CSRL0_DATAEND       0x00000008  // Data End.
#define USB_CSRL0_SETUP         0x00000008  // Setup Packet.
#define USB_CSRL0_STALLED       0x00000004  // Endpoint Stalled.
#define USB_CSRL0_TXRDY         0x00000002  // Transmit Packet Ready.
#define USB_CSRL0_RXRDY         0x00000001  // Receive Packet Ready.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_CSRH0 register.
//
//*****************************************************************************
#define USB_CSRH0_DTWE          0x00000004  // Data Toggle Write Enable.
#define USB_CSRH0_DT            0x00000002  // Data Toggle.
#define USB_CSRH0_FLUSH         0x00000001  // Flush FIFO.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_COUNT0 register.
//
//*****************************************************************************
#define USB_COUNT0_COUNT_M      0x0000007F  // Count.
#define USB_COUNT0_COUNT_S      0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TYPE0 register.
//
//*****************************************************************************
#define USB_TYPE0_SPEED_M       0x000000C0  // Operating Speed.
#define USB_TYPE0_SPEED_FULL    0x00000080  // Full
#define USB_TYPE0_SPEED_LOW     0x000000C0  // Low

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_NAKLMT register.
//
//*****************************************************************************
#define USB_NAKLMT_NAKLMT_M     0x0000001F  // EP0 NAK Limit.
#define USB_NAKLMT_NAKLMT_S     0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXMAXP1 register.
//
//*****************************************************************************
#define USB_TXMAXP1_MULT_M      0x0000F800  // Multiplier.
#define USB_TXMAXP1_MAXLOAD_M   0x000007FF  // Maximum Payload.
#define USB_TXMAXP1_MULT_S      11
#define USB_TXMAXP1_MAXLOAD_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXCSRL1 register.
//
//*****************************************************************************
#define USB_TXCSRL1_NAKTO       0x00000080  // NAK Timeout
#define USB_TXCSRL1_INCTX       0x00000080  // Incomplete Transmit.
#define USB_TXCSRL1_CLRDT       0x00000040  // Clear Data Toggle.
#define USB_TXCSRL1_STALLED     0x00000020  // Endpoint Stalled.
#define USB_TXCSRL1_STALL       0x00000010  // Send Stall.
#define USB_TXCSRL1_SETUP       0x00000010  // Setup Packet.
#define USB_TXCSRL1_FLUSH       0x00000008  // Flush FIFO.
#define USB_TXCSRL1_ERROR       0x00000004  // Error.
#define USB_TXCSRL1_UNDRN       0x00000004  // Underrun.
#define USB_TXCSRL1_FIFONE      0x00000002  // FIFO Not Empty.
#define USB_TXCSRL1_TXRDY       0x00000001  // Transmit Packet Ready.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXCSRH1 register.
//
//*****************************************************************************
#define USB_TXCSRH1_AUTOSET     0x00000080  // Auto Set.
#define USB_TXCSRH1_ISO         0x00000040  // ISO.
#define USB_TXCSRH1_MODE        0x00000020  // Mode.
#define USB_TXCSRH1_DMAEN       0x00000010  // DMA Request Enable.
#define USB_TXCSRH1_FDT         0x00000008  // Force Data Toggle.
#define USB_TXCSRH1_DMAMOD      0x00000004  // DMA Request Mode.
#define USB_TXCSRH1_DTWE        0x00000002  // Data Toggle Write Enable.
#define USB_TXCSRH1_DT          0x00000001  // Data Toggle.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXMAXP1 register.
//
//*****************************************************************************
#define USB_RXMAXP1_MULT_M      0x0000F800  // Multiplier.
#define USB_RXMAXP1_MAXLOAD_M   0x000007FF  // Maximum Payload.
#define USB_RXMAXP1_MULT_S      11
#define USB_RXMAXP1_MAXLOAD_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXCSRL1 register.
//
//*****************************************************************************
#define USB_RXCSRL1_CLRDT       0x00000080  // Clear Data Toggle.
#define USB_RXCSRL1_STALLED     0x00000040  // Endpoint Stalled.
#define USB_RXCSRL1_STALL       0x00000020  // Send Stall.
#define USB_RXCSRL1_REQPKT      0x00000020  // Request Packet.
#define USB_RXCSRL1_FLUSH       0x00000010  // Flush FIFO.
#define USB_RXCSRL1_DATAERR     0x00000008  // Data Error.
#define USB_RXCSRL1_NAKTO       0x00000008  // NAK Timeout.
#define USB_RXCSRL1_OVER        0x00000004  // Overrun.
#define USB_RXCSRL1_ERROR       0x00000004  // Error.
#define USB_RXCSRL1_FULL        0x00000002  // FIFO Full.
#define USB_RXCSRL1_RXRDY       0x00000001  // Receive Packet Ready.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXCSRH1 register.
//
//*****************************************************************************
#define USB_RXCSRH1_AUTOCL      0x00000080  // Auto Clear.
#define USB_RXCSRH1_AUTORQ      0x00000040  // Auto Request.
#define USB_RXCSRH1_ISO         0x00000040  // ISO.
#define USB_RXCSRH1_DMAEN       0x00000020  // DMA Request Enable.
#define USB_RXCSRH1_DISNYET     0x00000010  // Disable NYET
#define USB_RXCSRH1_PIDERR      0x00000010  // PID Error.
#define USB_RXCSRH1_DMAMOD      0x00000008  // DMA Request Mode.
#define USB_RXCSRH1_DTWE        0x00000004  // Data Toggle Write Enable.
#define USB_RXCSRH1_DT          0x00000002  // Data Toggle.
#define USB_RXCSRH1_INCRX       0x00000001  // Incomplete Receive.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXCOUNT1 register.
//
//*****************************************************************************
#define USB_RXCOUNT1_COUNT_M    0x00001FFF  // Receive Packet Count.
#define USB_RXCOUNT1_COUNT_S    0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXTYPE1 register.
//
//*****************************************************************************
#define USB_TXTYPE1_SPEED_M     0x000000C0  // Operating Speed.
#define USB_TXTYPE1_SPEED_DFLT  0x00000000  // Default
#define USB_TXTYPE1_SPEED_FULL  0x00000080  // Full
#define USB_TXTYPE1_SPEED_LOW   0x000000C0  // Low
#define USB_TXTYPE1_PROTO_M     0x00000030  // Protocol.
#define USB_TXTYPE1_PROTO_CTRL  0x00000000  // Control
#define USB_TXTYPE1_PROTO_ISOC  0x00000010  // Isochronous
#define USB_TXTYPE1_PROTO_BULK  0x00000020  // Bulk
#define USB_TXTYPE1_PROTO_INT   0x00000030  // Interrupt
#define USB_TXTYPE1_TEP_M       0x0000000F  // Target Endpoint Number.
#define USB_TXTYPE1_TEP_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXINTERVAL1
// register.
//
//*****************************************************************************
#define USB_TXINTERVAL1_NAKLMT_M \
                                0x000000FF  // NAK Limit.
#define USB_TXINTERVAL1_TXPOLL_M \
                                0x000000FF  // TX Polling
#define USB_TXINTERVAL1_TXPOLL_S \
                                0
#define USB_TXINTERVAL1_NAKLMT_S \
                                0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXTYPE1 register.
//
//*****************************************************************************
#define USB_RXTYPE1_SPEED_M     0x000000C0  // Operating Speed.
#define USB_RXTYPE1_SPEED_DFLT  0x00000000  // Default
#define USB_RXTYPE1_SPEED_FULL  0x00000080  // Full
#define USB_RXTYPE1_SPEED_LOW   0x000000C0  // Low
#define USB_RXTYPE1_PROTO_M     0x00000030  // Protocol.
#define USB_RXTYPE1_PROTO_CTRL  0x00000000  // Control
#define USB_RXTYPE1_PROTO_ISOC  0x00000010  // Isochronous
#define USB_RXTYPE1_PROTO_BULK  0x00000020  // Bulk
#define USB_RXTYPE1_PROTO_INT   0x00000030  // Interrupt
#define USB_RXTYPE1_TEP_M       0x0000000F  // Target Endpoint Number.
#define USB_RXTYPE1_TEP_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXINTERVAL1
// register.
//
//*****************************************************************************
#define USB_RXINTERVAL1_TXPOLL_M \
                                0x000000FF  // RX Polling
#define USB_RXINTERVAL1_NAKLMT_M \
                                0x000000FF  // NAK Limit.
#define USB_RXINTERVAL1_TXPOLL_S \
                                0
#define USB_RXINTERVAL1_NAKLMT_S \
                                0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXMAXP2 register.
//
//*****************************************************************************
#define USB_TXMAXP2_MULT_M      0x0000F800  // Multiplier.
#define USB_TXMAXP2_MAXLOAD_M   0x000007FF  // Maximum Payload.
#define USB_TXMAXP2_MULT_S      11
#define USB_TXMAXP2_MAXLOAD_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXCSRL2 register.
//
//*****************************************************************************
#define USB_TXCSRL2_INCTX       0x00000080  // Incomplete Transmit.
#define USB_TXCSRL2_NAKTO       0x00000080  // NAK Timeout
#define USB_TXCSRL2_CLRDT       0x00000040  // Clear Data Toggle.
#define USB_TXCSRL2_STALLED     0x00000020  // Endpoint Stalled.
#define USB_TXCSRL2_SETUP       0x00000010  // Setup Packet.
#define USB_TXCSRL2_STALL       0x00000010  // Send Stall.
#define USB_TXCSRL2_FLUSH       0x00000008  // Flush FIFO.
#define USB_TXCSRL2_ERROR       0x00000004  // Error.
#define USB_TXCSRL2_UNDRN       0x00000004  // Underrun.
#define USB_TXCSRL2_FIFONE      0x00000002  // FIFO Not Empty.
#define USB_TXCSRL2_TXRDY       0x00000001  // Transmit Packet Ready.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXCSRH2 register.
//
//*****************************************************************************
#define USB_TXCSRH2_AUTOSET     0x00000080  // Auto Set.
#define USB_TXCSRH2_ISO         0x00000040  // ISO.
#define USB_TXCSRH2_MODE        0x00000020  // Mode.
#define USB_TXCSRH2_DMAEN       0x00000010  // DMA Request Enable.
#define USB_TXCSRH2_FDT         0x00000008  // Force Data Toggle.
#define USB_TXCSRH2_DMAMOD      0x00000004  // DMA Request Mode.
#define USB_TXCSRH2_DTWE        0x00000002  // Data Toggle Write Enable.
#define USB_TXCSRH2_DT          0x00000001  // Data Toggle.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXMAXP2 register.
//
//*****************************************************************************
#define USB_RXMAXP2_MULT_M      0x0000F800  // Multiplier.
#define USB_RXMAXP2_MAXLOAD_M   0x000007FF  // Maximum Payload.
#define USB_RXMAXP2_MULT_S      11
#define USB_RXMAXP2_MAXLOAD_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXCSRL2 register.
//
//*****************************************************************************
#define USB_RXCSRL2_CLRDT       0x00000080  // Clear Data Toggle.
#define USB_RXCSRL2_STALLED     0x00000040  // Endpoint Stalled.
#define USB_RXCSRL2_REQPKT      0x00000020  // Request Packet.
#define USB_RXCSRL2_STALL       0x00000020  // Send Stall.
#define USB_RXCSRL2_FLUSH       0x00000010  // Flush FIFO.
#define USB_RXCSRL2_DATAERR     0x00000008  // Data Error.
#define USB_RXCSRL2_NAKTO       0x00000008  // NAK Timeout.
#define USB_RXCSRL2_ERROR       0x00000004  // Error.
#define USB_RXCSRL2_OVER        0x00000004  // Overrun.
#define USB_RXCSRL2_FULL        0x00000002  // FIFO Full.
#define USB_RXCSRL2_RXRDY       0x00000001  // Receive Packet Ready.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXCSRH2 register.
//
//*****************************************************************************
#define USB_RXCSRH2_AUTOCL      0x00000080  // Auto Clear.
#define USB_RXCSRH2_AUTORQ      0x00000040  // Auto Request.
#define USB_RXCSRH2_ISO         0x00000040  // ISO.
#define USB_RXCSRH2_DMAEN       0x00000020  // DMA Request Enable.
#define USB_RXCSRH2_DISNYET     0x00000010  // Disable NYET
#define USB_RXCSRH2_PIDERR      0x00000010  // PID Error.
#define USB_RXCSRH2_DMAMOD      0x00000008  // DMA Request Mode.
#define USB_RXCSRH2_DTWE        0x00000004  // Data Toggle Write Enable.
#define USB_RXCSRH2_DT          0x00000002  // Data Toggle.
#define USB_RXCSRH2_INCRX       0x00000001  // Incomplete Receive.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXCOUNT2 register.
//
//*****************************************************************************
#define USB_RXCOUNT2_COUNT_M    0x00001FFF  // Receive Packet Count.
#define USB_RXCOUNT2_COUNT_S    0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXTYPE2 register.
//
//*****************************************************************************
#define USB_TXTYPE2_SPEED_M     0x000000C0  // Operating Speed.
#define USB_TXTYPE2_SPEED_DFLT  0x00000000  // Default
#define USB_TXTYPE2_SPEED_FULL  0x00000080  // Full
#define USB_TXTYPE2_SPEED_LOW   0x000000C0  // Low
#define USB_TXTYPE2_PROTO_M     0x00000030  // Protocol.
#define USB_TXTYPE2_PROTO_CTRL  0x00000000  // Control
#define USB_TXTYPE2_PROTO_ISOC  0x00000010  // Isochronous
#define USB_TXTYPE2_PROTO_BULK  0x00000020  // Bulk
#define USB_TXTYPE2_PROTO_INT   0x00000030  // Interrupt
#define USB_TXTYPE2_TEP_M       0x0000000F  // Target Endpoint Number.
#define USB_TXTYPE2_TEP_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXINTERVAL2
// register.
//
//*****************************************************************************
#define USB_TXINTERVAL2_TXPOLL_M \
                                0x000000FF  // TX Polling
#define USB_TXINTERVAL2_NAKLMT_M \
                                0x000000FF  // NAK Limit.
#define USB_TXINTERVAL2_NAKLMT_S \
                                0
#define USB_TXINTERVAL2_TXPOLL_S \
                                0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXTYPE2 register.
//
//*****************************************************************************
#define USB_RXTYPE2_SPEED_M     0x000000C0  // Operating Speed.
#define USB_RXTYPE2_SPEED_DFLT  0x00000000  // Default
#define USB_RXTYPE2_SPEED_FULL  0x00000080  // Full
#define USB_RXTYPE2_SPEED_LOW   0x000000C0  // Low
#define USB_RXTYPE2_PROTO_M     0x00000030  // Protocol.
#define USB_RXTYPE2_PROTO_CTRL  0x00000000  // Control
#define USB_RXTYPE2_PROTO_ISOC  0x00000010  // Isochronous
#define USB_RXTYPE2_PROTO_BULK  0x00000020  // Bulk
#define USB_RXTYPE2_PROTO_INT   0x00000030  // Interrupt
#define USB_RXTYPE2_TEP_M       0x0000000F  // Target Endpoint Number.
#define USB_RXTYPE2_TEP_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXINTERVAL2
// register.
//
//*****************************************************************************
#define USB_RXINTERVAL2_TXPOLL_M \
                                0x000000FF  // RX Polling
#define USB_RXINTERVAL2_NAKLMT_M \
                                0x000000FF  // NAK Limit.
#define USB_RXINTERVAL2_TXPOLL_S \
                                0
#define USB_RXINTERVAL2_NAKLMT_S \
                                0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXMAXP3 register.
//
//*****************************************************************************
#define USB_TXMAXP3_MULT_M      0x0000F800  // Multiplier.
#define USB_TXMAXP3_MAXLOAD_M   0x000007FF  // Maximum Payload.
#define USB_TXMAXP3_MULT_S      11
#define USB_TXMAXP3_MAXLOAD_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXCSRL3 register.
//
//*****************************************************************************
#define USB_TXCSRL3_INCTX       0x00000080  // Incomplete Transmit.
#define USB_TXCSRL3_NAKTO       0x00000080  // NAK Timeout
#define USB_TXCSRL3_CLRDT       0x00000040  // Clear Data Toggle.
#define USB_TXCSRL3_STALLED     0x00000020  // Endpoint Stalled.
#define USB_TXCSRL3_SETUP       0x00000010  // Setup Packet.
#define USB_TXCSRL3_STALL       0x00000010  // Send Stall.
#define USB_TXCSRL3_FLUSH       0x00000008  // Flush FIFO.
#define USB_TXCSRL3_ERROR       0x00000004  // Error.
#define USB_TXCSRL3_UNDRN       0x00000004  // Underrun.
#define USB_TXCSRL3_FIFONE      0x00000002  // FIFO Not Empty.
#define USB_TXCSRL3_TXRDY       0x00000001  // Transmit Packet Ready.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXCSRH3 register.
//
//*****************************************************************************
#define USB_TXCSRH3_AUTOSET     0x00000080  // Auto Set.
#define USB_TXCSRH3_ISO         0x00000040  // ISO.
#define USB_TXCSRH3_MODE        0x00000020  // Mode.
#define USB_TXCSRH3_DMAEN       0x00000010  // DMA Request Enable.
#define USB_TXCSRH3_FDT         0x00000008  // Force Data Toggle.
#define USB_TXCSRH3_DMAMOD      0x00000004  // DMA Request Mode.
#define USB_TXCSRH3_DTWE        0x00000002  // Data Toggle Write Enable.
#define USB_TXCSRH3_DT          0x00000001  // Data Toggle.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXMAXP3 register.
//
//*****************************************************************************
#define USB_RXMAXP3_MULT_M      0x0000F800  // Multiplier.
#define USB_RXMAXP3_MAXLOAD_M   0x000007FF  // Maximum Payload.
#define USB_RXMAXP3_MULT_S      11
#define USB_RXMAXP3_MAXLOAD_S   0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXCSRL3 register.
//
//*****************************************************************************
#define USB_RXCSRL3_CLRDT       0x00000080  // Clear Data Toggle.
#define USB_RXCSRL3_STALLED     0x00000040  // Endpoint Stalled.
#define USB_RXCSRL3_STALL       0x00000020  // Send Stall.
#define USB_RXCSRL3_REQPKT      0x00000020  // Request Packet.
#define USB_RXCSRL3_FLUSH       0x00000010  // Flush FIFO.
#define USB_RXCSRL3_DATAERR     0x00000008  // Data Error.
#define USB_RXCSRL3_NAKTO       0x00000008  // NAK Timeout.
#define USB_RXCSRL3_ERROR       0x00000004  // Error.
#define USB_RXCSRL3_OVER        0x00000004  // Overrun.
#define USB_RXCSRL3_FULL        0x00000002  // FIFO Full.
#define USB_RXCSRL3_RXRDY       0x00000001  // Receive Packet Ready.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXCSRH3 register.
//
//*****************************************************************************
#define USB_RXCSRH3_AUTOCL      0x00000080  // Auto Clear.
#define USB_RXCSRH3_AUTORQ      0x00000040  // Auto Request.
#define USB_RXCSRH3_ISO         0x00000040  // ISO.
#define USB_RXCSRH3_DMAEN       0x00000020  // DMA Request Enable.
#define USB_RXCSRH3_DISNYET     0x00000010  // Disable NYET
#define USB_RXCSRH3_PIDERR      0x00000010  // PID Error.
#define USB_RXCSRH3_DMAMOD      0x00000008  // DMA Request Mode.
#define USB_RXCSRH3_DTWE        0x00000004  // Data Toggle Write Enable.
#define USB_RXCSRH3_DT          0x00000002  // Data Toggle.
#define USB_RXCSRH3_INCRX       0x00000001  // Incomplete Receive.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXCOUNT3 register.
//
//*****************************************************************************
#define USB_RXCOUNT3_COUNT_M    0x00001FFF  // Receive Packet Count.
#define USB_RXCOUNT3_COUNT_S    0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXTYPE3 register.
//
//*****************************************************************************
#define USB_TXTYPE3_SPEED_M     0x000000C0  // Operating Speed.
#define USB_TXTYPE3_SPEED_DFLT  0x00000000  // Default
#define USB_TXTYPE3_SPEED_FULL  0x00000080  // Full
#define USB_TXTYPE3_SPEED_LOW   0x000000C0  // Low
#define USB_TXTYPE3_PROTO_M     0x00000030  // Protocol.
#define USB_TXTYPE3_PROTO_CTRL  0x00000000  // Control
#define USB_TXTYPE3_PROTO_ISOC  0x00000010  // Isochronous
#define USB_TXTYPE3_PROTO_BULK  0x00000020  // Bulk
#define USB_TXTYPE3_PROTO_INT   0x00000030  // Interrupt
#define USB_TXTYPE3_TEP_M       0x0000000F  // Target Endpoint Number.
#define USB_TXTYPE3_TEP_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXINTERVAL3
// register.
//
//*****************************************************************************
#define USB_TXINTERVAL3_TXPOLL_M \
                                0x000000FF  // TX Polling
#define USB_TXINTERVAL3_NAKLMT_M \
                                0x000000FF  // NAK Limit.
#define USB_TXINTERVAL3_TXPOLL_S \
                                0
#define USB_TXINTERVAL3_NAKLMT_S \
                                0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXTYPE3 register.
//
//*****************************************************************************
#define USB_RXTYPE3_SPEED_M     0x000000C0  // Operating Speed.
#define USB_RXTYPE3_SPEED_DFLT  0x00000000  // Default
#define USB_RXTYPE3_SPEED_FULL  0x00000080  // Full
#define USB_RXTYPE3_SPEED_LOW   0x000000C0  // Low
#define USB_RXTYPE3_PROTO_M     0x00000030  // Protocol.
#define USB_RXTYPE3_PROTO_CTRL  0x00000000  // Control
#define USB_RXTYPE3_PROTO_ISOC  0x00000010  // Isochronous
#define USB_RXTYPE3_PROTO_BULK  0x00000020  // Bulk
#define USB_RXTYPE3_PROTO_INT   0x00000030  // Interrupt
#define USB_RXTYPE3_TEP_M       0x0000000F  // Target Endpoint Number.
#define USB_RXTYPE3_TEP_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXINTERVAL3
// register.
//
//*****************************************************************************
#define USB_RXINTERVAL3_TXPOLL_M \
                                0x000000FF  // RX Polling
#define USB_RXINTERVAL3_NAKLMT_M \
                                0x000000FF  // NAK Limit.
#define USB_RXINTERVAL3_TXPOLL_S \
                                0
#define USB_RXINTERVAL3_NAKLMT_S \
                                0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RQPKTCOUNT1
// register.
//
//*****************************************************************************
#define USB_RQPKTCOUNT1_M       0x0000FFFF  // Block Transfer Packet Count.
#define USB_RQPKTCOUNT1_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RQPKTCOUNT2
// register.
//
//*****************************************************************************
#define USB_RQPKTCOUNT2_M       0x0000FFFF  // Block Transfer Packet Count.
#define USB_RQPKTCOUNT2_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RQPKTCOUNT3
// register.
//
//*****************************************************************************
#define USB_RQPKTCOUNT3_M       0x0000FFFF  // Block Transfer Packet Count.
#define USB_RQPKTCOUNT3_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_RXDPKTBUFDIS
// register.
//
//*****************************************************************************
#define USB_RXDPKTBUFDIS_EP3    0x00000008  // EP3 RX Double-Packet Buffer
                                            // Disable.
#define USB_RXDPKTBUFDIS_EP2    0x00000004  // EP2 RX Double-Packet Buffer
                                            // Disable.
#define USB_RXDPKTBUFDIS_EP1    0x00000002  // EP1 RX Double-Packet Buffer
                                            // Disable.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_TXDPKTBUFDIS
// register.
//
//*****************************************************************************
#define USB_TXDPKTBUFDIS_EP3    0x00000008  // EP3 TX Double-Packet Buffer
                                            // Disable.
#define USB_TXDPKTBUFDIS_EP2    0x00000004  // EP2 TX Double-Packet Buffer
                                            // Disable.
#define USB_TXDPKTBUFDIS_EP1    0x00000002  // EP1 TX Double-Packet Buffer
                                            // Disable.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_EPC register.
//
//*****************************************************************************
#define USB_EPC_PFLTACT_M       0x00000300  // Power Fault Action.
#define USB_EPC_PFLTACT_UNCHG   0x00000000  // Unchanged
#define USB_EPC_PFLTACT_TRIS    0x00000100  // Tristate
#define USB_EPC_PFLTACT_LOW     0x00000200  // Low
#define USB_EPC_PFLTACT_HIGH    0x00000300  // High
#define USB_EPC_PFLTAEN         0x00000040  // Power Fault Action Enable.
#define USB_EPC_PFLTSEN_HIGH    0x00000020  // Power Fault Sense.
#define USB_EPC_PFLTEN          0x00000010  // Power Fault Input Enable.
#define USB_EPC_EPENDE          0x00000004  // EPEN Drive Enable.
#define USB_EPC_EPEN_M          0x00000003  // External Power Supply Enable
                                            // Configuration.
#define USB_EPC_EPEN_LOW        0x00000000  // Power Enable Active Low
#define USB_EPC_EPEN_HIGH       0x00000001  // Power Enable Active High
#define USB_EPC_EPEN_VBLOW      0x00000002  // Power Enable High if VBUS Low
#define USB_EPC_EPEN_VBHIGH     0x00000003  // Power Enable High if VBUS High

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_EPCRIS register.
//
//*****************************************************************************
#define USB_EPCRIS_PF           0x00000001  // USB Power Fault Interrupt
                                            // Status.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_EPCIM register.
//
//*****************************************************************************
#define USB_EPCIM_PF            0x00000001  // USB Power Fault Interrupt Mask.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_EPCISC register.
//
//*****************************************************************************
#define USB_EPCISC_PF           0x00000001  // USB Power Fault Interrupt Status
                                            // and Clear.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_DRRIS register.
//
//*****************************************************************************
#define USB_DRRIS_RESUME        0x00000001  // Resume Interrupt Status.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_DRIM register.
//
//*****************************************************************************
#define USB_DRIM_RESUME         0x00000001  // Resume Interrupt Mask.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_DRISC register.
//
//*****************************************************************************
#define USB_DRISC_RESUME        0x00000001  // Resume Interrupt Status and
                                            // Clear.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_GPCS register.
//
//*****************************************************************************
#define USB_GPCS_DEVMOD         0x00000001  // Device Mode.

//*****************************************************************************
//
// The following are defines for the bit fields in the USB_O_VPLEN register.
//
//*****************************************************************************
#define USB_VPLEN_VPLEN_M       0x000000FF  // VBus Pulse Length.
#define USB_VPLEN_VPLEN_S       0

#endif // __HW_USB_H__
