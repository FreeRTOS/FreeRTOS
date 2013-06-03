/*
 * @brief  USB registers and control functions
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * All rights reserved.
 *
 * @par
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licensor disclaim any and
 * all warranties, express or implied, including all implied warranties of
 * merchantability, fitness for a particular purpose and non-infringement of
 * intellectual property rights.  NXP Semiconductors assumes no responsibility
 * or liability for the use of the software, conveys no license or rights under any
 * patent, copyright, mask work right, or any other intellectual property rights in
 * or to any products. NXP Semiconductors reserves the right to make changes
 * in the software without notification. NXP Semiconductors also makes no
 * representation or warranty that such application will be suitable for the
 * specified use without further testing or modification.
 *
 * @par
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
 */

#ifndef __USB_001_H_
#define __USB_001_H_

#include "sys_config.h"
#include "cmsis.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup IP_USB_001 IP: USB Device, Host, & OTG register block and driver
 * @ingroup IP_Drivers
 * USB Device, Host, & OTG
 * Note: 
 * @{
 */

/**
 * @brief USB register block structure
 */
typedef struct
{
  __I  uint32_t Revision;             /* USB Host Registers                 */
  __IO uint32_t Control;
  __IO uint32_t CommandStatus;
  __IO uint32_t InterruptStatus;
  __IO uint32_t InterruptEnable;
  __IO uint32_t InterruptDisable;
  __IO uint32_t HCCA;
  __I  uint32_t PeriodCurrentED;
  __IO uint32_t ControlHeadED;
  __IO uint32_t ControlCurrentED;
  __IO uint32_t BulkHeadED;
  __IO uint32_t BulkCurrentED;
  __I  uint32_t DoneHead;
  __IO uint32_t FmInterval;
  __I  uint32_t FmRemaining;
  __I  uint32_t FmNumber;
  __IO uint32_t PeriodicStart;
  __IO uint32_t LSTreshold;
  __IO uint32_t RhDescriptorA;
  __IO uint32_t RhDescriptorB;
  __IO uint32_t RhStatus;
  __IO uint32_t RhPortStatus1;
  __IO uint32_t RhPortStatus2;
       uint32_t RESERVED0[40];
  __I  uint32_t Module_ID;

  __I  uint32_t IntSt;               /* USB On-The-Go Registers            */
  __IO uint32_t IntEn;
  __O  uint32_t IntSet;
  __O  uint32_t IntClr;
  __IO uint32_t StCtrl;
  __IO uint32_t Tmr;
       uint32_t RESERVED1[58];

  __I  uint32_t DevIntSt;            /* USB Device Interrupt Registers     */
  __IO uint32_t DevIntEn;
  __O  uint32_t DevIntClr;
  __O  uint32_t DevIntSet;

  __O  uint32_t CmdCode;             /* USB Device SIE Command Registers   */
  __I  uint32_t CmdData;

  __I  uint32_t RxData;              /* USB Device Transfer Registers      */
  __O  uint32_t TxData;
  __I  uint32_t RxPLen;
  __O  uint32_t TxPLen;
  __IO uint32_t Ctrl;
  __O  uint32_t DevIntPri;

  __I  uint32_t EpIntSt;             /* USB Device Endpoint Interrupt Regs */
  __IO uint32_t EpIntEn;
  __O  uint32_t EpIntClr;
  __O  uint32_t EpIntSet;
  __O  uint32_t EpIntPri;

  __IO uint32_t ReEp;                /* USB Device Endpoint Realization Reg*/
  __O  uint32_t EpInd;
  __IO uint32_t MaxPSize;

  __I  uint32_t DMARSt;              /* USB Device DMA Registers           */
  __O  uint32_t DMARClr;
  __O  uint32_t DMARSet;
       uint32_t RESERVED2[9];
  __IO uint32_t UDCAH;
  __I  uint32_t EpDMASt;
  __O  uint32_t EpDMAEn;
  __O  uint32_t EpDMADis;
  __I  uint32_t DMAIntSt;
  __IO uint32_t DMAIntEn;
       uint32_t RESERVED3[2];
  __I  uint32_t EoTIntSt;
  __O  uint32_t EoTIntClr;
  __O  uint32_t EoTIntSet;
  __I  uint32_t NDDRIntSt;
  __O  uint32_t NDDRIntClr;
  __O  uint32_t NDDRIntSet;
  __I  uint32_t SysErrIntSt;
  __O  uint32_t SysErrIntClr;
  __O  uint32_t SysErrIntSet;
       uint32_t RESERVED4[15];

  union {
  __I  uint32_t I2C_RX;                 /* USB OTG I2C Registers              */
  __O  uint32_t I2C_TX;
  };
  __IO  uint32_t I2C_STS;
  __IO uint32_t I2C_CTL;
  __IO uint32_t I2C_CLKHI;
  __O  uint32_t I2C_CLKLO;
       uint32_t RESERVED5[824];

  union {
  __IO uint32_t USBClkCtrl;             /* USB Clock Control Registers        */
  __IO uint32_t OTGClkCtrl;
  };
  union {
  __I  uint32_t USBClkSt;
  __I  uint32_t OTGClkSt;
  };
} IP_USB_001_T;
/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __USB_001_H_ */

