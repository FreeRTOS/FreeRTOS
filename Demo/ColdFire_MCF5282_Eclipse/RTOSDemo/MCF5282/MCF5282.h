/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.9
 */

#ifndef __MCF5282_H__
#define __MCF5282_H__


/********************************************************************/
/*
 * The basic data types
 */

typedef unsigned char           uint8;   /*  8 bits */
typedef unsigned short int      uint16;  /* 16 bits */
typedef unsigned long int       uint32;  /* 32 bits */

typedef signed char             int8;    /*  8 bits */
typedef signed short int        int16;   /* 16 bits */
typedef signed long int         int32;   /* 32 bits */

typedef volatile uint8          vuint8;  /*  8 bits */
typedef volatile uint16         vuint16; /* 16 bits */
typedef volatile uint32         vuint32; /* 32 bits */

#ifdef __cplusplus
extern "C" {
#endif

#if 0
#pragma define_section system ".system" far_absolute RW

/***
 * MCF5282 Derivative Memory map definitions from linker command files:
 * __IPSBAR, __FLASHBAR, __FLASHBAR_SIZE, __RAMBAR, __RAMBAR_SIZE
 * linker symbols must be defined in the linker command file.
 */

extern __declspec(system)  uint8 __IPSBAR[];
extern __declspec(system)  uint8 __FLASHBAR[];
extern __declspec(system)  uint8 __FLASHBAR_SIZE[];
extern __declspec(system)  uint8 __RAMBAR[];
extern __declspec(system)  uint8 __RAMBAR_SIZE[];
#endif

#define __IPSBAR ((uint8*)0x40000000)

#define IPSBAR_ADDRESS   (uint32)__IPSBAR
#define FLASHBAR_ADDRESS (uint32)__FLASHBAR
#define FLASHBAR_SIZE    (uint32)__FLASHBAR_SIZE
#define RAMBAR_ADDRESS   (uint32)__RAMBAR
#define RAMBAR_SIZE      (uint32)__RAMBAR_SIZE


#include "MCF5282_SCM.h"
#include "MCF5282_SDRAMC.h"
#include "MCF5282_CS.h"
#include "MCF5282_DMA.h"
#include "MCF5282_UART.h"
#include "MCF5282_I2C.h"
#include "MCF5282_QSPI.h"
#include "MCF5282_DTIM.h"
#include "MCF5282_INTC.h"
#include "MCF5282_GIACR.h"
#include "MCF5282_FEC.h"
#include "MCF5282_GPIO.h"
#include "MCF5282_PAD.h"
#include "MCF5282_RCM.h"
#include "MCF5282_PMM.h"
#include "MCF5282_CCM.h"
#include "MCF5282_CLOCK.h"
#include "MCF5282_EPORT.h"
#include "MCF5282_WTM.h"
#include "MCF5282_PIT.h"
#include "MCF5282_QADC.h"
#include "MCF5282_GPTA.h"
#include "MCF5282_GPTB.h"
#include "MCF5282_FlexCAN.h"
#include "MCF5282_CFM.h"

#ifdef __cplusplus
}
#endif


#endif /* __MCF5282_H__ */
