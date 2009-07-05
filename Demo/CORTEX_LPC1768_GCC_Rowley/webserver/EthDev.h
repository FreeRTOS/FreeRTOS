/*
 * @file:    EthDev.h
 * @purpose: Ethernet Device Definitions
 * @version: V1.10
 * @date:    24. Feb. 2009
 *----------------------------------------------------------------------------
 *
 * Copyright (C) 2009 ARM Limited. All rights reserved.
 *
 * ARM Limited (ARM) is supplying this software for use with Cortex-M3
 * processor based microcontrollers.  This file can be freely distributed
 * within development tools that are supporting such ARM based processors.
 *
 * THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
 * OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
 * ARM SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
 * CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
 *
 */

#ifndef _ETHDEV__H
#define _ETHDEV__H

#ifndef NULL
 #define NULL   0
#endif

/*----------------------------------------------------------------------------
  Ethernet Device Defines
 *----------------------------------------------------------------------------*/
#define EthDev_ADDR_SIZE        6                      /*!< Ethernet Address size in bytes */
#define EthDev_MTU_SIZE         1514                   /*!< Maximum Transmission Unit      */


/*----------------------------------------------------------------------------
  Ethernet Device Configuration and Control Command Defines
 *----------------------------------------------------------------------------*/
typedef enum {
  EthDev_LINK_DOWN              = 0,                   /*!< Ethernet link not established */
  EthDev_LINK_UP                = 1,                   /*!< Ethernet link established */
} EthDev_LINK;

typedef enum {
  EthDev_SPEED_10M              = 0,                   /*!< 10.0 Mbps link speed  */
  EthDev_SPEED_100M             = 1,                   /*!< 100.0 Mbps link speed */
  EthDev_SPEED_1000M            = 2,                   /*!< 1.0 Gbps link speed   */
} EthDev_SPEED;

typedef enum {
  EthDev_DUPLEX_HALF            = 0,                   /*!< Link half duplex */
  EthDev_DUPLEX_FULL            = 1,                   /*!< Link full duplex */
} EthDev_DUPLEX;

typedef enum {
  EthDev_MODE_AUTO              = 0,
  EthDev_MODE_10M_FULL          = 1,
  EthDev_MODE_10M_HALF          = 2,
  EthDev_MODE_100M_FULL         = 3,
  EthDev_MODE_100M_HALF         = 4,
  EthDev_MODE_1000M_FULL        = 5,
  EthDev_MODE_1000M_HALF        = 6,
} EthDev_MODE;

typedef struct {
  EthDev_LINK   Link   : 1;
  EthDev_DUPLEX Duplex : 1;
  EthDev_SPEED  Speed  : 2;
} EthDev_STATUS;


/*----------------------------------------------------------------------------
  Ethernet Device IO Block Structure
 *----------------------------------------------------------------------------*/
typedef struct {

   /* Initialized by the user application before call to Init. */
   EthDev_MODE   Mode;
   unsigned char HwAddr[EthDev_ADDR_SIZE];
   void         *(*RxFrame)      (int size);
   void          (*RxFrameReady) (int size);

   /* Initialized by Ethernet driver. */
   int           (*Init)       (void);
   int           (*UnInit)     (void);
   int           (*SetMCFilter)(int NumHwAddr, unsigned char *pHwAddr);
   int           (*TxFrame)    (void *pData, int size);
   void          (*Lock)       (void);
   void          (*UnLock)     (void);
   EthDev_STATUS (*LinkChk)    (void);
} EthDev_IOB;

// prototypes
portBASE_TYPE	Init_EMAC(void);
unsigned short 	ReadFrameBE_EMAC(void);
void           	CopyToFrame_EMAC(void *Source, unsigned int Size);
void           	CopyFromFrame_EMAC(void *Dest, unsigned short Size);
void           	DummyReadFrame_EMAC(unsigned short Size);
unsigned short 	StartReadFrame(void);
void           	EndReadFrame(void);
unsigned int   	CheckFrameReceived(void);
void           	RequestSend(void);
unsigned int   	Rdy4Tx(void);
void           	DoSend_EMAC(unsigned short FrameSize);
void 			vEMACWaitForInput( void );
unsigned long 	ulGetEMACRxData( void );
void vSendEMACTxData( unsigned short usTxDataLen );

#endif
