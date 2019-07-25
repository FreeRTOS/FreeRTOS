/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2010, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 * \file
 *
 * Interface for Serial Peripheral Interface (SPI) controller.
 *
 */

#ifndef _QSPI_
#define _QSPI_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

/*----------------------------------------------------------------------------
 *        Macros
 *----------------------------------------------------------------------------*/

/**
 *
 * Here are several macros which should be used when configuring a SPI
 * peripheral.
 *
 * \section qspi_configuration_macros SPI Configuration Macros
 * - \ref QSPI_PCS
 * - \ref QSPI_SCBR
 * - \ref QSPI_DLYBS
 * - \ref QSPI_DLYBCT
 */


/** Calculates the value of the CSR SCBR field given the baudrate and MCK. */
#define QSPI_SCBR(baudrate, masterClock) ((uint32_t) (masterClock / baudrate) << 8)

/** Calculates the value of the CSR DLYBS field given the desired delay (in ns) */
#define QSPI_DLYBS(delay, masterClock) ((uint32_t) (((masterClock / 1000000) * delay) / 1000) << 16)

/** Calculates the value of the CSR DLYBCT field given the desired delay (in ns) */
#define QSPI_DLYBCT(delay, masterClock) ((uint32_t) (((masterClock / 1000000) * delay) / 32000) << 24)

/*------------------------------------------------------------------------------ */

#ifdef __cplusplus
 extern "C" {
#endif

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
   
typedef enum{
     Device_Read,
     Device_Write
}AccesType;
       

typedef struct {
  uint8_t       Instruction;
  uint8_t       InstAddrFlag;  
  uint8_t       Option;
  uint8_t       OptionEn;
  uint8_t       OptionLen;
  uint8_t       ContinuousRead;
  uint8_t       DummyCycles;
  uint8_t       spiMode;  
  uint32_t      DataSize;
  uint32_t      InstAddr;
  uint8_t       *pData;
}qspiFrame;

extern volatile uint8_t INSTRE_Flag;
extern void QSPI_Enable( Qspi* qspi ) ;
extern void QSPI_Disable( Qspi* qspi ) ;
extern void QSPI_EnableIt( Qspi* qspi, uint32_t dwSources ) ;
extern void QSPI_DisableIt( Qspi* qspi, uint32_t dwSources ) ;
extern uint32_t QSPI_GetItMask( Qspi* qspi );

extern void QSPI_Configure( Qspi* qspi, uint32_t dwConfiguration ) ;
void QSPI_ConfigureClock( Qspi* qspi,uint32_t dwConfiguration );
extern void QSPI_SwReset( Qspi* qspi );

extern void QSPI_ConfigureCs( Qspi* qspi, uint8_t spiCs );

extern int QSPI_RxEmpty(Qspi *qspi);
extern int QSPI_TxRdy(Qspi *qspi);

extern uint32_t QSPI_Read( Qspi* qspi ) ;
extern void QSPI_Write( Qspi* qspi, uint16_t wData ) ;
extern void QSPI_WriteLast( Qspi* qspi,  uint16_t wData );

extern uint32_t QSPI_GetStatus( Qspi* qspi ) ;
extern uint32_t QSPI_IsFinished( Qspi* pQspi ) ;

extern uint32_t QSPI_IsEOFInst( Qspi* qspi );
extern uint32_t QSPI_IsCsRise( Qspi* qspi );
extern uint32_t QSPI_IsCsAsserted( Qspi* qspi );

extern void QSPI_SendFrame( Qspi* qspi, qspiFrame *pFrame, AccesType  ReadWrite);

extern void QSPI_SendFrameToMem( Qspi* qspi, qspiFrame *pFrame, AccesType  ReadWrite );

#ifdef __cplusplus
}
#endif

#endif /* #ifndef _QSPI_ */

