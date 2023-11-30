/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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
#define QSPI_SCBR(baudrate, masterClock) \
		((uint32_t) (masterClock / baudrate) << 8)

/** Calculates the value of the CSR DLYBS field given the desired delay (in ns) */
#define QSPI_DLYBS(delay, masterClock) \
		((uint32_t) (((masterClock / 1000000) * delay) / 1000) << 16)

/** Calculates the value of the CSR DLYBCT field given the desired delay (in ns) */
#define QSPI_DLYBCT(delay, masterClock) \
		((uint32_t) (((masterClock / 1000000) * delay) / 32000) << 24)

/*--------------------------------------------------------------------------- */

#ifdef __cplusplus
 extern "C" {
#endif

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
  
/** \brief qspi access modes 
 */
typedef enum{
	 CmdAccess = 0,
	 ReadAccess,
	 WriteAccess
}Access_t;

/** \brief qspi modes SPI or QSPI
 */
typedef enum{
	SpiMode = QSPI_MR_SMM_SPI,
	QspiMemMode = QSPI_MR_SMM_MEMORY
}QspiMode_t;


/** \brief qspi clock modes , regarding clock phase and clock polarity
 */
typedef enum{
	ClockMode_00 = 0,
	ClockMode_10,
	ClockMode_01,
	ClockMode_11
}QspiClockMode_t;


/** \brief qspi status codes
 */
typedef enum{
	QSPI_SUCCESS = 0,
	QSPI_BUSY,
	QSPI_BUSY_SENDING,
	QSPI_READ_ERROR,
	QSPI_WRITE_ERROR,
	QSPI_UNKNOWN_ERROR,
	QSPI_INIT_ERROR,
	QSPI_INPUT_ERROR,
	QSPI_TOTAL_ERROR
}QspidStatus_t;
	 

/** \brief qspi status regiter bits
 */
typedef enum {
	IsReceived    = QSPI_SR_RDRF,
	IsTxSent      = QSPI_SR_TDRE,
	IsTxEmpty     = QSPI_SR_TXEMPTY,
	IsOverrun     = QSPI_SR_OVRES,
	IsCsRise      = QSPI_SR_CSR,
	IsCsAsserted  = QSPI_SR_CSS,
	IsEofInst     = QSPI_SR_INSTRE,
	IsEnabled     = QSPI_SR_QSPIENS
}QspiStatus_t;

/** \brief qspi command structure
 */
typedef struct {
	uint8_t       Instruction; 
	uint8_t       Option;  
}QspiMemCmd_t;

/** \brief qspi buffer structure
 */
typedef struct {
	uint32_t      TxDataSize;     /* Tx buffer size */
	uint32_t      RxDataSize;     /* Rx buffer size */
	uint32_t      *pDataTx;       /* Tx buffer */
	uint32_t      *pDataRx;       /* Rx buffer */
}QspiBuffer_t;


/** \brief qspi frame structure for QSPI mode
 */
typedef struct {
   union _QspiInstFrame {
		uint32_t val;
		struct _QspiInstFrameBM {
			uint32_t bwidth:3,          /** Width of QSPI Addr , inst data */
					 reserved0:1,        /** Reserved*/
					 bInstEn:1,         /** Enable Inst */
					 bAddrEn:1,         /** Enable Address */
					 bOptEn:1,          /** Enable Option */
					 bDataEn:1,         /** Enable Data */
					 bOptLen:2,         /** Option Length*/
					 bAddrLen:1,        /** Addrs Length*/
					 reserved1:1,        /** Option Length*/
					 bXfrType:2,        /** Transfer type*/
					 bContinuesRead:1,  /** Continoues read mode*/
					 reserved2:1,        /** Reserved*/
					 bDummyCycles:5,    /**< Unicast hash match */
					 reserved3:11;       /** Reserved*/
		} bm;
	} InstFrame;
  uint32_t       Addr;
}QspiInstFrame_t;

/** \brief qspi driver structure
 */
typedef struct {
	uint8_t           qspiId;         /* QSPI ID */
	Qspi              *pQspiHw;       /* QSPI Hw instance */
	QspiMode_t        qspiMode;       /* Qspi mode: SPI or QSPI */
	QspiMemCmd_t      qspiCommand;    /* Qspi command structure*/
	QspiBuffer_t      qspiBuffer;     /* Qspi buffer*/
	QspiInstFrame_t   *pQspiFrame;    /* Qspi QSPI mode Fram register informations*/
}Qspid_t;


void QSPI_SwReset( Qspi *pQspi );

void QSPI_Disable( Qspi *pQspi );

void QSPI_Enable( Qspi *pQspi );

QspidStatus_t QSPI_EndTransfer( Qspi *pQspi );

uint32_t QSPI_GetStatus( Qspi *pQspi, const QspiStatus_t rStatus );

void QSPI_ConfigureClock( Qspi *pQspi, QspiClockMode_t ClockMode, 
		uint32_t dwClockCfg );
  
QspidStatus_t QSPI_SingleReadSPI( Qspid_t *pQspid, uint16_t* const pData );
	 
QspidStatus_t QSPI_MultiReadSPI( Qspid_t *pQspid, uint16_t* 
		const pData, uint32_t NumOfBytes );
	   
QspidStatus_t QSPI_SingleWriteSPI( Qspid_t *pQspid, uint16_t const *pData );

QspidStatus_t QSPI_MultiWriteSPI( Qspid_t *pQspid, uint16_t const *pData ,
		uint32_t NumOfBytes );

QspidStatus_t QSPI_EnableIt( Qspi *pQspi, uint32_t dwSources );

QspidStatus_t QSPI_DisableIt( Qspi *pQspi, uint32_t dwSources );
  
uint32_t QSPI_GetItMask( Qspi *pQspi );
	 
uint32_t QSPI_GetEnabledItStatus( Qspi *pQspi );
	 
QspidStatus_t QSPI_ConfigureInterface( Qspid_t *pQspid, QspiMode_t Mode, 
		uint32_t dwConfiguration );

QspidStatus_t QSPI_SendCommand( Qspid_t *pQspi, uint8_t const KeepCfg);
	 
QspidStatus_t QSPI_SendCommandWithData( Qspid_t *pQspi, uint8_t const KeepCfg);

QspidStatus_t QSPI_ReadCommand( Qspid_t *pQspi,  uint8_t const KeepCfg);

QspidStatus_t QSPI_EnableMemAccess( Qspid_t *pQspi, uint8_t const KeepCfg,
		uint8_t ScrambleFlag);

QspidStatus_t QSPI_ReadWriteMem( Qspid_t *pQspid, Access_t const ReadWrite);

#ifdef __cplusplus
}
#endif

#endif /* #ifndef _QSPI_ */

