/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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

/** \addtogroup qspi_module Working with QSPI
 * \ingroup peripherals_module
 * The QSPI driver provides the interface to configure and use the QSPI
 * peripheral.
 *
 * The Serial Peripheral Interface (QSPI) circuit is a synchronous serial
 * data link that provides communication with external devices in Master
 * or Slave Mode.
 *
 * To use the QSPI, the user has to follow these few steps:
 * -# Enable the QSPI pins required by the application (see pio.h).
 * -# Configure the QSPI using the \ref QSPI_Configure(). This enables the
 *    peripheral clock. The mode register is loaded with the given value.
 * -# Configure all the necessary chip selects with \ref QSPI_ConfigureNPCS().
 * -# Enable the QSPI by calling \ref QSPI_Enable().
 * -# Send/receive data using \ref QSPI_Write() and \ref QSPI_Read(). Note that
*  \ref QSPI_Read()
 *    must be called after \ref QSPI_Write() to retrieve the last value read.
 * -# Send/receive data using the PDC with the \ref QSPI_WriteBuffer() and
 *    \ref QSPI_ReadBuffer() functions.
 * -# Disable the QSPI by calling \ref QSPI_Disable().
 *
 * For more accurate information, please look at the QSPI section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref qspi.c\n
 * \ref qspi.h.\n
 */
/*@{*/
/*@}*/

/**
 * \file
 *
 * Implementation of Serial Peripheral Interface (QSPI) controller.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include "stdlib.h"
#include "string.h"   

#include <stdint.h>


#define SCRAMBLE_KEY    0x0BADDEAD
/*----------------------------------------------------------------------------
 *        Internal functions
 *----------------------------------------------------------------------------*/



/**
 * \brief Configure QSPI/SPI mode
 *
 * \param pQspi  Pointer to a Qspi instance.
 */
__STATIC_INLINE void QSPI_ConfigureMode( Qspi *pQspi, uint8_t dMode )
{
	assert(pQspi);
	pQspi->QSPI_MR =  dMode ;
}

/**
 * \brief Configure mode register of QSPI
 *
 * \param pQspi  Pointer to a Qspi instance.
 */
__STATIC_INLINE void QSPI_Configure( Qspi *pQspi, uint32_t dwConfiguration )
{
	assert(pQspi);
	pQspi->QSPI_MR |=  dwConfiguration ;
}


/**
 * \brief Configures a instruction address for QSPI in QSPI mode
 *
 * \param pQspi   Pointer to a Qspi instance.
 * \param dwAddr  Instruction Address
 */
__STATIC_INLINE void QSPI_SetInstAddr( Qspi *pQspi,uint32_t dwAddr )
{
	assert(pQspi);
	pQspi->QSPI_IAR = dwAddr ;
}


/**
 * \brief Configures instruction register with a given command for QSPI
 *
 * \param pQspi   Pointer to a Qspi instance.
 * \param dwInst  Instruction Code
 * \param dwOpt   Instruction Code option
 */
__STATIC_INLINE void QSPI_SetInst( Qspi *pQspi, uint8_t dwInst, uint8_t dwOpt )
{
	assert(pQspi);
	pQspi->QSPI_ICR = (dwInst | QSPI_ICR_OPT(dwOpt) );
}

/**
 * \brief Configures instruction frame register of QSPI
 *
 * \param pQspi         Pointer to a Qspi instance.
 * \param pInstFrame    Instruction Frame configuration
 */
__STATIC_INLINE void QSPI_SetInstFrame( Qspi *pQspi, QspiInstFrame_t *pInstFrame)
{
	assert(pQspi);
	pQspi->QSPI_IFR = pInstFrame->InstFrame.val;
}

/**
 * \brief Reads the Instruction frame of QSPI
 *
 * \param pQspi   Pointer to an Qspi instance.
 */
__STATIC_INLINE uint32_t QSPI_GetInstFrame( Qspi *pQspi )
{
	assert(pQspi);
	return pQspi->QSPI_IFR;
}

/**
 * \brief Read QSPI RDR register for SPI mode
 *
 * \param pQspi   Pointer to an Qspi instance.
 */
__STATIC_INLINE uint16_t QSPI_ReadSPI( Qspi *pQspi )
{
	assert(pQspi);
	while(!QSPI_GetStatus(pQspi, IsReceived));
	return  pQspi->QSPI_RDR;
}


/**
 * \brief Write to QSPI Tx register in SPI mode
 *
 * \param pQspi   Pointer to an Qspi instance.
 * \param wData   Data to transmit
 */
__STATIC_INLINE void QSPI_WriteSPI( Qspi *pQspi, uint16_t wData )
{
	assert(pQspi);
	/* Send data */
	while(!QSPI_GetStatus(pQspi, IsTxEmpty));
	pQspi->QSPI_TDR = wData ;
	while(!QSPI_GetStatus(pQspi, IsTxSent));
}

/**
 * \brief Configures QSPI scrambling with a given Key
 *
 * \param pQspi         Pointer to an Qspi instance.
 * \param wKey          Key for scramble/unscramble
 * \param EnableFlag    Enable/disable scramble
 * \param Random        Add random value with given key
 */
__STATIC_INLINE void QSPI_ScrambleData( Qspi *pQspi, uint32_t wKey, 
		uint8_t EnableFlag, uint8_t Random )
{
	assert(pQspi);
	assert(EnableFlag < 2);
	assert(Random < 2 );
	
	if(EnableFlag) {
	  pQspi->QSPI_SKR = wKey;
	}
	pQspi->QSPI_SMR = ( EnableFlag | (Random << 1));
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Enables a QSPI peripheral.
 *
 * \param pQspi  Pointer to a Qspi instance.
 */
void QSPI_Enable( Qspi *pQspi )
{
	assert(pQspi);
	pQspi->QSPI_CR = QSPI_CR_QSPIEN ;
	while(!(pQspi->QSPI_SR & QSPI_SR_QSPIENS));
}

/**
 * \brief Disables a QSPI peripheral.
 *
 * \param pQspi  Pointer to a Qspi instance.
 */
void QSPI_Disable( Qspi *pQspi )
{
	assert(pQspi);
	pQspi->QSPI_CR = QSPI_CR_QSPIDIS ;
	while(pQspi->QSPI_SR & QSPI_SR_QSPIENS);
}

/**
 * \brief Resets a QSPI peripheral.
 *
 * \param pQspi  Pointer to a Qspi instance.
 */
void QSPI_SwReset( Qspi *pQspi )
{
	assert(pQspi);
	pQspi->QSPI_CR = QSPI_CR_SWRST ;
}

/**
 * \brief Enables one or more interrupt sources of a QSPI peripheral.
 *
 * \param pQspi  Pointer to a Qspi instance.
 * \param sources Bitwise OR of selected interrupt sources.
 */
QspidStatus_t QSPI_EnableIt( Qspi *pQspi, uint32_t dwSources )
{
	assert(pQspi);
	pQspi->QSPI_IER = dwSources ;
	return QSPI_SUCCESS;
}

/**
 * \brief Disables one or more interrupt sources of a QSPI peripheral.
 *
 * \param pQspi  Pointer to a Qspi instance.
 * \param sources Bitwise OR of selected interrupt sources.
 */
QspidStatus_t QSPI_DisableIt( Qspi *pQspi, uint32_t dwSources )
{
	assert(pQspi);
	pQspi->QSPI_IDR = dwSources ;
	return QSPI_SUCCESS;
}

/**
 * \brief Return the interrupt mask register.
 *
 * \return Qspi interrupt mask register.
 */
uint32_t QSPI_GetItMask( Qspi *pQspi )
{
	assert(pQspi);
	return (pQspi->QSPI_IMR) ;
}

/**
 * \brief Returns enabled interrupt status
 *
 * \return Qspi interrupt mask register.
 */
uint32_t QSPI_GetEnabledItStatus( Qspi *pQspi )
{
	assert(pQspi);
	return (pQspi->QSPI_IMR & QSPI_GetStatus(pQspi, 0xFFFFFFFF) ) ;
}

/**
 * \brief Get the current status register of the given QSPI peripheral.
 * \note This resets the internal value of the status register, so further
 * read may yield different values.
 * \param pQspi   Pointer to a Qspi instance.
 * \param rStatus Compare status with given status bit
 * \return  QSPI status register.
 */
uint32_t QSPI_GetStatus( Qspi *pQspi, const QspiStatus_t rStatus )
{
	assert(pQspi);
	return (pQspi->QSPI_SR & rStatus) ;
}

/**
 * \brief Configures peripheral clock of a QSPI/SPI peripheral. 
 *
 * \param pQspi   Pointer to an Qspi instance.
 * \param dwConfiguration  Desired clock configuration.
 */
void QSPI_ConfigureClock( Qspi *pQspi, QspiClockMode_t ClockMode, uint32_t dwClockCfg )
{
	assert(pQspi);
	pQspi->QSPI_SCR = ClockMode ;
	pQspi->QSPI_SCR |= dwClockCfg ;
}

/**
 * \brief Configures QSPI/SPI 
 *
 * \param pQspi             Pointer to an Qspi instance.
 * \param Mode              Mode for QSPI or SPI 
 * \param dwConfiguration   Config of SPI or QSPI mode
 */
QspidStatus_t QSPI_ConfigureInterface( Qspid_t *pQspid, QspiMode_t Mode, 
		uint32_t dwConfiguration)
{    
	pQspid->pQspiHw = QSPI;
	pQspid->qspiId = ID_QSPI;    
	
	QSPI_Disable(pQspid->pQspiHw);
	QSPI_SwReset(pQspid->pQspiHw);
	
	QSPI_ConfigureMode(pQspid->pQspiHw, Mode);
	QSPI_Configure(pQspid->pQspiHw, dwConfiguration);  
	
	return QSPI_SUCCESS;
}


/**
 * \brief Ends ongoing transfer by releasing CS of QSPI peripheral.
 *
 * \param pQspi  Pointer to an Qspi instance.
 */
QspidStatus_t QSPI_EndTransfer( Qspi *pQspi )
{
	assert(pQspi);
	while(!QSPI_GetStatus(pQspi, IsTxEmpty));
	pQspi->QSPI_CR = QSPI_CR_LASTXFER ;
	
	return QSPI_SUCCESS;
}


/*----------------------------------------------------------------------------
 *        SPI functions
 *----------------------------------------------------------------------------*/
/**
 * \brief Reads the data received by a SPI peripheral. This
 * method must be called after a successful SPI_Write call.
 *
 * \param pQspid    Pointer to a Qspi instance.
 * \param pData     Buffer to put read value
 * \return Qspi status
 */
QspidStatus_t QSPI_SingleReadSPI( Qspid_t *pQspid, uint16_t* const pData )
{
	QspidStatus_t Status = QSPI_UNKNOWN_ERROR;
	Qspi *pQspi = pQspid->pQspiHw;
	uint32_t NumOfAttempt = 0;
	uint16_t Dummy= 0xFF;
	
	for(; ;) {
		if( QSPI_GetStatus(pQspi, IsReceived)) {
			*pData = QSPI_ReadSPI(pQspi) ;
			QSPI_WriteSPI(pQspi, Dummy);
			*pData = QSPI_ReadSPI(pQspi) ;
			NumOfAttempt = 0;
			Status = QSPI_SUCCESS;
		} else {
			if(NumOfAttempt > 0xFFFF) {
				Status = QSPI_READ_ERROR;
				TRACE_ERROR(" SPI Read Error \n\r");
				break;
			} else { 
				Status = QSPI_READ_ERROR;
				NumOfAttempt++;
			}
		}
	}
	return Status;
}

/**
 * \brief Reads multiple data received by a SPI peripheral. This
 * method must be called after a successful SPI_Write call.
 *
 * \param pQspid        Pointer to a Qspi instance.
 * \param pData         Pointer to read buffer
 * \param NumOfBytes    Num of bytes to read
 * 
 * \return Qspi status
 */
QspidStatus_t QSPI_MultiReadSPI( Qspid_t *pQspid, uint16_t* const pData, 
							uint32_t NumOfBytes )
{
	QspidStatus_t Status = QSPI_UNKNOWN_ERROR;
	Qspi *pQspi = pQspid->pQspiHw;
	uint32_t NumOfBytesRead = 0;
	uint32_t NumOfAttempt = 0;
	uint8_t *pwData = (uint8_t *)pData;
	uint16_t Dummy=0xFF;
	
	/* Dummy read  and write to discard  first bytes recvd and start 
		receiving new data*/
	Dummy = QSPI_ReadSPI(pQspi) ;
	QSPI_WriteSPI(pQspi, Dummy);
	for(; NumOfBytesRead < NumOfBytes;) {
		if( QSPI_GetStatus(pQspi, IsTxSent)) {
			*pwData= QSPI_ReadSPI(pQspi) ;
			if(pQspi->QSPI_MR & QSPI_MR_NBBITS_Msk) {
				pwData += sizeof(uint16_t);
			} else {
				pwData += sizeof(uint8_t);
			}
			NumOfBytesRead++;
			NumOfAttempt = 0;
			Status = QSPI_SUCCESS;
			QSPI_WriteSPI(pQspi, Dummy);
		} else {
			if(NumOfAttempt > 0xFFFF) {
				Status = QSPI_READ_ERROR;
				TRACE_ERROR(" SPI MultiRead Error \n\r");
				break;
			} else { 
				Status = QSPI_READ_ERROR;
				NumOfAttempt++;
			}
		}
	}
	return Status;
}

/**
 * \brief Sends a single data through a SPI peripheral.
 *
 * \param pQspid    Pointer to a Qspi instance.
 * \param pData     Pointer to Tx data
 * 
 * \return Qspi status
 */
QspidStatus_t QSPI_SingleWriteSPI( Qspid_t *pQspid, uint16_t const *pData )
{
	QspidStatus_t Status = QSPI_UNKNOWN_ERROR;
	Qspi *pQspi = pQspid->pQspiHw;
	uint32_t NumOfAttempt = 0;
	
	for(;;) {
		if( QSPI_GetStatus(pQspi, IsTxSent)) {
			QSPI_WriteSPI(pQspi, *pData);
			NumOfAttempt = 0;
			Status = QSPI_SUCCESS;
			break;
		} else {
			Status = QSPI_BUSY_SENDING;
			NumOfAttempt++;
			if(NumOfAttempt > 0xFFFF) {
				Status = QSPI_WRITE_ERROR;
				TRACE_ERROR(" SPI Write Error \n\r");
				break;
			}
		}
	}
	return Status;
	
}

/**
 * \brief Sends multiple data through a SPI peripheral. 
 *
 * \param pQspid        Pointer to a Qspi instance.
 * \param pData         Pointer to a Tx buffer 
 * \param NumOfBytes    Num of data to send.
 */
QspidStatus_t QSPI_MultiWriteSPI( Qspid_t *pQspid, uint16_t const *pData, 
								uint32_t NumOfBytes )
{
	QspidStatus_t Status = QSPI_UNKNOWN_ERROR;
	Qspi *pQspi = pQspid->pQspiHw;
	uint32_t NumOfBytesWrite = 0;
	uint32_t NumOfAttempt = 0;
	uint8_t *pwData = (uint8_t *)pData;
	uint8_t Addr_Inc = 0;
	
	if(pQspi->QSPI_MR & QSPI_MR_NBBITS_Msk) {
		Addr_Inc = sizeof(uint16_t);
	} else {
		Addr_Inc = sizeof(uint8_t);
	}
	
	for(; NumOfBytesWrite < NumOfBytes; NumOfBytesWrite++) {
		if( QSPI_GetStatus(pQspi, IsTxEmpty)) {
			QSPI_WriteSPI(pQspi, (uint16_t )*pwData);
			pwData += Addr_Inc;
			NumOfAttempt = 0;
			Status = QSPI_SUCCESS;
		} else {
			Status = QSPI_BUSY_SENDING;
			NumOfAttempt++;
			if(NumOfAttempt > 0xFFFF) {
				Status = QSPI_WRITE_ERROR;
				TRACE_ERROR(" SPI Multi Write Error \n\r");
				break;
			}
		}
	}
	return Status;
	
}

/*----------------------------------------------------------------------------
 *        QSPI functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Send an instruction over QSPI (oly a flash command no data)
 *
 * \param pQspi     Pointer to an Qspi instance.
 * \param KeepCfg   To keep Instruction fram value or restes to zero
 *
 * \return Returns 1 if At least one instruction end has been detected since 
 * the last read of QSPI_SR.; otherwise
 * returns 0.
 */
QspidStatus_t QSPI_SendCommand( Qspid_t *pQspid, uint8_t const KeepCfg)
{  
	QspiInstFrame_t*  const pFrame = pQspid->pQspiFrame;
	QspiMemCmd_t  pCommand = pQspid->qspiCommand;
	QspidStatus_t Status = QSPI_UNKNOWN_ERROR;
	
	if( pFrame->InstFrame.bm.bAddrEn)
	{
	  QSPI_SetInstAddr(pQspid->pQspiHw, pFrame->Addr);
	}
	QSPI_SetInst(pQspid->pQspiHw, (pCommand.Instruction & 0xFF), 
			( (pCommand.Option >> QSPI_ICR_OPT_Pos) & 0xFF));
	QSPI_SetInstFrame(pQspid->pQspiHw, pFrame );
	
	memory_sync(); 
	while(!(pQspid->pQspiHw->QSPI_SR & QSPI_SR_INSTRE));            
	// poll CR reg to know status if instruction has end
	if(!KeepCfg) {
	  pFrame->InstFrame.val = 0;
	}
	return Status;
}



/**
 * \brief Send instruction over QSPI with data
 *
 * \param pQspi     Pointer to an Qspi instance.
 * \param KeepCfg   To keep Instruction fram value or restes to zero
 *
 * \return Returns 1 if At least one instruction end has been detected 
 *  since the last read of QSPI_SR.; otherwise returns 0.
 */
QspidStatus_t QSPI_SendCommandWithData( Qspid_t *pQspid, uint8_t const KeepCfg)
{  
	QspiInstFrame_t* const  pFrame = pQspid->pQspiFrame;
	QspiMemCmd_t  pCommand = pQspid->qspiCommand;
	QspiBuffer_t    pBuffer     =  pQspid->qspiBuffer;
	uint32_t *pQspiBuffer = (uint32_t *)QSPIMEM_ADDR;
	QspidStatus_t Status = QSPI_UNKNOWN_ERROR;
   
	//assert(pBuffer.pDataRx);
	assert(pBuffer.pDataTx);
		
	QSPI_SetInst(pQspid->pQspiHw, (pCommand.Instruction & 0xFF), (pCommand.Option & 0xFF) );
	QSPI_SetInstFrame(pQspid->pQspiHw, pFrame );
	
	QSPI_GetInstFrame(pQspid->pQspiHw); 
	// to synchronize system bus accesses
	if(!KeepCfg) {
	  pFrame->InstFrame.val = 0;
	}
	
	memcpy(pQspiBuffer  ,pBuffer.pDataTx ,  pBuffer.TxDataSize ); 
	memory_sync();
	QSPI_EndTransfer(pQspid->pQspiHw ) ; 
	// End transmission after all data has been sent
	while(!(pQspid->pQspiHw->QSPI_SR & QSPI_SR_INSTRE)); 
	// poll CR reg to know status if instruction has end
	
	return Status;
}

/**
 * \brief Send instruction over QSPI to read data
 *
 * \param pQspi     Pointer to an Qspi instance.
 * \param KeepCfg   To keep Instruction from value or resets to zero
 *
 * \return Returns 1 if At least one instruction end has been detected 
 * since the last read of QSPI_SR.; otherwise returns 0.
 */
QspidStatus_t QSPI_ReadCommand( Qspid_t *pQspid, uint8_t const KeepCfg)
{  
	QspiInstFrame_t* const  pFrame = pQspid->pQspiFrame;
	QspiMemCmd_t  pCommand = pQspid->qspiCommand;
	QspiBuffer_t    pBuffer     =  pQspid->qspiBuffer;
	uint32_t *pQspiBuffer = (uint32_t *)QSPIMEM_ADDR;
	QspidStatus_t Status = QSPI_UNKNOWN_ERROR;
	
	assert(pBuffer.pDataRx);
	  
	QSPI_SetInst(pQspid->pQspiHw, (pCommand.Instruction & 0xFF), 
			(pCommand.Option & 0xFF) );
	QSPI_SetInstFrame(pQspid->pQspiHw, pFrame );
	
	QSPI_GetInstFrame(pQspid->pQspiHw);
		// to synchronize system bus accesses   
	if(!KeepCfg) {
	  pFrame->InstFrame.val = 0;
	}
	memcpy(pBuffer.pDataRx , pQspiBuffer,  pBuffer.RxDataSize ); 
	memory_sync();
	QSPI_EndTransfer(pQspid->pQspiHw ) ;                   
	// End transmission after all data has been sent
	while(!(pQspid->pQspiHw->QSPI_SR & QSPI_SR_INSTRE));             
	// poll CR reg to know status if instruction has end
	
	return Status;
}

/**
 * \brief Sends an instruction over QSPI and configures other related address
*  like Addr , Frame and synchronise bus access before data read or write
 *
 * \param pQspi         Pointer to an Qspi instance.
 * \param KeepCfg       To keep Instruction from value or resets to zero
 * \param ScrambleFlag  Enable or disable scramble on QSPI
 *
 * \return Returns 1 if At least one instruction end has been detected since 
 * the last read of QSPI_SR.; otherwise returns 0.
 */
QspidStatus_t QSPI_EnableMemAccess( Qspid_t *pQspid, uint8_t const KeepCfg, 
									uint8_t ScrambleFlag)
{  
	QspiInstFrame_t* const pFrame = pQspid->pQspiFrame;
	QspiMemCmd_t  pCommand = pQspid->qspiCommand;
		
	QspidStatus_t Status = QSPI_UNKNOWN_ERROR;
	 
	QSPI_SetInst(pQspid->pQspiHw, (pCommand.Instruction & 0xFF), 
			(pCommand.Option & 0xFF) );
	
	if(ScrambleFlag) {
	  QSPI_ScrambleData(pQspid->pQspiHw, SCRAMBLE_KEY, ScrambleFlag, 1);
	}
	
	QSPI_SetInstFrame(pQspid->pQspiHw, pFrame );
	
	QSPI_GetInstFrame(pQspid->pQspiHw);
	// to synchronize system bus accesses   
	if(!KeepCfg) {
	  pFrame->InstFrame.val = 0;
	} 
	Status = QSPI_SUCCESS;
	return Status;
}

/**
 * \brief Writes or reads the QSPI memory (0x80000000) to transmit or 
 * receive data from Flash memory
 * \param pQspi         Pointer to an Qspi instance.
 * \param ReadWrite     Flag to indicate read/write QSPI memory access
 *
 * \return Returns 1 if At least one instruction end has been detected since 
 * the last read of QSPI_SR.; otherwise returns 0.
 */
QspidStatus_t QSPI_ReadWriteMem( Qspid_t *pQspid, Access_t const ReadWrite)
{  
	QspidStatus_t Status = QSPI_UNKNOWN_ERROR;
	QspiInstFrame_t* const pFrame = pQspid->pQspiFrame;
	uint32_t *pQspiMem = (uint32_t *)( QSPIMEM_ADDR | pFrame->Addr);
	QspiBuffer_t    pBuffer     =  pQspid->qspiBuffer;
	
	assert( ( (ReadWrite > CmdAccess) && (ReadWrite <= WriteAccess) ) ? true: false );
	if (ReadWrite == WriteAccess) {
	  memcpy(pQspiMem, pBuffer.pDataTx , pBuffer.TxDataSize ); 
	} else {
	  memcpy(pBuffer.pDataRx, pQspiMem, pBuffer.RxDataSize ); 
	}
	memory_sync();
	QSPI_EndTransfer(pQspid->pQspiHw ) ;
	// End transmission after all data has been sent
	while(!(pQspid->pQspiHw->QSPI_SR & QSPI_SR_INSTRE));
	// poll CR reg to know status if instruction has end
	
	Status = QSPI_SUCCESS;
	return Status;
}
