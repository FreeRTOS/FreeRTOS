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

/** \addtogroup spi_module Working with QSPI
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
 * -# Send/receive data using \ref QSPI_Write() and \ref QSPI_Read(). Note that \ref QSPI_Read()
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



volatile uint8_t INSTRE_Flag =0;
/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Enables a QSPI peripheral.
 *
 * \param qspi  Pointer to an Qspi instance.
 */
extern void QSPI_Enable( Qspi* qspi )
{
    qspi->QSPI_CR = QSPI_CR_QSPIEN ;
    while(!(qspi->QSPI_SR & QSPI_SR_QSPIENS));
}

/**
 * \brief Disables a SPI peripheral.
 *
 * \param qspi  Pointer to an Qspi instance.
 */
extern void QSPI_Disable( Qspi* qspi )
{
    qspi->QSPI_CR = QSPI_CR_QSPIDIS ;
}

/**
 * \brief Reset a QSPI peripheral.
 *
 * \param qspi  Pointer to an Qspi instance.
 */
extern void QSPI_SwReset( Qspi* qspi )
{
    qspi->QSPI_CR = QSPI_CR_SWRST ;
    qspi->QSPI_CR = QSPI_CR_SWRST ;
}

/**
 * \brief Enables one or more interrupt sources of a QSPI peripheral.
 *
 * \param qspi  Pointer to an Qspi instance.
 * \param sources Bitwise OR of selected interrupt sources.
 */
extern void QSPI_EnableIt( Qspi* qspi, uint32_t dwSources )
{
    qspi->QSPI_IER = dwSources ;
}

/**
 * \brief Disables one or more interrupt sources of a QSPI peripheral.
 *
 * \param qspi  Pointer to an Qspi instance.
 * \param sources Bitwise OR of selected interrupt sources.
 */
extern void QSPI_DisableIt( Qspi* qspi, uint32_t dwSources )
{
    qspi->QSPI_IDR = dwSources ;
}

/**
 * \brief Return the interrupt mask register.
 *
 * \return Qspi interrupt mask register.
 */
extern uint32_t QSPI_GetItMask( Qspi* qspi )
{
    return (qspi->QSPI_IMR) ;
}

/**
 * \brief Configures a QSPI peripheral as specified. The configuration can be computed
 * using several macros (see \ref spi_configuration_macros).
 *
 * \param qspi  Pointer to an Qspi instance.
 * \param id   Peripheral ID of the QSPI.
 * \param configuration  Value of the QSPI configuration register.
 */
extern void QSPI_Configure( Qspi* qspi, uint32_t dwConfiguration )
{
    qspi->QSPI_CR = QSPI_CR_QSPIDIS ;

    /* Execute a software reset of the QSPI twice */
    QSPI_SwReset(qspi);
    qspi->QSPI_MR = dwConfiguration ;
}


/**
 * \brief Configures a chip select of a QSPI peripheral. The chip select configuration
 * is computed using several macros (see \ref spi_configuration_macros).
 *
 * \param qspi   Pointer to an Qspi instance.
 * \param npcs  Chip select to configure (0, 1, 2 or 3).
 * \param configuration  Desired chip select configuration.
 */
void QSPI_ConfigureClock( Qspi* qspi,uint32_t dwConfiguration )
{
    qspi->QSPI_SCR = dwConfiguration ;
}

/**
 * \brief Get the current status register of the given QSPI peripheral.
 * \note This resets the internal value of the status register, so further
 * read may yield different values.
 * \param qspi   Pointer to a Qspi instance.
 * \return  QSPI status register.
 */
extern uint32_t QSPI_GetStatus( Qspi* qspi )
{
    return qspi->QSPI_SR ;
}

/**
 * \brief Reads and returns the last word of data received by a SPI peripheral. This
 * method must be called after a successful SPI_Write call.
 *
 * \param spi  Pointer to an Spi instance.
 *
 * \return readed data.
 */
extern uint32_t QSPI_Read( Qspi* qspi )
{
    while ( (qspi->QSPI_SR & SPI_SR_RDRF) == 0 ) ;

    return qspi->QSPI_RDR & 0xFFFF ;
}

/**
 * \brief Sends data through a SPI peripheral. If the SPI is configured to use a fixed
 * peripheral select, the npcs value is meaningless. Otherwise, it identifies
 * the component which shall be addressed.
 *
 * \param spi   Pointer to an Spi instance.
 * \param npcs  Chip select of the component to address (0, 1, 2 or 3).
 * \param data  Word of data to send.
 */
extern void QSPI_Write( Qspi* qspi, uint16_t wData )
{
    /* Send data */
    while ( (qspi->QSPI_SR & QSPI_SR_TXEMPTY) == 0 ) ;
    qspi->QSPI_TDR = wData  ;
    while ( (qspi->QSPI_SR & QSPI_SR_TDRE) == 0 ) ;
}

/**
 * \brief Sends last data through a SPI peripheral.
 * If the SPI is configured to use a fixed peripheral select, the npcs value is
 * meaningless. Otherwise, it identifies the component which shall be addressed.
 *
 * \param spi   Pointer to an Spi instance.
 * \param npcs  Chip select of the component to address (0, 1, 2 or 3).
 * \param data  Word of data to send.
 */
extern void QSPI_WriteLast( Qspi* qspi,  uint16_t wData )
{
    /* Send data */
    while ( (qspi->QSPI_SR & QSPI_SR_TXEMPTY) == 0 ) ;
    qspi->QSPI_TDR = wData  ;
    qspi->QSPI_CR |= QSPI_CR_LASTXFER;
    while ( (qspi->QSPI_SR & QSPI_SR_TDRE) == 0 ) ;
}

/**
 * \brief Enable QSPI Chip Select.
 * \param qspi   Pointer to a Qspi instance.
 * \param cs    QSPI chip select index.
 */
extern void QSPI_ConfigureCs( Qspi* qspi, uint8_t spiCs )
{
    uint32_t dwSpiMr;

    /* Write to the MR register*/
    dwSpiMr = qspi->QSPI_MR ;
    dwSpiMr &= ~QSPI_MR_CSMODE_Msk ;
    dwSpiMr |= spiCs;
    qspi->QSPI_MR=dwSpiMr ;
}



/**
 * \brief Returns if data has been received. This
 * method must be called after a successful QSPI_Write call.
 *
 * \param qspi  Pointer to an Qspi instance.
 *
 * \return 1 if no data has been received else return return 0.
 */
extern int QSPI_RxEmpty(Qspi *qspi)
{
    return ((qspi->QSPI_SR & QSPI_SR_RDRF) == 0);
}

/**
 * \brief Returns 1 if application can write data. This
 * method must be called before QSPI_Write call.
 *
 * \param qspi  Pointer to an Qspi instance.
 *
 * \return 1 if application can write to the QSPI_TDR register else return return 0.
 */
extern int QSPI_TxRdy(Qspi *qspi)
{
    return ((qspi->QSPI_SR & QSPI_SR_TDRE) != 0);
}


/**
 * \brief Check if QSPI transfer finish.
 *
 * \param qspi  Pointer to an Qspi instance.
 *
 * \return Returns 1 if there is no pending write operation on the QSPI; otherwise
 * returns 0.
 */
extern uint32_t QSPI_IsFinished( Qspi* qspi )
{
    return ((qspi->QSPI_SR & QSPI_SR_TXEMPTY) != 0) ;
}

/**
 * \brief Check if QSPI Cs is asserted.
 *
 * \param qspi  Pointer to an Qspi instance.
 *
 * \return Returns 1 if tThe chip select is not asserted; otherwise
 * returns 0.
 */
extern uint32_t QSPI_IsCsAsserted( Qspi* qspi )
{
    return ((qspi->QSPI_SR & QSPI_SR_CSS) != 0) ;
}

/**
 * \brief Check if QSPI Cs is asserted.
 *
 * \param qspi  Pointer to an Qspi instance.
 *
 * \return Returns 1 if At least one chip select rise has been detected since the last read of QSPI_SR; otherwise
 * returns 0.
 */
extern uint32_t QSPI_IsCsRise( Qspi* qspi )
{
    return ((qspi->QSPI_SR & QSPI_SR_CSR) != 0) ;
}


/**
 * \brief Check if QSPI Cs is asserted.
 *
 * \param qspi  Pointer to an Qspi instance.
 *
 * \return Returns 1 if At least one instruction end has been detected since the last read of QSPI_SR.; otherwise
 * returns 0.
 */
extern uint32_t QSPI_IsEOFInst( Qspi* qspi )
{
    return ((qspi->QSPI_SR & QSPI_SR_INSTRE) != 0) ;
}

/**
 * \brief Send instrucion over SPI or QSPI
 *
 * \param qspi  Pointer to an Qspi instance.
 *
 * \return Returns 1 if At least one instruction end has been detected since the last read of QSPI_SR.; otherwise
 * returns 0.
 */
extern void QSPI_SendFrame( Qspi* qspi, qspiFrame *pFrame, AccesType  ReadWrite)
{  
    uint32_t regIFR, regICR, DummyRead;
    uint32_t *pQspiBuffer = (uint32_t *)QSPIMEM_ADDR;

    assert((qspi->QSPI_MR) & QSPI_MR_SMM);

    regIFR = (pFrame->spiMode | QSPI_IFR_INSTEN | (pFrame->OptionLen << QSPI_IFR_OPTL_Pos) | (pFrame->DummyCycles << QSPI_IFR_NBDUM_Pos)  | (pFrame->ContinuousRead << 14)) ;
    // Write the instruction to reg
    regICR = ( QSPI_ICR_OPT(pFrame->Option) | QSPI_ICR_INST(pFrame->Instruction));

    if(pFrame->OptionEn)
    {
        regIFR|=QSPI_IFR_OPTEN;
    }

    /* Instruction frame without Data, only Instruction**/  
    if(!(pFrame->DataSize))               
    {
        if(pFrame->InstAddrFlag)                            // If contain Address, put in IAr reg        
        {
            qspi->QSPI_IAR = pFrame->InstAddr;
            regIFR |= QSPI_IFR_ADDREN;
        }    
        qspi->QSPI_ICR = regICR;                            //  update Instruction code reg
        qspi->QSPI_IFR = regIFR;                            // Instruction Frame reg 
    }
    else  /* Instruction frame with Data and Instruction**/
    {    
        regIFR |= QSPI_IFR_DATAEN;    
        if(ReadWrite)
        {
            regIFR |= QSPI_IFR_TFRTYP_TRSFR_WRITE;      
            qspi->QSPI_ICR = regICR;
            qspi->QSPI_IFR = regIFR ;
            DummyRead =  qspi->QSPI_IFR;                        // to synchronize system bus accesses   
            if(pFrame->InstAddrFlag)
            {
                pQspiBuffer +=  pFrame->InstAddr;
            }
            memcpy(pQspiBuffer  ,pFrame->pData,  pFrame->DataSize); 
        } 
        else
        {      
            qspi->QSPI_ICR = regICR;
            qspi->QSPI_IFR = regIFR ;
            DummyRead =  qspi->QSPI_IFR;                        // to synchronize system bus accesses   
            memcpy(pFrame->pData,  pQspiBuffer,  pFrame->DataSize); 
        }

    }
    memory_barrier();
    qspi->QSPI_CR = QSPI_CR_LASTXFER;                     // End transmission after all data has been sent
    while(!(qspi->QSPI_SR & QSPI_SR_INSTRE));             // poll CR reg to know status if Intrustion has end



}


/**
 * \brief Send instrucion over SPI or QSPI
 *
 * \param qspi  Pointer to an Qspi instance.
 *
 * \return Returns 1 if At least one instruction end has been detected since the last read of QSPI_SR.; otherwise
 * returns 0.
 */
extern void QSPI_SendFrameToMem( Qspi* qspi, qspiFrame *pFrame, AccesType  ReadWrite)
{
    uint32_t regIFR, regICR, DummyRead ;
    uint8_t *pQspiMem = (uint8_t *)QSPIMEM_ADDR;

    assert((qspi->QSPI_MR) & QSPI_MR_SMM);  

    regIFR = (pFrame->spiMode | QSPI_IFR_INSTEN | QSPI_IFR_DATAEN | QSPI_IFR_ADDREN | (pFrame->OptionLen << QSPI_IFR_OPTL_Pos) | (pFrame->DummyCycles << QSPI_IFR_NBDUM_Pos) | (pFrame->ContinuousRead << 14)) ;
    // Write the instruction to reg
    regICR = ( QSPI_ICR_OPT(pFrame->Option) | QSPI_ICR_INST(pFrame->Instruction));
    if(pFrame->OptionEn)
    {
        regIFR|=QSPI_IFR_OPTEN;
    }
    pQspiMem +=  pFrame->InstAddr;
    if(ReadWrite)
    {   
        regIFR |= QSPI_IFR_TFRTYP_TRSFR_WRITE_MEMORY;
        memory_barrier();
        qspi->QSPI_ICR = regICR;
        qspi->QSPI_IFR = regIFR ;
        DummyRead =  qspi->QSPI_IFR;                // to synchronize system bus accesses  

        memcpy(pQspiMem  ,pFrame->pData,  pFrame->DataSize); 

    }
    else
    {
        regIFR |= QSPI_IFR_TFRTYP_TRSFR_READ_MEMORY;
        memory_barrier();
        qspi->QSPI_ICR = regICR;
        qspi->QSPI_IFR = regIFR ;
        DummyRead =  qspi->QSPI_IFR;                                                // to synchronize system bus accesses 
        memcpy(pFrame->pData, pQspiMem , pFrame->DataSize);   //  Read QSPI AHB memory space 

    } 
    memory_barrier();
    qspi->QSPI_CR = QSPI_CR_LASTXFER;             // End transmission after all data has been sent
    while(!(qspi->QSPI_SR & QSPI_SR_INSTRE));     // poll CR reg to know status if Intrustion has end

}

