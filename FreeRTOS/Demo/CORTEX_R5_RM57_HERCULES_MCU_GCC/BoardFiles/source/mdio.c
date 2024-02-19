/**
 *  \file   mdio.c
 *
 *  \brief  MDIO APIs.
 *
 *   This file contains the device abstraction layer APIs for MDIO.
 */

/*
 * Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

/* USER CODE BEGIN (0) */
/* USER CODE END */

#include "hw_reg_access.h"
#include "mdio.h"

/* USER CODE BEGIN (1) */
/* USER CODE END */

/*******************************************************************************
 *                       INTERNAL MACRO DEFINITIONS
 *******************************************************************************/
#define PHY_REG_MASK   ( 0x1FU )
#define PHY_ADDR_MASK  ( 0x1FU )
#define PHY_DATA_MASK  ( 0xFFFFU )
#define PHY_REG_SHIFT  ( 21U )
#define PHY_ADDR_SHIFT ( 16U )

/*******************************************************************************
 *                        API FUNCTION DEFINITIONS
 *******************************************************************************/

/**
 * \brief   Reads a PHY register using MDIO.
 *
 * \param   baseAddr      Base Address of the MDIO Module Registers.
 * \param   phyAddr       PHY Address.
 * \param   regNum        Register Number to be read.
 * \param   dataPtr       Pointer where the read value shall be written.
 *
 * \return  status of the read \n
 *          TRUE - read is successful.\n
 *          FALSE - read is not acknowledged properly.
 *
 **/
/* SourceId : ETH_SourceId_059 */
/* DesignId : ETH_DesignId_059*/
/* Requirements : CONQ_EMAC_SR62 */
boolean MDIOPhyRegRead( uint32 baseAddr,
                        uint32 phyAddr,
                        uint32 regNum,
                        volatile uint16 * dataPtr )
{
    boolean retVal = FALSE;
    /* Wait till transaction completion if any */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( HWREG( baseAddr + MDIO_USERACCESS0 ) & MDIO_USERACCESS0_GO )
           == MDIO_USERACCESS0_GO )
    {
    } /* Wait */

    HWREG( baseAddr
           + MDIO_USERACCESS0 ) = ( ( ( uint32 ) MDIO_USERACCESS0_READ )
                                    | MDIO_USERACCESS0_GO
                                    | ( ( regNum & PHY_REG_MASK ) << PHY_REG_SHIFT )
                                    | ( ( phyAddr & PHY_ADDR_MASK ) << PHY_ADDR_SHIFT ) );

    /* wait for command completion */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( HWREG( baseAddr + MDIO_USERACCESS0 ) & MDIO_USERACCESS0_GO )
           == MDIO_USERACCESS0_GO )
    {
    } /* Wait */

    /* Store the data if the read is acknowledged */
    if( ( ( HWREG( baseAddr + MDIO_USERACCESS0 ) ) & MDIO_USERACCESS0_ACK )
        == MDIO_USERACCESS0_ACK )
    {
        /*SAFETYMCUSW 439 S MR:11.3 <APPROVED> "Output is a 16 bit Value to be stored -
         * Advisory as per MISRA" */
        *dataPtr = ( uint16 ) ( ( HWREG( baseAddr + MDIO_USERACCESS0 ) )
                                & PHY_DATA_MASK );
        retVal = TRUE;
    }

    return retVal;
}

/**
 * \brief   Writes a PHY register using MDIO.
 *
 * \param   baseAddr      Base Address of the MDIO Module Registers.
 * \param   phyAddr       PHY Address.
 * \param   regNum        Register Number to be read.
 * \param   RegVal        Value to be written.
 *
 * \return  None
 *
 **/
/* SourceId : ETH_SourceId_058 */
/* DesignId : ETH_DesignId_058*/
/* Requirements : CONQ_EMAC_SR63 */
void MDIOPhyRegWrite( uint32 baseAddr, uint32 phyAddr, uint32 regNum, uint16 RegVal )
{
    /* Wait till transaction completion if any */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( HWREG( baseAddr + MDIO_USERACCESS0 ) & MDIO_USERACCESS0_GO )
           == MDIO_USERACCESS0_GO )
    {
    } /* Wait */

    HWREG( baseAddr
           + MDIO_USERACCESS0 ) = ( MDIO_USERACCESS0_WRITE | MDIO_USERACCESS0_GO
                                    | ( ( regNum & PHY_REG_MASK ) << PHY_REG_SHIFT )
                                    | ( ( phyAddr & PHY_ADDR_MASK ) << PHY_ADDR_SHIFT )
                                    | RegVal );

    /* wait for command completion*/
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( HWREG( baseAddr + MDIO_USERACCESS0 ) & MDIO_USERACCESS0_GO )
           == MDIO_USERACCESS0_GO )
    {
    } /* Wait */
}
/**
 * \brief   Reads the alive status of all PHY connected to the MDIO.
 *          The bit corresponding to the PHY address will be set if the PHY
 *          is alive.
 *
 * \param   baseAddr      Base Address of the MDIO Module Registers.
 *
 * \return  MDIO alive register state
 *
 **/
/* SourceId : ETH_SourceId_062 */
/* DesignId : ETH_DesignId_062*/
/* Requirements : CONQ_EMAC_SR64 */
uint32 MDIOPhyAliveStatusGet( uint32 baseAddr )
{
    return ( HWREG( baseAddr + MDIO_ALIVE ) );
}

/**
 * \brief   Reads the link status of all PHY connected to the MDIO.
 *          The bit corresponding to the PHY address will be set if the PHY
 *          link is active.
 *
 * \param   baseAddr      Base Address of the MDIO Module Registers.
 *
 * \return  MDIO link register state
 *
 **/
/* SourceId : ETH_SourceId_061 */
/* DesignId : ETH_DesignId_061*/
/* Requirements : CONQ_EMAC_SR67 */
uint32 MDIOPhyLinkStatusGet( uint32 baseAddr )
{
    return ( HWREG( baseAddr + MDIO_LINK ) );
}

/**
 * \brief   Initializes the MDIO peripheral. This enables the MDIO state
 *          machine, uses standard pre-amble and set the clock divider value.
 *
 * \param   baseAddr       Base Address of the MDIO Module Registers.
 * \param   mdioInputFreq  The clock input to the MDIO module
 * \param   mdioOutputFreq The clock output required on the MDIO bus
 * \return  None
 *
 **/
/* SourceId : ETH_SourceId_060 */
/* DesignId : ETH_DesignId_060*/
/* Requirements : CONQ_EMAC_SR59 */
void MDIOInit( uint32 baseAddr, uint32 mdioInputFreq, uint32 mdioOutputFreq )
{
    uint32 clkDiv = ( mdioInputFreq / mdioOutputFreq ) - 1U;
    HWREG( baseAddr + MDIO_CONTROL ) = ( ( clkDiv & MDIO_CONTROL_CLKDIV )
                                         | MDIO_CONTROL_ENABLE | MDIO_CONTROL_PREAMBLE
                                         | MDIO_CONTROL_FAULTENB );
}

/**
 * \brief   Function to enable MDIO.
 *
 * \param   baseAddr      Base Address of the MDIO Module Registers.
 *
 * \return  none
 *
 **/
/* SourceId : ETH_SourceId_056 */
/* DesignId : ETH_DesignId_056*/
/* Requirements : CONQ_EMAC_SR60 */
void MDIOEnable( uint32 baseAddr )
{
    HWREG( baseAddr + MDIO_CONTROL ) = HWREG( baseAddr + MDIO_CONTROL )
                                     | MDIO_CONTROL_ENABLE;
}

/**
 * \brief   Function to disable MDIO.
 *
 * \param   baseAddr      Base Address of the MDIO Module Registers.
 *
 * \return  none
 *
 **/
/* SourceId : ETH_SourceId_057 */
/* DesignId : ETH_DesignId_057*/
/* Requirements : CONQ_EMAC_SR61 */
void MDIODisable( uint32 baseAddr )
{
    HWREG( baseAddr + MDIO_CONTROL ) = HWREG( baseAddr + MDIO_CONTROL )
                                     & ( ~MDIO_CONTROL_ENABLE );
}

/* USER CODE BEGIN (2) */
/* USER CODE END */

/***************************** End Of File ***********************************/
