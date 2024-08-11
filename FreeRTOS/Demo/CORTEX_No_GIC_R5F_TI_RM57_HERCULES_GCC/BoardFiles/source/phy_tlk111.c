/**
 *  \file   phy_Tlk111.c
 *
 *  \brief  APIs for configuring Tlk111.
 *
 *   This file contains the device abstraction APIs for PHY Tlk111.
 */

/* Copyright (C) 2010 Texas Instruments Incorporated - www.ti.com
 * ALL RIGHTS RESERVED
 */

#include "sys_common.h"
#include "mdio.h"
#include "phy_tlk111.h"

/*******************************************************************************
 *                        API FUNCTION DEFINITIONS
 *******************************************************************************/
/**
 * \brief   Reads the PHY ID.
 *
 * \param   mdioBaseAddr  Base Address of the MDIO Module Registers.
 * \param   phyAddr       PHY Adress.
 *
 * \return  32 bit PHY ID (ID1:ID2)
 *
 **/
/* SourceId : ETH_SourceId_063 */
/* DesignId : ETH_DesignId_063*/
/* Requirements : ETH_SR49 */
uint32 Tlk111IDGet( uint32 mdioBaseAddr, uint32 phyAddr )
{
    uint32 id = 0U;
    uint16 data = 0U;

    /* read the ID1 register */
    ( void ) MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_ID1, &data );

    /* update the ID1 value */
    id = ( uint32 ) data;
    id = ( uint32 ) ( ( uint32 ) id << PHY_ID_SHIFT );

    /* read the ID2 register */
    ( void ) MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_ID2, &data );

    /* update the ID2 value */
    id |= data;

    /* return the ID in ID1:ID2 format */
    return id;
}

void Tlk111SwStrap( uint32 mdioBaseAddr, uint32 phyAddr )
{
    MDIOPhyRegWrite( mdioBaseAddr, phyAddr, ( uint32 ) PHY_SWSCR1, Tlk111_SWSCR1_Val );
    MDIOPhyRegWrite( mdioBaseAddr, phyAddr, ( uint32 ) PHY_SWSCR2, Tlk111_SWSCR2_Val );
    MDIOPhyRegWrite( mdioBaseAddr, phyAddr, ( uint32 ) PHY_SWSCR3, Tlk111_SWSCR3_Val );
    MDIOPhyRegWrite( mdioBaseAddr,
                     phyAddr,
                     ( uint32 ) PHY_SWSCR1,
                     ( Tlk111_SWSCR1_Val | Tlk111_SWStrapDone ) );
}

/**
 * \brief   Reads the link status of the PHY.
 *
 * \param   mdioBaseAddr  Base Address of the MDIO Module Registers.
 * \param   phyAddr       PHY Adress.
 * \param   retries       The number of retries before indicating down status
 *
 * \return  link status after reading \n
 *          TRUE if link is up
 *          FALSE if link is down \n
 *
 * \note    This reads both the basic status register of the PHY and the
 *          link register of MDIO for double check
 **/
/* SourceId : ETH_SourceId_067 */
/* DesignId : ETH_DesignId_067*/
/* Requirements : ETH_SR47 */
boolean Tlk111LinkStatusGet( uint32 mdioBaseAddr,
                             uint32 phyAddr,
                             volatile uint32 retries )
{
    volatile uint16 linkStatus = 0U;
    boolean retVal = TRUE;

    while( retVal == TRUE )
    {
        /* First read the BSR of the PHY */
        ( void ) MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_BSR, &linkStatus );

        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        if( ( linkStatus & PHY_LINK_STATUS ) != 0U )
        {
            /* Check if MDIO LINK register is updated */
            linkStatus = ( uint16 ) MDIOPhyLinkStatusGet( mdioBaseAddr );

            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
            if( ( linkStatus & ( uint16 ) ( ( uint16 ) 1U << phyAddr ) ) != 0U )
            {
                break;
            }
            else
            {
                /*SAFETYMCUSW 9 S MR:12.2 <APPROVED> "Ternary Operator Expression" */
                /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
                /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
                if( retries != 0U )
                {
                    retries--;
                }
                else
                {
                    retVal = FALSE;
                }
            }
        }
        else
        {
            /*SAFETYMCUSW 9 S MR:12.2 <APPROVED> "Ternary Operator Expression" */
            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
            if( retries != 0U )
            {
                retries--;
            }
            else
            {
                retVal = FALSE;
            }
        }
    }

    return retVal;
}

/**
 * \brief   This function does Autonegotiates with the EMAC device connected
 *          to the PHY. It will wait till the autonegotiation completes.
 *
 * \param   mdioBaseAddr  Base Address of the MDIO Module Registers.
 * \param   phyAddr       PHY Adress.
 * \param   advVal        Autonegotiation advertisement value
 *          advVal can take the following any OR combination of the values \n
 *               Tlk111_100BTX - 100BaseTX
 *               Tlk111_100BTX_FD - Full duplex capabilty for 100BaseTX
 *               Tlk111_10BT - 10BaseT
 *               Tlk111_10BT_FD - Full duplex capability for 10BaseT
 *
 * \return  status after autonegotiation \n
 *          TRUE if autonegotiation successful
 *          FALSE if autonegotiation failed
 *
 **/
/* SourceId : ETH_SourceId_065 */
/* DesignId : ETH_DesignId_065*/
/* Requirements : ETH_SR46 */
boolean Tlk111AutoNegotiate( uint32 mdioBaseAddr, uint32 phyAddr, uint16 advVal )
{
    volatile uint16 data = 0U, anar = 0U;
    boolean retVal = TRUE;
    uint32 phyNegTries = 0xFFFFU;
    if( MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_BCR, &data ) != TRUE )
    {
        retVal = FALSE;
    }

    data |= PHY_AUTONEG_ENABLE;

    /* Enable Auto Negotiation */
    MDIOPhyRegWrite( mdioBaseAddr, phyAddr, ( uint32 ) PHY_BCR, data );

    if( MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_BCR, &data ) != TRUE )
    {
        retVal = FALSE;
    }

    /* Write Auto Negotiation capabilities */
    ( void ) MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_AUTONEG_ADV, &anar );
    anar &= ( uint16 ) ( ~0xff10U );
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
    MDIOPhyRegWrite( mdioBaseAddr,
                     phyAddr,
                     ( uint32 ) PHY_AUTONEG_ADV,
                     ( anar | advVal ) );

    data |= PHY_AUTONEG_RESTART;

    /* Start Auto Negotiation */
    MDIOPhyRegWrite( mdioBaseAddr, phyAddr, ( uint32 ) PHY_BCR, data );

    /* Get the auto negotiation status*/
    if( MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_BSR, &data ) != TRUE )
    {
        retVal = FALSE;
    }

    /* Wait till auto negotiation is complete */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( ( ( uint16 ) ( PHY_AUTONEG_INCOMPLETE ) )
             == ( data & ( uint16 ) ( PHY_AUTONEG_STATUS ) ) )
           && ( retVal == TRUE ) && ( phyNegTries > 0U ) )
    {
        ( void ) MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_BSR, &data );
        phyNegTries--;
    }

    /* Check if the PHY is able to perform auto negotiation */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
    if( ( data & PHY_AUTONEG_ABLE ) != 0U )
    {
        retVal = TRUE;
    }
    else
    {
        retVal = FALSE;
    }

    return retVal;
}

/**
 * \brief   Reads the Link Partner Ability register of the PHY.
 *
 * \param   mdioBaseAddr  Base Address of the MDIO Module Registers.
 * \param   phyAddr       PHY Adress.
 * \param   ptnerAblty    The partner abilities of the EMAC
 *
 * \return  status after reading \n
 *          TRUE if reading successful
 *          FALSE if reading failed
 **/
/* SourceId : ETH_SourceId_066 */
/* DesignId : ETH_DesignId_066*/
/* Requirements : ETH_SR48 */
boolean Tlk111PartnerAbilityGet( uint32 mdioBaseAddr,
                                 uint32 phyAddr,
                                 uint16 * ptnerAblty )
{
    return (
        MDIOPhyRegRead( mdioBaseAddr, phyAddr, PHY_LINK_PARTNER_ABLTY, ptnerAblty ) );
}

/**
 * \brief   Resets the PHY.
 *
 * \param   mdioBaseAddr  Base Address of the MDIO Module Registers.
 * \param   phyAddr       PHY Adress.
 *
 * \return  No return value.
 **/
/* SourceId : ETH_SourceId_064 */
/* DesignId : ETH_DesignId_064*/
/* Requirements : ETH_SR44 */
void Tlk111Reset( uint32 mdioBaseAddr, uint32 phyAddr )
{
    uint32 delay = 0x1FFFU;
    MDIOPhyRegWrite( mdioBaseAddr, phyAddr, PHY_BCR, PHY_LPBK_ENABLE );
    /* A wait of 3us is required before allowing further operation. */
    while( delay > 0U )
    {
        delay--;
    }
}

/**
 * \brief   Enables PHY Loopback.
 *
 * \param   mdioBaseAddr  Base Address of the MDIO Module Registers.
 * \param   phyAddr       PHY Adress.
 *
 * \return  No return value.
 **/
/* SourceId : ETH_SourceId_069 */
/* DesignId : ETH_DesignId_069*/
/* Requirements : ETH_SR51 */
void Tlk111EnableLoopback( uint32 mdioBaseAddr, uint32 phyAddr )
{
    uint32 delay = 0x1FFFU;
    uint16 regVal = 0x0000U;
    ( void ) MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_BCR, &regVal );
    /* Disabling Auto Negotiate. */
    /*SAFETYMCUSW 334 S MR:10.5 <APPROVED> "Only unsigned short values are used." */
    regVal &= ( uint16 ) ( ~( ( uint16 ) PHY_AUTONEG_ENABLE ) );
    /* Enabling Loopback. */
    regVal |= PHY_LPBK_ENABLE;

    MDIOPhyRegWrite( mdioBaseAddr, phyAddr, ( uint32 ) PHY_BCR, regVal );

    while( delay > 0U )
    {
        delay--;
    }
}

/**
 * \brief   Disable PHY Loopback.
 *
 * \param   mdioBaseAddr  Base Address of the MDIO Module Registers.
 * \param   phyAddr       PHY Adress.
 *
 * \return  No return value.
 **/
/* SourceId : ETH_SourceId_070 */
/* DesignId : ETH_DesignId_070*/
/* Requirements : ETH_SR51 */
void Tlk111DisableLoopback( uint32 mdioBaseAddr, uint32 phyAddr )
{
    uint32 delay = 0x1FFFU;
    uint16 regVal = 0x0000U;
    ( void ) MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_BCR, &regVal );

    /* Enabling Loopback. */
    /*SAFETYMCUSW 334 S MR:10.5 <APPROVED> "Only unsigned short values are used." */
    regVal &= ( uint16 ) ( ~( ( uint16 ) PHY_LPBK_ENABLE ) );

    MDIOPhyRegWrite( mdioBaseAddr, phyAddr, ( uint32 ) PHY_BCR, regVal );

    while( delay > 0U )
    {
        delay--;
    }
}
/**
 * \brief   Reads the Transmit/Receive Timestamp
 *
 * \param   mdioBaseAddr  Base Address of the MDIO Module Registers.
 * \param   phyAddr       PHY Adress.
 * \param   type	      1- Transmit Timetamp
 *    					  2- Receive Timestamp
 * \param   timestamp     The read value that is returned to the user.
 *
 * \return  The timestamp is returned in 4 16-bit reads. They are stored in the following
 *order: Timestamp_ns [63:49] Overflow_cnt[48:47], Timestamp_ns[46:33]
 *			Timestamp_sec[32:16]
 *			Timestamp_sec[15:0]
 *			This is returned as a 64 bit value.
 *
 **/
/* SourceId : ETH_SourceId_068 */
/* DesignId : ETH_DesignId_068*/
/* Requirements : ETH_SR53 */
uint64 Tlk111GetTimeStamp( uint32 mdioBaseAddr, uint32 phyAddr, phyTimeStamp_t type )
{
    uint16 ts = 0U;
    /* (MISRA-C:2004 10.1/R) MISRA error reported with Code Composer Studio MISRA checker
     * (due to use of & ?) */
    uint16 * tsptr = &ts;
    uint64 timeStamp = 0u;
    if( type == 1U )
    {
        ( void ) MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_TXTS, tsptr );
        timeStamp |= ( uint64 ) ts;
        ( void ) MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_TXTS, tsptr );
        timeStamp = timeStamp << 16U;
        timeStamp |= ( uint64 ) ts;
        ( void ) MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_TXTS, tsptr );
        timeStamp = timeStamp << 16U;
        timeStamp |= ( uint64 ) ts;
        ( void ) MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_TXTS, tsptr );
        timeStamp = timeStamp << 16U;
        timeStamp |= ( uint64 ) ts;
    }
    else
    {
        ( void ) MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_RXTS, tsptr );
        timeStamp |= ( uint64 ) ts;
        ( void ) MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_RXTS, tsptr );
        timeStamp = timeStamp << 16U;
        timeStamp |= ( uint64 ) ts;
        ( void ) MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_RXTS, tsptr );
        timeStamp = timeStamp << 16U;
        timeStamp |= ( uint64 ) ts;
        ( void ) MDIOPhyRegRead( mdioBaseAddr, phyAddr, ( uint32 ) PHY_RXTS, tsptr );
        timeStamp = timeStamp << 16U;
        timeStamp |= ( uint64 ) ts;
    }

    return timeStamp;
}

/**
 * \brief   Reads the Speed info from Status register of the PHY.
 *
 * \param   mdioBaseAddr  Base Address of the MDIO Module Registers.
 * \param   phyAddr       PHY Adress.
 * \param   ptnerAblty    The partner abilities of the EMAC
 *
 * \return  status after reading \n
 *          TRUE if reading successful
 *          FALSE if reading failed
 **/
boolean Tlk111PartnerSpdGet( uint32 mdioBaseAddr, uint32 phyAddr, uint16 * ptnerAblty )
{
    return ( MDIOPhyRegRead( mdioBaseAddr, phyAddr, PHY_LINK_PARTNER_SPD, ptnerAblty ) );
}

/**************************** End Of File ***********************************/
