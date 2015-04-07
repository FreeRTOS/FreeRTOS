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

/** \file */

/*---------------------------------------------------------------------------
 *         Headers
 *---------------------------------------------------------------------------*/

#include <board.h>

/*---------------------------------------------------------------------------
 *         Definitions
 *---------------------------------------------------------------------------*/

/** Default max retry count */
#define MACB_RETRY_MAX            1000000

/*---------------------------------------------------------------------------
 *         Local functions
 *---------------------------------------------------------------------------*/

/**
 * Wait PHY operation complete.
 * Return 1 if the operation completed successfully.
 * May be need to re-implemented to reduce CPU load.
 * \param retry: the retry times, 0 to wait forever until complete.
 */
static uint8_t EMAC_WaitPhy( Emac *pHw, uint32_t retry )
{
    volatile uint32_t retry_count = 0;

    while (!EMAC_IsIdle(pHw))
    {
        if(retry == 0) continue;
        retry_count ++;
        if (retry_count >= retry)
        {
            return 0;
        }
    }
    return 1;
}

/**
 * Read PHY register.
 * Return 1 if successfully, 0 if timeout.
 * \param pHw HW controller address
 * \param PhyAddress PHY Address
 * \param Address Register Address
 * \param pValue Pointer to a 32 bit location to store read data
 * \param retry The retry times, 0 to wait forever until complete.
 */
static uint8_t EMAC_ReadPhy(Emac *pHw,
                            uint8_t PhyAddress,
                            uint8_t Address,
                            uint32_t *pValue,
                            uint32_t retry)
{
    EMAC_PHYMaintain(pHw, PhyAddress, Address, 1, 0);
    if ( EMAC_WaitPhy(pHw, retry) == 0 )
    {
        TRACE_ERROR("TimeOut EMAC_ReadPhy\n\r");
        return 0;
    }
    *pValue = EMAC_PHYData(pHw);
    return 1;
}

/**
 * Write PHY register
 * Return 1 if successfully, 0 if timeout.
 * \param pHw HW controller address
 * \param PhyAddress PHY Address
 * \param Address Register Address
 * \param Value Data to write ( Actually 16 bit data )
 * \param retry The retry times, 0 to wait forever until complete.
 */
static uint8_t EMAC_WritePhy(Emac *pHw,
                             uint8_t PhyAddress,
                             uint8_t Address,
                             uint32_t  Value,
                             uint32_t  retry)
{
    EMAC_PHYMaintain(pHw, PhyAddress, Address, 0, Value);
    if ( EMAC_WaitPhy(pHw, retry) == 0 )
    {
        TRACE_ERROR("TimeOut EMAC_WritePhy\n\r");
        return 0;
    }
    return 1;
}

/*---------------------------------------------------------------------------
 *         Exported functions
 *---------------------------------------------------------------------------*/

/**
 * Find a valid PHY Address ( from addrStart to 31 ).
 * Check BMSR register ( not 0 nor 0xFFFF )
 * Return 0xFF when no valid PHY Address found.
 * \param pMacb Pointer to the MACB instance
 */
uint8_t MACB_FindValidPhy(Macb *pMacb, uint8_t addrStart)
{
    sEmacd *pDrv = pMacb->pEmacd;
    Emac *pHw = pDrv->pHw;

    uint32_t  retryMax;
    uint32_t  value=0;
    uint8_t rc;
    uint8_t phyAddress;
    uint8_t cnt;

    TRACE_DEBUG("MACB_FindValidPhy\n\r");

    EMAC_ManagementEnable(pHw, 1);

    phyAddress = pMacb->phyAddress;
    retryMax = pMacb->retryMax;

    /* Check current phyAddress */
    rc = phyAddress;
    if( EMAC_ReadPhy(pHw, phyAddress, MII_PHYID1, &value, retryMax) == 0 )
    {
        TRACE_ERROR("MACB PROBLEM\n\r");
    }
    TRACE_DEBUG("_PHYID1  : 0x%X, addr: %d\n\r", value, phyAddress);

    /* Find another one */
    if (value != MII_OUI_MSB)
    {
        rc = 0xFF;
        for(cnt = 0; cnt < 32; cnt ++)
        {
            phyAddress = (phyAddress + 1) & 0x1F;
            if( EMAC_ReadPhy(pHw, phyAddress, MII_PHYID1, &value, retryMax) == 0 )
            {
                TRACE_ERROR("MACB PROBLEM\n\r");
            }
            TRACE_DEBUG("_PHYID1  : 0x%X, addr: %d\n\r", value, phyAddress);
            if (value == MII_OUI_MSB)
            {
                rc = phyAddress;
                break;
            }
        }
    }

    EMAC_ManagementEnable(pHw, 0);

    if (rc != 0xFF)
    {

        printf("** Valid PHY Found: %d\n\r", rc);
        EMAC_ReadPhy(pHw, phyAddress, MII_DSCSR, &value, retryMax);
        TRACE_DEBUG("_DSCSR  : 0x%X, addr: %d\n\r", value, phyAddress);

    }
    return rc;
}

/**
 * Dump all the useful registers
 * \param pMacb          Pointer to the MACB instance
 */
void MACB_DumpRegisters(Macb *pMacb)
{
    sEmacd *pDrv = pMacb->pEmacd;
    Emac *pHw = pDrv->pHw;

    uint8_t phyAddress;
    uint32_t retryMax;
    uint32_t value;

    TRACE_INFO("MACB_DumpRegisters\n\r");

    EMAC_ManagementEnable(pHw, 1);

    phyAddress = pMacb->phyAddress;
    retryMax = pMacb->retryMax;

    TRACE_INFO("%cMII MACB (@%d) Registers:\n\r",
        pMacb->RMII ? 'R' : ' ',
        phyAddress);

    EMAC_ReadPhy(pHw, phyAddress, MII_BMCR, &value, retryMax);
    TRACE_INFO(" _BMCR   : 0x%X\n\r", value);
    EMAC_ReadPhy(pHw, phyAddress, MII_BMSR, &value, retryMax);
    TRACE_INFO(" _BMSR   : 0x%X\n\r", value);
    EMAC_ReadPhy(pHw, phyAddress, MII_ANAR, &value, retryMax);
    TRACE_INFO(" _ANAR   : 0x%X\n\r", value);
    EMAC_ReadPhy(pHw, phyAddress, MII_ANLPAR, &value, retryMax);
    TRACE_INFO(" _ANLPAR : 0x%X\n\r", value);
    EMAC_ReadPhy(pHw, phyAddress, MII_ANER, &value, retryMax);
    TRACE_INFO(" _ANER   : 0x%X\n\r", value);
    EMAC_ReadPhy(pHw, phyAddress, MII_DSCR, &value, retryMax);
    TRACE_INFO(" _DSCR   : 0x%X\n\r", value);
    EMAC_ReadPhy(pHw, phyAddress, MII_DSCSR, &value, retryMax);
    TRACE_INFO(" _DSCSR  : 0x%X\n\r", value);
    EMAC_ReadPhy(pHw, phyAddress, MII_10BTCSR, &value, retryMax);
    TRACE_INFO(" _10BTCSR: 0x%X\n\r", value);
    EMAC_ReadPhy(pHw, phyAddress, MII_PWDOR, &value, retryMax);
    TRACE_INFO(" _PWDOR  : 0x%X\n\r", value);
    EMAC_ReadPhy(pHw, phyAddress, MII_CONFIGR, &value, retryMax);
    TRACE_INFO(" _CONFIGR: 0x%X\n\r", value);
    EMAC_ReadPhy(pHw, phyAddress, MII_MDINTR, &value, retryMax);
    TRACE_INFO(" _MDINTR : 0x%X\n\r", value);
    EMAC_ReadPhy(pHw, phyAddress, MII_RECR, &value, retryMax);
    TRACE_INFO(" _RECR   : 0x%X\n\r", value);
    EMAC_ReadPhy(pHw, phyAddress, MII_DISCR, &value, retryMax);
    TRACE_INFO(" _DISCR  : 0x%X\n\r", value);
    EMAC_ReadPhy(pHw, phyAddress, MII_RLSR, &value, retryMax);
    TRACE_INFO(" _RLSR   : 0x%X\n\r", value);

    EMAC_ManagementEnable(pHw, 0);
}

/**
 * Setup the maximum timeout count of the driver.
 * \param pMacb   Pointer to the MACB instance
 * \param toMax   Timeout maxmum count.
 */
void MACB_SetupTimeout(Macb *pMacb, uint32_t toMax)
{
    pMacb->retryMax = toMax;
}

/**
 * Initialize the MACB instance
 * \param pMacb        Pointer to the MACB instance
 * \param pEmac        Pointer to the Emac instance for the MACB
 * \param phyAddress   The PHY address used to access the PHY
 *                     ( pre-defined by pin status on PHY reset )
 */
void MACB_Init(Macb *pMacb, sEmacd *pEmacd, uint8_t phyAddress)
{
    pMacb->pEmacd = pEmacd;
    pMacb->phyAddress = phyAddress;
    /* Initialize timeout by default */
    pMacb->retryMax = MACB_RETRY_MAX;
}

/**
 * Issue a SW reset to reset all registers of the PHY
 * Return 1 if successfully, 0 if timeout.
 * \param pMacb   Pointer to the MACB instance
 */
uint8_t MACB_ResetPhy(Macb *pMacb)
{
    sEmacd *pDrv = pMacb->pEmacd;
    Emac *pHw = pDrv->pHw;

    uint32_t retryMax;
    uint32_t bmcr = MII_RESET;
    uint8_t phyAddress;
    uint32_t timeout = 10;
    uint8_t ret = 1;

    TRACE_INFO(" MACB_ResetPhy\n\r");

    phyAddress = pMacb->phyAddress;
    retryMax = pMacb->retryMax;

    EMAC_ManagementEnable(pHw, 1);

    bmcr = MII_RESET;
    EMAC_WritePhy(pHw, phyAddress, MII_BMCR, bmcr, retryMax);

    do
    {
        EMAC_ReadPhy(pHw, phyAddress, MII_BMCR, &bmcr, retryMax);
        timeout--;
    } while ((bmcr & MII_RESET) && timeout);

    EMAC_ManagementEnable(pHw, 0);

    if (!timeout)
    {
        ret = 0;
    }

    return( ret );
}

/**
 * Do a HW initialize to the PHY ( via RSTC ) and setup clocks & PIOs
 * This should be called only once to initialize the PHY pre-settings.
 * The PHY address is reset status of CRS,RXD[3:0] (the emacPins' pullups).
 * The COL pin is used to select MII mode on reset (pulled up for Reduced MII)
 * The RXDV pin is used to select test mode on reset (pulled up for test mode)
 * The above pins should be predefined for corresponding settings in resetPins
 * The EMAC peripheral pins are configured after the reset done.
 * Return 1 if RESET OK, 0 if timeout.
 * \param pMacb         Pointer to the MACB instance
 * \param mck         Main clock setting to initialize clock
 * \param resetPins   Pointer to list of PIOs to configure before HW RESET
 *                       (for PHY power on reset configuration latch)
 * \param nbResetPins Number of PIO items that should be configured
 * \param emacPins    Pointer to list of PIOs for the EMAC interface
 * \param nbEmacPins  Number of PIO items that should be configured
 */

uint8_t MACB_InitPhy(Macb         *pMacb,
                     uint32_t      mck,
                     const Pin    *pResetPins,
                     uint32_t      nbResetPins,
                     const Pin    *pEmacPins,
                     uint32_t      nbEmacPins)
{
    sEmacd *pDrv = pMacb->pEmacd;
    Emac *pHw = pDrv->pHw;

    uint8_t rc = 1;
    uint8_t phy;

    /* Perform RESET */
    TRACE_DEBUG("RESET PHY\n\r");
    
    if (pResetPins)
    {
        /* Configure PINS */
        PIO_Configure(pResetPins, nbResetPins);
        /* Execute reset */
        RSTC_SetExtResetLength(MACB_RESET_LENGTH);
        RSTC_ExtReset();
        /* Get NRST level */
        /* Wait for end hardware reset */
        while (!RSTC_GetNrstLevel());
    }
    /* Configure EMAC runtime pins */
    if (rc)
    {
        PIO_Configure(pEmacPins, nbEmacPins);
        rc = EMAC_SetClock( pHw, mck );
        if (!rc)
        {
            TRACE_ERROR("No Valid MDC clock\n\r");
            return 0;
        }

        /* Check PHY Address */
        phy = MACB_FindValidPhy(pMacb, 0);
        if (phy == 0xFF)
        {
            TRACE_ERROR("PHY Access fail\n\r");
            return 0;
        }
        if(phy != pMacb->phyAddress)
        {
            pMacb->phyAddress = phy;
            MACB_ResetPhy(pMacb);
        }

    }
    else
    {
        TRACE_ERROR("PHY Reset Timeout\n\r");
    }

    return rc;
}

/**
 * Issue a Auto Negotiation of the PHY
 * Return 1 if successfully, 0 if timeout.
 * \param pMacb   Pointer to the MACB instance
 */
uint8_t MACB_AutoNegotiate(Macb *pMacb, uint8_t rmiiMode)
{
    sEmacd *pDrv = pMacb->pEmacd;
    Emac *pHw = pDrv->pHw;

    uint32_t retryMax;
    uint32_t value;
    uint32_t phyAnar;
    uint32_t phyAnalpar;
    uint32_t retryCount= 0;
    uint8_t phyAddress;
    uint8_t bFD = 0;
    uint8_t bSP = 0;
    uint8_t rc = 1;

    pMacb->RMII = rmiiMode;

    phyAddress = pMacb->phyAddress;
    retryMax = pMacb->retryMax;

    EMAC_ManagementEnable(pHw, 1);

    if (!EMAC_ReadPhy(pHw, phyAddress, MII_PHYID1, &value, retryMax))
    {
        TRACE_ERROR("Pb EMAC_ReadPhy Id1\n\r");
        rc = 0;
        goto AutoNegotiateExit;
    }
    TRACE_DEBUG("ReadPhy Id1 0x%X, addresse: %d\n\r", value, phyAddress);
    if (!EMAC_ReadPhy(pHw, phyAddress, MII_PHYID2, &phyAnar, retryMax))
    {
        TRACE_ERROR("Pb EMAC_ReadPhy Id2\n\r");
        rc = 0;
        goto AutoNegotiateExit;
    }
    TRACE_DEBUG("ReadPhy Id2 0x%X\n\r", phyAnar);

    if( ( value == MII_OUI_MSB )
     && ( ((phyAnar>>10)&MII_LSB_MASK) == MII_OUI_LSB ) )
    {
        TRACE_DEBUG("Vendor Number Model = 0x%X\n\r", ((phyAnar>>4)&0x3F));
        TRACE_DEBUG("Model Revision Number = 0x%X\n\r", (phyAnar&0x7));
    }
    else
    {
        TRACE_ERROR("Problem OUI value\n\r");
    }        

    /* Setup control register */
    rc  = EMAC_ReadPhy(pHw, phyAddress, MII_BMCR, &value, retryMax);
    if (rc == 0)
    {
        goto AutoNegotiateExit;
    }

    value &= ~MII_AUTONEG;   /* Remove autonegotiation enable */
    value &= ~(MII_LOOPBACK|MII_POWER_DOWN);
    value |=  MII_ISOLATE;   /* Electrically isolate PHY */
    rc = EMAC_WritePhy(pHw, phyAddress, MII_BMCR, value, retryMax);
    if (rc == 0)
    {
        goto AutoNegotiateExit;
    }

    /* Set the Auto_negotiation Advertisement Register
       MII advertising for Next page
       100BaseTxFD and HD, 10BaseTFD and HD, IEEE 802.3 */
    phyAnar = MII_TX_FDX | MII_TX_HDX |
              MII_10_FDX | MII_10_HDX | MII_AN_IEEE_802_3;
    rc = EMAC_WritePhy(pHw, phyAddress, MII_ANAR, phyAnar, retryMax);
    if (rc == 0)
    {
        goto AutoNegotiateExit;
    }

    /* Read & modify control register */
    rc  = EMAC_ReadPhy(pHw, phyAddress, MII_BMCR, &value, retryMax);
    if (rc == 0)
    {
        goto AutoNegotiateExit;
    }

    value |= MII_SPEED_SELECT | MII_AUTONEG | MII_DUPLEX_MODE;
    rc = EMAC_WritePhy(pHw, phyAddress, MII_BMCR, value, retryMax);
    if (rc == 0)
    {
        goto AutoNegotiateExit;
    }

    /* Restart Auto_negotiation */
    value |=  MII_RESTART_AUTONEG;
    value &= ~MII_ISOLATE;
    rc = EMAC_WritePhy(pHw, phyAddress, MII_BMCR, value, retryMax);
    if (rc == 0)
    {
        goto AutoNegotiateExit;
    }
    TRACE_DEBUG(" _BMCR: 0x%X\n\r", value);

    /* Check AutoNegotiate complete */
    while (1)
    {
        rc  = EMAC_ReadPhy(pHw, phyAddress, MII_BMSR, &value, retryMax);
        if (rc == 0)
        {
            TRACE_ERROR("_BMSR Rd err\n\r");
            goto AutoNegotiateExit;
        }
        /* Done successfully */
        if (value & MII_AUTONEG_COMP)
        {
            printf("AutoNegotiate complete\n\r");
            break;
        }

        /* Timeout check */
        if (retryMax)
        {
            if (++ retryCount >= retryMax)
            {
                MACB_DumpRegisters(pMacb);
                TRACE_ERROR("TimeOut\n\r");
                rc = 0;
                goto AutoNegotiateExit;
            }
        }
    }

    /* Get the AutoNeg Link partner base page */
    rc  = EMAC_ReadPhy(pHw, phyAddress, MII_ANLPAR, &phyAnalpar, retryMax);
    if (rc == 0)
    {
        goto AutoNegotiateExit;
    }

    /* Setup the EMAC link speed */
    if ((phyAnar & phyAnalpar) & MII_TX_FDX)
    {
        /* set MII for 100BaseTX and Full Duplex */
        bSP = 1; bFD = 1;
    }
    else if ((phyAnar & phyAnalpar) & MII_10_FDX)
    {
        /* set MII for 10BaseT and Full Duplex */
        bSP = 0; bFD = 1;
    }
    else if ((phyAnar & phyAnalpar) & MII_TX_HDX)
    {
        // set MII for 100BaseTX and half Duplex
        bSP = 1; bFD = 0;
    }
    else if ((phyAnar & phyAnalpar) & MII_10_HDX)
    {
        // set MII for 10BaseT and half Duplex
        bSP = 0; bFD = 0;
    }
    EMAC_SetSpeed(pHw, bSP);
    EMAC_FullDuplexEnable(pHw, bFD);

    EMAC_RMIIEnable(pHw, rmiiMode);
    EMAC_TransceiverClockEnable(pHw, 1);

AutoNegotiateExit:
    EMAC_ManagementEnable(pHw, 0);
    return rc;
}

/**
 * Get the Link & speed settings, and automatically setup the EMAC with the
 * settings.
 * Return 1 if link found, 0 if no ethernet link.
 * \param pMacb          Pointer to the MACB instance
 * \param applySetting Apply the settings to EMAC interface
 */
uint8_t MACB_GetLinkSpeed(Macb *pMacb, uint8_t applySetting)
{
    sEmacd *pDrv = pMacb->pEmacd;
    Emac *pHw = pDrv->pHw;

    uint32_t retryMax;
    uint32_t stat1;
    uint32_t stat2;
    uint8_t phyAddress, bSP, bFD;
    uint8_t rc = 1;
       
    TRACE_DEBUG("MACB_GetLinkSpeed\n\r");
    bSP = 0; bFD = 0;
    EMAC_ManagementEnable(pHw, 1);

    phyAddress = pMacb->phyAddress;
    retryMax = pMacb->retryMax;

    rc  = EMAC_ReadPhy(pHw, phyAddress, MII_BMSR, &stat1, retryMax);
    if (rc == 0)
    {
        goto GetLinkSpeedExit;
    }

    if ((stat1 & MII_LINK_STATUS) == 0)
    {
        TRACE_ERROR("Pb: LinkStat: 0x%x\n\r", (unsigned int)stat1);
        rc = 0;
        goto GetLinkSpeedExit;
    }

    if (applySetting == 0)
    {
        TRACE_WARNING("Speed #%d not applied\n\r", applySetting);
        bSP = 0; bFD = 0;
        goto GetLinkSpeedExit;
    }

    /* Re-configure Link speed */
    rc  = EMAC_ReadPhy(pHw, phyAddress, MII_DSCSR, &stat2, retryMax);
    if (rc == 0)
    {
        TRACE_ERROR("Pb _DSCSR: rc 0x%x\n\r", rc);
        goto GetLinkSpeedExit;
    }

    if ((stat1 & MII_100BASE_TX_FD) && (stat2 & MII_100FDX))
    {
        /* set Emac for 100BaseTX and Full Duplex */
        bSP = 1; bFD = 1;
    }

    if ((stat1 & MII_10BASE_T_FD) && (stat2 & MII_10FDX))
    {
        /* set MII for 10BaseT and Full Duplex */
        bSP= 0; bFD = 1;
    }

    if ((stat1 & MII_100BASE_T4_HD) && (stat2 & MII_100HDX))
    {
        /* set MII for 100BaseTX and Half Duplex */
        bSP = 1; bFD = 0;
    }

    if ((stat1 & MII_10BASE_T_HD) && (stat2 & MII_10HDX))
    {
        /* set MII for 10BaseT and Half Duplex */
        bSP = 0; bFD = 0;
    }
    EMAC_SetSpeed(pHw, bSP);
    EMAC_FullDuplexEnable(pHw, bFD);

    /* Start the EMAC transfers */
    TRACE_DEBUG("MACB_GetLinkSpeed passed\n\r");

GetLinkSpeedExit:
    EMAC_ManagementEnable(pHw, 0);
    return rc;
}

