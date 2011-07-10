/*!
 * \file    eth_phy.c
 * \brief   Ethernet Physical Layer Interface Driver
 * \version $Revision: 1.3 $
 * \author  Michael Norman
 * 
 * This is a generic driver for all Ethernet PHYs with the basic MII registers
 */

#include "common.h"
#include "eth_phy.h"
#include "mii.h"

/* Variable to save off auto-negotiate settings */
int eth_phy_anar = 0
    | PHY_ANAR_100BTX_FDX
    | PHY_ANAR_100BTX
    | PHY_ANAR_10BT_FDX
    | PHY_ANAR_10BT;

int
eth_phy_reset(int ch, int phy_addr)
{
#if MII_CHECK_TIMEOUT
    int timeout; 
#endif
    int settings;

    /* Reset the PHY */
    if (mii_write(ch, phy_addr, PHY_BMCR, PHY_BMCR_RESET)) 
        return 1;
    /* Wait for reset to complete */
#if MII_CHECK_TIMEOUT
    for (timeout = 0; timeout < MII_LINK_TIMEOUT; ++timeout)
#endif
    while(1)
    {
      /* Read back the contents of the CTRL register and verify
       * that RESET is not set - this is a sanity check to ensure
       * that we are talking to the PHY correctly. RESET should
       * always be cleared. */
      if (!(mii_read(ch, phy_addr, PHY_BMCR, &settings)) && !(settings & PHY_BMCR_RESET))
        break;/*FSL: ready*/
    }
#if MII_CHECK_TIMEOUT
    if (timeout == MII_LINK_TIMEOUT || (settings & PHY_BMCR_RESET))
        return 1;
    else
#endif      
        return 0;
}

/********************************************************************/
/*!
 * \brief   Enable the Ethernet PHY in auto-negotiate mode
 * \param   phy_addr    Address of the PHY
 * \param   speed       Desired speed (MII_10BASE_T or MII_100BASE_TX)
 * \param   duplex      Desired duplex (MII_FDX or MII_HDX)
 * \return  0 if successful; non-zero otherwise
 */
int
eth_phy_autoneg(int ch, int phy_addr, ENET_SPEED speed, ENET_DUPLEX duplex)
{
    int timeout, settings;

    /* Reset the PHY */
    eth_phy_reset(ch, phy_addr);

    /* Set the Auto-Negotiation Advertisement Register */
    if (speed == MII_10BASET)
    {
        settings = (duplex == MII_FDX) 
            ? PHY_ANAR_10BT_FDX | PHY_ANAR_10BT 
            : PHY_ANAR_10BT;
    }
    else /* (speed == MII_100BASET) */
    {
        settings = (duplex == MII_FDX)  
            ? PHY_ANAR_100BTX_FDX   | 
              PHY_ANAR_100BTX       | 
              PHY_ANAR_10BT_FDX     | 
              PHY_ANAR_10BT
            : PHY_ANAR_10BT_FDX     | 
              PHY_ANAR_10BT;
    }
    
    /* Save off the settings we just advertised */
    eth_phy_anar = settings;
    
    if (mii_write(ch, phy_addr, PHY_ANAR, settings))
        return 1;
        
    /* Enable Auto-Negotiation */
    if (mii_write(ch, phy_addr, PHY_BMCR, PHY_BMCR_AN_ENABLE | PHY_BMCR_AN_RESTART))
        return 1;

    /* Wait for auto-negotiation to complete */
    for (timeout = 0; timeout < MII_LINK_TIMEOUT; ++timeout)
    {
        if (mii_read(ch, phy_addr, PHY_BMSR, &settings))
            return 1;
        if (settings & PHY_BMSR_AN_COMPLETE)
            break;
    }
    /* Read the BMSR one last time */
    if (mii_read(ch, phy_addr, PHY_BMSR, &settings))
        return 1;
    if (timeout == MII_LINK_TIMEOUT || !(settings & PHY_BMSR_LINK))
        return 1;
    else
        return 0;
}
/********************************************************************/
/*!
 * \brief   Enable the Ethernet PHY in manual mode
 * \param   phy_addr    Address of the PHY
 * \param   speed       Desired speed (MII_10BASE_T or MII_100BASE_TX)
 * \param   duplex      Desired duplex (MII_FDX or MII_HDX)
 * \param   loop        Put PHY in loopback mode?
 * \return  0 if successful; non-zero otherwise
 */
int 
eth_phy_manual(int ch, int phy_addr, ENET_SPEED speed, ENET_DUPLEX duplex, int loop)
{
    int timeout; 
    int settings = 0;
  
    /* Reset the PHY */
        /* Reset the PHY */
    eth_phy_reset(ch, phy_addr);
    
    if (loop)
        settings |= PHY_BMCR_LOOP;
    if (duplex == MII_FDX)
        settings |= PHY_BMCR_FDX;
    if (speed == MII_100BASET)
        settings |= PHY_BMCR_SPEED;

    if (mii_write(ch, phy_addr, PHY_BMCR, settings))
        return 1;
    
    /* Wait for link */
    for (timeout = 0; timeout < MII_LINK_TIMEOUT; ++timeout)
    {
        if (mii_read(ch, phy_addr, PHY_BMSR, &settings))
            return 1;
        if (settings & PHY_BMSR_LINK)
            break;
    }

#if MII_CHECK_TIMEOUT    
    if (timeout == MII_LINK_TIMEOUT || !(settings & PHY_BMSR_LINK))
        return 1;
    else
#endif      
        return 0;
}
/********************************************************************/
/*!
 * \brief   Get the auto-negotiated speed
 * \param   phy_addr    Address of the PHY
 * \param   speed       Pointer where speed data is stored
 * \return  0 if successful; non-zero otherwise
 */
int 
eth_phy_get_speed(int ch, int phy_addr, int *speed)
{
#if MII_CHECK_TIMEOUT
    int timeout;
#endif
    int settings = 0;

    /* Get Link Partner settings */
#if MII_CHECK_TIMEOUT
    for (timeout = 0; timeout < MII_TIMEOUT; ++timeout)
#endif
    while(1)
    {      
        if (mii_read(ch, phy_addr, PHY_ANLPAR, &settings))
            return 1;
        else
            break;
    }
#if MII_CHECK_TIMEOUT
    if (timeout == MII_TIMEOUT)
        return 1;
#endif
    
    settings &= eth_phy_anar;
    if (settings & PHY_ANLPAR_100BT4     ||
        settings & PHY_ANLPAR_100BTX_FDX ||
        settings & PHY_ANLPAR_100BTX)
        *speed = MII_100BASET;
    else
        *speed = MII_10BASET;

    return 0;
}
/********************************************************************/
/*!
 * \brief   Get the auto-negotiated duplex
 * \param   phy_addr    Address of the PHY
 * \param   speed       Pointer where speed data is stored
 * \return  0 if successful; non-zero otherwise
 */
int 
eth_phy_get_duplex(int ch, int phy_addr, int *speed)
{
#if MII_CHECK_TIMEOUT  
    int timeout;
#endif    
    int settings = 0;

    /* Get Link Partner settings */
#if MII_CHECK_TIMEOUT
    for (timeout = 0; timeout < MII_TIMEOUT; ++timeout)
#endif
    while(1)
    {
        if (mii_read(ch, phy_addr, PHY_ANLPAR, &settings))
            return 1;
        else
            break;
    }
#if MII_CHECK_TIMEOUT
    if (timeout == MII_TIMEOUT)
        return 1;
#endif
    
    settings &= eth_phy_anar;
    if (settings & PHY_ANLPAR_100BTX_FDX ||
        settings & PHY_ANLPAR_10BTX_FDX)
        *speed = MII_FDX;
    else
        *speed = MII_HDX;

    return 0;
}


/********************************************************************/
/*!
 * \brief   Get the manual speed
 * \param   phy_addr    Address of the PHY
 * \param   speed       Pointer where speed data is stored
 * \return  0 if successful; non-zero otherwise
 */
int 
eth_phy_get_manual_speed(int ch, int phy_addr, int *speed)
{
#if MII_CHECK_TIMEOUT
    int timeout;
#endif
    int settings = 0;

    /* Get Link Partner settings */
#if MII_CHECK_TIMEOUT
    for (timeout = 0; timeout < MII_TIMEOUT; ++timeout)
#endif
    while(1)
    {      
#ifdef TWR_K60N512 
        if (mii_read(ch, phy_addr, PHY_PHYCTRL2, &settings))//Micrel
#else
        if (mii_read(ch, phy_addr, PHY_PHYSTS, &settings))//National Semiconductors
#endif
            return 1;
        else
            break;
    }
#if MII_CHECK_TIMEOUT
    if (timeout == MII_TIMEOUT)
        return 1;
#endif

#ifdef TWR_K60N512
    /*FSL: obtain speed/duplex*/
    settings = (settings & PHY_PHYCTRL2_OP_MOD_MASK)>>PHY_PHYCTRL2_OP_MOD_SHIFT;
    
    if (settings == PHY_PHYCTRL2_MODE_OP_MOD_10MBPS_HD     ||
        settings == PHY_PHYCTRL2_MODE_OP_MOD_10MBPS_FD)
        *speed = MII_10BASET;
    else
        *speed = MII_100BASET;
#else
    if (settings & PHY_PHYSTS_SPEEDSTATUS)
        *speed = MII_10BASET;
    else
        *speed = MII_100BASET;    
#endif
    
    return 0;
}
/********************************************************************/
/*!
 * \brief   Get the manual duplex
 * \param   phy_addr    Address of the PHY
 * \param   duplex       Pointer where duplex data is stored
 * \return  0 if successful; non-zero otherwise
 */
int 
eth_phy_get_manual_duplex(int ch, int phy_addr, int *duplex)
{
#if MII_CHECK_TIMEOUT  
    int timeout;
#endif    
    int settings = 0;

    /* Get Link Partner settings */
#if MII_CHECK_TIMEOUT
    for (timeout = 0; timeout < MII_TIMEOUT; ++timeout)
#endif
    while(1)
    {
#ifdef TWR_K60N512 
        if (mii_read(ch, phy_addr, PHY_PHYCTRL2, &settings))//Micrel
#else
        if (mii_read(ch, phy_addr, PHY_PHYSTS, &settings))//National Semiconductors
#endif
            return 1;
        else
            break;
    }
#if MII_CHECK_TIMEOUT
    if (timeout == MII_TIMEOUT)
        return 1;
#endif

#ifdef TWR_K60N512    
    /*FSL: obtain speed/duplex*/
    settings = (settings & PHY_PHYCTRL2_OP_MOD_MASK)>>PHY_PHYCTRL2_OP_MOD_SHIFT;
    
    if (settings == PHY_PHYCTRL2_MODE_OP_MOD_10MBPS_HD     ||
        settings == PHY_PHYCTRL2_MODE_OP_MOD_100MBPS_HD)
        *duplex = MII_HDX;
    else
        *duplex = MII_FDX;
#else
    if (settings & PHY_PHYSTS_DUPLEXSTATUS)
        *duplex = MII_FDX;
    else
        *duplex = MII_HDX;
#endif

    return 0;
}

/********************************************************************/
/*!
 * \brief   Get the manual speed
 * \param   phy_addr    Address of the PHY
 * \param   loop        set if loopback is needed
 * \return  0 if successful; non-zero otherwise
 */
int 
eth_phy_set_remote_loopback(int ch, int phy_addr, int loop)
{
#if MII_CHECK_TIMEOUT
    int timeout;
#endif
    int settings = 0;

    /* Get Link Partner settings */
#if MII_CHECK_TIMEOUT
    for (timeout = 0; timeout < MII_TIMEOUT; ++timeout)
#endif
    while(1)
    {      
        if (mii_read(ch, phy_addr, PHY_PHYCTRL1, &settings))
            return 1;
        else
            break;
    }
#if MII_CHECK_TIMEOUT
    if (timeout == MII_TIMEOUT)
        return 1;
#endif
    /*set remote loopback flag*/
    if(loop)
      settings |= PHY_PHYCTRL1_REMOTE_LOOP; /*set bit*/
    else      
      settings &= ~PHY_PHYCTRL1_REMOTE_LOOP; /*clear bit*/
    
    if (mii_write(ch, phy_addr, PHY_PHYCTRL1, settings))
        return 1;

    return 0;
}

/********************************************************************/
/*!
 * \brief   Print all the MII registers (0x00-0x1F)
 * \param   phy_addr    Address of the PHY
 */
int 
eth_phy_reg_dump(int ch, int phy_addr)
{
    int j, settings;
    
    printf("\n    MII Register Block\n");
    printf("--------------------------------");
    for (j = 0; j < 32; j++)
    {
        mii_read(ch, phy_addr, j, &settings);
        if (!(j % 4))
            printf("\n0x%02X-0x%02X : %04X ", j, j + 3, settings);
        else
            printf("%04X ", settings);
    }
    printf("\n");
    
    return 0;
}
