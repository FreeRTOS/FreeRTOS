/**
 *  \file   emac_phyConfig.h
 *
 *  \brief  PHY Configuration file for selecting and configuring the required PHY.
 *
 *   This file contains the mappings of the PHY APIs so that the right one is chosen based
 * on the user's preference.
 */

/* (c) Texas Instruments 2009-2014, All rights reserved. */

#ifndef _EMAC_PHYCONFIG_H_
#define _EMAC_PHYCONFIG_H_

/* USER CODE BEGIN (0) */
/* USER CODE END */

#include "phy_dp83640.h"

/* USER CODE BEGIN (1) */
/* USER CODE END */

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (2) */
/* USER CODE END */

#define PhyIDGet             Dp83640IDGet
#define PhyLinkStatusGet     Dp83640LinkStatusGet
#define PhyAutoNegotiate     Dp83640AutoNegotiate
#define PhyPartnerAbilityGet Dp83640PartnerAbilityGet
#define PhyReset             Dp83640Reset
#define PhyEnableLoopback    Dp83640EnableLoopback
#define PhyDisableLoopback   Dp83640DisableLoopback
#define PhyGetTimeStamp      Dp83640GetTimeStamp
#define PhyPartnerSpdGet     Dp83640PartnerSpdGet

#ifdef __cplusplus
}
#endif

/**@}*/
#endif /* _EMAC_PHYCONFIG_H_ */
