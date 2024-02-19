/*
 * Tlk111.h
 */

/* Copyright (C) 2010 Texas Instruments Incorporated - www.ti.com
 * ALL RIGHTS RESERVED
 */

#ifndef _PHY_TLK111_H_
#define _PHY_TLK111_H_

#ifdef __cplusplus
extern "C" {
#endif

/** @enum PHY_timestamp
 *   @brief Alias names for transmit and receive timestamps
 *   This enumeration is used to provide alias names for getting the transmit and receive
 * timestamps from the Tlk111GetTimeStamp API.
 */
typedef enum phyTimeStamp
{
    Txtimestamp = 1, /*Transmit Timestamp*/
    Rxtimestamp = 2  /*Receive Timestamp */
} phyTimeStamp_t;
/* PHY register offset definitions */
#define PHY_BCR                        ( 0u )
#define PHY_BSR                        ( 1u )
#define PHY_ID1                        ( 2u )
#define PHY_ID2                        ( 3u )
#define PHY_AUTONEG_ADV                ( 4u )
#define PHY_LINK_PARTNER_ABLTY         ( 5u )
#define PHY_LINK_PARTNER_SPD           ( 16u )
#define PHY_SWSCR1                     ( 9u )
#define PHY_SWSCR2                     ( 10u )
#define PHY_SWSCR3                     ( 11u )
#define PHY_TXTS                       ( 28u )
#define PHY_RXTS                       ( 29u )

/* PHY status definitions */
#define PHY_ID_SHIFT                   ( 16u )
#define PHY_SOFTRESET                  ( 0x8000U )
#define PHY_AUTONEG_ENABLE             ( 0x1000u )
#define PHY_AUTONEG_RESTART            ( 0x0200u )
#define PHY_AUTONEG_COMPLETE           ( 0x0020u )
#define PHY_AUTONEG_INCOMPLETE         ( 0x0000u )
#define PHY_AUTONEG_STATUS             ( 0x0020u )
#define PHY_AUTONEG_ABLE               ( 0x0008u )
#define PHY_LPBK_ENABLE                ( 0x4000u )
#define PHY_LINK_STATUS                ( 0x0004u )
#define PHY_INVALID_TYPE               ( 0x0u )

/* PHY ID. The LSB nibble will vary between different phy revisions */
#define Tlk111_PHY_ID                  ( 0x2000A212 )
#define Tlk111_PHY_ID_REV_MASK         ( 0x0000000Fu )
#define Tlk111_PHY_ID_OUI              ( 0x2000A000 )
#define Tlk111_PHY_ID_OUI_MASK         ( 0xFFFFFC00 )

/* Pause operations */
#define Tlk111_PAUSE_NIL               ( 0x0000u )
#define Tlk111_PAUSE_SYM               ( 0x0400u )
#define Tlk111_PAUSE_ASYM              ( 0x0800u )
#define Tlk111_PAUSE_BOTH_SYM_ASYM     ( 0x0C00u )

/* 100 Base TX Full Duplex capablity */
#define Tlk111_100BTX_HD               ( 0x0000u )
#define Tlk111_100BTX_FD               ( 0x0100u )

/* 100 Base TX capability */
#define Tlk111_NO_100BTX               ( 0x0000u )
#define Tlk111_100BTX                  ( 0x0080u )

/* 10 BaseT duplex capabilities */
#define Tlk111_10BT_HD                 ( 0x0000u )
#define Tlk111_10BT_FD                 ( 0x0040u )

/* 10 BaseT ability*/
#define Tlk111_NO_10BT                 ( 0x0000u )
#define Tlk111_10BT                    ( 0x0020u )

/* Software Strap Register 1 */
#define Tlk111_SWStrapDone             ( 1u << 15 )
#define Tlk111_Auto_MDIX_Ena           ( 1u << 14 )
#define Tlk111_Auto_Neg_Ena            ( 1u << 13 )
#define Tlk111_Auto_AnMode_10BT_HD     ( 0u << 11 )
#define Tlk111_Auto_AnMode_10BT_FD     ( 1u << 11 )
#define Tlk111_Auto_AnMode_100BT_HD    ( 2u << 11 )
#define Tlk111_Auto_AnMode_100BT_FD    ( 3u << 11 )
#define Tlk111_Force_LEDMode1          ( 1u << 10 )
#define Tlk111_RMII_Enhanced           ( 1u << 9 )
#define Tlk111_TDR_AutoRun             ( 1u << 8 )
#define Tlk111_LinkLoss_Recovery       ( 1u << 8 )
#define Tlk111_FastAutoMdix            ( 1u << 6 )
#define Tlk111_RobustAutoMdix          ( 1u << 5 )
#define Tlk111_FastAnEn                ( 1u << 4 )
#define Tlk111_FastAnSel0              ( 0u << 2 )
#define Tlk111_FastAnSel1              ( 1u << 2 )
#define Tlk111_FastAnSel2              ( 2u << 2 )
#define Tlk111_FastRxDvDetect          ( 1u << 1 )
#define Tlk111_IntPdn_InterruptOut     ( 1u << 0 )

/* Software Strap Register 2 */
#define Tlk111_100BT_Force_FE_LinkDrop ( 1u << 15 )
#define Tlk111_Rsv1                    ( 2u << 7 )
#define Tlk111_FastLinkUpParallel      ( 1u << 6 )
#define Tlk111_ExtendedFDAbility       ( 1u << 5 )
#define Tlk111_ExtendedLEDLink         ( 1u << 4 )
#define Tlk111_IsolateMII_100BT_HD     ( 1u << 3 )
#define Tlk111_RXERR_DuringIdle        ( 1u << 2 )
#define Tlk111_OddNibbleDetectDisable  ( 1u << 1 )
#define Tlk111_RMII_Use_RXCLK          ( 1u << 0 )
#define Tlk111_RMII_Use_XI             ( 0u << 0 )

/* Software Strap Register 2 */
#define Tlk111_FastLinkDown            ( 1u << 10 )
#define Tlk111_PolaritySwap            ( 1u << 6 )
#define Tlk111_MDIXSwap                ( 1u << 5 )
#define Tlk111_Bypass4B5B              ( 1u << 4 )
#define Tlk111_FastLinkDownRxErrCnt    ( 1u << 3 )
#define Tlk111_FastLinkDownMLT3ErrCnt  ( 1u << 2 )
#define Tlk111_FastLinkDownLowSnr      ( 1u << 1 )
#define Tlk111_FastLinkDownSigLoss     ( 1u << 0 )

/* The Values for SWSCR Registers */
#define Tlk111_SWSCR1_Val                                                      \
    ( Tlk111_Auto_MDIX_Ena | Tlk111_Auto_Neg_Ena | Tlk111_Auto_AnMode_100BT_FD \
      | Tlk111_Force_LEDMode1 | Tlk111_IntPdn_InterruptOut )
#define Tlk111_SWSCR2_Val ( Tlk111_Rsv1 | Tlk111_RXERR_DuringIdle )
#define Tlk111_SWSCR3_Val ( 0u )

/**************************************************************************
                        API function Prototypes
***************************************************************************/
extern uint32 Tlk111IDGet( uint32 mdioBaseAddr, uint32 phyAddr );
extern void Tlk111SwStrap( uint32 mdioBaseAddr, uint32 phyAddr );
extern void Tlk111Reset( uint32 mdioBaseAddr, uint32 phyAddr );
extern boolean Tlk111AutoNegotiate( uint32 mdioBaseAddr, uint32 phyAddr, uint16 advVal );
extern boolean Tlk111PartnerAbilityGet( uint32 mdioBaseAddr,
                                        uint32 phyAddr,
                                        uint16 * ptnerAblty );
extern boolean Tlk111LinkStatusGet( uint32 mdioBaseAddr,
                                    uint32 phyAddr,
                                    volatile uint32 retries );
extern uint64 Tlk111GetTimeStamp( uint32 mdioBaseAddr,
                                  uint32 phyAddr,
                                  phyTimeStamp_t type );
extern void Tlk111EnableLoopback( uint32 mdioBaseAddr, uint32 phyAddr );
extern void Tlk111DisableLoopback( uint32 mdioBaseAddr, uint32 phyAddr );
extern boolean Tlk111PartnerSpdGet( uint32 mdioBaseAddr,
                                    uint32 phyAddr,
                                    uint16 * ptnerAblty );

#ifdef __cplusplus
}
#endif
#endif
