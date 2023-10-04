/**************************************************************************//**
 * @file     epwm.h
 * @version  V3.00
 * @brief    M2351 series EPWM driver header file
 *
 * @note
 * Copyright (C) 2017 Nuvoton Technology Corp. All rights reserved.
 *****************************************************************************/
#ifndef __EPWM_H__
    #define __EPWM_H__

    #ifdef __cplusplus
        extern "C"
        {
    #endif


/** @addtogroup Standard_Driver Standard Driver
 * @{
 */

/** @addtogroup EPWM_Driver EPWM Driver
 * @{
 */

/** @addtogroup EPWM_EXPORTED_CONSTANTS EPWM Exported Constants
 * @{
 */
    #define EPWM_CHANNEL_NUM    ( 6UL )                      /*!< EPWM channel number */
    #define EPWM_CH_0_MASK      ( 0x1UL )                    /*!< EPWM channel 0 mask \hideinitializer */
    #define EPWM_CH_1_MASK      ( 0x2UL )                    /*!< EPWM channel 1 mask \hideinitializer */
    #define EPWM_CH_2_MASK      ( 0x4UL )                    /*!< EPWM channel 2 mask \hideinitializer */
    #define EPWM_CH_3_MASK      ( 0x8UL )                    /*!< EPWM channel 3 mask \hideinitializer */
    #define EPWM_CH_4_MASK      ( 0x10UL )                   /*!< EPWM channel 4 mask \hideinitializer */
    #define EPWM_CH_5_MASK      ( 0x20UL )                   /*!< EPWM channel 5 mask \hideinitializer */

/*---------------------------------------------------------------------------------------------------------*/
/*  Counter Type Constant Definitions                                                                      */
/*---------------------------------------------------------------------------------------------------------*/
    #define EPWM_UP_COUNTER         ( 0UL )                  /*!< Up counter type */
    #define EPWM_DOWN_COUNTER       ( 1UL )                  /*!< Down counter type */
    #define EPWM_UP_DOWN_COUNTER    ( 2UL )                  /*!< Up-Down counter type */

/*---------------------------------------------------------------------------------------------------------*/
/*  Aligned Type Constant Definitions                                                                      */
/*---------------------------------------------------------------------------------------------------------*/
    #define EPWM_EDGE_ALIGNED      ( 1UL )                   /*!< EPWM working in edge aligned type(down count) */
    #define EPWM_CENTER_ALIGNED    ( 2UL )                   /*!< EPWM working in center aligned type */

/*---------------------------------------------------------------------------------------------------------*/
/*  Output Level Constant Definitions                                                                      */
/*---------------------------------------------------------------------------------------------------------*/
    #define EPWM_OUTPUT_NOTHING    ( 0UL )                   /*!< EPWM output nothing */
    #define EPWM_OUTPUT_LOW        ( 1UL )                   /*!< EPWM output low */
    #define EPWM_OUTPUT_HIGH       ( 2UL )                   /*!< EPWM output high */
    #define EPWM_OUTPUT_TOGGLE     ( 3UL )                   /*!< EPWM output toggle */

/*---------------------------------------------------------------------------------------------------------*/
/*  Synchronous Start Function Control Constant Definitions                                                */
/*---------------------------------------------------------------------------------------------------------*/
    #define EPWM_SSCTL_SSRC_EPWM0    ( 0UL << EPWM_SSCTL_SSRC_Pos )             /*!< Synchronous start source comes from EPWM0 */
    #define EPWM_SSCTL_SSRC_EPWM1    ( 1UL << EPWM_SSCTL_SSRC_Pos )             /*!< Synchronous start source comes from EPWM1  */
    #define EPWM_SSCTL_SSRC_BPWM0    ( 2UL << EPWM_SSCTL_SSRC_Pos )             /*!< Synchronous start source comes from BPWM0 */
    #define EPWM_SSCTL_SSRC_BPWM1    ( 3UL << EPWM_SSCTL_SSRC_Pos )             /*!< Synchronous start source comes from BPWM1 */

/*---------------------------------------------------------------------------------------------------------*/
/*  Trigger Source Select Constant Definitions                                                             */
/*---------------------------------------------------------------------------------------------------------*/
    #define EPWM_TRG_ADC_EVEN_ZERO             ( 0UL )         /*!< EPWM trigger ADC while counter of even channel matches zero point */
    #define EPWM_TRG_ADC_EVEN_PERIOD           ( 1UL )         /*!< EPWM trigger ADC while counter of even channel matches period point */
    #define EPWM_TRG_ADC_EVEN_ZERO_PERIOD      ( 2UL )         /*!< EPWM trigger ADC while counter of even channel matches zero or period point */
    #define EPWM_TRG_ADC_EVEN_COMPARE_UP       ( 3UL )         /*!< EPWM trigger ADC while counter of even channel matches up count to comparator point */
    #define EPWM_TRG_ADC_EVEN_COMPARE_DOWN     ( 4UL )         /*!< EPWM trigger ADC while counter of even channel matches down count to comparator point */
    #define EPWM_TRG_ADC_ODD_ZERO              ( 5UL )         /*!< EPWM trigger ADC while counter of odd channel matches zero point */
    #define EPWM_TRG_ADC_ODD_PERIOD            ( 6UL )         /*!< EPWM trigger ADC while counter of odd channel matches period point */
    #define EPWM_TRG_ADC_ODD_ZERO_PERIOD       ( 7UL )         /*!< EPWM trigger ADC while counter of odd channel matches zero or period point */
    #define EPWM_TRG_ADC_ODD_COMPARE_UP        ( 8UL )         /*!< EPWM trigger ADC while counter of odd channel matches up count to comparator point */
    #define EPWM_TRG_ADC_ODD_COMPARE_DOWN      ( 9UL )         /*!< EPWM trigger ADC while counter of odd channel matches down count to comparator point */
    #define EPWM_TRG_ADC_CH_0_FREE_CMP_UP      ( 10UL )        /*!< EPWM trigger ADC while counter of channel 0 matches up count to free comparator point */
    #define EPWM_TRG_ADC_CH_0_FREE_CMP_DOWN    ( 11UL )        /*!< EPWM trigger ADC while counter of channel 0 matches down count to free comparator point */
    #define EPWM_TRG_ADC_CH_2_FREE_CMP_UP      ( 12UL )        /*!< EPWM trigger ADC while counter of channel 2 matches up count to free comparator point */
    #define EPWM_TRG_ADC_CH_2_FREE_CMP_DOWN    ( 13UL )        /*!< EPWM trigger ADC while counter of channel 2 matches down count to free comparator point */
    #define EPWM_TRG_ADC_CH_4_FREE_CMP_UP      ( 14UL )        /*!< EPWM trigger ADC while counter of channel 4 matches up count to free comparator point */
    #define EPWM_TRG_ADC_CH_4_FREE_CMP_DOWN    ( 15UL )        /*!< EPWM trigger ADC while counter of channel 4 matches down count to free comparator point */

    #define EPWM_TRIGGER_DAC_ZERO              ( 0x1UL )       /*!< EPWM trigger DAC while counter down count to 0  \hideinitializer */
    #define EPWM_TRIGGER_DAC_PERIOD            ( 0x100UL )     /*!< EPWM trigger DAC while counter matches (PERIOD + 1) \hideinitializer */
    #define EPWM_TRIGGER_DAC_COMPARE_UP        ( 0x10000UL )   /*!< EPWM trigger DAC while counter up count to CMPDAT \hideinitializer */
    #define EPWM_TRIGGER_DAC_COMPARE_DOWN      ( 0x1000000UL ) /*!< EPWM trigger DAC while counter down count to CMPDAT \hideinitializer */

/*---------------------------------------------------------------------------------------------------------*/
/*  Fail brake Control Constant Definitions                                                                */
/*---------------------------------------------------------------------------------------------------------*/
    #define EPWM_FB_EDGE_ACMP0       ( EPWM_BRKCTL0_1_CPO0EBEN_Msk )                            /*!< Comparator 0 as edge-detect fault brake source */
    #define EPWM_FB_EDGE_ACMP1       ( EPWM_BRKCTL0_1_CPO1EBEN_Msk )                            /*!< Comparator 1 as edge-detect fault brake source */
    #define EPWM_FB_EDGE_BKP0        ( EPWM_BRKCTL0_1_BRKP0EEN_Msk )                            /*!< BKP0 pin as edge-detect fault brake source */
    #define EPWM_FB_EDGE_BKP1        ( EPWM_BRKCTL0_1_BRKP1EEN_Msk )                            /*!< BKP1 pin as edge-detect fault brake source */
    #define EPWM_FB_EDGE_ADCRM       ( EPWM_BRKCTL0_1_EADCEBEN_Msk )                            /*!< ADC Result Monitor (ADCRM) as edge-detect fault brake source */
    #define EPWM_FB_EDGE_SYS_CSS     ( EPWM_BRKCTL0_1_SYSEBEN_Msk | EPWM_FAILBRK_CSSBRKEN_Msk ) /*!< System fail condition: clock security system detection as edge-detect fault brake source */
    #define EPWM_FB_EDGE_SYS_BOD     ( EPWM_BRKCTL0_1_SYSEBEN_Msk | EPWM_FAILBRK_BODBRKEN_Msk ) /*!< System fail condition: brown-out detection as edge-detect fault brake source */
    #define EPWM_FB_EDGE_SYS_RAM     ( EPWM_BRKCTL0_1_SYSEBEN_Msk | EPWM_FAILBRK_RAMBRKEN_Msk ) /*!< System fail condition: SRAM parity error detection as edge-detect fault brake source */
    #define EPWM_FB_EDGE_SYS_COR     ( EPWM_BRKCTL0_1_SYSEBEN_Msk | EPWM_FAILBRK_CORBRKEN_Msk ) /*!< System fail condition: core lockup detection as edge-detect fault brake source */

    #define EPWM_FB_LEVEL_ACMP0      ( EPWM_BRKCTL0_1_CPO0LBEN_Msk )                            /*!< Comparator 0 as level-detect fault brake source */
    #define EPWM_FB_LEVEL_ACMP1      ( EPWM_BRKCTL0_1_CPO1LBEN_Msk )                            /*!< Comparator 1 as level-detect fault brake source */
    #define EPWM_FB_LEVEL_BKP0       ( EPWM_BRKCTL0_1_BRKP0LEN_Msk )                            /*!< BKP0 pin as level-detect fault brake source */
    #define EPWM_FB_LEVEL_BKP1       ( EPWM_BRKCTL0_1_BRKP1LEN_Msk )                            /*!< BKP1 pin as level-detect fault brake source */
    #define EPWM_FB_LEVEL_ADCRM      ( EPWM_BRKCTL0_1_EADCLBEN_Msk )                            /*!< ADC Result Monitor (ADCRM) as level-detect fault brake source */
    #define EPWM_FB_LEVEL_SYS_CSS    ( EPWM_BRKCTL0_1_SYSLBEN_Msk | EPWM_FAILBRK_CSSBRKEN_Msk ) /*!< System fail condition: clock security system detection as level-detect fault brake source */
    #define EPWM_FB_LEVEL_SYS_BOD    ( EPWM_BRKCTL0_1_SYSLBEN_Msk | EPWM_FAILBRK_BODBRKEN_Msk ) /*!< System fail condition: brown-out detection as level-detect fault brake source */
    #define EPWM_FB_LEVEL_SYS_RAM    ( EPWM_BRKCTL0_1_SYSLBEN_Msk | EPWM_FAILBRK_RAMBRKEN_Msk ) /*!< System fail condition: SRAM parity error detection as level-detect fault brake source */
    #define EPWM_FB_LEVEL_SYS_COR    ( EPWM_BRKCTL0_1_SYSLBEN_Msk | EPWM_FAILBRK_CORBRKEN_Msk ) /*!< System fail condition: core lockup detection as level-detect fault brake source */

    #define EPWM_FB_EDGE             ( 0UL )                                                    /*!< edge-detect fault brake */
    #define EPWM_FB_LEVEL            ( 8UL )                                                    /*!< level-detect fault brake */

/*---------------------------------------------------------------------------------------------------------*/
/*  Leading Edge Blanking Control Constant Definitions                                                     */
/*---------------------------------------------------------------------------------------------------------*/
    #define EPWM_LEBCTL_TRGTYPE_RISING               ( 0UL << EPWM_LEBCTL_TRGTYPE_Pos )                                           /*!< EPWM Leading Edge Blanking Trigger Type Is Rising Edge \hideinitializer */
    #define EPWM_LEBCTL_TRGTYPE_FALLING              ( 1UL << EPWM_LEBCTL_TRGTYPE_Pos )                                           /*!< EPWM Leading Edge Blanking Trigger Type Is Falling Edge \hideinitializer */
    #define EPWM_LEBCTL_TRGTYPE_RISING_OR_FALLING    ( 2UL << EPWM_LEBCTL_TRGTYPE_Pos )                                           /*!< EPWM Leading Edge Blanking Trigger Type Is Rising or Falling Edge \hideinitializer */
    #define EPWM_LEBCTL_SRCEN0                       ( EPWM_LEBCTL_SRCEN0_Msk )                                                   /*!< EPWM Leading Edge Blanking Source From EPWMx_CH0 Enable \hideinitializer */
    #define EPWM_LEBCTL_SRCEN2                       ( EPWM_LEBCTL_SRCEN2_Msk )                                                   /*!< EPWM Leading Edge Blanking Source From EPWMx_CH2 Enable \hideinitializer */
    #define EPWM_LEBCTL_SRCEN4                       ( EPWM_LEBCTL_SRCEN4_Msk )                                                   /*!< EPWM Leading Edge Blanking Source From EPWMx_CH4 Enable \hideinitializer */
    #define EPWM_LEBCTL_SRCEN0_2                     ( EPWM_LEBCTL_SRCEN0_Msk | EPWM_LEBCTL_SRCEN2_Msk )                          /*!< EPWM Leading Edge Blanking Source From EPWMx_CH0 and EPWMx_CH2 Enable \hideinitializer */
    #define EPWM_LEBCTL_SRCEN0_4                     ( EPWM_LEBCTL_SRCEN0_Msk | EPWM_LEBCTL_SRCEN4_Msk )                          /*!< EPWM Leading Edge Blanking Source From EPWMx_CH0 and EPWMx_CH4 Enable \hideinitializer */
    #define EPWM_LEBCTL_SRCEN2_4                     ( EPWM_LEBCTL_SRCEN2_Msk | EPWM_LEBCTL_SRCEN4_Msk )                          /*!< EPWM Leading Edge Blanking Source From EPWMx_CH2 and EPWMx_CH4 Enable \hideinitializer */
    #define EPWM_LEBCTL_SRCEN0_2_4                   ( EPWM_LEBCTL_SRCEN0_Msk | EPWM_LEBCTL_SRCEN2_Msk | EPWM_LEBCTL_SRCEN4_Msk ) /*!< EPWM Leading Edge Blanking Source From EPWMx_CH0, EPWMx_CH2 and EPWMx_CH4 Enable \hideinitializer */

/*---------------------------------------------------------------------------------------------------------*/
/*  Capture Control Constant Definitions                                                                   */
/*---------------------------------------------------------------------------------------------------------*/
    #define EPWM_CAPTURE_INT_RISING_LATCH             ( 1UL )     /*!< EPWM capture interrupt if channel has rising transition */
    #define EPWM_CAPTURE_INT_FALLING_LATCH            ( 0x100UL ) /*!< EPWM capture interrupt if channel has falling transition */

    #define EPWM_CAPTURE_PDMA_RISING_LATCH            ( 0x2UL )   /*!< EPWM capture rising latched data transfer by PDMA */
    #define EPWM_CAPTURE_PDMA_FALLING_LATCH           ( 0x4UL )   /*!< EPWM capture falling latched data transfer by PDMA */
    #define EPWM_CAPTURE_PDMA_RISING_FALLING_LATCH    ( 0x6UL )   /*!< EPWM capture rising and falling latched data transfer by PDMA */

/*---------------------------------------------------------------------------------------------------------*/
/*  Duty Interrupt Type Constant Definitions                                                               */
/*---------------------------------------------------------------------------------------------------------*/
    #define EPWM_DUTY_INT_DOWN_COUNT_MATCH_CMP    ( EPWM_INTEN0_CMPDIEN0_Msk ) /*!< EPWM duty interrupt triggered if down count match comparator */
    #define EPWM_DUTY_INT_UP_COUNT_MATCH_CMP      ( EPWM_INTEN0_CMPUIEN0_Msk ) /*!< EPWM duty interrupt triggered if up down match comparator */

/*---------------------------------------------------------------------------------------------------------*/
/*  Interrupt Flag Accumulator Constant Definitions                                                        */
/*---------------------------------------------------------------------------------------------------------*/
    #define EPWM_IFA_ZERO_POINT                  ( 0UL )   /*!< EPWM counter equal to zero */
    #define EPWM_IFA_PERIOD_POINT                ( 1UL )   /*!< EPWM counter equal to period */
    #define EPWM_IFA_COMPARE_UP_COUNT_POINT      ( 2UL )   /*!< EPWM counter up count to comparator value */
    #define EPWM_IFA_COMPARE_DOWN_COUNT_POINT    ( 3UL )   /*!< EPWM counter down count to comparator value */

/*---------------------------------------------------------------------------------------------------------*/
/*  Load Mode Constant Definitions                                                                         */
/*---------------------------------------------------------------------------------------------------------*/
    #define EPWM_LOAD_MODE_IMMEDIATE    ( EPWM_CTL0_IMMLDEN0_Msk )            /*!< EPWM immediately load mode \hideinitializer */
    #define EPWM_LOAD_MODE_WINDOW       ( EPWM_CTL0_WINLDEN0_Msk )            /*!< EPWM window load mode \hideinitializer */
    #define EPWM_LOAD_MODE_CENTER       ( EPWM_CTL0_CTRLD0_Msk )              /*!< EPWM center load mode \hideinitializer */

/*---------------------------------------------------------------------------------------------------------*/
/*  Synchronize Control Constant Definitions                                                               */
/*---------------------------------------------------------------------------------------------------------*/
    #define EPWM_SYNC_OUT_FROM_SYNCIN_SWSYNC          ( 0UL ) /*!< Synchronize source from SYNC_IN or SWSYNC  \hideinitializer */
    #define EPWM_SYNC_OUT_FROM_COUNT_TO_ZERO          ( 1UL ) /*!< Synchronize source from counter equal to 0  \hideinitializer */
    #define EPWM_SYNC_OUT_FROM_COUNT_TO_COMPARATOR    ( 2UL ) /*!< Synchronize source from counter equal to CMPDAT1, CMPDAT3, CMPDAT5 \hideinitializer */
    #define EPWM_SYNC_OUT_DISABLE                     ( 3UL ) /*!< SYNC_OUT will not be generated \hideinitializer */
    #define EPWM_PHS_DIR_DECREMENT                    ( 0UL ) /*!< EPWM counter count decrement  \hideinitializer */
    #define EPWM_PHS_DIR_INCREMENT                    ( 1UL ) /*!< EPWM counter count increment  \hideinitializer */

/*---------------------------------------------------------------------------------------------------------*/
/*  Noise Filter Clock Divide Select Constant Definitions                                                  */
/*---------------------------------------------------------------------------------------------------------*/
    #define EPWM_NF_CLK_DIV_1      ( 0UL )                 /*!< Noise filter clock is HCLK divide by 1 \hideinitializer */
    #define EPWM_NF_CLK_DIV_2      ( 1UL )                 /*!< Noise filter clock is HCLK divide by 2 \hideinitializer */
    #define EPWM_NF_CLK_DIV_4      ( 2UL )                 /*!< Noise filter clock is HCLK divide by 4 \hideinitializer */
    #define EPWM_NF_CLK_DIV_8      ( 3UL )                 /*!< Noise filter clock is HCLK divide by 8 \hideinitializer */
    #define EPWM_NF_CLK_DIV_16     ( 4UL )                 /*!< Noise filter clock is HCLK divide by 16 \hideinitializer */
    #define EPWM_NF_CLK_DIV_32     ( 5UL )                 /*!< Noise filter clock is HCLK divide by 32 \hideinitializer */
    #define EPWM_NF_CLK_DIV_64     ( 6UL )                 /*!< Noise filter clock is HCLK divide by 64 \hideinitializer */
    #define EPWM_NF_CLK_DIV_128    ( 7UL )                 /*!< Noise filter clock is HCLK divide by 128 \hideinitializer */

/*---------------------------------------------------------------------------------------------------------*/
/*  Clock Source Select Constant Definitions                                                               */
/*---------------------------------------------------------------------------------------------------------*/
    #define EPWM_CLKSRC_EPWM_CLK    ( 0UL )                /*!< EPWM Clock source selects to EPWM0_CLK or EPWM1_CLK \hideinitializer */
    #define EPWM_CLKSRC_TIMER0      ( 1UL )                /*!< EPWM Clock source selects to TIMER0 overflow \hideinitializer */
    #define EPWM_CLKSRC_TIMER1      ( 2UL )                /*!< EPWM Clock source selects to TIMER1 overflow \hideinitializer */
    #define EPWM_CLKSRC_TIMER2      ( 3UL )                /*!< EPWM Clock source selects to TIMER2 overflow \hideinitializer */
    #define EPWM_CLKSRC_TIMER3      ( 4UL )                /*!< EPWM Clock source selects to TIMER3 overflow \hideinitializer */


/*@}*/ /* end of group EPWM_EXPORTED_CONSTANTS */


/** @addtogroup EPWM_EXPORTED_FUNCTIONS EPWM Exported Functions
 * @{
 */

/**
 * @brief This macro enable complementary mode
 * @param[in] epwm The pointer of the specified EPWM module
 * @return None
 * @details This macro is used to enable complementary mode of EPWM module.
 * \hideinitializer
 */
    #define EPWM_ENABLE_COMPLEMENTARY_MODE( epwm )                        ( ( epwm )->CTL1 = ( epwm )->CTL1 | ( 0x7ul << EPWM_CTL1_OUTMODE0_Pos ) )

/**
 * @brief This macro disable complementary mode, and enable independent mode.
 * @param[in] epwm The pointer of the specified EPWM module
 * @return None
 * @details This macro is used to disable complementary mode of EPWM module.
 * \hideinitializer
 */
    #define EPWM_DISABLE_COMPLEMENTARY_MODE( epwm )                       ( ( epwm )->CTL1 = ( epwm )->CTL1 & ~( 0x7ul << EPWM_CTL1_OUTMODE0_Pos ) )

/**
 * @brief This macro enable group mode
 * @param[in] epwm The pointer of the specified EPWM module
 * @return None
 * @details This macro is used to enable group mode of EPWM module.
 * \hideinitializer
 */
    #define EPWM_ENABLE_GROUP_MODE( epwm )                                ( ( epwm )->CTL0 = ( epwm )->CTL0 | EPWM_CTL0_GROUPEN_Msk )

/**
 * @brief This macro disable group mode
 * @param[in] epwm The pointer of the specified EPWM module
 * @return None
 * @details This macro is used to disable group mode of EPWM module.
 * \hideinitializer
 */
    #define EPWM_DISABLE_GROUP_MODE( epwm )                               ( ( epwm )->CTL0 = ( epwm )->CTL0 & ~EPWM_CTL0_GROUPEN_Msk )

/**
 * @brief Enable timer synchronous start counting function of specified channel(s)
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelMask Combination of enabled channels. Each bit corresponds to a channel
 *                           Bit 0 represents channel 0, bit 1 represents channel 1...
 * @param[in] u32SyncSrc Synchronous start source selection, valid values are:
 *              - \ref EPWM_SSCTL_SSRC_EPWM0
 *              - \ref EPWM_SSCTL_SSRC_EPWM1
 *              - \ref EPWM_SSCTL_SSRC_BPWM0
 *              - \ref EPWM_SSCTL_SSRC_BPWM1
 * @return None
 * @details This macro is used to enable timer synchronous start counting function of specified channel(s).
 * \hideinitializer
 */
    #define EPWM_ENABLE_TIMER_SYNC( epwm, u32ChannelMask, u32SyncSrc )    ( ( epwm )->SSCTL = ( ( epwm )->SSCTL & ~EPWM_SSCTL_SSRC_Msk ) | ( u32SyncSrc ) | ( u32ChannelMask ) )

/**
 * @brief Disable timer synchronous start counting function of specified channel(s)
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelMask Combination of enabled channels. Each bit corresponds to a channel
 *                           Bit 0 represents channel 0, bit 1 represents channel 1...
 * @return None
 * @details This macro is used to disable timer synchronous start counting function of specified channel(s).
 * \hideinitializer
 */
    #define EPWM_DISABLE_TIMER_SYNC( epwm, u32ChannelMask ) \
    do {                                                    \
        int i;                                              \
        for( i = 0; i < 6; i++ ) {                          \
            if( ( u32ChannelMask ) & ( 1UL << i ) )         \
            {                                               \
                ( epwm )->SSCTL &= ~( 1UL << i );           \
            }                                               \
        }                                                   \
    } while( 0 )

/**
 * @brief This macro enable EPWM counter synchronous start counting function.
 * @param[in] epwm The pointer of the specified EPWM module
 * @return None
 * @details This macro is used to make selected EPWM0 and EPWM1 channel(s) start counting at the same time.
 *          To configure synchronous start counting channel(s) by EPWM_ENABLE_TIMER_SYNC() and EPWM_DISABLE_TIMER_SYNC().
 * \hideinitializer
 */
    #define EPWM_TRIGGER_SYNC_START( epwm )                         ( ( epwm )->SSTRG = EPWM_SSTRG_CNTSEN_Msk )

/**
 * @brief This macro enable output inverter of specified channel(s)
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelMask Combination of enabled channels. Each bit corresponds to a channel
 *                           Bit 0 represents channel 0, bit 1 represents channel 1...
 * @return None
 * @details This macro is used to enable output inverter of specified channel(s).
 * \hideinitializer
 */
    #define EPWM_ENABLE_OUTPUT_INVERTER( epwm, u32ChannelMask )     ( ( epwm )->POLCTL = ( u32ChannelMask ) )

/**
 * @brief This macro get captured rising data
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelNum EPWM channel number. Valid values are between 0~5
 * @return None
 * @details This macro is used to get captured rising data of specified channel.
 * \hideinitializer
 */
    #define EPWM_GET_CAPTURE_RISING_DATA( epwm, u32ChannelNum )     ( ( epwm )->CAPDAT[ ( u32ChannelNum ) ].RCAPDAT )

/**
 * @brief This macro get captured falling data
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelNum EPWM channel number. Valid values are between 0~5
 * @return None
 * @details This macro is used to get captured falling data of specified channel.
 * \hideinitializer
 */
    #define EPWM_GET_CAPTURE_FALLING_DATA( epwm, u32ChannelNum )    ( ( epwm )->CAPDAT[ ( u32ChannelNum ) ].FCAPDAT )

/**
 * @brief This macro mask output logic to high or low
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelMask Combination of enabled channels. Each bit corresponds to a channel
 *                           Bit 0 represents channel 0, bit 1 represents channel 1...
 * @param[in] u32LevelMask Output logic to high or low
 * @return None
 * @details This macro is used to mask output logic to high or low of specified channel(s).
 * @note If u32ChannelMask parameter is 0, then mask function will be disabled.
 * \hideinitializer
 */
    #define EPWM_MASK_OUTPUT( epwm, u32ChannelMask, u32LevelMask ) \
    do {                                                           \
        ( epwm )->MSKEN = ( u32ChannelMask );                      \
        ( epwm )->MSK = ( u32LevelMask );                          \
    } while( 0 )

/**
 * @brief This macro set the prescaler of the selected channel
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelNum EPWM channel number. Valid values are between 0~5
 * @param[in] u32Prescaler Clock prescaler of specified channel. Valid values are between 0 ~ 0xFFF
 * @return None
 * @details This macro is used to set the prescaler of specified channel.
 * @note Every even channel N, and channel (N + 1) share a prescaler. So if channel 0 prescaler changed, channel 1 will also be affected.
 *       The clock of EPWM counter is divided by (u32Prescaler + 1).
 * \hideinitializer
 */
    #define EPWM_SET_PRESCALER( epwm, u32ChannelNum, u32Prescaler )    ( ( epwm )->CLKPSC[ ( u32ChannelNum ) >> 1 ] = ( u32Prescaler ) )

/**
 * @brief This macro get the prescaler of the selected channel
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelNum EPWM channel number. Valid values are between 0~5
 * @return Return Clock prescaler of specified channel. Valid values are between 0 ~ 0xFFF
 * @details This macro is used to get the prescaler of specified channel.
 * @note Every even channel N, and channel (N + 1) share a prescaler. So if channel 0 prescaler changed, channel 1 will also be affected.
 *       The clock of EPWM counter is divided by (u32Prescaler + 1).
 * \hideinitializer
 */
    #define EPWM_GET_PRESCALER( epwm, u32ChannelNum )                  ( ( epwm )->CLKPSC[ ( u32ChannelNum ) >> 1U ] )

/**
 * @brief This macro set the comparator of the selected channel
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelNum EPWM channel number. Valid values are between 0~5
 * @param[in] u32CMR Comparator of specified channel. Valid values are between 0~0xFFFF
 * @return None
 * @details This macro is used to set the comparator of specified channel.
 * @note This new setting will take effect on next EPWM period.
 * \hideinitializer
 */
    #define EPWM_SET_CMR( epwm, u32ChannelNum, u32CMR )                ( ( epwm )->CMPDAT[ ( u32ChannelNum ) ] = ( u32CMR ) )

/**
 * @brief This macro get the comparator of the selected channel
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelNum EPWM channel number. Valid values are between 0~5
 * @return Return the comparator of specified channel. Valid values are between 0~0xFFFF
 * @details This macro is used to get the comparator of specified channel.
 * \hideinitializer
 */
    #define EPWM_GET_CMR( epwm, u32ChannelNum )                        ( ( epwm )->CMPDAT[ ( u32ChannelNum ) ] )

/**
 * @brief This macro set the free trigger comparator of the selected channel
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelNum EPWM channel number. Valid values are between 0~5
 * @param[in] u32FTCMR Free trigger comparator of specified channel. Valid values are between 0~0xFFFF
 * @return None
 * @details This macro is used to set the free trigger comparator of specified channel.
 * @note This new setting will take effect on next EPWM period.
 * \hideinitializer
 */
    #define EPWM_SET_FTCMR( epwm, u32ChannelNum, u32FTCMR )            ( ( ( epwm )->FTCMPDAT[ ( ( u32ChannelNum ) >> 1U ) ] ) = ( u32FTCMR ) )

/**
 * @brief This macro set the period of the selected channel
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelNum EPWM channel number. Valid values are between 0~5
 * @param[in] u32CNR Period of specified channel. Valid values are between 0~0xFFFF
 * @return None
 * @details This macro is used to set the period of specified channel.
 * @note This new setting will take effect on next EPWM period.
 * @note EPWM counter will stop if period length set to 0.
 * \hideinitializer
 */
    #define EPWM_SET_CNR( epwm, u32ChannelNum, u32CNR )                ( ( epwm )->PERIOD[ ( u32ChannelNum ) ] = ( u32CNR ) )

/**
 * @brief This macro get the period of the selected channel
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelNum EPWM channel number. Valid values are between 0~5
 * @return Return the period of specified channel. Valid values are between 0~0xFFFF
 * @details This macro is used to get the period of specified channel.
 * \hideinitializer
 */
    #define EPWM_GET_CNR( epwm, u32ChannelNum )                        ( ( epwm )->PERIOD[ ( u32ChannelNum ) ] )

/**
 * @brief This macro set the EPWM aligned type
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelMask Combination of enabled channels. Each bit corresponds to a channel
 *                           Bit 0 represents channel 0, bit 1 represents channel 1...
 * @param[in] u32AlignedType EPWM aligned type, valid values are:
 *              - \ref EPWM_EDGE_ALIGNED
 *              - \ref EPWM_CENTER_ALIGNED
 * @return None
 * @details This macro is used to set the EPWM aligned type of specified channel(s).
 * \hideinitializer
 */
    #define EPWM_SET_ALIGNED_TYPE( epwm, u32ChannelMask, u32AlignedType )                                                \
    do {                                                                                                                 \
        uint32_t i;                                                                                                      \
        for( i = 0UL; i < 6UL; i++ ) {                                                                                   \
            if( ( u32ChannelMask ) & ( 1UL << i ) )                                                                      \
            {                                                                                                            \
                ( epwm )->CTL1 = ( ( ( epwm )->CTL1 & ~( 3UL << ( i << 1 ) ) ) | ( ( u32AlignedType ) << ( i << 1 ) ) ); \
            }                                                                                                            \
        }                                                                                                                \
    } while( 0 )

/**
 * @brief Set load window of window loading mode for specified channel(s)
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelMask Combination of enabled channels. Each bit corresponds to a channel
 *                           Bit 0 represents channel 0, bit 1 represents channel 1...
 * @return None
 * @details This macro is used to set load window of window loading mode for specified channel(s).
 * \hideinitializer
 */
    #define EPWM_SET_LOAD_WINDOW( epwm, u32ChannelMask )    ( ( epwm )->LOAD |= ( u32ChannelMask ) )

/**
 * @brief Trigger synchronous event from specified channel(s)
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelNum EPWM channel number. Valid values are 0, 2, 4
 *                           Bit 0 represents channel 0, bit 1 represents channel 2 and bit 2 represents channel 4
 * @return None
 * @details This macro is used to trigger synchronous event from specified channel(s).
 * \hideinitializer
 */
    #define EPWM_TRIGGER_SYNC( epwm, u32ChannelNum )        ( ( epwm )->SWSYNC |= ( 1U << ( ( u32ChannelNum ) >> 1 ) ) )

/**
 * @brief Clear counter of specified channel(s)
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelMask Combination of enabled channels. Each bit corresponds to a channel
 *                           Bit 0 represents channel 0, bit 1 represents channel 1...
 * @return None
 * @details This macro is used to clear counter of specified channel(s).
 * \hideinitializer
 */
    #define EPWM_CLR_COUNTER( epwm, u32ChannelMask )        ( ( epwm )->CNTCLR |= ( u32ChannelMask ) )

/**
 * @brief Set output level at zero, compare up, period(center) and compare down of specified channel(s)
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelMask Combination of enabled channels. Each bit corresponds to a channel
 *                           Bit 0 represents channel 0, bit 1 represents channel 1...
 * @param[in] u32ZeroLevel output level at zero point, valid values are:
 *              - \ref EPWM_OUTPUT_NOTHING
 *              - \ref EPWM_OUTPUT_LOW
 *              - \ref EPWM_OUTPUT_HIGH
 *              - \ref EPWM_OUTPUT_TOGGLE
 * @param[in] u32CmpUpLevel output level at compare up point, valid values are:
 *              - \ref EPWM_OUTPUT_NOTHING
 *              - \ref EPWM_OUTPUT_LOW
 *              - \ref EPWM_OUTPUT_HIGH
 *              - \ref EPWM_OUTPUT_TOGGLE
 * @param[in] u32PeriodLevel output level at period(center) point, valid values are:
 *              - \ref EPWM_OUTPUT_NOTHING
 *              - \ref EPWM_OUTPUT_LOW
 *              - \ref EPWM_OUTPUT_HIGH
 *              - \ref EPWM_OUTPUT_TOGGLE
 * @param[in] u32CmpDownLevel output level at compare down point, valid values are:
 *              - \ref EPWM_OUTPUT_NOTHING
 *              - \ref EPWM_OUTPUT_LOW
 *              - \ref EPWM_OUTPUT_HIGH
 *              - \ref EPWM_OUTPUT_TOGGLE
 * @return None
 * @details This macro is used to Set output level at zero, compare up, period(center) and compare down of specified channel(s).
 * \hideinitializer
 */
    #define EPWM_SET_OUTPUT_LEVEL( epwm, u32ChannelMask, u32ZeroLevel, u32CmpUpLevel, u32PeriodLevel, u32CmpDownLevel )                                                                     \
    do {                                                                                                                                                                                    \
        uint32_t i;                                                                                                                                                                         \
        for( i = 0UL; i < 6UL; i++ ) {                                                                                                                                                      \
            if( ( u32ChannelMask ) & ( 1UL << i ) ) {                                                                                                                                       \
                ( epwm )->WGCTL0 = ( ( ( epwm )->WGCTL0 & ~( 3UL << ( i << 1 ) ) ) | ( ( u32ZeroLevel ) << ( i << 1 ) ) );                                                                  \
                ( epwm )->WGCTL0 = ( ( ( epwm )->WGCTL0 & ~( 3UL << ( EPWM_WGCTL0_PRDPCTL0_Pos + ( i << 1 ) ) ) ) | ( ( u32PeriodLevel ) << ( EPWM_WGCTL0_PRDPCTL0_Pos + ( i << 1 ) ) ) );  \
                ( epwm )->WGCTL1 = ( ( ( epwm )->WGCTL1 & ~( 3UL << ( i << 1 ) ) ) | ( ( u32CmpUpLevel ) << ( i << 1 ) ) );                                                                 \
                ( epwm )->WGCTL1 = ( ( ( epwm )->WGCTL1 & ~( 3UL << ( EPWM_WGCTL1_CMPDCTL0_Pos + ( i << 1 ) ) ) ) | ( ( u32CmpDownLevel ) << ( EPWM_WGCTL1_CMPDCTL0_Pos + ( i << 1 ) ) ) ); \
            }                                                                                                                                                                               \
        }                                                                                                                                                                                   \
    } while( 0 )

/**
 * @brief Trigger brake event from specified channel(s)
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelMask Combination of enabled channels. Each bit corresponds to a channel
 *                           Bit 0 represents channel 0, bit 1 represents channel 2 and bit 2 represents channel 4
 * @param[in] u32BrakeType Type of brake trigger.
 *              - \ref EPWM_FB_EDGE
 *              - \ref EPWM_FB_LEVEL
 * @return None
 * @details This macro is used to trigger brake event from specified channel(s).
 * \hideinitializer
 */
    #define EPWM_TRIGGER_BRAKE( epwm, u32ChannelMask, u32BrakeType )    ( ( epwm )->SWBRK |= ( ( u32ChannelMask ) << ( u32BrakeType ) ) )

/**
 * @brief Set Dead zone clock source
 * @param[in] epwm The pointer of the specified EPWM module
 * @param[in] u32ChannelNum EPWM channel number. Valid values are between 0~5
 * @param[in] u32AfterPrescaler Dead zone clock source is from prescaler output. Valid values are TRUE (after prescaler) or FALSE (before prescaler).
 * @return None
 * @details This macro is used to set Dead zone clock source. Every two channels share the same setting.
 * @note The write-protection function should be disabled before using this function.
 * \hideinitializer
 */
    #define EPWM_SET_DEADZONE_CLK_SRC( epwm, u32ChannelNum, u32AfterPrescaler )                                                    \
    ( ( ( epwm )->DTCTL[ ( u32ChannelNum ) >> 1 ] ) = ( ( epwm )->DTCTL[ ( u32ChannelNum ) >> 1 ] & ~EPWM_DTCTL0_1_DTCKSEL_Msk ) | \
                                                      ( ( u32AfterPrescaler ) << EPWM_DTCTL0_1_DTCKSEL_Pos ) )

/*---------------------------------------------------------------------------------------------------------*/
/* Define EPWM functions prototype                                                                          */
/*---------------------------------------------------------------------------------------------------------*/
    uint32_t EPWM_ConfigCaptureChannel( EPWM_T * epwm,
                                        uint32_t u32ChannelNum,
                                        uint32_t u32UnitTimeNsec,
                                        uint32_t u32CaptureEdge );
    uint32_t EPWM_ConfigOutputChannel( EPWM_T * epwm,
                                       uint32_t u32ChannelNum,
                                       uint32_t u32Frequency,
                                       uint32_t u32DutyCycle );
    void EPWM_Start( EPWM_T * epwm,
                     uint32_t u32ChannelMask );
    void EPWM_Stop( EPWM_T * epwm,
                    uint32_t u32ChannelMask );
    void EPWM_ForceStop( EPWM_T * epwm,
                         uint32_t u32ChannelMask );
    void EPWM_EnableADCTrigger( EPWM_T * epwm,
                                uint32_t u32ChannelNum,
                                uint32_t u32Condition );
    void EPWM_DisableADCTrigger( EPWM_T * epwm,
                                 uint32_t u32ChannelNum );
    void EPWM_ClearADCTriggerFlag( EPWM_T * epwm,
                                   uint32_t u32ChannelNum,
                                   uint32_t u32Condition );
    uint32_t EPWM_GetADCTriggerFlag( EPWM_T * epwm,
                                     uint32_t u32ChannelNum );
    void EPWM_EnableDACTrigger( EPWM_T * epwm,
                                uint32_t u32ChannelNum,
                                uint32_t u32Condition );
    void EPWM_DisableDACTrigger( EPWM_T * epwm,
                                 uint32_t u32ChannelNum );
    void EPWM_ClearDACTriggerFlag( EPWM_T * epwm,
                                   uint32_t u32ChannelNum,
                                   uint32_t u32Condition );
    uint32_t EPWM_GetDACTriggerFlag( EPWM_T * epwm,
                                     uint32_t u32ChannelNum );
    void EPWM_EnableFaultBrake( EPWM_T * epwm,
                                uint32_t u32ChannelMask,
                                uint32_t u32LevelMask,
                                uint32_t u32BrakeSource );
    void EPWM_EnableCapture( EPWM_T * epwm,
                             uint32_t u32ChannelMask );
    void EPWM_DisableCapture( EPWM_T * epwm,
                              uint32_t u32ChannelMask );
    void EPWM_EnableOutput( EPWM_T * epwm,
                            uint32_t u32ChannelMask );
    void EPWM_DisableOutput( EPWM_T * epwm,
                             uint32_t u32ChannelMask );
    void EPWM_EnablePDMA( EPWM_T * epwm,
                          uint32_t u32ChannelNum,
                          uint32_t u32RisingFirst,
                          uint32_t u32Mode );
    void EPWM_DisablePDMA( EPWM_T * epwm,
                           uint32_t u32ChannelNum );
    void EPWM_EnableDeadZone( EPWM_T * epwm,
                              uint32_t u32ChannelNum,
                              uint32_t u32Duration );
    void EPWM_DisableDeadZone( EPWM_T * epwm,
                               uint32_t u32ChannelNum );
    void EPWM_EnableCaptureInt( EPWM_T * epwm,
                                uint32_t u32ChannelNum,
                                uint32_t u32Edge );
    void EPWM_DisableCaptureInt( EPWM_T * epwm,
                                 uint32_t u32ChannelNum,
                                 uint32_t u32Edge );
    void EPWM_ClearCaptureIntFlag( EPWM_T * epwm,
                                   uint32_t u32ChannelNum,
                                   uint32_t u32Edge );
    uint32_t EPWM_GetCaptureIntFlag( EPWM_T * epwm,
                                     uint32_t u32ChannelNum );
    void EPWM_EnableDutyInt( EPWM_T * epwm,
                             uint32_t u32ChannelNum,
                             uint32_t u32IntDutyType );
    void EPWM_DisableDutyInt( EPWM_T * epwm,
                              uint32_t u32ChannelNum );
    void EPWM_ClearDutyIntFlag( EPWM_T * epwm,
                                uint32_t u32ChannelNum );
    uint32_t EPWM_GetDutyIntFlag( EPWM_T * epwm,
                                  uint32_t u32ChannelNum );
    void EPWM_EnableFaultBrakeInt( EPWM_T * epwm,
                                   uint32_t u32BrakeSource );
    void EPWM_DisableFaultBrakeInt( EPWM_T * epwm,
                                    uint32_t u32BrakeSource );
    void EPWM_ClearFaultBrakeIntFlag( EPWM_T * epwm,
                                      uint32_t u32BrakeSource );
    uint32_t EPWM_GetFaultBrakeIntFlag( EPWM_T * epwm,
                                        uint32_t u32BrakeSource );
    void EPWM_EnablePeriodInt( EPWM_T * epwm,
                               uint32_t u32ChannelNum,
                               uint32_t u32IntPeriodType );
    void EPWM_DisablePeriodInt( EPWM_T * epwm,
                                uint32_t u32ChannelNum );
    void EPWM_ClearPeriodIntFlag( EPWM_T * epwm,
                                  uint32_t u32ChannelNum );
    uint32_t EPWM_GetPeriodIntFlag( EPWM_T * epwm,
                                    uint32_t u32ChannelNum );
    void EPWM_EnableZeroInt( EPWM_T * epwm,
                             uint32_t u32ChannelNum );
    void EPWM_DisableZeroInt( EPWM_T * epwm,
                              uint32_t u32ChannelNum );
    void EPWM_ClearZeroIntFlag( EPWM_T * epwm,
                                uint32_t u32ChannelNum );
    uint32_t EPWM_GetZeroIntFlag( EPWM_T * epwm,
                                  uint32_t u32ChannelNum );
    void EPWM_EnableAcc( EPWM_T * epwm,
                         uint32_t u32ChannelNum,
                         uint32_t u32IntFlagCnt,
                         uint32_t u32IntAccSrc );
    void EPWM_DisableAcc( EPWM_T * epwm,
                          uint32_t u32ChannelNum );
    void EPWM_EnableAccInt( EPWM_T * epwm,
                            uint32_t u32ChannelNum );
    void EPWM_DisableAccInt( EPWM_T * epwm,
                             uint32_t u32ChannelNum );
    void EPWM_ClearAccInt( EPWM_T * epwm,
                           uint32_t u32ChannelNum );
    uint32_t EPWM_GetAccInt( EPWM_T * epwm,
                             uint32_t u32ChannelNum );
    void EPWM_EnableAccPDMA( EPWM_T * epwm,
                             uint32_t u32ChannelNum );
    void EPWM_DisableAccPDMA( EPWM_T * epwm,
                              uint32_t u32ChannelNum );
    void EPWM_ClearFTDutyIntFlag( EPWM_T * epwm,
                                  uint32_t u32ChannelNum );
    uint32_t EPWM_GetFTDutyIntFlag( EPWM_T * epwm,
                                    uint32_t u32ChannelNum );
    void EPWM_EnableLoadMode( EPWM_T * epwm,
                              uint32_t u32ChannelNum,
                              uint32_t u32LoadMode );
    void EPWM_DisableLoadMode( EPWM_T * epwm,
                               uint32_t u32ChannelNum,
                               uint32_t u32LoadMode );
    void EPWM_ConfigSyncPhase( EPWM_T * epwm,
                               uint32_t u32ChannelNum,
                               uint32_t u32SyncSrc,
                               uint32_t u32Direction,
                               uint32_t u32StartPhase );
    void EPWM_EnableSyncPhase( EPWM_T * epwm,
                               uint32_t u32ChannelMask );
    void EPWM_DisableSyncPhase( EPWM_T * epwm,
                                uint32_t u32ChannelMask );
    void EPWM_EnableSyncNoiseFilter( EPWM_T * epwm,
                                     uint32_t u32ClkCnt,
                                     uint32_t u32ClkDivSel );
    void EPWM_DisableSyncNoiseFilter( EPWM_T * epwm );
    void EPWM_EnableSyncPinInverse( EPWM_T * epwm );
    void EPWM_DisableSyncPinInverse( EPWM_T * epwm );
    void EPWM_SetClockSource( EPWM_T * epwm,
                              uint32_t u32ChannelNum,
                              uint32_t u32ClkSrcSel );
    void EPWM_EnableBrakeNoiseFilter( EPWM_T * epwm,
                                      uint32_t u32BrakePinNum,
                                      uint32_t u32ClkCnt,
                                      uint32_t u32ClkDivSel );
    void EPWM_DisableBrakeNoiseFilter( EPWM_T * epwm,
                                       uint32_t u32BrakePinNum );
    void EPWM_EnableBrakePinInverse( EPWM_T * epwm,
                                     uint32_t u32BrakePinNum );
    void EPWM_DisableBrakePinInverse( EPWM_T * epwm,
                                      uint32_t u32BrakePinNum );
    void EPWM_SetBrakePinSource( EPWM_T * epwm,
                                 uint32_t u32BrakePinNum,
                                 uint32_t u32SelAnotherModule );
    void EPWM_SetLeadingEdgeBlanking( EPWM_T * epwm,
                                      uint32_t u32TrigSrcSel,
                                      uint32_t u32TrigType,
                                      uint32_t u32BlankingCnt,
                                      uint32_t u32BlankingEnable );
    uint32_t EPWM_GetWrapAroundFlag( EPWM_T * epwm,
                                     uint32_t u32ChannelNum );
    void EPWM_ClearWrapAroundFlag( EPWM_T * epwm,
                                   uint32_t u32ChannelNum );

/*@}*/ /* end of group EPWM_EXPORTED_FUNCTIONS */

/*@}*/ /* end of group EPWM_Driver */

/*@}*/ /* end of group Standard_Driver */

    #ifdef __cplusplus
}
    #endif

#endif /* __EPWM_H__ */

/*** (C) COPYRIGHT 2017 Nuvoton Technology Corp. ***/
