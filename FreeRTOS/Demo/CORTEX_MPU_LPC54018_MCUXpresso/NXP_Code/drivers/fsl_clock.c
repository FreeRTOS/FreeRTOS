/*
 * Copyright (c) 2016, Freescale Semiconductor, Inc.
 * Copyright 2016 - 2019 , NXP
 * All rights reserved.
 *
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "fsl_clock.h"
#include "fsl_power.h"
/*******************************************************************************
 * Definitions
 ******************************************************************************/
/* Component ID definition, used by tools. */
#ifndef FSL_COMPONENT_ID
#define FSL_COMPONENT_ID "platform.drivers.clock"
#endif
#define NVALMAX (0x100U)
#define PVALMAX (0x20U)
#define MVALMAX (0x8000U)

#define USB_NVALMAX (0x4U)
#define USB_PVALMAX (0x8U)
#define USB_MVALMAX (0x100U)

#define PLL_MAX_N_DIV 0x100U
#define USB_PLL_MAX_N_DIV 0x100U

#define PLL_MDEC_VAL_P (0U)                          /*!<  MDEC is in bits  16 downto 0 */
#define PLL_MDEC_VAL_M (0x1FFFFUL << PLL_MDEC_VAL_P) /*!<  NDEC is in bits  9 downto 0 */
#define PLL_NDEC_VAL_P (0U)                          /*!<  NDEC is in bits  9:0 */
#define PLL_NDEC_VAL_M (0x3FFUL << PLL_NDEC_VAL_P)
#define PLL_PDEC_VAL_P (0U) /*!<  PDEC is in bits 6:0 */
#define PLL_PDEC_VAL_M (0x7FUL << PLL_PDEC_VAL_P)

#define PLL_MIN_CCO_FREQ_MHZ (275000000U)
#define PLL_MAX_CCO_FREQ_MHZ (550000000U)
#define PLL_LOWER_IN_LIMIT (4000U) /*!<  Minimum PLL input rate */
#define PLL_MIN_IN_SSMODE (2000000U)
#define PLL_MAX_IN_SSMODE (4000000U)

/*!<  Middle of the range values for spread-spectrum */
#define PLL_SSCG_MF_FREQ_VALUE 4U
#define PLL_SSCG_MC_COMP_VALUE 2U
#define PLL_SSCG_MR_DEPTH_VALUE 4U
#define PLL_SSCG_DITHER_VALUE 0U

/*!<  USB PLL CCO MAX AND MIN FREQ */
#define USB_PLL_MIN_CCO_FREQ_MHZ (156000000U)
#define USB_PLL_MAX_CCO_FREQ_MHZ (320000000U)
#define USB_PLL_LOWER_IN_LIMIT (1000000U) /*!<  Minimum PLL input rate */

#define USB_PLL_MSEL_VAL_P (0U) /*!<  MSEL is in bits  7 downto 0 */
#define USB_PLL_MSEL_VAL_M (0xFFU)
#define USB_PLL_PSEL_VAL_P (8U) /*!<  PDEC is in bits 9:8 */
#define USB_PLL_PSEL_VAL_M (0x3U)
#define USB_PLL_NSEL_VAL_P (10U) /*!<  NDEC is in bits  11:10 */
#define USB_PLL_NSEL_VAL_M (0x3U)

/*!<  SWITCH USB POSTDIVIDER FOR REGITSER WRITING */
#define SWITCH_USB_PSEL(x) \
    (((x) == 0x0U) ? 0x1U : ((x) == 0x1U) ? 0x02U : ((x) == 0x2U) ? 0x4U : ((x) == 3U) ? 0x8U : 0U)

/*!<  SYS PLL NDEC reg */
#define PLL_NDEC_VAL_SET(value) (((unsigned long)(value) << PLL_NDEC_VAL_P) & PLL_NDEC_VAL_M)
/*!<  SYS PLL PDEC reg */
#define PLL_PDEC_VAL_SET(value) (((unsigned long)(value) << PLL_PDEC_VAL_P) & PLL_PDEC_VAL_M)
/*!<  SYS PLL MDEC reg */
#define PLL_MDEC_VAL_SET(value) (((unsigned long)(value) << PLL_MDEC_VAL_P) & PLL_MDEC_VAL_M)

/*!<  SYS PLL NSEL reg */
#define USB_PLL_NSEL_VAL_SET(value) (((unsigned long)(value)&USB_PLL_NSEL_VAL_M) << USB_PLL_NSEL_VAL_P)
/*!<  SYS PLL PSEL reg */
#define USB_PLL_PSEL_VAL_SET(value) (((unsigned long)(value)&USB_PLL_PSEL_VAL_M) << USB_PLL_PSEL_VAL_P)
/*!<  SYS PLL MSEL reg */
#define USB_PLL_MSEL_VAL_SET(value) (((unsigned long)(value)&USB_PLL_MSEL_VAL_M) << USB_PLL_MSEL_VAL_P)

/*!<  FRAC control */
#define AUDIO_PLL_FRACT_MD_P (0U)
#define AUDIO_PLL_FRACT_MD_INT_P (15U)
#define AUDIO_PLL_FRACT_MD_M (0x7FFFUL << AUDIO_PLL_FRACT_MD_P)
#define AUDIO_PLL_FRACT_MD_INT_M (0x7FUL << AUDIO_PLL_FRACT_MD_INT_P)

#define AUDIO_PLL_MD_FRACT_SET(value) (((unsigned long)(value) << AUDIO_PLL_FRACT_MD_P) & PLL_FRAC_MD_FRACT_M)
#define AUDIO_PLL_MD_INT_SET(value) (((unsigned long)(value) << AUDIO_PLL_FRACT_MD_INT_P) & AUDIO_PLL_FRACT_MD_INT_M)

/* Saved value of PLL output rate, computed whenever needed to save run-time
   computation on each call to retrive the PLL rate. */
static uint32_t s_Pll_Freq;
static uint32_t s_Usb_Pll_Freq;
static uint32_t s_Audio_Pll_Freq;

/** External clock rate on the CLKIN pin in Hz. If not used,
    set this to 0. Otherwise, set it to the exact rate in Hz this pin is
    being driven at. */
static const uint32_t g_I2S_Mclk_Freq   = 0U;
static const uint32_t g_Ext_Clk_Freq    = 12000000U;
static const uint32_t g_Lcd_Clk_In_Freq = 0U;

/*******************************************************************************
 * Variables
 ******************************************************************************/

/*******************************************************************************
 * Prototypes
 ******************************************************************************/
/* Find encoded NDEC value for raw N value, max N = NVALMAX */
static uint32_t pllEncodeN(uint32_t N);
/* Find decoded N value for raw NDEC value */
static uint32_t pllDecodeN(uint32_t NDEC);
/* Find encoded PDEC value for raw P value, max P = PVALMAX */
static uint32_t pllEncodeP(uint32_t P);
/* Find decoded P value for raw PDEC value */
static uint32_t pllDecodeP(uint32_t PDEC);
/* Find encoded MDEC value for raw M value, max M = MVALMAX */
static uint32_t pllEncodeM(uint32_t M);
/* Find decoded M value for raw MDEC value */
static uint32_t pllDecodeM(uint32_t MDEC);
/* Find SELP, SELI, and SELR values for raw M value, max M = MVALMAX */
static void pllFindSel(uint32_t M, uint32_t *pSelP, uint32_t *pSelI, uint32_t *pSelR);
/* Get predivider (N) from PLL NDEC setting */
static uint32_t findPllPreDiv(uint32_t ctrlReg, uint32_t nDecReg);
/* Get postdivider (P) from PLL PDEC setting */
static uint32_t findPllPostDiv(uint32_t ctrlReg, uint32_t pDecReg);
/* Get multiplier (M) from PLL MDEC and BYPASS_FBDIV2 settings */
static uint32_t findPllMMult(uint32_t ctrlReg, uint32_t mDecReg);
/* Convert the binary to fractional part */
static double Binary2Fractional(uint32_t binaryPart);
/* Calculate the powerTimes' power of 2 */
static uint32_t power2Cal(uint32_t powerTimes);
/* Get the greatest common divisor */
static uint32_t FindGreatestCommonDivisor(uint32_t m, uint32_t n);
/* Set PLL output based on desired output rate */
static pll_error_t CLOCK_GetPllConfig(uint32_t finHz, uint32_t foutHz, pll_setup_t *pSetup);

/* Update local PLL rate variable */
static void CLOCK_GetSystemPLLOutFromSetupUpdate(pll_setup_t *pSetup);
static void CLOCK_GetAudioPLLOutFromSetupUpdate(pll_setup_t *pSetup);

/*!
 * @brief Set fro clock frequency.
 * Due to LPC540xx 0A silicon and LPC540xx 1B silicon have different ROM addresses for set fro
 * frequency api, so add this api to get rom version.
 * @param base romVersion pointer to recieve rom version.
 */
#if defined(FSL_FROHF_SETTING_API_ADDRESS_DETERMINE_BY_ROM_VERSION) && \
    (FSL_FROHF_SETTING_API_ADDRESS_DETERMINE_BY_ROM_VERSION)
static uint32_t CLOCK_GetRomVersion(uint8_t *romVersion);
#endif

static const uint8_t wdtFreqLookup[32] = {0,  8,  12, 15, 18, 20, 24, 26, 28, 30, 32, 34, 36, 38, 40, 41,
                                          42, 44, 45, 46, 48, 49, 50, 52, 53, 54, 56, 57, 58, 59, 60, 61};
/*******************************************************************************
 * Code
 ******************************************************************************/
#if defined(FSL_FROHF_SETTING_API_ADDRESS_DETERMINE_BY_ROM_VERSION) && \
    (FSL_FROHF_SETTING_API_ADDRESS_DETERMINE_BY_ROM_VERSION)
static uint32_t CLOCK_GetRomVersion(uint8_t *romVersion)
{
    uint32_t command[5] = {0U}, result[4] = {0U};

    command[0] = 55U;
    result[0]  = 0;
    result[1]  = 0;
    ((void (*)(uint32_t cmd[5], uint32_t stat[4]))FSL_FEATURE_SYSCON_IAP_ENTRY_LOCATION)(command, result);

    *romVersion = (uint8_t)(result[1]);

    return result[0];
}
#endif

/**
 * brief
 *  Initialize the Core clock to given frequency (12, 48 or 96 MHz), this API is implememnt in ROM code.
 * Turns on FRO and uses default CCO, if freq is 12000000, then high speed output is off, else high speed
 * output is enabled.
 * Usage: CLOCK_SetupFROClocking(frequency), (frequency must be one of 12, 48 or 96 MHz)
 *  Note: Need to make sure ROM and OTP has power(PDRUNCFG0[17,29]= 0U) before calling this API since this API is
 * implemented in ROM code and the FROHF TRIM value is stored in OTP
 *
 * param froFreq target fro frequency.
 * return   Nothing
 */

void CLOCK_SetupFROClocking(uint32_t froFreq)
{
    uint32_t froRomAddr = 0U;
#if defined(FSL_FROHF_SETTING_API_ADDRESS_DETERMINE_BY_ROM_VERSION) && \
    (FSL_FROHF_SETTING_API_ADDRESS_DETERMINE_BY_ROM_VERSION)
    uint8_t romVersion = 0U;

    if (CLOCK_GetRomVersion(&romVersion) == (uint32_t)kStatus_Success)
    {
        if (romVersion == FSL_ROM_VERSION_1B)
        {
            froRomAddr = FSL_ROM_VERSION_1B_FRO_SETTING_ADDR;
        }
        else
        {
            froRomAddr = FSL_ROM_VERSION_0A_FRO_SETTING_ADDR;
        }

        (*((void (*)(uint32_t funcname))(froRomAddr)))(froFreq);
    }
#else
    froRomAddr = FSL_ROM_VERSION_0A_FRO_SETTING_ADDR;

    (*((void (*)(uint32_t))(froRomAddr)))(froFreq);
#endif
}

/* Clock Selection for IP */
/**
 * brief	Configure the clock selection muxes.
 * param	connection	: Clock to be configured.
 * return	Nothing
 */
void CLOCK_AttachClk(clock_attach_id_t connection)
{
    uint8_t mux;
    uint8_t sel;
    uint16_t item;
    uint32_t tmp32 = (uint32_t)connection;
    uint32_t i;
    volatile uint32_t *pClkSel;

    pClkSel = &(SYSCON->STICKCLKSEL);

    if (kNONE_to_NONE != connection)
    {
        for (i = 0U; i < 2U; i++)
        {
            if (tmp32 == 0U)
            {
                break;
            }
            item = (uint16_t)GET_ID_ITEM(tmp32);
            if (item != 0UL)
            {
                mux = GET_ID_ITEM_MUX(item);
                sel = GET_ID_ITEM_SEL(item);
                if (mux == CM_ASYNCAPB)
                {
                    SYSCON->ASYNCAPBCTRL          = SYSCON_ASYNCAPBCTRL_ENABLE(1);
                    ASYNC_SYSCON->ASYNCAPBCLKSELA = sel;
                }
                else
                {
                    ((volatile uint32_t *)pClkSel)[mux] = sel;
                }
            }
            tmp32 = GET_ID_NEXT_ITEM(tmp32); /* pick up next descriptor */
        }
    }
}

/* Return the actual clock attach id */
/**
 * brief   Get the actual clock attach id.
 * This fuction uses the offset in input attach id, then it reads the actual source value in
 * the register and combine the offset to obtain an actual attach id.
 * param   attachId  : Clock attach id to get.
 * return  Clock source value.
 */
clock_attach_id_t CLOCK_GetClockAttachId(clock_attach_id_t attachId)
{
    uint8_t mux;
    uint8_t actualSel;
    uint32_t tmp32 = (uint32_t)attachId;
    uint32_t i;
    uint32_t actualAttachId = 0U;
    uint32_t selector       = GET_ID_SELECTOR(tmp32);
    volatile uint32_t *pClkSel;

    pClkSel = &(SYSCON->STICKCLKSEL);

    if (kNONE_to_NONE == attachId)
    {
        return kNONE_to_NONE;
    }

    for (i = 0U; i < 2U; i++)
    {
        mux = GET_ID_ITEM_MUX(tmp32);
        if (tmp32 != 0UL)
        {
            if (mux == CM_ASYNCAPB)
            {
                actualSel = (uint8_t)(ASYNC_SYSCON->ASYNCAPBCLKSELA);
            }
            else
            {
                actualSel = (uint8_t)(((volatile uint32_t *)pClkSel)[mux]);
            }

            /* Consider the combination of two registers */
            actualAttachId |= CLK_ATTACH_ID(mux, actualSel, i);
        }
        tmp32 = GET_ID_NEXT_ITEM(tmp32); /*!<  pick up next descriptor */
    }

    actualAttachId |= selector;

    return (clock_attach_id_t)actualAttachId;
}

/* Set IP Clock Divider */
/**
 * brief	Setup peripheral clock dividers.
 * param	div_name	: Clock divider name
 * param divided_by_value: Value to be divided
 * param reset :  Whether to reset the divider counter.
 * return	Nothing
 */
void CLOCK_SetClkDiv(clock_div_name_t div_name, uint32_t divided_by_value, bool reset)
{
    volatile uint32_t *pClkDiv;

    pClkDiv = &(SYSCON->SYSTICKCLKDIV);
    if (reset)
    {
        ((volatile uint32_t *)pClkDiv)[(uint8_t)div_name] = 1UL << 29U;
    }
    if (divided_by_value == 0U) /*!<  halt */
    {
        ((volatile uint32_t *)pClkDiv)[(uint8_t)div_name] = 1UL << 30U;
    }
    else
    {
        ((volatile uint32_t *)pClkDiv)[(uint8_t)div_name] = (divided_by_value - 1U);
    }
}

/* Get CLOCK OUT Clk */
/*! brief	Return Frequency of ClockOut
 *  return	Frequency of ClockOut
 */
uint32_t CLOCK_GetClockOutClkFreq(void)
{
    uint32_t freq = 0U;

    switch (SYSCON->CLKOUTSELA)
    {
        case 0U:
            freq = CLOCK_GetCoreSysClkFreq();
            break;

        case 1U:
            freq = CLOCK_GetExtClkFreq();
            break;

        case 2U:
            freq = CLOCK_GetWdtOscFreq();
            break;

        case 3U:
            freq = CLOCK_GetFroHfFreq();
            break;

        case 4U:
            freq = CLOCK_GetPllOutFreq();
            break;

        case 5U:
            freq = CLOCK_GetUsbPllOutFreq();
            break;

        case 6U:
            freq = CLOCK_GetAudioPllOutFreq();
            break;

        case 7U:
            freq = CLOCK_GetOsc32KFreq();
            break;

        default:
            freq = 0U;
            break;
    }
    return freq / ((SYSCON->CLKOUTDIV & 0xffU) + 1U);
}

/* Get SPIFI Clk */
/*! brief	Return Frequency of Spifi Clock
 *  return	Frequency of Spifi.
 */
uint32_t CLOCK_GetSpifiClkFreq(void)
{
    uint32_t freq = 0U;

    switch (SYSCON->SPIFICLKSEL)
    {
        case 0U:
            freq = CLOCK_GetCoreSysClkFreq();
            break;
        case 1U:
            freq = CLOCK_GetPllOutFreq();
            break;
        case 2U:
            freq = CLOCK_GetUsbPllOutFreq();
            break;
        case 3U:
            freq = CLOCK_GetFroHfFreq();
            break;
        case 4U:
            freq = CLOCK_GetAudioPllOutFreq();
            break;
        case 7U:
            freq = 0U;
            break;
        default:
            freq = 0U;
            break;
    }

    return freq / ((SYSCON->SPIFICLKDIV & 0xffU) + 1U);
}

/* Get ADC Clk */
/*! brief	Return Frequency of Adc Clock
 *  return	Frequency of Adc Clock.
 */
uint32_t CLOCK_GetAdcClkFreq(void)
{
    uint32_t freq = 0U;

    switch (SYSCON->ADCCLKSEL)
    {
        case 0U:
            freq = CLOCK_GetFroHfFreq();
            break;
        case 1U:
            freq = CLOCK_GetPllOutFreq();
            break;
        case 2U:
            freq = CLOCK_GetUsbPllOutFreq();
            break;
        case 3U:
            freq = CLOCK_GetAudioPllOutFreq();
            break;
        case 7U:
            freq = 0U;
            break;
        default:
            freq = 0U;
            break;
    }

    return freq / ((SYSCON->ADCCLKDIV & 0xffU) + 1U);
}

/* Get USB0 Clk */
/*! brief	Return Frequency of Usb0 Clock
 *  return	Frequency of Usb0 Clock.
 */
uint32_t CLOCK_GetUsb0ClkFreq(void)
{
    uint32_t freq = 0U;

    switch (SYSCON->USB0CLKSEL)
    {
        case 0U:
            freq = CLOCK_GetFroHfFreq();
            break;
        case 1U:
            freq = CLOCK_GetPllOutFreq();
            break;
        case 2U:
            freq = CLOCK_GetUsbPllOutFreq();
            break;
        case 7U:
            freq = 0U;
            break;

        default:
            freq = 0U;
            break;
    }

    return freq / ((SYSCON->USB0CLKDIV & 0xffU) + 1U);
}

/* Get USB1 Clk */
/*! brief	Return Frequency of Usb1 Clock
 *  return	Frequency of Usb1 Clock.
 */
uint32_t CLOCK_GetUsb1ClkFreq(void)
{
    uint32_t freq = 0U;

    switch (SYSCON->USB1CLKSEL)
    {
        case 0U:
            freq = CLOCK_GetCoreSysClkFreq();
            break;
        case 1U:
            freq = CLOCK_GetPllOutFreq();
            break;
        case 2U:
            freq = CLOCK_GetUsbPllOutFreq();
            break;
        case 7U:
            freq = 0U;
            break;

        default:
            freq = 0U;
            break;
    }

    return freq / ((SYSCON->USB1CLKDIV & 0xffU) + 1U);
}

/* Get MCLK Clk */
/*! brief	Return Frequency of MClk Clock
 *  return	Frequency of MClk Clock.
 */
uint32_t CLOCK_GetMclkClkFreq(void)
{
    uint32_t freq = 0U;

    switch (SYSCON->MCLKCLKSEL)
    {
        case 0U:
            freq = CLOCK_GetFroHfFreq() / ((SYSCON->FROHFDIV & 0xffu) + 1U);
            break;
        case 1U:
            freq = CLOCK_GetAudioPllOutFreq();
            break;
        case 7U:
            freq = 0U;
            break;

        default:
            freq = 0U;
            break;
    }

    return freq / ((SYSCON->MCLKDIV & 0xffU) + 1U);
}

/* Get SCTIMER Clk */
/*! brief	Return Frequency of SCTimer Clock
 *  return	Frequency of SCTimer Clock.
 */
uint32_t CLOCK_GetSctClkFreq(void)
{
    uint32_t freq = 0U;

    switch (SYSCON->SCTCLKSEL)
    {
        case 0U:
            freq = CLOCK_GetCoreSysClkFreq();
            break;
        case 1U:
            freq = CLOCK_GetPllOutFreq();
            break;
        case 2U:
            freq = CLOCK_GetFroHfFreq();
            break;
        case 3U:
            freq = CLOCK_GetAudioPllOutFreq();
            break;
        case 7U:
            freq = 0U;
            break;

        default:
            freq = 0U;
            break;
    }

    return freq / ((SYSCON->SCTCLKDIV & 0xffU) + 1U);
}

/* Get SDIO Clk */
/*! brief	Return Frequency of SDIO Clock
 *  return	Frequency of SDIO Clock.
 */
uint32_t CLOCK_GetSdioClkFreq(void)
{
    uint32_t freq = 0U;

    switch (SYSCON->SDIOCLKSEL)
    {
        case 0U:
            freq = CLOCK_GetCoreSysClkFreq();
            break;
        case 1U:
            freq = CLOCK_GetPllOutFreq();
            break;
        case 2U:
            freq = CLOCK_GetUsbPllOutFreq();
            break;
        case 3U:
            freq = CLOCK_GetFroHfFreq();
            break;
        case 4U:
            freq = CLOCK_GetAudioPllOutFreq();
            break;
        case 7U:
            freq = 0U;
            break;
        default:
            freq = 0U;
            break;
    }

    return freq / ((SYSCON->SDIOCLKDIV & 0xffU) + 1U);
}

/* Get LCD Clk */
/*! brief	Return Frequency of LCD Clock
 *  return	Frequency of LCD Clock.
 */
uint32_t CLOCK_GetLcdClkFreq(void)
{
    uint32_t freq = 0U;

    switch (SYSCON->LCDCLKSEL)
    {
        case 0U:
            freq = CLOCK_GetCoreSysClkFreq();
            break;
        case 1U:
            freq = CLOCK_GetLcdClkIn();
            break;
        case 2U:
            freq = CLOCK_GetFroHfFreq();
            break;
        case 3U:
            freq = 0U;
            break;

        default:
            freq = 0U;
            break;
    }

    return freq / ((SYSCON->LCDCLKDIV & 0xffU) + 1U);
}

/* Get LCD CLK IN Clk */
/*! brief	Return Frequency of LCD CLKIN Clock
 *  return	Frequency of LCD CLKIN Clock.
 */
uint32_t CLOCK_GetLcdClkIn(void)
{
    return g_Lcd_Clk_In_Freq;
}

/* Get FRO 12M Clk */
/*! brief	Return Frequency of FRO 12MHz
 *  return	Frequency of FRO 12MHz
 */
uint32_t CLOCK_GetFro12MFreq(void)
{
    return ((SYSCON->PDRUNCFG[0] & SYSCON_PDRUNCFG_PDEN_FRO_MASK) != 0UL) ? 0U : 12000000U;
}

/* Get EXT OSC Clk */
/*! brief	Return Frequency of External Clock
 *  return	Frequency of External Clock. If no external clock is used returns 0.
 */
uint32_t CLOCK_GetExtClkFreq(void)
{
    return g_Ext_Clk_Freq;
}

/* Get WATCH DOG Clk */
/*! brief	Return Frequency of Watchdog Oscillator
 *  return	Frequency of Watchdog Oscillator
 */
uint32_t CLOCK_GetWdtOscFreq(void)
{
    uint8_t freq_sel, div_sel;
    if ((SYSCON->PDRUNCFG[0] & SYSCON_PDRUNCFG_PDEN_WDT_OSC_MASK) != 0UL)
    {
        return 0U;
    }
    else
    {
        div_sel = (uint8_t)(((SYSCON->WDTOSCCTRL & 0x1fU) + 1U) << 1U);
        freq_sel =
            wdtFreqLookup[((SYSCON->WDTOSCCTRL & SYSCON_WDTOSCCTRL_FREQSEL_MASK) >> SYSCON_WDTOSCCTRL_FREQSEL_SHIFT)];
        return ((uint32_t)freq_sel * 50000U) / ((uint32_t)div_sel);
    }
}

/* Get HF FRO Clk */
/*! brief	Return Frequency of High-Freq output of FRO
 *  return	Frequency of High-Freq output of FRO
 */
uint32_t CLOCK_GetFroHfFreq(void)
{
    if (((SYSCON->PDRUNCFG[0] & SYSCON_PDRUNCFG_PDEN_FRO_MASK) != 0UL) ||
        (0UL == (SYSCON->FROCTRL & SYSCON_FROCTRL_HSPDCLK_MASK)))
    {
        return 0U;
    }

    if ((SYSCON->FROCTRL & SYSCON_FROCTRL_SEL_MASK) != 0UL)
    {
        return 96000000U;
    }
    else
    {
        return 48000000U;
    }
}

/* Get SYSTEM PLL Clk */
/*! brief	Return Frequency of PLL
 *  return	Frequency of PLL
 */
uint32_t CLOCK_GetPllOutFreq(void)
{
    return s_Pll_Freq;
}

/* Get AUDIO PLL Clk */
/*! brief	Return Frequency of AUDIO PLL
 *  return	Frequency of PLL
 */
uint32_t CLOCK_GetAudioPllOutFreq(void)
{
    return s_Audio_Pll_Freq;
}

/* Get USB PLL Clk */
/*! brief	Return Frequency of USB PLL
 *  return	Frequency of PLL
 */
uint32_t CLOCK_GetUsbPllOutFreq(void)
{
    return s_Usb_Pll_Freq;
}

/* Get RTC OSC Clk */
/*! brief	Return Frequency of 32kHz osc
 *  return	Frequency of 32kHz osc
 */
uint32_t CLOCK_GetOsc32KFreq(void)
{
    return CLK_RTC_32K_CLK; /* Needs to be corrected to check that RTC Clock is enabled */
}

/* Get MAIN Clk */
/*! brief	Return Frequency of Core System
 *  return	Frequency of Core System
 */
uint32_t CLOCK_GetCoreSysClkFreq(void)
{
    uint32_t freq = 0U;

    switch (SYSCON->MAINCLKSELB)
    {
        case 0U:
            if (SYSCON->MAINCLKSELA == 0U)
            {
                freq = CLOCK_GetFro12MFreq();
            }
            else if (SYSCON->MAINCLKSELA == 1U)
            {
                freq = CLOCK_GetExtClkFreq();
            }
            else if (SYSCON->MAINCLKSELA == 2U)
            {
                freq = CLOCK_GetWdtOscFreq();
            }
            else if (SYSCON->MAINCLKSELA == 3U)
            {
                freq = CLOCK_GetFroHfFreq();
            }
            else
            {
                /* Add comment to prevent the case of rule 15.7. */
            }
            break;
        case 2U:
            freq = CLOCK_GetPllOutFreq();
            break;

        case 3U:
            freq = CLOCK_GetOsc32KFreq();
            break;

        default:
            freq = 0U;
            break;
    }

    return freq;
}

/* Get I2S MCLK Clk */
/*! brief	Return Frequency of I2S MCLK Clock
 *  return	Frequency of I2S MCLK Clock
 */
uint32_t CLOCK_GetI2SMClkFreq(void)
{
    return g_I2S_Mclk_Freq;
}

/* Get ASYNC APB Clk */
/*! brief	Return Frequency of Asynchronous APB Clock
 *  return	Frequency of Asynchronous APB Clock Clock
 */
uint32_t CLOCK_GetAsyncApbClkFreq(void)
{
    async_clock_src_t clkSrc;
    uint32_t clkRate;

    clkSrc = CLOCK_GetAsyncApbClkSrc();

    switch (clkSrc)
    {
        case kCLOCK_AsyncMainClk:
            clkRate = CLOCK_GetCoreSysClkFreq();
            break;
        case kCLOCK_AsyncFro12Mhz:
            clkRate = CLK_FRO_12MHZ;
            break;
        default:
            clkRate = 0U;
            break;
    }

    return clkRate;
}

/* Get MCAN Clk */
/*! brief	Return Frequency of MCAN Clock
 *  param	MCanSel : 0U: MCAN0; 1U: MCAN1
 *  return	Frequency of MCAN Clock
 */
uint32_t CLOCK_GetMCanClkFreq(uint32_t MCanSel)
{
    uint32_t freq = 0U;
    switch (MCanSel)
    {
        case 0U:
            freq = CLOCK_GetCoreSysClkFreq() / ((SYSCON->CAN0CLKDIV & 0xffU) + 1U);
            break;
        case 1U:
            freq = CLOCK_GetCoreSysClkFreq() / ((SYSCON->CAN1CLKDIV & 0xffU) + 1U);
            break;

        default:
            freq = 0U;
            break;
    }

    return freq;
}

/* Get FLEXCOMM Clk */
/*! brief	Return Frequency of Flexcomm functional Clock
 *  return	Frequency of Flexcomm functional Clock
 */
uint32_t CLOCK_GetFlexCommClkFreq(uint32_t id)
{
    uint32_t freq = 0U;

    if (id != 10U)
    {
        switch (SYSCON->FCLKSEL[id])
        {
            case 0U:
                freq = CLOCK_GetFro12MFreq();
                break;
            case 1U:
                freq = CLOCK_GetFroHfFreq() / ((SYSCON->FROHFDIV & 0xffu) + 1U);
                break;
            case 2U:
                freq = CLOCK_GetAudioPllOutFreq();
                break;
            case 3U:
                freq = CLOCK_GetI2SMClkFreq();
                break;
            case 4U:
                freq = CLOCK_GetFrgClkFreq();
                break;

            default:
                freq = 0U;
                break;
        }
    }
    else
    {
        switch (SYSCON->FCLKSEL10)
        {
            case 0U:
                freq = CLOCK_GetCoreSysClkFreq();
                break;
            case 1U:
                freq = CLOCK_GetPllOutFreq();
                break;
            case 2U:
                freq = CLOCK_GetUsbPllOutFreq();
                break;
            case 3U:
                freq = CLOCK_GetFroHfFreq();
                break;
            case 4U:
                freq = CLOCK_GetAudioPllOutFreq();
                break;
            default:
                freq = 0U;
                break;
        }
    }

    return freq;
}

/* Get FRG Clk */
uint32_t CLOCK_GetFRGInputClock(void)
{
    uint32_t freq = 0U;

    switch (SYSCON->FRGCLKSEL)
    {
        case 0U:
            freq = CLOCK_GetCoreSysClkFreq();
            break;
        case 1U:
            freq = CLOCK_GetPllOutFreq();
            break;
        case 2U:
            freq = CLOCK_GetFro12MFreq();
            break;
        case 3U:
            freq = CLOCK_GetFroHfFreq();
            break;

        default:
            freq = 0U;
            break;
    }

    return freq;
}

/* Get FRG Clk */
/*! brief  Return Frequency of frg
 *  return Frequency of FRG
 */
uint32_t CLOCK_GetFrgClkFreq(void)
{
    uint32_t freq = 0U;

    if ((SYSCON->FRGCTRL & SYSCON_FRGCTRL_DIV_MASK) == SYSCON_FRGCTRL_DIV_MASK)
    {
        freq = (uint32_t)(((uint64_t)CLOCK_GetFRGInputClock() * (SYSCON_FRGCTRL_DIV_MASK + 1U)) /
                          ((SYSCON_FRGCTRL_DIV_MASK + 1U) +
                           ((SYSCON->FRGCTRL & SYSCON_FRGCTRL_MULT_MASK) >> SYSCON_FRGCTRL_MULT_SHIFT)));
    }
    else
    {
        freq = 0U;
    }

    return freq;
}

/* Get FRG Clk */
/*! brief  Return Frequency of dmic
 *  return Frequency of DMIC
 */
uint32_t CLOCK_GetDmicClkFreq(void)
{
    uint32_t freq = 0U;

    switch (SYSCON->DMICCLKSEL)
    {
        case 0U:
            freq = CLOCK_GetFro12MFreq();
            break;
        case 1U:
            freq = CLOCK_GetFroHfFreq();
            break;
        case 2U:
            freq = CLOCK_GetPllOutFreq();
            break;
        case 3U:
            freq = CLOCK_GetI2SMClkFreq();
            break;
        case 4U:
            freq = CLOCK_GetCoreSysClkFreq();
            break;
        case 5U:
            freq = CLOCK_GetWdtOscFreq();
            break;
        default:
            freq = 0U;
            break;
    }

    return freq / ((SYSCON->DMICCLKDIV & 0xffU) + 1U);
    ;
}

/* Set FRG Clk */
uint32_t CLOCK_SetFRGClock(uint32_t freq)
{
    assert(0UL != freq);

    uint32_t input = CLOCK_GetFRGInputClock();
    uint32_t mul;

    if ((freq > 48000000U) || (freq > input) || (input / freq >= 2U))
    {
        /* FRG output frequency should be less than equal to 48MHz */
        return 0U;
    }
    else
    {
        mul             = (uint32_t)((((uint64_t)input - freq) * 256U) / ((uint64_t)freq));
        SYSCON->FRGCTRL = (mul << SYSCON_FRGCTRL_MULT_SHIFT) | SYSCON_FRGCTRL_DIV_MASK;
        return 1U;
    }
}

/* Set IP Clk */
/*! brief	Return Frequency of selected clock
 *  return	Frequency of selected clock
 */
uint32_t CLOCK_GetFreq(clock_name_t clockName)
{
    uint32_t freq;
    switch (clockName)
    {
        case kCLOCK_CoreSysClk:
            freq = CLOCK_GetCoreSysClkFreq();
            break;
        case kCLOCK_BusClk:
            freq = CLOCK_GetCoreSysClkFreq() / ((SYSCON->AHBCLKDIV & 0xffU) + 1U);
            break;
        case kCLOCK_ClockOut:
            freq = CLOCK_GetClockOutClkFreq();
            break;
        case kCLOCK_Mclk:
            freq = CLOCK_GetMclkClkFreq();
            break;
        case kCLOCK_FroHf:
            freq = CLOCK_GetFroHfFreq();
            break;
        case kCLOCK_Fro12M:
            freq = CLOCK_GetFro12MFreq();
            break;
        case kCLOCK_ExtClk:
            freq = CLOCK_GetExtClkFreq();
            break;
        case kCLOCK_PllOut:
            freq = CLOCK_GetPllOutFreq();
            break;
        case kCLOCK_WdtOsc:
            freq = CLOCK_GetWdtOscFreq();
            break;
        case kCLOCK_Frg:
            freq = CLOCK_GetFrgClkFreq();
            break;

        case kCLOCK_AsyncApbClk:
            freq = CLOCK_GetAsyncApbClkFreq();
            break;
        default:
            freq = 0U;
            break;
    }

    return freq;
}

/* Find encoded NDEC value for raw N value, max N = NVALMAX */
static uint32_t pllEncodeN(uint32_t N)
{
    uint32_t x, i;

    /* Find NDec */
    switch (N)
    {
        case 0U:
            x = 0x3FFU;
            break;

        case 1U:
            x = 0x302U;
            break;

        case 2U:
            x = 0x202U;
            break;

        default:
            x = 0x080U;
            for (i = N; i <= NVALMAX; i++)
            {
                x = (((x ^ (x >> 2U) ^ (x >> 3U) ^ (x >> 4U)) & 1U) << 7U) | ((x >> 1U) & 0x7FU);
            }
            break;
    }

    return x & (PLL_NDEC_VAL_M >> PLL_NDEC_VAL_P);
}

/* Find decoded N value for raw NDEC value */
static uint32_t pllDecodeN(uint32_t NDEC)
{
    uint32_t n, x, i;

    /* Find NDec */
    switch (NDEC)
    {
        case 0x3FFU:
            n = 0U;
            break;

        case 0x302U:
            n = 1U;
            break;

        case 0x202U:
            n = 2U;
            break;

        default:
            x = 0x080U;
            n = 0xFFFFFFFFU;
            for (i = NVALMAX; i >= 3U; i--)
            {
                x = (((x ^ (x >> 2U) ^ (x >> 3U) ^ (x >> 4U)) & 1U) << 7U) | ((x >> 1U) & 0x7FU);
                if ((x & (PLL_NDEC_VAL_M >> PLL_NDEC_VAL_P)) == NDEC)
                {
                    /* Decoded value of NDEC */
                    n = i;
                    break;
                }
            }
            break;
    }

    return n;
}

/* Find encoded PDEC value for raw P value, max P = PVALMAX */
static uint32_t pllEncodeP(uint32_t P)
{
    uint32_t x, i;

    /* Find PDec */
    switch (P)
    {
        case 0U:
            x = 0x7FU;
            break;

        case 1U:
            x = 0x62U;
            break;

        case 2U:
            x = 0x42U;
            break;

        default:
            x = 0x10U;
            for (i = P; i <= PVALMAX; i++)
            {
                x = (((x ^ (x >> 2U)) & 1U) << 4U) | ((x >> 1U) & 0xFU);
            }
            break;
    }

    return x & (PLL_PDEC_VAL_M >> PLL_PDEC_VAL_P);
}

/* Find decoded P value for raw PDEC value */
static uint32_t pllDecodeP(uint32_t PDEC)
{
    uint32_t p, x, i;

    /* Find PDec */
    switch (PDEC)
    {
        case 0x7FU:
            p = 0U;
            break;

        case 0x62U:
            p = 1U;
            break;

        case 0x42U:
            p = 2U;
            break;

        default:
            x = 0x10U;
            p = 0xFFFFFFFFU;
            for (i = PVALMAX; i >= 3U; i--)
            {
                x = (((x ^ (x >> 2U)) & 1U) << 4U) | ((x >> 1U) & 0xFU);
                if ((x & (PLL_PDEC_VAL_M >> PLL_PDEC_VAL_P)) == PDEC)
                {
                    /* Decoded value of PDEC */
                    p = i;
                    break;
                }
            }
            break;
    }

    return p;
}

/* Find encoded MDEC value for raw M value, max M = MVALMAX */
static uint32_t pllEncodeM(uint32_t M)
{
    uint32_t i, x;

    /* Find MDec */
    switch (M)
    {
        case 0U:
            x = 0x1FFFFU;
            break;

        case 1U:
            x = 0x18003U;
            break;

        case 2U:
            x = 0x10003U;
            break;

        default:
            x = 0x04000U;
            for (i = M; i <= MVALMAX; i++)
            {
                x = (((x ^ (x >> 1U)) & 1U) << 14U) | ((x >> 1U) & 0x3FFFU);
            }
            break;
    }

    return x & (PLL_MDEC_VAL_M >> PLL_MDEC_VAL_P);
}

/* Find decoded M value for raw MDEC value */
static uint32_t pllDecodeM(uint32_t MDEC)
{
    uint32_t m, i, x;

    /* Find MDec */
    switch (MDEC)
    {
        case 0x1FFFFU:
            m = 0U;
            break;

        case 0x18003U:
            m = 1U;
            break;

        case 0x10003U:
            m = 2U;
            break;

        default:
            x = 0x04000U;
            m = 0xFFFFFFFFU;
            for (i = MVALMAX; i >= 3U; i--)
            {
                x = (((x ^ (x >> 1U)) & 1U) << 14U) | ((x >> 1U) & 0x3FFFU);
                if ((x & (PLL_MDEC_VAL_M >> PLL_MDEC_VAL_P)) == MDEC)
                {
                    /* Decoded value of MDEC */
                    m = i;
                    break;
                }
            }
            break;
    }

    return m;
}

/* Find SELP, SELI, and SELR values for raw M value, max M = MVALMAX */
static void pllFindSel(uint32_t M, uint32_t *pSelP, uint32_t *pSelI, uint32_t *pSelR)
{
    /* bandwidth: compute selP from Multiplier */
    if (M < 60U)
    {
        *pSelP = (M >> 1U) + 1U;
    }
    else
    {
        *pSelP = PVALMAX - 1U;
    }

    /* bandwidth: compute selI from Multiplier */
    if (M > 16384U)
    {
        *pSelI = 1U;
    }
    else if (M > 8192U)
    {
        *pSelI = 2U;
    }
    else if (M > 2048U)
    {
        *pSelI = 4U;
    }
    else if (M >= 501U)
    {
        *pSelI = 8U;
    }
    else if (M >= 60U)
    {
        *pSelI = 4U * (1024U / (M + 9U));
    }
    else
    {
        *pSelI = (M & 0x3CU) + 4U;
    }

    if (*pSelI > ((0x3FUL << SYSCON_SYSPLLCTRL_SELI_SHIFT) >> SYSCON_SYSPLLCTRL_SELI_SHIFT))
    {
        *pSelI = ((0x3FUL << SYSCON_SYSPLLCTRL_SELI_SHIFT) >> SYSCON_SYSPLLCTRL_SELI_SHIFT);
    }

    *pSelR = 0U;
}

/* Get predivider (N) from PLL NDEC setting */
static uint32_t findPllPreDiv(uint32_t ctrlReg, uint32_t nDecReg)
{
    uint32_t preDiv = 1;

    /* Direct input is not used? */
    if ((ctrlReg & (1UL << SYSCON_SYSPLLCTRL_DIRECTI_SHIFT)) == 0U)
    {
        /* Decode NDEC value to get (N) pre divider */
        preDiv = pllDecodeN(nDecReg & 0x3FFU);
        if (preDiv == 0U)
        {
            preDiv = 1U;
        }
    }

    /* Adjusted by 1, directi is used to bypass */
    return preDiv;
}

/* Get postdivider (P) from PLL PDEC setting */
static uint32_t findPllPostDiv(uint32_t ctrlReg, uint32_t pDecReg)
{
    uint32_t postDiv = 1U;

    /* Direct input is not used? */
    if ((ctrlReg & SYSCON_SYSPLLCTRL_DIRECTO_MASK) == 0U)
    {
        /* Decode PDEC value to get (P) post divider */
        postDiv = 2U * pllDecodeP(pDecReg & 0x7FU);
        if (postDiv == 0U)
        {
            postDiv = 2U;
        }
    }

    /* Adjusted by 1, directo is used to bypass */
    return postDiv;
}

/* Get multiplier (M) from PLL MDEC and BYPASS_FBDIV2 settings */
static uint32_t findPllMMult(uint32_t ctrlReg, uint32_t mDecReg)
{
    uint32_t mMult = 1U;

    /* Decode MDEC value to get (M) multiplier */
    mMult = pllDecodeM(mDecReg & 0x1FFFFU);

    if (mMult == 0U)
    {
        mMult = 1U;
    }

    return mMult;
}

/* Calculate the powerTimes' power of 2 */
static uint32_t power2Cal(uint32_t powerTimes)
{
    uint32_t ret = 1U;
    uint32_t i;
    for (i = 0; i < powerTimes; i++)
    {
        ret *= 2U;
    }

    return ret;
}

/* Convert the binary to fractional part */
static double Binary2Fractional(uint32_t binaryPart)
{
    double fractional = 0.0;
    for (uint32_t i = 0U; i <= 14U; i++)
    {
        fractional += (double)(uint32_t)((binaryPart >> i) & 0x1U) / (double)(uint32_t)power2Cal(15U - i);
    }
    return fractional;
}

/* Find greatest common divisor between m and n */
static uint32_t FindGreatestCommonDivisor(uint32_t m, uint32_t n)
{
    uint32_t tmp;

    while (n != 0U)
    {
        tmp = n;
        n   = m % n;
        m   = tmp;
    }

    return m;
}

/*
 * Set PLL output based on desired output rate.
 * In this function, the it calculates the PLL setting for output frequency from input clock
 * frequency. The calculation would cost a few time. So it is not recommaned to use it frequently.
 * the "pllctrl", "pllndec", "pllpdec", "pllmdec" would updated in this function.
 */
static pll_error_t CLOCK_GetPllConfigInternal(uint32_t finHz, uint32_t foutHz, pll_setup_t *pSetup)
{
    uint32_t nDivOutHz, fccoHz, multFccoDiv;
    uint32_t pllPreDivider, pllMultiplier, pllPostDivider;
    uint32_t pllDirectInput, pllDirectOutput;
    uint32_t pllSelP, pllSelI, pllSelR, uplimoff;

    /* Baseline parameters (no input or output dividers) */
    pllPreDivider   = 1U; /* 1 implies pre-divider will be disabled */
    pllPostDivider  = 0U; /* 0 implies post-divider will be disabled */
    pllDirectOutput = 1U;
    multFccoDiv     = 2U;

    /* Verify output rate parameter */
    if (foutHz > PLL_MAX_CCO_FREQ_MHZ)
    {
        /* Maximum PLL output with post divider=1 cannot go above this frequency */
        return kStatus_PLL_OutputTooHigh;
    }
    if (foutHz < (PLL_MIN_CCO_FREQ_MHZ / (PVALMAX << 1U)))
    {
        /* Minmum PLL output with maximum post divider cannot go below this frequency */
        return kStatus_PLL_OutputTooLow;
    }

    /* Verify input rate parameter */
    if (finHz < PLL_LOWER_IN_LIMIT)
    {
        /* Input clock into the PLL cannot be lower than this */
        return kStatus_PLL_InputTooLow;
    }

    /* Find the optimal CCO frequency for the output and input that
       will keep it inside the PLL CCO range. This may require
       tweaking the post-divider for the PLL. */
    fccoHz = foutHz;
    while (fccoHz < PLL_MIN_CCO_FREQ_MHZ)
    {
        /* CCO output is less than minimum CCO range, so the CCO output
           needs to be bumped up and the post-divider is used to bring
           the PLL output back down. */
        pllPostDivider++;
        if (pllPostDivider > PVALMAX)
        {
            return kStatus_PLL_OutsideIntLimit;
        }

        /* Target CCO goes up, PLL output goes down */
        fccoHz          = foutHz * (pllPostDivider * 2U);
        pllDirectOutput = 0U;
    }

    /* Determine if a pre-divider is needed to get the best frequency */
    if ((finHz > PLL_LOWER_IN_LIMIT) && (fccoHz >= finHz))
    {
        uint32_t a = FindGreatestCommonDivisor(fccoHz, (multFccoDiv * finHz));

        if (a > 20000U)
        {
            a = (multFccoDiv * finHz) / a;
            if ((a != 0U) && (a < PLL_MAX_N_DIV))
            {
                pllPreDivider = a;
            }
        }
    }

    /* Bypass pre-divider hardware if pre-divider is 1 */
    if (pllPreDivider > 1U)
    {
        pllDirectInput = 0U;
    }
    else
    {
        pllDirectInput = 1U;
    }

    /* Determine PLL multipler */
    nDivOutHz     = (finHz / pllPreDivider);
    pllMultiplier = (fccoHz / nDivOutHz) / multFccoDiv;

    /* Find optimal values for filter */
    /* Will bumping up M by 1 get us closer to the desired CCO frequency? */
    if ((nDivOutHz * ((multFccoDiv * pllMultiplier * 2U) + 1U)) < (fccoHz * 2U))
    {
        pllMultiplier++;
    }

    /* Setup filtering */
    pllFindSel(pllMultiplier, &pllSelP, &pllSelI, &pllSelR);
    uplimoff = 0U;

    /* Get encoded value for M (mult) and use manual filter, disable SS mode */
    pSetup->pllmdec = PLL_MDEC_VAL_SET(pllEncodeM(pllMultiplier));

    /* Get encoded values for N (prediv) and P (postdiv) */
    pSetup->pllndec = PLL_NDEC_VAL_SET(pllEncodeN(pllPreDivider));
    pSetup->pllpdec = PLL_PDEC_VAL_SET(pllEncodeP(pllPostDivider));

    /* PLL control */
    pSetup->pllctrl = (pllSelR << SYSCON_SYSPLLCTRL_SELR_SHIFT) |           /* Filter coefficient */
                      (pllSelI << SYSCON_SYSPLLCTRL_SELI_SHIFT) |           /* Filter coefficient */
                      (pllSelP << SYSCON_SYSPLLCTRL_SELP_SHIFT) |           /* Filter coefficient */
                      (0UL << SYSCON_SYSPLLCTRL_BYPASS_SHIFT) |             /* PLL bypass mode disabled */
                      (uplimoff << SYSCON_SYSPLLCTRL_UPLIMOFF_SHIFT) |      /* SS/fractional mode disabled */
                      (pllDirectInput << SYSCON_SYSPLLCTRL_DIRECTI_SHIFT) | /* Bypass pre-divider? */
                      (pllDirectOutput << SYSCON_SYSPLLCTRL_DIRECTO_SHIFT); /* Bypass post-divider? */

    return kStatus_PLL_Success;
}

#if (defined(CLOCK_USR_CFG_PLL_CONFIG_CACHE_COUNT) && CLOCK_USR_CFG_PLL_CONFIG_CACHE_COUNT)
/* Alloct the static buffer for cache. */
static pll_setup_t gPllSetupCacheStruct[CLOCK_USR_CFG_PLL_CONFIG_CACHE_COUNT];
static uint32_t gFinHzCache[CLOCK_USR_CFG_PLL_CONFIG_CACHE_COUNT]  = {0};
static uint32_t gFoutHzCache[CLOCK_USR_CFG_PLL_CONFIG_CACHE_COUNT] = {0};
static uint32_t gPllSetupCacheIdx                                  = 0U;
#endif /* CLOCK_USR_CFG_PLL_CONFIG_CACHE_COUNT */

/*
 * Calculate the PLL setting values from input clock freq to output freq.
 */
static pll_error_t CLOCK_GetPllConfig(uint32_t finHz, uint32_t foutHz, pll_setup_t *pSetup)
{
    pll_error_t retErr;
#if (defined(CLOCK_USR_CFG_PLL_CONFIG_CACHE_COUNT) && CLOCK_USR_CFG_PLL_CONFIG_CACHE_COUNT)
    uint32_t i;

    for (i = 0U; i < CLOCK_USR_CFG_PLL_CONFIG_CACHE_COUNT; i++)
    {
        if ((finHz == gFinHzCache[i]) && (foutHz == gFoutHzCache[i]))
        {
            /* Hit the target in cache buffer. */
            pSetup->pllctrl = gPllSetupCacheStruct[i].pllctrl;
            pSetup->pllndec = gPllSetupCacheStruct[i].pllndec;
            pSetup->pllpdec = gPllSetupCacheStruct[i].pllpdec;
            pSetup->pllmdec = gPllSetupCacheStruct[i].pllmdec;
            retErr          = kStatus_PLL_Success;
            break;
        }
    }

    if (i < CLOCK_USR_CFG_PLL_CONFIG_CACHE_COUNT)
    {
        return retErr;
    }
#endif /* CLOCK_USR_CFG_PLL_CONFIG_CACHE_COUNT */

    /* No cache or did not hit the cache. */
    retErr = CLOCK_GetPllConfigInternal(finHz, foutHz, pSetup);

#if (defined(CLOCK_USR_CFG_PLL_CONFIG_CACHE_COUNT) && CLOCK_USR_CFG_PLL_CONFIG_CACHE_COUNT)
    if (kStatus_PLL_Success == retErr)
    {
        /* Cache the most recent calulation result into buffer. */
        gFinHzCache[gPllSetupCacheIdx]  = finHz;
        gFoutHzCache[gPllSetupCacheIdx] = foutHz;

        gPllSetupCacheStruct[gPllSetupCacheIdx].pllctrl = pSetup->pllctrl;
        gPllSetupCacheStruct[gPllSetupCacheIdx].pllndec = pSetup->pllndec;
        gPllSetupCacheStruct[gPllSetupCacheIdx].pllpdec = pSetup->pllpdec;
        gPllSetupCacheStruct[gPllSetupCacheIdx].pllmdec = pSetup->pllmdec;
        /* Update the index for next available buffer. */
        gPllSetupCacheIdx = (gPllSetupCacheIdx + 1U) % CLOCK_USR_CFG_PLL_CONFIG_CACHE_COUNT;
    }
#endif /* CLOCK_USR_CFG_PLL_CONFIG_CACHE_COUNT */

    return retErr;
}

/* Update SYSTEM PLL rate variable */
static void CLOCK_GetSystemPLLOutFromSetupUpdate(pll_setup_t *pSetup)
{
    s_Pll_Freq = CLOCK_GetSystemPLLOutFromSetup(pSetup);
}

/* Update AUDIO PLL rate variable */
static void CLOCK_GetAudioPLLOutFromSetupUpdate(pll_setup_t *pSetup)
{
    s_Audio_Pll_Freq = CLOCK_GetAudioPLLOutFromSetup(pSetup);
}

/* Update AUDIO Fractional PLL rate variable */
static void CLOCK_GetAudioPLLOutFromAudioFracSetupUpdate(pll_setup_t *pSetup)
{
    s_Audio_Pll_Freq = CLOCK_GetAudioPLLOutFromFractSetup(pSetup);
}

/* Update USB PLL rate variable */
static void CLOCK_GetUsbPLLOutFromSetupUpdate(const usb_pll_setup_t *pSetup)
{
    s_Usb_Pll_Freq = CLOCK_GetUsbPLLOutFromSetup(pSetup);
}

/* Return System PLL input clock rate */
/*! brief	Return System PLL input clock rate
 *  return	System PLL input clock rate
 */
uint32_t CLOCK_GetSystemPLLInClockRate(void)
{
    uint32_t clkRate = 0U;

    switch ((SYSCON->SYSPLLCLKSEL & SYSCON_SYSPLLCLKSEL_SEL_MASK))
    {
        case 0x00U:
            clkRate = CLK_FRO_12MHZ;
            break;

        case 0x01U:
            clkRate = CLOCK_GetExtClkFreq();
            break;

        case 0x02U:
            clkRate = CLOCK_GetWdtOscFreq();
            break;

        case 0x03U:
            clkRate = CLOCK_GetOsc32KFreq();
            break;

        default:
            clkRate = 0U;
            break;
    }

    return clkRate;
}

/* Return Audio PLL input clock rate */
/*! brief	Return Audio PLL input clock rate
 *  return	Audio PLL input clock rate
 */
uint32_t CLOCK_GetAudioPLLInClockRate(void)
{
    uint32_t clkRate = 0U;

    switch ((SYSCON->AUDPLLCLKSEL & SYSCON_AUDPLLCLKSEL_SEL_MASK))
    {
        case 0x00U:
            clkRate = CLK_FRO_12MHZ;
            break;

        case 0x01U:
            clkRate = CLOCK_GetExtClkFreq();
            break;

        default:
            clkRate = 0U;
            break;
    }

    return clkRate;
}

/* Return System PLL output clock rate from setup structure */
/*! brief	Return System PLL output clock rate from setup structure
 *  param	pSetup	: Pointer to a PLL setup structure
 *  return	System PLL output clock rate the setup structure will generate
 */
uint32_t CLOCK_GetSystemPLLOutFromSetup(pll_setup_t *pSetup)
{
    uint32_t prediv, postdiv, mMult, inPllRate;
    uint64_t workRate;

    inPllRate = CLOCK_GetSystemPLLInClockRate();
    /* If the PLL is bypassed, PLL would not be used and the output of PLL module would just be the input clock*/
    if ((pSetup->pllctrl & (SYSCON_SYSPLLCTRL_BYPASS_MASK)) == 0U)
    {
        /* PLL is not in bypass mode, get pre-divider, and M divider, post-divider. */
        /*
         * 1. Pre-divider
         * Pre-divider is only available when the DIRECTI is disabled.
         */
        if (0U == (pSetup->pllctrl & SYSCON_SYSPLLCTRL_DIRECTI_MASK))
        {
            prediv = findPllPreDiv(pSetup->pllctrl, pSetup->pllndec);
        }
        else
        {
            prediv = 1U; /* The pre-divider is bypassed. */
        }
        /*
         * 2. Post-divider
         * Post-divider is only available when the DIRECTO is disabled.
         */
        if (0U == (pSetup->pllctrl & SYSCON_SYSPLLCTRL_DIRECTO_MASK))
        {
            postdiv = findPllPostDiv(pSetup->pllctrl, pSetup->pllpdec);
        }
        else
        {
            postdiv = 1U; /* The post-divider is bypassed. */
        }
        /* Adjust input clock */
        inPllRate = inPllRate / prediv;

        /* MDEC used for rate */
        mMult    = findPllMMult(pSetup->pllctrl, pSetup->pllmdec);
        workRate = (uint64_t)inPllRate * (uint64_t)mMult;

        workRate = workRate / ((uint64_t)postdiv);
        workRate = workRate * 2U; /* SYS PLL hardware cco is divide by 2 before to M-DIVIDER*/
    }
    else
    {
        /* In bypass mode */
        workRate = (uint64_t)inPllRate;
    }

    return (uint32_t)workRate;
}

/* Return Usb PLL output clock rate from setup structure */
/*! brief	Return System USB PLL output clock rate from setup structure
 *  param	pSetup	: Pointer to a PLL setup structure
 *  return	System PLL output clock rate the setup structure will generate
 */
uint32_t CLOCK_GetUsbPLLOutFromSetup(const usb_pll_setup_t *pSetup)
{
    uint32_t nsel, psel, msel, inPllRate;
    uint64_t workRate;
    inPllRate = CLOCK_GetExtClkFreq();
    msel      = pSetup->msel;
    psel      = pSetup->psel;
    nsel      = pSetup->nsel;

    /* Make sure the PSEL is correct. */
    if (0U == SWITCH_USB_PSEL(psel))
    {
        return 0UL;
    }

    if (pSetup->fbsel)
    {
        /*integer_mode: Fout = M*(Fin/N),  Fcco = 2*P*M*(Fin/N) */
        workRate = ((uint64_t)inPllRate) * ((uint64_t)msel + 1U) / ((uint64_t)nsel + 1U);
    }
    else
    {
        /* non integer_mode: Fout = M*(Fin/N)/(2*P), Fcco = M * (Fin/N) */
        workRate = ((uint64_t)inPllRate / ((uint64_t)nsel + 1U)) * (msel + 1U) / (2U * SWITCH_USB_PSEL(psel));
    }

    return (uint32_t)workRate;
}

/* Return Audio PLL output clock rate from setup structure */
/*! brief	Return System AUDIO PLL output clock rate from setup structure
 *  param	pSetup	: Pointer to a PLL setup structure
 *  return	System PLL output clock rate the setup structure will generate
 */
uint32_t CLOCK_GetAudioPLLOutFromSetup(pll_setup_t *pSetup)
{
    uint32_t prediv, postdiv, mMult, inPllRate;
    uint64_t workRate;

    inPllRate = CLOCK_GetAudioPLLInClockRate();
    if ((pSetup->pllctrl & (1UL << SYSCON_SYSPLLCTRL_BYPASS_SHIFT)) == 0U)
    {
        /* PLL is not in bypass mode, get pre-divider, and M divider, post-divider. */
        /*
         * 1. Pre-divider
         * Pre-divider is only available when the DIRECTI is disabled.
         */
        if (0U == (pSetup->pllctrl & SYSCON_AUDPLLCTRL_DIRECTI_MASK))
        {
            prediv = findPllPreDiv(pSetup->pllctrl, pSetup->pllndec);
        }
        else
        {
            prediv = 1U; /* The pre-divider is bypassed. */
        }
        /*
         * 2. Post-divider
         * Post-divider is only available when the DIRECTO is disabled.
         */
        if (0U == (pSetup->pllctrl & SYSCON_AUDPLLCTRL_DIRECTO_MASK))
        {
            postdiv = findPllPostDiv(pSetup->pllctrl, pSetup->pllpdec);
        }
        else
        {
            postdiv = 1U; /* The post-divider is bypassed. */
        }
        /* Adjust input clock */
        inPllRate = inPllRate / prediv;

        /* MDEC used for rate */
        mMult    = findPllMMult(pSetup->pllctrl, pSetup->pllmdec);
        workRate = (uint64_t)inPllRate * (uint64_t)mMult;

        workRate = workRate / ((uint64_t)postdiv);
        workRate = workRate * 2U; /* SYS PLL hardware cco is divide by 2 before to M-DIVIDER*/
    }
    else
    {
        /* In bypass mode */
        workRate = (uint64_t)inPllRate;
    }

    return (uint32_t)workRate;
}

/* Return Audio PLL output clock rate from audio fractioanl setup structure */
/*! brief	Return System AUDIO PLL output clock rate from audio fractioanl setup structure
 *  param	pSetup	: Pointer to a PLL setup structure
 *  return	System PLL output clock rate the setup structure will generate
 */
uint32_t CLOCK_GetAudioPLLOutFromFractSetup(pll_setup_t *pSetup)
{
    uint32_t prediv, postdiv, inPllRate;
    double workRate, mMultFactional;

    inPllRate = CLOCK_GetAudioPLLInClockRate();
    if ((pSetup->pllctrl & (1UL << SYSCON_SYSPLLCTRL_BYPASS_SHIFT)) == 0U)
    {
        /* PLL is not in bypass mode, get pre-divider, and M divider, post-divider. */
        /*
         * 1. Pre-divider
         * Pre-divider is only available when the DIRECTI is disabled.
         */
        if (0U == (pSetup->pllctrl & SYSCON_AUDPLLCTRL_DIRECTI_MASK))
        {
            prediv = findPllPreDiv(pSetup->pllctrl, pSetup->pllndec);
        }
        else
        {
            prediv = 1U; /* The pre-divider is bypassed. */
        }
        /*
         * 2. Post-divider
         * Post-divider is only available when the DIRECTO is disabled.
         */
        if (0U == (pSetup->pllctrl & SYSCON_AUDPLLCTRL_DIRECTO_MASK))
        {
            postdiv = findPllPostDiv(pSetup->pllctrl, pSetup->pllpdec);
        }
        else
        {
            postdiv = 1U; /* The post-divider is bypassed. */
        }
        /* Adjust input clock */
        inPllRate = inPllRate / prediv;

        mMultFactional = (double)(uint32_t)(pSetup->audpllfrac >> 15) +
                         (double)(uint32_t)Binary2Fractional(pSetup->audpllfrac & 0x7FFFU);
        workRate = (double)inPllRate * (double)mMultFactional;

        workRate = workRate / ((double)postdiv);
        workRate = workRate * 2.0; /* SYS PLL hardware cco is divide by 2 before to M-DIVIDER*/
    }
    else
    {
        /* In bypass mode */
        workRate = (double)(uint64_t)inPllRate;
    }

    return (uint32_t)workRate;
}

/* Set the current PLL Rate */
/*! brief Store the current PLL rate
 *  param	rate: Current rate of the PLL
 *  return	Nothing
 **/
void CLOCK_SetStoredPLLClockRate(uint32_t rate)
{
    s_Pll_Freq = rate;
}

/* Set the current Audio PLL Rate */
/*! brief Store the current AUDIO PLL rate
 *  param	rate: Current rate of the PLL
 *  return	Nothing
 **/
void CLOCK_SetStoredAudioPLLClockRate(uint32_t rate)
{
    s_Audio_Pll_Freq = rate;
}

/* Set the current Usb PLL Rate */
void CLOCK_SetStoredUsbPLLClockRate(uint32_t rate)
{
    s_Usb_Pll_Freq = rate;
}

/* Return System PLL output clock rate */
/*! brief	Return System PLL output clock rate
 *  param	recompute	: Forces a PLL rate recomputation if true
 *  return	System PLL output clock rate
 *  note	The PLL rate is cached in the driver in a variable as
 *  the rate computation function can take some time to perform. It
 *  is recommended to use 'false' with the 'recompute' parameter.
 */
uint32_t CLOCK_GetSystemPLLOutClockRate(bool recompute)
{
    pll_setup_t Setup;
    uint32_t rate;

    if ((recompute) || (s_Pll_Freq == 0U))
    {
        Setup.pllctrl = SYSCON->SYSPLLCTRL;
        Setup.pllndec = SYSCON->SYSPLLNDEC;
        Setup.pllpdec = SYSCON->SYSPLLPDEC;
        Setup.pllmdec = SYSCON->SYSPLLMDEC;

        CLOCK_GetSystemPLLOutFromSetupUpdate(&Setup);
    }

    rate = s_Pll_Freq;

    return rate;
}

/* Return AUDIO PLL output clock rate */
/*! brief	Return System AUDIO PLL output clock rate
 *  param	recompute	: Forces a AUDIO PLL rate recomputation if true
 *  return	System AUDIO PLL output clock rate
 *  note	The AUDIO PLL rate is cached in the driver in a variable as
 *  the rate computation function can take some time to perform. It
 *  is recommended to use 'false' with the 'recompute' parameter.
 */
uint32_t CLOCK_GetAudioPLLOutClockRate(bool recompute)
{
    pll_setup_t Setup;
    uint32_t rate;

    if ((recompute) || (s_Audio_Pll_Freq == 0U))
    {
        Setup.pllctrl = SYSCON->AUDPLLCTRL;
        Setup.pllndec = SYSCON->AUDPLLNDEC;
        Setup.pllpdec = SYSCON->AUDPLLPDEC;
        Setup.pllmdec = SYSCON->AUDPLLMDEC;

        CLOCK_GetAudioPLLOutFromSetupUpdate(&Setup);
    }

    rate = s_Audio_Pll_Freq;
    return rate;
}

/* Return USB PLL output clock rate */
uint32_t CLOCK_GetUsbPLLOutClockRate(bool recompute)
{
    usb_pll_setup_t Setup;
    uint32_t rate;

    if ((recompute) || (s_Usb_Pll_Freq == 0U))
    {
        Setup.msel  = (uint8_t)((SYSCON->USBPLLCTRL >> SYSCON_USBPLLCTRL_MSEL_SHIFT) & SYSCON_USBPLLCTRL_MSEL_MASK);
        Setup.psel  = (uint8_t)((SYSCON->USBPLLCTRL >> SYSCON_USBPLLCTRL_PSEL_SHIFT) & SYSCON_USBPLLCTRL_PSEL_MASK);
        Setup.nsel  = (uint8_t)((SYSCON->USBPLLCTRL >> SYSCON_USBPLLCTRL_NSEL_SHIFT) & SYSCON_USBPLLCTRL_NSEL_MASK);
        Setup.fbsel = (((SYSCON->USBPLLCTRL >> SYSCON_USBPLLCTRL_FBSEL_SHIFT) & SYSCON_USBPLLCTRL_FBSEL_MASK) != 0UL);
        Setup.bypass =
            (((SYSCON->USBPLLCTRL >> SYSCON_USBPLLCTRL_BYPASS_SHIFT) & SYSCON_USBPLLCTRL_BYPASS_MASK) != 0UL);
        Setup.direct =
            (((SYSCON->USBPLLCTRL >> SYSCON_USBPLLCTRL_DIRECT_SHIFT) & SYSCON_USBPLLCTRL_DIRECT_MASK) != 0UL);
        CLOCK_GetUsbPLLOutFromSetupUpdate(&Setup);
    }

    rate = s_Usb_Pll_Freq;
    return rate;
}

/* Set PLL output based on the passed PLL setup data */
/*! brief	Set PLL output based on the passed PLL setup data
 *  param	pControl	: Pointer to populated PLL control structure to generate setup with
 *  param	pSetup		: Pointer to PLL setup structure to be filled
 *  return	PLL_ERROR_SUCCESS on success, or PLL setup error code
 *  note	Actual frequency for setup may vary from the desired frequency based on the
 *  accuracy of input clocks, rounding, non-fractional PLL mode, etc.
 */
pll_error_t CLOCK_SetupPLLData(pll_config_t *pControl, pll_setup_t *pSetup)
{
    uint32_t inRate;
    pll_error_t pllError;

    /* Determine input rate for the PLL */
    if ((pControl->flags & PLL_CONFIGFLAG_USEINRATE) != 0U)
    {
        inRate = pControl->inputRate;
    }
    else
    {
        inRate = CLOCK_GetSystemPLLInClockRate();
    }

    /* PLL flag options */
    pllError        = CLOCK_GetPllConfig(inRate, pControl->desiredRate, pSetup);
    pSetup->pllRate = pControl->desiredRate;
    return pllError;
}

/* Set PLL output from PLL setup structure */
/*! brief	Set PLL output from PLL setup structure (precise frequency)
 * param	pSetup	: Pointer to populated PLL setup structure
 * param flagcfg : Flag configuration for PLL config structure
 * return	PLL_ERROR_SUCCESS on success, or PLL setup error code
 * note	This function will power off the PLL, setup the PLL with the
 * new setup data, and then optionally powerup the PLL, wait for PLL lock,
 * and adjust system voltages to the new PLL rate. The function will not
 * alter any source clocks (ie, main systen clock) that may use the PLL,
 * so these should be setup prior to and after exiting the function.
 */
pll_error_t CLOCK_SetupSystemPLLPrec(pll_setup_t *pSetup, uint32_t flagcfg)
{
    if ((SYSCON->SYSPLLCLKSEL & SYSCON_SYSPLLCLKSEL_SEL_MASK) == 0x01U)
    {
        /* Turn on the ext clock if system pll input select clk_in */
        CLOCK_Enable_SysOsc(true);
    }
    /* Enable power for PLLs */
    POWER_SetPLL();
    /* Power off PLL during setup changes */
    POWER_EnablePD(kPDRUNCFG_PD_SYS_PLL0);

    pSetup->flags = flagcfg;

    /* Write PLL setup data */
    SYSCON->SYSPLLCTRL = pSetup->pllctrl;
    SYSCON->SYSPLLNDEC = pSetup->pllndec;
    SYSCON->SYSPLLNDEC = pSetup->pllndec | (1UL << SYSCON_SYSPLLNDEC_NREQ_SHIFT); /* latch */
    SYSCON->SYSPLLPDEC = pSetup->pllpdec;
    SYSCON->SYSPLLPDEC = pSetup->pllpdec | (1UL << SYSCON_SYSPLLPDEC_PREQ_SHIFT); /* latch */
    SYSCON->SYSPLLMDEC = pSetup->pllmdec;
    SYSCON->SYSPLLMDEC = pSetup->pllmdec | (1UL << SYSCON_SYSPLLMDEC_MREQ_SHIFT); /* latch */

    /* Flags for lock or power on */
    if ((pSetup->flags & (PLL_SETUPFLAG_POWERUP | PLL_SETUPFLAG_WAITLOCK)) != 0U)
    {
        /* If turning the PLL back on, perform the following sequence to accelerate PLL lock */
        uint32_t maxCCO    = (1UL << 18U) | 0x5dd2U; /* CCO = 1.6Ghz + MDEC enabled*/
        uint32_t curSSCTRL = SYSCON->SYSPLLMDEC & ~(1UL << 17U);

        /* Initialize  and power up PLL */
        SYSCON->SYSPLLMDEC = maxCCO;
        POWER_DisablePD(kPDRUNCFG_PD_SYS_PLL0);

        /* Set mreq to activate */
        SYSCON->SYSPLLMDEC = maxCCO | (1UL << 17U);

        /* Delay for 72 uSec @ 12Mhz */
        SDK_DelayAtLeastUs(72U, SDK_DEVICE_MAXIMUM_CPU_CLOCK_FREQUENCY);

        /* clear mreq to prepare for restoring mreq */
        SYSCON->SYSPLLMDEC = curSSCTRL;

        /* set original value back and activate */
        SYSCON->SYSPLLMDEC = curSSCTRL | (1UL << 17U);

        /* Enable peripheral states by setting low */
        POWER_DisablePD(kPDRUNCFG_PD_SYS_PLL0);
    }
    if ((pSetup->flags & PLL_SETUPFLAG_WAITLOCK) != 0U)
    {
        while (CLOCK_IsSystemPLLLocked() == false)
        {
        }
    }

    /* Update current programmed PLL rate var */
    CLOCK_GetSystemPLLOutFromSetupUpdate(pSetup);

    /* System voltage adjustment, occurs prior to setting main system clock */
    if ((pSetup->flags & PLL_SETUPFLAG_ADGVOLT) != 0U)
    {
        POWER_SetVoltageForFreq(s_Pll_Freq);
    }

    return kStatus_PLL_Success;
}

/* Set AUDIO PLL output from AUDIO PLL setup structure */
/*! brief	Set AUDIO PLL output from AUDIOPLL setup structure (precise frequency)
 * param	pSetup	: Pointer to populated PLL setup structure
 * param flagcfg : Flag configuration for PLL config structure
 * return	PLL_ERROR_SUCCESS on success, or PLL setup error code
 * note	This function will power off the PLL, setup the PLL with the
 * new setup data, and then optionally powerup the AUDIO PLL, wait for PLL lock,
 * and adjust system voltages to the new AUDIOPLL rate. The function will not
 * alter any source clocks (ie, main systen clock) that may use the AUDIO PLL,
 * so these should be setup prior to and after exiting the function.
 */
pll_error_t CLOCK_SetupAudioPLLPrec(pll_setup_t *pSetup, uint32_t flagcfg)
{
    if ((SYSCON->AUDPLLCLKSEL & SYSCON_AUDPLLCLKSEL_SEL_MASK) == 0x01U)
    {
        /* Turn on the ext clock if system pll input select clk_in */
        CLOCK_Enable_SysOsc(true);
    }
    /* Enable power VD3 for PLLs */
    POWER_SetPLL();
    /* Power off PLL during setup changes */
    POWER_EnablePD(kPDRUNCFG_PD_AUDIO_PLL);

    pSetup->flags = flagcfg;

    /* Write PLL setup data */
    SYSCON->AUDPLLCTRL = pSetup->pllctrl;
    SYSCON->AUDPLLNDEC = pSetup->pllndec;
    SYSCON->AUDPLLNDEC = pSetup->pllndec | (1UL << SYSCON_SYSPLLNDEC_NREQ_SHIFT); /* latch */
    SYSCON->AUDPLLPDEC = pSetup->pllpdec;
    SYSCON->AUDPLLPDEC = pSetup->pllpdec | (1UL << SYSCON_SYSPLLPDEC_PREQ_SHIFT); /* latch */
    SYSCON->AUDPLLMDEC = pSetup->pllmdec;
    SYSCON->AUDPLLMDEC = pSetup->pllmdec | (1UL << SYSCON_SYSPLLMDEC_MREQ_SHIFT); /* latch */
    SYSCON->AUDPLLFRAC = SYSCON_AUDPLLFRAC_SEL_EXT(1);                            /* disable fractional function */

    /* Flags for lock or power on */
    if ((pSetup->flags & (PLL_SETUPFLAG_POWERUP | PLL_SETUPFLAG_WAITLOCK)) != 0U)
    {
        /* If turning the PLL back on, perform the following sequence to accelerate PLL lock */
        uint32_t maxCCO    = (1UL << 18U) | 0x5dd2U; /* CCO = 1.6Ghz + MDEC enabled*/
        uint32_t curSSCTRL = SYSCON->AUDPLLMDEC & ~(1UL << 17U);

        /* Initialize  and power up PLL */
        SYSCON->AUDPLLMDEC = maxCCO;
        POWER_DisablePD(kPDRUNCFG_PD_AUDIO_PLL);

        /* Set mreq to activate */
        SYSCON->AUDPLLMDEC = maxCCO | (1UL << 17U);

        /* Delay for 72 uSec @ 12Mhz */
        SDK_DelayAtLeastUs(72U, SDK_DEVICE_MAXIMUM_CPU_CLOCK_FREQUENCY);

        /* clear mreq to prepare for restoring mreq */
        SYSCON->AUDPLLMDEC = curSSCTRL;

        /* set original value back and activate */
        SYSCON->AUDPLLMDEC = curSSCTRL | (1UL << 17U);

        /* Enable peripheral states by setting low */
        POWER_DisablePD(kPDRUNCFG_PD_AUDIO_PLL);
    }
    if ((pSetup->flags & PLL_SETUPFLAG_WAITLOCK) != 0U)
    {
        while (CLOCK_IsAudioPLLLocked() == false)
        {
        }
    }

    /* Update current programmed PLL rate var */
    CLOCK_GetAudioPLLOutFromSetupUpdate(pSetup);

    return kStatus_PLL_Success;
}

/* Set AUDIO PLL output from AUDIO PLL fractional setup structure */
/*! brief	Set AUDIO PLL output from AUDIOPLL setup structure using the Audio Fractional divider register(precise
 * frequency)
 * param	pSetup	: Pointer to populated PLL setup structure
 * param flagcfg : Flag configuration for PLL config structure
 * return	PLL_ERROR_SUCCESS on success, or PLL setup error code
 * note	This function will power off the PLL, setup the PLL with the
 * new setup data, and then optionally powerup the AUDIO PLL, wait for PLL lock,
 * and adjust system voltages to the new AUDIOPLL rate. The function will not
 * alter any source clocks (ie, main systen clock) that may use the AUDIO PLL,
 * so these should be setup prior to and after exiting the function.
 */
pll_error_t CLOCK_SetupAudioPLLPrecFract(pll_setup_t *pSetup, uint32_t flagcfg)
{
    if ((SYSCON->AUDPLLCLKSEL & SYSCON_AUDPLLCLKSEL_SEL_MASK) == 0x01U)
    {
        /* Turn on the ext clock if system pll input select clk_in */
        CLOCK_Enable_SysOsc(true);
    }
    /* Enable power VD3 for PLLs */
    POWER_SetPLL();
    /* Power off PLL during setup changes */
    POWER_EnablePD(kPDRUNCFG_PD_AUDIO_PLL);

    pSetup->flags = flagcfg;

    /* Write PLL setup data */
    SYSCON->AUDPLLCTRL = pSetup->pllctrl;
    SYSCON->AUDPLLNDEC = pSetup->pllndec;
    SYSCON->AUDPLLNDEC = pSetup->pllndec | (1UL << SYSCON_SYSPLLNDEC_NREQ_SHIFT); /* latch */
    SYSCON->AUDPLLPDEC = pSetup->pllpdec;
    SYSCON->AUDPLLPDEC = pSetup->pllpdec | (1UL << SYSCON_SYSPLLPDEC_PREQ_SHIFT); /* latch */
    SYSCON->AUDPLLMDEC = pSetup->pllmdec;
    SYSCON->AUDPLLFRAC = SYSCON_AUDPLLFRAC_SEL_EXT(0); /* enable fractional function */
    SYSCON->AUDPLLFRAC = pSetup->audpllfrac;
    SYSCON->AUDPLLFRAC = pSetup->audpllfrac | (1UL << SYSCON_AUDPLLFRAC_REQ_SHIFT);

    /* Enable peripheral states by setting low */
    POWER_DisablePD(kPDRUNCFG_PD_AUDIO_PLL);

    if ((pSetup->flags & PLL_SETUPFLAG_WAITLOCK) != 0U)
    {
        while (CLOCK_IsAudioPLLLocked() == false)
        {
        }
    }

    /* Update current programmed PLL rate var */
    CLOCK_GetAudioPLLOutFromAudioFracSetupUpdate(pSetup);

    return kStatus_PLL_Success;
}

/* Set Audio PLL output based on the passed Audio PLL setup data */
/*! brief	Set AUDIO PLL output based on the passed AUDIO PLL setup data
 *  param	pControl	: Pointer to populated PLL control structure to generate setup with
 *  param	pSetup		: Pointer to PLL setup structure to be filled
 *  return	PLL_ERROR_SUCCESS on success, or PLL setup error code
 *  note	Actual frequency for setup may vary from the desired frequency based on the
 *  accuracy of input clocks, rounding, non-fractional PLL mode, etc.
 */
pll_error_t CLOCK_SetupAudioPLLData(pll_config_t *pControl, pll_setup_t *pSetup)
{
    uint32_t inRate;
    pll_error_t pllError;

    /* Determine input rate for the PLL */
    if ((pControl->flags & PLL_CONFIGFLAG_USEINRATE) != 0U)
    {
        inRate = pControl->inputRate;
    }
    else
    {
        inRate = CLOCK_GetAudioPLLInClockRate();
    }

    /* PLL flag options */
    pllError        = CLOCK_GetPllConfig(inRate, pControl->desiredRate, pSetup);
    pSetup->pllRate = pControl->desiredRate;
    return pllError;
}

/* Setup PLL Frequency from pre-calculated value */
/**
 * brief	Set PLL output from PLL setup structure (precise frequency)
 * param	pSetup	: Pointer to populated PLL setup structure
 * return	kStatus_PLL_Success on success, or PLL setup error code
 * note	This function will power off the PLL, setup the PLL with the
 * new setup data, and then optionally powerup the PLL, wait for PLL lock,
 * and adjust system voltages to the new PLL rate. The function will not
 * alter any source clocks (ie, main systen clock) that may use the PLL,
 * so these should be setup prior to and after exiting the function.
 */
pll_error_t CLOCK_SetPLLFreq(const pll_setup_t *pSetup)
{
    if ((SYSCON->SYSPLLCLKSEL & SYSCON_SYSPLLCLKSEL_SEL_MASK) == 0x01U)
    {
        /* Turn on the ext clock if system pll input select clk_in */
        CLOCK_Enable_SysOsc(true);
    }
    /* Enable power VD3 for PLLs */
    POWER_SetPLL();
    /* Power off PLL during setup changes */
    POWER_EnablePD(kPDRUNCFG_PD_SYS_PLL0);

    /* Write PLL setup data */
    SYSCON->SYSPLLCTRL = pSetup->pllctrl;
    SYSCON->SYSPLLNDEC = pSetup->pllndec;
    SYSCON->SYSPLLNDEC = pSetup->pllndec | (1UL << SYSCON_SYSPLLNDEC_NREQ_SHIFT); /* latch */
    SYSCON->SYSPLLPDEC = pSetup->pllpdec;
    SYSCON->SYSPLLPDEC = pSetup->pllpdec | (1UL << SYSCON_SYSPLLPDEC_PREQ_SHIFT); /* latch */
    SYSCON->SYSPLLMDEC = pSetup->pllmdec;
    SYSCON->SYSPLLMDEC = pSetup->pllmdec | (1UL << SYSCON_SYSPLLMDEC_MREQ_SHIFT); /* latch */

    /* Flags for lock or power on */
    if ((pSetup->flags & (PLL_SETUPFLAG_POWERUP | PLL_SETUPFLAG_WAITLOCK)) != 0U)
    {
        /* If turning the PLL back on, perform the following sequence to accelerate PLL lock */
        uint32_t maxCCO    = (1UL << 18U) | 0x5dd2U; /* CCO = 1.6Ghz + MDEC enabled*/
        uint32_t curSSCTRL = SYSCON->SYSPLLMDEC & ~(1UL << 17U);

        /* Initialize  and power up PLL */
        SYSCON->SYSPLLMDEC = maxCCO;
        POWER_DisablePD(kPDRUNCFG_PD_SYS_PLL0);

        /* Set mreq to activate */
        SYSCON->SYSPLLMDEC = maxCCO | (1UL << 17U);

        /* Delay for 72 uSec @ 12Mhz */
        SDK_DelayAtLeastUs(72U, SDK_DEVICE_MAXIMUM_CPU_CLOCK_FREQUENCY);

        /* clear mreq to prepare for restoring mreq */
        SYSCON->SYSPLLMDEC = curSSCTRL;

        /* set original value back and activate */
        SYSCON->SYSPLLMDEC = curSSCTRL | (1UL << 17U);

        /* Enable peripheral states by setting low */
        POWER_DisablePD(kPDRUNCFG_PD_SYS_PLL0);
    }
    if ((pSetup->flags & PLL_SETUPFLAG_WAITLOCK) != 0U)
    {
        while (CLOCK_IsSystemPLLLocked() == false)
        {
        }
    }

    /* Update current programmed PLL rate var */
    s_Pll_Freq = pSetup->pllRate;

    return kStatus_PLL_Success;
}

/* Setup Audio PLL Frequency from pre-calculated value */
/**
 * brief	Set Audio PLL output from Audio PLL setup structure (precise frequency)
 * param	pSetup	: Pointer to populated PLL setup structure
 * return	kStatus_PLL_Success on success, or Audio PLL setup error code
 * note	This function will power off the PLL, setup the Audio PLL with the
 * new setup data, and then optionally powerup the PLL, wait for Audio PLL lock,
 * and adjust system voltages to the new PLL rate. The function will not
 * alter any source clocks (ie, main systen clock) that may use the Audio PLL,
 * so these should be setup prior to and after exiting the function.
 */
pll_error_t CLOCK_SetAudioPLLFreq(const pll_setup_t *pSetup)
{
    if ((SYSCON->AUDPLLCLKSEL & SYSCON_AUDPLLCLKSEL_SEL_MASK) == 0x01U)
    {
        /* Turn on the ext clock if system pll input select clk_in */
        CLOCK_Enable_SysOsc(true);
    }
    /* Enable power VD3 for PLLs */
    POWER_SetPLL();
    /* Power off Audio PLL during setup changes */
    POWER_EnablePD(kPDRUNCFG_PD_AUDIO_PLL);

    /* Write Audio PLL setup data */
    SYSCON->AUDPLLCTRL = pSetup->pllctrl;
    SYSCON->AUDPLLFRAC = pSetup->audpllfrac;
    SYSCON->AUDPLLFRAC = pSetup->audpllfrac | (1UL << SYSCON_AUDPLLFRAC_REQ_SHIFT); /* latch */
    SYSCON->AUDPLLNDEC = pSetup->pllndec;
    SYSCON->AUDPLLNDEC = pSetup->pllndec | (1UL << SYSCON_AUDPLLNDEC_NREQ_SHIFT); /* latch */
    SYSCON->AUDPLLPDEC = pSetup->pllpdec;
    SYSCON->AUDPLLPDEC = pSetup->pllpdec | (1UL << SYSCON_AUDPLLPDEC_PREQ_SHIFT); /* latch */
    SYSCON->AUDPLLMDEC = pSetup->pllmdec;
    SYSCON->AUDPLLMDEC = pSetup->pllmdec | (1UL << SYSCON_AUDPLLMDEC_MREQ_SHIFT); /* latch */
    SYSCON->AUDPLLFRAC = SYSCON_AUDPLLFRAC_SEL_EXT(1);                            /* disable fractional function */

    /* Flags for lock or power on */
    if ((pSetup->flags & (PLL_SETUPFLAG_POWERUP | PLL_SETUPFLAG_WAITLOCK)) != 0U)
    {
        /* If turning the PLL back on, perform the following sequence to accelerate PLL lock */
        uint32_t maxCCO    = (1UL << 18U) | 0x5dd2U; /* CCO = 1.6Ghz + MDEC enabled*/
        uint32_t curSSCTRL = SYSCON->SYSPLLMDEC & ~(1UL << 17U);

        /* Initialize  and power up PLL */
        SYSCON->SYSPLLMDEC = maxCCO;
        POWER_DisablePD(kPDRUNCFG_PD_AUDIO_PLL);

        /* Set mreq to activate */
        SYSCON->SYSPLLMDEC = maxCCO | (1UL << 17U);

        /* Delay for 72 uSec @ 12Mhz */
        SDK_DelayAtLeastUs(72U, SDK_DEVICE_MAXIMUM_CPU_CLOCK_FREQUENCY);

        /* clear mreq to prepare for restoring mreq */
        SYSCON->SYSPLLMDEC = curSSCTRL;

        /* set original value back and activate */
        SYSCON->SYSPLLMDEC = curSSCTRL | (1UL << 17U);

        /* Enable peripheral states by setting low */
        POWER_DisablePD(kPDRUNCFG_PD_AUDIO_PLL);
    }
    if ((pSetup->flags & PLL_SETUPFLAG_WAITLOCK) != 0U)
    {
        while (CLOCK_IsAudioPLLLocked() == false)
        {
        }
    }

    /* Update current programmed PLL rate var */
    s_Audio_Pll_Freq = pSetup->pllRate;

    return kStatus_PLL_Success;
}

/* Setup USB PLL Frequency from pre-calculated value */
/**
 * brief	Set USB PLL output from USB PLL setup structure (precise frequency)
 * param	pSetup	: Pointer to populated USB PLL setup structure
 * return	kStatus_PLL_Success on success, or USB PLL setup error code
 * note	This function will power off the USB PLL, setup the PLL with the
 * new setup data, and then optionally powerup the USB PLL, wait for USB PLL lock,
 * and adjust system voltages to the new USB PLL rate. The function will not
 * alter any source clocks (ie, usb pll clock) that may use the USB PLL,
 * so these should be setup prior to and after exiting the function.
 */
pll_error_t CLOCK_SetUsbPLLFreq(const usb_pll_setup_t *pSetup)
{
    uint32_t usbpllctrl, fccoHz;
    uint8_t msel, psel, nsel;
    bool pllDirectInput, pllDirectOutput, pllfbsel;

    msel            = pSetup->msel;
    psel            = pSetup->psel;
    nsel            = pSetup->nsel;
    pllDirectOutput = pSetup->direct;
    pllDirectInput  = pSetup->bypass;
    pllfbsel        = pSetup->fbsel;

    /* Input clock into the PLL cannot be lower than this */
    if (pSetup->inputRate < USB_PLL_LOWER_IN_LIMIT)
    {
        return kStatus_PLL_InputTooLow;
    }

    if (pllfbsel)
    {
        /*integer_mode: Fout = M*(Fin/N),  Fcco = 2*P*M*(Fin/N) */
        fccoHz = (pSetup->inputRate / ((uint32_t)nsel + 1U)) * 2U * (msel + 1U) * SWITCH_USB_PSEL(psel);

        /* USB PLL CCO out rate cannot be lower than this */
        if (fccoHz < USB_PLL_MIN_CCO_FREQ_MHZ)
        {
            return kStatus_PLL_CCOTooLow;
        }
        /* USB PLL CCO out rate cannot be Higher than this */
        if (fccoHz > USB_PLL_MAX_CCO_FREQ_MHZ)
        {
            return kStatus_PLL_CCOTooHigh;
        }
    }
    else
    {
        /* non integer_mode: Fout = M*(Fin/N)/(2*P), Fcco = M * (Fin/N) */
        fccoHz = pSetup->inputRate / ((uint32_t)nsel + 1U) * (msel + 1U);

        /* USB PLL CCO out rate cannot be lower than this */
        if (fccoHz < USB_PLL_MIN_CCO_FREQ_MHZ)
        {
            return kStatus_PLL_CCOTooLow;
        }
        /* USB PLL CCO out rate cannot be Higher than this */
        if (fccoHz > USB_PLL_MAX_CCO_FREQ_MHZ)
        {
            return kStatus_PLL_CCOTooHigh;
        }
    }

    /* If configure the USB HOST clock, VD5 power for USB PHY should be enable
       before the PLL is working */
    /* Turn on the ext clock for usb pll input */
    CLOCK_Enable_SysOsc(true);

    /* Enable power VD3 for PLLs */
    POWER_SetPLL();

    /* Power on the VD5 for USB PHY */
    POWER_SetUsbPhy();

    /* Power off USB PLL during setup changes */
    POWER_EnablePD(kPDRUNCFG_PD_USB_PLL);

    /* Write USB PLL setup data */
    usbpllctrl = USB_PLL_NSEL_VAL_SET(nsel) |                                  /* NSEL VALUE */
                 USB_PLL_PSEL_VAL_SET(psel) |                                  /* PSEL VALUE */
                 USB_PLL_MSEL_VAL_SET(msel) |                                  /* MSEL VALUE */
                 (uint32_t)pllDirectInput << SYSCON_USBPLLCTRL_BYPASS_SHIFT |  /* BYPASS DISABLE */
                 (uint32_t)pllDirectOutput << SYSCON_USBPLLCTRL_DIRECT_SHIFT | /* DIRECTO DISABLE */
                 (uint32_t)pllfbsel << SYSCON_USBPLLCTRL_FBSEL_SHIFT;          /* FBSEL SELECT */

    SYSCON->USBPLLCTRL = usbpllctrl;

    POWER_DisablePD(kPDRUNCFG_PD_USB_PLL);

    /* Delay for 72 uSec @ 12Mhz for the usb pll to lock */
    SDK_DelayAtLeastUs(72U, SDK_DEVICE_MAXIMUM_CPU_CLOCK_FREQUENCY);
    if (false == pllDirectInput)
    {
        while (CLOCK_IsUsbPLLLocked() == false)
        {
        }
    }
    CLOCK_GetUsbPLLOutFromSetupUpdate(pSetup);
    return kStatus_PLL_Success;
}

/* Set System PLL clock based on the input frequency and multiplier */
/*! brief	Set PLL output based on the multiplier and input frequency
 * param	multiply_by	: multiplier
 * param	input_freq	: Clock input frequency of the PLL
 * return	Nothing
 * note	Unlike the Chip_Clock_SetupSystemPLLPrec() function, this
 * function does not disable or enable PLL power, wait for PLL lock,
 * or adjust system voltages. These must be done in the application.
 * The function will not alter any source clocks (ie, main systen clock)
 * that may use the PLL, so these should be setup prior to and after
 * exiting the function.
 */
void CLOCK_SetupSystemPLLMult(uint32_t multiply_by, uint32_t input_freq)
{
    uint32_t cco_freq = input_freq * multiply_by;
    uint32_t pdec     = 1U;
    uint32_t selr;
    uint32_t seli;
    uint32_t selp;
    uint32_t mdec, ndec;

    uint32_t directo = SYSCON_SYSPLLCTRL_DIRECTO(1);

    while (cco_freq < 275000000U)
    {
        multiply_by <<= 1U; /* double value in each iteration */
        pdec <<= 1U;        /* correspondingly double pdec to cancel effect of double msel */
        cco_freq = input_freq * multiply_by;
    }
    selr = 0U;
    if (multiply_by < 60U)
    {
        seli = (multiply_by & 0x3cU) + 4U;
        selp = (multiply_by >> 1U) + 1U;
    }
    else
    {
        selp = 31U;
        if (multiply_by > 16384U)
        {
            seli = 1U;
        }
        else if (multiply_by > 8192U)
        {
            seli = 2U;
        }
        else if (multiply_by > 2048U)
        {
            seli = 4U;
        }
        else if (multiply_by >= 501U)
        {
            seli = 8U;
        }
        else
        {
            seli = 4U * (1024U / (multiply_by + 9U));
        }
    }

    if (pdec > 1U)
    {
        directo = 0U;        /* use post divider */
        pdec    = pdec / 2U; /* Account for minus 1 encoding */
                             /* Translate P value */
        switch (pdec)
        {
            case 1U:
                pdec = 0x62U; /* 1  * 2 */
                break;
            case 2U:
                pdec = 0x42U; /* 2  * 2 */
                break;
            case 4U:
                pdec = 0x02U; /* 4  * 2 */
                break;
            case 8U:
                pdec = 0x0bU; /* 8  * 2 */
                break;
            case 16U:
                pdec = 0x11U; /* 16 * 2 */
                break;
            case 32U:
                pdec = 0x08U; /* 32 * 2 */
                break;
            default:
                pdec = 0x08U;
                break;
        }
    }

    mdec = PLL_MDEC_VAL_SET(pllEncodeM(multiply_by));
    ndec = 0x302U; /* pre divide by 1 (hardcoded) */

    SYSCON->SYSPLLCTRL = directo | (selr << SYSCON_SYSPLLCTRL_SELR_SHIFT) | (seli << SYSCON_SYSPLLCTRL_SELI_SHIFT) |
                         (selp << SYSCON_SYSPLLCTRL_SELP_SHIFT);
    SYSCON->SYSPLLPDEC = pdec | (1U << 7U);   /* set Pdec value and assert preq */
    SYSCON->SYSPLLNDEC = ndec | (1UL << 10U); /* set Pdec value and assert preq */
    SYSCON->SYSPLLMDEC = (1UL << 17U) | mdec; /* select non sscg MDEC value, assert mreq and select mdec value */
}

/* Enable USB DEVICE FULL SPEED clock */
/*! brief Enable USB Device FS clock.
 * param	src	: clock source
 * param	freq: clock frequency
 * Enable USB Device Full Speed clock.
 */
bool CLOCK_EnableUsbfs0DeviceClock(clock_usb_src_t src, uint32_t freq)
{
    bool ret = true;

    CLOCK_DisableClock(kCLOCK_Usbd0);

    if (kCLOCK_UsbSrcFro == src)
    {
        switch (freq)
        {
            case 96000000U:
                CLOCK_SetClkDiv(kCLOCK_DivUsb0Clk, 2U, false); /*!< Div by 2 to get 48MHz, no divider reset */
                break;

            case 48000000U:
                CLOCK_SetClkDiv(kCLOCK_DivUsb0Clk, 1U, false); /*!< Div by 1 to get 48MHz, no divider reset */
                break;

            default:
                ret = false;
                break;
        }
        /* Turn ON FRO HF and let it adjust TRIM value based on USB SOF */
        SYSCON->FROCTRL = (SYSCON->FROCTRL & ~((0x01UL << 15U) | (0xFUL << 26U))) | SYSCON_FROCTRL_HSPDCLK_MASK |
                          SYSCON_FROCTRL_USBCLKADJ_MASK;
        /* Select FRO 96 or 48 MHz */
        CLOCK_AttachClk(kFRO_HF_to_USB0_CLK);
    }
    else
    {
        /*Set the USB PLL as the Usb0 CLK*/
        POWER_DisablePD(kPDRUNCFG_PD_USB_PLL);

        usb_pll_setup_t pll_setup = {0x3FU, 0x01U, 0x03U, false, false, false, 12000000U};

        (void)CLOCK_SetUsbPLLFreq(&pll_setup);
        CLOCK_SetClkDiv(kCLOCK_DivUsb0Clk, 1U, false);
        CLOCK_AttachClk(kUSB_PLL_to_USB0_CLK);
        SDK_DelayAtLeastUs(50U, SDK_DEVICE_MAXIMUM_CPU_CLOCK_FREQUENCY);
    }
    CLOCK_EnableClock(kCLOCK_Usbd0);
    CLOCK_EnableClock(kCLOCK_UsbRam1);

    return ret;
}

/* Enable USB HOST FULL SPEED clock */
/*! brief Enable USB HOST FS clock.
 * param	src	: clock source
 * param	freq: clock frequency
 * Enable USB HOST Full Speed clock.
 */
bool CLOCK_EnableUsbfs0HostClock(clock_usb_src_t src, uint32_t freq)
{
    bool ret = true;

    CLOCK_DisableClock(kCLOCK_Usbhmr0);
    CLOCK_DisableClock(kCLOCK_Usbhsl0);

    if (kCLOCK_UsbSrcFro == src)
    {
        switch (freq)
        {
            case 96000000U:
                CLOCK_SetClkDiv(kCLOCK_DivUsb0Clk, 2U, false); /*!< Div by 2 to get 48MHz, no divider reset */
                break;

            case 48000000U:
                CLOCK_SetClkDiv(kCLOCK_DivUsb0Clk, 1U, false); /*!< Div by 1 to get 48MHz, no divider reset */
                break;

            default:
                ret = false;
                break;
        }
        /* Turn ON FRO HF and let it adjust TRIM value based on USB SOF */
        SYSCON->FROCTRL = (SYSCON->FROCTRL & ~((0x01UL << 15U) | (0xFUL << 26U))) | SYSCON_FROCTRL_HSPDCLK_MASK |
                          SYSCON_FROCTRL_USBCLKADJ_MASK;
        /* Select FRO 96 or 48 MHz */
        CLOCK_AttachClk(kFRO_HF_to_USB0_CLK);
    }
    else
    {
        /*Set the USB PLL as the Usb0 CLK*/
        POWER_DisablePD(kPDRUNCFG_PD_USB_PLL);

        usb_pll_setup_t pll_setup = {0x3FU, 0x01U, 0x03U, false, false, false, 12000000U};

        (void)CLOCK_SetUsbPLLFreq(&pll_setup);
        CLOCK_SetClkDiv(kCLOCK_DivUsb0Clk, 1U, false);
        CLOCK_AttachClk(kUSB_PLL_to_USB0_CLK);
        SDK_DelayAtLeastUs(50U, SDK_DEVICE_MAXIMUM_CPU_CLOCK_FREQUENCY);
    }
    CLOCK_EnableClock(kCLOCK_Usbhmr0);
    CLOCK_EnableClock(kCLOCK_Usbhsl0);
    CLOCK_EnableClock(kCLOCK_UsbRam1);

    return ret;
}

/* Enable USB DEVICE HIGH SPEED clock */
/*! brief Enable USB Device HS clock.
 * param	src	: clock source
 * param	freq: clock frequency
 * Enable USB Device High Speed clock.
 */
bool CLOCK_EnableUsbhs0DeviceClock(clock_usb_src_t src, uint32_t freq)
{
    bool ret = true;
    CLOCK_DisableClock(kCLOCK_Usbd1);
    /* Power on the VD5 for USB PHY */
    POWER_SetUsbPhy();
    if (kCLOCK_UsbSrcFro == src)
    {
        switch (freq)
        {
            case 96000000U:
                CLOCK_SetClkDiv(kCLOCK_DivUsb1Clk, 2U, false); /*!< Div by 2 to get 48MHz, no divider reset */
                break;

            case 48000000U:
                CLOCK_SetClkDiv(kCLOCK_DivUsb1Clk, 1U, false); /*!< Div by 1 to get 48MHz, no divider reset */
                break;

            default:
                ret = false;
                break;
        }
        /* Turn ON FRO HF and let it adjust TRIM value based on USB SOF */
        SYSCON->FROCTRL = (SYSCON->FROCTRL & ~((0x01UL << 15U) | (0xFUL << 26U))) | SYSCON_FROCTRL_HSPDCLK_MASK |
                          SYSCON_FROCTRL_USBCLKADJ_MASK;
        /* Select FRO 96 or 48 MHz */
        CLOCK_AttachClk(kFRO_HF_to_USB1_CLK);
    }
    else
    {
        SDK_DelayAtLeastUs(50, SDK_DEVICE_MAXIMUM_CPU_CLOCK_FREQUENCY);
        usb_pll_setup_t pll_setup = {0x3FU, 0x01U, 0x03U, false, false, false, 12000000U};

        (void)CLOCK_SetUsbPLLFreq(&pll_setup);

        /* Select USB PLL output as USB clock src */
        CLOCK_SetClkDiv(kCLOCK_DivUsb1Clk, 1U, false);
        CLOCK_AttachClk(kUSB_PLL_to_USB1_CLK);
    }

    SDK_DelayAtLeastUs(50, SDK_DEVICE_MAXIMUM_CPU_CLOCK_FREQUENCY);
    /* Enable USB1D and USB1RAM */
    CLOCK_EnableClock(kCLOCK_Usbd1);
    CLOCK_EnableClock(kCLOCK_UsbRam1);
    POWER_DisablePD(kPDRUNCFG_PD_USB1_PHY); /* Turn on power for USB PHY */
    return ret;
}

/* Enable USB HOST HIGH SPEED clock */
/*! brief Enable USB HOST HS clock.
 * param	src	: clock source
 * param	freq: clock frequency
 * Enable USB HOST High Speed clock.
 */
bool CLOCK_EnableUsbhs0HostClock(clock_usb_src_t src, uint32_t freq)
{
    bool ret = true;
    CLOCK_DisableClock(kCLOCK_Usbh1);
    /* Power on the VD5 for USB PHY */
    POWER_SetUsbPhy();
    if (kCLOCK_UsbSrcFro == src)
    {
        switch (freq)
        {
            case 96000000U:
                CLOCK_SetClkDiv(kCLOCK_DivUsb1Clk, 2U, false); /*!< Div by 2 to get 48MHz, no divider reset */
                break;

            case 48000000U:
                CLOCK_SetClkDiv(kCLOCK_DivUsb1Clk, 1U, false); /*!< Div by 1 to get 48MHz, no divider reset */
                break;

            default:
                ret = false;
                break;
        }
        /* Turn ON FRO HF and let it adjust TRIM value based on USB SOF */
        SYSCON->FROCTRL = (SYSCON->FROCTRL & ~((0x01UL << 15U) | (0xFUL << 26U))) | SYSCON_FROCTRL_HSPDCLK_MASK |
                          SYSCON_FROCTRL_USBCLKADJ_MASK;
        /* Select FRO 96 or 48 MHz */
        CLOCK_AttachClk(kFRO_HF_to_USB1_CLK);
    }
    else
    {
        SDK_DelayAtLeastUs(50U, SDK_DEVICE_MAXIMUM_CPU_CLOCK_FREQUENCY);
        usb_pll_setup_t pll_setup = {0x3FU, 0x01U, 0x03U, false, false, false, 12000000U};

        (void)CLOCK_SetUsbPLLFreq(&pll_setup);

        /* Select USB PLL output as USB clock src */
        CLOCK_SetClkDiv(kCLOCK_DivUsb1Clk, 1U, false);
        CLOCK_AttachClk(kUSB_PLL_to_USB1_CLK);
    }

    SDK_DelayAtLeastUs(50, SDK_DEVICE_MAXIMUM_CPU_CLOCK_FREQUENCY);
    /* Enable USBh1 and USB1RAM */
    CLOCK_EnableClock(kCLOCK_Usbh1);
    CLOCK_EnableClock(kCLOCK_UsbRam1);
    POWER_DisablePD(kPDRUNCFG_PD_USB1_PHY); /* Turn on power for USB PHY */
    return ret;
}
