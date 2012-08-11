/*******************************************************************************
 * (c) Copyright 2009 Actel Corporation.  All rights reserved.
 * 
 *  SmartFusion A2FxxxM3 CMSIS system initialization.
 *
 * SVN $Revision: 2069 $
 * SVN $Date: 2010-01-28 00:23:48 +0000 (Thu, 28 Jan 2010) $
 */
#include "a2fxxxm3.h"
#include "mss_assert.h"

/* System frequency (FCLK) coming out of reset is 25MHz. */
#define RESET_SYSCLCK_FREQ      25000000uL

/*
 * SmartFusion Microcontroller Subsystem FLCK frequency.
 * The value of SMARTFUSION_FCLK_FREQ is used to report the system's clock
 * frequency in system's which either do not use the Actel System Boot or
 * a version of the Actel System Boot older than 1.3.1. In eitehr of these cases
 * SMARTFUSION_FCLK_FREQ should be defined in the projects settings to reflect
 * the FCLK frequency selected in the Libero MSS configurator.
 * Systems using the Actel System Boot version 1.3.1 or later do not require this
 * define since the system's frequency is retrieved from eNVM spare pages where
 * the MSS Configurator stored the frequency selected during hardware design/configuration.
 */
#ifdef SMARTFUSION_FCLK_FREQ
#define SMARTFUSION_FCLK_FREQ_DEFINED   1
#else
#define SMARTFUSION_FCLK_FREQ_DEFINED   0
#define SMARTFUSION_FCLK_FREQ    RESET_SYSCLCK_FREQ
#endif

/* Divider values for APB0, APB1 and ACE clocks. */
#define RESET_PCLK0_DIV         4uL
#define RESET_PCLK1_DIV         4uL
#define RESET_ACE_DIV           4uL
#define RESET_FPGA_CLK_DIV      4uL

/* System register clock control mask and shift for PCLK dividers. */
#define PCLK_DIV_MASK       0x00000003uL
#define PCLK0_DIV_SHIFT     2uL
#define PCLK1_DIV_SHIFT     4uL
#define ACE_DIV_SHIFT       6uL

/* System register MSS_CCC_DIV_CR mask and shift for GLB (FPGA fabric clock). */
#define OBDIV_SHIFT         8uL
#define OBDIV_MASK          0x0000001FuL
#define OBDIVHALF_SHIFT     13uL
#define OBDIVHALF_MASK      0x00000001uL

/*
 * Actel system boot version defines used to extract the system clock from eNVM
 * spare pages.
 * These defines allow detecting the presence of Actel system boot in eNVM spare
 * pages and the version of that system boot executable and associated
 * configuration data.
 */
#define SYSBOOT_KEY_ADDR        (uint32_t *)0x6008081C
#define SYSBOOT_KEY_VALUE       0x4C544341uL
#define SYSBOOT_VERSION_ADDR    (uint32_t *)0x60080840
#define SYSBOOT_1_3_FCLK_ADDR   (uint32_t *)0x6008162C
#define SYSBOOT_2_x_FCLK_ADDR   (uint32_t *)0x60081EAC

/*
 * The system boot version is stored in the least significant 24 bits of a word.
 * The FCLK is stored in eNVM from version 1.3.1 of the system boot. We expect
 * that the major version number of the system boot version will change if the
 * system boot configuration data layout needs to change. 
 */
#define SYSBOOT_VERSION_MASK    0x00FFFFFFuL
#define MIN_SYSBOOT_VERSION     0x00010301uL
#define SYSBOOT_VERSION_2_X     0x00020000uL
#define MAX_SYSBOOT_VERSION     0x00030000uL

/* Standard CMSIS global variables. */
uint32_t SystemFrequency = SMARTFUSION_FCLK_FREQ;          /*!< System Clock Frequency (Core Clock) */
uint32_t SystemCoreClock = SMARTFUSION_FCLK_FREQ;          /*!< System Clock Frequency (Core Clock) */

/* SmartFusion specific clocks. */
uint32_t g_FrequencyPCLK0 = (SMARTFUSION_FCLK_FREQ / RESET_PCLK0_DIV);      /*!< Clock frequency of APB bus 0. */  
uint32_t g_FrequencyPCLK1 = (SMARTFUSION_FCLK_FREQ / RESET_PCLK1_DIV);      /*!< Clock frequency of APB bus 1. */
uint32_t g_FrequencyACE = (SMARTFUSION_FCLK_FREQ / RESET_ACE_DIV);          /*!< Clock frequency of Analog Compute Engine. */
uint32_t g_FrequencyFPGA = (SMARTFUSION_FCLK_FREQ / RESET_FPGA_CLK_DIV);    /*!< Clock frequecny of FPGA fabric */

/* Local functions */
static uint32_t GetSystemClock( void );

/***************************************************************************//**
 * See system_a2fm3fxxx.h for details.
 */
void SystemInit(void)
{
}

/***************************************************************************//**
 *
 */
void SystemCoreClockUpdate (void)
{
    uint32_t PclkDiv0;
    uint32_t PclkDiv1;
    uint32_t AceDiv;
    uint32_t FabDiv;

    const uint32_t pclk_div_lut[4] = { 1uL, 2uL, 4uL, 1uL };

    /* Read PCLK dividers from system registers. Multiply the value read from
     * system register by two to get actual divider value. */
    PclkDiv0 = pclk_div_lut[((SYSREG->MSS_CLK_CR >> PCLK0_DIV_SHIFT) & PCLK_DIV_MASK)];
    PclkDiv1 = pclk_div_lut[((SYSREG->MSS_CLK_CR >> PCLK1_DIV_SHIFT) & PCLK_DIV_MASK)];
    AceDiv = pclk_div_lut[((SYSREG->MSS_CLK_CR >> ACE_DIV_SHIFT) & PCLK_DIV_MASK)];
    {
        /* Compute the FPGA fabric frequency divider. */
        uint32_t obdiv;
        uint32_t obdivhalf;
        
        obdiv = (SYSREG->MSS_CCC_DIV_CR >> OBDIV_SHIFT) & OBDIV_MASK;
        obdivhalf = (SYSREG->MSS_CCC_DIV_CR >> OBDIVHALF_SHIFT) & OBDIVHALF_MASK;
        FabDiv = obdiv + 1uL;
        if ( obdivhalf != 0uL )
        {
            FabDiv = FabDiv * 2uL;
        }
    }
    
    /* Retrieve FCLK from eNVM spare pages if Actel system boot programmed as part of the system. */
    
    /* Read system clock from eNVM spare pages. */
    SystemCoreClock = GetSystemClock();
    g_FrequencyPCLK0 = SystemCoreClock / PclkDiv0;
    g_FrequencyPCLK1 = SystemCoreClock / PclkDiv1;
    g_FrequencyACE = SystemCoreClock / AceDiv;
    g_FrequencyFPGA = SystemCoreClock / FabDiv;
    
    /* Keep SystemFrequency as well as SystemCoreClock for legacy reasons. */
    SystemFrequency = SystemCoreClock;
}

/***************************************************************************//**
 * Retrieve the system clock frequency from eNVM spare page if available.
 * Returns the frequency defined through SMARTFUSION_FCLK_FREQ if FCLK cannot be
 * retrieved from eNVM spare pages.
 * The FCLK frequency value selected in the MSS Configurator software tool is
 * stored in eNVM spare pages as part of the Actel system boot configuration data.
 */
uint32_t GetSystemClock( void )
{
    uint32_t fclk = 0uL;
    
    uint32_t * p_sysboot_key = SYSBOOT_KEY_ADDR;
    
    if ( SYSBOOT_KEY_VALUE == *p_sysboot_key )
    {
        /* Actel system boot programmed, check if it has the FCLK value stored. */
        uint32_t *p_sysboot_version = SYSBOOT_VERSION_ADDR;
        uint32_t sysboot_version = *p_sysboot_version;
        
        sysboot_version &= SYSBOOT_VERSION_MASK;
        
        if ( sysboot_version >= MIN_SYSBOOT_VERSION )
        {
            /* Handle change of eNVM location of FCLK between 1.3.x and 2.x.x versions of the system boot. */
            if ( sysboot_version < SYSBOOT_VERSION_2_X )
            {
                /* Read FCLK value from MSS configurator generated configuration
                 * data stored in eNVM spare pages as part of system boot version 1.3.x
                 * configuration tables. */
                uint32_t *p_fclk = SYSBOOT_1_3_FCLK_ADDR;
                fclk = *p_fclk;
            }
            else if ( sysboot_version < MAX_SYSBOOT_VERSION )
            {
                /* Read FCLK value from MSS configurator generated configuration
                 * data stored in eNVM spare pages as part of system boot version 2.x.x
                 * configuration tables. */
                uint32_t *p_fclk = SYSBOOT_2_x_FCLK_ADDR;
                fclk = *p_fclk;
            }
            else
            {
                fclk = 0uL;
            }
        }
    }
    
    if ( 0uL == fclk )
    {
        /* 
         * Could not retrieve FCLK from system boot configuration data. Fall back
         * to using SMARTFUSION_FCLK_FREQ which must then be defined as part of
         * project settings.
         */
        ASSERT( SMARTFUSION_FCLK_FREQ_DEFINED );
        fclk = SMARTFUSION_FCLK_FREQ;
    }
    
    return fclk;
}

