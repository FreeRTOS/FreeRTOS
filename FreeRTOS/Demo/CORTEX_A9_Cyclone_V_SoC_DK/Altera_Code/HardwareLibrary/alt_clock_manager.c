/******************************************************************************
 *
 * Copyright 2013 Altera Corporation. All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of the author may not be used to endorse or promote products
 * derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO
 * EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
 * OF SUCH DAMAGE.
 *
 ******************************************************************************/

#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>

#include "socal/hps.h"
#include "socal/socal.h"
#include "socal/alt_sysmgr.h"
#include "hwlib.h"
#include "alt_clock_manager.h"
#include "alt_mpu_registers.h"

#define UINT12_MAX              (4096)

#define printf( ... )

/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Useful Structures ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/


        /* General structure used to hold parameters of various clock entities, */
typedef struct ALT_CLK_PARAMS_s
{
    alt_freq_t      freqcur;                   // current frequency of the clock
    alt_freq_t      freqmin;                   // minimum allowed frequency for this clock
    alt_freq_t      freqmax;                   // maximum allowed frequency for this clock
    uint32_t        guardband : 7;             // guardband percentage (0-100) if this clock
                                               //    is a PLL, ignored otherwise
    uint32_t        active    : 1;             // current state of activity of this clock
} ALT_CLK_PARAMS_t;


typedef struct ALT_EXT_CLK_PARAMBLOK_s
{
    ALT_CLK_PARAMS_t        clkosc1;        // ALT_CLK_OSC1
    ALT_CLK_PARAMS_t        clkosc2;        // ALT_CLK_OSC2
    ALT_CLK_PARAMS_t        periph;         // ALT_CLK_F2H_PERIPH_REF
    ALT_CLK_PARAMS_t        sdram;          // ALT_CLK_F2H_SDRAM_REF
} ALT_EXT_CLK_PARAMBLOK_t;


        /* Initializes the External Clock Frequency Limits block                        */
        /* The first field is the current external clock frequency, and can be set by   */
        /* alt_clk_ext_clk_freq_set(), the second and third fields are the minimum and  */
        /* maximum frequencies, the fourth field is ignored, and the fifth field        */
        /* contains the current activity state of the clock, 1=active, 0=inactive.      */
        /* Values taken from Section 2.3 and Section 2.7.1 of the HHP HPS-Clocking      */
        /* NPP specification.                                                           */
static ALT_EXT_CLK_PARAMBLOK_t alt_ext_clk_paramblok =
{
    { 25000000, 10000000, 50000000, 0, 1 },
    { 25000000, 10000000, 50000000, 0, 1 },
    {        0, 10000000, 50000000, 0, 1 },
    {        0, 10000000, 50000000, 0, 1 }
};


        /* PLL frequency limits */
typedef struct ALT_PLL_CLK_PARAMBLOK_s
{
    ALT_CLK_PARAMS_t       MainPLL_600;         // Main PLL values for 600 MHz SoC
    ALT_CLK_PARAMS_t       PeriphPLL_600;       // Peripheral PLL values for 600 MHz SoC
    ALT_CLK_PARAMS_t       SDRAMPLL_600;        // SDRAM PLL values for 600 MHz SoC
    ALT_CLK_PARAMS_t       MainPLL_800;         // Main PLL values for 800 MHz SoC
    ALT_CLK_PARAMS_t       PeriphPLL_800;       // Peripheral PLL values for 800 MHz SoC
    ALT_CLK_PARAMS_t       SDRAMPLL_800;        // SDRAM PLL values for 800 MHz SoC
} ALT_PLL_CLK_PARAMBLOK_t;


    /* Initializes the PLL frequency limits block                               */
    /* The first field is the current frequency, the second and third fields    */
    /* are the design limits of the PLLs as listed in Section 3.2.1.2 of the    */
    /* HHP HPS-Clocking NPP document. The fourth field of each line is the      */
    /* guardband percentage, and the fifth field of each line is the current    */
    /* state of the PLL, 1=active, 0=inactive.                                  */
#define     ALT_ORIGINAL_GUARDBAND_VAL      20
#define     ALT_GUARDBAND_LIMIT             20

static ALT_PLL_CLK_PARAMBLOK_t alt_pll_clk_paramblok =
{
    { 0, 320000000, 1200000000, ALT_ORIGINAL_GUARDBAND_VAL, 0 },
    { 0, 320000000,  900000000, ALT_ORIGINAL_GUARDBAND_VAL, 0 },
    { 0, 320000000,  800000000, ALT_ORIGINAL_GUARDBAND_VAL, 0 },
    { 0, 320000000, 1600000000, ALT_ORIGINAL_GUARDBAND_VAL, 1 },
    { 0, 320000000, 1250000000, ALT_ORIGINAL_GUARDBAND_VAL, 1 },
    { 0, 320000000, 1066000000, ALT_ORIGINAL_GUARDBAND_VAL, 1 }
};


        /* PLL counter frequency limits */
typedef struct ALT_PLL_CNTR_FREQMAX_s
{
    alt_freq_t       MainPLL_C0;         // Main PLL Counter 0 parameter block
    alt_freq_t       MainPLL_C1;         // Main PLL Counter 1 parameter block
    alt_freq_t       MainPLL_C2;         // Main PLL Counter 2 parameter block
    alt_freq_t       MainPLL_C3;         // Main PLL Counter 3 parameter block
    alt_freq_t       MainPLL_C4;         // Main PLL Counter 4 parameter block
    alt_freq_t       MainPLL_C5;         // Main PLL Counter 5 parameter block
    alt_freq_t       PeriphPLL_C0;       // Peripheral PLL Counter 0 parameter block
    alt_freq_t       PeriphPLL_C1;       // Peripheral PLL Counter 1 parameter block
    alt_freq_t       PeriphPLL_C2;       // Peripheral PLL Counter 2 parameter block
    alt_freq_t       PeriphPLL_C3;       // Peripheral PLL Counter 3 parameter block
    alt_freq_t       PeriphPLL_C4;       // Peripheral PLL Counter 4 parameter block
    alt_freq_t       PeriphPLL_C5;       // Peripheral PLL Counter 5 parameter block
    alt_freq_t       SDRAMPLL_C0;        // SDRAM PLL Counter 0 parameter block
    alt_freq_t       SDRAMPLL_C1;        // SDRAM PLL Counter 1 parameter block
    alt_freq_t       SDRAMPLL_C2;        // SDRAM PLL Counter 2 parameter block
    alt_freq_t       SDRAMPLL_C5;        // SDRAM PLL Counter 5 parameter block
} ALT_PLL_CNTR_FREQMAX_t;

//
// The following pll max frequency array statically defined must be recalculated each time
// when powering up, by calling alt_clk_clkmgr_init()
//
// for 14.1 uboot preloader, the following values are calculated dynamically.
//
// Arrial 5
// alt_pll_cntr_maxfreq.MainPLL_C0   = 1050000000
// alt_pll_cntr_maxfreq.MainPLL_C1   =  350000000
// alt_pll_cntr_maxfreq.MainPLL_C2   =  262500000
// alt_pll_cntr_maxfreq.MainPLL_C3   =  350000000
// alt_pll_cntr_maxfreq.MainPLL_C4   =    2050781
// alt_pll_cntr_maxfreq.MainPLL_C5   =  116666666
// alt_pll_cntr_maxfreq.PeriphPLL_C0 =    1953125
// alt_pll_cntr_maxfreq.PeriphPLL_C1 =  250000000
// alt_pll_cntr_maxfreq.PeriphPLL_C2 =    1953125
// alt_pll_cntr_maxfreq.PeriphPLL_C3 =  200000000
// alt_pll_cntr_maxfreq.PeriphPLL_C4 =  200000000
// alt_pll_cntr_maxfreq.PeriphPLL_C5 =    1953125
// alt_pll_cntr_maxfreq.SDRAMPLL_C0  =  533333333
// alt_pll_cntr_maxfreq.SDRAMPLL_C1  = 1066666666
// alt_pll_cntr_maxfreq.SDRAMPLL_C2  =  533333333
// alt_pll_cntr_maxfreq.SDRAMPLL_C5  =  177777777

// Cyclone V
// alt_pll_cntr_maxfreq.MainPLL_C0   =  925000000
// alt_pll_cntr_maxfreq.MainPLL_C1   =  370000000
// alt_pll_cntr_maxfreq.MainPLL_C2   =  462500000
// alt_pll_cntr_maxfreq.MainPLL_C3   =  370000000
// alt_pll_cntr_maxfreq.MainPLL_C4   =    3613281
// alt_pll_cntr_maxfreq.MainPLL_C5   =  123333333
// alt_pll_cntr_maxfreq.PeriphPLL_C0 =    1953125
// alt_pll_cntr_maxfreq.PeriphPLL_C1 =  250000000
// alt_pll_cntr_maxfreq.PeriphPLL_C2 =    1953125
// alt_pll_cntr_maxfreq.PeriphPLL_C3 =  200000000
// alt_pll_cntr_maxfreq.PeriphPLL_C4 =  200000000
// alt_pll_cntr_maxfreq.PeriphPLL_C5 =    1953125
// alt_pll_cntr_maxfreq.SDRAMPLL_C0  =  400000000
// alt_pll_cntr_maxfreq.SDRAMPLL_C1  =  800000000
// alt_pll_cntr_maxfreq.SDRAMPLL_C2  =  400000000
// alt_pll_cntr_maxfreq.SDRAMPLL_C5  =  133333333


/* Initializes the PLL Counter output maximum frequency block  */
static ALT_PLL_CNTR_FREQMAX_t alt_pll_cntr_maxfreq =
{
    800000000,    /* Main PLL Outputs */
    400000000,
    400000000,
    432000000,
    250000000,
    125000000,
    250000000,    /* Peripheral PLL Outputs */
    250000000,
    432000000,
    250000000,
    200000000,
    100000000,    /* SDRAM PLL Outputs */
    533000000,
    1066000000,
    533000000,
    200000000
};



        /* Maximum multiply, divide, and counter divisor values for each PLL */
#define     ALT_CLK_PLL_MULT_MAX        4095
#define     ALT_CLK_PLL_DIV_MAX         63
#define     ALT_CLK_PLL_CNTR_MAX        511


        /* Definitions for the reset request and reset acknowledge bits    */
        /* for each of the output counters for each of the PLLS            */
#define     ALT_CLK_PLL_RST_BIT_C0      0x00000001
#define     ALT_CLK_PLL_RST_BIT_C1      0x00000002
#define     ALT_CLK_PLL_RST_BIT_C2      0x00000004
#define     ALT_CLK_PLL_RST_BIT_C3      0x00000008
#define     ALT_CLK_PLL_RST_BIT_C4      0x00000010
#define     ALT_CLK_PLL_RST_BIT_C5      0x00000020


        /* These are the bits that deal with PLL lock and this macro */
        /* defines a mask to test for bits outside of these */
#define ALT_CLK_MGR_PLL_LOCK_BITS  (ALT_CLKMGR_INTREN_MAINPLLACHIEVED_CLR_MSK \
                                  & ALT_CLKMGR_INTREN_PERPLLACHIEVED_CLR_MSK \
                                  & ALT_CLKMGR_INTREN_SDRPLLACHIEVED_CLR_MSK \
                                  & ALT_CLKMGR_INTREN_MAINPLLLOST_CLR_MSK \
                                  & ALT_CLKMGR_INTREN_PERPLLLOST_CLR_MSK \
                                  & ALT_CLKMGR_INTREN_SDRPLLLOST_CLR_MSK)


// Undocumented register which determines clock dividers for main PLL C0, C1, and C2. These should be considered RO.
#define ALT_CLKMGR_ALTERA_OFST           0xe0
#define ALT_CLKMGR_ALTERA_MPUCLK_OFST    0x0
#define ALT_CLKMGR_ALTERA_MAINCLK_OFST   0x4
#define ALT_CLKMGR_ALTERA_DBGATCLK_OFST  0x8
#define ALT_CLKMGR_ALTERA_ADDR           ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_ADDR) + ALT_CLKMGR_ALTERA_OFST))
#define ALT_CLKMGR_ALTERA_MPUCLK_ADDR    ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_ALTERA_ADDR) + ALT_CLKMGR_ALTERA_MPUCLK_OFST))
#define ALT_CLKMGR_ALTERA_MAINCLK_ADDR   ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_ALTERA_ADDR) + ALT_CLKMGR_ALTERA_MAINCLK_OFST))
#define ALT_CLKMGR_ALTERA_DBGATCLK_ADDR  ALT_CAST(void *, (ALT_CAST(char *, ALT_CLKMGR_ALTERA_ADDR) + ALT_CLKMGR_ALTERA_DBGATCLK_OFST))
#define ALT_CLKMGR_ALTERA_MPUCLK_CNT_GET(value)   (((value) & 0x000001ff) >> 0)
#define ALT_CLKMGR_ALTERA_MAINCLK_CNT_GET(value)  (((value) & 0x000001ff) >> 0)
#define ALT_CLKMGR_ALTERA_DBGATCLK_CNT_GET(value) (((value) & 0x000001ff) >> 0)

/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Utility functions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/


/****************************************************************************************/
/* alt_clk_mgr_wait() introduces a delay, not very exact, but very light in             */
/* implementation. Depending upon the optinization level, it will wait at least the     */
/* number of clock cycles specified in the cnt parameter, sometimes many more. The      */
/* reg parameter is set to a register or a memory location that was recently used (so   */
/* as to avoid accidently evicting a register and a recently-used cache line in favor   */
/* of one whose values are not actually needed.). The cnt parameter sets the number of  */
/* repeated volatile memory reads and so sets a minimum time delay measured in          */
/* mpu_clk cycles. If mpu_clk = osc1 clock (as in bypass mode), then this gives a       */
/* minimum osc1 clock cycle delay.                                                      */
/****************************************************************************************/

inline static void alt_clk_mgr_wait(void* reg, uint32_t cnt)
{
    for (; cnt ; cnt--)
    {
        (void) alt_read_word(reg);
    }
}

    /* Wait time constants */
    /* These values came from Section 4.9.4 of the HHP HPS-Clocking NPP document */
#define ALT_SW_MANAGED_CLK_WAIT_CTRDIV          30      /* 30 or more MPU clock cycles */
#define ALT_SW_MANAGED_CLK_WAIT_HWCTRDIV        40
#define ALT_SW_MANAGED_CLK_WAIT_BYPASS          30
#define ALT_SW_MANAGED_CLK_WAIT_SAFEREQ         30
#define ALT_SW_MANAGED_CLK_WAIT_SAFEEXIT        30
#define ALT_SW_MANAGED_CLK_WAIT_NANDCLK         8       /* 8 or more MPU clock cycles */


#define ALT_BYPASS_TIMEOUT_CNT      50
        // arbitrary number until i find more info
#define ALT_TIMEOUT_PHASE_SYNC      300
        // how many loops to wait for the SDRAM clock to come around
        // to zero and allow for writing a new divisor ratio to it

ALT_STATUS_CODE alt_clk_plls_settle_wait(void)
{
    int32_t     i = ALT_BYPASS_TIMEOUT_CNT;
    bool        nofini;

    do
    {
        nofini = alt_read_word(ALT_CLKMGR_STAT_ADDR) & ALT_CLKMGR_STAT_BUSY_SET_MSK;
    } while (nofini && i--);
            // wait until clocks finish transitioning and become stable again
    return (i > 0) ? ALT_E_SUCCESS : ALT_E_ERROR;
}

static ALT_STATUS_CODE alt_clk_pll_lock_wait(ALT_CLK_t pll, uint32_t timeout)
{
    uint32_t locked_mask = 0;

    if      (pll == ALT_CLK_MAIN_PLL)       { locked_mask = ALT_CLKMGR_INTER_MAINPLLLOCKED_SET_MSK; }
    else if (pll == ALT_CLK_PERIPHERAL_PLL) { locked_mask = ALT_CLKMGR_INTER_PERPLLLOCKED_SET_MSK; }
    else if (pll == ALT_CLK_SDRAM_PLL)      { locked_mask = ALT_CLKMGR_INTER_SDRPLLLOCKED_SET_MSK; }
    else
    {
        return ALT_E_BAD_ARG;
    }

    do
    {
        uint32_t int_status = alt_read_word(ALT_CLKMGR_INTER_ADDR);
        if (int_status & locked_mask)
        {
            return ALT_E_SUCCESS;
        }

    } while (timeout--);

    return ALT_E_TMO;
}

        /* Useful utility macro for checking if two values  */
        /* are within a certain percentage of each other    */
#define  alt_within_delta(ref, neu, prcnt)  (((((neu) * 100)/(ref)) < (100 + (prcnt))) \
                                            && ((((neu) * 100)/(ref)) > (100 - (prcnt))))


        /* Flags to include or omit code sections */
// There are four cases where there is a small possibility of producing clock
// glitches. Code has been added from an abundance of caution to prevent
// these glitches. If further testing shows that this extra code is not necessary
// under any conditions, it may be easily eliminated by clearing these flags.

#define ALT_PREVENT_GLITCH_BYP              true
// for PLL entering or leaving bypass
#define ALT_PREVENT_GLITCH_EXSAFE           true
// for PLL exiting safe mode
#define ALT_PREVENT_GLITCH_CNTRRST          true
// resets counter phase
#define ALT_PREVENT_GLITCH_CHGC1            true
// for changing Main PLL C1 counter



/****************************************************************************************/
/* Bare-bones utility function used to make the somewhat complex writes to the PLL      */
/* counter registers (the clock dividers) easier. No parameter-checking or              */
/* error-checking, this is a static to this file and invisible to Doxygen.              */
/****************************************************************************************/

static void alt_clk_pllcounter_write(void* vcoaddr, void* stataddr, void* cntraddr,
        uint32_t val, uint32_t msk, uint32_t shift)
{
#if ALT_PREVENT_GLITCH_CNTRRST
    // this is here from an abundance of caution and it may not be necessary
    // to put the counter in reset for this write
    volatile uint32_t   temp;

    alt_setbits_word(vcoaddr, msk << shift);                // put the counter in reset
    do
    {
        temp = alt_read_word(stataddr);
    } while (!(temp & msk));

    alt_write_word(cntraddr, val);
    alt_clrbits_word(vcoaddr, msk << shift);                // release counter reset

#else       // should we find out that resetting the counters as above is unnecessary
    alt_write_word(cntraddr, val);
#endif
}


/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Main Functions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/


/****************************************************************************************/
/* alt_clk_lock_status_clear() clears assertions of one or more of the PLL lock status  */
/* conditions.                                                                          */
/****************************************************************************************/

ALT_STATUS_CODE alt_clk_lock_status_clear(ALT_CLK_PLL_LOCK_STATUS_t lock_stat_mask)
{
    if (lock_stat_mask & (  ALT_CLKMGR_INTER_MAINPLLACHIEVED_CLR_MSK
                          & ALT_CLKMGR_INTER_PERPLLACHIEVED_CLR_MSK
                          & ALT_CLKMGR_INTER_SDRPLLACHIEVED_CLR_MSK
                          & ALT_CLKMGR_INTER_MAINPLLLOST_CLR_MSK
                          & ALT_CLKMGR_INTER_PERPLLLOST_CLR_MSK
                          & ALT_CLKMGR_INTER_SDRPLLLOST_CLR_MSK)
        )
    {
        return ALT_E_BAD_ARG;
    }
    else
    {
        alt_setbits_word(ALT_CLKMGR_INTER_ADDR, lock_stat_mask);
        return ALT_E_SUCCESS;
    }
}


/****************************************************************************************/
/* alt_clk_lock_status_get() returns the value of the PLL lock status conditions.       */
/****************************************************************************************/

uint32_t alt_clk_lock_status_get(void)
{
    return alt_read_word(ALT_CLKMGR_INTER_ADDR) & (  ALT_CLKMGR_INTER_MAINPLLACHIEVED_SET_MSK
                                                   | ALT_CLKMGR_INTER_PERPLLACHIEVED_SET_MSK
                                                   | ALT_CLKMGR_INTER_SDRPLLACHIEVED_SET_MSK
                                                   | ALT_CLKMGR_INTER_MAINPLLLOST_SET_MSK
                                                   | ALT_CLKMGR_INTER_PERPLLLOST_SET_MSK
                                                   | ALT_CLKMGR_INTER_SDRPLLLOST_SET_MSK
                                                   | ALT_CLKMGR_INTER_MAINPLLLOCKED_SET_MSK
                                                   | ALT_CLKMGR_INTER_PERPLLLOCKED_SET_MSK
                                                   | ALT_CLKMGR_INTER_SDRPLLLOCKED_SET_MSK );
}


/****************************************************************************************/
/* alt_clk_pll_is_locked() returns ALT_E_TRUE if the designated PLL is currently        */
/* locked and ALT_E_FALSE if not.                                                       */
/****************************************************************************************/

ALT_STATUS_CODE alt_clk_pll_is_locked(ALT_CLK_t pll)
{
    ALT_STATUS_CODE status = ALT_E_BAD_ARG;

    if (pll == ALT_CLK_MAIN_PLL)
    {
        status = (alt_read_word(ALT_CLKMGR_INTER_ADDR) & ALT_CLKMGR_INTER_MAINPLLLOCKED_SET_MSK)
                ? ALT_E_TRUE : ALT_E_FALSE;
    }
    else if (pll == ALT_CLK_PERIPHERAL_PLL)
    {
        status = (alt_read_word(ALT_CLKMGR_INTER_ADDR) & ALT_CLKMGR_INTER_PERPLLLOCKED_SET_MSK)
                ? ALT_E_TRUE : ALT_E_FALSE;
    }
    else if (pll == ALT_CLK_SDRAM_PLL)
    {
        status = (alt_read_word(ALT_CLKMGR_INTER_ADDR) & ALT_CLKMGR_INTER_SDRPLLLOCKED_SET_MSK)
                ? ALT_E_TRUE : ALT_E_FALSE;
    }
    return status;
}


/****************************************************************************************/
/* alt_clk_safe_mode_clear() clears the safe mode status of the Clock Manager following */
/* a reset.                                                                             */
/****************************************************************************************/

ALT_STATUS_CODE alt_clk_safe_mode_clear(void)
{
    ALT_STATUS_CODE status = ALT_E_ERROR;
#if ALT_PREVENT_GLITCH_EXSAFE
    uint32_t        temp;

    temp = alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR);
    alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp &
            (ALT_CLKMGR_MAINPLL_EN_L4MPCLK_CLR_MSK & ALT_CLKMGR_MAINPLL_EN_L4SPCLK_CLR_MSK));
                    // gate off l4MP and L4SP clocks (no matter their source)

    alt_setbits_word(ALT_CLKMGR_CTL_ADDR, ALT_CLKMGR_CTL_SAFEMOD_SET_MSK);
                    // clear safe mode bit
    status = alt_clk_plls_settle_wait();
    alt_replbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR,
            ALT_CLKMGR_MAINPLL_EN_L4MPCLK_SET_MSK | ALT_CLKMGR_MAINPLL_EN_L4SPCLK_SET_MSK,
            temp);
                    // gate l4MP and L4SP clocks back on if they were on previously

#else
    alt_setbits_word(ALT_CLKMGR_CTL_ADDR, ALT_CLKMGR_CTL_SAFEMOD_SET_MSK);
                    // clear safe mode bit
    status = alt_clk_plls_settle_wait();

#endif
    return status;
}


/****************************************************************************************/
/* alt_clk_is_in_safe_mode() returns whether the specified safe mode clock domain is in */
/* safe mode or not.                                                                    */
/****************************************************************************************/

bool alt_clk_is_in_safe_mode(ALT_CLK_SAFE_DOMAIN_t clk_domain)
{
    bool        ret = false;
    uint32_t    temp;

    if (clk_domain == ALT_CLK_DOMAIN_NORMAL)
    {
        ret = alt_read_word(ALT_CLKMGR_CTL_ADDR) & ALT_CLKMGR_CTL_SAFEMOD_SET_MSK;
                // is the main clock domain in safe mode?
    }
    else if (clk_domain == ALT_CLK_DOMAIN_DEBUG)
    {
        temp = alt_read_word(ALT_CLKMGR_DBCTL_ADDR);
        if (temp & ALT_CLKMGR_DBCTL_STAYOSC1_SET_MSK)
        {
            ret = true;                // is the debug clock domain in safe mode?
        }
        else if (temp & ALT_CLKMGR_DBCTL_ENSFMDWR_SET_MSK)
        {
            ret = alt_read_word(ALT_CLKMGR_CTL_ADDR) & ALT_CLKMGR_CTL_SAFEMOD_SET_MSK;
                    // is the debug clock domain following the main clock domain
                    // AND is the main clock domain in safe mode?
        }
    }
    return ret;
}

/****************************************************************************************/
/* alt_clk_pll_bypass_disable() disables bypass mode for the specified PLL, removing    */
/* it from bypass mode and allowing it to provide the output of the PLL to drive the    */
/* six main clocks.                                                                     */
/****************************************************************************************/

ALT_STATUS_CODE alt_clk_pll_bypass_disable(ALT_CLK_t pll)
{
    ALT_STATUS_CODE status = ALT_E_BAD_ARG;
    uint32_t        temp;
#if  ALT_PREVENT_GLITCH_BYP
    uint32_t        temp1;
    bool            restore_0 = false;
    bool            restore_1 = false;
#endif

    // this function should only be called after the selected PLL is locked
    if (alt_clk_pll_is_locked(pll) == ALT_E_TRUE)
    {
        if (pll == ALT_CLK_MAIN_PLL)
        {
#if  ALT_PREVENT_GLITCH_BYP
            // if L4MP or L4SP source is set to Main PLL C1, gate it off before changing
            // bypass state, then gate clock back on. FogBugz #63778
            temp  = alt_read_word(ALT_CLKMGR_MAINPLL_L4SRC_ADDR);
            temp1 = alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR);

            if ((temp1 & ALT_CLKMGR_MAINPLL_EN_L4MPCLK_SET_MSK) && (!(temp & ALT_CLKMGR_MAINPLL_L4SRC_L4MP_SET_MSK)))
            {
                restore_0 = true;
            }
            if ((temp1 & ALT_CLKMGR_MAINPLL_EN_L4SPCLK_SET_MSK) && (!(temp & ALT_CLKMGR_MAINPLL_L4SRC_L4SP_SET_MSK)))
            {
                restore_1 = true;
            }
            temp = temp1;
            if (restore_0) { temp &= ALT_CLKMGR_MAINPLL_EN_L4MPCLK_CLR_MSK; }
            if (restore_1) { temp &= ALT_CLKMGR_MAINPLL_EN_L4SPCLK_CLR_MSK; }
            if (restore_0 || restore_1) { alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp); }
#endif

            // assert outresetall of main PLL
            temp = alt_read_word(ALT_CLKMGR_MAINPLL_VCO_ADDR);
            alt_write_word(ALT_CLKMGR_MAINPLL_VCO_ADDR, temp | ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL_SET_MSK);

            // deassert outresetall of main PLL
            alt_write_word(ALT_CLKMGR_MAINPLL_VCO_ADDR, temp & ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL_CLR_MSK);

            alt_clk_plls_settle_wait();

            // remove bypass
            alt_clrbits_word(ALT_CLKMGR_BYPASS_ADDR, ALT_CLKMGR_BYPASS_MAINPLL_SET_MSK);
            status = alt_clk_plls_settle_wait();

#if  ALT_PREVENT_GLITCH_BYP
            if (restore_0 || restore_1)
            {
                alt_clk_mgr_wait(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
                            // wait a bit more before reenabling the L4MP and L4SP clocks
                alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp1);
            }
#endif
        }

        else if (pll == ALT_CLK_PERIPHERAL_PLL)
        {
#if  ALT_PREVENT_GLITCH_BYP
            // if L4MP or L4SP source is set to Main PLL C1, gate it off before changing
            // bypass state, then gate clock back on. FogBugz #63778
            temp = alt_read_word(ALT_CLKMGR_MAINPLL_L4SRC_ADDR);
            temp1 = alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR);

            if ((temp1 & ALT_CLKMGR_MAINPLL_EN_L4MPCLK_SET_MSK) && (temp & ALT_CLKMGR_MAINPLL_L4SRC_L4MP_SET_MSK))
            {
                    restore_0 = true;
            }
            if ((temp1 & ALT_CLKMGR_MAINPLL_EN_L4SPCLK_SET_MSK) && (temp & ALT_CLKMGR_MAINPLL_L4SRC_L4SP_SET_MSK))
            {
                    restore_1 = true;
            }
            temp = temp1;
            if (restore_0)  { temp &= ALT_CLKMGR_MAINPLL_EN_L4MPCLK_CLR_MSK; }
            if (restore_1)  { temp &= ALT_CLKMGR_MAINPLL_EN_L4SPCLK_CLR_MSK; }
            if (restore_0 || restore_1) { alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp); }
#endif

            // assert outresetall of Peripheral PLL
            temp = alt_read_word(ALT_CLKMGR_PERPLL_VCO_ADDR);
            alt_write_word(ALT_CLKMGR_PERPLL_VCO_ADDR, temp | ALT_CLKMGR_PERPLL_VCO_OUTRSTALL_SET_MSK);
            alt_clk_plls_settle_wait();

            // deassert outresetall of main PLL
            alt_write_word(ALT_CLKMGR_PERPLL_VCO_ADDR, temp & ALT_CLKMGR_PERPLL_VCO_OUTRSTALL_CLR_MSK);

            // remove bypass - don't think that there's any need to touch the bypass clock source
            alt_clrbits_word(ALT_CLKMGR_BYPASS_ADDR, ALT_CLKMGR_BYPASS_PERPLL_SET_MSK);
            status = alt_clk_plls_settle_wait();

#if  ALT_PREVENT_GLITCH_BYP
            if (restore_0 || restore_1)
            {
                alt_clk_mgr_wait(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
                            // wait a bit more before reenabling the L4MP and L4SP clocks
                alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp1);
            }
#endif
        }

        else if (pll == ALT_CLK_SDRAM_PLL)
        {
            // assert outresetall of SDRAM PLL
            temp = alt_read_word(ALT_CLKMGR_SDRPLL_VCO_ADDR);
            alt_write_word(ALT_CLKMGR_SDRPLL_VCO_ADDR, temp | ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL_SET_MSK);

            // deassert outresetall of main PLL
            alt_write_word(ALT_CLKMGR_SDRPLL_VCO_ADDR, temp & ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL_CLR_MSK);
            alt_clk_plls_settle_wait();

            // remove bypass - don't think that there's any need to touch the bypass clock source
            alt_clrbits_word(ALT_CLKMGR_BYPASS_ADDR, ALT_CLKMGR_BYPASS_SDRPLLSRC_SET_MSK);
            status = alt_clk_plls_settle_wait();
        }
    }
    else
    {
        status = ALT_E_ERROR;
    }

    return status;
}


/****************************************************************************************/
/* alt_clk_pll_bypass_enable() enable bypass mode for the specified PLL.                */
/****************************************************************************************/

ALT_STATUS_CODE alt_clk_pll_bypass_enable(ALT_CLK_t pll, bool use_input_mux)
{
    ALT_STATUS_CODE status = ALT_E_BAD_ARG;
    uint32_t        temp;
#ifdef  ALT_PREVENT_GLITCH_BYP
    uint32_t        temp1;
    bool            restore_0 = false;
    bool            restore_1 = false;
#endif

    if (pll == ALT_CLK_MAIN_PLL)
    {
        if (!use_input_mux)
        {
#ifdef  ALT_PREVENT_GLITCH_BYP
            // if L4MP or L4SP source is set to Main PLL C1, gate it off before changing
            // bypass state, then gate clock back on. FogBugz #63778
            temp  = alt_read_word(ALT_CLKMGR_MAINPLL_L4SRC_ADDR);
            temp1 = alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR);

            if ((temp1 & ALT_CLKMGR_MAINPLL_EN_L4MPCLK_SET_MSK) && (!(temp & ALT_CLKMGR_MAINPLL_L4SRC_L4MP_SET_MSK)))
            {
                restore_0 = true;
            }
            if ((temp1 & ALT_CLKMGR_MAINPLL_EN_L4SPCLK_SET_MSK) && (!(temp & ALT_CLKMGR_MAINPLL_L4SRC_L4SP_SET_MSK)))
            {
                restore_1 = true;
            }
            temp = temp1;
            if (restore_0) { temp &= ALT_CLKMGR_MAINPLL_EN_L4MPCLK_CLR_MSK; }
            if (restore_1) { temp &= ALT_CLKMGR_MAINPLL_EN_L4SPCLK_CLR_MSK; }
            if (restore_0 || restore_1) { alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp); }

            alt_setbits_word(ALT_CLKMGR_BYPASS_ADDR, ALT_CLKMGR_BYPASS_MAINPLL_SET_MSK);
                        // no input mux select on main PLL

            status = alt_clk_plls_settle_wait();
                        // wait before reenabling the L4MP and L4SP clocks
            if (restore_0 || restore_1) { alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp1); }

#else
            alt_setbits_word(ALT_CLKMGR_BYPASS_ADDR, ALT_CLKMGR_BYPASS_MAINPLL_SET_MSK);
                        // no input mux select on main PLL
            status = alt_clk_plls_settle_wait();

#endif
            status = ALT_E_SUCCESS;
        }
        else
        {
            status =  ALT_E_BAD_ARG;
        }
    }
    else if (pll == ALT_CLK_PERIPHERAL_PLL)
    {
#ifdef  ALT_PREVENT_GLITCH_BYP
        // if L4MP or L4SP source is set to Peripheral PLL C1, gate it off before changing
        // bypass state, then gate clock back on. FogBugz #63778
        temp  = alt_read_word(ALT_CLKMGR_MAINPLL_L4SRC_ADDR);
        temp1 = alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR);

        if ((temp1 & ALT_CLKMGR_MAINPLL_EN_L4MPCLK_SET_MSK) && (temp & ALT_CLKMGR_MAINPLL_L4SRC_L4MP_SET_MSK))
        {
            restore_0 = true;
        }
        if ((temp1 & ALT_CLKMGR_MAINPLL_EN_L4SPCLK_SET_MSK) && (temp & ALT_CLKMGR_MAINPLL_L4SRC_L4SP_SET_MSK))
        {
            restore_1 = true;
        }
        temp = temp1;
        if (restore_0) { temp &= ALT_CLKMGR_MAINPLL_EN_L4MPCLK_CLR_MSK; }
        if (restore_1) { temp &= ALT_CLKMGR_MAINPLL_EN_L4SPCLK_CLR_MSK; }
        if (restore_0 || restore_1) { alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp); }

        temp = alt_read_word(ALT_CLKMGR_BYPASS_ADDR) &
                (ALT_CLKMGR_BYPASS_PERPLL_CLR_MSK & ALT_CLKMGR_BYPASS_PERPLLSRC_CLR_MSK);
        temp |= (use_input_mux) ? ALT_CLKMGR_BYPASS_PERPLL_SET_MSK |
                ALT_CLKMGR_BYPASS_PERPLLSRC_SET_MSK : ALT_CLKMGR_BYPASS_PERPLL_SET_MSK;
                    // set bypass bit and optionally the source select bit

        alt_write_word(ALT_CLKMGR_BYPASS_ADDR, temp);
        alt_clk_mgr_wait(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
                    // wait a bit before reenabling the L4MP and L4SP clocks
        if (restore_0 || restore_1) { alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp1); }

#else
        temp = alt_read_word(ALT_CLKMGR_BYPASS_ADDR) &
                (ALT_CLKMGR_BYPASS_PERPLL_CLR_MSK & ALT_CLKMGR_BYPASS_PERPLLSRC_CLR_MSK);
        temp |= (use_input_mux) ? ALT_CLKMGR_BYPASS_PERPLL_SET_MSK |
                ALT_CLKMGR_BYPASS_PERPLLSRC_SET_MSK : ALT_CLKMGR_BYPASS_PERPLL_SET_MSK;
                    // set bypass bit and optionally the source select bit
#endif
        status = ALT_E_SUCCESS;
    }

    else if (pll == ALT_CLK_SDRAM_PLL)
    {
        temp = alt_read_word(ALT_CLKMGR_BYPASS_ADDR) &
                (ALT_CLKMGR_BYPASS_SDRPLL_CLR_MSK & ALT_CLKMGR_BYPASS_SDRPLLSRC_CLR_MSK);
        temp |= (use_input_mux) ? ALT_CLKMGR_BYPASS_SDRPLL_SET_MSK |
                ALT_CLKMGR_BYPASS_SDRPLLSRC_SET_MSK : ALT_CLKMGR_BYPASS_SDRPLL_SET_MSK;
                    // set bypass bit and optionally the source select bit
        alt_write_word(ALT_CLKMGR_BYPASS_ADDR, temp);
        status = ALT_E_SUCCESS;
    }
    return status;
}


/****************************************************************************************/
/* alt_clk_pll_is_bypassed() returns whether the specified PLL is in bypass or not.     */
/* Bypass is a special state where the PLL VCO and the C0-C5 counters are bypassed      */
/* and not in the circuit. Either the Osc1 clock input or the input chosen by the       */
/* input mux may be selected to be operational in the bypass state. All changes to      */
/* the PLL VCO must be made in bypass mode to avoid the potential of producing clock    */
/* glitches which may affect downstream clock dividers and peripherals.                 */
/****************************************************************************************/

ALT_STATUS_CODE alt_clk_pll_is_bypassed(ALT_CLK_t pll)
{
    ALT_STATUS_CODE status = ALT_E_BAD_ARG;

    if (pll == ALT_CLK_MAIN_PLL)
    {
        status = (ALT_CLKMGR_CTL_SAFEMOD_GET(alt_read_word(ALT_CLKMGR_CTL_ADDR))
                || ALT_CLKMGR_BYPASS_MAINPLL_GET(alt_read_word(ALT_CLKMGR_BYPASS_ADDR)))
                ? ALT_E_TRUE : ALT_E_FALSE;
    }
    else if (pll == ALT_CLK_PERIPHERAL_PLL)
    {
        status = (ALT_CLKMGR_CTL_SAFEMOD_GET(alt_read_word(ALT_CLKMGR_CTL_ADDR))
                || ALT_CLKMGR_BYPASS_PERPLL_GET(alt_read_word(ALT_CLKMGR_BYPASS_ADDR)))
                ? ALT_E_TRUE : ALT_E_FALSE;
    }
    else if (pll == ALT_CLK_SDRAM_PLL)
    {
        status = (ALT_CLKMGR_CTL_SAFEMOD_GET(alt_read_word(ALT_CLKMGR_CTL_ADDR))
                || ALT_CLKMGR_BYPASS_SDRPLL_GET(alt_read_word(ALT_CLKMGR_BYPASS_ADDR)))
                ? ALT_E_TRUE : ALT_E_FALSE;
    }
    return status;
}


/****************************************************************************************/
/* alt_clk_pll_source_get() returns the current input of the specified PLL.             */
/****************************************************************************************/

ALT_CLK_t alt_clk_pll_source_get(ALT_CLK_t pll)
{
    ALT_CLK_t      ret = ALT_CLK_UNKNOWN;
    uint32_t       temp;


    if (pll == ALT_CLK_MAIN_PLL)
    {
        ret = ALT_CLK_IN_PIN_OSC1;
    }
    else if (pll == ALT_CLK_PERIPHERAL_PLL)
    {
        // three possible clock sources for the peripheral PLL
        temp = ALT_CLKMGR_PERPLL_VCO_PSRC_GET(alt_read_word(ALT_CLKMGR_PERPLL_VCO_ADDR));
        if (temp == ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC1)
        {
            ret = ALT_CLK_IN_PIN_OSC1;
        }
        else if (temp == ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC2)
        {
            ret = ALT_CLK_IN_PIN_OSC2;
        }
        else if (temp == ALT_CLKMGR_PERPLL_VCO_PSRC_E_F2S_PERIPH_REF)
        {
            ret = ALT_CLK_F2H_PERIPH_REF;
        }
    }
    else if (pll == ALT_CLK_SDRAM_PLL)
    {
        // three possible clock sources for the SDRAM PLL
        temp = ALT_CLKMGR_SDRPLL_VCO_SSRC_GET(alt_read_word(ALT_CLKMGR_SDRPLL_VCO_ADDR));
        if (temp == ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC1)
        {
            ret = ALT_CLK_IN_PIN_OSC1;
        }
        else if (temp == ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC2)
        {
            ret = ALT_CLK_IN_PIN_OSC2;
        }
        else if (temp == ALT_CLKMGR_SDRPLL_VCO_SSRC_E_F2S_SDRAM_REF)
        {
            ret = ALT_CLK_F2H_SDRAM_REF;
        }
    }
    return ret;
}

//
// alt_clk_clock_disable() disables the specified clock. Once the clock is disabled,
// its clock signal does not propagate to its clocked elements.
//
ALT_STATUS_CODE alt_clk_clock_disable(ALT_CLK_t clk)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    switch (clk)
    {
        // For PLLs, put them in bypass mode.
    case ALT_CLK_MAIN_PLL:
    case ALT_CLK_PERIPHERAL_PLL:
    case ALT_CLK_SDRAM_PLL:
        status = alt_clk_pll_bypass_enable(clk, false);
        break;

        // Clocks that originate at the Main PLL.
    case ALT_CLK_L4_MAIN:
        alt_clrbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_L4MAINCLK_SET_MSK);
        break;
    case ALT_CLK_L3_MP:
        alt_clrbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_L3MPCLK_SET_MSK);
        break;
    case ALT_CLK_L4_MP:
        alt_clrbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_L4MPCLK_SET_MSK);
        break;
    case ALT_CLK_L4_SP:
        alt_clrbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_L4SPCLK_SET_MSK);
        break;
    case ALT_CLK_DBG_AT:
        alt_clrbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_DBGATCLK_SET_MSK);
        break;
    case ALT_CLK_DBG:
        alt_clrbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_DBGCLK_SET_MSK);
        break;
    case ALT_CLK_DBG_TRACE:
        alt_clrbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK_SET_MSK);
        break;
    case ALT_CLK_DBG_TIMER:
        alt_clrbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK_SET_MSK);
        break;
    case ALT_CLK_CFG:
        alt_clrbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_CFGCLK_SET_MSK);
        break;
    case ALT_CLK_H2F_USER0:
        alt_clrbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK_SET_MSK);
        break;

        // Clocks that originate at the Peripheral PLL.
    case ALT_CLK_EMAC0:
        alt_clrbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_EMAC0CLK_SET_MSK);
        break;
    case ALT_CLK_EMAC1:
        alt_clrbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_EMAC1CLK_SET_MSK);
        break;
    case ALT_CLK_USB_MP:
        alt_clrbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_USBCLK_SET_MSK);
        break;
    case ALT_CLK_SPI_M:
        alt_clrbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_SPIMCLK_SET_MSK);
        break;
    case ALT_CLK_CAN0:
        alt_clrbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_CAN0CLK_SET_MSK);
        break;
    case ALT_CLK_CAN1:
        alt_clrbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_CAN1CLK_SET_MSK);
        break;
    case ALT_CLK_GPIO_DB:
        alt_clrbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_GPIOCLK_SET_MSK);
        break;
    case ALT_CLK_H2F_USER1:
        alt_clrbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK_SET_MSK);
        break;
    case ALT_CLK_SDMMC:
        alt_clrbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_SDMMCCLK_SET_MSK);
        break;
    case ALT_CLK_NAND_X:
        alt_clrbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_NANDCLK_SET_MSK);
        alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_SW_MANAGED_CLK_WAIT_NANDCLK);
        // gate nand_clk off before nand_x_clk.
        alt_clrbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_NANDXCLK_SET_MSK);
        break;
    case ALT_CLK_NAND:
        alt_clrbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_NANDCLK_SET_MSK);
        break;
    case ALT_CLK_QSPI:
        alt_clrbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_QSPICLK_SET_MSK);
        break;

        // Clocks that originate at the SDRAM PLL.
    case ALT_CLK_DDR_DQS:
        alt_clrbits_word(ALT_CLKMGR_SDRPLL_EN_ADDR, ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK_SET_MSK);
        break;
    case ALT_CLK_DDR_2X_DQS:
        alt_clrbits_word(ALT_CLKMGR_SDRPLL_EN_ADDR, ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK_SET_MSK);
        break;
    case ALT_CLK_DDR_DQ:
        alt_clrbits_word(ALT_CLKMGR_SDRPLL_EN_ADDR, ALT_CLKMGR_SDRPLL_EN_DDRDQCLK_SET_MSK);
        break;
    case ALT_CLK_H2F_USER2:
        alt_clrbits_word(ALT_CLKMGR_SDRPLL_EN_ADDR, ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK_SET_MSK);
        break;

    default:
        status = ALT_E_BAD_ARG;
        break;
    }

    return status;
}


//
// alt_clk_clock_enable() enables the specified clock. Once the clock is enabled, its
// clock signal propagates to its elements.
//
ALT_STATUS_CODE alt_clk_clock_enable(ALT_CLK_t clk)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    switch (clk)
    {
        // For PLLs, take them out of bypass mode.
    case ALT_CLK_MAIN_PLL:
    case ALT_CLK_PERIPHERAL_PLL:
    case ALT_CLK_SDRAM_PLL:
        status = alt_clk_pll_bypass_disable(clk);
        break;

        // Clocks that originate at the Main PLL.
    case ALT_CLK_L4_MAIN:
        alt_setbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_L4MAINCLK_SET_MSK);
        break;
    case ALT_CLK_L3_MP:
        alt_setbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_L3MPCLK_SET_MSK);
        break;
    case ALT_CLK_L4_MP:
        alt_setbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_L4MPCLK_SET_MSK);
        break;
    case ALT_CLK_L4_SP:
        alt_setbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_L4SPCLK_SET_MSK);
        break;
    case ALT_CLK_DBG_AT:
        alt_setbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_DBGATCLK_SET_MSK);
        break;
    case ALT_CLK_DBG:
        alt_setbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_DBGCLK_SET_MSK);
        break;
    case ALT_CLK_DBG_TRACE:
        alt_setbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK_SET_MSK);
        break;
    case ALT_CLK_DBG_TIMER:
        alt_setbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK_SET_MSK);
        break;
    case ALT_CLK_CFG:
        alt_setbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_CFGCLK_SET_MSK);
        break;
    case ALT_CLK_H2F_USER0:
        alt_setbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK_SET_MSK);
        break;

        // Clocks that originate at the Peripheral PLL.
    case ALT_CLK_EMAC0:
        alt_setbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_EMAC0CLK_SET_MSK);
        break;
    case ALT_CLK_EMAC1:
        alt_setbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_EMAC1CLK_SET_MSK);
        break;
    case ALT_CLK_USB_MP:
        alt_setbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_USBCLK_SET_MSK);
        break;
    case ALT_CLK_SPI_M:
        alt_setbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_SPIMCLK_SET_MSK);
        break;
    case ALT_CLK_CAN0:
        alt_setbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_CAN0CLK_SET_MSK);
        break;
    case ALT_CLK_CAN1:
        alt_setbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_CAN1CLK_SET_MSK);
        break;
    case ALT_CLK_GPIO_DB:
        alt_setbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_GPIOCLK_SET_MSK);
        break;
    case ALT_CLK_H2F_USER1:
        alt_setbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK_SET_MSK);
        break;
    case ALT_CLK_SDMMC:
        alt_setbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_SDMMCCLK_SET_MSK);
        break;
    case ALT_CLK_NAND_X:
        // implementation detail - should ALK_CLK_NAND be gated off here before enabling ALT_CLK_NAND_X?
        alt_setbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_NANDXCLK_SET_MSK);
        // implementation detail - should this wait be enforced here?
        alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_SW_MANAGED_CLK_WAIT_NANDCLK);
        break;
    case ALT_CLK_NAND:
        // enabling ALT_CLK_NAND always implies enabling ALT_CLK_NAND_X first
        alt_setbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_NANDXCLK_SET_MSK);
        alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_SW_MANAGED_CLK_WAIT_NANDCLK);
        // gate nand_x_clk on at least 8 MCU clocks before nand_clk
        alt_setbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_NANDCLK_SET_MSK);
        break;
    case ALT_CLK_QSPI:
        alt_setbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_QSPICLK_SET_MSK);
        break;

        // Clocks that originate at the SDRAM PLL.
    case ALT_CLK_DDR_DQS:
        alt_setbits_word(ALT_CLKMGR_SDRPLL_EN_ADDR, ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK_SET_MSK);
        break;
    case ALT_CLK_DDR_2X_DQS:
        alt_setbits_word(ALT_CLKMGR_SDRPLL_EN_ADDR, ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK_SET_MSK);
        break;
    case ALT_CLK_DDR_DQ:
        alt_setbits_word(ALT_CLKMGR_SDRPLL_EN_ADDR, ALT_CLKMGR_SDRPLL_EN_DDRDQCLK_SET_MSK);
        break;
    case ALT_CLK_H2F_USER2:
        alt_setbits_word(ALT_CLKMGR_SDRPLL_EN_ADDR, ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK_SET_MSK);
        break;

    default:
        status = ALT_E_BAD_ARG;
        break;
    }

    return status;
}

//
// alt_clk_is_enabled() returns whether the specified clock is enabled or not.
//
ALT_STATUS_CODE alt_clk_is_enabled(ALT_CLK_t clk)
{
    ALT_STATUS_CODE status = ALT_E_BAD_ARG;

    switch (clk)
    {
        // For PLLs, this function checks if the PLL is bypassed or not.
    case ALT_CLK_MAIN_PLL:
    case ALT_CLK_PERIPHERAL_PLL:
    case ALT_CLK_SDRAM_PLL:
        status = (alt_clk_pll_is_bypassed(clk) != ALT_E_TRUE);
        break;

        // These clocks are not gated, so must return a ALT_E_BAD_ARG type error.
    case ALT_CLK_MAIN_PLL_C0:
    case ALT_CLK_MAIN_PLL_C1:
    case ALT_CLK_MAIN_PLL_C2:
    case ALT_CLK_MAIN_PLL_C3:
    case ALT_CLK_MAIN_PLL_C4:
    case ALT_CLK_MAIN_PLL_C5:
    case ALT_CLK_MPU:
    case ALT_CLK_MPU_L2_RAM:
    case ALT_CLK_MPU_PERIPH:
    case ALT_CLK_L3_MAIN:
    case ALT_CLK_L3_SP:
    case ALT_CLK_DBG_BASE:
    case ALT_CLK_MAIN_QSPI:
    case ALT_CLK_MAIN_NAND_SDMMC:
    case ALT_CLK_PERIPHERAL_PLL_C0:
    case ALT_CLK_PERIPHERAL_PLL_C1:
    case ALT_CLK_PERIPHERAL_PLL_C2:
    case ALT_CLK_PERIPHERAL_PLL_C3:
    case ALT_CLK_PERIPHERAL_PLL_C4:
    case ALT_CLK_PERIPHERAL_PLL_C5:
    case ALT_CLK_SDRAM_PLL_C0:
    case ALT_CLK_SDRAM_PLL_C1:
    case ALT_CLK_SDRAM_PLL_C2:
    case ALT_CLK_SDRAM_PLL_C5:
        status = ALT_E_BAD_ARG;
        break;

        // Clocks that originate at the Main PLL.
    case ALT_CLK_L4_MAIN:
        status = (ALT_CLKMGR_MAINPLL_EN_L4MAINCLK_GET(alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_L3_MP:
        status = (ALT_CLKMGR_MAINPLL_EN_L3MPCLK_GET(alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_L4_MP:
        status = (ALT_CLKMGR_MAINPLL_EN_L4MPCLK_GET(alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_L4_SP:
        status = (ALT_CLKMGR_MAINPLL_EN_L4SPCLK_GET(alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_DBG_AT:
        status = (ALT_CLKMGR_MAINPLL_EN_DBGATCLK_GET(alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_DBG:
        status = (ALT_CLKMGR_MAINPLL_EN_DBGCLK_GET(alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_DBG_TRACE:
        status = (ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK_GET(alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_DBG_TIMER:
        status = (ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK_GET(alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_CFG:
        status = (ALT_CLKMGR_MAINPLL_EN_CFGCLK_GET(alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_H2F_USER0:
        status = (ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK_GET(alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;

        // Clocks that originate at the Peripheral PLL.
    case ALT_CLK_EMAC0:
        status = (ALT_CLKMGR_PERPLL_EN_EMAC0CLK_GET(alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_EMAC1:
        status = (ALT_CLKMGR_PERPLL_EN_EMAC1CLK_GET(alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_USB_MP:
        status = (ALT_CLKMGR_PERPLL_EN_USBCLK_GET(alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_SPI_M:
        status = (ALT_CLKMGR_PERPLL_EN_SPIMCLK_GET(alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_CAN0:
        status = (ALT_CLKMGR_PERPLL_EN_CAN0CLK_GET(alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_CAN1:
        status = (ALT_CLKMGR_PERPLL_EN_CAN1CLK_GET(alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_GPIO_DB:
        status = (ALT_CLKMGR_PERPLL_EN_GPIOCLK_GET(alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_H2F_USER1:
        status = (ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK_GET(alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;

        // Clocks that may originate at the Main PLL, the Peripheral PLL, or the FPGA.
    case ALT_CLK_SDMMC:
        status = (ALT_CLKMGR_PERPLL_EN_SDMMCCLK_GET(alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_NAND_X:
        status = (ALT_CLKMGR_PERPLL_EN_NANDXCLK_GET(alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_NAND:
        status = (ALT_CLKMGR_PERPLL_EN_NANDCLK_GET(alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_QSPI:
        status = (ALT_CLKMGR_PERPLL_EN_QSPICLK_GET(alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;

        // Clocks that originate at the SDRAM PLL.
    case ALT_CLK_DDR_DQS:
        status = (ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK_GET(alt_read_word(ALT_CLKMGR_SDRPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_DDR_2X_DQS:
        status = (ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK_GET(alt_read_word(ALT_CLKMGR_SDRPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_DDR_DQ:
        status = (ALT_CLKMGR_SDRPLL_EN_DDRDQCLK_GET(alt_read_word(ALT_CLKMGR_SDRPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;
    case ALT_CLK_H2F_USER2:
        status = (ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK_GET(alt_read_word(ALT_CLKMGR_SDRPLL_EN_ADDR)))
            ? ALT_E_TRUE : ALT_E_FALSE;
        break;

    default:
        status = ALT_E_BAD_ARG;
        break;

    }

    return status;
}

//
// alt_clk_source_get() gets the input reference clock source selection value for the
// specified clock or PLL.
//
ALT_CLK_t alt_clk_source_get(ALT_CLK_t clk)
{
    ALT_CLK_t ret = ALT_CLK_UNKNOWN;
    uint32_t  temp;

    switch (clk)
    {
        // Potential external clock sources.
        // these clock entities are their own source
    case ALT_CLK_IN_PIN_OSC1:
    case ALT_CLK_IN_PIN_OSC2:
    case ALT_CLK_F2H_PERIPH_REF:
    case ALT_CLK_F2H_SDRAM_REF:
    case ALT_CLK_IN_PIN_JTAG:
    case ALT_CLK_IN_PIN_ULPI0:
    case ALT_CLK_IN_PIN_ULPI1:
    case ALT_CLK_IN_PIN_EMAC0_RX:
    case ALT_CLK_IN_PIN_EMAC1_RX:
        ret = clk;
        break;

        // Phase-Locked Loops.
    case ALT_CLK_MAIN_PLL:
    case ALT_CLK_OSC1:
        ret = ALT_CLK_IN_PIN_OSC1;
        break;
    case ALT_CLK_PERIPHERAL_PLL:
        ret = alt_clk_pll_source_get(ALT_CLK_PERIPHERAL_PLL);
        break;
    case ALT_CLK_SDRAM_PLL:
        ret = alt_clk_pll_source_get(ALT_CLK_SDRAM_PLL);
        break;

        // Main Clock Group.
    case ALT_CLK_MAIN_PLL_C0:
    case ALT_CLK_MAIN_PLL_C1:
    case ALT_CLK_MAIN_PLL_C2:
    case ALT_CLK_MAIN_PLL_C3:
    case ALT_CLK_MAIN_PLL_C4:
    case ALT_CLK_MAIN_PLL_C5:
        // check bypass, return either osc1 or PLL ID
        ret = (alt_clk_pll_is_bypassed(ALT_CLK_MAIN_PLL) == ALT_E_TRUE) ?
            ALT_CLK_IN_PIN_OSC1 : ALT_CLK_MAIN_PLL;
        break;

    case ALT_CLK_MPU_PERIPH:
    case ALT_CLK_MPU_L2_RAM:
    case ALT_CLK_MPU:
        ret = (alt_clk_pll_is_bypassed(ALT_CLK_MAIN_PLL) == ALT_E_TRUE) ?
            ALT_CLK_IN_PIN_OSC1 : ALT_CLK_MAIN_PLL_C0;
        break;

    case ALT_CLK_L4_MAIN:
    case ALT_CLK_L3_MAIN:
    case ALT_CLK_L3_MP:
    case ALT_CLK_L3_SP:
        ret = (alt_clk_pll_is_bypassed(ALT_CLK_MAIN_PLL) == ALT_E_TRUE) ?
            ALT_CLK_IN_PIN_OSC1 : ALT_CLK_MAIN_PLL_C1;
        break;

    case ALT_CLK_L4_MP:
        // read the state of the L4_mp source bit
        if ((ALT_CLKMGR_MAINPLL_L4SRC_L4MP_GET(alt_read_word(ALT_CLKMGR_MAINPLL_L4SRC_ADDR)))
            == ALT_CLKMGR_MAINPLL_L4SRC_L4MP_E_MAINPLL)
        {
            ret = (alt_clk_pll_is_bypassed(ALT_CLK_MAIN_PLL) == ALT_E_TRUE) ?
                ALT_CLK_IN_PIN_OSC1 : ALT_CLK_MAIN_PLL_C1;
        }
        else
        {
            // if the clock comes from periph_base_clk
            ret = (alt_clk_pll_is_bypassed(ALT_CLK_PERIPHERAL_PLL) == ALT_E_TRUE) ?
                alt_clk_pll_source_get(ALT_CLK_PERIPHERAL_PLL) : ALT_CLK_PERIPHERAL_PLL_C4;
        }
        break;

    case ALT_CLK_L4_SP:
        // read the state of the source bit
        if ((ALT_CLKMGR_MAINPLL_L4SRC_L4SP_GET(alt_read_word(ALT_CLKMGR_MAINPLL_L4SRC_ADDR)))
            == ALT_CLKMGR_MAINPLL_L4SRC_L4SP_E_MAINPLL)
        {
            ret = (alt_clk_pll_is_bypassed(ALT_CLK_MAIN_PLL) == ALT_E_TRUE) ?
                ALT_CLK_IN_PIN_OSC1 : ALT_CLK_MAIN_PLL_C1;
        }
        else
        {
            // if the clock comes from periph_base_clk
            ret = (alt_clk_pll_is_bypassed(ALT_CLK_PERIPHERAL_PLL) == ALT_E_TRUE) ?
                alt_clk_pll_source_get(ALT_CLK_PERIPHERAL_PLL) : ALT_CLK_PERIPHERAL_PLL_C4;
        }
        break;

    case ALT_CLK_DBG_BASE:
    case ALT_CLK_DBG_AT:
    case ALT_CLK_DBG_TRACE:
    case ALT_CLK_DBG_TIMER:
    case ALT_CLK_DBG:
        ret = (alt_clk_pll_is_bypassed(ALT_CLK_MAIN_PLL) == ALT_E_TRUE) ?
            ALT_CLK_OSC1 : ALT_CLK_MAIN_PLL_C2;
        break;
    case ALT_CLK_MAIN_QSPI:
        ret = (alt_clk_pll_is_bypassed(ALT_CLK_MAIN_PLL) == ALT_E_TRUE) ?
            ALT_CLK_OSC1 : ALT_CLK_MAIN_PLL_C3;
        break;
    case ALT_CLK_MAIN_NAND_SDMMC:
        ret = (alt_clk_pll_is_bypassed(ALT_CLK_MAIN_PLL) == ALT_E_TRUE) ?
            ALT_CLK_OSC1 : ALT_CLK_MAIN_PLL_C4;
        break;
    case ALT_CLK_CFG:
    case ALT_CLK_H2F_USER0:
        ret = (alt_clk_pll_is_bypassed(ALT_CLK_MAIN_PLL) == ALT_E_TRUE) ?
            ALT_CLK_OSC1 : ALT_CLK_MAIN_PLL_C5;
        break;

        // Peripherals Clock Group
    case ALT_CLK_PERIPHERAL_PLL_C0:
    case ALT_CLK_PERIPHERAL_PLL_C1:
    case ALT_CLK_PERIPHERAL_PLL_C2:
    case ALT_CLK_PERIPHERAL_PLL_C3:
    case ALT_CLK_PERIPHERAL_PLL_C4:
    case ALT_CLK_PERIPHERAL_PLL_C5:
        // if the clock comes from periph_base_clk
        ret = (alt_clk_pll_is_bypassed(ALT_CLK_PERIPHERAL_PLL) == ALT_E_TRUE) ?
            alt_clk_pll_source_get(ALT_CLK_PERIPHERAL_PLL) : ALT_CLK_PERIPHERAL_PLL;
        break;

    case ALT_CLK_EMAC0:
        ret = (alt_clk_pll_is_bypassed(ALT_CLK_PERIPHERAL_PLL) == ALT_E_TRUE) ?
            alt_clk_pll_source_get(ALT_CLK_PERIPHERAL_PLL) :  ALT_CLK_PERIPHERAL_PLL_C0;
        break;

    case ALT_CLK_EMAC1:
        ret = (alt_clk_pll_is_bypassed(ALT_CLK_PERIPHERAL_PLL) == ALT_E_TRUE) ?
            alt_clk_pll_source_get(ALT_CLK_PERIPHERAL_PLL) :  ALT_CLK_PERIPHERAL_PLL_C1;
        break;

    case ALT_CLK_USB_MP:
    case ALT_CLK_SPI_M:
    case ALT_CLK_CAN0:
    case ALT_CLK_CAN1:
    case ALT_CLK_GPIO_DB:
        ret = (alt_clk_pll_is_bypassed(ALT_CLK_PERIPHERAL_PLL) == ALT_E_TRUE) ?
            alt_clk_pll_source_get(ALT_CLK_PERIPHERAL_PLL) :  ALT_CLK_PERIPHERAL_PLL_C4;
        break;

    case ALT_CLK_H2F_USER1:
        ret = (alt_clk_pll_is_bypassed(ALT_CLK_PERIPHERAL_PLL) == ALT_E_TRUE) ?
            alt_clk_pll_source_get(ALT_CLK_PERIPHERAL_PLL) :  ALT_CLK_PERIPHERAL_PLL_C5;
        break;

    case ALT_CLK_SDMMC:
        temp = ALT_CLKMGR_PERPLL_SRC_SDMMC_GET(alt_read_word(ALT_CLKMGR_PERPLL_SRC_ADDR));
        if (temp == ALT_CLKMGR_PERPLL_SRC_SDMMC_E_F2S_PERIPH_REF_CLK)
        {
            ret = ALT_CLK_F2H_PERIPH_REF;
        }
        else if (temp == ALT_CLKMGR_PERPLL_SRC_SDMMC_E_MAIN_NAND_CLK)
        {
            ret = (alt_clk_pll_is_bypassed(ALT_CLK_MAIN_PLL) == ALT_E_TRUE) ?
                ALT_CLK_IN_PIN_OSC1 : ALT_CLK_MAIN_PLL_C4;
        }
        else if (temp == ALT_CLKMGR_PERPLL_SRC_SDMMC_E_PERIPH_NAND_CLK)
        {
            ret = (alt_clk_pll_is_bypassed(ALT_CLK_PERIPHERAL_PLL) == ALT_E_TRUE) ?
                alt_clk_pll_source_get(ALT_CLK_PERIPHERAL_PLL) :  ALT_CLK_PERIPHERAL_PLL_C3;
        }
        break;

    case ALT_CLK_NAND_X:
    case ALT_CLK_NAND:
        temp = ALT_CLKMGR_PERPLL_SRC_NAND_GET(alt_read_word(ALT_CLKMGR_PERPLL_SRC_ADDR));
        if (temp == ALT_CLKMGR_PERPLL_SRC_NAND_E_F2S_PERIPH_REF_CLK)
        {
            ret = ALT_CLK_F2H_PERIPH_REF;
        }
        else if (temp == ALT_CLKMGR_PERPLL_SRC_NAND_E_MAIN_NAND_CLK)
        {
            ret = (alt_clk_pll_is_bypassed(ALT_CLK_MAIN_PLL) == ALT_E_TRUE) ?
                ALT_CLK_IN_PIN_OSC1 : ALT_CLK_MAIN_PLL_C4;
        }
        else if (temp == ALT_CLKMGR_PERPLL_SRC_NAND_E_PERIPH_NAND_CLK)
        {
            ret = (alt_clk_pll_is_bypassed(ALT_CLK_PERIPHERAL_PLL) == ALT_E_TRUE) ?
                alt_clk_pll_source_get(ALT_CLK_PERIPHERAL_PLL) :  ALT_CLK_PERIPHERAL_PLL_C3;
        }
        break;

    case ALT_CLK_QSPI:
        temp = ALT_CLKMGR_PERPLL_SRC_QSPI_GET(alt_read_word(ALT_CLKMGR_PERPLL_SRC_ADDR));
        if (temp == ALT_CLKMGR_PERPLL_SRC_QSPI_E_F2S_PERIPH_REF_CLK)
        {
            ret = ALT_CLK_F2H_PERIPH_REF;
        }
        else if (temp == ALT_CLKMGR_PERPLL_SRC_QSPI_E_MAIN_QSPI_CLK)
        {
            ret = (alt_clk_pll_is_bypassed(ALT_CLK_MAIN_PLL) == ALT_E_TRUE) ?
                ALT_CLK_IN_PIN_OSC1 : ALT_CLK_MAIN_PLL_C3;
        }
        else if (temp == ALT_CLKMGR_PERPLL_SRC_QSPI_E_PERIPH_QSPI_CLK)
        {
            ret = (alt_clk_pll_is_bypassed(ALT_CLK_PERIPHERAL_PLL) == ALT_E_TRUE) ?
                alt_clk_pll_source_get(ALT_CLK_PERIPHERAL_PLL) :  ALT_CLK_PERIPHERAL_PLL_C2;
        }
        break;

        // SDRAM Clock Group
    case ALT_CLK_SDRAM_PLL_C0:
    case ALT_CLK_SDRAM_PLL_C1:
    case ALT_CLK_SDRAM_PLL_C2:
    case ALT_CLK_SDRAM_PLL_C3:
    case ALT_CLK_SDRAM_PLL_C4:
    case ALT_CLK_SDRAM_PLL_C5:
        ret = (alt_clk_pll_is_bypassed(ALT_CLK_SDRAM_PLL) == ALT_E_TRUE) ?
            alt_clk_pll_source_get(ALT_CLK_SDRAM_PLL) :  ALT_CLK_SDRAM_PLL;
        break;
    case ALT_CLK_DDR_DQS:
        ret = (alt_clk_pll_is_bypassed(ALT_CLK_SDRAM_PLL) == ALT_E_TRUE) ?
            alt_clk_pll_source_get(ALT_CLK_SDRAM_PLL) :  ALT_CLK_SDRAM_PLL_C0;
        break;
    case ALT_CLK_DDR_2X_DQS:
        ret = (alt_clk_pll_is_bypassed(ALT_CLK_SDRAM_PLL) == ALT_E_TRUE) ?
            alt_clk_pll_source_get(ALT_CLK_SDRAM_PLL) :  ALT_CLK_SDRAM_PLL_C1;
        break;
    case ALT_CLK_DDR_DQ:
        ret = (alt_clk_pll_is_bypassed(ALT_CLK_SDRAM_PLL) == ALT_E_TRUE) ?
            alt_clk_pll_source_get(ALT_CLK_SDRAM_PLL) :  ALT_CLK_SDRAM_PLL_C2;
        break;
    case ALT_CLK_H2F_USER2:
        ret = (alt_clk_pll_is_bypassed(ALT_CLK_SDRAM_PLL) == ALT_E_TRUE) ?
            alt_clk_pll_source_get(ALT_CLK_SDRAM_PLL) :  ALT_CLK_SDRAM_PLL_C5;
        break;

        // Clock Output Pins
    case ALT_CLK_OUT_PIN_EMAC0_TX:
    case ALT_CLK_OUT_PIN_EMAC1_TX:
    case ALT_CLK_OUT_PIN_SDMMC:
    case ALT_CLK_OUT_PIN_I2C0_SCL:
    case ALT_CLK_OUT_PIN_I2C1_SCL:
    case ALT_CLK_OUT_PIN_I2C2_SCL:
    case ALT_CLK_OUT_PIN_I2C3_SCL:
    case ALT_CLK_OUT_PIN_SPIM0:
    case ALT_CLK_OUT_PIN_SPIM1:
    case ALT_CLK_OUT_PIN_QSPI:
        ret = ALT_CLK_UNKNOWN;
        break;

    default:
        ret = ALT_CLK_UNKNOWN;
        break;
    }

    return ret;
}

//
// alt_clk_source_set() sets the specified clock's input reference clock source
// selection to the specified input. It does not handle gating the specified clock
// off and back on, those are covered in other functions in this API, but it does
// verify that the clock is off before changing the divider or PLL. Note that the PLL
// must have regained phase-lock before being the bypass is disabled.
//
ALT_STATUS_CODE alt_clk_source_set(ALT_CLK_t clk, ALT_CLK_t ref_clk)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    uint32_t        temp;

    if (ALT_CLK_MAIN_PLL == clk)
    {
        if ((ref_clk == ALT_CLK_IN_PIN_OSC1) || (ref_clk == ALT_CLK_OSC1))
        {
            // ret = ALT_E_SUCCESS;
        }
        else
        {
            status = ALT_E_BAD_ARG;
        }
    }
    else if (ALT_CLK_PERIPHERAL_PLL == clk)
    {
        // the PLL must be bypassed before getting here
        temp  = alt_read_word(ALT_CLKMGR_PERPLL_VCO_ADDR);
        temp &= ALT_CLKMGR_PERPLL_VCO_PSRC_CLR_MSK;

        if ((ref_clk == ALT_CLK_IN_PIN_OSC1) || (ref_clk == ALT_CLK_OSC1))
        {
            temp |= ALT_CLKMGR_PERPLL_VCO_PSRC_SET(ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC1);
            alt_write_word(ALT_CLKMGR_PERPLL_VCO_ADDR, temp);
        }
        else if (ref_clk == ALT_CLK_IN_PIN_OSC2)
        {
            temp |= ALT_CLKMGR_PERPLL_VCO_PSRC_SET(ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC2);
            alt_write_word(ALT_CLKMGR_PERPLL_VCO_ADDR, temp);
        }
        else if (ref_clk == ALT_CLK_F2H_PERIPH_REF)
        {
            temp |= ALT_CLKMGR_PERPLL_VCO_PSRC_SET(ALT_CLKMGR_PERPLL_VCO_PSRC_E_F2S_PERIPH_REF);
            alt_write_word(ALT_CLKMGR_PERPLL_VCO_ADDR, temp);
        }
        else
        {
            status = ALT_E_INV_OPTION;
        }
    }
    else if (ALT_CLK_SDRAM_PLL == clk)
    {
        temp  = alt_read_word(ALT_CLKMGR_SDRPLL_VCO_ADDR);
        temp &= ALT_CLKMGR_SDRPLL_VCO_SSRC_CLR_MSK;

        if ((ref_clk == ALT_CLK_IN_PIN_OSC1) || (ref_clk == ALT_CLK_OSC1))
        {
            temp |= ALT_CLKMGR_SDRPLL_VCO_SSRC_SET(ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC1);
            alt_write_word(ALT_CLKMGR_SDRPLL_VCO_ADDR, temp);
        }
        else if (ref_clk == ALT_CLK_IN_PIN_OSC2)
        {
            temp |= ALT_CLKMGR_SDRPLL_VCO_SSRC_SET(ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC2);
            alt_write_word(ALT_CLKMGR_SDRPLL_VCO_ADDR, temp);
        }
        else if (ref_clk == ALT_CLK_F2H_SDRAM_REF)
        {
            temp |= ALT_CLKMGR_SDRPLL_VCO_SSRC_SET(ALT_CLKMGR_SDRPLL_VCO_SSRC_E_F2S_SDRAM_REF);
            alt_write_word(ALT_CLKMGR_SDRPLL_VCO_ADDR, temp);
        }
        else
        {
            status = ALT_E_INV_OPTION;
        }
    }
    else if ( ALT_CLK_L4_MP == clk)
    {
        // clock is gated off
        if (ref_clk == ALT_CLK_MAIN_PLL_C1)
        {
            alt_clrbits_word(ALT_CLKMGR_MAINPLL_L4SRC_ADDR, ALT_CLKMGR_MAINPLL_L4SRC_L4MP_SET_MSK);
        }
        else if (ref_clk == ALT_CLK_PERIPHERAL_PLL_C4)
        {
            alt_setbits_word(ALT_CLKMGR_MAINPLL_L4SRC_ADDR, ALT_CLKMGR_MAINPLL_L4SRC_L4MP_SET_MSK);
        }
        else
        {
            status = ALT_E_INV_OPTION;
        }
    }
    else if ( ALT_CLK_L4_SP == clk)
    {
        if (ref_clk == ALT_CLK_MAIN_PLL_C1)
        {
            alt_clrbits_word(ALT_CLKMGR_MAINPLL_L4SRC_ADDR, ALT_CLKMGR_MAINPLL_L4SRC_L4SP_SET_MSK);
        }
        else if (ref_clk == ALT_CLK_PERIPHERAL_PLL_C4)
        {
            alt_setbits_word(ALT_CLKMGR_MAINPLL_L4SRC_ADDR, ALT_CLKMGR_MAINPLL_L4SRC_L4SP_SET_MSK);
        }
        else
        {
            status = ALT_E_INV_OPTION;
        }
    }
    else if (ALT_CLK_SDMMC == clk)
    {
        temp  = alt_read_word(ALT_CLKMGR_PERPLL_SRC_ADDR);
        temp &= ALT_CLKMGR_PERPLL_SRC_SDMMC_CLR_MSK;

        if (ref_clk == ALT_CLK_F2H_PERIPH_REF)
        {
            temp |= ALT_CLKMGR_PERPLL_SRC_SDMMC_SET(ALT_CLKMGR_PERPLL_SRC_SDMMC_E_F2S_PERIPH_REF_CLK);
            alt_write_word(ALT_CLKMGR_PERPLL_SRC_ADDR, temp);
        }
        else if ((ref_clk == ALT_CLK_MAIN_PLL_C4) || (ref_clk == ALT_CLK_MAIN_NAND_SDMMC))
        {
            temp |= ALT_CLKMGR_PERPLL_SRC_SDMMC_SET(ALT_CLKMGR_PERPLL_SRC_SDMMC_E_MAIN_NAND_CLK);
            alt_write_word(ALT_CLKMGR_PERPLL_SRC_ADDR, temp);
        }
        else if (ref_clk == ALT_CLK_PERIPHERAL_PLL_C3)
        {
            temp |= ALT_CLKMGR_PERPLL_SRC_SDMMC_SET(ALT_CLKMGR_PERPLL_SRC_SDMMC_E_PERIPH_NAND_CLK);
            alt_write_word(ALT_CLKMGR_PERPLL_SRC_ADDR, temp);
        }
        else
        {
            status = ALT_E_INV_OPTION;
        }
    }
    else if ((ALT_CLK_NAND_X == clk) || ( ALT_CLK_NAND == clk))
    {
        temp = alt_read_word(ALT_CLKMGR_PERPLL_SRC_ADDR);
        temp &= ALT_CLKMGR_PERPLL_SRC_NAND_CLR_MSK;

        if (ref_clk == ALT_CLK_F2H_PERIPH_REF)
        {
            temp |= ALT_CLKMGR_PERPLL_SRC_NAND_SET(ALT_CLKMGR_PERPLL_SRC_NAND_E_F2S_PERIPH_REF_CLK);
            alt_write_word(ALT_CLKMGR_PERPLL_SRC_ADDR, temp);
        }
        else if ((ref_clk == ALT_CLK_MAIN_PLL_C4) || (ref_clk == ALT_CLK_MAIN_NAND_SDMMC))
        {
            temp |= ALT_CLKMGR_PERPLL_SRC_NAND_SET(ALT_CLKMGR_PERPLL_SRC_NAND_E_MAIN_NAND_CLK);
            alt_write_word(ALT_CLKMGR_PERPLL_SRC_ADDR, temp);
        }
        else if (ref_clk == ALT_CLK_PERIPHERAL_PLL_C3)
        {
            temp |= ALT_CLKMGR_PERPLL_SRC_NAND_SET(ALT_CLKMGR_PERPLL_SRC_NAND_E_PERIPH_NAND_CLK);
            alt_write_word(ALT_CLKMGR_PERPLL_SRC_ADDR, temp);
        }
        else
        {
            status = ALT_E_INV_OPTION;
        }
    }
    else if (ALT_CLK_QSPI == clk)
    {
        temp  = alt_read_word(ALT_CLKMGR_PERPLL_SRC_ADDR);
        temp &= ALT_CLKMGR_PERPLL_SRC_QSPI_CLR_MSK;

        if (ref_clk == ALT_CLK_F2H_PERIPH_REF)
        {
            temp |= ALT_CLKMGR_PERPLL_SRC_QSPI_SET(ALT_CLKMGR_PERPLL_SRC_QSPI_E_F2S_PERIPH_REF_CLK);
            alt_write_word(ALT_CLKMGR_PERPLL_SRC_ADDR, temp);
        }
        else if ((ref_clk == ALT_CLK_MAIN_PLL_C3) || (ref_clk == ALT_CLK_MAIN_QSPI))
        {
            temp |= ALT_CLKMGR_PERPLL_SRC_QSPI_SET(ALT_CLKMGR_PERPLL_SRC_QSPI_E_MAIN_QSPI_CLK);
            alt_write_word(ALT_CLKMGR_PERPLL_SRC_ADDR, temp);
        }
        else if (ref_clk == ALT_CLK_PERIPHERAL_PLL_C2)
        {
            temp |= ALT_CLKMGR_PERPLL_SRC_QSPI_SET(ALT_CLKMGR_PERPLL_SRC_QSPI_E_PERIPH_QSPI_CLK);
            alt_write_word(ALT_CLKMGR_PERPLL_SRC_ADDR, temp);
        }
        else
        {
            status = ALT_E_INV_OPTION;
        }
    }

    return status;
}

//
// alt_clk_ext_clk_freq_set() specifies the frequency of the external clock source as
// a measure of Hz. This value is stored in a static array and used for calculations.
// The supplied frequency should be within the Fmin and Fmax values allowed for the
// external clock source.
//
ALT_STATUS_CODE alt_clk_ext_clk_freq_set(ALT_CLK_t clk, alt_freq_t freq)
{
    ALT_STATUS_CODE status = ALT_E_BAD_ARG;

    if ((clk == ALT_CLK_IN_PIN_OSC1) || (clk == ALT_CLK_OSC1))      // two names for one input
    {
        if ((freq >= alt_ext_clk_paramblok.clkosc1.freqmin) && (freq <= alt_ext_clk_paramblok.clkosc1.freqmax))
        {
            alt_ext_clk_paramblok.clkosc1.freqcur = freq;
            status = ALT_E_SUCCESS;
        }
        else
        {
            status = ALT_E_ARG_RANGE;
        }
    }
    else if (clk == ALT_CLK_IN_PIN_OSC2)                            // the other clock input pin
    {
        if ((freq >= alt_ext_clk_paramblok.clkosc2.freqmin) && (freq <= alt_ext_clk_paramblok.clkosc2.freqmax))
        {
            alt_ext_clk_paramblok.clkosc2.freqcur = freq;
            status = ALT_E_SUCCESS;
        }
        else
        {
            status = ALT_E_ARG_RANGE;
        }
    }
    else if (clk == ALT_CLK_F2H_PERIPH_REF)                         // clock from the FPGA
    {
        if ((freq >= alt_ext_clk_paramblok.periph.freqmin) && (freq <= alt_ext_clk_paramblok.periph.freqmax))
        {
            alt_ext_clk_paramblok.periph.freqcur = freq;
            status = ALT_E_SUCCESS;
        }
        else
        {
            status = ALT_E_ARG_RANGE;
        }
    }
    else if (clk == ALT_CLK_F2H_SDRAM_REF)                          // clock from the FPGA SDRAM
    {
        if ((freq >= alt_ext_clk_paramblok.sdram.freqmin) && (freq <= alt_ext_clk_paramblok.sdram.freqmax))
        {
            alt_ext_clk_paramblok.sdram.freqcur = freq;
            status = ALT_E_SUCCESS;
        }
        else
        {
            status = ALT_E_ARG_RANGE;
        }
    }
    else
    {
        status = ALT_E_BAD_ARG;
    }

    return status;
}


//
// alt_clk_ext_clk_freq_get returns the frequency of the external clock source as
// a measure of Hz. This value is stored in a static array.
//
alt_freq_t alt_clk_ext_clk_freq_get(ALT_CLK_t clk)
{
    uint32_t ret = 0;

    if ((clk == ALT_CLK_IN_PIN_OSC1) || (clk == ALT_CLK_OSC1))      // two names for one input
    {
        ret = alt_ext_clk_paramblok.clkosc1.freqcur;
    }
    else if (clk == ALT_CLK_IN_PIN_OSC2)
    {
        ret = alt_ext_clk_paramblok.clkosc2.freqcur;
    }
    else if (clk == ALT_CLK_F2H_PERIPH_REF)                         // clock from the FPGA
    {
        ret = alt_ext_clk_paramblok.periph.freqcur;
    }
    else if (clk == ALT_CLK_F2H_SDRAM_REF)                         // clock from the FPGA
    {
        ret = alt_ext_clk_paramblok.sdram.freqcur;
    }
    return ret;
}


//
// alt_clk_pll_cfg_get() returns the current PLL configuration.
//
ALT_STATUS_CODE alt_clk_pll_cfg_get(ALT_CLK_t pll, ALT_CLK_PLL_CFG_t * pll_cfg)
{
    ALT_STATUS_CODE        ret = ALT_E_ERROR;                  // return value
    uint32_t               temp;                               // temp variable

    if (pll_cfg == NULL)
    {
		ret = ALT_E_BAD_ARG;
		return ret;
    }

    if (pll == ALT_CLK_MAIN_PLL)
    {
        temp = alt_read_word(ALT_CLKMGR_MAINPLL_VCO_ADDR);
        pll_cfg->ref_clk = ALT_CLK_IN_PIN_OSC1;
        pll_cfg->mult = ALT_CLKMGR_MAINPLL_VCO_NUMER_GET(temp);
        pll_cfg->div = ALT_CLKMGR_MAINPLL_VCO_DENOM_GET(temp);

        // Get the C0-C5 divider values:
        pll_cfg->cntrs[0] = ALT_CLKMGR_MAINPLL_MPUCLK_CNT_GET(alt_read_word(ALT_CLKMGR_ALTERA_MPUCLK_ADDR));
        // C0 - mpu_clk

        pll_cfg->cntrs[1] = ALT_CLKMGR_MAINPLL_MAINCLK_CNT_GET(alt_read_word(ALT_CLKMGR_ALTERA_MAINCLK_ADDR));
        // C1 - main_clk

        pll_cfg->cntrs[2] = ALT_CLKMGR_MAINPLL_DBGATCLK_CNT_GET(alt_read_word(ALT_CLKMGR_MAINPLL_DBGATCLK_ADDR));
        // C2 - dbg_base_clk

        pll_cfg->cntrs[3] = ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT_GET(alt_read_word(ALT_CLKMGR_MAINPLL_MAINQSPICLK_ADDR));
        // C3 - main_qspi_clk

        pll_cfg->cntrs[4] = ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT_GET(alt_read_word(ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_ADDR));
        // C4 - main_nand_sdmmc_clk

        pll_cfg->cntrs[5] = ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT_GET(alt_read_word(ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_ADDR));
        // C5 - cfg_s2f_user0_clk aka cfg_h2f_user0_clk

        // The Main PLL C0-C5 outputs have no phase shift capabilities :
        pll_cfg->pshift[0] = pll_cfg->pshift[1] = pll_cfg->pshift[2] =
            pll_cfg->pshift[3] = pll_cfg->pshift[4] = pll_cfg->pshift[5] = 0;
        ret = ALT_E_SUCCESS;
    }
    else if (pll == ALT_CLK_PERIPHERAL_PLL)
    {
        temp = ALT_CLKMGR_PERPLL_VCO_PSRC_GET(alt_read_word(ALT_CLKMGR_PERPLL_VCO_ADDR));
        if (temp <= 2)
        {
            if (temp == ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC1)
            {
                pll_cfg->ref_clk = ALT_CLK_IN_PIN_OSC1;
            }
            else if (temp == ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC2)
            {
                pll_cfg->ref_clk = ALT_CLK_IN_PIN_OSC2;
            }
            else if (temp == ALT_CLKMGR_PERPLL_VCO_PSRC_E_F2S_PERIPH_REF)
            {
                pll_cfg->ref_clk = ALT_CLK_F2H_PERIPH_REF;
            }

            temp = alt_read_word(ALT_CLKMGR_PERPLL_VCO_ADDR);
            pll_cfg->mult = ALT_CLKMGR_PERPLL_VCO_NUMER_GET(temp);
            pll_cfg->div = ALT_CLKMGR_PERPLL_VCO_DENOM_GET(temp);

            // Get the C0-C5 divider values:
            pll_cfg->cntrs[0] = ALT_CLKMGR_PERPLL_EMAC0CLK_CNT_GET(alt_read_word(ALT_CLKMGR_PERPLL_EMAC0CLK_ADDR));
            // C0 - emac0_clk

            pll_cfg->cntrs[1] = ALT_CLKMGR_PERPLL_EMAC1CLK_CNT_GET(alt_read_word(ALT_CLKMGR_PERPLL_EMAC1CLK_ADDR));
            // C1 - emac1_clk

            pll_cfg->cntrs[2] = ALT_CLKMGR_PERPLL_PERQSPICLK_CNT_GET(alt_read_word(ALT_CLKMGR_PERPLL_PERQSPICLK_ADDR));
            // C2 - periph_qspi_clk

            pll_cfg->cntrs[3] = ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT_GET(alt_read_word(ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_ADDR));
            // C3 - periph_nand_sdmmc_clk

            pll_cfg->cntrs[4] = ALT_CLKMGR_PERPLL_PERBASECLK_CNT_GET(alt_read_word(ALT_CLKMGR_PERPLL_PERBASECLK_ADDR));
            // C4 - periph_base_clk

            pll_cfg->cntrs[5] = ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT_GET(alt_read_word(ALT_CLKMGR_PERPLL_S2FUSER1CLK_ADDR));
            // C5 - s2f_user1_clk

            // The Peripheral PLL C0-C5 outputs have no phase shift capabilities :
            pll_cfg->pshift[0] = pll_cfg->pshift[1] = pll_cfg->pshift[2] =
                pll_cfg->pshift[3] = pll_cfg->pshift[4] = pll_cfg->pshift[5] = 0;
            ret = ALT_E_SUCCESS;
        }
    }
    else if (pll == ALT_CLK_SDRAM_PLL)
    {
        temp = ALT_CLKMGR_SDRPLL_VCO_SSRC_GET(alt_read_word(ALT_CLKMGR_SDRPLL_VCO_ADDR));
        if (temp <= 2)
        {
            if (temp == ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC1)
            {
                pll_cfg->ref_clk = ALT_CLK_IN_PIN_OSC1;
            }
            else if (temp == ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC2)
            {
                pll_cfg->ref_clk = ALT_CLK_IN_PIN_OSC2;
            }
            else if (temp == ALT_CLKMGR_SDRPLL_VCO_SSRC_E_F2S_SDRAM_REF)
            {
                pll_cfg->ref_clk = ALT_CLK_F2H_SDRAM_REF;
            }

            pll_cfg->mult = ALT_CLKMGR_SDRPLL_VCO_NUMER_GET(alt_read_word(ALT_CLKMGR_SDRPLL_VCO_ADDR));
            pll_cfg->div = ALT_CLKMGR_SDRPLL_VCO_DENOM_GET(alt_read_word(ALT_CLKMGR_SDRPLL_VCO_ADDR));

            // Get the C0-C5 divider values:
            pll_cfg->cntrs[0]  = ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT_GET(alt_read_word(ALT_CLKMGR_SDRPLL_DDRDQSCLK_ADDR));
            pll_cfg->pshift[0] = ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE_GET(alt_read_word(ALT_CLKMGR_SDRPLL_DDRDQSCLK_ADDR));
            // C0  - ddr_dqs_clk

            pll_cfg->cntrs[1]  = ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT_GET(alt_read_word(ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_ADDR));
            pll_cfg->pshift[1] = ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE_GET(alt_read_word(ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_ADDR));
            // C1  - ddr_2x_dqs_clk

            pll_cfg->cntrs[2]  = ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT_GET(alt_read_word(ALT_CLKMGR_SDRPLL_DDRDQCLK_ADDR));
            pll_cfg->pshift[2] = ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE_GET(alt_read_word(ALT_CLKMGR_SDRPLL_DDRDQCLK_ADDR));
            // C2  - ddr_dq_clk

            pll_cfg->cntrs[3]  = pll_cfg->cntrs[4] = pll_cfg->pshift[3] = pll_cfg->pshift[4] = 0;
            // C3  & C4 outputs don't exist on the SDRAM PLL

            pll_cfg->cntrs[5]  = ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT_GET(alt_read_word(ALT_CLKMGR_SDRPLL_S2FUSER2CLK_ADDR));
            pll_cfg->pshift[5] = ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE_GET(alt_read_word(ALT_CLKMGR_SDRPLL_S2FUSER2CLK_ADDR));
            // C5  - s2f_user2_clk or h2f_user2_clk

            ret = ALT_E_SUCCESS;
        }
    }

    return ret;
}


//
// alt_clk_pll_cfg_set() sets the PLL configuration using the configuration parameters
// specified in pll_cfg.
//
ALT_STATUS_CODE alt_clk_pll_cfg_set(ALT_CLK_t pll, const ALT_CLK_PLL_CFG_t * pll_cfg)
{
    if (pll_cfg == NULL)
    {
		return ALT_E_BAD_ARG;
    }

    if (alt_clk_pll_is_bypassed(pll) != ALT_E_TRUE)         // safe to write the PLL registers?
    {
        return ALT_E_ERROR;
    }

    ALT_STATUS_CODE ret = ALT_E_ERROR;
    uint32_t        temp;

    if (pll == ALT_CLK_MAIN_PLL)
    {
        temp  = (ALT_CLKMGR_MAINPLL_VCO_NUMER_CLR_MSK & ALT_CLKMGR_MAINPLL_VCO_DENOM_CLR_MSK)
            & alt_read_word(ALT_CLKMGR_MAINPLL_VCO_ADDR);
        temp |= ALT_CLKMGR_MAINPLL_VCO_NUMER_SET(pll_cfg->mult) |
            ALT_CLKMGR_MAINPLL_VCO_DENOM_SET(pll_cfg->div);

        alt_write_word(ALT_CLKMGR_MAINPLL_VCO_ADDR, temp);
        alt_write_word(ALT_CLKMGR_ALTERA_MPUCLK_ADDR,           pll_cfg->cntrs[0]);
        alt_write_word(ALT_CLKMGR_ALTERA_MAINCLK_ADDR,          pll_cfg->cntrs[1]);
        alt_write_word(ALT_CLKMGR_MAINPLL_DBGATCLK_ADDR,         pll_cfg->cntrs[2]);
        alt_write_word(ALT_CLKMGR_MAINPLL_MAINQSPICLK_ADDR,      pll_cfg->cntrs[3]);
        alt_write_word(ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_ADDR, pll_cfg->cntrs[4]);
        alt_write_word(ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_ADDR,   pll_cfg->cntrs[5]);
        ret = ALT_E_SUCCESS;
    }
    else if (pll == ALT_CLK_PERIPHERAL_PLL)
    {
        temp =  ALT_CLKMGR_PERPLL_VCO_NUMER_CLR_MSK & ALT_CLKMGR_PERPLL_VCO_DENOM_CLR_MSK
            & ALT_CLKMGR_PERPLL_VCO_PSRC_CLR_MSK;
        temp &= alt_read_word(ALT_CLKMGR_PERPLL_VCO_ADDR);
        temp |= ALT_CLKMGR_PERPLL_VCO_NUMER_SET(pll_cfg->mult)
            | ALT_CLKMGR_PERPLL_VCO_DENOM_SET(pll_cfg->div);

        if ((pll_cfg->ref_clk == ALT_CLK_IN_PIN_OSC1) || (pll_cfg->ref_clk == ALT_CLK_OSC1))
        {
            temp |= ALT_CLKMGR_PERPLL_VCO_PSRC_SET(ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC1);
        }
        else if (pll_cfg->ref_clk == ALT_CLK_IN_PIN_OSC2)
        {
            temp |= ALT_CLKMGR_PERPLL_VCO_PSRC_SET(ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC2);
        }
        else if (pll_cfg->ref_clk == ALT_CLK_F2H_PERIPH_REF)
        {
            temp |= ALT_CLKMGR_PERPLL_VCO_PSRC_SET(ALT_CLKMGR_PERPLL_VCO_PSRC_E_F2S_PERIPH_REF);
        }
        else
        {
            return ret;
        }

        alt_write_word(ALT_CLKMGR_PERPLL_VCO_ADDR, temp);
        alt_write_word(ALT_CLKMGR_PERPLL_EMAC0CLK_ADDR,        pll_cfg->cntrs[0]);
        alt_write_word(ALT_CLKMGR_PERPLL_EMAC1CLK_ADDR,        pll_cfg->cntrs[1]);
        alt_write_word(ALT_CLKMGR_PERPLL_PERQSPICLK_ADDR,      pll_cfg->cntrs[2]);
        alt_write_word(ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_ADDR, pll_cfg->cntrs[3]);
        alt_write_word(ALT_CLKMGR_PERPLL_PERBASECLK_ADDR,      pll_cfg->cntrs[4]);
        alt_write_word(ALT_CLKMGR_PERPLL_S2FUSER1CLK_ADDR,     pll_cfg->cntrs[5]);
        ret = ALT_E_SUCCESS;
    }
    else if (pll == ALT_CLK_SDRAM_PLL)
    {
        // write the SDRAM PLL VCO Counter -----------------------------
        temp =  ALT_CLKMGR_SDRPLL_VCO_NUMER_CLR_MSK & ALT_CLKMGR_SDRPLL_VCO_DENOM_CLR_MSK
            & ALT_CLKMGR_SDRPLL_VCO_SSRC_CLR_MSK;           // make a mask
        temp &= alt_read_word(ALT_CLKMGR_SDRPLL_VCO_ADDR);
        temp |= ALT_CLKMGR_SDRPLL_VCO_NUMER_SET(pll_cfg->mult)
            | ALT_CLKMGR_SDRPLL_VCO_DENOM_SET(pll_cfg->div)
            | ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL_SET_MSK;
        // setting this bit aligns the output phase of the counters and prevents
        // glitches and too-short clock periods when restarting.
        // this bit is cleared at the end of this routine

        if ((pll_cfg->ref_clk == ALT_CLK_IN_PIN_OSC1) || (pll_cfg->ref_clk == ALT_CLK_OSC1))
        {
            temp |= ALT_CLKMGR_SDRPLL_VCO_SSRC_SET(ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC1);
        }
        else if (pll_cfg->ref_clk == ALT_CLK_IN_PIN_OSC2)
        {
            temp |= ALT_CLKMGR_SDRPLL_VCO_SSRC_SET(ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC2);
        }
        else if (pll_cfg->ref_clk == ALT_CLK_F2H_PERIPH_REF)
        {
            temp |= ALT_CLKMGR_SDRPLL_VCO_SSRC_SET(ALT_CLKMGR_SDRPLL_VCO_SSRC_E_F2S_SDRAM_REF);
        }
        else
        {
            return ret;
        }

        alt_write_word(ALT_CLKMGR_SDRPLL_VCO_ADDR, temp);

        // write the SDRAM PLL C0 Divide Counter -----------------------------
        temp =  ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT_SET(pll_cfg->cntrs[0])
            | ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE_SET(pll_cfg->pshift[0]);

        alt_clk_pllcounter_write(ALT_CLKMGR_SDRPLL_VCO_ADDR, ALT_CLKMGR_STAT_ADDR,
                                 ALT_CLKMGR_SDRPLL_DDRDQSCLK_ADDR, temp,
                                 ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT_SET_MSK | ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE_SET_MSK,
                                 ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT_LSB);

        // write the SDRAM PLL C1 Divide Counter -----------------------------
        if (ret == ALT_E_SUCCESS)
        {
            temp =  ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT_SET(pll_cfg->cntrs[1])
                | ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE_SET(pll_cfg->pshift[1]);
            alt_clk_pllcounter_write(ALT_CLKMGR_SDRPLL_VCO_ADDR, ALT_CLKMGR_STAT_ADDR,
                                     ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_ADDR, temp,
                                     ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT_SET_MSK | ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE_SET_MSK,
                                     ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT_LSB);
        }

        // write the SDRAM PLL C2 Divide Counter -----------------------------
        if (ret == ALT_E_SUCCESS)
        {
            temp =  ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT_SET(pll_cfg->cntrs[2])
                | ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE_SET(pll_cfg->pshift[2]);
            alt_clk_pllcounter_write(ALT_CLKMGR_SDRPLL_VCO_ADDR, ALT_CLKMGR_STAT_ADDR,
                                     ALT_CLKMGR_SDRPLL_DDRDQCLK_ADDR, temp,
                                     ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT_SET_MSK | ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE_SET_MSK,
                                     ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT_LSB);
        }

        // write the SDRAM PLL C5 Divide Counter -----------------------------
        if (ret == ALT_E_SUCCESS)
        {
            temp =  ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT_SET(pll_cfg->cntrs[2])
                | ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE_SET(pll_cfg->pshift[2]);
            alt_clk_pllcounter_write(ALT_CLKMGR_SDRPLL_VCO_ADDR, ALT_CLKMGR_STAT_ADDR,
                                     ALT_CLKMGR_SDRPLL_S2FUSER2CLK_ADDR, temp,
                                     ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT_SET_MSK | ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE_SET_MSK,
                                     ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT_LSB);
        }

        if (ret == ALT_E_SUCCESS)
        {
            alt_clrbits_word(ALT_CLKMGR_SDRPLL_VCO_ADDR, ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL_SET_MSK);
            // allow the phase multiplexer and output counter to leave reset
        }
    }

    return ret;
}


//
// alt_clk_pll_vco_cfg_get() returns the current PLL VCO frequency configuration.
//
ALT_STATUS_CODE alt_clk_pll_vco_cfg_get(ALT_CLK_t pll, uint32_t * mult, uint32_t * div)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    uint32_t        temp;

    if ( (mult == NULL) || (div == NULL) )
    {
		return ALT_E_BAD_ARG;
    }

    if (pll == ALT_CLK_MAIN_PLL)
    {
        temp = alt_read_word(ALT_CLKMGR_MAINPLL_VCO_ADDR);
        *mult = ALT_CLKMGR_MAINPLL_VCO_NUMER_GET(temp) + 1;
        *div  = ALT_CLKMGR_MAINPLL_VCO_DENOM_GET(temp) + 1;
    }
    else if (pll == ALT_CLK_PERIPHERAL_PLL)
    {
        temp = alt_read_word(ALT_CLKMGR_PERPLL_VCO_ADDR);
        *mult = ALT_CLKMGR_PERPLL_VCO_NUMER_GET(temp) + 1;
        *div  = ALT_CLKMGR_PERPLL_VCO_DENOM_GET(temp) + 1;
    }
    else if (pll == ALT_CLK_SDRAM_PLL)
    {
        temp = alt_read_word(ALT_CLKMGR_SDRPLL_VCO_ADDR);
        *mult = ALT_CLKMGR_SDRPLL_VCO_NUMER_GET(temp) + 1;
        *div  = ALT_CLKMGR_SDRPLL_VCO_DENOM_GET(temp) + 1;
    }
    else
    {
        status = ALT_E_ERROR;
    }

    return status;
}


/****************************************************************************************/
/* This enum enumerates a set of possible change methods that are available for use by  */
/* alt_clk_pll_vco_cfg_set() to change VCO parameter settings.                          */
/****************************************************************************************/

typedef enum ALT_CLK_PLL_VCO_CHG_METHOD_e
{
    ALT_VCO_CHG_NONE_VALID      = 0,            /*  No valid method to  change PLL
                                                 *  VCO was found                       */
    ALT_VCO_CHG_NOCHANGE        = 0x00000001,   /*  Proposed new VCO values are the
                                                 *  same as the old values              */
    ALT_VCO_CHG_NUM             = 0x00000002,   /*  Can change the VCO multiplier
                                                 *  alone                               */
    ALT_VCO_CHG_NUM_BYP         = 0x00000004,   /*  A VCO multiplier-only change will
                                                 *  require putting the PLL in bypass   */
    ALT_VCO_CHG_DENOM           = 0x00000008,   /*  Can change the VCO divider
                                                 *  alone                               */
    ALT_VCO_CHG_DENOM_BYP       = 0x00000010,   /*  A VCO divider-only change will
                                                 *  require putting the PLL in bypass   */
    ALT_VCO_CHG_NUM_DENOM       = 0x00000020,   /*  Can change the clock multiplier
                                                 *  first. then the clock divider       */
    ALT_VCO_CHG_NUM_DENOM_BYP   = 0x00000040,   /*  Changing the clock multiplier first.
                                                 *  then the clock divider will
                                                 *  require putting the PLL in bypass   */
    ALT_VCO_CHG_DENOM_NUM       = 0x00000080,   /*  Can change the clock divider first.
                                                 *  then the clock multiplier           */
    ALT_VCO_CHG_DENOM_NUM_BYP   = 0x00000100    /*  Changing the clock divider first.
                                                 *  then the clock multiplier will
                                                 *  require putting the PLL in bypass   */
} ALT_CLK_PLL_VCO_CHG_METHOD_t;



/****************************************************************************************/
/* alt_clk_pll_vco_chg_methods_get() determines which possible methods to change the    */
/* VCO are allowed within the limits set by the maximum PLL multiplier and divider      */
/* values and by the upper and lower frequency limits of the PLL, and also determines   */
/* whether each of these changes can be made without the PLL losing lock, which         */
/* requires the PLL to be bypassed before making changes, and removed from bypass state */
/* afterwards.                                                                          */
/****************************************************************************************/


#define ALT_CLK_PLL_VCO_CHG_METHOD_TEST_MODE        false
    // used for testing writes to the PLL VCOs



static ALT_CLK_PLL_VCO_CHG_METHOD_t alt_clk_pll_vco_chg_methods_get(ALT_CLK_t pll,
        uint32_t mult, uint32_t div )
{
#if ALT_CLK_PLL_VCO_CHG_METHOD_TEST_MODE

    // used for testing
    return ALT_VCO_CHG_NOCHANGE;

#else

    // check PLL max value limits
    if (   (mult == 0) || (mult > ALT_CLK_PLL_MULT_MAX)
        || (div  == 0) || (div  > ALT_CLK_PLL_DIV_MAX)
       )
    {
        return ALT_VCO_CHG_NONE_VALID;
    }

    ALT_CLK_PLL_VCO_CHG_METHOD_t    ret = ALT_VCO_CHG_NONE_VALID;
    uint32_t                        temp;
    uint32_t                        numer;
    uint32_t                        denom;
    uint32_t                        freqmax;
    uint32_t                        freqmin;
    uint32_t                        inputfreq;
    uint32_t                        guardband;
    bool                            numerchg = false;
    bool                            denomchg = false;
    bool                            within_gb;

    // gather data values according to PLL
    if (pll == ALT_CLK_MAIN_PLL)
    {
        temp = alt_read_word(ALT_CLKMGR_MAINPLL_VCO_ADDR);

        numer = ALT_CLKMGR_MAINPLL_VCO_NUMER_GET(temp);
        denom = ALT_CLKMGR_MAINPLL_VCO_DENOM_GET(temp);

        freqmax   = alt_pll_clk_paramblok.MainPLL_800.freqmax;
        freqmin   = alt_pll_clk_paramblok.MainPLL_800.freqmin;
        guardband = alt_pll_clk_paramblok.MainPLL_800.guardband;

        inputfreq = alt_ext_clk_paramblok.clkosc1.freqcur;
    }

    else if (pll == ALT_CLK_PERIPHERAL_PLL)
    {
        temp = alt_read_word(ALT_CLKMGR_PERPLL_VCO_ADDR);

        numer = ALT_CLKMGR_PERPLL_VCO_NUMER_GET(temp);
        denom = ALT_CLKMGR_PERPLL_VCO_DENOM_GET(temp);

        freqmax   = alt_pll_clk_paramblok.PeriphPLL_800.freqmax;
        freqmin   = alt_pll_clk_paramblok.PeriphPLL_800.freqmin;
        guardband = alt_pll_clk_paramblok.PeriphPLL_800.guardband;

        temp = ALT_CLKMGR_PERPLL_VCO_PSRC_GET(temp);
        if (temp == ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC1)
        {
            inputfreq = alt_ext_clk_paramblok.clkosc1.freqcur;
        }
        else if (temp == ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC2)
        {
            inputfreq = alt_ext_clk_paramblok.clkosc2.freqcur;
        }
        else if (temp == ALT_CLKMGR_PERPLL_VCO_PSRC_E_F2S_PERIPH_REF)
        {
            inputfreq = alt_ext_clk_paramblok.periph.freqcur;
        }
        else
        {
            return ret;
        }
    }

    else if (pll == ALT_CLK_SDRAM_PLL)
    {
        temp = alt_read_word(ALT_CLKMGR_SDRPLL_VCO_ADDR);

        numer = ALT_CLKMGR_SDRPLL_VCO_NUMER_GET(temp);
        denom = ALT_CLKMGR_SDRPLL_VCO_DENOM_GET(temp);

        freqmax   = alt_pll_clk_paramblok.SDRAMPLL_800.freqmax;
        freqmin   = alt_pll_clk_paramblok.SDRAMPLL_800.freqmin;
        guardband = alt_pll_clk_paramblok.SDRAMPLL_800.guardband;

        temp = ALT_CLKMGR_SDRPLL_VCO_SSRC_GET(temp);
        if (temp == ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC1)
        {
            inputfreq = alt_ext_clk_paramblok.clkosc1.freqcur;
        }
        else if (temp == ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC2)
        {
            inputfreq = alt_ext_clk_paramblok.clkosc2.freqcur;
        }
        else if (temp == ALT_CLKMGR_SDRPLL_VCO_SSRC_E_F2S_SDRAM_REF)
        {
            inputfreq = alt_ext_clk_paramblok.sdram.freqcur;
        }
        else
        {
            return ret;
        }
    }
    else
    {
        return ret;
    }

    temp = mult * (inputfreq / div);
    if ((temp <= freqmax) && (temp >= freqmin))     // are the final values within frequency limits?
    {
        numer++;
        denom++;
        numerchg = (mult != numer);
        denomchg = (div != denom);

        if (!numerchg && !denomchg)
        {
            ret = ALT_VCO_CHG_NOCHANGE;
        }
        else if (numerchg && !denomchg)
        {
            within_gb = alt_within_delta(numer, mult, guardband);
            // check if change is within the guardband limits
            temp = mult * (inputfreq / denom);
            if ((temp <= freqmax) && (temp >= freqmin))
            {
                ret = ALT_VCO_CHG_NUM;
                if (!within_gb) ret |= ALT_VCO_CHG_NUM_BYP;
            }
        }
        else if (!numerchg && denomchg)
        {
            within_gb = alt_within_delta(denom, div, guardband);
            temp = numer * (inputfreq / div);
            if ((temp <= freqmax) && (temp >= freqmin))
            {
                ret = ALT_VCO_CHG_DENOM;
                if (!within_gb)
                {
                    ret |= ALT_VCO_CHG_DENOM_BYP;
                }
            }
        }
        else    //numerchg && denomchg
        {
            within_gb = alt_within_delta(numer, mult, guardband);
            temp = mult * (inputfreq / denom);
            if ((temp <= freqmax) && (temp >= freqmin))
            {
                ret = ALT_VCO_CHG_NUM_DENOM;
                if (!within_gb)
                {
                    ret |= ALT_VCO_CHG_NUM_DENOM_BYP;
                }
            }
            within_gb = alt_within_delta(denom, div, guardband);
            temp = numer * (inputfreq / div);
            if ((temp <= freqmax) && (temp >= freqmin))
            {
                ret = ALT_VCO_CHG_DENOM_NUM;
                if (!within_gb)
                {
                    ret |= ALT_VCO_CHG_DENOM_NUM_BYP;
                }
            }
        }
    }

    return ret;
#endif
}


/****************************************************************************************/
/* alt_clk_pll_vco_cfg_set() sets the PLL VCO frequency configuration using the         */
/* supplied multiplier and divider arguments. alt_clk_pll_vco_chg_methods_get()         */
/* determines which methods are allowed by the limits set by the maximum multiplier     */
/* and divider values and by the upper and lower frequency limits of the PLL, and also  */
/* determines whether these changes can be made without requiring the PLL to be         */
/* bypassed. alt_clk_pll_vco_cfg_set() then carries out the actions required to effect  */
/* the method chosen to change the VCO settings.                                        */
/****************************************************************************************/

ALT_STATUS_CODE alt_clk_pll_vco_cfg_set(ALT_CLK_t pll, uint32_t mult, uint32_t div)
{
    ALT_STATUS_CODE                 ret = ALT_E_ERROR;
    ALT_CLK_PLL_VCO_CHG_METHOD_t    method;
    bool                            byp = false;
    void                            *vaddr;
    uint32_t                        numermask, denommask;
    uint32_t                        numershift, denomshift;


    method = alt_clk_pll_vco_chg_methods_get(pll, mult, div);

    if (method == ALT_VCO_CHG_NONE_VALID)
    {
        ret = ALT_E_BAD_CLK;
    }
    else if (method == ALT_VCO_CHG_NOCHANGE)
    {
        ret = ALT_E_INV_OPTION;
    }
    else
    {
        if (pll == ALT_CLK_MAIN_PLL)
        {
            vaddr = ALT_CLKMGR_MAINPLL_VCO_ADDR;
            numermask = ALT_CLKMGR_MAINPLL_VCO_NUMER_SET_MSK;
            denommask = ALT_CLKMGR_MAINPLL_VCO_DENOM_SET_MSK;
            numershift = ALT_CLKMGR_MAINPLL_VCO_NUMER_LSB;
            denomshift = ALT_CLKMGR_MAINPLL_VCO_DENOM_LSB;
        }
        else if (pll == ALT_CLK_PERIPHERAL_PLL)
        {
            vaddr = ALT_CLKMGR_PERPLL_VCO_ADDR;
            numermask = ALT_CLKMGR_PERPLL_VCO_NUMER_SET_MSK;
            denommask = ALT_CLKMGR_PERPLL_VCO_DENOM_SET_MSK;
            numershift = ALT_CLKMGR_PERPLL_VCO_NUMER_LSB;
            denomshift = ALT_CLKMGR_PERPLL_VCO_DENOM_LSB;
        }
        else if (pll == ALT_CLK_SDRAM_PLL)
        {
            vaddr = ALT_CLKMGR_SDRPLL_VCO_ADDR;
            numermask = ALT_CLKMGR_SDRPLL_VCO_NUMER_SET_MSK;
            denommask = ALT_CLKMGR_SDRPLL_VCO_DENOM_SET_MSK;
            numershift = ALT_CLKMGR_SDRPLL_VCO_NUMER_LSB;
            denomshift = ALT_CLKMGR_SDRPLL_VCO_DENOM_LSB;
        }
        else { return ALT_E_BAD_ARG; }

        mult--;
        div--;

        if (method & ALT_VCO_CHG_NUM)
        {
            if (method & ALT_VCO_CHG_NUM_BYP)
            {
                alt_clk_pll_bypass_enable(pll, 0);
                byp = true;
                alt_clk_mgr_wait(vaddr, ALT_SW_MANAGED_CLK_WAIT_BYPASS);
            }
            alt_replbits_word(vaddr, numermask, mult << numershift);
        }

        else if (method & ALT_VCO_CHG_DENOM)
        {
            if (method & ALT_VCO_CHG_DENOM_BYP)
            {
                alt_clk_pll_bypass_enable(pll, 0);
                byp = true;
            }
            alt_replbits_word(vaddr, denommask, div << denomshift);
        }

        else if (method & ALT_VCO_CHG_NUM_DENOM)
        {
            if (method & ALT_VCO_CHG_NUM_DENOM_BYP)
            {
                alt_clk_pll_bypass_enable(pll, 0);
                byp = true;
            }
            alt_replbits_word(vaddr, numermask, mult << numershift);
            if (!byp)       // if PLL is not bypassed
            {
                ret = alt_clk_pll_lock_wait(ALT_CLK_MAIN_PLL, 1000);
                      // verify PLL is still locked or wait for it to lock again
            }
            alt_replbits_word(vaddr, denommask, div << denomshift);
        }

        else if (method & ALT_VCO_CHG_DENOM_NUM)
        {
            if (method & ALT_VCO_CHG_DENOM_NUM_BYP)
            {
                alt_clk_pll_bypass_enable(pll, 0);
                byp = true;
            }
            alt_replbits_word(vaddr, numermask, mult << numershift);
            if (!byp)       // if PLL is not bypassed
            {
                ret = alt_clk_pll_lock_wait(ALT_CLK_MAIN_PLL, 1000);
                      // verify PLL is still locked or wait for it to lock again
            }
            alt_replbits_word(vaddr, denommask, div << denomshift);
        }

        ret = alt_clk_pll_lock_wait(ALT_CLK_MAIN_PLL, 1000);
              // verify PLL is still locked or wait for it to lock again
        if (byp)
        {
            alt_clk_pll_bypass_disable(pll);
            alt_clk_mgr_wait(vaddr, ALT_SW_MANAGED_CLK_WAIT_BYPASS);
                // wait for PLL to come out of bypass mode completely
        }
    }
    return ret;
}


//
// alt_clk_pll_vco_freq_get() gets the VCO frequency of the specified PLL.
// Note that since there is at present no known way for software to obtain the speed
// bin of the SoC or MPU that it is running on, the function below only deals with the
// 800 MHz part. This may need to be revised in the future.
//
ALT_STATUS_CODE alt_clk_pll_vco_freq_get(ALT_CLK_t pll, alt_freq_t * freq)
{
    uint64_t            temp1 = 0;
    uint32_t            temp;
    uint32_t            numer;
    uint32_t            denom;
    ALT_STATUS_CODE     ret = ALT_E_BAD_ARG;

    if (freq == NULL)
    {
		return ret;
    }

    if (pll == ALT_CLK_MAIN_PLL)
    {
        temp = alt_read_word(ALT_CLKMGR_MAINPLL_VCO_ADDR);
        numer = ALT_CLKMGR_MAINPLL_VCO_NUMER_GET(temp);
        denom = ALT_CLKMGR_MAINPLL_VCO_DENOM_GET(temp);
        temp1 = (uint64_t) alt_ext_clk_paramblok.clkosc1.freqcur;
        temp1 *= (numer + 1);
        temp1 /= (denom + 1);

        if (temp1 <= UINT32_MAX)
        {
            temp = (alt_freq_t) temp1;
            alt_pll_clk_paramblok.MainPLL_800.freqcur = temp;
            // store this value in the parameter block table
	     *freq = temp;
            // should NOT check value against PLL frequency limits
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ERROR;
        }
    }
    else if (pll == ALT_CLK_PERIPHERAL_PLL)
    {
        temp = alt_read_word(ALT_CLKMGR_PERPLL_VCO_ADDR);
        numer = ALT_CLKMGR_PERPLL_VCO_NUMER_GET(temp);
        denom = ALT_CLKMGR_PERPLL_VCO_DENOM_GET(temp);
        temp = ALT_CLKMGR_PERPLL_VCO_PSRC_GET(temp);
        if (temp == ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC1)
        {
            temp1 = (uint64_t) alt_ext_clk_paramblok.clkosc1.freqcur;
        }
        else if (temp == ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC2)
        {
            temp1 = (uint64_t) alt_ext_clk_paramblok.clkosc2.freqcur;
        }
        else if (temp == ALT_CLKMGR_PERPLL_VCO_PSRC_E_F2S_PERIPH_REF)
        {
            temp1 = (uint64_t) alt_ext_clk_paramblok.periph.freqcur;
        }

        if (temp1 != 0)
        {
            temp1 *= (numer + 1);
            temp1 /= (denom + 1);
            if (temp1 <= UINT32_MAX)
            {
                temp = (alt_freq_t) temp1;
                alt_pll_clk_paramblok.PeriphPLL_800.freqcur = temp;
                // store this value in the parameter block table

                *freq = temp;
                ret = ALT_E_SUCCESS;
            }
            else
            {
                ret = ALT_E_ERROR;
            }
        }       // this returns ALT_BAD_ARG if the source isn't known
    }
    else if (pll == ALT_CLK_SDRAM_PLL)
    {
        temp = alt_read_word(ALT_CLKMGR_SDRPLL_VCO_ADDR);
        numer = ALT_CLKMGR_SDRPLL_VCO_NUMER_GET(temp);
        denom = ALT_CLKMGR_SDRPLL_VCO_DENOM_GET(temp);
        temp = ALT_CLKMGR_SDRPLL_VCO_SSRC_GET(temp);
        if (temp == ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC1)
        {
            temp1 = (uint64_t) alt_ext_clk_paramblok.clkosc1.freqcur;
        }
        else if (temp == ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC2)
        {
            temp1 = (uint64_t) alt_ext_clk_paramblok.clkosc2.freqcur;
        }
        else if (temp == ALT_CLKMGR_SDRPLL_VCO_SSRC_E_F2S_SDRAM_REF)
        {
            temp1 = (uint64_t) alt_ext_clk_paramblok.sdram.freqcur;
        }

        if (temp1 != 0)
        {
            temp1 *= (numer + 1);
            temp1 /= (denom + 1);
            if (temp1 <= UINT32_MAX)
            {
                temp = (alt_freq_t) temp1;
                alt_pll_clk_paramblok.SDRAMPLL_800.freqcur = temp;
                // store this value in the parameter block table

                *freq = temp;
                ret = ALT_E_SUCCESS;
            }
            else
            {
                ret = ALT_E_ERROR;
            }
        }
    }       // which returns ALT_BAD_ARG if the source isn't known

    return ret;
}

//
// Returns the current guard band range in effect for the PLL.
//
uint32_t alt_clk_pll_guard_band_get(ALT_CLK_t pll)
{
    uint32_t ret = 0;

    if (pll == ALT_CLK_MAIN_PLL)
    {
        ret = alt_pll_clk_paramblok.MainPLL_800.guardband;
    }
    else if (pll == ALT_CLK_PERIPHERAL_PLL)
    {
        ret = alt_pll_clk_paramblok.PeriphPLL_800.guardband;
    }
    else if (pll == ALT_CLK_SDRAM_PLL)
    {
        ret = alt_pll_clk_paramblok.SDRAMPLL_800.guardband;
    }
    return ret;
}

//
// clk_mgr_pll_guard_band_set() changes the guard band from its current value to permit
// a more lenient or stringent policy to be in effect for the implementation of the
// functions configuring PLL VCO frequency.
//
ALT_STATUS_CODE alt_clk_pll_guard_band_set(ALT_CLK_t pll, uint32_t guard_band)
{
    if (   (guard_band > UINT12_MAX) || (guard_band <= 0)
        || (guard_band > ALT_GUARDBAND_LIMIT)
       )
    {
        return ALT_E_ARG_RANGE;
    }

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (pll == ALT_CLK_MAIN_PLL)
    {
        alt_pll_clk_paramblok.MainPLL_800.guardband = guard_band;
        //alt_pll_clk_paramblok.MainPLL_600.guardband = guard_band;
        // ??? Don't know how to check the MPU speed bin yet, so only 800 MHz struct is used
    }
    else if (pll == ALT_CLK_PERIPHERAL_PLL)
    {
        alt_pll_clk_paramblok.PeriphPLL_800.guardband = guard_band;
        //alt_pll_clk_paramblok.PeriphPLL_600.guardband = guard_band;
    }
    else if (pll == ALT_CLK_SDRAM_PLL)
    {
        alt_pll_clk_paramblok.SDRAMPLL_800.guardband = guard_band;
        //alt_pll_clk_paramblok.SDRAMPLL_600.guardband = guard_band;
    }
    else
    {
        status = ALT_E_ERROR;
    }

    return status;
}

//
// alt_clk_divider_get() gets configured divider value for the specified clock.
//
ALT_STATUS_CODE alt_clk_divider_get(ALT_CLK_t clk, uint32_t * div)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    uint32_t        temp;

    if (div == NULL)
    {
		return ALT_E_BAD_ARG;
    }

    switch (clk)
    {
        // Main PLL outputs
    case ALT_CLK_MAIN_PLL_C0:
    case ALT_CLK_MPU:
        *div = (ALT_CLKMGR_MAINPLL_MPUCLK_CNT_GET(alt_read_word(ALT_CLKMGR_MAINPLL_MPUCLK_ADDR)) + 1) *
               (ALT_CLKMGR_ALTERA_MPUCLK_CNT_GET(alt_read_word(ALT_CLKMGR_ALTERA_MPUCLK_ADDR)) + 1);
        break;

    case ALT_CLK_MAIN_PLL_C1:
    case ALT_CLK_L4_MAIN:
    case ALT_CLK_L3_MAIN:
        *div = (ALT_CLKMGR_MAINPLL_MAINCLK_CNT_GET(alt_read_word(ALT_CLKMGR_MAINPLL_MAINCLK_ADDR)) + 1) *
               (ALT_CLKMGR_ALTERA_MAINCLK_CNT_GET(alt_read_word(ALT_CLKMGR_ALTERA_MAINCLK_ADDR)) + 1);
        break;

    case ALT_CLK_MAIN_PLL_C2:
    case ALT_CLK_DBG_BASE:
    case ALT_CLK_DBG_TIMER:
        *div = (ALT_CLKMGR_MAINPLL_DBGATCLK_CNT_GET(alt_read_word(ALT_CLKMGR_MAINPLL_DBGATCLK_ADDR)) + 1) *
               (ALT_CLKMGR_ALTERA_DBGATCLK_CNT_GET(alt_read_word(ALT_CLKMGR_ALTERA_DBGATCLK_ADDR)) + 1);
        break;

    case ALT_CLK_MAIN_PLL_C3:
    case ALT_CLK_MAIN_QSPI:
        *div = (ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT_GET(alt_read_word(ALT_CLKMGR_MAINPLL_MAINQSPICLK_ADDR))) + 1;
        break;

    case ALT_CLK_MAIN_PLL_C4:
    case ALT_CLK_MAIN_NAND_SDMMC:
        *div = (ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT_GET(alt_read_word(ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_ADDR))) + 1;
        break;

    case ALT_CLK_MAIN_PLL_C5:
    case ALT_CLK_CFG:
    case ALT_CLK_H2F_USER0:
        *div = (ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT_GET(alt_read_word(ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_ADDR))) + 1;
        break;

        /////

        // Peripheral PLL outputs
    case ALT_CLK_PERIPHERAL_PLL_C0:
    case ALT_CLK_EMAC0:
        *div = (ALT_CLKMGR_PERPLL_EMAC0CLK_CNT_GET(alt_read_word(ALT_CLKMGR_PERPLL_EMAC0CLK_ADDR))) + 1;
        break;

    case ALT_CLK_PERIPHERAL_PLL_C1:
    case ALT_CLK_EMAC1:
        *div = (ALT_CLKMGR_PERPLL_EMAC1CLK_CNT_GET(alt_read_word(ALT_CLKMGR_PERPLL_EMAC1CLK_ADDR))) + 1;
        break;

    case ALT_CLK_PERIPHERAL_PLL_C2:
        *div = (ALT_CLKMGR_PERPLL_PERQSPICLK_CNT_GET(alt_read_word(ALT_CLKMGR_PERPLL_PERQSPICLK_ADDR))) + 1;
        break;

    case ALT_CLK_PERIPHERAL_PLL_C3:
        *div = (ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT_GET(alt_read_word(ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_ADDR))) + 1;
        break;

    case ALT_CLK_PERIPHERAL_PLL_C4:
        *div = (ALT_CLKMGR_PERPLL_PERBASECLK_CNT_GET(alt_read_word(ALT_CLKMGR_PERPLL_PERBASECLK_ADDR))) + 1;
        break;

    case ALT_CLK_PERIPHERAL_PLL_C5:
    case ALT_CLK_H2F_USER1:
        *div = (ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT_GET(alt_read_word(ALT_CLKMGR_PERPLL_S2FUSER1CLK_ADDR))) + 1;
        break;

        /////

        // SDRAM PLL outputs
    case ALT_CLK_SDRAM_PLL_C0:
    case ALT_CLK_DDR_DQS:
        *div = (ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT_GET(alt_read_word(ALT_CLKMGR_SDRPLL_DDRDQSCLK_ADDR))) + 1;
        break;

    case ALT_CLK_SDRAM_PLL_C1:
    case ALT_CLK_DDR_2X_DQS:
        *div = (ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT_GET(alt_read_word(ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_ADDR))) + 1;
        break;

    case ALT_CLK_SDRAM_PLL_C2:
    case ALT_CLK_DDR_DQ:
        *div = (ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT_GET(alt_read_word(ALT_CLKMGR_SDRPLL_DDRDQCLK_ADDR))) + 1;
        break;

    case ALT_CLK_SDRAM_PLL_C5:
    case ALT_CLK_H2F_USER2:
        *div = (ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT_GET(alt_read_word(ALT_CLKMGR_SDRPLL_S2FUSER2CLK_ADDR))) + 1;
        break;

        /////

        // Other clock dividers
    case ALT_CLK_L3_MP:
        temp = ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_GET(alt_read_word(ALT_CLKMGR_MAINPLL_MAINDIV_ADDR));
        if (temp <= ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_E_DIV2)
        {
            *div = temp + 1;
        }
        else
        {
            status = ALT_E_ERROR;
        }
        break;

    case ALT_CLK_L3_SP:
        temp = ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_GET(alt_read_word(ALT_CLKMGR_MAINPLL_MAINDIV_ADDR));
        if (temp <= ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_E_DIV2)
        {
            *div = temp + 1;
        }
        else
        {
            status = ALT_E_ERROR;
        }
        // note that this value does not include the additional effect
        // of the L3_MP divider that is upchain from this one
        break;

    case ALT_CLK_L4_MP:
        temp = ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_GET(alt_read_word(ALT_CLKMGR_MAINPLL_MAINDIV_ADDR));
        if (temp <= ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_DIV16)
        {
            *div = 1 << temp;
        }
        else
        {
            status = ALT_E_ERROR;
        }
        break;

    case ALT_CLK_L4_SP:
        temp = ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_GET(alt_read_word(ALT_CLKMGR_MAINPLL_MAINDIV_ADDR));
        if (temp <= ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_DIV16)
        {
            *div = 1 << temp;
        }
        else
        {
            status = ALT_E_ERROR;
        }
        break;

    case ALT_CLK_DBG_AT:
        temp = ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_GET(alt_read_word(ALT_CLKMGR_MAINPLL_DBGDIV_ADDR));
        if (temp <= ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_E_DIV4)
        {
            *div = 1 << temp;
        }
        else
        {
            status = ALT_E_ERROR;
        }
        break;

    case ALT_CLK_DBG:
        temp = ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_GET(alt_read_word(ALT_CLKMGR_MAINPLL_DBGDIV_ADDR));
        if (temp <= ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_E_DIV4)
        {
            *div =  1 << temp;
        }
        else
        {
            status = ALT_E_ERROR;
        }
        // note that this value does not include the value of the upstream dbg_at_clk divder
        break;

    case ALT_CLK_DBG_TRACE:
        temp = ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_GET(alt_read_word(ALT_CLKMGR_MAINPLL_TRACEDIV_ADDR));
        if (temp <= ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_DIV16)
        {
            *div =  1 << temp;
        }
        else
        {
            status = ALT_E_ERROR;
        }
        break;

    case ALT_CLK_USB_MP:
        temp = ALT_CLKMGR_PERPLL_DIV_USBCLK_GET(alt_read_word(ALT_CLKMGR_PERPLL_DIV_ADDR));
        if (temp <= ALT_CLKMGR_PERPLL_DIV_USBCLK_E_DIV16)
        {
            *div = 1 << temp;
        }
        else
        {
            status = ALT_E_ERROR;
        }
        break;

    case ALT_CLK_SPI_M:
        temp = ALT_CLKMGR_PERPLL_DIV_SPIMCLK_GET(alt_read_word(ALT_CLKMGR_PERPLL_DIV_ADDR));
        if (temp <= ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_DIV16)
        {
            *div = 1 << temp;
        }
        else
        {
            status = ALT_E_ERROR;
        }
        break;

    case ALT_CLK_CAN0:
        temp = ALT_CLKMGR_PERPLL_DIV_CAN0CLK_GET(alt_read_word(ALT_CLKMGR_PERPLL_DIV_ADDR));
        if (temp <= ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_DIV16)
        {
            *div = 1 << temp;
        }
        else
        {
            status = ALT_E_ERROR;
        }
        break;

    case ALT_CLK_CAN1:
        temp = ALT_CLKMGR_PERPLL_DIV_CAN1CLK_GET(alt_read_word(ALT_CLKMGR_PERPLL_DIV_ADDR));
        if (temp <= ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_DIV16)
        {
            *div = 1 << temp;
        }
        else
        {
            status = ALT_E_ERROR;
        }
        break;

    case ALT_CLK_GPIO_DB:
        temp = ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK_GET(alt_read_word(ALT_CLKMGR_PERPLL_GPIODIV_ADDR));
        *div = temp + 1;
        break;

    case ALT_CLK_MPU_PERIPH:
        *div = 4;                           // set by hardware
        break;

    case ALT_CLK_MPU_L2_RAM:
        *div = 2;                           // set by hardware
        break;

    case ALT_CLK_NAND:
        *div = 4;                           // set by hardware
        break;

    default:
        status = ALT_E_BAD_ARG;
        break;
    }

    return status;
}

/////

#define ALT_CLK_WITHIN_FREQ_LIMITS_TEST_MODE        false
    // used for testing writes to the the full range of counters without
    // regard to the usual output frequency upper and lower limits


static ALT_STATUS_CODE alt_clk_within_freq_limits(ALT_CLK_t clk, uint32_t div)
{
#if ALT_CLK_WITHIN_FREQ_LIMITS_TEST_MODE
    return ALT_E_TRUE;
#else

    if (div == 0)
    {
        return ALT_E_BAD_ARG;
    }

    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    uint32_t        numer = 0;
    uint32_t        hilimit;
    uint32_t        lolimit;

    switch (clk)
    {
        // Counters of the Main PLL
    case ALT_CLK_MAIN_PLL_C0:
        hilimit = alt_pll_cntr_maxfreq.MainPLL_C0;
        lolimit = alt_ext_clk_paramblok.clkosc1.freqcur;
        status = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &numer);
        break;
    case  ALT_CLK_MAIN_PLL_C1:
        hilimit = alt_pll_cntr_maxfreq.MainPLL_C1;
        lolimit = alt_ext_clk_paramblok.clkosc1.freqcur;
        status = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &numer);
        break;
    case ALT_CLK_MAIN_PLL_C2:
        hilimit = alt_pll_cntr_maxfreq.MainPLL_C2;
        lolimit = alt_ext_clk_paramblok.clkosc1.freqcur;
        status = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &numer);
        break;
    case ALT_CLK_MAIN_PLL_C3:
        hilimit = alt_pll_cntr_maxfreq.MainPLL_C3;
        lolimit = 0;
        status = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &numer);
        break;
    case ALT_CLK_MAIN_PLL_C4:
        hilimit = alt_pll_cntr_maxfreq.MainPLL_C4;
        lolimit = alt_ext_clk_paramblok.clkosc1.freqcur;
        status = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &numer);
        break;
    case ALT_CLK_MAIN_PLL_C5:
        hilimit = alt_pll_cntr_maxfreq.MainPLL_C5;
        lolimit = alt_ext_clk_paramblok.clkosc1.freqcur;
        status = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &numer);
        break;

    // Counters of the Peripheral PLL
    case ALT_CLK_PERIPHERAL_PLL_C0:
        hilimit = alt_pll_cntr_maxfreq.PeriphPLL_C0;
        lolimit = 0;
        status = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &numer);
        break;
    case ALT_CLK_PERIPHERAL_PLL_C1:
        hilimit = alt_pll_cntr_maxfreq.PeriphPLL_C1;
        lolimit = 0;
        status = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &numer);
        break;
    case ALT_CLK_PERIPHERAL_PLL_C2:
        hilimit = alt_pll_cntr_maxfreq.PeriphPLL_C2;
        lolimit = 0;
        status = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &numer);
        break;
    case ALT_CLK_PERIPHERAL_PLL_C3:
        hilimit = alt_pll_cntr_maxfreq.PeriphPLL_C3;
        lolimit = 0;
        status = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &numer);
        break;
    case ALT_CLK_PERIPHERAL_PLL_C4:
        hilimit = alt_pll_cntr_maxfreq.PeriphPLL_C4;
        lolimit = 0;
        status = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &numer);
        break;
    case ALT_CLK_PERIPHERAL_PLL_C5:
        hilimit = alt_pll_cntr_maxfreq.PeriphPLL_C5;
        lolimit = alt_ext_clk_paramblok.clkosc1.freqcur;
        status = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &numer);
        break;

    // Counters of the SDRAM PLL
    case ALT_CLK_SDRAM_PLL_C0:
        hilimit = alt_pll_cntr_maxfreq.SDRAMPLL_C0;
        lolimit = 0;
        status = alt_clk_pll_vco_freq_get(ALT_CLK_SDRAM_PLL, &numer);
        break;
    case ALT_CLK_SDRAM_PLL_C1:
        hilimit = alt_pll_cntr_maxfreq.SDRAMPLL_C1;
        lolimit = 0;
        status = alt_clk_pll_vco_freq_get(ALT_CLK_SDRAM_PLL, &numer);
        break;
    case ALT_CLK_SDRAM_PLL_C2:
        hilimit = alt_pll_cntr_maxfreq.SDRAMPLL_C2;
        lolimit = 0;
        status = alt_clk_pll_vco_freq_get(ALT_CLK_SDRAM_PLL, &numer);
        break;
    case ALT_CLK_SDRAM_PLL_C5:
        hilimit = alt_pll_cntr_maxfreq.SDRAMPLL_C5;
        lolimit = alt_ext_clk_paramblok.clkosc1.freqcur;
        status = alt_clk_pll_vco_freq_get(ALT_CLK_SDRAM_PLL, &numer);
        break;

    default:
        status = ALT_E_BAD_ARG;
        break;
    }

    if (status == ALT_E_SUCCESS)
    {
        numer = numer / div;
        if ((numer <= hilimit) && (numer >= lolimit))
        {
            status = ALT_E_TRUE;
        }
        else
        {
            status = ALT_E_FALSE;
        }
    }

    return status;
#endif
}

static bool alt_clkmgr_is_val_modulo_n(uint32_t div, uint32_t mod)
{
    if (mod == 1)
    {
        return true;
    }
    else if (mod == 2)
    {
        return (div & 0x1) == 0;
    }
    else if (mod == 4)
    {
        return (div & 0x3) == 0;
    }
    else
    {
        return (div % mod) == 0;
    }
}

//
// alt_clk_divider_set() sets the divider value for the specified clock.
//
// See pages 38, 44, 45, and 46 of the HPS-Clocking NPP for a map of the
// HPS clocking architecture and hierarchy of connections.
//
ALT_STATUS_CODE alt_clk_divider_set(ALT_CLK_t clk, uint32_t div)
{
    ALT_STATUS_CODE     ret = ALT_E_BAD_ARG;
    volatile uint32_t   temp, temp1;
    uint32_t            wrval = UINT32_MAX;              // value to be written
    bool                restore_0 = false;
    bool                restore_1 = false;
    bool                restore_2 = false;

    switch (clk)
    {
        // Main PLL outputs
    case ALT_CLK_MAIN_PLL_C0:
    case ALT_CLK_MPU:
        {
            uint32_t prediv = (ALT_CLKMGR_ALTERA_MPUCLK_CNT_GET(alt_read_word(ALT_CLKMGR_ALTERA_MPUCLK_ADDR)) + 1);

            if (   (div <= ((ALT_CLKMGR_MAINPLL_MPUCLK_CNT_SET_MSK + 1) * prediv))
                && alt_clkmgr_is_val_modulo_n(div, prediv)
                && (alt_clk_within_freq_limits(ALT_CLK_MAIN_PLL_C0, div) == ALT_E_TRUE) )
            {
                wrval = (div / prediv) - 1;

                // HW managed clock, change by writing to the external counter,  no need to gate clock
                // or match phase or wait for transistion time. No other field in the register to mask off either.
                alt_write_word(ALT_CLKMGR_MAINPLL_MPUCLK_ADDR, wrval);
                ret = ALT_E_SUCCESS;
            }
            else
            {
                ret = ALT_E_ARG_RANGE;
            }
        }
        break;

    case ALT_CLK_MAIN_PLL_C1:
    case ALT_CLK_L3_MAIN:
        {
            uint32_t prediv = (ALT_CLKMGR_ALTERA_MAINCLK_CNT_GET(alt_read_word(ALT_CLKMGR_ALTERA_MAINCLK_ADDR)) + 1);

            if (   (div <= ((ALT_CLKMGR_MAINPLL_MAINCLK_CNT_SET_MSK + 1) * prediv))
                && alt_clkmgr_is_val_modulo_n(div, prediv)
                && (alt_clk_within_freq_limits(ALT_CLK_MAIN_PLL_C1, div) == ALT_E_TRUE) )
            {
                // HW managed clock, change by writing to the external counter, no need to gate clock
                // or match phase or wait for transistion time. No other field in the register to mask off either.

                wrval = (div / prediv) - 1;

#if ALT_PREVENT_GLITCH_CHGC1
                // if L4MP or L4SP source is set to Main PLL C1, gate it off before changing
                // bypass state, then gate clock back on. FogBugz #63778
                temp  = alt_read_word(ALT_CLKMGR_MAINPLL_L4SRC_ADDR);
                temp1 = alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR);

                if ((temp1 & ALT_CLKMGR_MAINPLL_EN_L4MPCLK_SET_MSK) && (!(temp & ALT_CLKMGR_MAINPLL_L4SRC_L4MP_SET_MSK)))
                {
                    restore_0 = true;
                }
                if ((temp1 & ALT_CLKMGR_MAINPLL_EN_L4SPCLK_SET_MSK) && (!(temp & ALT_CLKMGR_MAINPLL_L4SRC_L4SP_SET_MSK)))
                {
                    restore_1 = true;
                }
                temp = temp1;
                if (restore_0) { temp &= ALT_CLKMGR_MAINPLL_EN_L4MPCLK_CLR_MSK; }
                if (restore_1) { temp &= ALT_CLKMGR_MAINPLL_EN_L4SPCLK_CLR_MSK; }
                if (restore_0 || restore_1) { alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp); }

                alt_write_word(ALT_CLKMGR_MAINPLL_MAINCLK_ADDR, wrval);

                alt_clk_mgr_wait(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
                // wait a bit before reenabling the L4MP and L4SP clocks
                if (restore_0 || restore_1) { alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp1); }
#else
                alt_write_word(ALT_CLKMGR_MAINPLL_MAINCLK_ADDR, wrval);
#endif
                ret = ALT_E_SUCCESS;
            }
            else
            {
                ret = ALT_E_ARG_RANGE;
            }
        }
        break;

    case ALT_CLK_MAIN_PLL_C2:
    case ALT_CLK_DBG_BASE:
        {
            uint32_t prediv = (ALT_CLKMGR_ALTERA_DBGATCLK_CNT_GET(alt_read_word(ALT_CLKMGR_ALTERA_DBGATCLK_ADDR)) + 1);

            if (   (div <= ((ALT_CLKMGR_MAINPLL_DBGATCLK_CNT_SET_MSK + 1) * prediv))
                   && alt_clkmgr_is_val_modulo_n(div, prediv)
                && (alt_clk_within_freq_limits(ALT_CLK_MAIN_PLL_C2, div) == ALT_E_TRUE) )
            {
                wrval = (div / prediv) - 1;
                // HW managed clock, change by writing to the external counter,  no need to gate clock
                // or match phase or wait for transistion time. No other field in the register to mask off either.
                alt_write_word(ALT_CLKMGR_MAINPLL_DBGATCLK_ADDR, wrval);

                ret = ALT_E_SUCCESS;
            }
            else
            {
                ret = ALT_E_ARG_RANGE;
            }
        }
        break;

    case ALT_CLK_MAIN_PLL_C3:
        // The rest of the PLL outputs do not have external counters, but
        // their internal counters are programmable rather than fixed
        if (   (div <= (ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT_SET_MSK + 1))
            && (alt_clk_within_freq_limits(ALT_CLK_MAIN_PLL_C3, div) == ALT_E_TRUE) )
        {
            // if the main_qspi_clk input is selected for the qspi_clk
            if (ALT_CLKMGR_PERPLL_SRC_QSPI_GET(alt_read_word(ALT_CLKMGR_PERPLL_SRC_ADDR)) ==
                ALT_CLKMGR_PERPLL_SRC_QSPI_E_MAIN_QSPI_CLK)
            {
                restore_0 = (temp = alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR)) & ALT_CLKMGR_PERPLL_EN_QSPICLK_SET_MSK;
                if (restore_0)             // AND if the QSPI clock is currently enabled
                {
                    alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp & ALT_CLKMGR_PERPLL_EN_QSPICLK_CLR_MSK);
                    // gate off the QSPI clock
                }

                wrval = div - 1;
                // the rest are software-managed clocks and require a reset sequence to write to
                alt_clk_pllcounter_write(ALT_CLKMGR_MAINPLL_VCO_ADDR,
                                         ALT_CLKMGR_MAINPLL_STAT_ADDR,
                                         ALT_CLKMGR_MAINPLL_MAINQSPICLK_ADDR,
                                         wrval,
                                         ALT_CLK_PLL_RST_BIT_C3,
                                         ALT_CLKMGR_MAINPLL_VCO_OUTRST_LSB);

                alt_clk_mgr_wait(ALT_CLKMGR_MAINPLL_MAINQSPICLK_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
                if (restore_0)
                {
                    alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp);
                    // if the QSPI clock was gated on (enabled) before, return it to that state
                }
                ret = ALT_E_SUCCESS;
            }
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_MAIN_PLL_C4:
    case ALT_CLK_MAIN_NAND_SDMMC:
        if (   (div <= (ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT_SET_MSK + 1))
            && (alt_clk_within_freq_limits(ALT_CLK_MAIN_PLL_C4, div) == ALT_E_TRUE) )
        {
            temp  = alt_read_word(ALT_CLKMGR_PERPLL_SRC_ADDR);
            temp1 = alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR);

            // do we need to gate off the SDMMC clock ?
            if (ALT_CLKMGR_PERPLL_SRC_SDMMC_GET(temp) == ALT_CLKMGR_PERPLL_SRC_SDMMC_E_MAIN_NAND_CLK)
            {
                if (temp1 & ALT_CLKMGR_PERPLL_EN_SDMMCCLK_SET_MSK) { restore_0 = true; }
            }

            // do we need to gate off the NAND clock and/or the NANDX clock?
            if (ALT_CLKMGR_PERPLL_SRC_NAND_GET(temp) == ALT_CLKMGR_PERPLL_SRC_NAND_E_MAIN_NAND_CLK)
            {
                if (temp1 & ALT_CLKMGR_PERPLL_EN_NANDXCLK_SET_MSK) { restore_1 = true; }
                if (temp1 & ALT_CLKMGR_PERPLL_EN_NANDCLK_SET_MSK)  { restore_2 = true; }
            }

            temp = temp1;
            if (restore_1 && restore_2)
            {
                temp &= ALT_CLKMGR_PERPLL_EN_NANDCLK_CLR_MSK;
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp);
                alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_SW_MANAGED_CLK_WAIT_NANDCLK);
                // gate nand_clk off at least 8 MPU clock cycles before before nand_x_clk
            }

            if (restore_0 || restore_1)
            {
                if (restore_0) { temp &= ALT_CLKMGR_PERPLL_EN_SDMMCCLK_CLR_MSK; }
                if (restore_1) { temp &= ALT_CLKMGR_PERPLL_EN_NANDXCLK_CLR_MSK; }
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp);
                // gate off sdmmc_clk and/or nand_x_clk
            }

            // now write the new divisor ratio
            wrval = div - 1;
            alt_clk_pllcounter_write(ALT_CLKMGR_MAINPLL_VCO_ADDR,
                                     ALT_CLKMGR_MAINPLL_STAT_ADDR,
                                     ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_ADDR,
                                     wrval,
                                     ALT_CLK_PLL_RST_BIT_C4,
                                     ALT_CLKMGR_MAINPLL_VCO_OUTRST_LSB);
            alt_clk_mgr_wait(ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);

            if (restore_0 || restore_1)
            {
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp1 & ALT_CLKMGR_PERPLL_EN_NANDCLK_CLR_MSK);
                // if the NANDX and/or SDMMC clock was gated on (enabled) before, return it to that state
                if (restore_1 && restore_2)
                {
                    // wait at least 8 clock cycles to turn the nand_clk on
                    alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_SW_MANAGED_CLK_WAIT_NANDCLK);
                    alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp1);
                }
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_MAIN_PLL_C5:
    case ALT_CLK_CFG:
    case ALT_CLK_H2F_USER0:
        if (   (div <= (ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT_SET_MSK + 1))
            && (alt_clk_within_freq_limits(ALT_CLK_MAIN_PLL_C5, div) == ALT_E_TRUE) )
        {
            temp = alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR);
            restore_0 = ((temp & ALT_CLKMGR_MAINPLL_EN_CFGCLK_SET_MSK) ||
                         (temp & ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK_SET_MSK));
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp & (ALT_CLKMGR_MAINPLL_EN_CFGCLK_CLR_MSK &
                                                                   ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK_CLR_MSK)); // clear both
            }

            // now write the new divisor ratio
            wrval = div - 1;
            alt_clk_pllcounter_write(ALT_CLKMGR_MAINPLL_VCO_ADDR,
                                     ALT_CLKMGR_MAINPLL_STAT_ADDR,
                                     ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_ADDR,
                                     wrval,
                                     ALT_CLK_PLL_RST_BIT_C5,
                                     ALT_CLKMGR_MAINPLL_VCO_OUTRST_LSB);

            alt_clk_mgr_wait(ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);

            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp);
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

        /////

        // Peripheral PLL outputs
    case ALT_CLK_PERIPHERAL_PLL_C0:
    case ALT_CLK_EMAC0:
        if (   (div <= (ALT_CLKMGR_PERPLL_EMAC0CLK_CNT_SET_MSK + 1))
            && (alt_clk_within_freq_limits(ALT_CLK_PERIPHERAL_PLL_C0, div) == ALT_E_TRUE) )
        {
            temp = alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR);
            restore_0 = temp & ALT_CLKMGR_PERPLL_EN_EMAC0CLK_SET_MSK;

            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp & ALT_CLKMGR_PERPLL_EN_EMAC0CLK_CLR_MSK);
            }

            // now write the new divisor ratio
            wrval = div - 1;
            alt_clk_pllcounter_write(ALT_CLKMGR_PERPLL_VCO_ADDR,
                                     ALT_CLKMGR_PERPLL_STAT_ADDR,
                                     ALT_CLKMGR_PERPLL_EMAC0CLK_ADDR,
                                     wrval,
                                     ALT_CLK_PLL_RST_BIT_C0,
                                     ALT_CLKMGR_PERPLL_VCO_OUTRST_LSB);

            alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_EMAC0CLK_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp);
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_PERIPHERAL_PLL_C1:
    case ALT_CLK_EMAC1:
        if (   (div <= (ALT_CLKMGR_PERPLL_EMAC1CLK_CNT_SET_MSK + 1))
            && (alt_clk_within_freq_limits(ALT_CLK_PERIPHERAL_PLL_C1, div) == ALT_E_TRUE) )
        {
            temp = alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR);
            restore_0 = temp & ALT_CLKMGR_PERPLL_EN_EMAC1CLK_SET_MSK;

            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp & ALT_CLKMGR_PERPLL_EN_EMAC1CLK_CLR_MSK);
            }
            // now write the new divisor ratio
            wrval = div - 1;
            alt_clk_pllcounter_write(ALT_CLKMGR_PERPLL_VCO_ADDR,
                                     ALT_CLKMGR_PERPLL_STAT_ADDR,
                                     ALT_CLKMGR_PERPLL_EMAC1CLK_ADDR,
                                     wrval,
                                     ALT_CLK_PLL_RST_BIT_C1,
                                     ALT_CLKMGR_PERPLL_VCO_OUTRST_LSB);

            alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_EMAC1CLK_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp);
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_PERIPHERAL_PLL_C2:
        if (   (div <= (ALT_CLKMGR_PERPLL_PERQSPICLK_CNT_SET_MSK + 1))
            && (alt_clk_within_freq_limits(ALT_CLK_PERIPHERAL_PLL_C2, div) == ALT_E_TRUE) )
        {
            temp = ALT_CLKMGR_PERPLL_SRC_QSPI_GET(alt_read_word(ALT_CLKMGR_PERPLL_SRC_ADDR));
            if (temp == ALT_CLKMGR_PERPLL_SRC_QSPI_E_PERIPH_QSPI_CLK)
            {
                // if qspi source is set to Peripheral PLL C2
                temp = alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR);
                // and if qspi_clk is enabled
                restore_0 = temp & ALT_CLKMGR_PERPLL_EN_QSPICLK_SET_MSK;
                if (restore_0)
                {
                    alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp & ALT_CLKMGR_PERPLL_EN_QSPICLK_CLR_MSK);
                    // gate it off
                }
            }

            // now write the new divisor ratio
            wrval = div - 1;
            alt_clk_pllcounter_write(ALT_CLKMGR_PERPLL_VCO_ADDR,
                                     ALT_CLKMGR_PERPLL_STAT_ADDR,
                                     ALT_CLKMGR_PERPLL_PERQSPICLK_ADDR,
                                     wrval,
                                     ALT_CLK_PLL_RST_BIT_C2,
                                     ALT_CLKMGR_PERPLL_VCO_OUTRST_LSB);

            alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_PERQSPICLK_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp);
                // if the clock was gated on (enabled) before, return it to that state
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_PERIPHERAL_PLL_C3:
        if (   (div <= (ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT_SET_MSK + 1))
            && (alt_clk_within_freq_limits(ALT_CLK_PERIPHERAL_PLL_C3, div) == ALT_E_TRUE) )
        {
            // first, are the clock MUX input selections currently set to use the clock we want to change?
            temp = alt_read_word(ALT_CLKMGR_PERPLL_SRC_ADDR);
            restore_0 = (ALT_CLKMGR_PERPLL_SRC_SDMMC_GET(temp) == ALT_CLKMGR_PERPLL_SRC_SDMMC_E_PERIPH_NAND_CLK);
            restore_1 = restore_2 = (ALT_CLKMGR_PERPLL_SRC_NAND_GET(temp) == ALT_CLKMGR_PERPLL_SRC_NAND_E_PERIPH_NAND_CLK);

            // now AND those with the current state of the three gate enables
            // to get the clocks which must be gated off and then back on
            temp1 = temp = alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR);
            restore_0 = restore_0 && (temp & ALT_CLKMGR_PERPLL_EN_SDMMCCLK_SET_MSK);
            restore_1 = restore_1 && (temp & ALT_CLKMGR_PERPLL_EN_NANDXCLK_SET_MSK);
            restore_2 = restore_2 && (temp & ALT_CLKMGR_PERPLL_EN_NANDCLK_SET_MSK);

            // gate off the clocks that depend on the clock divider that we want to change
            if (restore_2) { temp &= ALT_CLKMGR_PERPLL_EN_NANDCLK_CLR_MSK; }
            if (restore_0) { temp &= ALT_CLKMGR_PERPLL_EN_SDMMCCLK_CLR_MSK; }
            alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp);

            // the NAND clock must be gated off before the NANDX clock,
            if (restore_1)
            {
                alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_ADDR, ALT_SW_MANAGED_CLK_WAIT_NANDCLK);
                temp &= ALT_CLKMGR_PERPLL_EN_NANDXCLK_CLR_MSK;
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp);
            }

            // now write the new divisor ratio
            wrval = div - 1;
            alt_clk_pllcounter_write(ALT_CLKMGR_PERPLL_VCO_ADDR,
                                     ALT_CLKMGR_PERPLL_STAT_ADDR,
                                     ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_ADDR,
                                     wrval,
                                     ALT_CLK_PLL_RST_BIT_C3,
                                     ALT_CLKMGR_PERPLL_VCO_OUTRST_LSB);

            alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV );

            // NAND clock and NAND_X clock cannot be written together, must be a set sequence with a delay
            alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp1 & ALT_CLKMGR_PERPLL_EN_NANDCLK_CLR_MSK);
            if (restore_2)
            {
                // the NANDX clock must be gated on before the NAND clock.
                alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_ADDR, ALT_SW_MANAGED_CLK_WAIT_NANDCLK );
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp1);
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_PERIPHERAL_PLL_C4:
        if (   (div <= (ALT_CLKMGR_PERPLL_PERBASECLK_CNT_SET_MSK + 1))
            && (alt_clk_within_freq_limits(ALT_CLK_PERIPHERAL_PLL_C4, div) == ALT_E_TRUE) )
        {
            // look at the L4 set of clock gates first
            temp1 = alt_read_word(ALT_CLKMGR_MAINPLL_L4SRC_ADDR);
            restore_0 = (ALT_CLKMGR_MAINPLL_L4SRC_L4MP_GET(temp1) == ALT_CLKMGR_MAINPLL_L4SRC_L4MP_E_PERIPHPLL);
            restore_1 = (ALT_CLKMGR_MAINPLL_L4SRC_L4SP_GET(temp1) == ALT_CLKMGR_MAINPLL_L4SRC_L4SP_E_PERIPHPLL);
            temp1 = alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR);
            restore_0 = restore_0 && (temp1 & ALT_CLKMGR_MAINPLL_EN_L4MPCLK_SET_MSK);
            restore_1 = restore_1 && (temp1 & ALT_CLKMGR_MAINPLL_EN_L4SPCLK_SET_MSK);

            // if the l4_sp and l4_mp clocks are not set to use the periph_base_clk
            // from the Peripheral PLL C4 clock divider output, or if they are
            // not currently gated on, don't change their gates
            temp = alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR);
            if (restore_0) { temp &= ALT_CLKMGR_MAINPLL_EN_L4MPCLK_CLR_MSK; }
            if (restore_1) { temp &= ALT_CLKMGR_MAINPLL_EN_L4SPCLK_CLR_MSK; }
            alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp);

            // now look at the C4 direct set of clock gates
            // first, create a mask of the C4 direct set of clock gate enables
            temp = (  ALT_CLKMGR_PERPLL_EN_USBCLK_SET_MSK
                    | ALT_CLKMGR_PERPLL_EN_SPIMCLK_SET_MSK
                    | ALT_CLKMGR_PERPLL_EN_CAN0CLK_SET_MSK
                    | ALT_CLKMGR_PERPLL_EN_CAN1CLK_SET_MSK
                    | ALT_CLKMGR_PERPLL_EN_GPIOCLK_SET_MSK );

            // gate off all the C4 Direct set of clocks
            alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp1 & ~temp);

            // change the clock divider ratio - the reason we're here
            wrval = div - 1;
            alt_clk_pllcounter_write(ALT_CLKMGR_PERPLL_VCO_ADDR,
                                     ALT_CLKMGR_PERPLL_STAT_ADDR,
                                     ALT_CLKMGR_PERPLL_PERBASECLK_ADDR,
                                     wrval,
                                     ALT_CLK_PLL_RST_BIT_C4,
                                     ALT_CLKMGR_PERPLL_VCO_OUTRST_LSB);

            alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_PERBASECLK_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV );

            // gate the affected clocks that were on before back on - both sets of gates
            temp = (restore_0) ? ALT_CLKMGR_MAINPLL_EN_L4MPCLK_SET_MSK : 0;
            if (restore_1) { temp |= ALT_CLKMGR_MAINPLL_EN_L4SPCLK_SET_MSK; }
            alt_setbits_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp);
            alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp1);
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_PERIPHERAL_PLL_C5:
    case ALT_CLK_H2F_USER1:
        if (   (div <= (ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT_SET_MSK + 1))
            && (alt_clk_within_freq_limits(ALT_CLK_PERIPHERAL_PLL_C5, div) == ALT_E_TRUE) )
        {
            temp = alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR);
            restore_0 = temp & ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK_SET_MSK;
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp & ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK_CLR_MSK);
            }

            // now write the new divisor ratio
            wrval = div - 1;
            alt_clk_pllcounter_write(ALT_CLKMGR_PERPLL_VCO_ADDR,
                                     ALT_CLKMGR_PERPLL_STAT_ADDR,
                                     ALT_CLKMGR_PERPLL_S2FUSER1CLK_ADDR,
                                     wrval,
                                     ALT_CLK_PLL_RST_BIT_C5,
                                     ALT_CLKMGR_PERPLL_VCO_OUTRST_LSB);

            alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV );
            if (restore_0) { alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp); }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

        /////

        // SDRAM PLL outputs
    case ALT_CLK_SDRAM_PLL_C0:
    case ALT_CLK_DDR_DQS:
        if (   (div <= (ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT_SET_MSK + 1))
            && (alt_clk_within_freq_limits(ALT_CLK_SDRAM_PLL_C0, div) == ALT_E_TRUE) )
        {
            wrval = div - 1;
            temp = alt_read_word(ALT_CLKMGR_SDRPLL_EN_ADDR);
            if (temp & ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK_SET_MSK)
            {
                // if clock is currently on, gate it off
                alt_write_word(ALT_CLKMGR_SDRPLL_EN_ADDR, temp & ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK_CLR_MSK);
                restore_0 = true;
            }

            alt_clk_pllcounter_write(ALT_CLKMGR_SDRPLL_VCO_ADDR,
                                     ALT_CLKMGR_SDRPLL_STAT_ADDR,
                                     ALT_CLKMGR_SDRPLL_DDRDQSCLK_ADDR,
                                     wrval,
                                     ALT_CLK_PLL_RST_BIT_C0,
                                     ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT_LSB);
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_SDRPLL_EN_ADDR, temp);         // which has the enable bit set
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_SDRAM_PLL_C1:
    case ALT_CLK_DDR_2X_DQS:
        if (   (div <= (ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT_SET_MSK + 1))
            && (alt_clk_within_freq_limits(ALT_CLK_SDRAM_PLL_C1, div) == ALT_E_TRUE) )
        {
            wrval = div - 1;
            temp = alt_read_word(ALT_CLKMGR_SDRPLL_EN_ADDR);
            if (temp & ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK_SET_MSK)
            {
                // if clock is currently on, gate it off
                alt_write_word(ALT_CLKMGR_SDRPLL_EN_ADDR, temp & ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK_CLR_MSK);
                restore_0 = true;
            }

            alt_clk_pllcounter_write(ALT_CLKMGR_SDRPLL_VCO_ADDR,
                                     ALT_CLKMGR_SDRPLL_STAT_ADDR,
                                     ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_ADDR,
                                     wrval,
                                     ALT_CLK_PLL_RST_BIT_C1,
                                     ALT_CLKMGR_SDRPLL_VCO_OUTRST_LSB);
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_SDRPLL_EN_ADDR, temp);         // which has the enable bit set
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_SDRAM_PLL_C2:
    case ALT_CLK_DDR_DQ:
        if (   (div <= (ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT_SET_MSK + 1))
            && (alt_clk_within_freq_limits(ALT_CLK_SDRAM_PLL_C2, div) == ALT_E_TRUE) )
        {
            wrval = div - 1;
            temp = alt_read_word(ALT_CLKMGR_SDRPLL_EN_ADDR);
            if (temp & ALT_CLKMGR_SDRPLL_EN_DDRDQCLK_SET_MSK)
            {
                // if clock is currently on, gate it off
                alt_write_word(ALT_CLKMGR_SDRPLL_EN_ADDR, temp & ALT_CLKMGR_SDRPLL_EN_DDRDQCLK_CLR_MSK);
                restore_0 = true;
            }

            alt_clk_pllcounter_write(ALT_CLKMGR_SDRPLL_VCO_ADDR,
                                     ALT_CLKMGR_SDRPLL_STAT_ADDR,
                                     ALT_CLKMGR_SDRPLL_DDRDQCLK_ADDR,
                                     wrval,
                                     ALT_CLK_PLL_RST_BIT_C2,
                                     ALT_CLKMGR_SDRPLL_VCO_OUTRST_LSB);
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_SDRPLL_EN_ADDR, temp);         // which has the enable bit set
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_SDRAM_PLL_C5:
    case ALT_CLK_H2F_USER2:
        if (   (div <= (ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT_SET_MSK + 1))
            && (alt_clk_within_freq_limits(ALT_CLK_SDRAM_PLL_C5, div) == ALT_E_TRUE) )
        {
            wrval = div - 1;
            temp = alt_read_word(ALT_CLKMGR_SDRPLL_EN_ADDR);
            if (temp & ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK_SET_MSK)
            {
                // if clock is currently on, gate it off
                alt_write_word(ALT_CLKMGR_SDRPLL_EN_ADDR, temp & ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK_CLR_MSK);
                restore_0 = true;
            }

            alt_clk_pllcounter_write(ALT_CLKMGR_SDRPLL_VCO_ADDR,
                                     ALT_CLKMGR_SDRPLL_STAT_ADDR,
                                     ALT_CLKMGR_SDRPLL_S2FUSER2CLK_ADDR,
                                     wrval,
                                     ALT_CLK_PLL_RST_BIT_C5,
                                     ALT_CLKMGR_SDRPLL_VCO_OUTRST_LSB);
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_SDRPLL_EN_ADDR, temp);         // which has the enable bit set
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

        /////

        // Other clock dividers
    case ALT_CLK_L3_MP:
        if      (div == 1) { wrval = ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_E_DIV1; }
        else if (div == 2) { wrval = ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_E_DIV2; }

        if (wrval != UINT32_MAX)
        {
            temp = alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR);
            if (temp & ALT_CLKMGR_MAINPLL_EN_L3MPCLK_SET_MSK)
            {
                // if clock is currently on, gate it off
                alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp & ALT_CLKMGR_MAINPLL_EN_L3MPCLK_CLR_MSK);
                restore_0 = true;
            }
            alt_replbits_word(ALT_CLKMGR_MAINPLL_MAINDIV_ADDR, ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_SET_MSK,
                              wrval << ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_LSB);
            alt_clk_mgr_wait(ALT_CLKMGR_MAINPLL_EN_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV );
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp);         // which has the enable bit set
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_L3_SP:
        // note that the L3MP divider is upstream from the L3SP divider
        // and any changes to the former will affect the output of both
        if      (div == 1) { wrval = ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_E_DIV1; }
        else if (div == 2) { wrval = ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_E_DIV2; }

        if (wrval != UINT32_MAX)
        {
            alt_replbits_word(ALT_CLKMGR_MAINPLL_MAINDIV_ADDR, ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_SET_MSK,
                              wrval << ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_LSB);
            // no clock gate to close and reopen
            alt_clk_mgr_wait(ALT_CLKMGR_MAINPLL_MAINDIV_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV );
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_L4_MP:
        if      (div ==  1) { wrval = ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_DIV1; }
        else if (div ==  2) { wrval = ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_DIV2; }
        else if (div ==  4) { wrval = ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_DIV4; }
        else if (div ==  8) { wrval = ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_DIV8; }
        else if (div == 16) { wrval = ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_DIV16; }

        if (wrval != UINT32_MAX)
        {
            temp = alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR);
            if (temp & ALT_CLKMGR_MAINPLL_EN_L4MPCLK_SET_MSK)
            {
                // if clock is currently on, gate it off
                alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp & ALT_CLKMGR_MAINPLL_EN_L4MPCLK_CLR_MSK);
                restore_0 = true;
            }
            alt_replbits_word(ALT_CLKMGR_MAINPLL_MAINDIV_ADDR, ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_SET_MSK,
                              wrval << ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_LSB);
            alt_clk_mgr_wait(ALT_CLKMGR_MAINPLL_MAINDIV_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp);         // which has the enable bit set
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_L4_SP:
        if      (div ==  1) { wrval = ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_DIV1; }
        else if (div ==  2) { wrval = ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_DIV2; }
        else if (div ==  4) { wrval = ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_DIV4; }
        else if (div ==  8) { wrval = ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_DIV8; }
        else if (div == 16) { wrval = ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_DIV16; }

        if (wrval != UINT32_MAX)
        {
            temp = alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR);
            if (temp & ALT_CLKMGR_MAINPLL_EN_L4SPCLK_SET_MSK)
            {
                // if clock is currently on, gate it off
                alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp & ALT_CLKMGR_MAINPLL_EN_L4SPCLK_CLR_MSK);
                restore_0 = true;
            }
            alt_replbits_word(ALT_CLKMGR_MAINPLL_MAINDIV_ADDR, ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_SET_MSK,
                              wrval << ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_LSB);
            alt_clk_mgr_wait(ALT_CLKMGR_MAINPLL_MAINDIV_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp);
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_DBG_AT:
        if      (div == 1) { wrval = ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_E_DIV1; }
        else if (div == 2) { wrval = ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_E_DIV2; }
        else if (div == 4) { wrval = ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_E_DIV4; }

        if (wrval != UINT32_MAX)
        {
            temp = alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR);
            if (temp & ALT_CLKMGR_MAINPLL_EN_DBGATCLK_SET_MSK)
            {
                // if clock is currently on, gate it off
                alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp & ALT_CLKMGR_MAINPLL_EN_DBGATCLK_CLR_MSK);
                restore_0 = true;
            }
            alt_replbits_word(ALT_CLKMGR_MAINPLL_DBGDIV_ADDR, ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_SET_MSK,
                              wrval << ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_LSB);
            alt_clk_mgr_wait(ALT_CLKMGR_MAINPLL_DBGDIV_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp);
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_DBG:
        if      (div == 2) { wrval = ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_E_DIV2; }
        else if (div == 4) { wrval = ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_E_DIV4; }

        if (wrval != UINT32_MAX)
        {
            temp = alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR);
            if (temp & ALT_CLKMGR_MAINPLL_EN_DBGCLK_SET_MSK)
            {
                // if clock is currently on, gate it off
                alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp & ALT_CLKMGR_MAINPLL_EN_DBGCLK_CLR_MSK);
                restore_0 = true;
            }
            alt_replbits_word(ALT_CLKMGR_MAINPLL_DBGDIV_ADDR, ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_SET_MSK,
                              wrval << (ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_LSB - 1));
            // account for the fact that the divisor ratios are 2x the value
            alt_clk_mgr_wait(ALT_CLKMGR_MAINPLL_DBGDIV_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp);
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_DBG_TRACE:
        if      (div ==  1) { wrval = ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_DIV1; }
        else if (div ==  2) { wrval = ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_DIV2; }
        else if (div ==  4) { wrval = ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_DIV4; }
        else if (div ==  8) { wrval = ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_DIV8; }
        else if (div == 16) { wrval = ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_DIV16; }

        if (wrval != UINT32_MAX)
        {
            temp = alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR);
            if (temp & ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK_SET_MSK)
            {
                // if clock is currently on, gate it off
                alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp & ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK_CLR_MSK);
                restore_0 = true;
            }
            alt_replbits_word(ALT_CLKMGR_MAINPLL_TRACEDIV_ADDR, ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_SET_MSK,
                              wrval << ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_LSB);
            alt_clk_mgr_wait(ALT_CLKMGR_MAINPLL_TRACEDIV_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, temp);
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_USB_MP:
        if      (div ==  1) { wrval = ALT_CLKMGR_PERPLL_DIV_USBCLK_E_DIV1; }
        else if (div ==  2) { wrval = ALT_CLKMGR_PERPLL_DIV_USBCLK_E_DIV2; }
        else if (div ==  4) { wrval = ALT_CLKMGR_PERPLL_DIV_USBCLK_E_DIV4; }
        else if (div ==  8) { wrval = ALT_CLKMGR_PERPLL_DIV_USBCLK_E_DIV8; }
        else if (div == 16) { wrval = ALT_CLKMGR_PERPLL_DIV_USBCLK_E_DIV16; }

        if (wrval != UINT32_MAX)
        {
            temp = alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR);
            if (temp & ALT_CLKMGR_PERPLL_EN_USBCLK_SET_MSK)
            {
                // if clock is currently on, gate it off
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp & ALT_CLKMGR_PERPLL_EN_USBCLK_CLR_MSK);
                restore_0 = true;
            }
            alt_replbits_word(ALT_CLKMGR_PERPLL_DIV_ADDR, ALT_CLKMGR_PERPLL_DIV_USBCLK_SET_MSK,
                              wrval << ALT_CLKMGR_PERPLL_DIV_USBCLK_LSB);
            alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_DIV_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp);
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_SPI_M:
        if      (div ==  1) { wrval = ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_DIV1; }
        else if (div ==  2) { wrval = ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_DIV2; }
        else if (div ==  4) { wrval = ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_DIV4; }
        else if (div ==  8) { wrval = ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_DIV8; }
        else if (div == 16) { wrval = ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_DIV16; }

        if (wrval != UINT32_MAX)
        {
            temp = alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR);
            if (temp & ALT_CLKMGR_PERPLL_EN_SPIMCLK_SET_MSK)
            {
                // if clock is currently on, gate it off
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp & ALT_CLKMGR_PERPLL_EN_SPIMCLK_CLR_MSK);
                restore_0 = true;
            }
            alt_replbits_word(ALT_CLKMGR_PERPLL_DIV_ADDR, ALT_CLKMGR_PERPLL_DIV_SPIMCLK_SET_MSK,
                              wrval << ALT_CLKMGR_PERPLL_DIV_SPIMCLK_LSB);
            alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_DIV_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp);
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_CAN0:
        if      (div ==  1) { wrval = ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_DIV1; }
        else if (div ==  2) { wrval = ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_DIV2; }
        else if (div ==  4) { wrval = ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_DIV4; }
        else if (div ==  8) { wrval = ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_DIV8; }
        else if (div == 16) { wrval = ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_DIV16; }

        if (wrval != UINT32_MAX)
        {
            temp = alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR);
            if (temp & ALT_CLKMGR_PERPLL_EN_CAN0CLK_SET_MSK)
            {
                // if clock is currently on, gate it off
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp & ALT_CLKMGR_PERPLL_EN_CAN0CLK_CLR_MSK);
                restore_0 = true;
            }
            alt_replbits_word(ALT_CLKMGR_PERPLL_DIV_ADDR, ALT_CLKMGR_PERPLL_DIV_CAN0CLK_SET_MSK,
                              wrval << ALT_CLKMGR_PERPLL_DIV_CAN0CLK_LSB);
            alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_DIV_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp);
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_CAN1:
        if      (div ==  1) { wrval = ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_DIV1; }
        else if (div ==  2) { wrval = ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_DIV2; }
        else if (div ==  4) { wrval = ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_DIV4; }
        else if (div ==  8) { wrval = ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_DIV8; }
        else if (div == 16) { wrval = ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_DIV16; }

        if (wrval != UINT32_MAX)
        {
            temp = alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR);
            if (temp & ALT_CLKMGR_PERPLL_EN_CAN1CLK_SET_MSK)
            {
                // if clock is currently on, gate it off
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp & ALT_CLKMGR_PERPLL_EN_CAN1CLK_CLR_MSK);
                restore_0 = true;
            }
            alt_replbits_word(ALT_CLKMGR_PERPLL_DIV_ADDR, ALT_CLKMGR_PERPLL_DIV_CAN1CLK_SET_MSK,
                              wrval << ALT_CLKMGR_PERPLL_DIV_CAN1CLK_LSB);
            alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_DIV_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp);
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_GPIO_DB:           // GPIO debounce clock
        if (div <= ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK_SET_MSK)
        {
            temp = alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR);
            if (temp & ALT_CLKMGR_PERPLL_EN_GPIOCLK_SET_MSK)
            {
                // if clock is currently on, gate it off
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp & ALT_CLKMGR_PERPLL_EN_GPIOCLK_CLR_MSK);
                restore_0 = true;
            }
            wrval = div - 1;
            alt_replbits_word(ALT_CLKMGR_PERPLL_GPIODIV_ADDR, ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK_SET_MSK,
                              wrval << ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK_LSB);
            alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_GPIODIV_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
            if (restore_0)
            {
                alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, temp);
            }
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = ALT_E_ARG_RANGE;
        }
        break;

    case ALT_CLK_MAIN_QSPI:
        temp = ALT_CLKMGR_PERPLL_SRC_QSPI_GET(alt_read_word(ALT_CLKMGR_PERPLL_SRC_ADDR));
        // get the QSPI clock source
        restore_0 = alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR) & ALT_CLKMGR_PERPLL_EN_QSPICLK_SET_MSK;
        // and the current enable state
        wrval = div - 1;

        if (temp == ALT_CLKMGR_PERPLL_SRC_QSPI_E_MAIN_QSPI_CLK)
        {           // if the main_qspi_clk (Main PLL C3 Ouput) input is selected
            if (div <= ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT_SET_MSK)
            {
                if (restore_0)
                {
                    alt_clrbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_QSPICLK_SET_MSK);
                }                // gate off the QSPI clock

                alt_clk_pllcounter_write(ALT_CLKMGR_MAINPLL_VCO_ADDR,
                                         ALT_CLKMGR_MAINPLL_STAT_ADDR,
                                         ALT_CLKMGR_MAINPLL_MAINQSPICLK_ADDR,
                                         wrval,
                                         ALT_CLK_PLL_RST_BIT_C3,
                                         ALT_CLKMGR_MAINPLL_VCO_OUTRST_LSB);

                alt_clk_mgr_wait(ALT_CLKMGR_MAINPLL_MAINQSPICLK_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
                if (restore_0)
                {
                    alt_setbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_QSPICLK_SET_MSK);
                    // if the QSPI clock was gated on (enabled) before, return it to that state
                }
                ret = ALT_E_SUCCESS;
            }
            else
            {
                ret = ALT_E_ARG_RANGE;
            }
        }
        else if (temp == ALT_CLKMGR_PERPLL_SRC_QSPI_E_PERIPH_QSPI_CLK)
        {
            if (div <= ALT_CLKMGR_PERPLL_PERQSPICLK_CNT_SET_MSK)
            {
                if (restore_0)
                {
                    alt_clrbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_QSPICLK_SET_MSK);
                }                // gate off the QSPI clock

                alt_clk_pllcounter_write(ALT_CLKMGR_PERPLL_VCO_ADDR,
                                         ALT_CLKMGR_PERPLL_STAT_ADDR,
                                         ALT_CLKMGR_PERPLL_PERQSPICLK_ADDR,
                                         wrval,
                                         ALT_CLK_PLL_RST_BIT_C2,
                                         ALT_CLKMGR_PERPLL_VCO_OUTRST_LSB);

                alt_clk_mgr_wait(ALT_CLKMGR_PERPLL_PERQSPICLK_ADDR, ALT_SW_MANAGED_CLK_WAIT_CTRDIV);
                if (restore_0)
                {
                    alt_setbits_word(ALT_CLKMGR_PERPLL_EN_ADDR, ALT_CLKMGR_PERPLL_EN_QSPICLK_SET_MSK);
                    // if the QSPI clock was gated on (enabled) before, return it to that state
                }
                ret = ALT_E_SUCCESS;
            }
            else
            {
                ret = ALT_E_ARG_RANGE;
            }
        }
        break;

        /////

    default:
        ret = ALT_E_BAD_ARG;
        break;
    }

    return ret;
}

//
// alt_clk_freq_get() returns the output frequency of the specified clock.
//
ALT_STATUS_CODE alt_clk_freq_get(ALT_CLK_t clk, alt_freq_t* freq)
{
    ALT_STATUS_CODE ret = ALT_E_BAD_ARG;
    uint32_t        temp = 0;
    uint64_t        numer = 0;
    uint64_t        denom = 1;

    if (freq == NULL)
	{
		return ret;
	}

    switch (clk)
    {
        // External Inputs
    case ALT_CLK_IN_PIN_OSC1:
    case ALT_CLK_OSC1:
        numer = alt_ext_clk_paramblok.clkosc1.freqcur;
        // denom = 1 by default
        ret = ALT_E_SUCCESS;
        break;

    case ALT_CLK_IN_PIN_OSC2:
        numer = alt_ext_clk_paramblok.clkosc2.freqcur;
        // denom = 1 by default
        ret = ALT_E_SUCCESS;
        break;

    case ALT_CLK_F2H_PERIPH_REF:
        numer = alt_ext_clk_paramblok.periph.freqcur;
        // denom = 1 by default
        ret = ALT_E_SUCCESS;
        break;

    case ALT_CLK_F2H_SDRAM_REF:
        numer = alt_ext_clk_paramblok.sdram.freqcur;
        // denom = 1 by default
        ret = ALT_E_SUCCESS;
        break;

        /////

        // PLLs
    case ALT_CLK_MAIN_PLL:
        if (alt_clk_pll_is_bypassed(ALT_CLK_MAIN_PLL) == ALT_E_TRUE)
        {
            temp = alt_ext_clk_paramblok.clkosc1.freqcur;
            ret = ALT_E_SUCCESS;
        }
        else
        {
            ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
        }
        numer = (uint64_t) temp;
        // denom = 1 by default
        break;

    case ALT_CLK_PERIPHERAL_PLL:
        if (alt_clk_pll_is_bypassed(ALT_CLK_PERIPHERAL_PLL) == ALT_E_TRUE)
        {
            temp = ALT_CLKMGR_PERPLL_VCO_PSRC_GET(alt_read_word(ALT_CLKMGR_PERPLL_VCO_ADDR));
            if (temp == ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC1)
            {
                temp = alt_ext_clk_paramblok.clkosc1.freqcur;
                ret = ALT_E_SUCCESS;
            }
            else if (temp == ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC2)
            {
                temp = alt_ext_clk_paramblok.clkosc2.freqcur;
                ret = ALT_E_SUCCESS;
            }
            else if (temp == ALT_CLKMGR_PERPLL_VCO_PSRC_E_F2S_PERIPH_REF)
            {
                temp = alt_ext_clk_paramblok.periph.freqcur;
                ret = ALT_E_SUCCESS;
            }
            else
            {
                ret = ALT_E_ERROR;
            }
        }
        else
        {
            ret = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &temp);
        }
        numer = (uint64_t) temp;
        // denom = 1 by default
        break;

    case ALT_CLK_SDRAM_PLL:
        if (alt_clk_pll_is_bypassed(ALT_CLK_SDRAM_PLL) == ALT_E_TRUE)
        {
            temp = ALT_CLKMGR_SDRPLL_VCO_SSRC_GET(alt_read_word(ALT_CLKMGR_SDRPLL_VCO_ADDR));
            if (temp == ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC1)
            {
                temp = alt_ext_clk_paramblok.clkosc1.freqcur;
                ret = ALT_E_SUCCESS;
            }
            else if (temp == ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC2)
            {
                temp = alt_ext_clk_paramblok.clkosc2.freqcur;
                ret = ALT_E_SUCCESS;
            }
            else if (temp == ALT_CLKMGR_SDRPLL_VCO_SSRC_E_F2S_SDRAM_REF)
            {
                temp = alt_ext_clk_paramblok.sdram.freqcur;
                ret = ALT_E_SUCCESS;
            }
            else
            {
                ret = ALT_E_ERROR;
            }
        }
        else
        {
            ret = alt_clk_pll_vco_freq_get(ALT_CLK_SDRAM_PLL, &temp);
        }
        numer = (uint64_t) temp;
        // denom = 1 by default
        break;

        /////

        // Main Clock Group
    case ALT_CLK_MAIN_PLL_C0:
    case ALT_CLK_MAIN_PLL_C1:
    case ALT_CLK_MAIN_PLL_C2:
    case ALT_CLK_MAIN_PLL_C3:
    case ALT_CLK_MAIN_PLL_C4:
    case ALT_CLK_MAIN_PLL_C5:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(clk, &temp);
            denom = (uint64_t) temp;
        }
        break;

    case ALT_CLK_MPU:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C0, &temp);
            denom = (uint64_t) temp;
        }
        break;

    case ALT_CLK_MPU_PERIPH:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C0, &temp);
        }
        if (ret == ALT_E_SUCCESS)
        {
            denom = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_MPU_PERIPH, &temp);
            denom = denom * (uint64_t) temp;
        }
        break;

    case ALT_CLK_MPU_L2_RAM:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C0, &temp);
        }
        if (ret == ALT_E_SUCCESS)
        {
            denom = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_MPU_L2_RAM, &temp);
            denom = denom * (uint64_t) temp;
        }
        break;

    case ALT_CLK_L4_MAIN:
    case ALT_CLK_L3_MAIN:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C1, &temp);
            denom = (uint64_t) temp;
        }
        break;

    case ALT_CLK_L3_MP:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C1, &temp);
        }
        if (ret == ALT_E_SUCCESS)
        {
            denom = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_L3_MP, &temp);
            denom = denom * (uint64_t) temp;
        }
        break;

    case ALT_CLK_L3_SP:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C1, &temp);
        }
        if (ret == ALT_E_SUCCESS)
        {
            denom = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_L3_MP, &temp);
        }
        if (ret == ALT_E_SUCCESS)
        {
            denom = denom * (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_L3_SP, &temp);
            denom = denom * (uint64_t) temp;
        }
        break;

    case ALT_CLK_L4_MP:
        ret = alt_clk_divider_get(ALT_CLK_L4_MP, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            denom = (uint64_t) temp;
            temp = ALT_CLKMGR_MAINPLL_L4SRC_L4MP_GET(alt_read_word(ALT_CLKMGR_MAINPLL_L4SRC_ADDR));
            if (temp == ALT_CLKMGR_MAINPLL_L4SRC_L4MP_E_MAINPLL)
            {
                ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
                if (ret == ALT_E_SUCCESS)
                {
                    numer = (uint64_t) temp;
                    ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C1, &temp);
                    denom = denom * (uint64_t) temp;        // no real harm if temp is garbage data
                }
            }
            else if (temp == ALT_CLKMGR_MAINPLL_L4SRC_L4MP_E_PERIPHPLL)
            {
                ret = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &temp);
                if (ret == ALT_E_SUCCESS)
                {
                    numer = (uint64_t) temp;
                    ret = alt_clk_divider_get(ALT_CLK_PERIPHERAL_PLL_C4, &temp);
                    denom = denom * (uint64_t) temp;
                }
            }
        }
        break;

    case ALT_CLK_L4_SP:
        ret = alt_clk_divider_get(ALT_CLK_L4_SP, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            denom = (uint64_t) temp;
            temp = ALT_CLKMGR_MAINPLL_L4SRC_L4SP_GET(alt_read_word(ALT_CLKMGR_MAINPLL_L4SRC_ADDR));
            if (temp == ALT_CLKMGR_MAINPLL_L4SRC_L4SP_E_MAINPLL)
            {
                ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
                if (ret == ALT_E_SUCCESS)
                {
                    numer = (uint64_t) temp;
                    ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C1, &temp);
                    denom = denom * (uint64_t) temp;
                }
            }
            else if (temp == ALT_CLKMGR_MAINPLL_L4SRC_L4SP_E_PERIPHPLL)         // periph_base_clk
            {
                ret = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &temp);
                if (ret == ALT_E_SUCCESS)
                {
                    numer = (uint64_t) temp;
                    ret = alt_clk_divider_get(ALT_CLK_PERIPHERAL_PLL_C4, &temp);
                    denom = denom * (uint64_t) temp;
                }
            }
        }
        break;

    case ALT_CLK_DBG_BASE:
    case ALT_CLK_DBG_TIMER:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C2, &temp);
            denom = (uint64_t) temp;
        }
        break;

    case ALT_CLK_DBG_AT:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C2, &temp);
        }
        if (ret == ALT_E_SUCCESS)
        {
            denom = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_DBG_AT, &temp);
            denom = denom * (uint64_t) temp;
        }
        break;

    case ALT_CLK_DBG:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C2, &temp);
        }
        if (ret == ALT_E_SUCCESS)
        {
            denom = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_DBG_AT, &temp);
        }
        if (ret == ALT_E_SUCCESS)
        {
            denom = denom * (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_DBG, &temp);
            denom = denom * (uint64_t) temp;
        }
        break;

    case ALT_CLK_DBG_TRACE:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C2, &temp);
        }
        if (ret == ALT_E_SUCCESS)
        {
            denom = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_DBG_TRACE, &temp);
            denom = denom * (uint64_t) temp;
        }
        break;

    case ALT_CLK_MAIN_QSPI:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C3, &temp);
            denom = (uint64_t) temp;
        }
        break;

    case ALT_CLK_MAIN_NAND_SDMMC:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C4, &temp);
            denom = (uint64_t) temp;
        }
        break;

    case ALT_CLK_CFG:
    case ALT_CLK_H2F_USER0:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C5, &temp);
            denom = (uint64_t) temp;
        }
        break;

        /////

        // Peripheral Clock Group
    case ALT_CLK_PERIPHERAL_PLL_C0:
    case ALT_CLK_PERIPHERAL_PLL_C1:
    case ALT_CLK_PERIPHERAL_PLL_C2:
    case ALT_CLK_PERIPHERAL_PLL_C3:
    case ALT_CLK_PERIPHERAL_PLL_C4:
    case ALT_CLK_PERIPHERAL_PLL_C5:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(clk, &temp);
            denom = (uint64_t) temp;
        }
        break;

    case ALT_CLK_EMAC0:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_PERIPHERAL_PLL_C0, &temp);
            denom = (uint64_t) temp;
        }
        break;

    case ALT_CLK_EMAC1:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_PERIPHERAL_PLL_C1, &temp);
            denom = (uint64_t) temp;
        }
        break;

    case ALT_CLK_USB_MP:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_PERIPHERAL_PLL_C4, &temp);
            if (ret == ALT_E_SUCCESS)
            {
                denom = (uint64_t) temp;
                ret = alt_clk_divider_get(ALT_CLK_USB_MP, &temp);
                denom = denom * (uint64_t) temp;
            }
        }
        break;

    case ALT_CLK_SPI_M:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_PERIPHERAL_PLL_C4, &temp);
        }
        if (ret == ALT_E_SUCCESS)
        {
            denom = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_SPI_M, &temp);
            denom = denom * (uint64_t) temp;
        }
        break;

    case ALT_CLK_CAN0:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_PERIPHERAL_PLL_C4, &temp);
        }
        if (ret == ALT_E_SUCCESS)
        {
            denom = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_CAN0, &temp);
            denom = denom * (uint64_t) temp;
        }
        break;

    case ALT_CLK_CAN1:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_PERIPHERAL_PLL_C4, &temp);
        }
        if (ret == ALT_E_SUCCESS)
        {
            denom = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_CAN1, &temp);
            denom = denom * (uint64_t) temp;
        }
        break;

    case ALT_CLK_GPIO_DB:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_PERIPHERAL_PLL_C4, &temp);
        }
        if (ret == ALT_E_SUCCESS)
        {
            denom = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_GPIO_DB, &temp);
            denom = denom * (uint64_t) temp;
        }
        break;

    case ALT_CLK_H2F_USER1:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_PERIPHERAL_PLL_C5, &temp);
            denom = (uint64_t) temp;
        }
        break;

        /* Clocks That Can Switch Between Different Clock Groups */
    case ALT_CLK_SDMMC:
        temp = ALT_CLKMGR_PERPLL_SRC_SDMMC_GET(alt_read_word(ALT_CLKMGR_PERPLL_SRC_ADDR));
        if (temp == ALT_CLKMGR_PERPLL_SRC_SDMMC_E_F2S_PERIPH_REF_CLK)
        {
            numer = (uint64_t) alt_ext_clk_paramblok.periph.freqcur;
            // denom = 1 by default
            ret = ALT_E_SUCCESS;
        }
        else if (temp == ALT_CLKMGR_PERPLL_SRC_SDMMC_E_MAIN_NAND_CLK)
        {
            ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
            if (ret == ALT_E_SUCCESS)
            {
                numer = (uint64_t) temp;
                ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C4, &temp);
                denom = (uint64_t) temp;
            }
        }
        else if (temp == ALT_CLKMGR_PERPLL_SRC_SDMMC_E_PERIPH_NAND_CLK)
        {
            ret = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &temp);
            if (ret == ALT_E_SUCCESS)
            {
                numer = (uint64_t) temp;
                ret = alt_clk_divider_get(ALT_CLK_PERIPHERAL_PLL_C3, &temp);
                denom = (uint64_t) temp;
            }
        }
        else
        {
            ret = ALT_E_ERROR;
        }
        break;

    case ALT_CLK_NAND:
        denom = 4;
        // the absence of a break statement here is not a mistake
    case ALT_CLK_NAND_X:
        temp = ALT_CLKMGR_PERPLL_SRC_NAND_GET(alt_read_word(ALT_CLKMGR_PERPLL_SRC_ADDR));
        if (temp == ALT_CLKMGR_PERPLL_SRC_NAND_E_F2S_PERIPH_REF_CLK)
        {
            numer = (uint64_t) alt_ext_clk_paramblok.periph.freqcur;
            // denom = 1 or 4 by default;
            ret = ALT_E_SUCCESS;
        }
        else if (temp == ALT_CLKMGR_PERPLL_SRC_NAND_E_MAIN_NAND_CLK)
        {
            ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
            if (ret == ALT_E_SUCCESS)
            {
                numer = (uint64_t) temp;
                ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C4, &temp);
                denom = denom * (uint64_t) temp;
            }
        }
        else if (temp == ALT_CLKMGR_PERPLL_SRC_NAND_E_PERIPH_NAND_CLK)
        {
            ret = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &temp);
            if (ret == ALT_E_SUCCESS)
            {
                numer = (uint64_t) temp;
                ret = alt_clk_divider_get(ALT_CLK_PERIPHERAL_PLL_C3, &temp);
                denom = denom * (uint64_t) temp;
            }
        }
        else
        {
            ret = ALT_E_ERROR;
        }
        break;

    case ALT_CLK_QSPI:
        temp = ALT_CLKMGR_PERPLL_SRC_QSPI_GET(alt_read_word(ALT_CLKMGR_PERPLL_SRC_ADDR));
        if (temp == ALT_CLKMGR_PERPLL_SRC_QSPI_E_F2S_PERIPH_REF_CLK)
        {
            numer = (uint64_t) alt_ext_clk_paramblok.periph.freqcur;
            // denom = 1 by default;
            ret = ALT_E_SUCCESS;
        }
        else if (temp == ALT_CLKMGR_PERPLL_SRC_QSPI_E_MAIN_QSPI_CLK)
        {
            ret = alt_clk_pll_vco_freq_get(ALT_CLK_MAIN_PLL, &temp);
            if (ret == ALT_E_SUCCESS)
            {
                numer = (uint64_t) temp;
                ret = alt_clk_divider_get(ALT_CLK_MAIN_PLL_C3, &temp);
                denom = (uint64_t) temp;
            }
        }
        else if (temp == ALT_CLKMGR_PERPLL_SRC_QSPI_E_PERIPH_QSPI_CLK)
        {
            ret = alt_clk_pll_vco_freq_get(ALT_CLK_PERIPHERAL_PLL, &temp);
            if (ret == ALT_E_SUCCESS)
            {
                numer = (uint64_t) temp;
                ret = alt_clk_divider_get(ALT_CLK_PERIPHERAL_PLL_C2, &temp);
                denom = (uint64_t) temp;
            }
        }
        else
        {
            ret = ALT_E_ERROR;
        }
        break;

        /////

        // SDRAM Clock Group
    case ALT_CLK_SDRAM_PLL_C0:
    case ALT_CLK_DDR_DQS:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_SDRAM_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_SDRAM_PLL_C0, &temp);
            denom = (uint64_t) temp;
        }
        break;

    case ALT_CLK_SDRAM_PLL_C1:
    case ALT_CLK_DDR_2X_DQS:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_SDRAM_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_SDRAM_PLL_C1, &temp);
            denom = (uint64_t) temp;
        }
        break;

    case ALT_CLK_SDRAM_PLL_C2:
    case ALT_CLK_DDR_DQ:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_SDRAM_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_SDRAM_PLL_C2, &temp);
            denom = (uint64_t) temp;
        }
        break;

    case ALT_CLK_SDRAM_PLL_C5:
    case ALT_CLK_H2F_USER2:
        ret = alt_clk_pll_vco_freq_get(ALT_CLK_SDRAM_PLL, &temp);
        if (ret == ALT_E_SUCCESS)
        {
            numer = (uint64_t) temp;
            ret = alt_clk_divider_get(ALT_CLK_SDRAM_PLL_C5, &temp);
            denom = (uint64_t) temp;
        }
        break;

    default:
        ret = ALT_E_BAD_ARG;
        break;

    }   // end of switch-case construct

    if (ret == ALT_E_SUCCESS)
    {
        // will not get here if none of above cases match
        if (denom > 0)
        {
            numer /= denom;
            if (numer <= UINT32_MAX)
            {
                *freq = (uint32_t) numer;
            }
            else
            {
                ret = ALT_E_ERROR;
            }
        }
        else
        {
            ret = ALT_E_ERROR;
        }
    }

    return ret;
}

//
// alt_clk_irq_disable() disables one or more of the lock status conditions as
// contributors to the clkmgr_IRQ interrupt signal state.
//
ALT_STATUS_CODE alt_clk_irq_disable(ALT_CLK_PLL_LOCK_STATUS_t lock_stat_mask)
{
    if (!(lock_stat_mask & ALT_CLK_MGR_PLL_LOCK_BITS))
    {
        alt_clrbits_word(ALT_CLKMGR_INTREN_ADDR, lock_stat_mask);
        return ALT_E_SUCCESS;
    }
    else
    {
        return ALT_E_BAD_ARG;
    }
}

//
// alt_clk_irq_enable() enables one or more of the lock status conditions as
// contributors to the clkmgr_IRQ interrupt signal state.
//
ALT_STATUS_CODE alt_clk_irq_enable(ALT_CLK_PLL_LOCK_STATUS_t lock_stat_mask)
{
    if (!(lock_stat_mask & ALT_CLK_MGR_PLL_LOCK_BITS))
    {
        alt_setbits_word(ALT_CLKMGR_INTREN_ADDR, lock_stat_mask);
        return ALT_E_SUCCESS;
    }
    else
    {
        return ALT_E_BAD_ARG;
    }
}

/////

//
// alt_clk_group_cfg_raw_get() gets the raw configuration state of the designated
// clock group.
//
ALT_STATUS_CODE alt_clk_group_cfg_raw_get(ALT_CLK_GRP_t clk_group,
                                          ALT_CLK_GROUP_RAW_CFG_t * clk_group_raw_cfg)
{
    clk_group_raw_cfg->verid     = alt_read_word(ALT_SYSMGR_SILICONID1_ADDR);
    clk_group_raw_cfg->siliid2   = alt_read_word(ALT_SYSMGR_SILICONID2_ADDR);
    clk_group_raw_cfg->clkgrpsel = clk_group;

    if (clk_group == ALT_MAIN_PLL_CLK_GRP)
    {
        // Main PLL VCO register
        clk_group_raw_cfg->clkgrp.mainpllgrp.raw.vco = alt_read_word(ALT_CLKMGR_MAINPLL_VCO_ADDR);

        // Main PLL Misc register
        clk_group_raw_cfg->clkgrp.mainpllgrp.raw.misc = alt_read_word(ALT_CLKMGR_MAINPLL_MISC_ADDR);

        // Main PLL C0-C5 Counter registers
        clk_group_raw_cfg->clkgrp.mainpllgrp.raw.mpuclk = alt_read_word(ALT_CLKMGR_MAINPLL_MPUCLK_ADDR);
        // doing these as 32-bit reads and writes avoids unnecessary masking operations

        clk_group_raw_cfg->clkgrp.mainpllgrp.raw.mainclk          = alt_read_word(ALT_CLKMGR_MAINPLL_MAINCLK_ADDR);
        clk_group_raw_cfg->clkgrp.mainpllgrp.raw.dbgatclk         = alt_read_word(ALT_CLKMGR_MAINPLL_DBGATCLK_ADDR);
        clk_group_raw_cfg->clkgrp.mainpllgrp.raw.mainqspiclk      = alt_read_word(ALT_CLKMGR_MAINPLL_MAINQSPICLK_ADDR);
        clk_group_raw_cfg->clkgrp.mainpllgrp.raw.mainnandsdmmcclk = alt_read_word(ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_ADDR);
        clk_group_raw_cfg->clkgrp.mainpllgrp.raw.cfgs2fuser0clk   = alt_read_word(ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_ADDR);

        // Main PLL Enable register
        clk_group_raw_cfg->clkgrp.mainpllgrp.raw.en = alt_read_word(ALT_CLKMGR_MAINPLL_EN_ADDR);

        // Main PLL Maindiv register
        clk_group_raw_cfg->clkgrp.mainpllgrp.raw.maindiv = alt_read_word(ALT_CLKMGR_MAINPLL_MAINDIV_ADDR);

        // Main PLL Debugdiv register
        clk_group_raw_cfg->clkgrp.mainpllgrp.raw.dbgdiv = alt_read_word(ALT_CLKMGR_MAINPLL_DBGDIV_ADDR);

        // Main PLL Tracediv register
        clk_group_raw_cfg->clkgrp.mainpllgrp.raw.tracediv = alt_read_word(ALT_CLKMGR_MAINPLL_TRACEDIV_ADDR);

        // Main PLL L4 Source register
        clk_group_raw_cfg->clkgrp.mainpllgrp.raw.l4src = alt_read_word(ALT_CLKMGR_MAINPLL_L4SRC_ADDR);

        // Main PLL Status register
        clk_group_raw_cfg->clkgrp.mainpllgrp.raw.stat = alt_read_word(ALT_CLKMGR_MAINPLL_STAT_ADDR);
        // clkgrp.mainpllgrp.stat.outresetack is defined in the ALT_CLKMGR_MAINPLL_STAT_s declaration
        // as a const but alt_indwrite_word() overrides that restriction.

        // padding ...
        clk_group_raw_cfg->clkgrp.mainpllgrp.raw._pad_0x38_0x40[0] = 0;
        clk_group_raw_cfg->clkgrp.mainpllgrp.raw._pad_0x38_0x40[1] = 0;

        return ALT_E_SUCCESS;
    }
    else if (clk_group == ALT_PERIPH_PLL_CLK_GRP)
    {
        // Peripheral PLL VCO register
        clk_group_raw_cfg->clkgrp.perpllgrp.raw.vco = alt_read_word(ALT_CLKMGR_PERPLL_VCO_ADDR);

        // Peripheral PLL Misc register
        clk_group_raw_cfg->clkgrp.perpllgrp.raw.misc = alt_read_word(ALT_CLKMGR_PERPLL_MISC_ADDR);

        // Peripheral PLL C0-C5 Counters
        clk_group_raw_cfg->clkgrp.perpllgrp.raw.emac0clk = alt_read_word(ALT_CLKMGR_PERPLL_EMAC0CLK_ADDR);
        // doing these as 32-bit reads and writes avoids unnecessary masking operations

        clk_group_raw_cfg->clkgrp.perpllgrp.raw.emac1clk        = alt_read_word(ALT_CLKMGR_PERPLL_EMAC1CLK_ADDR);
        clk_group_raw_cfg->clkgrp.perpllgrp.raw.perqspiclk      = alt_read_word(ALT_CLKMGR_PERPLL_PERQSPICLK_ADDR);
        clk_group_raw_cfg->clkgrp.perpllgrp.raw.pernandsdmmcclk = alt_read_word(ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_ADDR);
        clk_group_raw_cfg->clkgrp.perpllgrp.raw.perbaseclk      = alt_read_word(ALT_CLKMGR_PERPLL_PERBASECLK_ADDR);
        clk_group_raw_cfg->clkgrp.perpllgrp.raw.s2fuser1clk     = alt_read_word(ALT_CLKMGR_PERPLL_S2FUSER1CLK_ADDR);

        // Peripheral PLL Enable register
        clk_group_raw_cfg->clkgrp.perpllgrp.raw.en = alt_read_word(ALT_CLKMGR_PERPLL_EN_ADDR);

        // Peripheral PLL Divider register
        clk_group_raw_cfg->clkgrp.perpllgrp.raw.div = alt_read_word(ALT_CLKMGR_PERPLL_DIV_ADDR);

        // Peripheral PLL GPIO Divider register
        clk_group_raw_cfg->clkgrp.perpllgrp.raw.gpiodiv = alt_read_word(ALT_CLKMGR_PERPLL_GPIODIV_ADDR);

        // Peripheral PLL Source register
        clk_group_raw_cfg->clkgrp.perpllgrp.raw.src = alt_read_word(ALT_CLKMGR_PERPLL_SRC_ADDR);

        // Peripheral PLL Status register
        clk_group_raw_cfg->clkgrp.perpllgrp.raw.stat = alt_read_word(ALT_CLKMGR_PERPLL_STAT_ADDR);

        // padding ...
        clk_group_raw_cfg->clkgrp.perpllgrp.raw._pad_0x34_0x40[0] = 0;
        clk_group_raw_cfg->clkgrp.perpllgrp.raw._pad_0x34_0x40[1] = 0;
        clk_group_raw_cfg->clkgrp.perpllgrp.raw._pad_0x34_0x40[2] = 0;

        return ALT_E_SUCCESS;
    }
    else if (clk_group == ALT_SDRAM_PLL_CLK_GRP)
    {
        // SDRAM PLL VCO register
        clk_group_raw_cfg->clkgrp.sdrpllgrp.raw.vco = alt_read_word(ALT_CLKMGR_SDRPLL_VCO_ADDR);

        // SDRAM PLL Control register
        clk_group_raw_cfg->clkgrp.sdrpllgrp.raw.ctrl = alt_read_word(ALT_CLKMGR_SDRPLL_CTL_ADDR);

        // SDRAM PLL C0-C2 & C5 Counters
        clk_group_raw_cfg->clkgrp.sdrpllgrp.raw.ddrdqsclk = alt_read_word(ALT_CLKMGR_SDRPLL_DDRDQSCLK_ADDR);
        // doing these as 32-bit reads and writes avoids unnecessary masking operations

        clk_group_raw_cfg->clkgrp.sdrpllgrp.raw.ddr2xdqsclk = alt_read_word(ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_ADDR);
        clk_group_raw_cfg->clkgrp.sdrpllgrp.raw.ddrdqclk    = alt_read_word(ALT_CLKMGR_SDRPLL_DDRDQCLK_ADDR);
        clk_group_raw_cfg->clkgrp.sdrpllgrp.raw.s2fuser2clk = alt_read_word(ALT_CLKMGR_SDRPLL_S2FUSER2CLK_ADDR);

        // SDRAM PLL Enable register
        clk_group_raw_cfg->clkgrp.sdrpllgrp.raw.en = alt_read_word(ALT_CLKMGR_SDRPLL_EN_ADDR);

        // SDRAM PLL Status register
        clk_group_raw_cfg->clkgrp.sdrpllgrp.raw.stat = alt_read_word(ALT_CLKMGR_SDRPLL_STAT_ADDR);

        return ALT_E_SUCCESS;
    }
    else
    {
        return ALT_E_BAD_ARG;
    }
}

//
// alt_clk_group_cfg_raw_set() sets the clock group configuration.
//
ALT_STATUS_CODE alt_clk_group_cfg_raw_set(const ALT_CLK_GROUP_RAW_CFG_t * clk_group_raw_cfg)
{
    // test for matching silicon ID, but not for matching silicon revision number
    if (ALT_SYSMGR_SILICONID1_ID_GET(alt_read_word(ALT_SYSMGR_SILICONID1_ADDR)) !=
        ALT_SYSMGR_SILICONID1_ID_GET(clk_group_raw_cfg->verid))
    {
        return ALT_E_BAD_VERSION;
    }

    // get the PLL ID
    ALT_CLK_GRP_t clk_group = clk_group_raw_cfg->clkgrpsel;
    ALT_CLK_t     pll;

    if      (clk_group == ALT_MAIN_PLL_CLK_GRP)   { pll = ALT_CLK_MAIN_PLL; }
    else if (clk_group == ALT_PERIPH_PLL_CLK_GRP) { pll = ALT_CLK_PERIPHERAL_PLL; }
    else if (clk_group == ALT_SDRAM_PLL_CLK_GRP)  { pll = ALT_CLK_SDRAM_PLL; }
    else
    {
        return ALT_E_ERROR;
    }

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // if the PLL isn't in bypass mode, put it in bypass mode
    bool byp = false;
    if (alt_clk_pll_is_bypassed(pll) == ALT_E_FALSE)
    {
        status = alt_clk_pll_bypass_enable(pll, false);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }

        byp = true;
    }

    // now write the values in the ALT_CLK_GROUP_RAW_CFG_t structure to the registers
    if (clk_group == ALT_MAIN_PLL_CLK_GRP)
    {
        // Main PLL VCO register
        alt_write_word(ALT_CLKMGR_MAINPLL_VCO_ADDR, clk_group_raw_cfg->clkgrp.mainpllgrp.raw.vco &
                       ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL_CLR_MSK & ALT_CLKMGR_MAINPLL_VCO_OUTRST_CLR_MSK);
        // the outreset and outresetall bits were probably clear when the
        // state was saved, but make sure they're clear now

        // Main PLL Misc register
        alt_write_word(ALT_CLKMGR_MAINPLL_MISC_ADDR, clk_group_raw_cfg->clkgrp.mainpllgrp.raw.misc);

        // Main PLL C0-C5 Counter registers
        alt_write_word(ALT_CLKMGR_MAINPLL_MPUCLK_ADDR,           clk_group_raw_cfg->clkgrp.mainpllgrp.raw.mpuclk);
        alt_write_word(ALT_CLKMGR_MAINPLL_MAINCLK_ADDR,          clk_group_raw_cfg->clkgrp.mainpllgrp.raw.mainclk);
        alt_write_word(ALT_CLKMGR_MAINPLL_DBGATCLK_ADDR,         clk_group_raw_cfg->clkgrp.mainpllgrp.raw.dbgatclk);
        alt_write_word(ALT_CLKMGR_MAINPLL_MAINQSPICLK_ADDR,      clk_group_raw_cfg->clkgrp.mainpllgrp.raw.mainqspiclk);
        alt_write_word(ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_ADDR, clk_group_raw_cfg->clkgrp.mainpllgrp.raw.mainnandsdmmcclk);
        alt_write_word(ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_ADDR,   clk_group_raw_cfg->clkgrp.mainpllgrp.raw.cfgs2fuser0clk);

        // Main PLL Counter Enable register
        alt_write_word(ALT_CLKMGR_MAINPLL_EN_ADDR, clk_group_raw_cfg->clkgrp.mainpllgrp.raw.en);

        // Main PLL Maindiv register
        alt_write_word(ALT_CLKMGR_MAINPLL_MAINDIV_ADDR, clk_group_raw_cfg->clkgrp.mainpllgrp.raw.maindiv);

        // Main PLL Debugdiv register
        alt_write_word(ALT_CLKMGR_MAINPLL_DBGDIV_ADDR, clk_group_raw_cfg->clkgrp.mainpllgrp.raw.dbgdiv);

        // Main PLL Tracediv register
        alt_write_word(ALT_CLKMGR_MAINPLL_TRACEDIV_ADDR, clk_group_raw_cfg->clkgrp.mainpllgrp.raw.tracediv);

        // Main PLL L4 Source register
        alt_write_word(ALT_CLKMGR_MAINPLL_L4SRC_ADDR, clk_group_raw_cfg->clkgrp.mainpllgrp.raw.l4src);
    }
    else if (clk_group == ALT_PERIPH_PLL_CLK_GRP)
    {
        // Peripheral PLL VCO register
        alt_write_word(ALT_CLKMGR_PERPLL_VCO_ADDR, clk_group_raw_cfg->clkgrp.perpllgrp.raw.vco &
                       ALT_CLKMGR_PERPLL_VCO_OUTRST_CLR_MSK & ALT_CLKMGR_PERPLL_VCO_OUTRSTALL_CLR_MSK);
        // the outreset and outresetall bits were probably clear when the
        // state was saved, but make sure they're clear now

        // Peripheral PLL Misc register
        alt_write_word(ALT_CLKMGR_PERPLL_MISC_ADDR, clk_group_raw_cfg->clkgrp.perpllgrp.raw.misc);

        // Peripheral PLL C0-C5 Counters
        alt_write_word(ALT_CLKMGR_PERPLL_EMAC0CLK_ADDR,        clk_group_raw_cfg->clkgrp.perpllgrp.raw.emac0clk);
        alt_write_word(ALT_CLKMGR_PERPLL_EMAC1CLK_ADDR,        clk_group_raw_cfg->clkgrp.perpllgrp.raw.emac1clk);
        alt_write_word(ALT_CLKMGR_PERPLL_PERQSPICLK_ADDR,      clk_group_raw_cfg->clkgrp.perpllgrp.raw.perqspiclk);
        alt_write_word(ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_ADDR, clk_group_raw_cfg->clkgrp.perpllgrp.raw.pernandsdmmcclk);
        alt_write_word(ALT_CLKMGR_PERPLL_PERBASECLK_ADDR,      clk_group_raw_cfg->clkgrp.perpllgrp.raw.perbaseclk);
        alt_write_word(ALT_CLKMGR_PERPLL_S2FUSER1CLK_ADDR,     clk_group_raw_cfg->clkgrp.perpllgrp.raw.s2fuser1clk);

        // Peripheral PLL Counter Enable register
        alt_write_word(ALT_CLKMGR_PERPLL_EN_ADDR, clk_group_raw_cfg->clkgrp.perpllgrp.raw.en);

        // Peripheral PLL Divider register
        alt_write_word(ALT_CLKMGR_PERPLL_DIV_ADDR, clk_group_raw_cfg->clkgrp.perpllgrp.raw.div);

        // Peripheral PLL GPIO Divider register
        alt_write_word(ALT_CLKMGR_PERPLL_GPIODIV_ADDR, clk_group_raw_cfg->clkgrp.perpllgrp.raw.gpiodiv);

        // Peripheral PLL Source register
        alt_write_word(ALT_CLKMGR_PERPLL_SRC_ADDR, clk_group_raw_cfg->clkgrp.perpllgrp.raw.src);
    }
    else if (clk_group == ALT_SDRAM_PLL_CLK_GRP)
    {
        // SDRAM PLL VCO register
        alt_write_word(ALT_CLKMGR_SDRPLL_VCO_ADDR, clk_group_raw_cfg->clkgrp.sdrpllgrp.raw.vco &
                       ALT_CLKMGR_SDRPLL_VCO_OUTRST_CLR_MSK & ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL_CLR_MSK);
        // the outreset and outresetall bits were probably clear when the
        // state was saved, but make sure they're clear now

        // SDRAM PLL Control register
        alt_write_word(ALT_CLKMGR_SDRPLL_CTL_ADDR, clk_group_raw_cfg->clkgrp.sdrpllgrp.raw.ctrl);

        // SDRAM PLL C0-C2 & C5 Counters
        alt_write_word(ALT_CLKMGR_SDRPLL_DDRDQSCLK_ADDR,   clk_group_raw_cfg->clkgrp.sdrpllgrp.raw.ddrdqsclk);
        alt_write_word(ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_ADDR, clk_group_raw_cfg->clkgrp.sdrpllgrp.raw.ddr2xdqsclk);
        alt_write_word(ALT_CLKMGR_SDRPLL_DDRDQCLK_ADDR,    clk_group_raw_cfg->clkgrp.sdrpllgrp.raw.ddrdqclk);
        alt_write_word(ALT_CLKMGR_SDRPLL_S2FUSER2CLK_ADDR, clk_group_raw_cfg->clkgrp.sdrpllgrp.raw.s2fuser2clk);

        // SDRAM PLL Counter Enable register
        alt_write_word(ALT_CLKMGR_SDRPLL_EN_ADDR, clk_group_raw_cfg->clkgrp.sdrpllgrp.raw.en);
    }

    // if PLL was not bypassed before, restore that state
    if (byp)
    {
        status = alt_clk_pll_bypass_disable(pll);
    }

    return status;
}

//
// alt_clk_id_to_string() converts a clock ID to a text string.
//
ALT_STATUS_CODE alt_clk_id_to_string(ALT_CLK_t clk_id, char * output, size_t size)
{
    char * name = NULL;

    switch (clk_id)
    {
    case ALT_CLK_IN_PIN_OSC1:
        name =  "IN_PIN_OSC1";
        break;
    case ALT_CLK_IN_PIN_OSC2:
        name =  "IN_PIN_OSC2";
        break;

        // FPGA Clock Sources External to HPS
    case ALT_CLK_F2H_PERIPH_REF:
        name =  "F2H_PERIPH_REF";
        break;
    case ALT_CLK_F2H_SDRAM_REF:
        name =  "F2H_SDRAM_REF";
        break;

        // Other Clock Sources External to HPS
    case ALT_CLK_IN_PIN_JTAG:
        name =  "IN_PIN_JTAG";
        break;
    case ALT_CLK_IN_PIN_ULPI0:
        name =  "IN_PIN_ULPI0";
        break;
    case ALT_CLK_IN_PIN_ULPI1:
        name =  "IN_PIN_ULPI1";
        break;
    case ALT_CLK_IN_PIN_EMAC0_RX:
        name =  "IN_PIN_EMAC0_RX";
        break;
    case ALT_CLK_IN_PIN_EMAC1_RX:
        name =  "IN_PIN_EMAC1_RX";
        break;

        // PLLs
    case ALT_CLK_MAIN_PLL:
        name =  "MAIN_PLL";
        break;
    case ALT_CLK_PERIPHERAL_PLL:
        name =  "PERIPHERAL_PLL";
        break;
    case ALT_CLK_SDRAM_PLL:
        name =  "SDRAM_PLL";
        break;

        // OSC1 Clock Group - The OSC1 clock group contains those clocks which are derived
        // directly from the osc_clk_1_HPS pin
    case ALT_CLK_OSC1:
        name =  "OSC1";
        break;

        // Main Clock Group - The following clocks are derived from the Main PLL.
    case ALT_CLK_MAIN_PLL_C0:
        name =  "MAIN_PLL_C0";
        break;
    case ALT_CLK_MAIN_PLL_C1:
        name =  "MAIN_PLL_C1";
        break;
    case ALT_CLK_MAIN_PLL_C2:
        name =  "MAIN_PLL_C2";
        break;
    case ALT_CLK_MAIN_PLL_C3:
        name =  "MAIN_PLL_C3";
        break;
    case ALT_CLK_MAIN_PLL_C4:
        name =  "MAIN_PLL_C4";
        break;
    case ALT_CLK_MAIN_PLL_C5:
        name =  "MAIN_PLL_C5";
        break;
    case ALT_CLK_MPU:
        name =  "MPU";
        break;
    case ALT_CLK_MPU_L2_RAM:
        name =  "MPU_L2_RAM";
        break;
    case ALT_CLK_MPU_PERIPH:
        name =  "MPU_PERIPH";
        break;
    case ALT_CLK_L3_MAIN:
        name =  "L3_MAIN";
        break;
    case ALT_CLK_L3_MP:
        name =  "L3_MP";
        break;
    case ALT_CLK_L3_SP:
        name =  "L3_SP";
        break;
    case ALT_CLK_L4_MAIN:
        name =  "L4_MAIN";
        break;
    case ALT_CLK_L4_MP:
        name =  "L4_MP";
        break;
    case ALT_CLK_L4_SP:
        name =  "L4_SP";
        break;
    case ALT_CLK_DBG_BASE:
        name =  "DBG_BASE";
        break;
    case ALT_CLK_DBG_AT:
        name =  "DBG_AT";
        break;
    case ALT_CLK_DBG_TRACE:
        name =  "DBG_TRACE";
        break;
    case ALT_CLK_DBG_TIMER:
        name =  "DBG_TIMER";
        break;
    case ALT_CLK_DBG:
        name =  "DBG";
        break;
    case ALT_CLK_MAIN_QSPI:
        name =  "MAIN_QSPI";
        break;
    case ALT_CLK_MAIN_NAND_SDMMC:
        name =  "MAIN_NAND_SDMMC";
        break;
    case ALT_CLK_CFG:
        name =  "CFG";
        break;
    case ALT_CLK_H2F_USER0:
        name =  "H2F_USER0";
        break;

        // Peripherals Clock Group - The following clocks are derived from the Peripheral PLL.
    case ALT_CLK_PERIPHERAL_PLL_C0:
        name =  "PERIPHERAL_PLL_C0";
        break;
    case ALT_CLK_PERIPHERAL_PLL_C1:
        name =  "PERIPHERAL_PLL_C1";
        break;
    case ALT_CLK_PERIPHERAL_PLL_C2:
        name =  "PERIPHERAL_PLL_C2";
        break;
    case ALT_CLK_PERIPHERAL_PLL_C3:
        name =  "PERIPHERAL_PLL_C3";
        break;
    case ALT_CLK_PERIPHERAL_PLL_C4:
        name =  "PERIPHERAL_PLL_C4";
        break;
    case ALT_CLK_PERIPHERAL_PLL_C5:
        name =  "PERIPHERAL_PLL_C5";
        break;
    case ALT_CLK_USB_MP:
        name =  "USB_MP";
        break;
    case ALT_CLK_SPI_M:
        name =  "SPI_M";
        break;
    case ALT_CLK_QSPI:
        name =  "QSPI";
        break;
    case ALT_CLK_NAND_X:
        name =  "NAND_X";
        break;
    case ALT_CLK_NAND:
        name =  "NAND";
        break;
    case ALT_CLK_SDMMC:
        name =  "SDMMC";
        break;
    case ALT_CLK_EMAC0:
        name =  "EMAC0";
        break;
    case ALT_CLK_EMAC1:
        name =  "EMAC1";
        break;
    case ALT_CLK_CAN0:
        name =  "CAN0";
        break;
    case ALT_CLK_CAN1:
        name =  "CAN1";
        break;
    case ALT_CLK_GPIO_DB:
        name =  "GPIO_DB";
        break;
    case ALT_CLK_H2F_USER1:
        name =  "H2F_USER1";
        break;

        // SDRAM Clock Group - The following clocks are derived from the SDRAM PLL.
    case ALT_CLK_SDRAM_PLL_C0:
        name =  "SDRAM_PLL_C0";
        break;
    case ALT_CLK_SDRAM_PLL_C1:
        name =  "SDRAM_PLL_C1";
        break;
    case ALT_CLK_SDRAM_PLL_C2:
        name =  "SDRAM_PLL_C2";
        break;
    case ALT_CLK_SDRAM_PLL_C3:
        name =  "SDRAM_PLL_C3";
        break;
    case ALT_CLK_SDRAM_PLL_C4:
        name =  "SDRAM_PLL_C4";
        break;
    case ALT_CLK_SDRAM_PLL_C5:
        name =  "SDRAM_PLL_C5";
        break;
    case ALT_CLK_DDR_DQS:
        name =  "DDR_DQS";
        break;
    case ALT_CLK_DDR_2X_DQS:
        name =  "DDR_2X_DQS";
        break;
    case ALT_CLK_DDR_DQ:
        name =  "DDR_DQ";
        break;
    case ALT_CLK_H2F_USER2:
        name =  "H2F_USER2";
        break;

        // Clock Output Pins
    case ALT_CLK_OUT_PIN_EMAC0_TX:
        name =  "OUT_PIN_EMAC0_TX";
        break;
    case ALT_CLK_OUT_PIN_EMAC1_TX:
        name =  "OUT_PIN_EMAC1_TX";
        break;
    case ALT_CLK_OUT_PIN_SDMMC:
        name =  "OUT_PIN_SDMMC";
        break;
    case ALT_CLK_OUT_PIN_I2C0_SCL:
        name =  "OUT_PIN_I2C0_SCL";
        break;
    case ALT_CLK_OUT_PIN_I2C1_SCL:
        name =  "OUT_PIN_I2C1_SCL";
        break;
    case ALT_CLK_OUT_PIN_I2C2_SCL:
        name =  "OUT_PIN_I2C2_SCL";
        break;
    case ALT_CLK_OUT_PIN_I2C3_SCL:
        name =  "OUT_PIN_I2C3_SCL";
        break;
    case ALT_CLK_OUT_PIN_SPIM0:
        name =  "OUT_PIN_SPIM0";
        break;
    case ALT_CLK_OUT_PIN_SPIM1:
        name =  "OUT_PIN_SPIM1";
        break;
    case ALT_CLK_OUT_PIN_QSPI:
        name =  "OUT_PIN_QSPI";
        break;
    case ALT_CLK_UNKNOWN:
        name =  "UNKNOWN";
        break;

        // do *not* put a 'default' statement here. Then the compiler will throw
        // an error if another clock id enum is added if the corresponding
        // string is not added to this function.
    }

    if (name != NULL)
    {
        snprintf(output, size, "ALT_CLK_%s", name);
        return ALT_E_SUCCESS;
    }
    else
    {
        return ALT_E_BAD_ARG;
    }
}


//
// alt_clk_pll_cntr_maxfreq_recalc() recalculate the maxmum frequency of the specified clock.
//
ALT_STATUS_CODE alt_clk_pll_cntr_maxfreq_recalc(ALT_CLK_t clk, ALT_PLL_CNTR_FREQMAX_t * maxfreq)
{
    ALT_STATUS_CODE ret = ALT_E_BAD_ARG;
	alt_freq_t freq;

	ret = alt_clk_freq_get(clk, &freq);

	if (ret == ALT_E_SUCCESS)
    {

        switch (clk)
        {
            // Main Clock Group
        case ALT_CLK_MAIN_PLL_C0:
            maxfreq->MainPLL_C0 = freq;
			printf("alt_pll_cntr_maxfreq.MainPLL_C0   = %10d\n", (unsigned int)freq);
            break;
        case ALT_CLK_MAIN_PLL_C1:
            maxfreq->MainPLL_C1 = freq;
			printf("alt_pll_cntr_maxfreq.MainPLL_C1   = %10d\n", (unsigned int)freq);
            break;
        case ALT_CLK_MAIN_PLL_C2:
            maxfreq->MainPLL_C2 = freq;
			printf("alt_pll_cntr_maxfreq.MainPLL_C2   = %10d\n", (unsigned int)freq);
            break;
        case ALT_CLK_MAIN_PLL_C3:
            maxfreq->MainPLL_C3 = freq;
			printf("alt_pll_cntr_maxfreq.MainPLL_C3   = %10d\n", (unsigned int)freq);
            break;
        case ALT_CLK_MAIN_PLL_C4:
            maxfreq->MainPLL_C4 = freq;
			printf("alt_pll_cntr_maxfreq.MainPLL_C4   = %10d\n", (unsigned int)freq);
            break;
        case ALT_CLK_MAIN_PLL_C5:
            maxfreq->MainPLL_C5 = freq;
			printf("alt_pll_cntr_maxfreq.MainPLL_C5   = %10d\n", (unsigned int)freq);
            break;

            // Peripheral Clock Group
        case ALT_CLK_PERIPHERAL_PLL_C0:
            maxfreq->PeriphPLL_C0 = freq;
			printf("alt_pll_cntr_maxfreq.PeriphPLL_C0 = %10d\n", (unsigned int)freq);
            break;
        case ALT_CLK_PERIPHERAL_PLL_C1:
            maxfreq->PeriphPLL_C1 = freq;
			printf("alt_pll_cntr_maxfreq.PeriphPLL_C1 = %10d\n", (unsigned int)freq);
            break;
        case ALT_CLK_PERIPHERAL_PLL_C2:
            maxfreq->PeriphPLL_C2 = freq;
			printf("alt_pll_cntr_maxfreq.PeriphPLL_C2 = %10d\n", (unsigned int)freq);
            break;
        case ALT_CLK_PERIPHERAL_PLL_C3:
            maxfreq->PeriphPLL_C3 = freq;
			printf("alt_pll_cntr_maxfreq.PeriphPLL_C3 = %10d\n", (unsigned int)freq);
            break;
        case ALT_CLK_PERIPHERAL_PLL_C4:
            maxfreq->PeriphPLL_C4 = freq;
			printf("alt_pll_cntr_maxfreq.PeriphPLL_C4 = %10d\n", (unsigned int)freq);
            break;
        case ALT_CLK_PERIPHERAL_PLL_C5:
            maxfreq->PeriphPLL_C5 = freq;
			printf("alt_pll_cntr_maxfreq.PeriphPLL_C5 = %10d\n", (unsigned int)freq);
            break;

            // SDRAM Clock Group
        case ALT_CLK_SDRAM_PLL_C0:
            maxfreq->SDRAMPLL_C0 = freq;
			printf("alt_pll_cntr_maxfreq.SDRAMPLL_C0  = %10d\n", (unsigned int)freq);
            break;
        case ALT_CLK_SDRAM_PLL_C1:
            maxfreq->SDRAMPLL_C1 = freq;
			printf("alt_pll_cntr_maxfreq.SDRAMPLL_C1  = %10d\n", (unsigned int)freq);
            break;
        case ALT_CLK_SDRAM_PLL_C2:
            maxfreq->SDRAMPLL_C2 = freq;
			printf("alt_pll_cntr_maxfreq.SDRAMPLL_C2  = %10d\n", (unsigned int)freq);
            break;
        case ALT_CLK_SDRAM_PLL_C5:
            maxfreq->SDRAMPLL_C5 = freq;
			printf("alt_pll_cntr_maxfreq.SDRAMPLL_C5  = %10d\n", (unsigned int)freq);
            break;
        default:
            ret = ALT_E_BAD_ARG;
			printf("bad max frequency parameter\n");
            break;
    	}   // end of switch-case construct
    }

    return ret;
}

//
//  u-boot preloader actually initialize clock manager circuitry
//
//  alt_clk_clkmgr_init() attempt to fix the pll counter max frequencies, since
//  thses frequencies are not known in advance until u-boot programmed clock manager.
//
ALT_STATUS_CODE alt_clk_clkmgr_init(void)
{
    ALT_STATUS_CODE ret = ALT_E_SUCCESS;
    ALT_STATUS_CODE status ;

	status = alt_clk_pll_cntr_maxfreq_recalc(ALT_CLK_MAIN_PLL_C0,&alt_pll_cntr_maxfreq );
	if (status != ALT_E_SUCCESS) ret = ALT_E_ERROR;

	status = alt_clk_pll_cntr_maxfreq_recalc(ALT_CLK_MAIN_PLL_C1,&alt_pll_cntr_maxfreq );
	if (status != ALT_E_SUCCESS) ret = ALT_E_ERROR;

	status = alt_clk_pll_cntr_maxfreq_recalc(ALT_CLK_MAIN_PLL_C2,&alt_pll_cntr_maxfreq );
	if (status != ALT_E_SUCCESS) ret = ALT_E_ERROR;

	status = alt_clk_pll_cntr_maxfreq_recalc(ALT_CLK_MAIN_PLL_C3,&alt_pll_cntr_maxfreq );
	if (status != ALT_E_SUCCESS) ret = ALT_E_ERROR;

	status = alt_clk_pll_cntr_maxfreq_recalc(ALT_CLK_MAIN_PLL_C4,&alt_pll_cntr_maxfreq );
	if (status != ALT_E_SUCCESS) ret = ALT_E_ERROR;

	status = alt_clk_pll_cntr_maxfreq_recalc(ALT_CLK_MAIN_PLL_C5,&alt_pll_cntr_maxfreq );
	if (status != ALT_E_SUCCESS) ret = ALT_E_ERROR;

	status = alt_clk_pll_cntr_maxfreq_recalc(ALT_CLK_PERIPHERAL_PLL_C0,&alt_pll_cntr_maxfreq );
	if (status != ALT_E_SUCCESS) ret = ALT_E_ERROR;

	status = alt_clk_pll_cntr_maxfreq_recalc(ALT_CLK_PERIPHERAL_PLL_C1,&alt_pll_cntr_maxfreq );
	if (status != ALT_E_SUCCESS) ret = ALT_E_ERROR;

	status = alt_clk_pll_cntr_maxfreq_recalc(ALT_CLK_PERIPHERAL_PLL_C2,&alt_pll_cntr_maxfreq );
	if (status != ALT_E_SUCCESS) ret = ALT_E_ERROR;

	status = alt_clk_pll_cntr_maxfreq_recalc(ALT_CLK_PERIPHERAL_PLL_C3,&alt_pll_cntr_maxfreq );
	if (status != ALT_E_SUCCESS) ret = ALT_E_ERROR;

	status = alt_clk_pll_cntr_maxfreq_recalc(ALT_CLK_PERIPHERAL_PLL_C4,&alt_pll_cntr_maxfreq );
	if (status != ALT_E_SUCCESS) ret = ALT_E_ERROR;

	status = alt_clk_pll_cntr_maxfreq_recalc(ALT_CLK_PERIPHERAL_PLL_C5,&alt_pll_cntr_maxfreq );
	if (status != ALT_E_SUCCESS) ret = ALT_E_ERROR;


	status = alt_clk_pll_cntr_maxfreq_recalc(ALT_CLK_SDRAM_PLL_C0,&alt_pll_cntr_maxfreq );
	if (status != ALT_E_SUCCESS) ret = ALT_E_ERROR;

	status = alt_clk_pll_cntr_maxfreq_recalc(ALT_CLK_SDRAM_PLL_C1,&alt_pll_cntr_maxfreq );
	if (status != ALT_E_SUCCESS) ret = ALT_E_ERROR;

	status = alt_clk_pll_cntr_maxfreq_recalc(ALT_CLK_SDRAM_PLL_C2,&alt_pll_cntr_maxfreq );
	if (status != ALT_E_SUCCESS) ret = ALT_E_ERROR;

	status = alt_clk_pll_cntr_maxfreq_recalc(ALT_CLK_SDRAM_PLL_C5,&alt_pll_cntr_maxfreq );
	if (status != ALT_E_SUCCESS) ret = ALT_E_ERROR;


	return ret;
}

