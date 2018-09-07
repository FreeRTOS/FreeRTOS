/** @file system.h
*   @brief System Driver Header File
*   @date 23.July.2009
*   @version 1.01.001
*   
*   This file contains:
*   - Definitions
*   - Types
*   .
*   which are relevant for the System driver.
*/

/* (c) Texas Instruments 2009-2010, All rights reserved. */

#ifndef __SYS_SYSTEM_H__
#define __SYS_SYSTEM_H__


/* System General Definitions */

/** @enum systemInterrupt
*   @brief Alias names for clock sources
*
*   This enumeration is used to provide alias names for the clock sources:
*     - IRQ
*     - FIQ
*/
enum systemInterrupt
{
    SYS_IRQ, /**< Alias for IRQ interrupt */
    SYS_FIQ  /**< Alias for FIQ interrupt */
};

/** @enum systemClockSource
*   @brief Alias names for clock sources
*
*   This enumeration is used to provide alias names for the clock sources:
*     - Oscillator
*     - Pll
*     - 32 kHz Oscillator
*     - External1
*     - Low Power Oscillator Low
*     - Low Power Oscillator High
*     - Flexray Pll
*     - External2
*     - Synchronous VCLK1
*/
enum systemClockSource
{
    SYS_OSC       = 0, /**< Alias for oscillator clock Source                */
    SYS_PLL       = 1, /**< Alias for Pll clock Source                       */
    SYS_O32       = 2, /**< Alias for 32 kHz oscillator clock Source         */
    SYS_EXTERNAL  = 3, /**< Alias for external clock Source                  */
    SYS_LPO_LOW   = 4, /**< Alias for low power oscillator low clock Source  */
    SYS_LPO_HIGH  = 5, /**< Alias for low power oscillator high clock Source */
    SYS_FR_PLL    = 6, /**< Alias for flexray pll clock Source               */
    SYS_EXTERNAL2 = 7, /**< Alias for external 2 clock Source                */
    SYS_VCLK      = 9  /**< Alias for synchronous VCLK1 clock Source         */
};

#define SYS_DOZE_MODE   0x000F3F02U
#define SYS_SNOOZE_MODE 0x000F3F03U
#define SYS_SLEEP_MODE  0x000FFFFFU


/** @def SYS_PRE1
*   @brief Alias name for RTI1CLK PRE clock source
*
*   This is an alias name for the RTI1CLK pre clock source.
*   This can be either:
*     - Oscillator
*     - Pll
*     - 32 kHz Oscillator
*     - External
*     - Low Power Oscillator Low
*     - Low Power Oscillator High
*     - Flexray Pll
*/
#define SYS_PRE1 SYS_PLL

/** @def SYS_PRE2
*   @brief Alias name for RTI2CLK pre clock source
*
*   This is an alias name for the RTI2CLK pre clock source.
*   This can be either:
*     - Oscillator
*     - Pll
*     - 32 kHz Oscillator
*     - External
*     - Low Power Oscillator Low
*     - Low Power Oscillator High
*     - Flexray Pll
*/
#define SYS_PRE2 SYS_PLL


/* System Register Frame 1 Definition */
/** @struct systemBase1
*   @brief System Register Frame 1 Definition
*
*   This type is used to access the System 1 Registers.
*/
/** @typedef systemBASE1_t
*   @brief System Register Frame 1 Type Definition
*
*   This type is used to access the System 1 Registers.
*/
typedef volatile struct systemBase1
{
    unsigned SYSPC1;                 /* 0x0000 */
    unsigned SYSPC2;                 /* 0x0004 */
    unsigned SYSPC3;                 /* 0x0008 */
    unsigned SYSPC4;                 /* 0x000C */
    unsigned SYSPC5;                 /* 0x0010 */
    unsigned SYSPC6;                 /* 0x0014 */
    unsigned SYSPC7;                 /* 0x0018 */
    unsigned SYSPC8;                 /* 0x001C */
    unsigned SYSPC9;                 /* 0x0020 */
    unsigned SSWPLL1;                /* 0x0024 */
    unsigned SSWPLL2;                /* 0x0028 */
    unsigned SSWPLL3;                /* 0x002C */
    unsigned CSDIS;                  /* 0x0030 */
    unsigned CSDISSET;               /* 0x0034 */
    unsigned CSDISCLR;               /* 0x0038 */
    unsigned CSDDIS;                 /* 0x003C */
    unsigned CSDDISSET;              /* 0x0040 */
    unsigned CSDDISCLR;              /* 0x0044 */
    unsigned GHVSRC;                 /* 0x0048 */
    unsigned VCLKASRC;               /* 0x004C */
    unsigned RCLKSRC;                /* 0x0050 */
    unsigned CSVSTAT;                /* 0x0054 */
    unsigned MSTGCR;                 /* 0x0058 */
    unsigned MINITGCR;               /* 0x005C */
    unsigned MSINENA;                /* 0x0060 */
    unsigned MSTFAIL;                /* 0x0064 */
    unsigned MSTCGSTAT;              /* 0x0068 */
    unsigned MINISTAT;               /* 0x006C */
    unsigned PLLCTL1;                /* 0x0070 */
    unsigned PLLCTL2;                /* 0x0074 */
    unsigned UERFLAG;                /* 0x0078 */
    unsigned DIEIDL;                 /* 0x007C */
    unsigned DIEIDH;                 /* 0x0080 */
    unsigned VRCTL;                  /* 0x0084 */
    unsigned LPOMONCTL;              /* 0x0088 */
    unsigned CLKTEST;                /* 0x008C */
    unsigned DFTCTRLREG1;            /* 0x0090 */
    unsigned DFTCTRLREG2;            /* 0x0094 */
    unsigned : 32U;                  /* 0x0098 */
    unsigned : 32U;                  /* 0x009C */
    unsigned GPREG1;                 /* 0x00A0 */
    unsigned BTRMSEL;                /* 0x00A4 */
    unsigned IMPFASTS;               /* 0x00A8 */
    unsigned IMPFTADD;               /* 0x00AC */
    unsigned SSISR1;                 /* 0x00B0 */
    unsigned SSISR2;                 /* 0x00B4 */
    unsigned SSISR3;                 /* 0x00B8 */
    unsigned SSISR4;                 /* 0x00BC */
    unsigned RAMGCR;                 /* 0x00C0 */
    unsigned BMMCR1;                 /* 0x00C4 */
    unsigned BMMCR2;                 /* 0x00C8 */
    unsigned MMUGCR;                 /* 0x00CC */
#ifdef __little_endian__
    unsigned        : 8U;            /* 0x00D0 */
    unsigned PENA   : 1U;            /* 0x00D0 */
    unsigned        : 7U;            /* 0x00D0 */
    unsigned VCLKR  : 4U;            /* 0x00D0 */
    unsigned        : 4U;            /* 0x00D0 */
    unsigned VCLK2R : 4U;            /* 0x00D0 */
    unsigned        : 4U;            /* 0x00D0 */
#else
    unsigned        : 4U;            /* 0x00D0 */
    unsigned VCLK2R : 4U;            /* 0x00D0 */
    unsigned        : 4U;            /* 0x00D0 */
    unsigned VCLKR  : 4U;            /* 0x00D0 */
    unsigned        : 7U;            /* 0x00D0 */
    unsigned PENA   : 1U;            /* 0x00D0 */
    unsigned        : 8U;            /* 0x00D0 */
#endif
    unsigned ECPCNTL;                /* 0x00D4 */
    unsigned DSPGCR;                 /* 0x00D8 */
    unsigned DEVCR1;                 /* 0x00DC */
    unsigned SYSECR;                 /* 0x00E0 */
    unsigned SYSESR;                 /* 0x00E4 */
    unsigned ITIFLAG;                /* 0x00E8 */
    unsigned GBLSTAT;                /* 0x00EC */
    unsigned DEV;                    /* 0x00F0 */
    unsigned SSIVEC;                 /* 0x00F4 */
    unsigned SSIF;                   /* 0x00F8 */
} systemBASE1_t;


/** @def systemREG1
*   @brief System Register Frame 1 Pointer
*
*   This pointer is used by the system driver to access the system frame 1 registers.
*/
#define systemREG1 ((systemBASE1_t *)0xFFFFFF00U)

/** @def systemPORT
*   @brief ECLK GIO Port Register Pointer
*
*   Pointer used by the GIO driver to access I/O PORT of System/Eclk
*   (use the GIO drivers to access the port pins).
*/
#define systemPORT ((gioPORT_t *)0xFFFFFF04U)


/* System Register Frame 2 Definition */
/** @struct systemBase2
*   @brief System Register Frame 2 Definition
*
*   This type is used to access the System 2 Registers.
*/
/** @typedef systemBASE2_t
*   @brief System Register Frame 2 Type Definition
*
*   This type is used to access the System 2 Registers.
*/
typedef volatile struct systemBase2
{
    unsigned PLLCTL3;        /* 0x0000 */
    unsigned : 32U;          /* 0x0004 */
    unsigned STCCLKDIV;      /* 0x0008 */
    unsigned CLKHB_GLBREG;   /* 0x000C */
    unsigned CLKHB_RTIDREG;  /* 0x0010 */
    unsigned HBCD_STAT;      /* 0x0014 */
    unsigned : 32U;          /* 0x0018 */
    unsigned : 32U;          /* 0x001C */
    unsigned CLKTRMI1;       /* 0x0020 */
    unsigned ECPCNTRL0;      /* 0x0024 */
    unsigned ECPCNTRL1;      /* 0x0028 */
    unsigned ECPCNTRL2;      /* 0x002C */
    unsigned ECPCNTRL3;      /* 0x0030 */
    unsigned : 32U;          /* 0x0034 */
    unsigned : 32U;          /* 0x0038 */
    unsigned CLK2CNTRL;      /* 0x003C */
    unsigned VCLKACON1;      /* 0x0040 */
} systemBASE2_t;


/** @def systemREG2
*   @brief System Register Frame 2 Pointer
*
*   This pointer is used by the system driver to access the system frame 2 registers.
*/
#define systemREG2 ((systemBASE2_t *)0xFFFFE100U)


/** @struct pcrBase
*   @brief Pcr Register Frame Definition
*
*   This type is used to access the Pcr Registers.
*/
/** @typedef pcrBASE_t
*   @brief PCR Register Frame Type Definition
*
*   This type is used to access the PCR Registers.
*/
typedef volatile struct pcrBase
{
    unsigned PMPROTSET0;    /* 0x0000 */
    unsigned PMPROTSET1;    /* 0x0004 */
    unsigned : 32U;         /* 0x0008 */
    unsigned : 32U;         /* 0x000C */
    unsigned PMPROTCLR0;    /* 0x0010 */
    unsigned PMPROTCLR1;    /* 0x0014 */
    unsigned : 32U;         /* 0x0018 */
    unsigned : 32U;         /* 0x001C */
    unsigned PPROTSET0;     /* 0x0020 */
    unsigned PPROTSET1;     /* 0x0024 */
    unsigned PPROTSET2;     /* 0x0028 */
    unsigned PPROTSET3;     /* 0x002C */
    unsigned : 32U;         /* 0x0030 */
    unsigned : 32U;         /* 0x0034 */
    unsigned : 32U;         /* 0x0038 */
    unsigned : 32U;         /* 0x003C */
    unsigned PPROTCLR0;     /* 0x0040 */
    unsigned PPROTCLR1;     /* 0x0044 */
    unsigned PPROTCLR2;     /* 0x0048 */
    unsigned PPROTCLR3;     /* 0x004C */
    unsigned : 32U;         /* 0x0050 */
    unsigned : 32U;         /* 0x0054 */
    unsigned : 32U;         /* 0x0058 */
    unsigned : 32U;         /* 0x005C */
    unsigned PCSPWRDWNSET0; /* 0x0060 */
    unsigned PCSPWRDWNSET1; /* 0x0064 */
    unsigned : 32U;         /* 0x0068 */
    unsigned : 32U;         /* 0x006C */
    unsigned PCSPWRDWNCLR0; /* 0x0070 */
    unsigned PCSPWRDWNCLR1; /* 0x0074 */
    unsigned : 32U;         /* 0x0078 */
    unsigned : 32U;         /* 0x007C */
    unsigned PSPWRDWNSET0;  /* 0x0080 */
    unsigned PSPWRDWNSET1;  /* 0x0084 */
    unsigned PSPWRDWNSET2;  /* 0x0088 */
    unsigned PSPWRDWNSET3;  /* 0x008C */
    unsigned : 32U;         /* 0x0090 */
    unsigned : 32U;         /* 0x0094 */
    unsigned : 32U;         /* 0x0098 */
    unsigned : 32U;         /* 0x009C */
    unsigned PSPWRDWNCLR0;  /* 0x00A0 */
    unsigned PSPWRDWNCLR1;  /* 0x00A4 */
    unsigned PSPWRDWNCLR2;  /* 0x00A8 */
    unsigned PSPWRDWNCLR3;  /* 0x00AC */
} pcrBASE_t;

/** @def pcrREG
*   @brief Pcr Register Frame Pointer
*
*   This pointer is used by the system driver to access the Pcr registers.
*/
#define pcrREG ((pcrBASE_t *)0xFFFFE000U)

/* FlashW General Definitions */


/** @enum flashWPowerModes
*   @brief Alias names for flash bank power modes
*
*   This enumeration is used to provide alias names for the flash bank power modes:
*     - sleep
*     - standby
*     - active
*/
enum flashWPowerModes
{
    SYS_SLEEP   = 0U, /**< Alias for flash bank power mode sleep   */
    SYS_STANDBY = 1U, /**< Alias for flash bank power mode standby */
    SYS_ACTIVE  = 3U  /**< Alias for flash bank power mode active  */
};


/** @struct flashWBase
*   @brief Flash Wrapper Register Frame Definition
*
*   This type is used to access the Flash Wrapper Registers.
*/
/** @typedef flashWBASE_t
*   @brief Flash Wrapper Register Frame Type Definition
*
*   This type is used to access the Flash Wrapper Registers.
*/
typedef volatile struct flashWBase
{
    unsigned FRDCNTL;     /* 0x0000 */
    unsigned FSPRD;       /* 0x0004 */
    unsigned FEDACCTRL1;  /* 0x0008 */
    unsigned FEDACCTRL2;  /* 0x000C */
    unsigned FCORERRCNT;  /* 0x0010 */
    unsigned FCORERRADD;  /* 0x0014 */
    unsigned FCORERRPOS;  /* 0x0018 */
    unsigned FEDACSTATUS; /* 0x001C */
    unsigned FUNCERRADD;  /* 0x0020 */
    unsigned FEDACSDIS;   /* 0x0024 */
    unsigned FPRIMADDTAG; /* 0x0028 */
    unsigned FREDUADDTAG; /* 0x002C */
    unsigned FBPROT;      /* 0x0030 */
    unsigned FBSE;        /* 0x0034 */
    unsigned FBBUSY;      /* 0x0038 */
    unsigned FBAC;        /* 0x003C */
    unsigned FBFALLBACK;  /* 0x0040 */
    unsigned FBPRDY;      /* 0x0044 */
    unsigned FPAC1;       /* 0x0048 */
    unsigned FPAC2;       /* 0x004C */
    unsigned FMAC;        /* 0x0050 */
    unsigned FMSTAT;      /* 0x0054 */
    unsigned FEMUDMSW;    /* 0x0058 */
    unsigned FEMUDLSW;    /* 0x005C */
    unsigned FEMUECC;     /* 0x0060 */
    unsigned FLOCK;       /* 0x0064 */
    unsigned FEMUADDR;    /* 0x0068 */
    unsigned FDIAGCTRL;   /* 0x006C */
    unsigned FRAWDATAH;   /* 0x0070 */
    unsigned FRAWDATAL;   /* 0x0074 */
    unsigned FRAWECC;     /* 0x0078 */
    unsigned FPAROVR;     /* 0x007C */
    unsigned FVREADCT;    /* 0x0080 */
    unsigned FVHVCT1;     /* 0x0084 */
    unsigned FVHVCT2;     /* 0x0088 */
    unsigned FVNVCT;      /* 0x008C */
    unsigned FVPPCT;      /* 0x0090 */
    unsigned FVWLCT;      /* 0x0094 */
    unsigned FEFUSE;      /* 0x0098 */
    unsigned : 32U;       /* 0x009C */
    unsigned : 32U;       /* 0x00A0 */
    unsigned : 32U;       /* 0x00A4 */
    unsigned : 32U;       /* 0x00A8 */
    unsigned : 32U;       /* 0x00AC */
    unsigned : 32U;       /* 0x00B0 */
    unsigned : 32U;       /* 0x00B4 */
    unsigned : 32U;       /* 0x00B8 */
    unsigned : 32U;       /* 0x00BC */
    unsigned FEDACSDIS2;  /* 0x00C0 */
    unsigned : 32U;       /* 0x00C4 */
    unsigned : 32U;       /* 0x00C8 */
    unsigned : 32U;       /* 0x00CC */
    unsigned : 32U;       /* 0x00D0 */
    unsigned : 32U;       /* 0x00D4 */
    unsigned : 32U;       /* 0x00D8 */
    unsigned : 32U;       /* 0x00DC */
    unsigned : 32U;       /* 0x00E0 */
    unsigned : 32U;       /* 0x00E4 */
    unsigned : 32U;       /* 0x00E8 */
    unsigned : 32U;       /* 0x00EC */
    unsigned : 32U;       /* 0x00F0 */
    unsigned : 32U;       /* 0x00F4 */
    unsigned : 32U;       /* 0x00F8 */
    unsigned : 32U;       /* 0x00FC */
    unsigned FBSTROBES;   /* 0x0100 */
    unsigned FPSTROBES;   /* 0x0104 */
    unsigned FBMODE;      /* 0x0108 */
    unsigned FTCR;        /* 0x010C */
    unsigned FADDR;       /* 0x0110 */
    unsigned FWRITE;      /* 0x0114 */
    unsigned FCBITSEL;    /* 0x0118 */
    unsigned FTCTRL;      /* 0x011C */
    unsigned FWPWRITE0;   /* 0x0120 */
    unsigned FWPWRITE1;   /* 0x0124 */
    unsigned FWPWRITE2;   /* 0x0128 */
    unsigned FWPWRITE3;   /* 0x012C */
    unsigned FWPWRITE4;   /* 0x0130 */
} flashWBASE_t;

/** @def flashWREG
*   @brief Flash Wrapper Register Frame Pointer
*
*   This pointer is used by the system driver to access the flash wrapper registers.
*/
#define flashWREG ((flashWBASE_t *)(0xFFF87000U))

/* System Interface Functions */
void systemInit(void);

#endif
