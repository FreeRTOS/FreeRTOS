/** @file sys_vim.h
*   @brief Vectored Interrupt Module Header File
*   @date 05.November.2010
*   @version 1.01.000
*   
*   This file contains:
*   - VIM Type Definitions
*   - VIM General Definitions
*   .
*   which are relevant for the Vectored Interrupt Controller.
*/

/* (c) Texas Instruments 2010, All rights reserved. */

#ifndef __SYS_VIM_H__
#define __SYS_VIM_H__

/* USER CODE BEGIN (0) */
/* USER CODE END */


/* VIM Type Definitions */

/** @typedef t_isrFuncPTR
*   @brief ISR Function Pointer Type Definition
*
*   This type is used to access the ISR handler.
*/
typedef void (*t_isrFuncPTR)();

/* USER CODE BEGIN (1) */
/* USER CODE END */


/* VIM General Configuration */

#define VIM_CHANNELS 96U

/* USER CODE BEGIN (2) */
/* USER CODE END */

/* Interrupt Handlers */

extern void phantomInterrupt(void);
extern void esmHighLevelInterrupt(void);
extern void vPortPreemptiveTick(void);
extern void vPortNonPreemptiveTick(void);
extern void vPortYeildWithinAPI(void);


/* Vim Register Frame Definition */
/** @struct vimBase
*   @brief Vim Register Frame Definition
*
*   This type is used to access the Vim Registers.
*/
/** @typedef vimBASE_t
*   @brief VIM Register Frame Type Definition
*
*   This type is used to access the VIM Registers.
*/
typedef volatile struct vimBase
{
    unsigned              : 24U;    /* 0x0000        */
    unsigned      IRQIVEC :  8U;    /* 0x0000        */
    unsigned              : 24U;    /* 0x0004        */
    unsigned      FIQIVEC :  8U;    /* 0x0004        */
    unsigned      : 32U;            /* 0x0008        */
    unsigned      : 32U;            /* 0x000C        */
    unsigned      FIRQPR0;          /* 0x0010        */
    unsigned      FIRQPR1;          /* 0x0014        */
    unsigned      FIRQPR2;          /* 0x0018        */
    unsigned      FIRQPR3;          /* 0x001C        */
    unsigned      INTREQ0;          /* 0x0020        */
    unsigned      INTREQ1;          /* 0x0024        */
    unsigned      INTREQ2;          /* 0x0028        */
    unsigned      INTREQ3;          /* 0x002C        */
    unsigned      REQMASKSET0;      /* 0x0030        */
    unsigned      REQMASKSET1;      /* 0x0034        */
    unsigned      REQMASKSET2;      /* 0x0038        */
    unsigned      REQMASKSET3;      /* 0x003C        */
    unsigned      REQMASKCLR0;      /* 0x0040        */
    unsigned      REQMASKCLR1;      /* 0x0044        */
    unsigned      REQMASKCLR2;      /* 0x0048        */
    unsigned      REQMASKCLR3;      /* 0x004C        */
    unsigned      WAKEMASKSET0;     /* 0x0050        */
    unsigned      WAKEMASKSET1;     /* 0x0054        */
    unsigned      WAKEMASKSET2;     /* 0x0058        */
    unsigned      WAKEMASKSET3;     /* 0x005C        */
    unsigned      WAKEMASKCLR0;     /* 0x0060        */
    unsigned      WAKEMASKCLR1;     /* 0x0064        */
    unsigned      WAKEMASKCLR2;     /* 0x0068        */
    unsigned      WAKEMASKCLR3;     /* 0x006C        */
    unsigned      IRQVECREG;        /* 0x0070        */
    unsigned      FIQVECREQ;        /* 0x0074        */
    unsigned                 :  9U; /* 0x0078        */
    unsigned      CAPEVTSRC1 :  7U; /* 0x0078        */
    unsigned                 :  9U; /* 0x0078        */
    unsigned      CAPEVTSRC0 :  7U; /* 0x0078        */
    unsigned      : 32U;            /* 0x007C        */
    unsigned char CHANMAP[64U];     /* 0x0080-0x017C */
} vimBASE_t;

#define vimREG ((vimBASE_t *)0xFFFFFE00U)

/* USER CODE BEGIN (3) */
/* USER CODE END */


#endif
