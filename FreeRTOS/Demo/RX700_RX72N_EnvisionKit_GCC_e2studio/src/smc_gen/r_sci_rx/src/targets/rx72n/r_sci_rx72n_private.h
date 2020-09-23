/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products. No 
* other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all 
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, 
* FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED. TO THE MAXIMUM 
* EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES 
* SHALL BE LIABLE FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS 
* SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability of 
* this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer 
*
* Copyright (C) 2019 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : r_sci_rx72n_private.h
* Description  : Functions for using SCI on the RX72N device.
************************************************************************************************************************
* History : DD.MM.YYYY Version Description
*           30.12.2019 1.00    Initial Release.
***********************************************************************************************************************/

#ifndef SCI_RX72N_H
#define SCI_RX72N_H

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include "../../r_sci_rx_private.h"

#if (SCI_CFG_ASYNC_INCLUDED)
#include "r_byteq_if.h"
#endif

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/

/* Mask of all active channels */
#define SCI_CFG_CH_INCLUDED_MASK ((SCI_CFG_CH0_INCLUDED << 0)   |   \
                                  (SCI_CFG_CH1_INCLUDED << 1)   |   \
                                  (SCI_CFG_CH2_INCLUDED << 2)   |   \
                                  (SCI_CFG_CH3_INCLUDED << 3)   |   \
                                  (SCI_CFG_CH4_INCLUDED << 4)   |   \
                                  (SCI_CFG_CH5_INCLUDED << 5)   |   \
                                  (SCI_CFG_CH6_INCLUDED << 6)   |   \
                                  (SCI_CFG_CH7_INCLUDED << 7)   |   \
                                  (SCI_CFG_CH8_INCLUDED << 8)   |   \
                                  (SCI_CFG_CH9_INCLUDED << 9)   |   \
                                  (SCI_CFG_CH10_INCLUDED << 10) |   \
                                  (SCI_CFG_CH11_INCLUDED << 11) |   \
                                  (SCI_CFG_CH12_INCLUDED << 12))

/* SCI SCR register masks */
#define SCI_SCR_TEI_MASK    (0x80U)     /* transmit interrupt enable */
#define SCI_SCR_REI_MASK    (0x40U)     /* receive interrupt enable */
#define SCI_SCR_TE_MASK     (0x20U)     /* transmitter enable */
#define SCI_SCR_RE_MASK     (0x10U)     /* receiver enable */
#define SCI_EN_XCVR_MASK    (SCI_SCR_RE_MASK | SCI_SCR_TE_MASK | SCI_SCR_REI_MASK | SCI_SCR_TEI_MASK)

/* SCI SSR register receiver error masks */
#define SCI_SSR_ORER_MASK         (0x20U)     /* overflow error */
#define SCI_SSR_FER_MASK          (0x10U)     /* framing error */
#define SCI_SSR_PER_MASK          (0x08U)     /* parity err */
#define SCI_RCVR_ERR_MASK         (SCI_SSR_ORER_MASK | SCI_SSR_FER_MASK | SCI_SSR_PER_MASK)
#define SCI_SSR_CLR_MASK          (0xC0U)     /* SSR register cleare mask (11000000b) */
#if SCI_CFG_FIFO_INCLUDED
#define SCI_SSRFIFO_CLR_MASK      (0xC6U)     /* SSR register cleare mask (11000110b) */
#define SCI_SSRFIFO_TDFE_MASK     (0x80U)     /* SSR register transmit data empty flag mask (10000000b) */
#define SCI_SSRFIFO_RDF_MASK      (0x40U)     /* SSR register receive FIFO full flag mask (01000000b) */
#define SCI_SSRFIFO_DR_MASK       (0x01U)     /* SSR register receive DR flag mask (00000001b) */
#endif

/* Macros to enable and disable ICU interrupts */
#define ENABLE_RXI_INT      (*hdl->rom->icu_rxi |= hdl->rom->rxi_en_mask)
#define DISABLE_RXI_INT     (*hdl->rom->icu_rxi &= (uint8_t)~hdl->rom->rxi_en_mask)
#define ENABLE_TXI_INT      (*hdl->rom->icu_txi |= hdl->rom->txi_en_mask)
#define DISABLE_TXI_INT     (*hdl->rom->icu_txi &= (uint8_t)~hdl->rom->txi_en_mask)

#define ENABLE_ERI_INT      (*hdl->rom->icu_grp |= hdl->rom->eri_ch_mask)
#define DISABLE_ERI_INT     (*hdl->rom->icu_grp &= ~hdl->rom->eri_ch_mask)
#define ENABLE_TEI_INT      (*hdl->rom->icu_grp |= hdl->rom->tei_ch_mask)
#define DISABLE_TEI_INT     (*hdl->rom->icu_grp &= ~hdl->rom->tei_ch_mask)

#define NUM_DIVISORS_ASYNC  (9)
#define NUM_DIVISORS_SYNC   (4)

/*****************************************************************************
Typedef definitions
******************************************************************************/

/* ROM INFO */

typedef struct st_sci_ch_rom    /* SCI ROM info for channel control block */
{
    volatile  struct st_sci7 R_BSP_EVENACCESS_SFR   *regs;   /* base ptr to ch registers */
    volatile  uint32_t       R_BSP_EVENACCESS_SFR  *mstp;          /* ptr to mstp register */
    uint32_t                        stop_mask;          /* mstp mask to disable ch */
#if SCI_CFG_TEI_INCLUDED
    bsp_int_src_t                   tei_vector;
    bsp_int_cb_t                    tei_isr;
#endif
    bsp_int_src_t                   eri_vector;
    bsp_int_cb_t                    eri_isr;
    uint32_t                        tei_ch_mask;    /* ICU IR and IEN mask */
    uint32_t                        eri_ch_mask;    /* ICU IR and IEN mask */
    volatile  uint8_t R_BSP_EVENACCESS_SFR   *ipr_rxi;       /* ptr to IPR register */
    volatile  uint8_t R_BSP_EVENACCESS_SFR   *ipr_txi;       /* ptr to IPR register */
    volatile  uint8_t R_BSP_EVENACCESS_SFR   *ir_rxi;        /* ptr to RXI IR register */
    volatile  uint8_t R_BSP_EVENACCESS_SFR   *ir_txi;        /* ptr to TXI IR register */

    /* 
    * DO NOT use the enable/disable interrupt bits in the SCR 
    * register. Pending interrupts can be lost that way.
    */
    volatile  uint8_t R_BSP_EVENACCESS_SFR   *icu_rxi;       /* ptr to ICU register */
    volatile  uint8_t R_BSP_EVENACCESS_SFR   *icu_txi;
    volatile  uint32_t R_BSP_EVENACCESS_SFR  *icu_grp;
    uint8_t                         rxi_en_mask;    /* ICU enable/disable rxi mask */
    uint8_t                         txi_en_mask;    /* ICU enable/disable txi mask */
} sci_ch_rom_t;


/* CHANNEL CONTROL BLOCK */

typedef struct st_sci_ch_ctrl       /* SCI channel control (for handle) */
{
    sci_ch_rom_t const *rom;        /* pointer to rom info */
    sci_mode_t      mode;           /* operational mode */
    uint32_t        baud_rate;      /* baud rate */
    void          (*callback)(void *p_args); /* function ptr for rcvr errs */
    union
    {
#if (SCI_CFG_ASYNC_INCLUDED)
        byteq_hdl_t     que;        /* async transmit queue handle */
#endif
        uint8_t         *buf;       /* sspi/sync tx buffer ptr */
    } u_tx_data;
    union
    {
#if (SCI_CFG_ASYNC_INCLUDED)
        byteq_hdl_t     que;        /* async receive queue handle */
#endif
        uint8_t         *buf;       /* sspi/sync rx buffer ptr */
    } u_rx_data;
    bool            tx_idle;        /* TDR is empty (async); TSR is empty (sync/sspi) */
#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
    bool            save_rx_data;   /* save the data that is clocked in */
    uint16_t        tx_cnt;         /* number of bytes to transmit */
    uint16_t        rx_cnt;         /* number of bytes to receive */
    bool            tx_dummy;       /* transmit dummy byte, not buffer */
#endif
    uint32_t        pclk_speed;     /* saved peripheral clock speed for break generation */
#if SCI_CFG_FIFO_INCLUDED
    uint8_t         fifo_ctrl;      /* fifo ctrl (enable/disable) flag */
    uint8_t         rx_dflt_thresh; /* RX FIFO threshold(default) */
    uint8_t         rx_curr_thresh; /* RX FIFO threshold(current) */
    uint8_t         tx_dflt_thresh; /* TX FIFO threshold(default) */
    uint8_t         tx_curr_thresh; /* TX FIFO threshold(current) */
#endif
} sci_ch_ctrl_t;


/* BAUD DIVISOR INFO */

/* BRR = (PCLK/(divisor * baud)) - 1 */
/* when abcs=1, divisor = 32*pow(2,2n-1) */
/* when abcs=0, divisor = 64*pow(2,2n-1) */

typedef struct st_baud_divisor
{
    int16_t     divisor;    // clock divisor
    uint8_t     abcs;       // abcs value to get divisor
    uint8_t     bgdm;       // bdgm value to get divisor
    uint8_t     cks;        // cks  value to get divisor (cks = n)
} baud_divisor_t;



/*****************************************************************************
Exported global variables and functions
******************************************************************************/
extern const sci_hdl_t g_sci_handles[];

#if (SCI_CFG_ASYNC_INCLUDED)
extern const baud_divisor_t async_baud[];
#endif
#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
extern const baud_divisor_t sync_baud[];
#endif

#if (SCI_CFG_CH0_INCLUDED)
extern const sci_ch_rom_t      ch0_rom;
extern sci_ch_ctrl_t           ch0_ctrl;
#endif

#if (SCI_CFG_CH1_INCLUDED)
extern const sci_ch_rom_t      ch1_rom;
extern sci_ch_ctrl_t           ch1_ctrl;
#endif

#if (SCI_CFG_CH2_INCLUDED)
extern const sci_ch_rom_t      ch2_rom;
extern sci_ch_ctrl_t           ch2_ctrl;
#endif

#if (SCI_CFG_CH3_INCLUDED)
extern const sci_ch_rom_t      ch3_rom;
extern sci_ch_ctrl_t           ch3_ctrl;
#endif

#if (SCI_CFG_CH4_INCLUDED)
extern const sci_ch_rom_t      ch4_rom;
extern sci_ch_ctrl_t           ch4_ctrl;
#endif

#if (SCI_CFG_CH5_INCLUDED)
extern const sci_ch_rom_t      ch5_rom;
extern sci_ch_ctrl_t           ch5_ctrl;
#endif

#if (SCI_CFG_CH6_INCLUDED)
extern const sci_ch_rom_t      ch6_rom;
extern sci_ch_ctrl_t           ch6_ctrl;
#endif

#if (SCI_CFG_CH7_INCLUDED)
extern const sci_ch_rom_t      ch7_rom;
extern sci_ch_ctrl_t           ch7_ctrl;
#endif

#if (SCI_CFG_CH8_INCLUDED)
extern const sci_ch_rom_t      ch8_rom;
extern sci_ch_ctrl_t           ch8_ctrl;
#endif

#if (SCI_CFG_CH9_INCLUDED)
extern const sci_ch_rom_t      ch9_rom;
extern sci_ch_ctrl_t           ch9_ctrl;
#endif

#if (SCI_CFG_CH10_INCLUDED)
extern const sci_ch_rom_t      ch10_rom;
extern sci_ch_ctrl_t           ch10_ctrl;
#endif

#if (SCI_CFG_CH11_INCLUDED)
extern const sci_ch_rom_t      ch11_rom;
extern sci_ch_ctrl_t           ch11_ctrl;
#endif

#if (SCI_CFG_CH12_INCLUDED)
extern const sci_ch_rom_t      ch12_rom;
extern sci_ch_ctrl_t           ch12_ctrl;
#endif

/*****************************************************************************
Exported global functions
******************************************************************************/
#if SCI_CFG_TEI_INCLUDED
extern void sci0_tei0_isr(void *cb_args);
extern void sci1_tei1_isr(void *cb_args);
extern void sci2_tei2_isr(void *cb_args);
extern void sci3_tei3_isr(void *cb_args);
extern void sci4_tei4_isr(void *cb_args);
extern void sci5_tei5_isr(void *cb_args);
extern void sci6_tei6_isr(void *cb_args);
extern void sci7_tei7_isr(void *cb_args);
extern void sci8_tei8_isr(void *cb_args);
extern void sci9_tei9_isr(void *cb_args);
extern void sci10_tei10_isr(void *cb_args);
extern void sci11_tei11_isr(void *cb_args);
extern void sci12_tei12_isr(void *cb_args);
#endif /* End of SCI_CFG_TEI_INCLUDED */

extern void sci0_eri0_isr(void *cb_args);
extern void sci1_eri1_isr(void *cb_args);
extern void sci2_eri2_isr(void *cb_args);
extern void sci3_eri3_isr(void *cb_args);
extern void sci4_eri4_isr(void *cb_args);
extern void sci5_eri5_isr(void *cb_args);
extern void sci6_eri6_isr(void *cb_args);
extern void sci7_eri7_isr(void *cb_args);
extern void sci8_eri8_isr(void *cb_args);
extern void sci9_eri9_isr(void *cb_args);
extern void sci10_eri10_isr(void *cb_args);
extern void sci11_eri11_isr(void *cb_args);
extern void sci12_eri12_isr(void *cb_args);

extern void sci_init_register(sci_hdl_t const hdl);

#if (SCI_CFG_ASYNC_INCLUDED)
extern sci_err_t sci_async_cmds(sci_hdl_t const hdl,
                         sci_cmd_t const cmd,
                         void            *p_args);
#endif

#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
extern sci_err_t sci_sync_cmds(sci_hdl_t const hdl,
                        sci_cmd_t const cmd,
                        void            *p_args);
#endif

extern sci_err_t sci_mcu_param_check(uint8_t const chan);

extern int32_t sci_init_bit_rate(sci_hdl_t const    hdl,
                          uint32_t const     pclk,
                          uint32_t const     baud);

extern void sci_initialize_ints(sci_hdl_t const hdl,
                                uint8_t const   priority);

extern void sci_disable_ints(sci_hdl_t const hdl);

#endif /* SCI_RX72N_H */

