/*
********************************************************************************
* TERN, Inc.
* (c) Copyright 2005, http://www.tern.com
*
* - Created to support i2chip module on a variety of TERN hardware platforms.
********************************************************************************
*/

#ifndef _I2CHIP_HW_H_
#define _I2CHIP_HW_H_

#include "types.h"

#ifdef TERN_SC    // SensorCore controller, has mapping identical to the RL
#define TERN_RL
#endif

#ifdef TERN_RL    // R-Engine-L controller, with mapping at MCS0.
#define I2CHIP_MCS_DIRECT
#define I2CHIP_INT4
#define TERN_RE
#endif                // TERN_RL

#ifdef TERN_5E
#define TERN_586
#endif

#ifdef TERN_RD
#define TERN_RE
#endif                // TERN_RD

#ifdef TERN_RE
#define TERN_186
#endif

#ifdef TERN_P51
void p51_window(unsigned int page);
#define I2CHIP_WINDOW
#define I2CHIP_P51
#ifdef  TERN_186
#define I2CHIP_INT4
#define TERN_16_BIT
#endif                // TERN_186
#ifdef  TERN_586
#define I2CHIP_INT0
#define I2CHIP_WINDOW_IO
#endif                // TERN_586
#endif                // TERN_P51

#ifdef TERN_CEYE
#define TERN_EE       // C-Eye configured with onboard i2chip, same as EE
#endif

#ifdef TERN_EE
#define TERN_186
#define I2CHIP_MCS_DIRECT
#define I2CHIP_INT4
#define TERN_16_BIT
#endif                    // TERN_EE

#ifdef TERN_MMC
#define I2CHIP_WINDOW
#define I2CHIP_MMC
#ifdef TERN_RD
#define I2CHIP_INT3
#else
#ifdef TERN_186
#define I2CHIP_INT4
#endif                   // TERN_186
#endif                   // TERN_RD
#ifdef TERN_586
#define I2CHIP_INT0
#define I2CHIP_WINDOW_IO
#endif                   // TERN_586
#endif                   // TERN_MMC

#ifdef TERN_586
#include "586.h"
void interrupt far int0_isr(void);
void interrupt far spu_m_isr(void);
void interrupt far spu_1_isr(void);
void interrupt far spu_2_isr(void);
#define MMCR 0xdf00
#endif                   // TERN_586

#ifdef TERN_186
#ifndef TERN_RE
#include "ae.h"
#else
#include "re.h"
#define I2CHIP_SHIFTED_ADDRESS
#endif
#endif


#ifndef I2CHIP_MCS_DIRECT
#ifndef I2CHIP_WINDOW
#ifndef I2CHIP_WINDOW_IO
#error You must define the TERN address mapping used to drive the I2CHIP module!
#endif  // I2CHIP_WINDOW_IO
#endif  // I2CHIP_MMC_WINDOW
#endif  // I2CHIP_MCS_DIRECT

#ifndef I2CHIP_INT0
#ifndef I2CHIP_INT3
#ifndef I2CHIP_INT4
#ifndef I2CHIP_POLL
#error You must specify an interrupt/polling mechanism for the I2CHIP module!
#endif  // I2CHIP_POLL
#endif  // I2CHIP_INT3
#endif  // I2CHIP_INT4
#endif  // I2CHIP_INT0

#ifdef   I2CHIP_POLL
#define  I2CHIP_POLL_ISR(a)   { delay_ms(20); disable(); a(); enable(); }
#define  INT_INIT(isr)
#define  INT_EOI
#endif   // I2CHIP_POLL

#ifdef   I2CHIP_INT4
#define  INT_INIT(isr) int4_init(1, isr)
#define  INT_EOI       outport(0xff22,0x0010)
#define  I2CHIP_POLL_ISR(a)
#endif

#ifdef   I2CHIP_INT3
#define  INT_INIT(isr) int3_init(1, isr)
#define  INT_EOI       outport(0xff22,0x000f)
#define  I2CHIP_POLL_ISR(a)
#endif

#ifdef   I2CHIP_INT0
#define  INT_INIT(isr) int0_init(1, isr)
#define  INT_EOI        outportb(_MPICOCW2_IO,0x61); // 586 only EOI
#define  I2CHIP_POLL_ISR(a)
#endif


#ifdef   I2CHIP_SHIFTED_ADDRESS
#define  SA_OFFSET(a)   ((a) << 1)
#else
#define  SA_OFFSET(a)   a
#endif   // I2CHIP_SHIFTED_ADDRESS ... *if*


// -------------------- WINDOW-RELATED DEFINES ----------------------
#ifdef   I2CHIP_WINDOW
void        i2chip_set_page(u_int addr);
#define  I2CHIP_SET_PAGE(p) i2chip_set_page(p)

u_char far* i2chip_mkptr(u_int addr);
void 			i2chip_push_window(u_int addr);
void 			i2chip_pop_window(void);
u_int       i2chip_get_window(void);
void i2chip_set_window(u_int window_addr);

// Set to command window.
// Note that if you're using other MMC chips within your application, you will
// need to call this function regularly, if you've changed the MMC chip/page
// selection via mmc_window().  The driver code otherwise assume that you never
// change away from chip 7, page 0.
#define  WINDOW_RESTORE_BASE    i2chip_mkptr(0)

//  ----------------------- I2CHIP_WINDOW_IO ----------------------------
#ifdef   I2CHIP_WINDOW_IO

#ifdef   TERN_5E
#define	I2CHIP_BASE_SEG	   0x2000			// Address offset for W3100A
#else
#define	I2CHIP_BASE_SEG	   0x1800			// Address offset for W3100A
#endif

#define  COMMAND_BASE_SEG     0x0000
#define	SEND_DATA_BUF		   0x4000			// Internal Tx buffer address of W3100A
#define	RECV_DATA_BUF		   0x6000			// Internal Rx buffer address of W3100A
#define  WINDOW_BASE_SEGM     COMMAND_BASE_SEG

#define  MK_FP_WINDOW(a, b)   i2chip_mkptr(a+SA_OFFSET(b))
#define  MK_FP_SA             MK_FP_WINDOW

u_char   io_read_value(u_char far* addr);
void     io_write_value(u_char far* addr, u_char value);
#define  READ_VALUE(a)        io_read_value(a)
#define  WRITE_VALUE(a, v)    io_write_value(a, v)

#define  WINDOW_PTR_INC(a)    \
         if ((FP_OFF(a) & 0xff) == 0xff) \
            a = MK_FP_WINDOW(i2chip_get_window() + 0x100, 0); \
         else \
         	a++;

#endif  // I2CHIP_WINDOW_IO

//  -------------------- !NOT! I2CHIP_WINDOW_IO ----------------------------
#ifndef  I2CHIP_WINDOW_IO

#define  READ_VALUE(a)        *(a)
#define  WRITE_VALUE(a, v)    *(a) = v

#define  WINDOW_BASE_SEGM  0x8000
#define  MK_FP_WINDOW(a, b)   i2chip_mkptr(a+SA_OFFSET(b))
#define  MK_FP_SA  MK_FP_WINDOW

#ifdef   I2CHIP_SHIFTED_ADDRESS
#define  COMMAND_BASE_SEG  0x0000
#define  SEND_DATA_BUF     0x8000
#define  RECV_DATA_BUF     0xC000
#define  WINDOW_PTR_INC(a)    \
         if ((FP_OFF(a) & 0xff) == 0xfe) \
            a = MK_FP_WINDOW(i2chip_get_window() + 0x100, 0); \
         else \
         	a+=2;
#else
#define  COMMAND_BASE_SEG  0x0000
#define  SEND_DATA_BUF     0x4000
#define  RECV_DATA_BUF     0x6000
#define  WINDOW_PTR_INC(a)    \
         if ((FP_OFF(a) & 0xff) == 0xff) \
            a = MK_FP_WINDOW(i2chip_get_window() + 0x100, 0); \
         else \
         	a++;
#endif   // I2CHIP_SHIFTED_ADDRESS
#endif   // NOT I2CHIP_WINDOW_IO

#endif   // I2CHIP_WINDOW

//  --------------------  I2CHIP_DIRECT ----------------------------
#ifdef   I2CHIP_MCS_DIRECT

#define  READ_VALUE(a)        *(a)
#define  WRITE_VALUE(a, v)    *(a) = v

#define  I2CHIP_BASE_SEG  0x8000
#define  MK_FP_SA(a, b)   MK_FP(a, SA_OFFSET(b))
#define  WINDOW_PTR_INC(a)   a+=SA_OFFSET(1);
#define  WINDOW_RESTORE_BASE
#define  MK_FP_WINDOW           MK_FP_SA
#define  WINDOW_BASE_SEG        I2CHIP_BASE_SEG
#define  COMMAND_BASE_SEG       I2CHIP_BASE_SEG

#ifdef   I2CHIP_SHIFTED_ADDRESS
#define	SEND_DATA_BUF		0x8800			// Internal Tx buffer address of W3100A
#define	RECV_DATA_BUF		0x8C00			// Internal Rx buffer address of W3100A
#else
#define	SEND_DATA_BUF		0x8400			// Internal Tx buffer address of W3100A
#define	RECV_DATA_BUF		0x8600			// Internal Rx buffer address of W3100A
#endif   // I2CHIP_SHIFTED_ADDRESS

#endif   // I2CHIP_MCS_DIRECT

/* Internal register set of W3100A */
#define	COMMAND(i)		((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, i)))
#define	INT_STATUS(i)	((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, I2CHIP_C0_ISR + i)))
#define	INT_REG   		((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, I2CHIP_IR)))
#define	INTMASK     	((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, I2CHIP_IMR)))
#define	RESETSOCK      ((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, 0x0A)))

#define RX_PTR_BASE		I2CHIP_C0_RW_PR
#define RX_PTR_SIZE		(I2CHIP_C1_RW_PR - I2CHIP_C0_RW_PR)

#define	RX_WR_PTR(i)	((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, RX_PTR_BASE + RX_PTR_SIZE * i)))
#define	RX_RD_PTR(i)	((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, RX_PTR_BASE + RX_PTR_SIZE * i + 0x04)))
#define	RX_ACK_PTR(i)	((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, TX_PTR_BASE + TX_PTR_SIZE * i + 0x08)))

#define TX_PTR_BASE		I2CHIP_C0_TW_PR
#define TX_PTR_SIZE		(I2CHIP_C1_TW_PR - I2CHIP_C0_TW_PR)

#define	TX_WR_PTR(i)	((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, TX_PTR_BASE + TX_PTR_SIZE * i)))
#define	TX_RD_PTR(i)	((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, TX_PTR_BASE + TX_PTR_SIZE * i + 0x04)))
#define	TX_ACK_PTR(i)	((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, RX_PTR_BASE + RX_PTR_SIZE * i + 0x08)))

/* Shadow Register Pointer Define */
/* For windowing purposes, these are definitely outside the first 256-byte Window...
therefore, use the MK_FP_WINDOW macros instead. */
#define SHADOW_RXWR_PTR(i)		((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, 0x1E0 + 3*i)))
#define SHADOW_RXRD_PTR(i)		((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, 0x1E1 + 3*i)))
#define SHADOW_TXACK_PTR(i)	((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, 0x1E2 + 3*i)))
#define SHADOW_TXWR_PTR(i)		((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, 0x1F0 + 3*i)))
#define SHADOW_TXRD_PTR(i)		((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, 0x1F1 + 3*i)))

#define SOCK_BASE		I2CHIP_C0_SSR
#define SOCK_SIZE		(I2CHIP_C1_SSR - I2CHIP_C0_SSR)

#define SOCK_STATUS(i)	((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, SOCK_BASE + SOCK_SIZE * i)))
#define OPT_PROTOCOL(i)	((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, SOCK_BASE + SOCK_SIZE * i + 0x01)))
#define DST_HA_PTR(i)	((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, SOCK_BASE + SOCK_SIZE * i + 0x02)))
#define DST_IP_PTR(i)	((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, SOCK_BASE + SOCK_SIZE * i + 0x08)))
#define DST_PORT_PTR(i)	((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, SOCK_BASE + SOCK_SIZE * i + 0x0C)))
#define SRC_PORT_PTR(i)	((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, SOCK_BASE + SOCK_SIZE * i + 0x0E)))
#define IP_PROTOCOL(i)	((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, SOCK_BASE + SOCK_SIZE * i + 0x10)))
#define TOS(i)				((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG,SOCK_BASE + SOCK_SIZE * i + 0x11)))
#define MSS(i)				((u_int far *)(MK_FP_WINDOW(COMMAND_BASE_SEG, SOCK_BASE + SOCK_SIZE * i + 0x12)))
#define P_WINDOW(i)		((u_int far *)(MK_FP_WINDOW(COMMAND_BASE_SEG,SOCK_BASE + SOCK_SIZE * i + 0x14)))
#define WINDOW(i)			((u_int far*)(MK_FP_WINDOW(COMMAND_BASE_SEG, SOCK_BASE + SOCK_SIZE * i + 0x16)))

#define GATEWAY_PTR		((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG,I2CHIP_GAR)))
#define SUBNET_MASK_PTR	((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG,I2CHIP_SMR)))

#define SRC_HA_PTR		((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG,I2CHIP_SHAR)))
#define SRC_IP_PTR		((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG,I2CHIP_SIPR)))
#define TIMEOUT_PTR		((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG,I2CHIP_IRTR)))

#define RX_DMEM_SIZE		((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG,I2CHIP_RMSR)))
#define TX_DMEM_SIZE		((u_char far *)(MK_FP_WINDOW(COMMAND_BASE_SEG,I2CHIP_TMSR)))

void i2chip_init(void);

#endif  // _irchip_hw_h
