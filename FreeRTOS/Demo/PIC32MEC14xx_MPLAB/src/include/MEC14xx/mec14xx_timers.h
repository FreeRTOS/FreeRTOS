/*****************************************************************************
* Copyright 2014 Microchip Technology Inc. and its subsidiaries.
* You may use this software and any derivatives exclusively with
* Microchip products.
* THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS".
* NO WARRANTIES, WHETHER EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE,
* INCLUDING ANY IMPLIED WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY,
* AND FITNESS FOR A PARTICULAR PURPOSE, OR ITS INTERACTION WITH MICROCHIP
* PRODUCTS, COMBINATION WITH ANY OTHER PRODUCTS, OR USE IN ANY APPLICATION.
* IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
* INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
* WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
* BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE.
* TO THE FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL
* CLAIMS IN ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF
* FEES, IF ANY, THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
* MICROCHIP PROVIDES THIS SOFTWARE CONDITIONALLY UPON YOUR ACCEPTANCE
* OF THESE TERMS.
*****************************************************************************/


/** @file mec14xx_timers.h
 *MEC14xx Timer definitions
 */
/** @defgroup MEC14xx Peripherals Timers
 */

#ifndef _MEC14XX_TIMERS_H
#define _MEC14XX_TIMERS_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/*******************************************************************************
 * Basic 16-bit Timer
 ******************************************************************************/

//
// Basic 16-bit timers, Number of Instances
//
#define BTMR_MAX_INSTANCE                (4ul)

//
// Offset between instances of the TMR blocks
//
#define BTMR_INSTANCE_BITPOS            (5ul)
#define BTMR_INSTANCE_OFFSET            (1ul << (BTMR_INSTANCE_BITPOS))

//
// Basic Timer Count Register (Offset +00h), 32-bit, uses b[15:0]
//
#define BTMR_CNT_MASK               (0x0000FFFFUL)

//
// Basic Timer Preload Register (Offset +04h), 32-bit, uses b[15:0]
//
#define BTMR_PRELOAD_MASK           (0x0000FFFFUL)

//
// Basic Timer Status Register (Offset +08h), 32-bit, uses b[0] (R/W1C)
//
#define BTMR_STATUS_ACTIVE          (0x01UL)

//
// Basic Timer Interrupt Enable Register (Offset +0Ch), 32-bit, uses b[0]
//
#define BTMR_INTEN                  (0x01UL)
#define BTMR_INTDIS                 (0ul)

//
// Basic Timer Control Register (Offset +10h), 32-bit, uses b[31:0]
//
#define BTMR_CNTL                   (0x10UL)
//
#define BTMR_CNTL_PRESCALE_MASK          (0xFFFF0000UL)
#define BTMR_CNTL_PRESCALE_BITPOS        (16U)
#define BTMR_CNTL_PRESCALE_FIELD_WIDTH   (16U)
#define BTMR_CNTL_RSVD_MASK              (0x0000FF02UL)
#define BTMR_CNTL_HALT                   (0x80UL)
#define BTMR_CNTL_RELOAD                 (0x40UL)
#define BTMR_CNTL_START                  (0x20UL)
#define BTMR_CNTL_SOFT_RESET             (0x10UL)
#define BTMR_CNTL_AUTO_RESTART           (0x08UL)
#define BTMR_CNTL_COUNT_UP               (0x04UL)
#define BTMR_CNTL_ENABLE                 (0x01UL)
//
#define BTMR_CNTL_HALT_BIT               (7U)
#define BTMR_CNTL_RELOAD_BIT             (6U)
#define BTMR_CNTL_START_BIT              (5U)
#define BTMR_CNTRL_SOFT_RESET_BIT        (4U)
#define BTMR_CNTL_AUTO_RESTART_BIT       (3U)
#define BTMR_CNTL_COUNT_DIR_BIT          (2U)
#define BTMR_CNTL_ENABLE_BIT             (0U)

/*******************************************************************************
 * RTOS Timer
 ******************************************************************************/
#define RTMR_MAX_INSTANCE       (1)

/* RTOS Timer clock input is 32KHz.
 * FW must enable 32KHz clock domain.
 * NOTE: AHB register interface uses 48MHz
 * clock domain.
 */
#define RTMR_CLOCK_SRC_FREQ_HZ  (32768ul)

//
// +00h Count Value, 32-bit Read-Only
// NOTE: Register must be read as 32-bit, there is no
// latch mechanism.
//
#define RTMR_COUNT_RO_OFS               (0ul)

//
// +04h Pre-load, 32-bit Read-Write
//
#define RTMR_PRELOAD_OFS                (4ul)

//
// +08h Control, 32-bit Read-Write
// Implements bits[4:0]
//
#define RTMR_CONTROL_OFS                (8ul)
#define RTMR_CONTROL_MASK               (0x1Ful)
#define RTMR_BLOCK_EN_BITPOS            (0)
#define RTMR_BLOCK_EN                   (1ul << (RTMR_BLOCK_EN_BITPOS))
#define RTMR_AUTO_RELOAD_BITPOS         (1)
#define RTMR_AUTO_RELOAD_EN             (1ul << (RTMR_AUTO_RELOAD_BITPOS))
#define RTMR_START_BITPOS               (2)
#define RTMR_START                      (1ul << (RTMR_START_BITPOS))
#define RTMR_EXT_HW_HALT_EN_BITPOS      (3)
#define RTMR_EXT_HW_HALT_EN             (1ul << (RTMR_EXT_HW_HALT_EN_BITPOS))
#define RTMR_FW_HALT_BITPOS             (4)
#define RTMR_FW_HALT                    (1ul << (RTMR_FW_HALT_BITPOS))


/*******************************************************************************
 * Hibernation Timer
 ******************************************************************************/
#define HIBTMR_MAX_INSTANCE             (1)

/* Hibernation Timer clock input is 32KHz.
 * FW must enable 32KHz clock domain.
 * NOTE: AHB register interface uses 48MHz
 * clock domain.
 */
#define HIBTMR_CLOCK_SRC_FREQ_HZ        (32768ul)

//
// +00h Preload, 16-bit Read-Write
//
#define HIBTMR_PRELOAD_OFS              (0ul)
/* Write 0 to Preload to disable timer, non-zero loads COUNT
 * and starts timer */
#define HIBTMR_PRELOAD_DISABLE          (0)


//
// +04h Control, 16-bit Read-Write
// Implements bit[0]
//
#define HIBTMR_CNTRL_OFS                (4ul)
#define HIBTMR_CNTRL_RESERVED_MASK      (0xFFFEu)
#define HIBTMR_CNTRL_MASK               (0x01ul)
#define HIBTMR_CNTRL_FREQ_32KHZ         (0)
#define HIBTMR_CNTRL_FREQ_8HZ           (1)

//
// +08h Count, 16-bit Read-Only
//
#define HIBTMR_COUNT_RO_OFS             (8ul)


/*******************************************************************************
 * RTC/Week Timer
 ******************************************************************************/
#define WKTMR_MAX_INSTANCE             (1)

/* Week Timer clock input is 32KHz.
 * FW must enable 32KHz clock domain.
 * NOTE: AHB register interface uses 48MHz
 * clock domain.
 */
#define WKTMR_CLOCK_SRC_FREQ_HZ        (32768ul)

//
// +00h Control, 8-bit Read-Write
//
#define WKTMR_CNTRL_OFS                (0ul)
#define WKTMR_CNTRL_MASK               (0x61u)
#define WKTMR_CNTRL_RESERVED_MASK      (~(WKTMR_CNTRL_MASK))
#define WKTMR_CNTRL_EN_BITPOS          (0)
#define WKTMR_CNTRL_EN                 (1ul << (WKTMR_CNTRL_EN_BITPOS))
#define WKTMR_BGPO_BITPOS              (5)
#define WKTMR_BGPO_LO                  (0ul << (WKTMR_BGPO_BITPOS))
#define WKTMR_BGPO_HI                  (1ul << (WKTMR_BGPO_BITPOS))
#define WKTMR_PWRUP_EVENT_EN_BITPOS    (6)
#define WKTMR_PWRUP_EVENT_EN           (1ul << (WKTMR_PWRUP_EVENT_EN_BITPOS))

//
// +04h 1-second COUNT, 32-bit Read-Write
// Implements bits[27:0]
//
#define WKTMR_COUNT_1S_OFS              (4ul)
#define WKTMR_COUNT_1S_MASK             (0x0FFFFFFFul)

//
// +08h COMPARE, 32-bit Read-Write
// Implements bits[27:0]
//
#define WKTMR_COMPARE_OFS               (8ul)
#define WKTMR_COUNT_1S_MASK             (0x0FFFFFFFul)

//
// +0Ch Clock Divider, 32-bit Read-Only
// Implements b[14:0]
//
#define WKTMR_CLOCK_DIVIDER_RO_OFS      (0x0Cul)
#define WKTMR_CLOCK_DIVIDER_RO_MASK     (0x7FFFul)

//
// +10h Sub-second Interrupt Events Select, 32-bit Read-Write
// Implements bits[3:0]
//
#define WKTMR_SUBSEC_EVENTS_SEL_OFS      (0x10ul)
#define WKTMR_SUBSEC_EVENTS_SEL_MASK     (0x0Ful)
#define WKTMR_SUBSEC_EV_DIS              (0u)
#define WKTMR_SUBSEC_EV_2HZ              (1u)
#define WKTMR_SUBSEC_EV_4HZ              (2u)
#define WKTMR_SUBSEC_EV_8HZ              (3u)
#define WKTMR_SUBSEC_EV_16HZ             (4u)
#define WKTMR_SUBSEC_EV_32HZ             (5u)
#define WKTMR_SUBSEC_EV_64HZ             (6u)
#define WKTMR_SUBSEC_EV_128HZ            (7u)
#define WKTMR_SUBSEC_EV_256HZ            (8u)
#define WKTMR_SUBSEC_EV_512HZ            (9u)
#define WKTMR_SUBSEC_EV_1024HZ           (10u)
#define WKTMR_SUBSEC_EV_2048HZ           (11u)
#define WKTMR_SUBSEC_EV_4096HZ           (12u)
#define WKTMR_SUBSEC_EV_8192HZ           (13u)
#define WKTMR_SUBSEC_EV_16384HZ          (14u)
#define WKTMR_SUBSEC_EV_32768HZ          (15u)

//
// +14h Sub-Week Control, 32-bit Read-Write
// Implements bits[9:4, 1:0]
// Bits[1:0] = Read-Write-1-Clear
// Bit[4] = Read-Only
// Bits[9:5] = Read-Write
//
#define WKTMR_SUB_CNTRL_OFS             (0x14ul)
#define WKTMR_SUB_CNTRL_MASK            (0x3F3ul)
#define WKTMR_SUB_CNTRL_RESERVED_MASK   (~(WKTMR_SUB_CNTRL_MASK))
#define WKTMR_SC_PWRUP_EV_STS_BITPOS    (0)
#define WKTMR_SC_PWRUP_EV_STS           (1ul << (WKTMR_SC_PWRUP_EV_STS_BITPOS))
#define WKTMR_WK_PWRUP_EV_STS_BITPOS    (1)
#define WKTMR_WK_PWRUP_EV_STS           (1ul << (WKTMR_WK_PWRUP_EV_STS_BITPOS))
#define WKTMR_SC_SYSPWR_PRES_STS_BITPOS (4)
#define WKTMR_SC_SYSPWR_PRES_STS        (1ul << (WKTMR_SC_SYSPWR_PRES_STS_BITPOS))
#define WKTMR_SC_SYSPWR_PRES_EN_BITPOS  (5)
#define WKTMR_SC_SYSPWR_PRES_EN         (1ul << (WKTMR_SC_SYSPWR_PRES_EN_BITPOS))
#define WKTMR_SC_AUTO_RELOAD_EN_BITPOS  (6)
#define WKTMR_SC_AUTO_RELOAD_EN         (1ul << (WKTMR_SC_AUTO_RELOAD_EN_BITPOS))
#define WKTMR_SC_CLKSRC_BITPOS          (7)
#define WKTMR_SC_CLKSRC_MASK            (0x07ul << (WKTMR_SC_CLKSRC_BITPOS))

//
// +18h Sub-Week Count, 32-bit Read-Write
// Implements bits[24:16, 8:0]
// Bit2[24:16] = Read-Only
// Bits[8:0] = Read-Write
//
#define WKTMR_SUBWK_COUNT_OFS           (0x18ul)
#define WKTMR_SUBWK_COUNT_MASK          (0x01FF01FFul)
#define WKTMR_SUBWK_COUNT_RESERVED_MASK (~(WKTMR_SUBWK_COUNT_MASK))
#define WKTMR_SUBWK_CNT_LOAD_BITPOS     (0)
#define WKTMR_SUBWK_CNT_LOAD_MASK       (0x1FFul)
#define WKTMR_SUBWK_CNT_VAL_RO_BITPOS   (16)
#define WKTMR_SUBWK_CNT_VAL_RO_MASK     (0x01FFul)


/*******************************************************************************
 * Basic 16-bit Timer API
 ******************************************************************************/

//
// Logical Basic Timer ID for API calls
//

#define BTMR0_ID                    (0x00u)
#define BTMR1_ID                    (0x01u)
#define BTMR2_ID                    (0x02u)
#define BTMR3_ID                    (0x03u)
#define BTMR_ID_MAX                 (0x04u)

//
// Logical flags for tmr_cntl parameter of TMRInit
// b[31:16] = prescaler
//
#define BTMR_AUTO_RESTART           (0x08u)
#define BTMR_ONE_SHOT               (0u)
#define BTMR_COUNT_UP               (0x04u)
#define BTMR_COUNT_DOWN             (0u)
#define BTMR_INT_EN                 (0x01u)
#define BTMR_NO_INT                 (0u)

uint32_t btmr_get_hw_addr(uint8_t btmr_id);

void btmr_sleep_en(uint8_t tmr_id, uint8_t sleep_en);
void btmr_reset(uint8_t tmr_id);
void btmr_init(uint8_t tmr_id, 
               uint16_t tmr_cntl,
               uint16_t prescaler,
               uint32_t initial_count,
               uint32_t preload_count);

void btmr_ien(uint8_t tmr_id, uint8_t ien);
uint8_t btmr_get_clr_ists(uint8_t tmr_id);

void btmr_reload(uint8_t tmr_id);
void btmr_set_count(uint8_t tmr_id, uint32_t count);
uint32_t btmr_count(uint8_t tmr_id);
void btmr_start(uint8_t tmr_id);
void btmr_stop(uint8_t tmr_id);
uint8_t btmr_is_stopped(uint8_t tmr_id);
void btmr_halt(uint8_t tmr_id);
void btmr_uhalt(uint8_t tmr_id);

/*******************************************************************************
 * End Basic 16-bit Timer API
 ******************************************************************************/

 
#ifdef __cplusplus
}
#endif

#endif // #ifndef _MEC14XX_TIMERS_H
/* end mec14xx_timers.h */
/**   @}
 */
