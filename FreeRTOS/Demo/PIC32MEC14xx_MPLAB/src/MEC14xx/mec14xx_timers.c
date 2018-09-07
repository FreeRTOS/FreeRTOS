/*****************************************************************************
* © 2014 Microchip Technology Inc. and its subsidiaries.
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


/** @file mec14xx_timers.c
 *MEC14xx Timers 
 */
/** @defgroup MEC14xx Peripherals Timers
 *  @{
 */


#include "appcfg.h"
#include "platform.h"
#include "MEC14xx/mec14xx.h"
#include "MEC14xx/mec14xx_pcr.h"
#include "MEC14xx/mec14xx_timers.h"


// pairs of bytes (sleep reg, bit position)
// sleep reg = 0 for EC_SLEEP_EN or 1 for EC_SLEEP_EN2
//
struct btmr_sleep_info_s {
    uint8_t slp_reg;
    uint8_t bit_pos;
};

static const struct btmr_sleep_info_s btmr_slp_info[BTMR_MAX_INSTANCE] = {
    { 0, PCR_EC_TIMER0_SLP_BITPOS },
    { 0, PCR_EC_TIMER1_SLP_BITPOS },
    { 1, PCR_EC2_TIMER2_SLP_BITPOS },
    { 1, PCR_EC2_TIMER3_SLP_BITPOS }
 };


#ifdef MEC14XX_BTIMER_CHECK_ID

/**
 * tmr_valid - Local helper that checks if logical Timer ID is 
 * valid. 
 * 
 * @author sworley 
 * 
 * @param tmr_id 0-based Timer ID
 * 
 * @return uint8_t Non-zero(VALID), 0(Invalid)
 */
static uint8_t btmr_valid(uint8_t tmr_id)
{
    if ( tmr_id < (BTMR_ID_MAX ) ) {
        return true;
    }
    return false;
}

#else

/**
 * @brief - This version of tmr_valid skips checking always 
 *        returning TRUE. Compiler may optimize it out.
 * 
 */
static uint8_t btmr_valid(uint8_t tmr_id) 
{ 
    (void) tmr_id;
    return true; 
}

#endif

uint32_t btmr_get_hw_addr(uint8_t btmr_id)
{
    return (uint32_t)(BTMR0_BASE) + 
           ((uint32_t)(btmr_id) << (BTMR_INSTANCE_BITPOS));
}

/**
 * btmr_sleep_en - Enable/Disable clock gating on idle of a 
 * timer 
 * 
 * @author sworley (8/16/2013)
 * 
 * @param tmr_id zero based timer ID.
 * @param pwr_on boolean true=ON, false=OFF
 */
void btmr_sleep_en(uint8_t tmr_id, uint8_t sleep_en)
{
    uint32_t sleep_mask;
    uint32_t volatile * p;
    
    sleep_mask = 0ul;
    if ( btmr_valid(tmr_id) ) {
        if (btmr_slp_info[tmr_id].slp_reg) {
            p = (uint32_t volatile *)&(PCR->EC_SLEEP_EN2);
        } else {
            p = (uint32_t volatile *)&(PCR->EC_SLEEP_EN);
        }
        sleep_mask = (1ul << btmr_slp_info[tmr_id].bit_pos);
        if (sleep_en) {
            *p |= (sleep_mask);
        } else {
            *p &= ~(sleep_mask);
        }
    }
}

/**
 * btmr_reset - Peform soft reset of specified timer.
 * 
 * @author sworley 
 * 
 * @param tmr_id 0-based Timer ID 
 * @note Soft reset set all registers to POR values.
 * Spins 256 times waiting on hardware to clear reset bit. 
 */
void btmr_reset(uint8_t tmr_id)
{
   BTMR_TypeDef * p;
   uint32_t wait_cnt;

   if (btmr_valid(tmr_id)) {
      p = (BTMR_TypeDef *)btmr_get_hw_addr(tmr_id);

      p->CONTROL = (BTMR_CNTL_SOFT_RESET);

      wait_cnt = 256ul;
      do {
          if ( 0ul == (p->CONTROL & BTMR_CNTL_SOFT_RESET) ) {
              break;
          }
      } 
      while ( wait_cnt-- ); 
   }      
}

/**
 * btmr_init - Initialize specified timer
 * @param zero based timer ID
 * @param tmr_cntl b[15:0] = timer configuration flags.
 * @param initial_count 
 * @param preload_count 
 * @note performs a soft reset of the timer before 
 *       configuration.
 */
void btmr_init(uint8_t tmr_id, 
               uint16_t tmr_cntl,
               uint16_t prescaler,
               uint32_t initial_count,
               uint32_t preload_count)
{
    BTMR_TypeDef * pTMR;

    pTMR = NULL;

    if (btmr_valid(tmr_id)) {
        btmr_reset(tmr_id);
        
        pTMR = (BTMR_TypeDef *)btmr_get_hw_addr(tmr_id);
        
        // Ungate timer clocks and program prescale
        pTMR->CONTROL = ((uint32_t)prescaler << 16) + (BTMR_CNTL_ENABLE);
        
        // Program Preload & initial counter value
        pTMR->PRELOAD = preload_count;
        pTMR->COUNT = initial_count;
        
        // Program control register, interrupt enable, and clear status
        if (tmr_cntl & BTMR_COUNT_UP) {
            pTMR->CONTROL |= BTMR_CNTL_COUNT_UP;  
        }
        if (tmr_cntl & BTMR_AUTO_RESTART) {
            pTMR->CONTROL |= BTMR_CNTL_AUTO_RESTART; 
        }
        
        if (tmr_cntl & BTMR_INT_EN) {
            pTMR->INTEN = 0x01u;    // enable first
            pTMR->STATUS = 0x01u;   // clear status
        }
    }
}

/**
 * btmr_ien - Enable specified timer's interrupt.
 * 
 * @author sworley 
 * 
 * @param tmr_id zero based timer ID.
 * @param ien Non-zero enable interrupt in timer block, 0 
 *            disable.
 * @note Write 0 or 1 to timer's INTEN register.
 */
void btmr_ien(uint8_t tmr_id, uint8_t ien)
{
    BTMR_TypeDef * p;

    if (btmr_valid(tmr_id)) {
        p = (BTMR_TypeDef *)btmr_get_hw_addr(tmr_id);

        if (ien) {
             p->INTEN = (BTMR_INTEN); 
        } else {
             p->INTEN = (BTMR_INTDIS); 
        }
    }
}

/**
 * tmr_get_clr_ists - Read Timer interrupt status and clear if
 * set. 
 * 
 * @author sworley 
 * 
 * @param tmr_id zero based timer ID.
 * 
 * @return uint8_t true (Timer interrupt status set) else false. 
 * @note If timer interrupt status is set then clear it before 
 *       returning.
 */
uint8_t btmr_get_clr_ists(uint8_t tmr_id)
{
    BTMR_TypeDef * p;
    uint8_t rc;

    rc = (MEC14XX_FALSE);
    if (btmr_valid(tmr_id)) {
        p = (BTMR_TypeDef *)btmr_get_hw_addr(tmr_id);

        if ( p->STATUS ) {
            p->STATUS = (BTMR_STATUS_ACTIVE);
            rc = true;
        }
    }
    return rc;
}

/**
 * btmr_reload - Force timer to reload counter from preload 
 * register. 
 * 
 * @param tmr_id zero based timer ID. 
 * @note Hardware will only reload counter if timer is running. 
 */
void btmr_reload(uint8_t tmr_id)
{
    BTMR_TypeDef * p;

    if ( btmr_valid(tmr_id) ) {
        p = (BTMR_TypeDef *)btmr_get_hw_addr(tmr_id);

        if (p->CONTROL & BTMR_CNTL_START) {
            p->CONTROL |= BTMR_CNTL_RELOAD;
        }
    }
}

/**
 * btmr_set_count - Program timer's counter register.
 * 
 * @author sworley 
 * 
 * @param tmr_id zero based timer ID
 * @param count new counter value 
 * @note Timer hardware may implement a 16-bit or 32-bit 
 *       hardware counter. If the timer is 16-bit only the lower
 *       16-bits of the count paramter are used.
 */
void btmr_set_count(uint8_t tmr_id, uint32_t count)
{
    BTMR_TypeDef * p;

    if (btmr_valid(tmr_id)) {
        p = (BTMR_TypeDef *)btmr_get_hw_addr(tmr_id);

        p->COUNT = count;
    }
}

/**
 * btmr_count - Return current value of timer's count register.
 * 
 * @author sworley 
 * 
 * @param tmr_id zero based timer ID.
 * 
 * @return uint32_t timer count may be 32 or 16 bits depending 
 *         upon the hardware.  On MEC1322 Timers 0-3 are 16-bit
 *         and Timers 4-5 are 32-bit.
 */
uint32_t btmr_count(uint8_t tmr_id)
{
    BTMR_TypeDef * p;
    uint32_t cnt;
    
    cnt = 0ul;
    if ( btmr_valid(tmr_id) ) {
        p = (BTMR_TypeDef *)btmr_get_hw_addr(tmr_id);
        cnt = (uint32_t)(p->COUNT);
    }
    
    return cnt;
}

/**
 * btmr_start - Start timer counting.
 * 
 * @author sworley 
 * 
 * @param tmr_id zero based timer ID.
 */
void btmr_start(uint8_t btmr_id)
{
    BTMR_TypeDef * p;

    if ( btmr_valid(btmr_id) ) {
        p = (BTMR_TypeDef *)btmr_get_hw_addr(btmr_id);
        p->CONTROL |= BTMR_CNTL_START;
    }
}

/**
 * btmr_stop - Stop timer.
 * 
 * @author sworley 
 * 
 * @param tmr_id zero based timer ID. 
 * @note When a stopped timer is started again it will reload 
 *       the count register from preload value.
 */
void btmr_stop(uint8_t tmr_id)
{
    BTMR_TypeDef * p;

    if (btmr_valid(tmr_id)) {
        p = (BTMR_TypeDef *)btmr_get_hw_addr(tmr_id);
        p->CONTROL &= ~(BTMR_CNTL_START);
    }
}

/**
 * btmr_is_stopped - Return state of timer's START bit.
 * 
 * @author sworley 
 * 
 * @param tmr_id zero based timer ID.
 * 
 * @return uint8_t false(timer not started), true(timer started)
 */
uint8_t btmr_is_stopped(uint8_t tmr_id)
{
    BTMR_TypeDef * p;
    uint8_t rc;
    
    rc = (MEC14XX_TRUE);
    if (btmr_valid(tmr_id)) {
        rc = (MEC14XX_FALSE);
        p = (BTMR_TypeDef *)btmr_get_hw_addr(tmr_id);
        if ((p->CONTROL & BTMR_CNTL_START) == 0) {
            rc = (MEC14XX_TRUE);
        }
    }
    return rc;
}


/**
 * btmr_halt - Halt timer counting with no reload on unhalt. 
 * 
 * @author sworley 
 * 
 * @param tmr_id zero based timer ID. 
 * @note A halted timer will not reload the count register when 
 *       unhalted, it will continue counting from the current
 *       count value.
 */
void btmr_halt(uint8_t tmr_id)
{
    BTMR_TypeDef * p;

    if ( btmr_valid(tmr_id) ) {
        p = (BTMR_TypeDef *)btmr_get_hw_addr(tmr_id);
        p->CONTROL |= (BTMR_CNTL_HALT);
    }
}


/**
 * btmr_unhalt - Unhalt timer counting.
 * 
 * @author sworley 
 * 
 * @param tmr_id zero based timer ID.
 */
void btmr_unhalt(uint8_t tmr_id)
{
    BTMR_TypeDef * p;

    if ( btmr_valid(tmr_id) ) {
        p = (BTMR_TypeDef *)btmr_get_hw_addr(tmr_id);
        p->CONTROL &= ~(BTMR_CNTL_HALT);
    }
}


/* end mec14xx_timers.c */
/**   @}
 */
