/*-----------------------------------------------------------------------------
 *           ATMEL Microcontroller Software Support  -  ROUSSET  -
 *-----------------------------------------------------------------------------
 * DISCLAIMER:  THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *----------------------------------------------------------------------------
 * File Name           : catb.h
 * Object              :
 * Creation            : DAL   21/Jun/2013
 *----------------------------------------------------------------------------
*/
#ifndef _V_CATB_H
#define _V_CATB_H

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Catb hardware registers */
typedef struct {
  __IO uint32_t CATB_CR;          /**< \brief (CATB Offset: 0x00) Control Register */
  __IO uint32_t CATB_CNTCR;       /**< \brief (CATB Offset: 0x04) Counter Control Register */
  __IO uint32_t CATB_IDLE;        /**< \brief (CATB Offset: 0x08) Sensor Idle Level */
  __IO uint32_t CATB_LEVEL;       /**< \brief (CATB Offset: 0x0C) Sensor Relative Level */
  __IO uint32_t CATB_RAW;         /**< \brief (CATB Offset: 0x10) Sensor Raw Value */
  __IO uint32_t CATB_TIMING;      /**< \brief (CATB Offset: 0x14) Filter Timing Register */
  __IO uint32_t CATB_THRESH;      /**< \brief (CATB Offset: 0x18) Threshold Register */
  __IO uint32_t CATB_PINSEL;      /**< \brief (CATB Offset: 0x1C) Pin Selection Register */
  __IO uint32_t CATB_DMA;         /**< \brief (CATB Offset: 0x20) Direct Memory Access Register */
  __IO uint32_t CATB_ISR;         /**< \brief (CATB Offset: 0x24) Interrupt Status Register */
  __IO uint32_t CATB_IER;         /**< \brief (CATB Offset: 0x28) Interrupt Enable Register */
  __IO uint32_t CATB_IDR;         /**< \brief (CATB Offset: 0x2C) Interrupt Disable Register */
  __IO uint32_t CATB_IMR;         /**< \brief (CATB Offset: 0x30) Interrupt Mask Register */
  __IO uint32_t CATB_SCR;         /**< \brief (CATB Offset: 0x34) Status Clear Register */
  __I  uint32_t Reserved1[2];
  __IO uint32_t CATB_INTCHi;      /**< \brief (CATB Offset: 0x40) In-Touch Status Register i */
  __I  uint32_t Reserved2[3];
  __IO uint32_t CATB_INTCHCLRn;   /**< \brief (CATB Offset: 0x50) In-Touch Status Clear Register n */
  __I  uint32_t Reserved3[3];
  __IO uint32_t CATB_OUTTCHi;     /**< \brief (CATB Offset: 0x60) Out-of-Touch Status Register i */
  __I  uint32_t Reserved4[3];
  __IO uint32_t CATB_OUTTCHCLRn;  /**< \brief (CATB Offset: 0x70) Out-of-Touch Status Clear Register n */
  __I  uint32_t Reserved5[33];
  __IO uint32_t CATB_PARAMETER;   /**< \brief (CATB Offset: 0xF8) Parameter Register */
} Catb;

#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */


#define LENGTH                  0x1F
#define TLEVEL                  100
#define TIDLE                   0
#define CATB_THRESH_RTHRESH                                   12
#define CATB_THRESH_FTHRESH                                    0
#define CATB_ISR_INTCH (0x1u << 1) /**< \brief (CATB_ISR_INTCH) In-touch */
#define CATB_ISR_OUTTCH (0x1u<< 2) /**< \brief (CATB_ISR_OUTTCH) Out-touch */
#define CATB_IER_INTCH (0x1u << 1) /**< \brief (CATB_IER_INTCH) In-touch */
#define CATB_IER_OUTTCH (0x1u<< 2) /**< \brief (CATB_IER_OUTTCH) Out-touch */
#define CATB_CR_SWRST                                      (0x1u <<  31)
#define CATB_CR_EN                                          ( 1u<<0 )
#define CATB_CR_CHARGET_Pos 16
#define CATB_CR_CHARGET_Msk (0xfu << CATB_CR_CHARGET_Pos) /**< \brief (CATB_CNTCR) Counter Top Value */
#define CATB_CR_CHARGET(value) ((CATB_CR_CHARGET_Msk & ((value) << CATB_CR_CHARGET_Pos)))
#define CATB_CNTCR_TOP                                         0
#define CATB_SPREAD                                           24
#define CATB_REPEAT                                           28
#define CATB_TIMING_TIDLE                                     16
#define CATB_TIMING_TLEVEL                                     0
#define CATB_ISR_SAMPLE                                     (1 << 0)
#define CATB_CR_RUN                                         (0x1u << 1)
#define CATB_CR_IIDLE                                         (1<< 2)
#define CATB_CR_DMAEN                                       (1 << 7)

#endif //_V_CATB_H
