/*****************************************************************************
* (c) 2014 Microchip Technology Inc. and its subsidiaries.
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

/** @file general_exception.c
 *MEC14xx General Exception Handler
 */
/** @defgroup MEC14xx Exceptions
 *  @{
 */


#include "appcfg.h"
#include "platform.h"
#include "MEC14xx/mec14xx.h"
#include "MEC14xx/mec14xx_trace_inline.h"

typedef struct gen_except_capture
{
    uint32_t stack_ptr;
    uint32_t cp0_status;
    uint32_t cp0_cause;
    uint32_t cp0_epc;
    uint32_t cp0_error_epc;
    uint32_t cp0_nexc;
    uint32_t cp0_nepc;
    uint32_t cp0_badvaddr;
    uint32_t ahb_err;
} GEN_EXCEPT_CAPTURE;

GEN_EXCEPT_CAPTURE gexc_cap;

void 
__attribute__((nomips16, noreturn)) _general_exception_handler (void)
{
    /* 
     *  MEC14xx Application General Exception handler
     */
    uint32_t e;

    /* Get current Stack Pointer. Note: this is not SP at
     * exception. XC32 wraps _general_exception_handler in
     * assembly code which saves state resulting is a
     * modified SP. Wrapper allocates 88 bytes for context
     * save. Original SP = SPcurrent + 88.
     */
    __asm__ __volatile (
      "move %0,$sp \n\t"
      "nop        \n\t" 
      :"=r" (e) 
      ::);
    gexc_cap.stack_ptr = e;
    
    gexc_cap.cp0_status = _CP0_GET_STATUS();
    gexc_cap.cp0_cause = _CP0_GET_CAUSE();
    gexc_cap.cp0_epc = _CP0_GET_EPC();
    gexc_cap.cp0_error_epc = _CP0_GET_ERROREPC();
    gexc_cap.cp0_nexc = _CP0_GET_NESTEDEXC();
    gexc_cap.cp0_nepc = _CP0_GET_NESTEDEPC();
    gexc_cap.cp0_badvaddr = _CP0_GET_BADVADDR();

    trace0(0, AP3GENEXCEPT, 0, "Application General Exception Handler (BEV=0)");
    TRACE11(601, AP3GENEXCEPT, 0, "Current SP   = 0x%08x",gexc_cap.stack_ptr);
    TRACE11(602, AP3GENEXCEPT, 0, "CP0 STATUS   = 0x%08x",gexc_cap.cp0_status);
    TRACE11(603, AP3GENEXCEPT, 0, "CP0 CAUSE    = 0x%08x",gexc_cap.cp0_cause);
    TRACE11(604, AP3GENEXCEPT, 0, "CP0 EPC      = 0x%08x",gexc_cap.cp0_epc);
    TRACE11(605, AP3GENEXCEPT, 0, "CP0 ERROREPC = 0x%08x",gexc_cap.cp0_error_epc);
    TRACE11(606, AP3GENEXCEPT, 0, "CP0 NEXC     = 0x%08x",gexc_cap.cp0_nexc);
    TRACE11(607, AP3GENEXCEPT, 0, "CP0 NEPC     = 0x%08x",gexc_cap.cp0_nepc);
    TRACE11(608, AP3GENEXCEPT, 0, "CP0 BADVADDR = 0x%08x",gexc_cap.cp0_badvaddr);

    for (;;) {
        __asm__ __volatile ("%(ssnop%)" : :);
    } 
}


/* end general_exception.c */
/**   @}
 */

