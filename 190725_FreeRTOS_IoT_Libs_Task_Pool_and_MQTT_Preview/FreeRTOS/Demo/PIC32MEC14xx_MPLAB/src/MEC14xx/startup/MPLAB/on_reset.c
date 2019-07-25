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

/** @file on_reset.c
 *MEC14xx XC32 M14K Startup code _on_reset handler
 */
/** @defgroup MEC14xx Startup
 *  @{
 */


#include "appcfg.h"
#include "platform.h"
#include "MEC14xx/mec14xx.h"
#include "MEC14xx/mec14xx_pcr.h"

/*
 * From linker command file
 */
extern uint32_t _ebase_address[];


/** _on_reset - Very early HW initialization.
 * @note XC32 startup code has initialized SP & GP. No other
 * C features have been initialized (before .bss clear and
 * global data init.) NOTE: MIPS M14K is still in Boot-Strap 
 * mode and EBASE has not been programmed. Any exception or 
 * interrupts will vector to the BEV Exception handler! 
 */
void
__attribute__((nomips16)) _on_reset (void)
{
    /* Enable JTAG */
    ECS_REG->JTAG_ENABLE |= 1u;

    /* Disable WDT */
    WDT->CONTROL = 0u;

    /* Set CPU clock divider specified in appcfg.h */
    PCR->PROC_CLOCK_CNTRL = ( PCR_CLOCK_DIVIDER );
    __EHB();
    CPU_NOP();

}


