/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

#ifndef SAMS7_CHIP_H
#define SAMS7_CHIP_H


/* Define WEAK attribute */
#if defined   ( __CC_ARM   )
    #define WEAK __attribute__ ((weak))
#elif defined ( __ICCARM__ )
    #define WEAK __weak
#elif defined (  __GNUC__  )
    #define WEAK __attribute__ ((weak))
#endif

/* Define NO_INIT attribute */
#if defined   ( __CC_ARM   )
    #define NO_INIT
#elif defined ( __ICCARM__ )
    #define NO_INIT __no_init
#elif defined (  __GNUC__  )
    #define NO_INIT
#endif

/* Define RAMFUNC attribute */
#ifdef __ICCARM__
#define RAMFUNC __ramfunc
#else
#define RAMFUNC __attribute__ ((section (".ramfunc")))
#endif

/*
 * Peripherals registers definitions
 */
#include "include/samv7/sam.h"

/*
 * Core
 */
//#include "include/exceptions.h"

#define memory_barrier()        __DSB();
/*
 * Peripherals
 */

#include "include/acc.h"
#include "include/aes.h"
#include "include/afec.h"
#include "include/efc.h"
#include "include/pio.h"
#include "include/pio_it.h"
#include "include/efc.h"
#include "include/mpu.h"
#include "include/gmac.h"
#include "include/gmacd.h"
#include "include/video.h"
#include "include/icm.h"
#include "include/isi.h"
#include "include/exceptions.h"
#include "include/pio_capture.h"
#include "include/rtc.h"
#include "include/rtt.h"
#include "include/tc.h"
#include "include/timetick.h"
#include "include/twi.h"
#include "include/twid.h"
#include "include/flashd.h"
#include "include/pmc.h"
#include "include/pwmc.h"
#include "include/supc.h"
#include "include/usart.h"
#include "include/uart.h"
#include "include/isi.h"
#include "include/hsmci.h"
#include "include/ssc.h"
#include "include/twi.h"
#include "include/twid.h"
#include "include/trng.h"
#include "include/wdt.h"
#include "include/spi.h"
#include "include/qspi.h"
#include "include/trace.h"
#include "include/xdmac.h"
#include "include/xdma_hardware_interface.h"
#include "include/xdmad.h"
#include "include/mcid.h"
#include "include/spi_dma.h"
#include "include/qspi_dma.h"
#include "include/uart_dma.h"
#include "include/usart_dma.h"
#include "include/afe_dma.h"
#include "include/dac_dma.h"

#define ENABLE_PERIPHERAL(dwId)         PMC_EnablePeripheral( dwId )
#define DISABLE_PERIPHERAL(dwId)        PMC_DisablePeripheral( dwId )
   
   
/* SCB Interrupt Control State Register Definitions */
#ifndef SCB_VTOR_TBLBASE_Pos
#define SCB_VTOR_TBLBASE_Pos               29                                             /*!< SCB VTOR: TBLBASE Position */
#define SCB_VTOR_TBLBASE_Msk               (1UL << SCB_VTOR_TBLBASE_Pos)                  /*!< SCB VTOR: TBLBASE Mask */
#endif

#define RESET_CYCLE_COUNTER()               { DWT->CTRL = 0;__ISB(); \
                                            while(DWT->CYCCNT != 0)DWT->CYCCNT = 0;\
                                            DWT->CTRL = DWT_CTRL_CYCCNTENA_Msk; }

#define GET_CYCLE_COUNTER(x)                 x=DWT->CYCCNT;

#endif /* SAMS7_CHIP_H */
