/*

Copyright (c) 2010 - 2021, Nordic Semiconductor ASA All rights reserved.

SPDX-License-Identifier: BSD-3-Clause

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this
   list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.

3. Neither the name of Nordic Semiconductor ASA nor the names of its
   contributors may be used to endorse or promote products derived from this
   software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY, AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL NORDIC SEMICONDUCTOR ASA OR CONTRIBUTORS BE
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.

*/

#ifndef _NRF5340_PERIPHERALS_H
#define _NRF5340_PERIPHERALS_H


/* Clock Peripheral */
#define CLOCK_PRESENT
#define CLOCK_COUNT 1

#define CLOCK_FEATURE_HFCLK_DIVIDE_PRESENT

/* Power Peripheral */
#define POWER_PRESENT
#define POWER_COUNT 1

/* Non-Volatile Memory Controller */
#define NVMC_PRESENT
#define NVMC_COUNT 1

/* NVM instruction  and data cache */
#define CACHE_PRESENT
#define CACHE_COUNT 1

/* Memory Protection Unit */
#define MPU_REGION_NUM 8

/* Regulators Peripheral */
#define REGULATORS_PRESENT
#define REGULATORS_COUNT 1

#define REGULATORS_FEATURE_VDDH_PRESENT

/* USB Regulator Peripheral */
#define USBREG_PRESENT
#define USBREG_COUNT 1

/* Volatile Memory Controller Peripheral */
#define VMC_PRESENT
#define VMC_COUNT 1

#define VMC_FEATURE_RAM_REGISTERS_PRESENT
#define VMC_FEATURE_RAM_REGISTERS_COUNT 8

/* Floating Point Unit */
#define FPU_PRESENT
#define FPU_COUNT 1

/* Systick timer */
#define SYSTICK_PRESENT
#define SYSTICK_COUNT 1

/* Inter-Processor Communication */
#define IPC_PRESENT
#define IPC_COUNT 1

#define IPC_CH_NUM 16
#define IPC_CONF_NUM 16
#define IPC_GPMEM_NUM 2

/* GPIO */
#define GPIO_PRESENT
#define GPIO_COUNT 2

#define P0_PIN_NUM 32
#define P1_PIN_NUM 16

#define P0_FEATURE_PINS_PRESENT 0xFFFFFFFFUL
#define P1_FEATURE_PINS_PRESENT 0x0000FFFFUL

/* NFC Tag */
#define NFCT_PRESENT
#define NFCT_COUNT 1

#define NFCT_EASYDMA_MAXCNT_SIZE 9

/* Distributed Peripheral to Peripheral Interconnect */
#define DPPI_PRESENT
#define DPPI_COUNT 1

#define DPPI_CH_NUM 32
#define DPPI_GROUP_NUM 6

/* Event Generator Unit */
#define EGU_PRESENT
#define EGU_COUNT 6

#define EGU0_CH_NUM 16
#define EGU1_CH_NUM 16
#define EGU2_CH_NUM 16
#define EGU3_CH_NUM 16
#define EGU4_CH_NUM 16
#define EGU5_CH_NUM 16

/* Timer/Counter */
#define TIMER_PRESENT
#define TIMER_COUNT 3

#define TIMER0_MAX_SIZE 32
#define TIMER1_MAX_SIZE 32
#define TIMER2_MAX_SIZE 32

#define TIMER0_CC_NUM 6
#define TIMER1_CC_NUM 6
#define TIMER2_CC_NUM 6

/* Real Time Counter */
#define RTC_PRESENT
#define RTC_COUNT 2

#define RTC0_CC_NUM 4
#define RTC1_CC_NUM 4

/* Watchdog Timer */
#define WDT_PRESENT
#define WDT_COUNT 2

/* Serial Peripheral Interface Master with DMA */
#define SPIM_PRESENT
#define SPIM_COUNT 5

#define SPIM0_MAX_DATARATE  8
#define SPIM1_MAX_DATARATE  8
#define SPIM2_MAX_DATARATE  8
#define SPIM3_MAX_DATARATE  8
#define SPIM4_MAX_DATARATE  32

#define SPIM0_FEATURE_HARDWARE_CSN_PRESENT  0
#define SPIM1_FEATURE_HARDWARE_CSN_PRESENT  0
#define SPIM2_FEATURE_HARDWARE_CSN_PRESENT  0
#define SPIM3_FEATURE_HARDWARE_CSN_PRESENT  0
#define SPIM4_FEATURE_HARDWARE_CSN_PRESENT  1

#define SPIM0_FEATURE_DCX_PRESENT  0
#define SPIM1_FEATURE_DCX_PRESENT  0
#define SPIM2_FEATURE_DCX_PRESENT  0
#define SPIM3_FEATURE_DCX_PRESENT  0
#define SPIM4_FEATURE_DCX_PRESENT  1

#define SPIM0_FEATURE_RXDELAY_PRESENT  0
#define SPIM1_FEATURE_RXDELAY_PRESENT  0
#define SPIM2_FEATURE_RXDELAY_PRESENT  0
#define SPIM3_FEATURE_RXDELAY_PRESENT  0
#define SPIM4_FEATURE_RXDELAY_PRESENT  1

#define SPIM0_EASYDMA_MAXCNT_SIZE 16
#define SPIM1_EASYDMA_MAXCNT_SIZE 16
#define SPIM2_EASYDMA_MAXCNT_SIZE 16
#define SPIM3_EASYDMA_MAXCNT_SIZE 16
#define SPIM4_EASYDMA_MAXCNT_SIZE 16

/* Serial Peripheral Interface Slave with DMA*/
#define SPIS_PRESENT
#define SPIS_COUNT 4

#define SPIS0_EASYDMA_MAXCNT_SIZE 16
#define SPIS1_EASYDMA_MAXCNT_SIZE 16
#define SPIS2_EASYDMA_MAXCNT_SIZE 16
#define SPIS3_EASYDMA_MAXCNT_SIZE 16

/* Two Wire Interface Master with DMA */
#define TWIM_PRESENT
#define TWIM_COUNT 4

#define TWIM0_EASYDMA_MAXCNT_SIZE 16
#define TWIM1_EASYDMA_MAXCNT_SIZE 16
#define TWIM2_EASYDMA_MAXCNT_SIZE 16
#define TWIM3_EASYDMA_MAXCNT_SIZE 16

/* Two Wire Interface Slave with DMA */
#define TWIS_PRESENT
#define TWIS_COUNT 4

#define TWIS0_EASYDMA_MAXCNT_SIZE 16
#define TWIS1_EASYDMA_MAXCNT_SIZE 16
#define TWIS2_EASYDMA_MAXCNT_SIZE 16
#define TWIS3_EASYDMA_MAXCNT_SIZE 16

/* Universal Asynchronous Receiver-Transmitter with DMA */
#define UARTE_PRESENT
#define UARTE_COUNT 4

#define UARTE0_EASYDMA_MAXCNT_SIZE 16
#define UARTE1_EASYDMA_MAXCNT_SIZE 16
#define UARTE2_EASYDMA_MAXCNT_SIZE 16
#define UARTE3_EASYDMA_MAXCNT_SIZE 16

/* Quadrature Decoder */
#define QDEC_PRESENT
#define QDEC_COUNT 2

/* Successive Approximation Analog to Digital Converter */
#define SAADC_PRESENT
#define SAADC_COUNT 1

#define SAADC_CH_NUM 8
#define SAADC_EASYDMA_MAXCNT_SIZE 15

/* GPIO Tasks and Events */
#define GPIOTE_PRESENT
#define GPIOTE_COUNT 2

#define GPIOTE_CH_NUM 8

#define GPIOTE_FEATURE_SET_PRESENT
#define GPIOTE_FEATURE_CLR_PRESENT

/* Low Power Comparator */
#define LPCOMP_PRESENT
#define LPCOMP_COUNT 1

#define LPCOMP_REFSEL_RESOLUTION 16

#define LPCOMP_FEATURE_HYST_PRESENT

/* Comparator */
#define COMP_PRESENT
#define COMP_COUNT 1

/* Pulse Width Modulator */
#define PWM_PRESENT
#define PWM_COUNT 4

#define PWM0_CH_NUM 4
#define PWM1_CH_NUM 4
#define PWM2_CH_NUM 4
#define PWM3_CH_NUM 4

#define PWM0_EASYDMA_MAXCNT_SIZE 15
#define PWM1_EASYDMA_MAXCNT_SIZE 15
#define PWM2_EASYDMA_MAXCNT_SIZE 15
#define PWM3_EASYDMA_MAXCNT_SIZE 15

/* ARM TrustZone Cryptocell 310 */
#define CRYPTOCELL_PRESENT
#define CRYPTOCELL_COUNT 1

/* Quad SPI */
#define QSPI_PRESENT
#define QSPI_COUNT 1

#define QSPI_EASYDMA_MAXCNT_SIZE 20

/* Mutex*/
#define MUTEX_PRESENT
#define MUTEX_COUNT 1

/* Key management Unit */
#define KMU_PRESENT
#define KMU_COUNT 1

/* Pulse density modulation */
#define PDM_PRESENT
#define PDM_COUNT 1

/* Secure Peripheral Unit */
#define SPU_PRESENT
#define SPU_COUNT 1

#define SPU_RAMREGION_SIZE 0x2000ul

/* Inter-IC Sound Interface */
#define I2S_PRESENT
#define I2S_COUNT 1

#define I2S_EASYDMA_MAXCNT_SIZE 14

/* Universal Serial Bus Device */
#define USBD_PRESENT
#define USBD_COUNT 1

#define USBD_EASYDMA_MAXCNT_SIZE 7

/* Oscillators */
#define OSCILLATORS_PRESENT
#define OSCILLATORS_COUNT 1

#endif      // _NRF5340_PERIPHERALS_H
