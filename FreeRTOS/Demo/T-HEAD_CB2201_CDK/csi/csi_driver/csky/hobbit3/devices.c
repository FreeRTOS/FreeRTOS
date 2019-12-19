/*
 * Copyright (C) 2017 C-SKY Microsystems Co., Ltd. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/******************************************************************************
 * @file     devices.c
 * @brief    source file for the devices
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#include <soc.h>
#include <config.h>
#include <drv_usart.h>
#include <stdio.h>
#include <drv_timer.h>
#include <drv_rtc.h>
#include <drv_trng.h>
#include <drv_crc.h>
#include <drv_aes.h>
#include <drv_rsa.h>
#include <drv_eflash.h>
#include <drv_spi.h>
#include <drv_gpio.h>

#include "pin_name.h"
#include "pinmux.h"

//typedef int32_t int32_t;

#define readl(addr) \
    ({ unsigned int __v = (*(volatile unsigned int *) (addr)); __v; })

#define writel(b,addr) (void)((*(volatile unsigned int *) (addr)) = (b))

#if 0
struct {
    uint32_t base;
    uint32_t irq;
}
const sg_usi_config[CONFIG_USI_NUM] = {
    {CSKY_USI0_BASE, USI0_IRQn},
    {CSKY_USI1_BASE, USI1_IRQn},
};
typedef struct {
    int32_t    sclk;
    int32_t    sd0;
    int32_t    sd1;
    int32_t    nss;
    uint16_t cfg_idx;    //idx of sg_usi_config[]
    uint16_t function;
} usi_pin_map_t;
const static usi_pin_map_t s_usi_pin_map[] = {
    {
        PA10_UART0CTS_USI0SCLK_SPU4_I2C0SCL,
        PA11_UART0RTS_USI0SD0_SPU5_I2C0SDA,
        PA12_XX_USI0SD1_XX_UART2RX,
        PA13_XX_USI0NSS_XX_UART2TX,
        0,
        1
    },
    {
        PA16_SPI0CS0_PWMTRIG0_XX_USI1SCLK,
        PA17_SPI0MOSI_PWMTRIG1_XX_USI1SD0,
        PA18_SPI0MISO_XX_SPU6_USI1SD1,
        PA19_SPI0SCK_FAULT_SPU7_USI1NSS,
        1,
        3
    },
};

#endif

struct {
    uint32_t base;
    uint32_t irq;
}
const static sg_usart_config[CONFIG_USART_NUM] = {
    {CSKY_UART0_BASE, UART0_IRQn},
    {CSKY_UART1_BASE, UART1_IRQn},
    {CSKY_UART2_BASE, UART2_IRQn},
    {CSKY_UART3_BASE, UART3_IRQn}
};
typedef struct {
    int32_t    tx;
    int32_t    rx;
#if 0
    int32_t    cts;
    int32_t    rts;
#endif
    uint16_t cfg_idx;    //idx of sg_usart_config[]
    uint16_t function;
} usart_pin_map_t;
const static usart_pin_map_t s_usart_pin_map[] = {
    {
        PA8_UART0TX_XX_SPU2_SIROUT0,
        PA9_UART0RX_XX_SPU3_SIRIN0,
        0,
        0
    },
    {
        PA21_UART1TX_PWM1_SPU9_SIROUT1,
        PA20_UART1RX_PWM0_SPU8_SIRIN1,
        1,
        0
    },
    {
        PA0_I2C0SCL_SPI1CS1_SPU0_UART1TX,
        PA1_I2C0SDA_SPI1CS2_SPU1_UART1RX,
        1,
        4,
    },
    {
        PB0_UART2TX_XX_XX_SIROUT2,
        PB1_UART2RX_XX_XX_SIRIN2,
        2,
        0
    },
    {
        PB13_UART3TX_SPI1MISO_SPU29_SIROUT3,
        PB12_UART3RX_SPI1CS0_SPU28_SIRIN3,
        3,
        0
    }
};

/**
  \param[in]   instance idx, must not exceed return value of target_get_usart_count()
  \brief       get usart instance.
  \return      pointer to usart instance
*/

int32_t target_usart_init(pin_t tx, pin_t rx, uint32_t *base, uint32_t *irq)
{
    uint32_t idx;

    for (idx = 0; idx < sizeof(s_usart_pin_map) / sizeof(usart_pin_map_t); idx++) {
        if (s_usart_pin_map[idx].tx == tx && s_usart_pin_map[idx].rx == rx) {
            *base = sg_usart_config[s_usart_pin_map[idx].cfg_idx].base;
            *irq = sg_usart_config[s_usart_pin_map[idx].cfg_idx].irq;
            /*pinmux*/
            pin_mux(s_usart_pin_map[idx].tx, s_usart_pin_map[idx].function);
            pin_mux(s_usart_pin_map[idx].rx, s_usart_pin_map[idx].function);
            return s_usart_pin_map[idx].cfg_idx;
        }
    }
    return -1;
}

/**
  \brief       control usart flow.
  \param[in]   tx_flow  The TX flow pin name
  \param[in]   rx_flow  The RX flow pin name
  \param[in]   flag 0-disable, 1-enable.
  \return      0 if setting ready ,negative for error code
*/
int32_t target_usart_flowctrl_init(int32_t tx_flow, int32_t rx_flow, uint32_t flag)
{
#if 0
    uint32_t idx;

    for (idx = 0; idx < sizeof(s_usart_pin_map) / sizeof(usart_pin_map_t); idx++) {
        if ((s_usart_pin_map[idx].cts == tx_flow) &&(s_usart_pin_map[idx].rts == rx_flow))
            break;
    }

    if (idx >= sizeof(s_usart_pin_map) / sizeof(usart_pin_map_t)) {
        return -1;
    }

    if ((s_usart_pin_map[idx].cts == tx_flow) && flag) {
        pin_mux(s_usart_pin_map[idx].cts, s_usart_pin_map[idx].function);
    } else if ((s_usart_pin_map[idx].cts == tx_flow) && (flag == 0)) {
        pin_mux(s_usart_pin_map[idx].cts, 0xff);
    } else {
        return -1;
    }

    if ((s_usart_pin_map[idx].rts == rx_flow) && flag) {
        pin_mux(s_usart_pin_map[idx].rts, s_usart_pin_map[idx].function);
    } else if ((s_usart_pin_map[idx].rts == rx_flow) && (flag == 0)) {
        pin_mux(s_usart_pin_map[idx].rts, 0xff);
    } else {
        return -1;
    }
    return 0;
#endif
    return 0;
}



struct {
    uint32_t base;
    uint32_t irq;
    uint32_t pin_num;
    port_name_t port;
}
const sg_gpio_config[CONFIG_GPIO_NUM] = {
    {CSKY_GPIO0_BASE, GPIOA_IRQn, 32, PORTA},
    {CSKY_GPIO1_BASE, GPIOB_IRQn, 16, PORTB}
};

typedef struct {
    int32_t    gpio_pin;
    uint32_t cfg_idx;    //idx of sg_gpio_config[]
} gpio_pin_map_t;
const static gpio_pin_map_t s_gpio_pin_map[] = {
    {PA0_I2C0SCL_SPI1CS1_SPU0_UART1TX ,0},
    {PA1_I2C0SDA_SPI1CS2_SPU1_UART1RX,0},
    {PA2_QSPI0CLK_XX_XX_XX,0},
    {PA3_QSPI0MISO_XX_XX_XX,0},
    {PA4_QSPI0MOSI_XX_XX_XX,0},
    {PA5_QSPI0HOLD_XX_XX_XX,0},
    {PA6_QSPI0WP_XX_XX_XX,0},
    {PA7_QSPI0CS0_XX_XX_XX,0},
    {PA8_UART0TX_XX_SPU2_SIROUT0,0},
    {PA9_UART0RX_XX_SPU3_SIRIN0,0},
    {PA10_UART0CTS_USI0SCLK_SPU4_I2C0SCL,0},
    {PA11_UART0RTS_USI0SD0_SPU5_I2C0SDA,0},
    {PA12_XX_USI0SD1_XX_UART2RX,0},
    {PA13_XX_USI0NSS_XX_UART2TX,0},
    {PA14_SPI0CS2_FAULT_I2C1SDA_XX,0},
    {PA15_SPI0CS1_XX_I2C1SCL_XX,0},
    {PA16_SPI0CS0_PWMTRIG0_XX_USI1SCLK,0},
    {PA17_SPI0MOSI_PWMTRIG1_XX_USI1SD0,0},
    {PA18_SPI0MISO_XX_SPU6_USI1SD1,0},
    {PA19_SPI0SCK_FAULT_SPU7_USI1NSS,0},
    {PA20_UART1RX_PWM0_SPU8_SIRIN1,0},
    {PA21_UART1TX_PWM1_SPU9_SIROUT1,0},
    {PA22_UART1CTS_PWM2_SPU10_XX,0},
    {PA23_UART1RTS_PWM3_SPU11_XX,0},
    {PA24_USI1NSS_PWM4_SPU12_XX,0},
    {PA25_USI1SD1_PWM5_SPU13_XX,0},
    {PA26_USI1SD0_PWM6_SPU14_XX,0},
    {PA27_USI1SCLK_PWM7_SPU15_XX,0},
    {PA28_I2C1SCL_PWM8_SPU16_XX,0},
    {PA29_I2C1SDA_PWM9_SPU17_XX,0},
    {PA30_I2C0SDA_PWM10_SPU18_XX,0},
    {PA31_I2C0SCL_PWM11_SPU19_XX,0},
    {PB0_UART2TX_XX_XX_SIROUT2,1},
    {PB1_UART2RX_XX_XX_SIRIN2,1},
    {PB2_UART2RTS_XX_XX_XX,1},
    {PB3_UART2CTS_XX_XX_XX,1},
    {PB4_XX_XX_SPU20_UART3TX,1},
    {PB5_QSPI1CS1_XX_SPU21_UART3RX,1},
    {PB6_QSPI1WP_XX_SPU22_XX,1},
    {PB7_QSPI1HOLD_XX_SPU23_XX,1},
    {PB8_QSPI1CS0_PWMTRIG0_SPU24_XX,1},
    {PB9_QSPI1MOSI_PWMTRIG1_SPU25_XX,1},
    {PB10_QSPI1MISO_XX_SPU26_I2C1SDA,1},
    {PB11_QSPI1CLK_XX_SPU27_I2C1SCL,1},
    {PB12_UART3RX_SPI1CS0_SPU28_SIRIN3,1},
    {PB13_UART3TX_SPI1MISO_SPU29_SIROUT3,1},
    {PB14_UART3RTS_SPI1MOSI_SPU30_XX,1},
    {PB15_UART3CTS_SPI1SCK_SPU31_XX,1}
};

int32_t target_gpio_port_init(port_name_t port, uint32_t *base, uint32_t *irq, uint32_t *pin_num)
{
    int i;

    for (i = 0; i < CONFIG_GPIO_NUM; i++) {
        if (sg_gpio_config[i].port == port) {
            *base = sg_gpio_config[i].base;
            *irq = sg_gpio_config[i].irq;
            *pin_num = sg_gpio_config[i].pin_num;
            return i;
        }
    }

    return -1;
}

/**
  \param[in]   instance idx, must not exceed return value of target_get_gpio_count()
  \brief       get gpio instance.
  \return      pointer to gpio instance
*/
int32_t target_gpio_pin_init(int32_t gpio_pin, uint32_t *port_idx)
{
    uint32_t idx;

    for (idx = 0; idx < sizeof(s_gpio_pin_map) / sizeof(gpio_pin_map_t); idx++) {
        if (s_gpio_pin_map[idx].gpio_pin == gpio_pin) {
            *port_idx = s_gpio_pin_map[idx].cfg_idx;
            /*pinmux*/
            pin_mux(s_gpio_pin_map[idx].gpio_pin, 0xff);
            return idx;
        }
    }

    return -1;
}

struct {
    uint32_t base;
    uint32_t irq;
}
const sg_timer_config[CONFIG_TIMER_NUM] = {
    {CSKY_TIM0_BASE, TIMA0_IRQn},
    {CSKY_TIM0_BASE + 0x14, TIMA1_IRQn},
    {CSKY_TIM1_BASE, TIMB0_IRQn},
    {CSKY_TIM1_BASE + 0x14, TIMB1_IRQn},
    {CSKY_TIM2_BASE, TIM34567_IRQn},
    {CSKY_TIM2_BASE + 0x14, TIM34567_IRQn},
    {CSKY_TIM3_BASE, TIM34567_IRQn},
    {CSKY_TIM3_BASE + 0x14, TIM34567_IRQn},
    {CSKY_TIM4_BASE, TIM34567_IRQn},
    {CSKY_TIM4_BASE + 0x14, TIM34567_IRQn},
    {CSKY_TIM5_BASE, TIM34567_IRQn},
    {CSKY_TIM5_BASE + 0x14, TIM34567_IRQn},
    {CSKY_TIM6_BASE, TIM34567_IRQn},
    {CSKY_TIM6_BASE + 0x14, TIM34567_IRQn},
};

int32_t target_get_timer_count(void)
{
    return CONFIG_TIMER_NUM;
}

int32_t target_get_timer(int32_t idx, uint32_t *base, uint32_t *irq)
{
    if (idx >= target_get_timer_count()) {
        return NULL;
    }

    *base = sg_timer_config[idx].base;
    *irq = sg_timer_config[idx].irq;
    return idx;
}

struct {
    uint32_t base;
    uint32_t irq;
}
const sg_sha_config[CONFIG_SHA_NUM] = {
    {CSKY_SHA_BASE, SHA_IRQn}
};

/**
  \brief       get sha instance count.
  \return      sha instance count
*/
int32_t target_get_sha_count(void)
{
    return CONFIG_SHA_NUM;
}

/**
  \param[in]   instance idx, must not exceed return value of target_get_sha_count()
  \brief       get sha instance.
  \return      pointer to sha instance
*/
int32_t target_get_sha(int32_t idx, uint32_t *base, uint32_t *irq)
{
    if (idx >= target_get_sha_count()) {
        return NULL;
    }

    *base = sg_sha_config[idx].base;
    *irq = sg_sha_config[idx].irq;
    return idx;
}

struct {
    uint32_t base;
    uint32_t irq;
}
const sg_rsa_config[CONFIG_RSA_NUM] = {
    {CSKY_RSA_BASE, RSA_IRQn}
};

/**
  \brief       get rsa instance count.
  \return      rsa instance count
*/
int32_t target_get_rsa_count(void)
{
    return CONFIG_RSA_NUM;
}

/**
  \param[in]   instance idx, must not exceed return value of target_get_rsa_count()
  \brief       get rsa instance.
  \return      pointer to rsa instance
*/
int32_t target_get_rsa(int32_t idx, uint32_t *base, uint32_t *irq)
{
    if (idx >= target_get_rsa_count()) {
        return NULL;
    }

    *base = sg_rsa_config[idx].base;
    *irq = sg_rsa_config[idx].irq;
    return idx;
}

struct {
    uint32_t base;
    uint32_t irq;
}
const sg_aes_config[CONFIG_AES_NUM] = {
    {CSKY_AES_BASE, AES_IRQn}
};

/**
  \brief       get aes instance count.
  \return      aes instance count
*/
int32_t target_get_aes_count(void)
{
    return CONFIG_AES_NUM;
}

/**
  \param[in]   instance idx, must not exceed return value of target_get_aes_count()
  \brief       get aes instance.
  \return      pointer to aes instance
*/
int32_t target_get_aes(int32_t idx, uint32_t *base, uint32_t *irq)
{
    if (idx >= target_get_aes_count()) {
        return NULL;
    }

    *base = sg_aes_config[idx].base;
    *irq = sg_aes_config[idx].irq;
    return idx;
}

struct {
    uint32_t base;
    uint32_t irq;
}
const sg_trng_config[CONFIG_TRNG_NUM] = {
    {CSKY_TRNG_BASE, TRNG_IRQn}
};

/**
  \param[in]   instance idx
  \brief       get trng instance.
  \return      pointer to trng instance
*/
int32_t target_get_trng(int32_t idx, uint32_t *base)
{
    *base = sg_trng_config[idx].base;

    return idx;
}

struct {
    uint32_t base;
}
const sg_crc_config[CONFIG_CRC_NUM] = {
    {CSKY_CRC_BASE}
};

/**
  \param[in]   instance idx
  \brief       get crc instance.
  \return      pointer to crc instance
*/
int32_t target_get_crc(int32_t idx, uint32_t *base)
{
    *base = sg_crc_config[idx].base;
    return idx;
}


struct {
    uint32_t base;
    uint32_t irq;
}
const sg_iic_config[CONFIG_IIC_NUM] = {
    {CSKY_I2C0_BASE, I2C0_IRQn},
    {CSKY_I2C1_BASE, I2C1_IRQn}
};

typedef struct {
    int32_t    scl;
    int32_t    sda;
    uint16_t cfg_idx;    //idx of sg_iic_config[]
    uint16_t function;
} iic_pin_map_t;
const static iic_pin_map_t s_iic_pin_map[] = {
    {
        PA31_I2C0SCL_PWM11_SPU19_XX,
        PA30_I2C0SDA_PWM10_SPU18_XX,
        0,
        0
    },
    {
        PA28_I2C1SCL_PWM8_SPU16_XX,
        PA29_I2C1SDA_PWM9_SPU17_XX,
        1,
        0
    }
};

/**
  \param[in]   instance idx, must not exceed return value of target_get_iic_count()
  \brief       get iic instance.
  \return      pointer to iic instance
*/
int32_t target_iic_init(int32_t idx, uint32_t *base, uint32_t *irq)
{
    if (idx >= sizeof(s_iic_pin_map) / sizeof(iic_pin_map_t)) {
        return -1;
    }

    *base = sg_iic_config[s_iic_pin_map[idx].cfg_idx].base;
    *irq = sg_iic_config[s_iic_pin_map[idx].cfg_idx].irq;
    /*pinmux*/
    pin_mux(s_iic_pin_map[idx].scl, s_iic_pin_map[idx].function);
    pin_mux(s_iic_pin_map[idx].sda, s_iic_pin_map[idx].function);
    return s_iic_pin_map[idx].cfg_idx;
}

#define BIT1 (0x1)
struct {
    uint32_t base;
    uint32_t irq;
}
const sg_rtc_config[CONFIG_RTC_NUM] = {
    {CSKY_RTC0_BASE, RTC_IRQn},

};

int32_t target_get_rtc_count(void)
{
    return CONFIG_RTC_NUM;
}

int32_t target_get_rtc(int32_t idx, uint32_t *base, uint32_t *irq)
{
    unsigned int value;

    if (idx >= target_get_rtc_count()) {
        return NULL;
    }

    value  = readl(CSKY_PMU_BASE);
    value &= ~BIT1;
    writel(value, CSKY_PMU_BASE);

    *base = sg_rtc_config[idx].base;
    *irq = sg_rtc_config[idx].irq;
    return idx;
}

struct {
    uint32_t base;
    uint32_t irq;
}

const sg_spi_config[CONFIG_SPI_NUM] = {
    {CSKY_SPI0_BASE, SPI0_IRQn},
    {CSKY_SPI1_BASE, SPI1_IRQn}
};
typedef struct {
    int32_t    mosi;
    int32_t    miso;
    int32_t    sclk;
    int32_t    ssel;
    uint32_t cfg_idx;    //idx of sg_iic_config[]
    uint16_t function;
} spi_pin_map_t;
const static spi_pin_map_t s_spi_pin_map[] = {
    {
        PA18_SPI0MISO_XX_SPU6_USI1SD1,
        PA17_SPI0MOSI_PWMTRIG1_XX_USI1SD0,
        PA19_SPI0SCK_FAULT_SPU7_USI1NSS,
        PA16_SPI0CS0_PWMTRIG0_XX_USI1SCLK,
        0,
        0
    },
    {
        PB13_UART3TX_SPI1MISO_SPU29_SIROUT3,
        PB14_UART3RTS_SPI1MOSI_SPU30_XX,
        PB15_UART3CTS_SPI1SCK_SPU31_XX,
        PB12_UART3RX_SPI1CS0_SPU28_SIRIN3,
        1,
        1
    }
};

/**
  \param[in]   instance idx, must not exceed return value of target_get_spi_count()
  \brief       get spi instance.
  \return      pointer to spi instance
*/
int32_t target_spi_init(int32_t idx, uint32_t *base, uint32_t *irq, uint32_t *ssel)
{
    if (idx >=  sizeof(s_spi_pin_map) / sizeof(spi_pin_map_t)) {
        return -1;
    }

    *base = sg_spi_config[s_spi_pin_map[idx].cfg_idx].base;
    *irq = sg_spi_config[s_spi_pin_map[idx].cfg_idx].irq;
    *ssel = s_spi_pin_map[idx].ssel;
    /*pinmux*/
    pin_mux(s_spi_pin_map[idx].mosi, s_spi_pin_map[idx].function);
    pin_mux(s_spi_pin_map[idx].miso, s_spi_pin_map[idx].function);
    pin_mux(s_spi_pin_map[idx].sclk, s_spi_pin_map[idx].function);
    pin_mux(s_spi_pin_map[idx].ssel, s_spi_pin_map[idx].function);

    return s_spi_pin_map[idx].cfg_idx;

}

struct {
    uint32_t base;
    uint32_t irq;
}
const sg_dmac_config[CONFIG_DMAC_NUM] = {
    {CSKY_DMAC0_BASE, DMAC_IRQn},
};

int32_t target_get_dmac_count(void)
{
    return CONFIG_DMAC_NUM;
}

int32_t target_get_dmac(int32_t idx, uint32_t *base, uint32_t *irq)
{
    if (idx >= target_get_dmac_count()) {
        return NULL;
    }

    *base = sg_dmac_config[idx].base;
    *irq = sg_dmac_config[idx].irq;
    return idx;
}

struct {
    uint32_t base;
    uint32_t irq;
}
const sg_pwm_config[CONFIG_PWM_NUM] = {
    {CSKY_PWM_BASE, PWM_IRQn},
};

typedef struct {
    int32_t    pwm_pin;
    uint32_t cfg_idx;    //idx of sg_pwm_config[]
    uint32_t ch_num;
    uint16_t function;
} pwm_pin_map_t;
const static pwm_pin_map_t s_pwm_pin_map[] = {
    {PA20_UART1RX_PWM0_SPU8_SIRIN1, 0, 0, 1},
    {PA21_UART1TX_PWM1_SPU9_SIROUT1, 0, 1, 1},
    {PA22_UART1CTS_PWM2_SPU10_XX, 0, 2, 1},
    {PA23_UART1RTS_PWM3_SPU11_XX, 0, 3, 1},
    {PA24_USI1NSS_PWM4_SPU12_XX, 0, 4, 1},
    {PA25_USI1SD1_PWM5_SPU13_XX, 0, 5, 1},
    {PA26_USI1SD0_PWM6_SPU14_XX, 0, 6, 1},
    {PA27_USI1SCLK_PWM7_SPU15_XX, 0, 7, 1},
    {PA28_I2C1SCL_PWM8_SPU16_XX, 0, 8, 1},
    {PA29_I2C1SDA_PWM9_SPU17_XX, 0, 9, 1},
    {PA30_I2C0SDA_PWM10_SPU18_XX, 0, 10, 1},
    {PA31_I2C0SCL_PWM11_SPU19_XX, 0, 11, 1}
};

/**
  \param[in]   instance idx, must not exceed return value of target_get_pwm_count()
  \brief       get pwm instance.
  \return      pointer to pwm instance
*/
int32_t target_pwm_init(int32_t pwm_pin, uint32_t *ch_num, uint32_t *base, uint32_t *irq)
{
    uint32_t idx;

    for (idx = 0; idx < sizeof(s_pwm_pin_map) / sizeof(pwm_pin_map_t); idx++) {
        if (s_pwm_pin_map[idx].pwm_pin == pwm_pin) {
            *base = sg_pwm_config[s_pwm_pin_map[idx].cfg_idx].base;
            *irq = sg_pwm_config[s_pwm_pin_map[idx].cfg_idx].irq;
            *ch_num = s_pwm_pin_map[idx].ch_num;
            /*pinmux*/
            pin_mux(s_pwm_pin_map[idx].pwm_pin, s_pwm_pin_map[idx].function);
            return s_pwm_pin_map[idx].cfg_idx;
        }
    }

    return -1;
}

struct {
    uint32_t base;
    uint32_t irq;
}
const sg_wdt_config[CONFIG_WDT_NUM] = {
    {CSKY_WDT_BASE, WDT_IRQn}
};

int32_t target_get_wdt_count(void)
{
    return CONFIG_WDT_NUM;
}

int32_t target_get_wdt(int32_t idx, uint32_t *base, uint32_t *irq)
{
    if (idx >= target_get_wdt_count()) {
        return NULL;
    }

    *base = sg_wdt_config[idx].base;
    *irq = sg_wdt_config[idx].irq;
    return idx;
}

int32_t target_get_etb_count(void)
{
    return CONFIG_ETB_NUM;
}

int32_t target_get_etb(int32_t idx, uint32_t *base, uint32_t *irq)
{
    if (idx >= target_get_etb_count()) {
        return NULL;
    }

//    *base = sg_etb_config[idx].base;
//    *irq = sg_etb_config[idx].irq;
    return 0;
}

struct {
    uint32_t base;
    uint32_t irq;
}
const sg_qspi_config[CONFIG_QSPI_NUM] = {
    {CSKY_QSPIC0_BASE, QSPIC1_IRQn},
    {CSKY_QSPIC1_BASE, QSPIC1_IRQn}
};
typedef struct {
    pin_name_t    sclk;
    pin_name_t    miso;
    pin_name_t    mosi;
    pin_name_t    hold;
    pin_name_t    wp;
    pin_name_t    ssel;
    uint32_t cfg_idx;
    uint16_t function;
} qspi_pin_map_t;
const static qspi_pin_map_t s_qspi_pin_map[] = {
    {
        PA2_QSPI0CLK_XX_XX_XX,
        PA3_QSPI0MISO_XX_XX_XX,
        PA4_QSPI0MOSI_XX_XX_XX,
        PA5_QSPI0HOLD_XX_XX_XX,
        PA6_QSPI0WP_XX_XX_XX,
        PA7_QSPI0CS0_XX_XX_XX,
        0,
        0
    },
    {
        PB11_QSPI1CLK_XX_SPU27_I2C1SCL,
        PB10_QSPI1MISO_XX_SPU26_I2C1SDA,
        PB9_QSPI1MOSI_PWMTRIG1_SPU25_XX,
        PB7_QSPI1HOLD_XX_SPU23_XX,
        PB6_QSPI1WP_XX_SPU22_XX,
        PB8_QSPI1CS0_PWMTRIG0_SPU24_XX,
        1,
        0
    }
};

/**
  \param[in]   instance idx, must not exceed return value of target_get_qspi_count()
  \brief       get qspi instance.
  \return      pointer to qspi instance
*/
int32_t target_qspi_init(pin_name_t mosi, pin_name_t miso, pin_name_t sclk, pin_name_t ssel, pin_name_t wp, pin_name_t hold, uint32_t *base, uint32_t *irq)
{
    uint32_t idx;

    for (idx = 0; idx < sizeof(s_qspi_pin_map) / sizeof(qspi_pin_map_t); idx++) {
        if (s_qspi_pin_map[idx].mosi == mosi && s_qspi_pin_map[idx].miso == miso
            && s_qspi_pin_map[idx].sclk == sclk && s_qspi_pin_map[idx].ssel == ssel
            && s_qspi_pin_map[idx].hold == hold && s_qspi_pin_map[idx].wp == wp) {

            pin_mux(s_qspi_pin_map[idx].mosi, s_qspi_pin_map[idx].function);
            pin_mux(s_qspi_pin_map[idx].miso, s_qspi_pin_map[idx].function);
            pin_mux(s_qspi_pin_map[idx].sclk, s_qspi_pin_map[idx].function);
            pin_mux(s_qspi_pin_map[idx].hold, s_qspi_pin_map[idx].function);
            pin_mux(s_qspi_pin_map[idx].wp, s_qspi_pin_map[idx].function);
            pin_mux(s_qspi_pin_map[idx].ssel, s_qspi_pin_map[idx].function);
            return s_qspi_pin_map[idx].cfg_idx;
        }
    }
    return -1;
}
