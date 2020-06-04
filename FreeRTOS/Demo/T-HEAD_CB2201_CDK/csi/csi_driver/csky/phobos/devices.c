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
#include "soc.h"
#include "config.h"
#include <drv_usart.h>
#include <drv_trng.h>
#include <drv_crc.h>
#include <drv_aes.h>
#include <drv_rsa.h>
#include <drv_eflash.h>
#include <drv_timer.h>
#include <drv_gpio.h>
#include <drv_iic.h>
#include <drv_rtc.h>
#include <drv_spi.h>
#include <drv_wdt.h>
#include <drv_sha.h>
#include <drv_pwm.h>
#include <drv_dmac.h>
#include <stdio.h>


#include "pin_name.h"
#include "pinmux.h"

//typedef int32_t pin_t;


#if CONFIG_IIC


struct {
    uint32_t base;
    uint32_t irq;
}
const sg_iic_config[CONFIG_IIC_NUM] = {
    {CSKY_I2C0_BASE, I2C0_IRQn},
    {CSKY_I2C1_BASE, I2C1_IRQn}
};


typedef struct {
    pin_t    scl;
    pin_t    sda;
    uint16_t cfg_idx;    //idx of sg_iic_config[]
    uint16_t function;
    //uint32_t scl_reg;
    //uint32_t scl_cfg;
    //uint32_t sda_reg;
    //uint32_t sda_cfg;
} iic_pin_map_t;
const static iic_pin_map_t s_iic_pin_map[] = {
    {
        PA4_SCL0_PWM4_SPI0RX_XX,
        PA5_SDA0_PWM5_SPI0CS_XX,
        0,
        0
    },
    {
        PA6_SPI0CLK_PWMTRIG0_SCL0_XX,
        PA7_SPI0TX_PWMTRIG1_SDA0_XX,
        0,
        2
    },
    {
        PA31_I2SSDA__SCL0_PWM4_XX,
        PB0_ADC0_SDA0_PWM5_XX,
        0,
        1
    },
    {
        PA8_SPI0RX_TRIGFAULT_SCL1_XX,
        PA9_SPI0CS_PWM0_SDA1_XX,
        1,
        2
    },
    {
        PA14_SCL1_PWM5_SPI1RX_XX,
        PA15_SDA1_PWMTRIG0_SPI1CS0_XX,
        1,
        0
    },
    {
        PB1_ADC1_SCL1_USISCLK_XX,
        PB2_ADC2_SDA1_USISD0_XX,
        1,
        1
    }
};


/**
  \param[in]   instance idx, must not exceed return value of target_get_iic_count()
  \brief       get iic instance.
  \return      pointer to iic instance
*/
int32_t target_iic_init(pin_t scl, pin_t sda, uint32_t *base, uint32_t *irq)
{
    uint32_t idx;

    for (idx = 0; idx < sizeof(s_iic_pin_map) / sizeof(iic_pin_map_t); idx++) {
        if (s_iic_pin_map[idx].scl == scl && s_iic_pin_map[idx].sda == sda) {
            *base = sg_iic_config[s_iic_pin_map[idx].cfg_idx].base;
            *irq = sg_iic_config[s_iic_pin_map[idx].cfg_idx].irq;
            /*pinmux*/
            pin_mux(s_iic_pin_map[idx].scl, s_iic_pin_map[idx].function);
            pin_mux(s_iic_pin_map[idx].sda, s_iic_pin_map[idx].function);
            return s_iic_pin_map[idx].cfg_idx;
        }
    }

    return -1;
}


#endif

#if CONFIG_USART
struct {
    uint32_t base;
    uint32_t irq;
}
const sg_usart_config[CONFIG_USART_NUM] = {
    {CSKY_UART0_BASE, UART0_IRQn},
    {CSKY_UART1_BASE, UART1_IRQn},
    {CSKY_UART2_BASE, UART2_IRQn},
    {CSKY_UART3_BASE, UART3_IRQn}
};
typedef struct {
    pin_t    tx;
    pin_t    rx;
    pin_t    cts;
    pin_t    rts;
    uint16_t cfg_idx;    //idx of sg_usart_config[]
    uint16_t function;
} usart_pin_map_t;
const static usart_pin_map_t s_usart_pin_map[] = {
    {
        PA0_TXD0_PWM0_XX_SIROUT0,
        PA1_RXD0_PWM1_XX_SIRIN0,
        -1,
        -1,
        0,
        0
    },
    {
        PA10_TXD1_PWM1_XX_SIROUT1,
        PA11_RXD1_PWM2_XX_SIRIN1,
        -1,
        -1,
        1,
        0
    },
    {
        PA23_TXD2_PWM5_XX_SIROUT2,
        PA22_RXD2_PWM4_XX_SIRIN2,
        PA24_CTS2_PWMTRIG0_SPI1CS1_XX,
        PA25_XX_PWMTRIG1_SPI1CS2_XX,
        2,
        0
    },
    {
        PA26_TXD3_PWMFAULT_XX_SIROUT3,
        PA27_RXD3_PWM0_XX_SIRIN3,
        -1,
        -1,
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
int32_t target_usart_flowctrl_init(pin_t tx_flow, pin_t rx_flow, uint32_t flag)
{
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
}

#endif

#if CONFIG_TRNG
struct {
    uint32_t base;
}
const sg_trng_config[CONFIG_TRNG_NUM] = {
    {CSKY_TRNG_BASE}
};

/**
  \brief       get trng instance count.
  \return      trng instance count
*/
int32_t target_get_trng_count(void)
{
    return CONFIG_TRNG_NUM;
}

/**
  \param[in]   instance idx, must not exceed return value of target_get_trng_count()
  \brief       get trng instance.
  \return      pointer to trng instance
*/
int32_t target_get_trng(int32_t idx, uint32_t *base)
{
    if (idx >= target_get_trng_count()) {
        return NULL;
    }

    *base = sg_trng_config[idx].base;
    return idx;
}

#endif

#if CONFIG_CRC
struct {
    uint32_t base;
}
const sg_crc_config[CONFIG_CRC_NUM] = {
    {CSKY_CRC_BASE}
};

/**
  \brief       get crc instance count.
  \return      crc instance count
*/
int32_t target_get_crc_count(void)
{
    return CONFIG_CRC_NUM;
}

/**
  \param[in]   instance idx, must not exceed return value of target_get_crc_count()
  \brief       get crc instance.
  \return      pointer to crc instance
*/
int32_t target_get_crc(int32_t idx, uint32_t *base)
{
    if (idx >= target_get_crc_count()) {
        return NULL;
    }

    *base = sg_crc_config[idx].base;
    return idx;
}

#endif


#if CONFIG_EFLASH
struct {
    uint32_t base;
    eflash_info info;
}
const sg_eflash_config[CONFIG_EFLASH_NUM] = {
    {CSKY_EFLASH_CONTROL_BASE, {0x10000000, 0x1003f800, 0x1fc}}
};

/**
  \brief       get eflash instance count.
  \return      eflash instance count
*/
int32_t target_get_eflash_count(void)
{
    return CONFIG_EFLASH_NUM;
}

/**
  \param[in]   instance idx, must not exceed return value of target_get_eflash_count()
  \brief       get eflash instance.
  \return      pointer to eflash instance
*/
int32_t target_get_eflash(int32_t idx, uint32_t *base, eflash_info *info)
{
    if (idx >= target_get_eflash_count()) {
        return NULL;
    }

    *base = sg_eflash_config[idx].base;
    info->start = sg_eflash_config[idx].info.start;
    info->end = sg_eflash_config[idx].info.end;
    info->sector_count = sg_eflash_config[idx].info.sector_count;
    return idx;
}

#endif

#if CONFIG_TIMER
struct {
    uint32_t base;
    uint32_t irq;
}
const sg_timer_config[CONFIG_TIMER_NUM] = {
    {CSKY_TIMERA0_BASE, TIMA0_IRQn},
    {CSKY_TIMERA1_BASE, TIMA1_IRQn},
    {CSKY_TIMERB0_BASE, TIMB0_IRQn},
    {CSKY_TIMERB1_BASE, TIMB1_IRQn}
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

#endif

#if CONFIG_GPIO
struct {
    uint32_t base;
    uint32_t irq;
    uint32_t pin_num;
    port_name_t port;
}
const sg_gpio_config[CONFIG_GPIO_NUM] = {
    {CSKY_GPIOA_BASE, GPIOA_IRQn, 32, PORTA},
    {CSKY_GPIOB_BASE, GPIOB_IRQn, 11, PORTB}
};

typedef struct {
    pin_t    gpio_pin;
    uint32_t cfg_idx;    //idx of sg_gpio_config[]
} gpio_pin_map_t;
const static gpio_pin_map_t s_gpio_pin_map[] = {
    {PA0_TXD0_PWM0_XX_SIROUT0, 0},
    {PA1_RXD0_PWM1_XX_SIRIN0, 0},
    {PA2_CTS0_PWM2_SPI0CLK_XX, 0},
    {PA3_RTS0_PWM3_SPI0TX_XX, 0},
    {PA4_SCL0_PWM4_SPI0RX_XX, 0},
    {PA5_SDA0_PWM5_SPI0CS_XX, 0},
    {PA6_SPI0CLK_PWMTRIG0_SCL0_XX, 0},
    {PA7_SPI0TX_PWMTRIG1_SDA0_XX, 0},
    {PA8_SPI0RX_TRIGFAULT_SCL1_XX, 0},
    {PA9_SPI0CS_PWM0_SDA1_XX, 0},
    {PA10_TXD1_PWM1_XX_SIROUT1, 0},
    {PA11_RXD1_PWM2_XX_SIRIN1, 0},
    {PA12_CTS1_PWM3_SPI1CLK_XX, 0},
    {PA13_RTS1_PWM4_SPI1TX_XX, 0},
    {PA14_SCL1_PWM5_SPI1RX_XX, 0},
    {PA15_SDA1_PWMTRIG0_SPI1CS0_XX, 0},
    {PA16_SPI1CLK_PWMTRIG1_XX_XX, 0},
    {PA17_SPI1TX_PWMFAULT_XX_XX, 0},
    {PA18_SPI1RX_PWM0_XX_XX, 0},
    {PA19_SPI1CS0_PWM1_XX_XX, 0},
    {PA20_SPI1CS1_PWM2_XX_XX, 0},
    {PA21_SPI1CS2_PWM3_XX_XX, 0},
    {PA22_RXD2_PWM4_XX_SIRIN2, 0},
    {PA23_TXD2_PWM5_XX_SIROUT2, 0},
    {PA24_CTS2_PWMTRIG0_SPI1CS1_XX, 0},
    {PA25_XX_PWMTRIG1_SPI1CS2_XX, 0},
    {PA26_TXD3_PWMFAULT_XX_SIROUT3, 0},
    {PA27_RXD3_PWM0_XX_SIRIN3, 0},
    {PA28_I2SMCLK_PWM1_XX_XX, 0},
    {PA29_I2SSCLK_PWM2_XX_XX, 0},
    {PA30_I2SWSCLK_PWM3_XX_XX, 0},
    {PA31_I2SSDA__SCL0_PWM4_XX, 0},
    {PB0_ADC0_SDA0_PWM5_XX, 1},
    {PB1_ADC1_SCL1_USISCLK_XX, 1},
    {PB2_ADC2_SDA1_USISD0_XX, 1},
    {PB3_ADC3_SPI1CLK_USISD1_XX, 1},
    {PB4_ADC4_SPI1TX_USINSS_XX, 1},
    {PB5_ADC5_SPI1RX_USISCLK_XX, 1},
    {PB6_ADC6_SPI1CS0_USISD0_XX, 1},
    {PB7_ADC7_SPI1CS1_USISD1_XX, 1},
    {PB8_PWMTRIG0_SPI1CS2_USINSS_XX, 1},
    {PB9_PWMTRIG1_CTS3_XX_XX, 1},
    {PB10_PWMFAULT_RTS3_XX_XX, 1}
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
int32_t target_gpio_pin_init(pin_t gpio_pin, uint32_t *port_idx)
{
    uint32_t idx;

    for (idx = 0; idx < sizeof(s_gpio_pin_map) / sizeof(gpio_pin_map_t); idx++) {
        if (s_gpio_pin_map[idx].gpio_pin == gpio_pin) {
            *port_idx = s_gpio_pin_map[idx].cfg_idx;
            /*pinmux*/
            pin_mux(s_gpio_pin_map[idx].gpio_pin, 0xff);
            if (idx >= 32) {
                return idx-32;
            }
            return idx;
        }
    }

    return -1;
}

#endif

#if CONFIG_AES
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

#endif


#if CONFIG_RSA
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

#endif

#if CONFIG_RTC
struct {
    uint32_t base;
    uint32_t irq;
}
const sg_rtc_config[CONFIG_RTC_NUM] = {
    {CSKY_RTC_BASE, RTC_IRQn}
};

int32_t target_get_rtc_count(void)
{
    return CONFIG_RTC_NUM;
}

int32_t target_get_rtc(int32_t idx, uint32_t *base, uint32_t *irq)
{
    if (idx >= target_get_rtc_count()) {
        return NULL;
    }

    *base = sg_rtc_config[idx].base;
    *irq = sg_rtc_config[idx].irq;
    return idx;
}

#endif

#if CONFIG_SPI
struct {
    uint32_t base;
    uint32_t irq;
}

const sg_spi_config[CONFIG_SPI_NUM] = {
    {CSKY_SPI0_BASE, SPI0_IRQn},
    {CSKY_SPI1_BASE, SPI1_IRQn}
};
typedef struct {
    pin_t    mosi;
    pin_t    miso;
    pin_t    sclk;
    pin_t    ssel;
    uint32_t cfg_idx;    //idx of sg_iic_config[]
    uint16_t function;
} spi_pin_map_t;
const static spi_pin_map_t s_spi_pin_map[] = {
    {
        PA7_SPI0TX_PWMTRIG1_SDA0_XX,
        PA8_SPI0RX_TRIGFAULT_SCL1_XX,
        PA6_SPI0CLK_PWMTRIG0_SCL0_XX,
        PA9_SPI0CS_PWM0_SDA1_XX,
        0,
        0
    },
    {
        PA17_SPI1TX_PWMFAULT_XX_XX,
        PA18_SPI1RX_PWM0_XX_XX,
        PA16_SPI1CLK_PWMTRIG1_XX_XX,
        PA19_SPI1CS0_PWM1_XX_XX,
        1,
        0
    },
    {
        PA13_RTS1_PWM4_SPI1TX_XX,
        PA14_SCL1_PWM5_SPI1RX_XX,
        PA12_CTS1_PWM3_SPI1CLK_XX,
        PA15_SDA1_PWMTRIG0_SPI1CS0_XX,
        1,
        2
    },
    {
        PB4_ADC4_SPI1TX_USINSS_XX,
        PB5_ADC5_SPI1RX_USISCLK_XX,
        PB3_ADC3_SPI1CLK_USISD1_XX,
        PB6_ADC6_SPI1CS0_USISD0_XX,
        1,
        1
    }
};

/**
  \param[in]   instance idx, must not exceed return value of target_get_spi_count()
  \brief       get spi instance.
  \return      pointer to spi instance
*/
int32_t target_spi_init(pin_t mosi, pin_t miso, pin_t sclk, pin_t ssel, uint32_t *base, uint32_t *irq)
{
    uint32_t idx;

    for (idx = 0; idx < sizeof(s_spi_pin_map) / sizeof(spi_pin_map_t); idx++) {
        if (s_spi_pin_map[idx].mosi == mosi && s_spi_pin_map[idx].miso == miso
            && s_spi_pin_map[idx].sclk == sclk && s_spi_pin_map[idx].ssel == ssel) {
            *base = sg_spi_config[s_spi_pin_map[idx].cfg_idx].base;
            *irq = sg_spi_config[s_spi_pin_map[idx].cfg_idx].irq;
            /*pinmux*/
            pin_mux(s_spi_pin_map[idx].mosi, s_spi_pin_map[idx].function);
            pin_mux(s_spi_pin_map[idx].miso, s_spi_pin_map[idx].function);
            pin_mux(s_spi_pin_map[idx].sclk, s_spi_pin_map[idx].function);
            pin_mux(s_spi_pin_map[idx].ssel, s_spi_pin_map[idx].function);

            return s_spi_pin_map[idx].cfg_idx;
        }
    }

    return -1;

}

#endif

#if CONFIG_WDT
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
#endif


#if CONFIG_SHA
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

#endif

#if CONFIG_PWM
struct {
    uint32_t base;
    uint32_t irq;
}
const sg_pwm_config[CONFIG_PWM_NUM] = {
    {CSKY_PWM_BASE, PWM_IRQn},
};

typedef struct {
    pin_t    pwm_pin;
    uint32_t cfg_idx;    //idx of sg_pwm_config[]
    uint32_t ch_num;
    uint16_t function;
} pwm_pin_map_t;
const static pwm_pin_map_t s_pwm_pin_map[] = {
    {PA0_TXD0_PWM0_XX_SIROUT0, 0, 0, 1},
    {PA9_SPI0CS_PWM0_SDA1_XX, 0, 0, 1},
    {PA18_SPI1RX_PWM0_XX_XX, 0, 0, 1},
    {PA27_RXD3_PWM0_XX_SIRIN3, 0, 0, 1},

    {PA1_RXD0_PWM1_XX_SIRIN0, 0, 1, 1},
    {PA10_TXD1_PWM1_XX_SIROUT1, 0, 1, 1},
    {PA19_SPI1CS0_PWM1_XX_XX, 0, 1, 1},
    {PA28_I2SMCLK_PWM1_XX_XX, 0, 1, 1},

    {PA2_CTS0_PWM2_SPI0CLK_XX, 0, 2, 1},
    {PA11_RXD1_PWM2_XX_SIRIN1, 0, 2, 1},
    {PA20_SPI1CS1_PWM2_XX_XX, 0, 2, 1},
    {PA29_I2SSCLK_PWM2_XX_XX, 0, 2, 1},

    {PA3_RTS0_PWM3_SPI0TX_XX, 0, 3, 1},
    {PA12_CTS1_PWM3_SPI1CLK_XX, 0, 3, 1},
    {PA21_SPI1CS2_PWM3_XX_XX, 0, 3, 1},
    {PA30_I2SWSCLK_PWM3_XX_XX, 0, 3, 1},

    {PA4_SCL0_PWM4_SPI0RX_XX, 0, 4, 1},
    {PA13_RTS1_PWM4_SPI1TX_XX, 0, 4, 1},
    {PA22_RXD2_PWM4_XX_SIRIN2, 0, 4, 1},
    {PA31_I2SSDA__SCL0_PWM4_XX, 0, 4, 1},

    {PA5_SDA0_PWM5_SPI0CS_XX, 0, 5, 1},
    {PA14_SCL1_PWM5_SPI1RX_XX, 0, 5, 1},
    {PA23_TXD2_PWM5_XX_SIROUT2, 0, 5, 1},
    {PB0_ADC0_SDA0_PWM5_XX, 0, 5, 1},
};

/**
  \param[in]   instance idx, must not exceed return value of target_get_pwm_count()
  \brief       get pwm instance.
  \return      pointer to pwm instance
*/
int32_t target_pwm_init(pin_t pwm_pin, uint32_t *ch_num, uint32_t *base, uint32_t *irq)
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


#endif


#if CONFIG_DMAC
struct {
    uint32_t base;
    uint32_t irq;
}
const sg_dmac_config[CONFIG_DMAC_NUM] = {
    {CSKY_DMA_BASE, DMAC_IRQn},
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
#endif

