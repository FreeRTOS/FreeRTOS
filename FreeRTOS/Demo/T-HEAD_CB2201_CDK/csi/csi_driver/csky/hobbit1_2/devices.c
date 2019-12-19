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
 * @date     24. August 2017
 ******************************************************************************/
#include "soc.h"
#include "config.h"
#include <drv_usart.h>
#include <drv_timer.h>
#include <drv_rtc.h>
#include <drv_trng.h>
#include <drv_crc.h>
#include <drv_aes.h>
#include <drv_rsa.h>
#include <drv_eflash.h>
#include <drv_spi.h>
#include <drv_gpio.h>

#include <stdio.h>

#include "pin_name.h"
#include "pinmux.h"

#define readl(addr) \
    ({ unsigned int __v = (*(volatile unsigned int *) (addr)); __v; })

#define writel(b,addr) (void)((*(volatile unsigned int *) (addr)) = (b))


#if CONFIG_GPIO
struct {
    uint32_t base;
    uint32_t irq;
    uint32_t pin_num;
    port_name_t port;
}
const sg_gpio_config[CONFIG_GPIO_NUM] = {
    {CSKY_GPIO0_BASE, GPIOA_IRQn, 28, PORTA},
    {CSKY_GPIO1_BASE, GPIOB_IRQn, 4, PORTB},
};

typedef struct {
    pin_t    gpio_pin;
    uint32_t cfg_idx;    //idx of sg_gpio_config[]
} gpio_pin_map_t;
const static gpio_pin_map_t s_gpio_pin_map[] = {
        {PA0_TRIG0_ACMP1P_TCK, 0},
        {PA1_TRIG1_ACMP1N_TMS, 0},
        {PA2_TXD0_SPI0MISO, 0},
        {PA3_RXD0_SPI0MOSI, 0},
        {PA4_CTS0_PWM0_SPI0SCK_TRIG0, 0},
        {PA5_RTS0_PWM1_SPI0SSN_TRIG1, 0},

        {PB0_SCL0_PWM2_I2SMCLK, 1},
        {PB1_SDA0_PWM3_I2SSCK, 1},
        {PB2_SPI0SCK_PWM4_I2SWS, 1},
        {PB3_SPI0MISO_PWM5_I2SSD, 1},

        {PA6_SPI0MOSI_PWM6_SCL0, 0},
        {PA7_SPI0SSN_PWM7_SDA0, 0},
        {PA8_WKUP_ADC0_ACMP0P, 0},
        {PA9_BOOT_ADC1_PWMFAULT, 0},
        {PA10_ADC2_TXD0, 0},
        {PA11_ACMP0N_ADC3_RXD0, 0},
        {PA12_PWM8_TCK_ADC4, 0},
        {PA13_PWM9_TMS_ADC5, 0},
        {PA14_PWM10_ADC6, 0},
        {PA15_PWM11_ADC7, 0},
        {PA16_RXD1_ADC8, 0},
        {PA17_TXD1_ADC9, 0},
        {PA18_SPI1SSN0_ACMP0O, 0},
        {PA19_SPI1SSN1_ACMP1O, 0},
        {PA20_SPI1SSN2_TRIG0_RXD1, 0},
        {PA21_SPI1SCK_TRIG1_TXD1, 0},
        {PA22_SPI1MISO_PWM0_ADC10, 0},
        {PA23_SPI1MOSI_PWM1_ADC11, 0},
        {PA24_TXD2_I2SMCLK_SPI1SSN0, 0},
        {PA25_RXD2_I2SSCK_SPI1SSN1, 0},
        {PA26_CTS2_I2SWS_ADC12, 0},
        {PA27_RTS2_I2SSD_ADC13, 0}
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
            if (idx >= 10) {
                return idx - 4;
            } else if (idx >= 6) {
                return idx - 6;
            } else {
                return idx;
            }
        }
    }

    return -1;
}

#endif

#if CONFIG_TIMER
struct {
    uint32_t base;
    uint32_t irq;
}
const sg_timer_config[CONFIG_TIMER_NUM] = {
    {CSKY_TIM0_BASE, TIMA0_IRQn},
    {CSKY_TIM0_BASE + 0x14, TIMA1_IRQn},
    {CSKY_TIM1_BASE, TIMB0_IRQn},
    {CSKY_TIM1_BASE + 0x14, TIMB1_IRQn}

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

#if CONFIG_PMU
struct {
    uint32_t base;
    uint32_t irq;
}
const sg_pmu_config[CONFIG_PMU_NUM] = {
    {CSKY_CLKGEN_BASE, POWM_IRQn}
};

int32_t target_get_pmu(int32_t idx, uint32_t *base, uint32_t *irq)
{
    if (idx > CONFIG_PMU_NUM) {
        return -1;
    }
    *base = sg_pmu_config[idx].base;
    *irq = sg_pmu_config[idx].irq;
    return idx;
}
#endif

#if CONFIG_RTC
#undef  CSKY_PMU_BASE
#define CSKY_PMU_BASE  0x40002000
#define BIT1 (0x1)
struct {
    uint32_t base;
    uint32_t irq;
}
const sg_rtc_config[CONFIG_RTC_NUM] = {
    {CSKY_RTC0_BASE, RTC_IRQn},
    {CSKY_RTC1_BASE, RTC1_IRQn}

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

#if CONFIG_USART
struct {
    uint32_t base;
    uint32_t irq;
}
const sg_usart_config[CONFIG_USART_NUM] = {
    {CSKY_UART0_BASE, UART0_IRQn},
    {CSKY_UART1_BASE, UART1_IRQn},
    {CSKY_UART2_BASE, UART2_IRQn},
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
        PA2_TXD0_SPI0MISO,
        PA3_RXD0_SPI0MOSI,
        -1,
        -1,
        0,
        0
    },
    {
        PA10_ADC2_TXD0,
        PA11_ACMP0N_ADC3_RXD0,
        -1,
        -1,
        0,
        2
    },
    {
        PA17_TXD1_ADC9,
        PA16_RXD1_ADC8,
        -1,
        -1,
        1,
        0
    },
    {
        PA21_SPI1SCK_TRIG1_TXD1,
        PA20_SPI1SSN2_TRIG0_RXD1,
        -1,
        -1,
        1,
        2,
    },
    {
        PA24_TXD2_I2SMCLK_SPI1SSN0,
        PA25_RXD2_I2SSCK_SPI1SSN1,
        PA26_CTS2_I2SWS_ADC12,
        PA27_RTS2_I2SSD_ADC13,
        2,
        0
    },
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
        PA2_TXD0_SPI0MISO,
        PA3_RXD0_SPI0MOSI,
        PA4_CTS0_PWM0_SPI0SCK_TRIG0,
        PA5_RTS0_PWM1_SPI0SSN_TRIG1,
        0,
        2
    },
    {
        PB3_SPI0MISO_PWM5_I2SSD,
        PA6_SPI0MOSI_PWM6_SCL0,
        PB2_SPI0SCK_PWM4_I2SWS,
        PA7_SPI0SSN_PWM7_SDA0,
        0,
        0
    },
    {
        PA22_SPI1MISO_PWM0_ADC10,
        PA23_SPI1MOSI_PWM1_ADC11,
        PA21_SPI1SCK_TRIG1_TXD1,
        PA18_SPI1SSN0_ACMP0O,
        1,
        0
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

#if CONFIG_EFLASH
struct {
    uint32_t base;
    eflash_info_t info;
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
int32_t target_get_eflash(int32_t idx, uint32_t *base, eflash_info_t *info)
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

#if CONFIG_DMAC
struct {
    uint32_t base;
    uint32_t irq;
}
const sg_dmac_config[CONFIG_DMAC_NUM] = {
    {CSKY_DMAC0_BASE, SEU_DMAC_IRQn},
    {CSKY_DMAC1_BASE, NONSEU_DMAC_IRQn}
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
} iic_pin_map_t;
const static iic_pin_map_t s_iic_pin_map[] = {
    {
        PB0_SCL0_PWM2_I2SMCLK,
        PB1_SDA0_PWM3_I2SSCK,
        0,
        0
    },
    {
        PA6_SPI0MOSI_PWM6_SCL0,
        PA7_SPI0SSN_PWM7_SDA0,
        0,
        2
    },
    {
        PC0_SCL1_CTS1_PWM10_ADC14,
        PC1_SDA1_RTS1_PWM11_ADC15,
        1,
        0
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
            if (s_iic_pin_map[idx].cfg_idx == 0) {
                pin_mux(s_iic_pin_map[idx].scl, s_iic_pin_map[idx].function);
                pin_mux(s_iic_pin_map[idx].sda, s_iic_pin_map[idx].function);
            }
            return s_iic_pin_map[idx].cfg_idx;
        }
    }

    return -1;
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
    {PA4_CTS0_PWM0_SPI0SCK_TRIG0, 0, 0, 1},
    {PA5_RTS0_PWM1_SPI0SSN_TRIG1, 0, 0, 1},
    {PB0_SCL0_PWM2_I2SMCLK, 0, 1, 1},
    {PB1_SDA0_PWM3_I2SSCK, 0, 1, 1},

    {PB2_SPI0SCK_PWM4_I2SWS, 0, 2, 1},
    {PB3_SPI0MISO_PWM5_I2SSD, 0, 2, 1},
    {PA6_SPI0MOSI_PWM6_SCL0, 0, 3, 1},
    {PA7_SPI0SSN_PWM7_SDA0, 0, 3, 1},

    {PA12_PWM8_TCK_ADC4, 0, 4, 0},
    {PA13_PWM9_TMS_ADC5, 0, 4, 0},
    {PA14_PWM10_ADC6, 0, 5, 0},
    {PA15_PWM11_ADC7, 0, 5, 0},

    {PA22_SPI1MISO_PWM0_ADC10, 0, 0, 1},
    {PA23_SPI1MOSI_PWM1_ADC11, 0, 0, 1},
    {PC0_SCL1_CTS1_PWM10_ADC14, 0, 5, 2},
    {PC1_SDA1_RTS1_PWM11_ADC15, 0, 5, 2}

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
