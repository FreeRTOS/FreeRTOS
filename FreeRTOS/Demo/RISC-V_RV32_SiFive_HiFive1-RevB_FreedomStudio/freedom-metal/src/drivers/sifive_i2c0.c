/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_I2C0
#include <metal/clock.h>
#include <metal/compiler.h>
#include <metal/drivers/sifive_gpio0.h>
#include <metal/drivers/sifive_i2c0.h>
#include <metal/io.h>
#include <metal/machine.h>
#include <metal/time.h>
#include <stdio.h>

/* Register fields */
#define METAL_I2C_CONTROL_EN (1UL << 7)
#define METAL_I2C_CONTROL_IE (1UL << 6)
#define METAL_I2C_WRITE (0UL << 0)
#define METAL_I2C_READ (1UL << 0)
#define METAL_I2C_CMD_START (1UL << 7)
#define METAL_I2C_CMD_STOP (1UL << 6)
#define METAL_I2C_CMD_READ (1UL << 5)
#define METAL_I2C_CMD_WRITE (1UL << 4)
#define METAL_I2C_CMD_ACK (1UL << 3)
#define METAL_I2C_CMD_IACK (1UL << 0)
#define METAL_I2C_STATUS_RXACK (1UL << 7)
#define METAL_I2C_STATUS_BUSY (1UL << 6)
#define METAL_I2C_STATUS_AL (1UL << 5)
#define METAL_I2C_STATUS_TIP (1UL << 1)
#define METAL_I2C_STATUS_IP (1UL << 0)

/* Prescaler max value */
#define METAL_I2C_PRESCALE_MAX 0xFFFF
/* Macros to access registers */
#define METAL_I2C_REG(offset) ((base + offset))
#define METAL_I2C_REGB(offset)                                                 \
    (__METAL_ACCESS_ONCE((__metal_io_u8 *)METAL_I2C_REG(offset)))
#define METAL_I2C_REGW(offset)                                                 \
    (__METAL_ACCESS_ONCE((__metal_io_u32 *)METAL_I2C_REG(offset)))

/* Timeout macros for register status checks */
#define METAL_I2C_RXDATA_TIMEOUT 1
#define METAL_I2C_TIMEOUT_RESET(timeout)                                       \
    timeout = metal_time() + METAL_I2C_RXDATA_TIMEOUT
#define METAL_I2C_TIMEOUT_CHECK(timeout)                                       \
    if (metal_time() > timeout) {                                              \
        METAL_I2C_LOG("I2C timeout error.\n");                                 \
        return METAL_I2C_RET_ERR;                                              \
    }
#define METAL_I2C_REG_CHECK(exp, timeout)                                      \
    while (exp) {                                                              \
        METAL_I2C_TIMEOUT_CHECK(timeout)                                       \
    }

/* Driver console logging */
#if defined(METAL_I2C_DEBUG)
#define METAL_I2C_LOG(x) printf(x)
#else
#define METAL_I2C_LOG(x)
#endif

/* Check endianess */
#if __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#error *** Unsupported endianess ***
#endif

#define METAL_SIFIVE_I2C_INSERT_STOP(stop_flag) ((stop_flag & 0x01UL) << 6)
#define METAL_SIFIVE_I2C_INSERT_RW_BIT(addr, rw)                               \
    ((addr & 0x7FUL) << 1 | (rw & 0x01UL))
#define METAL_SIFIVE_I2C_GET_PRESCALER(baud)                                   \
    ((clock_rate / (baud_rate * 5)) - 1)
#define METAL_I2C_INIT_OK 1
#define METAL_I2C_RET_OK 0
#define METAL_I2C_RET_ERR -1

static void pre_rate_change_callback(void *priv) {
    unsigned long base =
        __metal_driver_sifive_i2c0_control_base((struct metal_i2c *)priv);
    /* Check for any pending transfers */
    while (METAL_I2C_REGB(METAL_SIFIVE_I2C0_STATUS) & METAL_I2C_STATUS_TIP)
        ;
}

static void post_rate_change_callback(void *priv) {
    struct __metal_driver_sifive_i2c0 *i2c = priv;
    /* Set baud rate after clock rate change */
    metal_i2c_set_baud_rate(&i2c->i2c, i2c->baud_rate);
}

static void __metal_driver_sifive_i2c0_init(struct metal_i2c *gi2c,
                                            unsigned int baud_rate,
                                            metal_i2c_mode_t mode) {
    struct __metal_driver_sifive_gpio0 *pinmux =
        __metal_driver_sifive_i2c0_pinmux(gi2c);
    struct __metal_driver_sifive_i2c0 *i2c = (void *)gi2c;

    if ((pinmux != NULL) && (gi2c != NULL)) {
        /* configure I2C I/O pins */
        long pinmux_output_selector =
            __metal_driver_sifive_i2c0_pinmux_output_selector(gi2c);
        long pinmux_source_selector =
            __metal_driver_sifive_i2c0_pinmux_source_selector(gi2c);
        pinmux->gpio.vtable->enable_io((struct metal_gpio *)pinmux,
                                       pinmux_output_selector,
                                       pinmux_source_selector);

        /* 1: Master 0: Slave */
        if (mode == METAL_I2C_MASTER) {
            /* Set requested baud rate */
            if (metal_i2c_set_baud_rate(gi2c, baud_rate) == METAL_I2C_RET_OK) {
                i2c->init_done = METAL_I2C_INIT_OK;
            }
        } else {
            /* Nothing to do. slave mode not supported */
        }
    }
}

static int __metal_driver_sifive_i2c0_get_baud_rate(struct metal_i2c *gi2c) {
    struct __metal_driver_sifive_i2c0 *i2c = (void *)gi2c;
    return i2c->baud_rate;
}

static int __metal_driver_sifive_i2c0_set_baud_rate(struct metal_i2c *gi2c,
                                                    unsigned int baud_rate) {
    struct metal_clock *clock = __metal_driver_sifive_i2c0_clock(gi2c);
    struct __metal_driver_sifive_i2c0 *i2c = (void *)gi2c;
    unsigned long base = __metal_driver_sifive_i2c0_control_base(gi2c);
    int ret = METAL_I2C_RET_ERR;

    if ((clock != NULL) && (gi2c != NULL)) {
        long clock_rate = clock->vtable->get_rate_hz(clock);

        i2c->pre_rate_change_callback.callback = &pre_rate_change_callback;
        i2c->pre_rate_change_callback.priv = i2c;
        metal_clock_register_pre_rate_change_callback(
            clock, &(i2c->pre_rate_change_callback));

        i2c->post_rate_change_callback.callback = &post_rate_change_callback;
        i2c->post_rate_change_callback.priv = i2c;
        metal_clock_register_post_rate_change_callback(
            clock, &(i2c->post_rate_change_callback));

        /* Calculate prescaler value */
        long prescaler = METAL_SIFIVE_I2C_GET_PRESCALER(baud_rate);

        if ((prescaler > METAL_I2C_PRESCALE_MAX) || (prescaler < 0)) {
            /* Out of range value, return error */
            METAL_I2C_LOG("I2C Set baud failed.\n");
        } else {
            /* Set pre-scaler value */
            METAL_I2C_REGB(METAL_SIFIVE_I2C0_CONTROL) &= ~METAL_I2C_CONTROL_EN;
            METAL_I2C_REGB(METAL_SIFIVE_I2C0_PRESCALE_LOW) = prescaler & 0xFF;
            METAL_I2C_REGB(METAL_SIFIVE_I2C0_PRESCALE_HIGH) =
                (prescaler >> 8) & 0xFF;
            METAL_I2C_REGB(METAL_SIFIVE_I2C0_CONTROL) |= METAL_I2C_CONTROL_EN;

            i2c->baud_rate = baud_rate;
            ret = METAL_I2C_RET_OK;
        }
    } else {
        METAL_I2C_LOG("I2C Set baud failed.\n");
    }

    return ret;
}

static int __metal_driver_sifive_i2c0_write_addr(unsigned long base,
                                                 unsigned int addr,
                                                 unsigned char rw_flag) {
    time_t timeout;
    int ret = METAL_I2C_RET_OK;
    /* Reset timeout */
    METAL_I2C_TIMEOUT_RESET(timeout);

    /* Check if any transfer is in progress */
    METAL_I2C_REG_CHECK(
        (METAL_I2C_REGB(METAL_SIFIVE_I2C0_STATUS) & METAL_I2C_STATUS_TIP),
        timeout);

    /* Set transmit register to given address with read/write flag */
    METAL_I2C_REGB(METAL_SIFIVE_I2C0_TRANSMIT) =
        METAL_SIFIVE_I2C_INSERT_RW_BIT(addr, rw_flag);

    /* Set start flag to trigger the address transfer */
    METAL_I2C_REGB(METAL_SIFIVE_I2C0_COMMAND) =
        METAL_I2C_CMD_WRITE | METAL_I2C_CMD_START;
    /* Reset timeout */
    METAL_I2C_TIMEOUT_RESET(timeout);

    /* Check for transmit completion */
    METAL_I2C_REG_CHECK(
        (METAL_I2C_REGB(METAL_SIFIVE_I2C0_STATUS) & METAL_I2C_STATUS_TIP),
        timeout);

    /* Check for ACK from slave */
    if ((METAL_I2C_REGB(METAL_SIFIVE_I2C0_STATUS) & METAL_I2C_STATUS_RXACK)) {
        /* No ACK, return error */
        METAL_I2C_LOG("I2C RX ACK failed.\n");
        ret = METAL_I2C_RET_ERR;
    }

    return ret;
}

static int __metal_driver_sifive_i2c0_write(struct metal_i2c *i2c,
                                            unsigned int addr, unsigned int len,
                                            unsigned char buf[],
                                            metal_i2c_stop_bit_t stop_bit) {
    __metal_io_u8 command;
    time_t timeout;
    int ret;
    unsigned long base = __metal_driver_sifive_i2c0_control_base(i2c);
    unsigned int i;

    if ((i2c != NULL) &&
        ((struct __metal_driver_sifive_i2c0 *)i2c)->init_done) {

        /* Send address over I2C bus, current driver supports only 7bit
         * addressing */
        ret =
            __metal_driver_sifive_i2c0_write_addr(base, addr, METAL_I2C_WRITE);

        if (ret != METAL_I2C_RET_OK) {
            /* Write address failed */
            METAL_I2C_LOG("I2C Address Write failed.\n");
        } else {
            /* Set command flags */
            command = METAL_I2C_CMD_WRITE;

            for (i = 0; i < len; i++) {
                /* Copy into transmit register */
                METAL_I2C_REGB(METAL_SIFIVE_I2C0_TRANSMIT) = buf[i];

                /* for last byte transfer, check if stop condition is requested
                 */
                if (i == (len - 1)) {
                    command |= METAL_SIFIVE_I2C_INSERT_STOP(stop_bit);
                }
                /* Write command register */
                METAL_I2C_REGB(METAL_SIFIVE_I2C0_COMMAND) = command;
                /* Reset timeout */
                METAL_I2C_TIMEOUT_RESET(timeout);

                /* Check for transfer completion */
                METAL_I2C_REG_CHECK((METAL_I2C_REGB(METAL_SIFIVE_I2C0_STATUS) &
                                     METAL_I2C_STATUS_TIP),
                                    timeout);

                /* Check for ACK from slave */
                if ((METAL_I2C_REGB(METAL_SIFIVE_I2C0_STATUS) &
                     METAL_I2C_STATUS_RXACK)) {
                    /* No ACK, return error */
                    METAL_I2C_LOG("I2C RX ACK failed.\n");
                    ret = METAL_I2C_RET_ERR;
                    break;
                }
            }
        }

    } else {
        /* I2C device not initialized, return error */
        METAL_I2C_LOG("I2C device not initialized.\n");
        ret = METAL_I2C_RET_ERR;
    }

    return ret;
}
static int __metal_driver_sifive_i2c0_read(struct metal_i2c *i2c,
                                           unsigned int addr, unsigned int len,
                                           unsigned char buf[],
                                           metal_i2c_stop_bit_t stop_bit) {
    int ret;
    __metal_io_u8 command;
    time_t timeout;
    unsigned int i;
    unsigned long base = __metal_driver_sifive_i2c0_control_base(i2c);

    if ((i2c != NULL) &&
        ((struct __metal_driver_sifive_i2c0 *)i2c)->init_done) {

        /* Send address over I2C bus, current driver supports only 7bit
         * addressing */
        ret = __metal_driver_sifive_i2c0_write_addr(base, addr, METAL_I2C_READ);

        if (ret != METAL_I2C_RET_OK) {
            /* Write address failed */
            METAL_I2C_LOG("I2C Read failed.\n");
        } else {
            /* Set command flags */
            command = METAL_I2C_CMD_READ;

            for (i = 0; i < len; i++) {
                /* check for last transfer */
                if (i == (len - 1)) {
                    /* Set NACK to end read, if requested generate STOP
                     * condition */
                    command |= (METAL_I2C_CMD_ACK |
                                METAL_SIFIVE_I2C_INSERT_STOP(stop_bit));
                }
                /* Write command register */
                METAL_I2C_REGB(METAL_SIFIVE_I2C0_COMMAND) = command;
                /* Reset timeout */
                METAL_I2C_TIMEOUT_RESET(timeout);

                /* Wait for the read to complete */
                METAL_I2C_REG_CHECK((METAL_I2C_REGB(METAL_SIFIVE_I2C0_STATUS) &
                                     METAL_I2C_STATUS_TIP),
                                    timeout);
                /* Store the received byte */
                buf[i] = METAL_I2C_REGB(METAL_SIFIVE_I2C0_TRANSMIT);
            }
        }
    } else {
        /* I2C device not initialized, return error */
        METAL_I2C_LOG("I2C device not initialized.\n");
        ret = METAL_I2C_RET_ERR;
    }

    return ret;
}

static int
__metal_driver_sifive_i2c0_transfer(struct metal_i2c *i2c, unsigned int addr,
                                    unsigned char txbuf[], unsigned int txlen,
                                    unsigned char rxbuf[], unsigned int rxlen) {
    __metal_io_u8 command;
    time_t timeout;
    int ret;
    unsigned int i;
    unsigned long base = __metal_driver_sifive_i2c0_control_base(i2c);

    if ((i2c != NULL) &&
        ((struct __metal_driver_sifive_i2c0 *)i2c)->init_done) {
        if (txlen) {
            /* Set command flags */
            command = METAL_I2C_CMD_WRITE;
            /* Send address over I2C bus, current driver supports only 7bit
             * addressing */
            ret = __metal_driver_sifive_i2c0_write_addr(base, addr,
                                                        METAL_I2C_WRITE);

            if (ret != METAL_I2C_RET_OK) {
                /* Write address failed */
                METAL_I2C_LOG("I2C Write failed.\n");
                return ret;
            }
            for (i = 0; i < txlen; i++) {
                /* Copy into transmit register */
                METAL_I2C_REGB(METAL_SIFIVE_I2C0_TRANSMIT) = txbuf[i];

                if (i == (txlen - 1) && (rxlen == 0)) {
                    /* Insert stop condition to end transfer */
                    command |= METAL_I2C_CMD_STOP;
                }
                /* Write command register */
                METAL_I2C_REGB(METAL_SIFIVE_I2C0_COMMAND) = command;
                /* Reset timeout */
                METAL_I2C_TIMEOUT_RESET(timeout);

                /* Check for transfer completion. */
                METAL_I2C_REG_CHECK((METAL_I2C_REGB(METAL_SIFIVE_I2C0_STATUS) &
                                     METAL_I2C_STATUS_TIP),
                                    timeout);

                /* Check for ACK from slave. */
                if ((METAL_I2C_REGB(METAL_SIFIVE_I2C0_STATUS) &
                     METAL_I2C_STATUS_RXACK)) {
                    /* No ACK, return error */
                    METAL_I2C_LOG("I2C RX ACK failed.\n");
                    ret = METAL_I2C_RET_ERR;
                    break;
                }
            }
        }
        if (rxlen) {
            command = METAL_I2C_CMD_READ; /* Set command flags */
            /* Send address over I2C bus, current driver supports only 7bit
             * addressing */
            ret = __metal_driver_sifive_i2c0_write_addr(base, addr,
                                                        METAL_I2C_READ);

            if (ret != METAL_I2C_RET_OK) {
                /* Return error */
                METAL_I2C_LOG("I2C Read failed.\n");
                return ret;
            }
            for (i = 0; i < rxlen; i++) {
                /* check for last transfer */
                if (i == (rxlen - 1)) {
                    /* Set NACK to end read, generate STOP condition */
                    command |= (METAL_I2C_CMD_ACK | METAL_I2C_CMD_STOP);
                }
                /* Write command register */
                METAL_I2C_REGB(METAL_SIFIVE_I2C0_COMMAND) = command;
                /* Reset timeout */
                METAL_I2C_TIMEOUT_RESET(timeout);

                /* Wait for the read to complete */
                METAL_I2C_REG_CHECK((METAL_I2C_REGB(METAL_SIFIVE_I2C0_STATUS) &
                                     METAL_I2C_STATUS_TIP),
                                    timeout);
                /* Store the received byte */
                rxbuf[i] = METAL_I2C_REGB(METAL_SIFIVE_I2C0_TRANSMIT);
            }
        }
    } else {
        /* I2C device not initialized, return error */
        METAL_I2C_LOG("I2C device not initialized.\n");
        ret = METAL_I2C_RET_ERR;
    }

    return ret;
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_sifive_i2c0) = {
    .i2c.init = __metal_driver_sifive_i2c0_init,
    .i2c.write = __metal_driver_sifive_i2c0_write,
    .i2c.read = __metal_driver_sifive_i2c0_read,
    .i2c.transfer = __metal_driver_sifive_i2c0_transfer,
    .i2c.get_baud_rate = __metal_driver_sifive_i2c0_get_baud_rate,
    .i2c.set_baud_rate = __metal_driver_sifive_i2c0_set_baud_rate,
};

#endif /* METAL_SIFIVE_I2C0 */

typedef int no_empty_translation_units;
