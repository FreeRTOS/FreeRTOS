/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/i2c.h>
#include <metal/machine.h>

extern inline void metal_i2c_init(struct metal_i2c *i2c, unsigned int baud_rate,
                                  metal_i2c_mode_t mode);
extern inline int metal_i2c_write(struct metal_i2c *i2c, unsigned int addr,
                                  unsigned int len, unsigned char buf[],
                                  metal_i2c_stop_bit_t stop_bit);
extern inline int metal_i2c_read(struct metal_i2c *i2c, unsigned int addr,
                                 unsigned int len, unsigned char buf[],
                                 metal_i2c_stop_bit_t stop_bit);
extern inline int metal_i2c_transfer(struct metal_i2c *i2c, unsigned int addr,
                                     unsigned char txbuf[], unsigned int txlen,
                                     unsigned char rxbuf[], unsigned int rxlen);
extern inline int metal_i2c_get_baud_rate(struct metal_i2c *i2c);
extern inline int metal_i2c_set_baud_rate(struct metal_i2c *i2c, int baud_rate);

struct metal_i2c *metal_i2c_get_device(unsigned int device_num) {
#if __METAL_DT_MAX_I2CS > 0
    if (device_num < __METAL_DT_MAX_I2CS) {
        return (struct metal_i2c *)__metal_i2c_table[device_num];
    }
#endif
    return NULL;
}
