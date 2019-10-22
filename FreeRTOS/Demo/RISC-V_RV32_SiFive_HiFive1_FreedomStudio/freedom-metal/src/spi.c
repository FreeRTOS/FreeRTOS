/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine.h>
#include <metal/spi.h>

extern inline void metal_spi_init(struct metal_spi *spi, int baud_rate);
extern inline int metal_spi_transfer(struct metal_spi *spi, struct metal_spi_config *config, size_t len, char *tx_buf, char *rx_buf);
extern inline int metal_spi_get_baud_rate(struct metal_spi *spi);
extern inline int metal_spi_set_baud_rate(struct metal_spi *spi, int baud_rate);

struct metal_spi *metal_spi_get_device(int device_num)
{
    if(device_num >= __METAL_DT_MAX_SPIS) {
        return NULL;
    }

    return (struct metal_spi *) __metal_spi_table[device_num];
}
