/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__SPI_H
#define METAL__SPI_H

struct metal_spi;

/*! @brief The configuration for a SPI transfer */
struct metal_spi_config {
    /*! @brief The protocol for the SPI transfer */
    enum { METAL_SPI_SINGLE, METAL_SPI_DUAL, METAL_SPI_QUAD } protocol;

    /*! @brief The polarity of the SPI transfer, equivalent to CPOL */
    unsigned int polarity : 1;
    /*! @brief The phase of the SPI transfer, equivalent to CPHA */
    unsigned int phase : 1;
    /*! @brief The endianness of the SPI transfer */
    unsigned int little_endian : 1;
    /*! @brief The active state of the chip select line */
    unsigned int cs_active_high : 1;
    /*! @brief The chip select ID to activate for the SPI transfer */
    unsigned int csid;
    /*! @brief The spi command frame number (cycles = num * frame_len) */
    unsigned int cmd_num;
    /*! @brief The spi address frame number */
    unsigned int addr_num;
    /*! @brief The spi dummy frame number */
    unsigned int dummy_num;
    /*! @brief The Dual/Quad spi mode selection.*/
    enum {
        MULTI_WIRE_ALL,
        MULTI_WIRE_DATA_ONLY,
        MULTI_WIRE_ADDR_DATA
    } multi_wire;
};

struct metal_spi_vtable {
    void (*init)(struct metal_spi *spi, int baud_rate);
    int (*transfer)(struct metal_spi *spi, struct metal_spi_config *config,
                    size_t len, char *tx_buf, char *rx_buf);
    int (*get_baud_rate)(struct metal_spi *spi);
    int (*set_baud_rate)(struct metal_spi *spi, int baud_rate);
};

/*! @brief A handle for a SPI device */
struct metal_spi {
    const struct metal_spi_vtable *vtable;
};

/*! @brief Get a handle for a SPI device
 * @param device_num The index of the desired SPI device
 * @return A handle to the SPI device, or NULL if the device does not exist*/
struct metal_spi *metal_spi_get_device(unsigned int device_num);

/*! @brief Initialize a SPI device with a certain baud rate
 * @param spi The handle for the SPI device to initialize
 * @param baud_rate The baud rate to set the SPI device to
 */
__inline__ void metal_spi_init(struct metal_spi *spi, int baud_rate) {
    spi->vtable->init(spi, baud_rate);
}

/*! @brief Perform a SPI transfer
 * @param spi The handle for the SPI device to perform the transfer
 * @param config The configuration for the SPI transfer.
 * @param len The number of bytes to transfer
 * @param tx_buf The buffer to send over the SPI bus. Must be len bytes long. If
 * NULL, the SPI will transfer the value 0.
 * @param rx_buf The buffer to receive data into. Must be len bytes long. If
 * NULL, the SPI will ignore received bytes.
 * @return 0 if the transfer succeeds
 */
__inline__ int metal_spi_transfer(struct metal_spi *spi,
                                  struct metal_spi_config *config, size_t len,
                                  char *tx_buf, char *rx_buf) {
    return spi->vtable->transfer(spi, config, len, tx_buf, rx_buf);
}

/*! @brief Get the current baud rate of the SPI device
 * @param spi The handle for the SPI device
 * @return The baud rate in Hz
 */
__inline__ int metal_spi_get_baud_rate(struct metal_spi *spi) {
    return spi->vtable->get_baud_rate(spi);
}

/*! @brief Set the current baud rate of the SPI device
 * @param spi The handle for the SPI device
 * @param baud_rate The desired baud rate of the SPI device
 * @return 0 if the baud rate is successfully changed
 */
__inline__ int metal_spi_set_baud_rate(struct metal_spi *spi, int baud_rate) {
    return spi->vtable->set_baud_rate(spi, baud_rate);
}

#endif
