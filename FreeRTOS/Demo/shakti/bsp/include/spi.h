/***************************************************************************
 * Project                          : shakti devt board
 * Name of the file                 : spi.h
 * Brief Description of file        : Header to spi spansion driver
 * Name of Author                   : Kaustubh Ghormade
 * Email ID                         : kaustubh4347@gmail.com

 Copyright (C) 2019  IIT Madras. All rights reserved.

 This program is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program.  If not, see <https://www.gnu.org/licenses/>.
 ***************************************************************************/
/**
 * @file spi.h
 * @brief Header to spi spansion driver
 * @detail this is the header file for spi_flash_w25q32.c,spi_spansion.c
 */
#ifndef SPI_H
#define SPI_H

#include<stdlib.h>
#include <stdint.h> 

/*
   By default SPI0 is enabled at initialization.
   SPI0 is not available externally in certain boards.
   Check the SoC design for further information
 */

#define SPI0_OFFSET 0x00000000
#define SPI1_OFFSET 0x00000100
#define SPI2_OFFSET 0x00000200

#define SPI_CR1	     0x00020000
#define SPI_CR2	     0x00020004
#define SPI_SR       0x00020008
#define SPI_DR1	     0x0002000C
#define SPI_DR2	     0x00020010
#define SPI_DR3	     0x00020014
#define SPI_DR4	     0x00020018
#define SPI_DR5      0x0002001C
#define SPI_CRCPR    0x00020020
#define SPI_RXCRCR   0x00020024
#define SPI_TXCRCR   0x00020028

// defining SPI_CR1 register
#define SPI_CPHA	      (1 << 0)
#define SPI_CPOL	      (1 << 1)
#define SPI_MSTR	      (1 << 2)
#define SPI_BR(x)	      (x << 3)
#define SPI_SPE		      (1 << 6)
#define SPI_LSBFIRST	      (1 << 7)
#define SPI_SSI		      (1 << 8)
#define SPI_SSM		      (1 << 9)
#define SPI_RXONLY	      (1 << 10)
#define SPI_CRCL	      (1 << 11)
#define SPI_CCRCNEXT	      (1 << 12)
#define SPI_CRCEN	      (1 << 13)
#define SPI_BIDIOE	      (1 << 14)
#define SPI_BIDIMODE	      (1 << 15)
#define SPI_TOTAL_BITS_TX(x)  (x << 16)
#define SPI_TOTAL_BITS_RX(x)  (x << 24)

// defining SPI_CR2 register
#define SPI_RX_IMM_START   (1 << 16)
#define SPI_RX_START	   (1 << 15)
#define SPI_LDMA_TX	   (1 << 14)
#define SPI_LDMA_RX	   (1 << 13)
#define SPI_FRXTH	   (1 << 12)
#define SPI_DS(x)	   (x << 8)
#define SPI_TXEIE	   (1 << 7)
#define SPI_RXNEIE	   (1 << 6)
#define SPI_ERRIE	   (1 << 5)
#define SPI_FRF		   (1 << 4)
#define SPI_NSSP	   (1 << 3)
#define SPI_SSOE	   (1 << 2)
#define SPI_TXDMAEN	   (1 << 1)
#define SPI_RXDMAEN	   (1 << 0)

//defining SR register
#define SPI_FTLVL(x)	(x << 11)
#define SPI_FRLVL(x)	(x << 9)
#define SPI_FRE		(1 << 8)
#define SPI_OVR		(1 << 6)
#define SPI_MODF	(1 << 5)
#define SPI_CRCERR	(1 << 4)
#define TXE		(1 << 1)
#define RXNE		(1 << 0)

// function prototype

void configure_spi(uint32_t offset);
void spi_init(void);
void set_spi(uint32_t* addr, uint32_t val);
void bin(unsigned n);
void spi_tx_rx_start(void);
void spi_enable(void);
void spi_rx_enable(void);
void flash_cmd_addr_data(uint32_t command, uint32_t addr, uint32_t data);
void flash_write(uint32_t address, uint32_t data);
void flash_erase(uint32_t address);
uint32_t get_spi(uint32_t* addr);
uint32_t bitExtracted(uint32_t number, uint32_t k, uint32_t p) ;
uint32_t concat(uint32_t x, uint32_t y) ;
uint32_t spi_rxne_enable(void);
uint32_t spi_notbusy(void);
uint32_t flash_write_enable(void);
uint32_t flash_clear_sr(void);
uint32_t flash_cmd_addr(uint32_t command, uint32_t addr);
uint32_t flash_cmd_to_read(uint32_t command, uint32_t addr);
uint32_t flash_read(uint32_t address);
uint32_t flash_cmd_read(uint32_t command);
uint32_t flash_status_register_read(void);
uint32_t flash_device_id(void);

#endif
