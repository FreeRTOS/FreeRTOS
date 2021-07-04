/***************************************************************************
 * Project                               :  shakti devt board
 * Name of the file                      :  spi_driver.c
 * Brief Description of file             :  Driver to control the spi device.
 * Name of Author                        :  Kaustubh Ghormade
 * Email ID                              :  kaustubh4347@gmail.com

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
 * @file spi_spansion.c
 * @brief Does basic flash operatons .
 * @detail Configures SPI, flash device and then do all basic flash oerations.
 */

#include "spi.h"
#include "log.h"
#include "utils.h"

uint32_t* spi_cr1    = (uint32_t*) SPI_CR1;
uint32_t* spi_cr2    = (uint32_t*) SPI_CR2;
uint32_t* spi_sr     = (uint32_t*) SPI_SR ;
uint32_t* spi_dr1    = (uint32_t*) SPI_DR1;
uint32_t* spi_dr2    = (uint32_t*) SPI_DR2;
uint32_t* spi_dr3    = (uint32_t*) SPI_DR3;
uint32_t* spi_dr4    = (uint32_t*) SPI_DR4;
uint32_t* spi_dr5    = (uint32_t*) SPI_DR5;
uint32_t* spi_crcpr  = (uint32_t*) SPI_CRCPR;
uint32_t* spi_rxcrcr = (uint32_t*) SPI_RXCRCR;
uint32_t* spi_txcrcr = (uint32_t*) SPI_TXCRCR;

//By default, spi 0 is configured
/**
 * @fn void configure_spi(uint32_t offset)
 * @brief assigns memory mapped addres value to SPI registers.
 * @details Takes the SPI Base address and then adds offset to each and every
 *          spi registers..
 * @param uint32_t* ---> offset value
 */
void configure_spi(uint32_t offset)
{
	spi_cr1    = (uint32_t*) (SPI_CR1 + offset);
	spi_cr2    = (uint32_t*) (SPI_CR2 + offset);
	spi_sr     = (uint32_t*) (SPI_SR + offset);
	spi_dr1    = (uint32_t*) (SPI_DR1 + offset);
	spi_dr2    = (uint32_t*) (SPI_DR2 + offset);
	spi_dr3    = (uint32_t*) (SPI_DR3 + offset);
	spi_dr4    = (uint32_t*) (SPI_DR4 + offset);
	spi_dr5    = (uint32_t*) (SPI_DR5 + offset);
	spi_crcpr  = (uint32_t*) (SPI_CRCPR + offset);
	spi_rxcrcr = (uint32_t*) (SPI_RXCRCR + offset);
	spi_txcrcr = (uint32_t*) (SPI_TXCRCR + offset);
}

/**
 * @fn void set_spi(uint32_t* addr, uint32_t val)
 * @brief to assign value to memory mapped spi register
 * @details writes the given value to given addres (SPI).
 * @param uint32_t* addr 
 * @param uint32_t val 
 */
void set_spi(uint32_t* addr, uint32_t val)
{
	*addr = val;
}

/**
 * @fn uint32_t get_spi(uint32_t* addr)
 * @brief to get value for memory mapped spi register
 * @details Reads the SPI register value from passed address.
 * @param uint32_t* ---> address from where read has to happen
 * @return uint32_t ---> SPI Register read value.
 */
uint32_t get_spi(uint32_t* addr)
{
	return *addr;
}

/** @fn void spi_init(void)
 * @brief setting up baud rate and clock pole and phase 
 * @details Initialize the spi controller in Mode 3 (CPOL =1 & CPHA =1) with SCK= clk/16
 */
void spi_init(void)
{
	set_spi(spi_cr1, (SPI_BR(7)|SPI_CPHA|SPI_CPOL));
}

/** @fn  void spi_tx_rx_start(void)
 * @brief to start receiving data as soon as transmit state is complete
 * @details While receiving data from flash (reading Device ID, status register and reading flash)  
 *           in master mode use this function.
 * @warning Should be set before configuring the control register 1.
 */
void spi_tx_rx_start(void)
{
	set_spi(spi_cr2, (SPI_RX_IMM_START));
}


/** @fn void spi_rx_enable(void)
 * @brief to start receive state 
 * @details This is not in used when spi is in Master mode 
 */
void spi_rx_enable(void)
{
	set_spi(spi_cr2, (SPI_RX_START));
}

/**
 * @fn uint32_t bitExtracted(uint32_t number, uint32_t k, uint32_t p)
 * @brief Extract the k number of bit from (p-1) position of 'number'
 * @details If one want to extract the k bits from (p-1) position in 32 bit "number".   
 * @param uint32_t (number (32 bit))
 * @param uint32_t (k (number of bits to be extracted))
 * @param uint32_t (p (position from where the bits to be extracted))
 * @return uint32_t (32 bit which have k bit from "number" and rest are zero)
 */
uint32_t bitExtracted(uint32_t number, uint32_t k, uint32_t p)
{
	return (((1 << k) - 1) & (number >> (p - 1)));
}

/**
 * @fn  uint32_t spi_rxne_enable(void)
 * @brief to check if receive buffer is empty or not
 * @details As soons as data come to receive buffer this bit is set.  
 * @return uint32_t (1: if there is data uint32_to the RxFIFO else 0)
 */
uint32_t spi_rxne_enable(void)
{
	uint32_t value = 0;

	while (!(value & 0x1))
	{
		waitfor(100);
		value = get_spi(spi_sr);
	}
	return 1;
}

/**
 * @fn uint32_t spi_notbusy(void)
 * @brief to check if spi is ready for next transaction or busy with previous one
 * @details it read the status of bsy bit in spi_sr 
 * @warning One should check this bit before going to next transcation
 * @return uint32_t (0: SPI is busy in communication, 1: SPI nt busy)
 */
uint32_t spi_notbusy(void)
{
	uint32_t value = 0x80;

	while ((value & 0x80))
	{
		waitfor(10);
		value = get_spi(spi_sr);
	}

	return 1;
}

/**
 * @fn uint32_t flash_write_enable(void)
 * @brief to set the WEL (Write Enable Latch) bit in status register
 * @details Before modifying content of flash, one should enable the WEL bit first
 * @warning Without enabling this bit one cannot erase/write uint32_to the flash
 * @return uint32_t
 */
uint32_t flash_write_enable(void)
{
	set_spi(spi_dr1, 0x06000000);
	set_spi(spi_dr5, 0x06);
	set_spi(spi_cr1, (SPI_BR(7)|SPI_TOTAL_BITS_TX(8)|SPI_TOTAL_BITS_RX(0)|SPI_SPE|SPI_CPHA|SPI_CPOL));
	spi_notbusy();

	return 1;
}

/**
 * @fn uint32_t flash_clear_sr(void)
 * @brief to reset the status register
 * @details It will reset the bits of status register
 * @return uint32_t
 */

uint32_t flash_clear_sr(void)
{
	set_spi(spi_dr1,0x30000000);
	set_spi(spi_dr5,0x30);
	set_spi(spi_cr1, (SPI_BR(7)|SPI_TOTAL_BITS_TX(8)|SPI_TOTAL_BITS_RX(0)|SPI_SPE|SPI_CPHA|SPI_CPOL));
	spi_notbusy();

	return 1;
}

/**
 * @fn uint32_t flash_cmd_addr(uint32_t command, uint32_t addr)
 * @brief Use for sending 8bit of command + 32 bit of address 
 * @details Useful for function like erase
 * @warning to move data drom dr register to fifo there must be some data uint32_to spi_dr5 
 * @param uint32_t (command (opcode))
 * @param uint32_t (addr (address after the opcode))
 * @return uint32_t
 */
uint32_t flash_cmd_addr(uint32_t command, uint32_t addr)
{
	uint32_t address1 = bitExtracted(addr, 24, 9);
	uint32_t address2 = bitExtracted(addr, 8, 1);
	uint32_t data1 = command | address1 ;
	address2 = address2 << 24;

	set_spi(spi_dr1, data1);
	set_spi(spi_dr2, address2);
	set_spi(spi_dr5, 0);
	set_spi(spi_cr1, (SPI_BR(7)|SPI_TOTAL_BITS_TX(40)|SPI_TOTAL_BITS_RX(0)|SPI_SPE|SPI_CPHA|SPI_CPOL));
	waitfor(20);
	spi_notbusy();

	return 1;
}

/**
 * @fn void flash_cmd_addr_data(uint32_t command, uint32_t addr, uint32_t data)
 * @brief useful for function like Write 
 * @details use for sending 8bit command +32bit of write address + 32 bit of write data
 * @warning to move data from data register to fifo there must be some data uint32_to spi_dr5
 * @param uint32_t (command (opcode))
 * @param uint32_t (addr(address after the opcode))
 * @param uint32_t (data (data after the address))
 */
void flash_cmd_addr_data(uint32_t command, uint32_t addr, uint32_t data)
{
	uint32_t cmd_addr = command | ( (addr & 0xFFFFFF00)  >> 8);
	uint32_t data1 = ( (addr & 0xFF)  << 24 ) |( (data & 0xFFFFFF00)  >> 8);
	uint32_t data2 = ( (data & 0xFF)  << 24 ) & 0xFF000000;

	log_debug("\n cmd: %x;d1: %x; d2: %x", cmd_addr, data1, data2);

	set_spi(spi_dr1, cmd_addr);
	set_spi(spi_dr2, data1);
	set_spi(spi_dr3, data2);
	set_spi(spi_dr5, 0);
	set_spi(spi_cr1, (SPI_BR(7)|SPI_TOTAL_BITS_TX(72)|SPI_TOTAL_BITS_RX(0)|SPI_SPE|SPI_CPHA|SPI_CPOL));
	waitfor(20);
	spi_notbusy();
	flash_status_register_read();
}

/**
 * @fn void flash_write(uint32_t address, uint32_t data)
 * @brief  Write 4bytes of data from given address
 * @details flash_cmd_addr_data with opcode 12h.  
 * @warning before writing uint32_to the flash one should enable the WEL bit spi_sr by using write_enable(void)
 * @param uint32_t (addres (write address))
 * @param uint32_t(data (write data))
 */
void flash_write(uint32_t address, uint32_t data)
{
	flash_write_enable();
	flash_cmd_addr_data(0x12000000, address,data);
	flash_status_register_read();
}

/**
 * @fn uint32_t flash_cmd_to_read(uint32_t command, uint32_t addr)
 * @briefUse useful for function like read
 * @details for sending command of 8bit + read address of 32bit + 8bit of dummy cycle and receive 
 *          32bit value from flash 
 * @warning As receive shoild start as soon as transmit state end, use spi_rx_tx_start() Before 
 *          setting control register 1
 * @param uint32_t (command (opcode))
 * @param uint32_t (addr(read_address))
 * @return uint32_t 
 */
uint32_t flash_cmd_to_read(uint32_t command, uint32_t addr)
{
	uint32_t dr5;
	uint32_t address2 = bitExtracted(addr, 8, 1);

	address2 = address2 << 24;
	set_spi(spi_dr1, ( command  | ( (addr & 0xFFFFFF00) >> 8) ));
	set_spi(spi_dr2, ( (addr & 0xFF) << 24) );
	set_spi(spi_dr5, 0);
	spi_tx_rx_start();
	set_spi(spi_cr1, (SPI_BR(7)|SPI_TOTAL_BITS_TX(48)|SPI_TOTAL_BITS_RX(32)|SPI_SPE|SPI_CPHA|SPI_CPOL));
	waitfor(2000);

	if(spi_rxne_enable()) 
	{
		dr5 = *spi_dr5;
	}

	return dr5;

}

/** @fn uint32_t flash_read(uint32_t address)
 * @brief read the 4bytes data from given address 
 * @details flash_cmd_to_read with opcode 0Bh for fast read
 * @param uint32_t (address (read address))
 * @return uint32_t 
 */
uint32_t flash_read(uint32_t address)
{
	uint32_t read_value = flash_cmd_to_read(0x0C000000,address);
	return read_value;
}

/**
 * @fn uint32_t flash_cmd_read(uint32_t command)
 * @brief usefull for reading status register
 * @details use for sending 8bit command and receive the 32bit of data
 * @param uint32_t command (opcode)
 * @return uint32_t  value (flash response to opcode)
 */
uint32_t flash_cmd_read(uint32_t command)
{
	uint32_t dr5;
	set_spi(spi_dr1, command);
	set_spi(spi_dr5, command);
	spi_tx_rx_start();
	set_spi(spi_cr1, (SPI_BR(7)|SPI_TOTAL_BITS_TX(8)|SPI_TOTAL_BITS_RX(32)|SPI_SPE|SPI_CPHA|SPI_CPOL));
	if(spi_rxne_enable()) {
		dr5 = *spi_dr5;
	}
	return dr5;
}

/**
 * @fn  void flash_erase(uint32_t address)
 * @brief Erase the flash
 * @details Erase the 64kb sector from given address 
 * @warning before erasing the flash one should enable the WEL bit spi_sr by using write_enable()
 * @param uint32_t (address (address from which data should erase))
 */
void flash_erase(uint32_t address)
{
	flash_cmd_addr(0xdc000000, address);
}

/**
 * @fn uint32_t flash_status_register_read(void)
 * @briefRead read status register of flash
 * @details  Using flash_cmd_read function with opcode 05h to check status of WIP(Write in progress)
 *           and WEL(Write Enable Latch) bit.
 * @return uint32_t
 */
uint32_t flash_status_register_read(void)
{
	uint32_t stat = 0x3;

	while (stat & 0x03)
	{
		stat = flash_cmd_read(0x05000000);
		log_debug("flash status register val %x\n", stat);
	}

	return 0;
}

/**
 * @fn uint32_t flash_device_id(void)
 * @briefto read Device ID and Mfg. ID of flash
 * @details Device ID is 1byte and Mfg. ID of flash is of 2byte. Hence 8bit of command and receiving 
 *          24 bits of data from flash
 * @warning to move data from data register to fifo there must be some data uint32_to spi_dr5
 * @return uint32_t
 */
uint32_t flash_device_id(void)
{
	uint32_t dr3;
	uint32_t val1, val2;

	flash_write_enable();
	set_spi(spi_dr1, 0x9f000000);
	set_spi(spi_dr5, 0x9f000000);
	spi_tx_rx_start();
	set_spi(spi_cr1, (SPI_BR(7)|SPI_TOTAL_BITS_TX(8)|SPI_TOTAL_BITS_RX(24)|SPI_SPE|SPI_CPHA|SPI_CPOL));

	if(spi_rxne_enable())
	{
		dr3 = *spi_dr5;
	}

	val1 = bitExtracted(dr3, 8, 17);
	val2 = bitExtracted(dr3, 16, 1);

	log_debug("Device ID %x \n", val1);
	log_debug("extracted device id %x \n",val2);

	return 1;
}
