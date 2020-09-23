/***************************************************************************
* Project                               :  shakti devt board
* Name of the file                      :  spi_driver.c
* Brief Description of file             :  driver file for SPI based flash W25Q32
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
@file spi_flash_w25q32.c
@brief Does basic flash operatons . 
@detail Configures SPI, flash device and then do all basic flash oerations.* 
*/
#include "spi.h"
#include "utils.h"
int* spi_cr1    = (int*) SPI_CR1;
int* spi_cr2    = (int*) SPI_CR2;
int* spi_sr     = (int*) SPI_SR ;
int* spi_dr1    = (int*) SPI_DR1 ;
int* spi_dr2    = (int*) SPI_DR2 ;
int* spi_dr3    = (int*) SPI_DR3 ;
int* spi_dr4    = (int*) SPI_DR4 ;
int* spi_dr5    = (int*) SPI_DR5 ;
int* spi_crcpr  = (int*) SPI_CRCPR;
int* spi_rxcrcr = (int*) SPI_RXCRCR;
int* spi_txcrcr = (int*) SPI_TXCRCR; 


//By default, spi 0 is configured
/**
 * @fn void configure_spi(int offset)
 * @brief assigns memory mapped addres value to SPI registers.
 * @details Takes the SPI Base address and then adds offset to each and every
 *          spi registers..
 * @param int* ---> offset value 
 */
void configure_spi(int offset)	
{
	spi_cr1    = (int*) (SPI_CR1 + offset);
	spi_cr2    = (int*) (SPI_CR2 + offset);
	spi_sr     = (int*) (SPI_SR + offset);
	spi_dr1    = (int*) (SPI_DR1 + offset);
	spi_dr2    = (int*) (SPI_DR2 + offset);
	spi_dr3    = (int*) (SPI_DR3 + offset);
	spi_dr4    = (int*) (SPI_DR4 + offset);
	spi_dr5    = (int*) (SPI_DR5 + offset);
	spi_crcpr  = (int*) (SPI_CRCPR + offset);
	spi_rxcrcr = (int*) (SPI_RXCRCR + offset);
	spi_txcrcr = (int*) (SPI_TXCRCR + offset); 
}

/**
 * @fn void set_spi(int* addr, int val)
 * @brief to assign value to memory mapped spi register
 * @details writes the given value to given addres (SPI).
 * @param int* addr
 * @param int val
 */
void set_spi(int* addr, int val)
{
	*addr = val;
}

/**
 * @fn int get_spi(int* addr)
 * @brief to get value for memory mapped spi register
 * @details Reads the SPI register value from passed address.
 * @param int* ---> address from where read has to happen
 * @return int ---> SPI Register read value.
 */
int get_spi(int* addr)
{
	return *addr;
}

/** @fn void spi_init()
 * @brief setting up baud rate and clock pole and phase 
 * @details Initialize the spi controller in Mode 3 (CPOL =1 & CPHA =1) with SCK= clk/16;
 */
void spi_init()
{
	set_spi(spi_cr1, (SPI_BR(7)|SPI_CPHA|SPI_CPOL));
}

/** @fn void spi_tx_rx_start()
 * @brief to start receiving data as soon as transmit state is complete
 * @details While receiving data from flash (reading Device ID, status register and reading flash)   
 *           in master mode use this function.
 * @warning Should be set before configuring the control register 1.
 */
void spi_tx_rx_start()
{
	set_spi(spi_cr2, (SPI_RX_IMM_START));
}


/** @fn void spi_rx_enable()
 * @brief to start receive state 
 * @details This is not in used when spi is in Master mode 
 */
void spi_rx_enable()
{
	set_spi(spi_cr2, (SPI_RX_START));
}

/**
 * @fn int bitExtracted(int number, int k, int p) 
 * @brief Extract the k number of bit from (p-1) position of 'number'
 * @details If one want to extract the k bits from (p-1) position in 32 bit "number".   
 * @param int (number (32 bit)), int (k (number of bits to be extracted)), 
 * @param int (p (position from where the bits to be extracted))
 * @return int (32 bit which have k bit from "number" and rest are zero)
 */
int bitExtracted(int number, int k, int p) 
{
	return (((1 << k) - 1) & (number >> (p - 1))); 
}

/**
 * @fn int spi_rxne_enable()
 * @brief to check if receive buffer is empty or not
 * @details As soons as data come to receive buffer this bit is set.  
 * @return int (1: if there is data into the RxFIFO else 0)
 */
int spi_rxne_enable()
{
	int value = 0;

	while (!(value & 0x1))
	{
		waitfor(100);
		value = get_spi(spi_sr);
	}
	return 1;
}

/**
 * @fn int spi_notbusy()
 * @brief to check if spi is ready for next transaction or busy with previous one
 * @details it read the status of bsy bit in spi_sr 
 * @warning One should check this bit before going to next transcation
 * @return int (0: SPI is busy in communication, 1: SPI nt busy)
 */
int spi_notbusy()
{
	int value = 0x80;

	while ((value & 0x80))
	{
		waitfor(10);
		value = get_spi(spi_sr);
	}

	return 1;
}

/**
 * @fn int flash_write_enable()
 * @brief to set the WEL (Write Enable Latch) bit in status register
 * @details Before modifying content of flash, one should enable the WEL bit first
 * @warning Without enabling this bit one cannot erase/write into the flash
 * @return int
 */
int flash_write_enable()
{
	set_spi(spi_dr1, 0x06000000);
	set_spi(spi_dr5, 0x06);
	set_spi(spi_cr1, (SPI_BR(7)|SPI_TOTAL_BITS_TX(8)|SPI_TOTAL_BITS_RX(0)|SPI_SPE|SPI_CPHA|SPI_CPOL));
	spi_notbusy();
	return 1;
}

/**
 * @fn int flash_clear_sr()
 * @brief to reset the status register
 * @details It will reset the bits of status register
 * @return int
 */
int flash_clear_sr()
{
	set_spi(spi_dr1,0x30000000);
	set_spi(spi_dr5,0x30);
	set_spi(spi_cr1, (SPI_BR(7)|SPI_TOTAL_BITS_TX(8)|SPI_TOTAL_BITS_RX(0)|SPI_SPE|SPI_CPHA|SPI_CPOL));
	spi_notbusy();
	return 1;
}

/**
 * @fn int flash_cmd_addr(int command, int addr)
 * @brief Use for sending 8bit of command + 32 bit of address 
 * @details Useful for function like erase
 * @warning to move data drom dr register to fifo there must be some data into spi_dr5 
 * @param int (command (opcode))
 * @param int (addr (address after the opcode))
 * @return int
 */
int flash_cmd_addr(int command, int addr)
{
	printf("Erase dr1 \n");
	set_spi(spi_dr1, ((command << 24) | (addr) ) );
	set_spi(spi_dr5, 0);
	set_spi(spi_cr1, (SPI_BR(7)|SPI_TOTAL_BITS_TX(32)|SPI_TOTAL_BITS_RX(0)|SPI_SPE|SPI_CPHA|SPI_CPOL));
	waitfor(20);
	spi_notbusy();
	return 1;
}

/**
 * @fn void flash_cmd_addr_data(int command, int addr, int data)
 * @brief useful for function like Write 
 * @details use for sending 8bit command +32bit of write address + 32 bit of write data
 * @warning to move data from data register to fifo there must be some data into spi_dr5
 * @param int (command (opcode))
 * @param int (addr(address after the opcode))
 * @param int (data (data after the address))
 */
void flash_cmd_addr_data(int command, int addr, int data)
{
#if 0
	int address1 = bitExtracted(addr, 24, 9);
	int address2 = bitExtracted(addr, 8, 1);
	int cmd_addr = command  | address1;
	address2 = address2 << 24;
	int data1 = bitExtracted(data, 24, 9);
	data1 = address2 | data1;
	int data2 = bitExtracted(data, 8, 1);
	data2 = data2 << 24;
	set_spi(spi_dr1, cmd_addr);
	set_spi(spi_dr2, data1);
	set_spi(spi_dr3, data2);
	set_spi(spi_dr5, 0);
	set_spi(spi_cr1, (SPI_BR(7)|SPI_TOTAL_BITS_TX(40)|SPI_TOTAL_BITS_RX(0)|SPI_SPE|SPI_CPHA|SPI_CPOL));
	waitfor(20);
	spi_notbusy();
#else
	set_spi(spi_dr1,  ( (command << 24) | (addr) ) );
//	printf("\n Write Command: %x; Data: %x",  ((command << 24) | (addr) ), data );

	set_spi(spi_dr2, data);
//	set_spi(spi_dr3, data2);
	set_spi(spi_dr5, 0);
	set_spi(spi_cr1, (SPI_BR(7)|SPI_TOTAL_BITS_TX(64)|SPI_TOTAL_BITS_RX(0)|SPI_SPE|SPI_CPHA|SPI_CPOL));
	waitfor(20);
	spi_notbusy();

#endif
}

/**
 * @fn void flash_write(int address, int data)
 * @brief  Write 4bytes of data from given address
 * @details flash_cmd_addr_data with opcode 12h.  
 * @warning before writing into the flash one should enable the WEL bit spi_sr by using write_enable()
 * @param int (addres (write address))
 * @param int(data (write data))
 */
void flash_write(int address, int data)
{
	flash_cmd_addr_data(0x02, address,data);
}

/**
 * @fn int flash_cmd_to_read(int command, int addr)
 * @briefUse useful for function like read
 * @details for sending command of 8bit + read address of 32bit + 8bit of dummy cycle and receive 
 *          32bit value from flash 
 * @warning As receive shoild start as soon as transmit state end, use spi_rx_tx_start() Before 
 *          setting control register 1
 * @param int (command (opcode))
 * @param int (addr(read_address))
 * @return int 
 */
int flash_cmd_to_read(int command, int addr)
{

	int dr5;
//	int address1 = bitExtracted(addr, 24, 9);
//    int address2 = bitExtracted(addr, 8, 1);
//	int cmd_addr = command  | address1;
//	int address2 = address2 << 24;
//	printf("\n Read Command: %x",  ( (command << 24) | (addr) ) );
	set_spi(spi_dr1,  ( (command << 24) | (addr) ) );
//	set_spi(spi_dr2, address2);
	set_spi(spi_dr5, 0);
	spi_tx_rx_start();
	set_spi(spi_cr1, (SPI_BR(7)|SPI_TOTAL_BITS_TX(40)|SPI_TOTAL_BITS_RX(32)|SPI_SPE|SPI_CPHA|SPI_CPOL));
	waitfor(20);
	 
	if(spi_rxne_enable()) 
	{
		dr5 = *spi_dr5;
	}
   // printf("Reading from dr5 %x \n", dr5);
	return dr5;

}

/** @fn int flash_read(int address)
 * @brief read the 4bytes data from given address 
 * @details flash_cmd_to_read with opcode 0Bh for fast read
 * @param int (address (read address))
 * @return int 
 */
int flash_read(int address)
{
	int read_value = flash_cmd_to_read(0x0B,address);
	
	return read_value;
}

/**
 * @fn int flash_cmd_read(int command)
 * @brief usefull for reading status register
 * @details use for sending 8bit command and receive the 32bit of data
 * @param int command (opcode)
 * @return int  value (flash response to opcode)
 */
int flash_cmd_read(int command)
{
	int dr1, dr2, dr5;
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
 * @fn void flash_erase(int address)
 * @brief Erase the flash
 * @details Erase the 64kb sector from given address 
 * @warning before erasing the flash one should enable the WEL bit spi_sr by using write_enable()
 * @param int (address (address from which data should erase))
 */
void flash_erase(int address)
{
	printf("Cypress erase \n");
	flash_cmd_addr(0xD8, address);
	printf("Cypress erase done\n");
}

/**
 * @fn int flash_status_register_read()
 * @briefRead read status register of flash
 * @details  Using flash_cmd_read function with opcode 05h to check status of WIP(Write in progress) 
 *           and WEL(Write Enable Latch) bit.
 * @return int
 */
int flash_status_register_read()
{
	int stat = 0x3;

	while (stat & 0x03)
	{
		stat = flash_cmd_read(0x05000000);
		//printf("flash status register val %x\n", stat);
	}

	return 0;
}

/**
 * @fn flash_device_id
 * @briefto read Device ID and Mfg. ID of flash
 * @details Device ID is 1byte and Mfg. ID of flash is of 2byte. Hence 8bit of command and receiving 
 *          24 bits of data from flash
 * @warning to move data from data register to fifo there must be some data into spi_dr5
 * @return int
 */
int flash_device_id()
{
	int dr1, dr2, dr3;
	int val1, val2;
	flash_write_enable();
	set_spi(spi_dr1, 0x9F000000);
	set_spi(spi_dr5, 0x9F000000);
	spi_tx_rx_start();
	set_spi(spi_cr1, (SPI_BR(7)|SPI_TOTAL_BITS_TX(8)|SPI_TOTAL_BITS_RX(24)|SPI_SPE|SPI_CPHA|SPI_CPOL));

	if(spi_rxne_enable())
	{
		dr3 = *spi_dr5;
		dr2 = *spi_dr2;
	}

	val1 = bitExtracted(dr3, 8, 17);
	val2 = bitExtracted(dr3, 16, 1);

	printf("Device ID %x \n", val1);
	printf("extracted device id %x \n",val2);

	return 1;	
}

