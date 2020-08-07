/**
 *
 * \file
 *
 * \brief KS8851SNL driver for SAM.
 *
 * Copyright (c) 2013-2015 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */
/*
 * Support and FAQ: visit <a href="http://www.atmel.com/design-support/">Atmel Support</a>
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

#include "spi_master.h"
#include "ksz8851snl.h"
#include "ksz8851snl_reg.h"
#include "delay.h"
#include "pio.h"
#include "pio_handler.h"
#include "pdc.h"
#include "conf_eth.h"

/* Clock polarity. */
#define SPI_CLK_POLARITY 0

/* Clock phase. */
#define SPI_CLK_PHASE 1

/* SPI PDC register base. */
Pdc *g_p_spi_pdc = 0;

int lUDPLoggingPrintf( const char *pcFormatString, ... );

/* Temporary buffer for PDC reception. */
uint8_t tmpbuf[1536] __attribute__ ((aligned (16)));

union {
	uint64_t ul[2];
	uint8_t uc[16];
} cmdBuf, respBuf;

void dbg_add_line( const char *pcFormat, ... );

static void spi_clear_ovres( void );

/**
 * \brief Read register content, set bitmask and write back to register.
 *
 * \param reg the register address to modify.
 * \param bits_to_set bitmask to apply.
 */
void ksz8851_reg_setbits(uint16_t reg, uint16_t bits_to_set)
{
   uint16_t	temp;

   temp = ksz8851_reg_read(reg);
   temp |= bits_to_set;
   ksz8851_reg_write(reg, temp);
}

/**
 * \brief Read register content, clear bitmask and write back to register.
 *
 * \param reg the register address to modify.
 * \param bits_to_set bitmask to apply.
 */
void ksz8851_reg_clrbits(uint16_t reg, uint16_t bits_to_clr)
{
   uint16_t	temp;

   temp = ksz8851_reg_read(reg);
   temp &= ~(uint32_t) bits_to_clr;
   ksz8851_reg_write(reg, temp);
}

/**
 * \brief Configure the INTN interrupt.
 */
void configure_intn(void (*p_handler) (uint32_t, uint32_t))
{
//	gpio_configure_pin(KSZ8851SNL_INTN_GPIO, PIO_INPUT);
//	pio_set_input(PIOA, PIO_PA11_IDX, PIO_PULLUP);

	/* Configure PIO clock. */
	pmc_enable_periph_clk(INTN_ID);

	/* Adjust PIO debounce filter parameters, uses 10 Hz filter. */
	pio_set_debounce_filter(INTN_PIO, INTN_PIN_MSK, 10);

	/* Initialize PIO interrupt handlers, see PIO definition in board.h. */
	pio_handler_set(INTN_PIO, INTN_ID, INTN_PIN_MSK,
		INTN_ATTR, p_handler);

	/* Enable NVIC interrupts. */
	NVIC_SetPriority(INTN_IRQn, INT_PRIORITY_PIO);
	NVIC_EnableIRQ((IRQn_Type)INTN_ID);

	/* Enable PIO interrupts. */
	pio_enable_interrupt(INTN_PIO, INTN_PIN_MSK);
}

/**
 * \brief Read a register value.
 *
 * \param reg the register address to modify.
 *
 * \return the register value.
 */
uint16_t ksz8851_reg_read(uint16_t reg)
{
pdc_packet_t g_pdc_spi_tx_packet;
pdc_packet_t g_pdc_spi_rx_packet;
uint16_t cmd = 0;
uint16_t res = 0;
int iTryCount = 3;

	while( iTryCount-- > 0 )
	{
	uint32_t ulStatus;

		spi_clear_ovres();
		/* Move register address to cmd bits 9-2, make 32-bit address. */
		cmd = (reg << 2) & REG_ADDR_MASK;

		/* Last 2 bits still under "don't care bits" handled with byte enable. */
		/* Select byte enable for command. */
		if (reg & 2) {
			/* Odd word address writes bytes 2 and 3 */
			cmd |= (0xc << 10);
		} else {
			/* Even word address write bytes 0 and 1 */
			cmd |= (0x3 << 10);
		}

		/* Add command read code. */
		cmd |= CMD_READ;
		cmdBuf.uc[0] = cmd >> 8;
		cmdBuf.uc[1] = cmd & 0xff;
		cmdBuf.uc[2] = CONFIG_SPI_MASTER_DUMMY;
		cmdBuf.uc[3] = CONFIG_SPI_MASTER_DUMMY;

		/* Prepare PDC transfer. */
		g_pdc_spi_tx_packet.ul_addr = (uint32_t) cmdBuf.uc;
		g_pdc_spi_tx_packet.ul_size = 4;
		g_pdc_spi_rx_packet.ul_addr = (uint32_t) tmpbuf;
		g_pdc_spi_rx_packet.ul_size = 4;
		pdc_disable_transfer(g_p_spi_pdc, PERIPH_PTCR_RXTDIS | PERIPH_PTCR_TXTDIS);
		pdc_tx_init(g_p_spi_pdc, &g_pdc_spi_tx_packet, NULL);
		pdc_rx_init(g_p_spi_pdc, &g_pdc_spi_rx_packet, NULL);
	gpio_set_pin_low(KSZ8851SNL_CSN_GPIO);

	spi_disable_interrupt( KSZ8851SNL_SPI, ~0ul );
		pdc_enable_transfer(g_p_spi_pdc, PERIPH_PTCR_RXTEN | PERIPH_PTCR_TXTEN);
		for( ;; )
		{
			ulStatus = spi_read_status( KSZ8851SNL_SPI );
			if( ( ulStatus & ( SPI_SR_OVRES | SPI_SR_ENDRX ) ) != 0 )
			{
				break;
			}
		}
		gpio_set_pin_high( KSZ8851SNL_CSN_GPIO );
		if( ( ulStatus & SPI_SR_OVRES ) == 0 )
		{
			break;
		}
		pdc_disable_transfer(g_p_spi_pdc, PERIPH_PTCR_RXTDIS | PERIPH_PTCR_TXTDIS);
		lUDPLoggingPrintf( "ksz8851_reg_read: SPI_SR_OVRES\n" );
	}

	res = (tmpbuf[3] << 8) | tmpbuf[2];
	return res;
}

/**
 * \brief Write a register value.
 *
 * \param reg the register address to modify.
 * \param wrdata the new register value.
 */
void ksz8851_reg_write(uint16_t reg, uint16_t wrdata)
{
pdc_packet_t g_pdc_spi_tx_packet;
pdc_packet_t g_pdc_spi_rx_packet;
uint16_t cmd = 0;
int iTryCount = 3;

	while( iTryCount-- > 0 )
	{
	uint32_t ulStatus;


		spi_clear_ovres();
		/* Move register address to cmd bits 9-2, make 32-bit address. */
		cmd = (reg << 2) & REG_ADDR_MASK;

		/* Last 2 bits still under "don't care bits" handled with byte enable. */
		/* Select byte enable for command. */
		if (reg & 2) {
			/* Odd word address writes bytes 2 and 3 */
			cmd |= (0xc << 10);
		} else {
			/* Even word address write bytes 0 and 1 */
			cmd |= (0x3 << 10);
		}

		/* Add command write code. */
		cmd |= CMD_WRITE;
		cmdBuf.uc[0] = cmd >> 8;
		cmdBuf.uc[1] = cmd & 0xff;
		cmdBuf.uc[2] = wrdata & 0xff;
		cmdBuf.uc[3] = wrdata >> 8;

		/* Prepare PDC transfer. */
		g_pdc_spi_tx_packet.ul_addr = (uint32_t) cmdBuf.uc;
		g_pdc_spi_tx_packet.ul_size = 4;
		g_pdc_spi_rx_packet.ul_addr = (uint32_t) tmpbuf;
		g_pdc_spi_rx_packet.ul_size = 4;
		pdc_disable_transfer(g_p_spi_pdc, PERIPH_PTCR_RXTDIS | PERIPH_PTCR_TXTDIS);
		pdc_tx_init(g_p_spi_pdc, &g_pdc_spi_tx_packet, NULL);
		pdc_rx_init(g_p_spi_pdc, &g_pdc_spi_rx_packet, NULL);
		gpio_set_pin_low(KSZ8851SNL_CSN_GPIO);

		spi_disable_interrupt( KSZ8851SNL_SPI, ~0ul );

		pdc_enable_transfer(g_p_spi_pdc, PERIPH_PTCR_RXTEN | PERIPH_PTCR_TXTEN);
		for( ;; )
		{
			ulStatus = spi_read_status( KSZ8851SNL_SPI );
			if( ( ulStatus & ( SPI_SR_OVRES | SPI_SR_ENDRX ) ) != 0 )
			{
				break;
			}
		}
		gpio_set_pin_high( KSZ8851SNL_CSN_GPIO );
		if( ( ulStatus & SPI_SR_OVRES ) == 0 )
		{
			break;
		}
		pdc_disable_transfer(g_p_spi_pdc, PERIPH_PTCR_RXTDIS | PERIPH_PTCR_TXTDIS);
		lUDPLoggingPrintf( "ksz8851_reg_write: SPI_SR_OVRES\n" );
	}
}

static void spi_clear_ovres( void )
{
volatile uint32_t rc;
	rc = KSZ8851SNL_SPI->SPI_RDR;

	spi_read_status( KSZ8851SNL_SPI );
}

/**
 * \brief Read internal fifo buffer.
 *
 * \param buf the buffer to store the data from the fifo buffer.
 * \param len the amount of data to read.
 */
void ksz8851_fifo_read(uint8_t *buf, uint32_t len)
{
	pdc_packet_t g_pdc_spi_tx_packet;
	pdc_packet_t g_pdc_spi_rx_packet;
	pdc_packet_t g_pdc_spi_tx_npacket;
	pdc_packet_t g_pdc_spi_rx_npacket;

	memset( cmdBuf.uc, '\0', sizeof cmdBuf );
	cmdBuf.uc[0] = FIFO_READ;
	spi_clear_ovres();

	/* Prepare PDC transfer. */
	g_pdc_spi_tx_packet.ul_addr = (uint32_t) cmdBuf.uc;
	g_pdc_spi_tx_packet.ul_size = 9;
	g_pdc_spi_rx_packet.ul_addr = (uint32_t) respBuf.uc;
	g_pdc_spi_rx_packet.ul_size = 9;

	g_pdc_spi_tx_npacket.ul_addr = (uint32_t) buf;
	g_pdc_spi_tx_npacket.ul_size = len;
	g_pdc_spi_rx_npacket.ul_addr = (uint32_t) buf;
	g_pdc_spi_rx_npacket.ul_size = len;
	pdc_disable_transfer(g_p_spi_pdc, PERIPH_PTCR_RXTDIS | PERIPH_PTCR_TXTDIS);
	pdc_tx_init(g_p_spi_pdc, &g_pdc_spi_tx_packet, &g_pdc_spi_tx_npacket);
	pdc_rx_init(g_p_spi_pdc, &g_pdc_spi_rx_packet, &g_pdc_spi_rx_npacket);

spi_enable_interrupt(KSZ8851SNL_SPI, SPI_IER_RXBUFF | SPI_IER_OVRES);

	pdc_enable_transfer(g_p_spi_pdc, PERIPH_PTCR_RXTEN | PERIPH_PTCR_TXTEN);
}

/**
 * \brief Write internal fifo buffer.
 *
 * \param buf the buffer to send to the fifo buffer.
 * \param ulActualLength the total amount of data to write.
 * \param ulFIFOLength the size of the first pbuf to write from the pbuf chain.
 */
void ksz8851_fifo_write(uint8_t *buf, uint32_t ulActualLength, uint32_t ulFIFOLength)
{
	static uint8_t frameID = 0;

	pdc_packet_t g_pdc_spi_tx_packet;
	pdc_packet_t g_pdc_spi_rx_packet;
	pdc_packet_t g_pdc_spi_tx_npacket;
	pdc_packet_t g_pdc_spi_rx_npacket;

	/* Prepare control word and byte count. */
	cmdBuf.uc[0] = FIFO_WRITE;
	cmdBuf.uc[1] = frameID++ & 0x3f;
	cmdBuf.uc[2] = 0;
	cmdBuf.uc[3] = ulActualLength & 0xff;
	cmdBuf.uc[4] = ulActualLength >> 8;

	spi_clear_ovres();

	/* Prepare PDC transfer. */
	g_pdc_spi_tx_packet.ul_addr = (uint32_t) cmdBuf.uc;
	g_pdc_spi_tx_packet.ul_size = 5;

	g_pdc_spi_rx_packet.ul_addr = (uint32_t) respBuf.uc;
	g_pdc_spi_rx_packet.ul_size = 5;

	g_pdc_spi_tx_npacket.ul_addr = (uint32_t) buf;
	g_pdc_spi_tx_npacket.ul_size = ulFIFOLength;

	g_pdc_spi_rx_npacket.ul_addr = (uint32_t) tmpbuf;
	g_pdc_spi_rx_npacket.ul_size = ulFIFOLength;

	pdc_disable_transfer(g_p_spi_pdc, PERIPH_PTCR_RXTDIS | PERIPH_PTCR_TXTDIS);
	pdc_tx_init(g_p_spi_pdc, &g_pdc_spi_tx_packet, &g_pdc_spi_tx_npacket);
	#if( TX_USES_RECV == 1 )
		pdc_rx_init(g_p_spi_pdc, &g_pdc_spi_rx_packet, &g_pdc_spi_rx_npacket);
		spi_enable_interrupt(KSZ8851SNL_SPI, SPI_IER_ENDRX | SPI_IER_OVRES);
		pdc_enable_transfer(g_p_spi_pdc, PERIPH_PTCR_RXTEN | PERIPH_PTCR_TXTEN);
	#else
		spi_enable_interrupt(KSZ8851SNL_SPI, SPI_SR_TXBUFE | SPI_IER_OVRES);
		pdc_enable_transfer(g_p_spi_pdc, PERIPH_PTCR_TXTEN);
	#endif
}

/**
 * \brief Write dummy data to the internal fifo buffer.
 *
 * \param len the amount of dummy data to write.
 */
void ksz8851_fifo_dummy(uint32_t len)
{
	pdc_packet_t g_pdc_spi_tx_packet;
	pdc_packet_t g_pdc_spi_rx_packet;

	/* Prepare PDC transfer. */
	g_pdc_spi_tx_packet.ul_addr = (uint32_t) tmpbuf;
	g_pdc_spi_tx_packet.ul_size = len;
	g_pdc_spi_rx_packet.ul_addr = (uint32_t) tmpbuf;
	g_pdc_spi_rx_packet.ul_size = len;
	pdc_disable_transfer(g_p_spi_pdc, PERIPH_PTCR_RXTDIS | PERIPH_PTCR_TXTDIS);
	pdc_tx_init(g_p_spi_pdc, &g_pdc_spi_tx_packet, NULL);
	pdc_rx_init(g_p_spi_pdc, &g_pdc_spi_rx_packet, NULL);
	pdc_enable_transfer(g_p_spi_pdc, PERIPH_PTCR_RXTEN | PERIPH_PTCR_TXTEN);

	while (!(spi_read_status(KSZ8851SNL_SPI) & SPI_SR_ENDRX))
		;
}

void ksz8851snl_set_registers(void)
{
	/* Init step2-4: write QMU MAC address (low, middle then high). */
	ksz8851_reg_write(REG_MAC_ADDR_0, (ETHERNET_CONF_ETHADDR4 << 8) | ETHERNET_CONF_ETHADDR5);
	ksz8851_reg_write(REG_MAC_ADDR_2, (ETHERNET_CONF_ETHADDR2 << 8) | ETHERNET_CONF_ETHADDR3);
	ksz8851_reg_write(REG_MAC_ADDR_4, (ETHERNET_CONF_ETHADDR0 << 8) | ETHERNET_CONF_ETHADDR1);

	/* Init step5: enable QMU Transmit Frame Data Pointer Auto Increment. */
	ksz8851_reg_write(REG_TX_ADDR_PTR, ADDR_PTR_AUTO_INC);

	/* Init step6: configure QMU transmit control register. */
	ksz8851_reg_write(REG_TX_CTRL,
			TX_CTRL_ICMP_CHECKSUM |
			TX_CTRL_UDP_CHECKSUM |
			TX_CTRL_TCP_CHECKSUM |
			TX_CTRL_IP_CHECKSUM |
			TX_CTRL_FLOW_ENABLE |
			TX_CTRL_PAD_ENABLE |
			TX_CTRL_CRC_ENABLE
		);

	/* Init step7: enable QMU Receive Frame Data Pointer Auto Increment. */
	ksz8851_reg_write(REG_RX_ADDR_PTR, ADDR_PTR_AUTO_INC);

	/* Init step8: configure QMU Receive Frame Threshold for one frame. */
	ksz8851_reg_write(REG_RX_FRAME_CNT_THRES, 1);

	/* Init step9: configure QMU receive control register1. */
	ksz8851_reg_write(REG_RX_CTRL1,
			RX_CTRL_UDP_CHECKSUM |
			RX_CTRL_TCP_CHECKSUM |
			RX_CTRL_IP_CHECKSUM |
			RX_CTRL_MAC_FILTER |
			RX_CTRL_FLOW_ENABLE |
			RX_CTRL_BROADCAST |
			RX_CTRL_ALL_MULTICAST|
			RX_CTRL_UNICAST);
//	ksz8851_reg_write(REG_RX_CTRL1,
//			RX_CTRL_UDP_CHECKSUM |
//			RX_CTRL_TCP_CHECKSUM |
//			RX_CTRL_IP_CHECKSUM |
//			RX_CTRL_FLOW_ENABLE |
//			RX_CTRL_PROMISCUOUS);

	ksz8851_reg_write(REG_RX_CTRL2,
			RX_CTRL_IPV6_UDP_NOCHECKSUM |
			RX_CTRL_UDP_LITE_CHECKSUM |
			RX_CTRL_ICMP_CHECKSUM |
			RX_CTRL_BURST_LEN_FRAME);


//#define   RXQ_TWOBYTE_OFFSET          (0x0200)    /* Enable adding 2-byte before frame header for IP aligned with DWORD */
#warning Remember to try the above option to get a 2-byte offset

	/* Init step11: configure QMU receive queue: trigger INT and auto-dequeue frame. */
	ksz8851_reg_write( REG_RXQ_CMD, RXQ_CMD_CNTL | RXQ_TWOBYTE_OFFSET );

	/* Init step12: adjust SPI data output delay. */
	ksz8851_reg_write(REG_BUS_CLOCK_CTRL, BUS_CLOCK_166 | BUS_CLOCK_DIVIDEDBY_1);

	/* Init step13: restart auto-negotiation. */
	ksz8851_reg_setbits(REG_PORT_CTRL, PORT_AUTO_NEG_RESTART);

	/* Init step13.1: force link in half duplex if auto-negotiation failed. */
	if ((ksz8851_reg_read(REG_PORT_CTRL) & PORT_AUTO_NEG_RESTART) != PORT_AUTO_NEG_RESTART)
	{
		ksz8851_reg_clrbits(REG_PORT_CTRL, PORT_FORCE_FULL_DUPLEX);
	}

	/* Init step14: clear interrupt status. */
	ksz8851_reg_write(REG_INT_STATUS, 0xFFFF);

	/* Init step15: set interrupt mask. */
	ksz8851_reg_write(REG_INT_MASK, INT_RX);

	/* Init step16: enable QMU Transmit. */
	ksz8851_reg_setbits(REG_TX_CTRL, TX_CTRL_ENABLE);

	/* Init step17: enable QMU Receive. */
	ksz8851_reg_setbits(REG_RX_CTRL1, RX_CTRL_ENABLE);
}
/**
 * \brief KSZ8851SNL initialization function.
 *
 * \return 0 on success, 1 on communication error.
 */
uint32_t ksz8851snl_init(void)
{
uint32_t count = 10;
uint16_t dev_id = 0;
uint8_t id_ok = 0;

	/* Configure the SPI peripheral. */
	spi_enable_clock(KSZ8851SNL_SPI);
	spi_disable(KSZ8851SNL_SPI);
	spi_reset(KSZ8851SNL_SPI);
	spi_set_master_mode(KSZ8851SNL_SPI);
	spi_disable_mode_fault_detect(KSZ8851SNL_SPI);
	spi_set_peripheral_chip_select_value(KSZ8851SNL_SPI, ~(uint32_t)(1UL << KSZ8851SNL_CS_PIN));
spi_set_fixed_peripheral_select(KSZ8851SNL_SPI);
//spi_disable_peripheral_select_decode(KSZ8851SNL_SPI);

	spi_set_clock_polarity(KSZ8851SNL_SPI, KSZ8851SNL_CS_PIN, SPI_CLK_POLARITY);
	spi_set_clock_phase(KSZ8851SNL_SPI, KSZ8851SNL_CS_PIN, SPI_CLK_PHASE);
	spi_set_bits_per_transfer(KSZ8851SNL_SPI, KSZ8851SNL_CS_PIN,
			SPI_CSR_BITS_8_BIT);
	spi_set_baudrate_div(KSZ8851SNL_SPI, KSZ8851SNL_CS_PIN, (sysclk_get_cpu_hz() / KSZ8851SNL_CLOCK_SPEED));
//	spi_set_transfer_delay(KSZ8851SNL_SPI, KSZ8851SNL_CS_PIN, CONFIG_SPI_MASTER_DELAY_BS,
//			CONFIG_SPI_MASTER_DELAY_BCT);


	spi_set_transfer_delay(KSZ8851SNL_SPI, KSZ8851SNL_CS_PIN, 0, 0);

	spi_enable(KSZ8851SNL_SPI);

	/* Get pointer to UART PDC register base. */
	g_p_spi_pdc = spi_get_pdc_base(KSZ8851SNL_SPI);
	pdc_enable_transfer(g_p_spi_pdc, PERIPH_PTCR_RXTEN | PERIPH_PTCR_TXTEN);

	/* Control RSTN and CSN pin from the driver. */
	gpio_configure_pin(KSZ8851SNL_CSN_GPIO, KSZ8851SNL_CSN_FLAGS);
	gpio_set_pin_high(KSZ8851SNL_CSN_GPIO);
	gpio_configure_pin(KSZ8851SNL_RSTN_GPIO, KSZ8851SNL_RSTN_FLAGS);

	/* Reset the Micrel in a proper state. */
	while( count-- )
	{
		/* Perform hardware reset with respect to the reset timing from the datasheet. */
		gpio_set_pin_low(KSZ8851SNL_RSTN_GPIO);
		vTaskDelay(2);
		gpio_set_pin_high(KSZ8851SNL_RSTN_GPIO);
		vTaskDelay(2);

		/* Init step1: read chip ID. */
		dev_id = ksz8851_reg_read(REG_CHIP_ID);
		if( ( dev_id & 0xFFF0 ) == CHIP_ID_8851_16 )
		{
			id_ok = 1;
			break;
		}
	}
	if( id_ok != 0 )
	{
		ksz8851snl_set_registers();
	}

	return id_ok ? 1 : -1;
}

uint32_t ksz8851snl_reinit(void)
{
uint32_t count = 10;
uint16_t dev_id = 0;
uint8_t id_ok = 0;
	/* Reset the Micrel in a proper state. */
	while( count-- )
	{
		/* Perform hardware reset with respect to the reset timing from the datasheet. */
		gpio_set_pin_low(KSZ8851SNL_RSTN_GPIO);
		vTaskDelay(2);
		gpio_set_pin_high(KSZ8851SNL_RSTN_GPIO);
		vTaskDelay(2);

		/* Init step1: read chip ID. */
		dev_id = ksz8851_reg_read(REG_CHIP_ID);
		if( ( dev_id & 0xFFF0 ) == CHIP_ID_8851_16 )
		{
			id_ok = 1;
			break;
		}
	}
	if( id_ok != 0 )
	{
		ksz8851snl_set_registers();
	}

	return id_ok ? 1 : -1;
}

uint32_t ksz8851snl_reset_rx( void )
{
uint16_t usValue;

	usValue = ksz8851_reg_read(REG_RX_CTRL1);

	usValue &= ~( ( uint16_t ) RX_CTRL_ENABLE | RX_CTRL_FLUSH_QUEUE );

	ksz8851_reg_write( REG_RX_CTRL1, usValue ); vTaskDelay( 2 );
	ksz8851_reg_write( REG_RX_CTRL1, usValue | RX_CTRL_FLUSH_QUEUE ); vTaskDelay( 1 );
	ksz8851_reg_write( REG_RX_CTRL1, usValue ); vTaskDelay( 1 );
	ksz8851_reg_write( REG_RX_CTRL1, usValue | RX_CTRL_ENABLE ); vTaskDelay( 1 );

	return ( uint32_t )usValue;
}

uint32_t ksz8851snl_reset_tx( void )
{
uint16_t usValue;

	usValue = ksz8851_reg_read( REG_TX_CTRL );

	usValue &= ~( ( uint16_t ) TX_CTRL_ENABLE | TX_CTRL_FLUSH_QUEUE );

	ksz8851_reg_write( REG_TX_CTRL, usValue ); vTaskDelay( 2 );
	ksz8851_reg_write( REG_TX_CTRL, usValue | TX_CTRL_FLUSH_QUEUE ); vTaskDelay( 1 );
	ksz8851_reg_write( REG_TX_CTRL, usValue ); vTaskDelay( 1 );
	ksz8851_reg_write( REG_TX_CTRL, usValue | TX_CTRL_ENABLE ); vTaskDelay( 1 );

	return ( uint32_t )usValue;
}
