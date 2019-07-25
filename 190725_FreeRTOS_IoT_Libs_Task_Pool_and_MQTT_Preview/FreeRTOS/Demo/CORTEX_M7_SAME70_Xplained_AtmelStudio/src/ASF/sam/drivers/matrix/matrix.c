/**
 * \file
 *
 * \brief Matrix driver for SAM.
 *
 * Copyright (c) 2012-2015 Atmel Corporation. All rights reserved.
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

#include  "matrix.h"

/* / @cond 0 */
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/* / @endcond */

/**
 * \defgroup sam_drivers_matrix_group Matrix (MATRIX)
 *
 * \par Purpose
 *
 * The Bus Matrix implements a multi-layer AHB that enables parallel access
 * paths between multiple AHB masters and slaves in a system, which increases
 * the overall bandwidth.
 *
 * @{
 */

#if SAM4C
#ifdef SAM4C_0
#define MATRIX MATRIX0
#else
#define MATRIX MATRIX1
#endif
#endif

#if SAM4CP
#ifdef SAM4CP_0
#define MATRIX MATRIX0
#else
#define MATRIX MATRIX1
#endif
#endif

#if SAM4CM
#ifdef SAM4CM_0
#define MATRIX MATRIX0
#else
#define MATRIX MATRIX1
#endif
#endif

#ifndef MATRIX_WPMR_WPKEY_PASSWD
#define MATRIX_WPMR_WPKEY_PASSWD    MATRIX_WPMR_WPKEY(0x4D4154U)
#endif

/**
 * \brief Set undefined length burst type of the specified master.
 *
 * \param ul_id Master index.
 * \param burst_type Undefined length burst type.
 */
void matrix_set_master_burst_type(uint32_t ul_id, burst_type_t burst_type)
{
#if (SAMV70 || SAMS70|| SAME70)
	Matrix *p_matrix = MATRIX;
	volatile uint32_t *p_MCFG;
	volatile uint32_t ul_reg;
	uint32_t ul_dlt;

	ul_dlt = (uint32_t)&(p_matrix->MATRIX_MCFG1);
	ul_dlt = ul_dlt - (uint32_t)&(p_matrix->MATRIX_MCFG0);

	p_MCFG = (volatile uint32_t *)((uint32_t)&(p_matrix->MATRIX_MCFG0) +
			ul_id * ul_dlt);

	ul_reg = *p_MCFG & (~MATRIX_MCFG0_ULBT_Msk);
	*p_MCFG = ul_reg | (uint32_t)burst_type;
#else
	Matrix *p_matrix = MATRIX;
	volatile uint32_t ul_reg;

	ul_reg = p_matrix->MATRIX_MCFG[ul_id] & (~MATRIX_MCFG_ULBT_Msk);
	p_matrix->MATRIX_MCFG[ul_id] = ul_reg | (uint32_t)burst_type;
#endif
}

/**
 * \brief Get undefined length burst type of the specified master.
 *
 * \param ul_id Master index.
 *
 * \return Undefined length burst type.
 */
burst_type_t matrix_get_master_burst_type(uint32_t ul_id)
{
#if (SAMV70 || SAMS70|| SAME70)
	Matrix *p_matrix = MATRIX;
	volatile uint32_t *p_MCFG;
	volatile uint32_t ul_reg;
	uint32_t ul_dlt;

	ul_dlt = (uint32_t)&(p_matrix->MATRIX_MCFG1);
	ul_dlt = ul_dlt - (uint32_t)&(p_matrix->MATRIX_MCFG0);

	p_MCFG = (volatile uint32_t *)((uint32_t)&(p_matrix->MATRIX_MCFG0) +
			ul_id * ul_dlt);

	ul_reg = *p_MCFG & (~MATRIX_MCFG0_ULBT_Msk);
	return (burst_type_t)ul_reg;
#else
	Matrix *p_matrix = MATRIX;
	volatile uint32_t ul_reg;

	ul_reg = p_matrix->MATRIX_MCFG[ul_id] & (MATRIX_MCFG_ULBT_Msk);
	return (burst_type_t)ul_reg;
#endif
}

/**
 * \brief Set slot cycle of the specified slave.
 *
 * \param ul_id Slave index.
 * \param ul_slot_cycle Number of slot cycle.
 */
void matrix_set_slave_slot_cycle(uint32_t ul_id, uint32_t ul_slot_cycle)
{
	Matrix *p_matrix = MATRIX;
	volatile uint32_t ul_reg;

	ul_reg = p_matrix->MATRIX_SCFG[ul_id] & (~MATRIX_SCFG_SLOT_CYCLE_Msk);
	p_matrix->MATRIX_SCFG[ul_id] = ul_reg | MATRIX_SCFG_SLOT_CYCLE(
			ul_slot_cycle);
}

/**
 * \brief Get slot cycle of the specified slave.
 *
 * \param ul_id Slave index.
 *
 * \return Number of slot cycle.
 */
uint32_t matrix_get_slave_slot_cycle(uint32_t ul_id)
{
	Matrix *p_matrix = MATRIX;
	volatile uint32_t ul_reg;

	ul_reg = p_matrix->MATRIX_SCFG[ul_id] & (MATRIX_SCFG_SLOT_CYCLE_Msk);
	return (ul_reg >> MATRIX_SCFG_SLOT_CYCLE_Pos);
}

/**
 * \brief Set default master type of the specified slave.
 *
 * \param ul_id Slave index.
 * \param type Default master type.
 */
void matrix_set_slave_default_master_type(uint32_t ul_id, defaut_master_t type)
{
	Matrix *p_matrix = MATRIX;
	volatile uint32_t ul_reg;

	ul_reg = p_matrix->MATRIX_SCFG[ul_id] & (~MATRIX_SCFG_DEFMSTR_TYPE_Msk);
	p_matrix->MATRIX_SCFG[ul_id] = ul_reg | (uint32_t)type;
}

/**
 * \brief Get default master type of the specified slave.
 *
 * \param ul_id Slave index.
 *
 * \return Default master type.
 */
defaut_master_t matrix_get_slave_default_master_type(uint32_t ul_id)
{
	Matrix *p_matrix = MATRIX;
	volatile uint32_t ul_reg;

	ul_reg = p_matrix->MATRIX_SCFG[ul_id] & (MATRIX_SCFG_DEFMSTR_TYPE_Msk);
	return (defaut_master_t)ul_reg;
}

/**
 * \brief Set fixed default master of the specified slave.
 *
 * \param ul_id Slave index.
 * \param ul_fixed_id Fixed default master index.
 */
void matrix_set_slave_fixed_default_master(uint32_t ul_id, uint32_t ul_fixed_id)
{
	Matrix *p_matrix = MATRIX;
	volatile uint32_t ul_reg;

	ul_reg = p_matrix->MATRIX_SCFG[ul_id] &
			(~MATRIX_SCFG_FIXED_DEFMSTR_Msk);
	p_matrix->MATRIX_SCFG[ul_id]
		= ul_reg | MATRIX_SCFG_FIXED_DEFMSTR(ul_fixed_id);
}

/**
 * \brief Get fixed default master of the specified slave.
 *
 * \param ul_id Slave index.
 *
 * \return Fixed default master index.
 */
uint32_t matrix_get_slave_fixed_default_master(uint32_t ul_id)
{
	Matrix *p_matrix = MATRIX;
	volatile uint32_t ul_reg;

	ul_reg = p_matrix->MATRIX_SCFG[ul_id] & (MATRIX_SCFG_FIXED_DEFMSTR_Msk);
	return (ul_reg >> MATRIX_SCFG_FIXED_DEFMSTR_Pos);
}

#if !SAM4E && !SAM4C && !SAM4CP && !SAM4CM && \
	 !SAMV71 && !SAMV70 && !SAMS70 && !SAME70
/**
 * \brief Set slave arbitration type of the specified slave.
 *
 * \param ul_id Slave index.
 * \param type Arbitration type.
 */
void matrix_set_slave_arbitration_type(uint32_t ul_id, arbitration_type_t type)
{
	Matrix *p_matrix = MATRIX;
	volatile uint32_t ul_reg;

	ul_reg = p_matrix->MATRIX_SCFG[ul_id] & (~MATRIX_SCFG_ARBT_Msk);
	p_matrix->MATRIX_SCFG[ul_id] = ul_reg | (uint32_t)type;
}

/**
 * \brief Get slave arbitration type of the specified slave.
 *
 * \param ul_id Slave index.
 *
 * \return Arbitration type.
 */
arbitration_type_t matrix_get_slave_arbitration_type(uint32_t ul_id)
{
	Matrix *p_matrix = MATRIX;
	volatile uint32_t ul_reg;

	ul_reg = p_matrix->MATRIX_SCFG[ul_id] & (MATRIX_SCFG_ARBT_Msk);
	return (arbitration_type_t)ul_reg;
}

#endif

/**
 * \brief Set priority for the specified slave access.
 *
 * \param ul_id Slave index.
 * \param ul_prio Bitmask OR of priorities of master x.
 */
void matrix_set_slave_priority(uint32_t ul_id, uint32_t ul_prio)
{
#if (SAMV71 || SAMV70|| SAME70)
	Matrix *p_matrix = MATRIX;
	p_matrix->MATRIX_PR[ul_id].MATRIX_PRAS = ul_prio;
#else
	Matrix *p_matrix = MATRIX;
	volatile uint32_t *p_PRAS;
	uint32_t ul_dlt;

	ul_dlt = (uint32_t)&(p_matrix->MATRIX_PRAS1);
	ul_dlt = ul_dlt - (uint32_t)&(p_matrix->MATRIX_PRAS0);

	p_PRAS = (volatile uint32_t *)((uint32_t)&(p_matrix->MATRIX_PRAS0) +
			ul_id * ul_dlt);

	*p_PRAS = ul_prio;
#endif
}

/**
 * \brief Get priority for the specified slave access.
 *
 * \param ul_id Slave index.
 *
 * \return Bitmask OR of priorities of master x.
 */
uint32_t matrix_get_slave_priority(uint32_t ul_id)
{
#if (SAMV71 || SAMV70|| SAME70)
	Matrix *p_matrix = MATRIX;
	return p_matrix->MATRIX_PR[ul_id].MATRIX_PRAS;
#else
	Matrix *p_matrix = MATRIX;
	volatile uint32_t *p_PRAS;
	uint32_t ul_dlt;

	ul_dlt = (uint32_t)&(p_matrix->MATRIX_PRAS1);
	ul_dlt = ul_dlt - (uint32_t)&(p_matrix->MATRIX_PRAS0);

	p_PRAS = (volatile uint32_t *)((uint32_t)&(p_matrix->MATRIX_PRAS0) +
			ul_id * ul_dlt);

	return (*p_PRAS);
#endif
}

#if (SAMV71 || SAMV70|| SAME70 || SAMS70)
/**
 * \brief Set priority for the specified slave access.
 *
 * \param ul_id Slave index.
 * \param ul_prio_b Bitmask OR of priorities of master x.
 */
void matrix_set_slave_priority_b(uint32_t ul_id, uint32_t ul_prio_b)
{
#if (SAMV71 || SAMV70|| SAME70)
	Matrix *p_matrix = MATRIX;
	p_matrix->MATRIX_PR[ul_id].MATRIX_PRBS = ul_prio_b;
#else
	Matrix *p_matrix = MATRIX;
	volatile uint32_t *p_PRAS;
	uint32_t ul_dlt;

	ul_dlt = (uint32_t)&(p_matrix->MATRIX_PRBS1);
	ul_dlt = ul_dlt - (uint32_t)&(p_matrix->MATRIX_PRBS0);

	p_PRAS = (volatile uint32_t *)((uint32_t)&(p_matrix->MATRIX_PRBS0) +
			ul_id * ul_dlt);

	*p_PRAS = ul_prio;
#endif
}

/**
 * \brief Get priority for the specified slave access.
 *
 * \param ul_id Slave index.
 *
 * \return Bitmask OR of priorities of master x.
 */
uint32_t matrix_get_slave_priority_b(uint32_t ul_id)
{
#if (SAMV71 || SAMV70|| SAME70)
	Matrix *p_matrix = MATRIX;
	return p_matrix->MATRIX_PR[ul_id].MATRIX_PRBS;
#else
	Matrix *p_matrix = MATRIX;
	volatile uint32_t *p_PRAS;
	uint32_t ul_dlt;

	ul_dlt = (uint32_t)&(p_matrix->MATRIX_PRBS1);
	ul_dlt = ul_dlt - (uint32_t)&(p_matrix->MATRIX_PRBS0);

	p_PRAS = (volatile uint32_t *)((uint32_t)&(p_matrix->MATRIX_PRBS0) +
			ul_id * ul_dlt);

	return (*p_PRAS);
#endif
}
#endif

#if (SAM3XA || SAM3U || SAM4E ||\
	 SAMV71 || SAMV70 || SAMS70 || SAME70)
/**
 * \brief Set bus matrix master remap.
 *
 * \param ul_remap Bitmask OR of RCBx: 0 for disable, 1 for enable.
 */
void matrix_set_master_remap(uint32_t ul_remap)
{
	Matrix *p_matrix = MATRIX;

	p_matrix->MATRIX_MRCR = ul_remap;
}

/**
 * \brief Get bus matrix master remap.
 *
 * \return Bitmask OR of RCBx: 0 for disable, 1 for enable.
 */
uint32_t matrix_get_master_remap(void)
{
	Matrix *p_matrix = MATRIX;

	return (p_matrix->MATRIX_MRCR);
}

#endif

#if (SAM3S || SAM3XA || SAM3N || SAM4S || SAM4E || SAM4N || SAM4C || SAMG || SAM4CP || SAM4CM || \
	 SAMV71 || SAMV70 || SAMS70 || SAME70)
/**
 * \brief Set system IO.
 *
 * \param ul_io Bitmask OR of SYSIOx.
 */
void matrix_set_system_io(uint32_t ul_io)
{
	Matrix *p_matrix = MATRIX;

#if (SAM4C || SAM4CP || SAM4CM)

	p_matrix->MATRIX_SYSIO = ul_io;

#elif (SAMV71 || SAMV70 || SAMS70 || SAME70)
	
	p_matrix->CCFG_SYSIO &= 0xFFFF0000;
	p_matrix->CCFG_SYSIO |= (ul_io & 0xFFFF);

#else

	p_matrix->CCFG_SYSIO = ul_io;

#endif

}

/**
 * \brief Get system IO.
 *
 * \return Bitmask OR of SYSIOx.
 */
uint32_t matrix_get_system_io(void)
{
	Matrix *p_matrix = MATRIX;

#if (SAM4C || SAM4CP || SAM4CM)

	return (p_matrix->MATRIX_SYSIO);

#elif (SAMV71 || SAMV70 || SAMS70 || SAME70)

	return (p_matrix->CCFG_SYSIO & 0xFFFF);

#else

	return (p_matrix->CCFG_SYSIO);

#endif
}

#endif

#if (SAM3S || SAM4S || SAM4E || SAM4C || SAM4CP || SAM4CM || \
	 SAMV71 || SAMV70 || SAMS70 || SAME70)
/**
 * \brief Set NAND Flash Chip Select configuration register.
 *
 * \param ul_cs Bitmask OR of SMC_NFCSx: 0 if NCSx is not assigned,
 * 1 if NCSx is assigned.
 */
void matrix_set_nandflash_cs(uint32_t ul_cs)
{
	Matrix *p_matrix = MATRIX;


#if (SAM4C || SAM4CP || SAM4CM)

	p_matrix->MATRIX_SMCNFCS = ul_cs;

#else

	p_matrix->CCFG_SMCNFCS = ul_cs;

#endif
}

/**
 * \brief Get NAND Flash Chip Select configuration register.
 *
 * \return Bitmask OR of SMC_NFCSx.
 */
uint32_t matrix_get_nandflash_cs(void)
{
	Matrix *p_matrix = MATRIX;

#if (SAM4C || SAM4CP || SAM4CM)

	return (p_matrix->MATRIX_SMCNFCS);

#else

	return (p_matrix->CCFG_SMCNFCS);

#endif
}

#endif

#if (!SAMG)
/**
 * \brief Enable or disable write protect of MATRIX registers.
 *
 * \param ul_enable 1 to enable, 0 to disable.
 */
void matrix_set_writeprotect(uint32_t ul_enable)
{
	Matrix *p_matrix = MATRIX;

	if (ul_enable) {
		p_matrix->MATRIX_WPMR = MATRIX_WPMR_WPKEY_PASSWD | MATRIX_WPMR_WPEN;
	} else {
		p_matrix->MATRIX_WPMR = MATRIX_WPMR_WPKEY_PASSWD;
	}
}

/**
 * \brief Get write protect status.
 *
 * \return Write protect status.
 */
uint32_t matrix_get_writeprotect_status(void)
{
	Matrix *p_matrix = MATRIX;

	return (p_matrix->MATRIX_WPSR);
}
#endif

#if SAMG55
/**
 * \brief Set USB device mode.
 *
 */
void matrix_set_usb_device(void)
{
	Matrix *p_matrix = MATRIX;

	p_matrix->CCFG_SYSIO &= ~(CCFG_SYSIO_SYSIO10 | CCFG_SYSIO_SYSIO11);

	p_matrix->CCFG_USBMR |= CCFG_USBMR_DEVICE;
}

/**
 * \brief Set USB device mode.
 *
 */
void matrix_set_usb_host(void)
{
	Matrix *p_matrix = MATRIX;

	p_matrix->CCFG_SYSIO &= ~(CCFG_SYSIO_SYSIO10 | CCFG_SYSIO_SYSIO11);

	p_matrix->CCFG_USBMR &= ~CCFG_USBMR_DEVICE;
}
#endif

#if (SAMV71 || SAMV70|| SAME70)
/**
 * \brief Set CAN0 DMA base address.
 *
 * \param base_addr the 16-bit MSB of the CAN0 DMA base address.
 */
void matrix_set_can0_addr(uint32_t base_addr)
{
	Matrix *p_matrix = MATRIX;
	p_matrix->CCFG_CAN0 = CCFG_CAN0_CAN0DMABA(base_addr);
}

/**
 * \brief Set CAN1 DMA base address.
 *
 * \param base_addr the 16-bit MSB of the CAN1 DMA base address.
 */
void matrix_set_can1_addr(uint32_t base_addr)
{
	Matrix *p_matrix = MATRIX;
	volatile uint32_t ul_reg;

	ul_reg = p_matrix->CCFG_SYSIO & (~CCFG_SYSIO_CAN1DMABA_Msk);
	p_matrix->CCFG_SYSIO = ul_reg | CCFG_SYSIO_CAN1DMABA(base_addr);
}
#endif

/* @} */

/* / @cond 0 */
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/* / @endcond */
