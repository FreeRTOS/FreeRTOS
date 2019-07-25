/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/** \file */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include "peripherals/l2cc.h"
#include "cortex-a/cp15.h"
#include "trace.h"

#include <assert.h>
#include <stdbool.h>
#include <string.h>

/*----------------------------------------------------------------------------
 *        Functions
 *----------------------------------------------------------------------------*/

uint32_t l2cc_is_enabled(void)
{
	return ((L2CC->L2CC_CR) & L2CC_CR_L2CEN);
}

void l2cc_enable(void)
{
	L2CC->L2CC_CR |= L2CC_CR_L2CEN;
	asm volatile("": : :"memory");
	asm("dsb");
	asm("isb");
	trace_info("L2 cache is enabled\r\n");
}

void l2cc_disable(void)
{
	L2CC->L2CC_CR &= ~L2CC_CR_L2CEN;
	asm volatile("": : :"memory");
	asm("dsb");
	asm("isb");
	trace_info("L2 cache is disabled\r\n");
}

void l2cc_exclusive_cache(uint8_t enable)
{
	uint32_t cfg;
	if (l2cc_is_enabled()) {
		l2cc_disable();
	}
	cfg = L2CC->L2CC_ACR;
	if (enable) {
		cp15_exclusive_cache();
		cfg |= L2CC_ACR_EXCC;
		trace_info("L2 Exclusive mode enabled\n\r");
	} else {
		cp15_non_exclusive_cache();
		cfg &= ~L2CC_ACR_EXCC;
		trace_info("L2 Exclusive mode disabled\n\r");
	}
	L2CC->L2CC_ACR |= cfg;
}

void l2cc_config_lat_ram(struct _ram_latency_control * latencies)
{
	if (l2cc_is_enabled()) {
		l2cc_disable();
	}

	L2CC->L2CC_TRCR =
		(L2CC_TRCR_TSETLAT(latencies->tag.setup) |
		 L2CC_TRCR_TRDLAT(latencies->tag.read) |
		 L2CC_TRCR_TWRLAT(latencies->tag.write));
	L2CC->L2CC_DRCR =
		(L2CC_DRCR_DSETLAT(latencies->data.setup) |
		 L2CC_DRCR_DRDLAT(latencies->data.read) |
		 L2CC_DRCR_DWRLAT(latencies->data.write));
}

void l2cc_set_config(const struct _l2cc_control* cfg)
{
	uint32_t aux_control, debug_control, prefetch_control, power_control;

	if (cfg->offset > 31) {
		assert(0);
	}
	if ((cfg->offset > 7) && (cfg->offset < 15)) {
		assert(0);
	}
	if ((cfg->offset > 15) && (cfg->offset < 23)) {
		assert(0);
	}
	if ((cfg->offset > 23) && (cfg->offset < 31)) {
		assert(0);
	}

	if (l2cc_is_enabled()) {
		l2cc_disable();
	}

	aux_control = ((cfg->high_prior_so << 10) |
		       (cfg->store_buff_dev_limit << 11) |
		       (cfg->shared_attr_invalidate << 13) |
		       (cfg->evt_mon_bus << 20) |
		       (cfg->parity << 21) |
		       (cfg->shared_attr_override << 22) |
		       (L2CC_ACR_FWA(cfg->force_write_alloc)) |
		       (cfg->cache_replacement << 25) |
		       (cfg->non_sec_lockdown << 26) |
		       (cfg->it_acces_non_sec << 27) |
		       (cfg->data_prefetch << 28) |
		       (cfg->instruct_prefetch << 29));

	debug_control = ((cfg->no_cache_linefill << 0) |
			 (cfg->no_write_back << 1));

	prefetch_control = ((L2CC_PCR_OFFSET(cfg->offset << 0)) |
			    (cfg->exclusive_seq_same_id << 21) |
			    (cfg->incr_double_linefill << 23) |
			    (cfg->prefetch_drop << 24) |
			    (cfg->DLFWRDIS << 27) |
			    (cfg->data_prefetch << 28) |
			    (cfg->instruct_prefetch << 29) |
			    (cfg->double_linefill << 30));

	power_control = ((cfg->standby_mode << 0) |
			 (cfg->dyn_clock_gating << 1));

	L2CC->L2CC_ACR = aux_control;
	L2CC->L2CC_DCR = debug_control;
	L2CC->L2CC_PCR = prefetch_control;
	L2CC->L2CC_POWCR = power_control;
}

void l2cc_data_prefetch_enable(void)
{
	L2CC->L2CC_PCR |= L2CC_PCR_DATPEN;
}

void l2cc_inst_prefetch_enable(void)
{
	L2CC->L2CC_PCR |= L2CC_PCR_INSPEN;
}

void l2cc_enable_reset_counter(uint8_t event_counter)
{
	assert((event_counter > 3) ? 0 : 1);
	L2CC->L2CC_ECR = (L2CC_ECR_EVCEN | (event_counter << 1));
}

void l2cc_event_config(uint8_t event_counter, uint8_t source, uint8_t it)
{
	if (l2cc_is_enabled()) {
		L2CC->L2CC_CR = false;
	}
	assert((event_counter > 1) ? 0 : 1);
	if (!event_counter) {
		L2CC->L2CC_ECFGR0 = (source | it);
	} else {
		L2CC->L2CC_ECFGR1 = (source | it);
	}

}

uint32_t l2cc_event_counter_value(uint8_t event_counter)
{
	assert((event_counter > 1) ? 0 : 1);
	if (!event_counter) {
		return L2CC->L2CC_EVR0;
	} else {
		return L2CC->L2CC_EVR1;
	}
}

void l2cc_enable_it(uint16_t sources)
{
	L2CC->L2CC_IMR |= sources;
}

void l2cc_disable_it(uint16_t sources)
{
	L2CC->L2CC_IMR &= (!sources);
}

unsigned short l2cc_it_status_raw(uint16_t sources)
{
	return ((L2CC->L2CC_RISR) & sources) ? 1 : 0;
}

uint16_t l2cc_it_status_mask(uint16_t sources)
{
	return ((L2CC->L2CC_MISR) & sources) ? 1 : 0;
}

void l2cc_it_clear(uint16_t sources)
{
	L2CC->L2CC_ICR |= sources;
}

uint8_t l2cc_poll_spniden()
{
	return ((L2CC->L2CC_DCR & L2CC_DCR_SPNIDEN) >> 2);
}

void l2cc_cache_sync()
{
	while ((L2CC->L2CC_CSR) & L2CC_CSR_C) ;
	L2CC->L2CC_CSR = L2CC_CSR_C;
	while ((L2CC->L2CC_CSR) & L2CC_CSR_C) ;
}

void l2cc_invalidate_pal(uint32_t phys_addr)
{
	static uint32_t Tag;
	static uint16_t Index;
	Tag = (phys_addr >> (OFFSET_BIT + INDEX_BIT));
	Index = (phys_addr >> OFFSET_BIT) & ((1 << INDEX_BIT) - 1);
	L2CC->L2CC_IPALR = (L2CC_IPALR_TAG(Tag) | L2CC_IPALR_IDX(Index) | L2CC_IPALR_C);
	while ((L2CC->L2CC_IPALR) & L2CC_IPALR_C) ;
}

void l2cc_clean_pal(uint32_t phys_addr)
{
	static uint32_t Tag;
	static uint16_t Index;

	Tag = (phys_addr >> (OFFSET_BIT + INDEX_BIT));
	Index = (phys_addr >> OFFSET_BIT) & ((1 << INDEX_BIT) - 1);
	L2CC->L2CC_CPALR =
	    (L2CC_CPALR_TAG(Tag) | L2CC_CPALR_IDX(Index) | L2CC_CPALR_C);
	while ((L2CC->L2CC_CPALR) & L2CC_CPALR_C) ;
}

void l2cc_clean_ix(uint32_t phys_addr)
{
	static uint32_t Tag;
	static uint16_t Index;

	Tag = (phys_addr >> (OFFSET_BIT + INDEX_BIT));
	Index = (phys_addr >> OFFSET_BIT) & ((1 << INDEX_BIT) - 1);
	L2CC->L2CC_CIPALR =
	    (L2CC_CIPALR_TAG(Tag) | L2CC_CIPALR_IDX(Index) | L2CC_CIPALR_C);
	while ((L2CC->L2CC_CIPALR) & L2CC_CIPALR_C) ;
}

void l2cc_invalidate_way(uint8_t way)
{
	L2CC->L2CC_IWR = way;
	while (L2CC->L2CC_IWR) ;
	while (L2CC->L2CC_CSR) ;
}

void l2cc_clean_way(uint8_t way)
{
	L2CC->L2CC_CWR = way;
	while (L2CC->L2CC_CWR) ;
	while (L2CC->L2CC_CSR) ;
}

/**
 * \brief Clean Invalidate cache by way
 * \param way  way number
 */
static void l2cc_clean_invalidate_way(uint8_t way)
{
	L2CC->L2CC_CIWR = way;
	while (L2CC->L2CC_CSR) ;
}

void l2cc_clean_index(uint32_t phys_addr, uint8_t way)
{
	static uint16_t Index;

	Index = (phys_addr >> OFFSET_BIT) & ((1 << INDEX_BIT) - 1);
	L2CC->L2CC_CIR =
	    (L2CC_CIR_IDX(Index) | L2CC_CIR_WAY(way) | L2CC_CIR_C);
	while ((L2CC->L2CC_CIR) & L2CC_CIR_C) ;
}

void l2cc_clean_invalidate_index(uint32_t phys_addr, uint8_t way)
{
	static uint16_t Index;

	(void) way;
	Index = (phys_addr >> OFFSET_BIT) & ((1 << INDEX_BIT) - 1);
	L2CC->L2CC_CIIR =
	    (L2CC_CIIR_IDX(Index) | L2CC_CIIR_WAY(Index) | L2CC_CIIR_C);
	while ((L2CC->L2CC_CIIR) & L2CC_CIIR_C) ;
}

void l2cc_data_lockdown(uint8_t way)
{
	L2CC->L2CC_DLKR = way;
	while (L2CC->L2CC_CSR) ;
}

void l2cc_instruction_lockdown(uint8_t way)
{
	L2CC->L2CC_ILKR = way;
	while (L2CC->L2CC_CSR) ;
}

static void l2cc_clean(void)
{
	// Clean of L1; This is broadcast within the cluster
	cp15_dcache_clean();
	if (l2cc_is_enabled()) {
		// forces the address out past level 2
		l2cc_clean_way(0xFF);
		// Ensures completion of the L2 clean
		l2cc_cache_sync();
	}
}

static void l2cc_invalidate(void)
{
	if (l2cc_is_enabled()) {
		// forces the address out past level 2
		l2cc_invalidate_way(0xFF);
		// Ensures completion of the L2 inval
		l2cc_cache_sync();
	}
	// Inval of L1; This is broadcast within the cluster
	cp15_dcache_invalidate();
}

static void l2cc_clean_invalidate(void)
{
	/* Clean of L1; This is broadcast within the cluster */
	cp15_dcache_clean();

	if (l2cc_is_enabled()) {
		/* forces the address out past level 2 */
		l2cc_clean_invalidate_way(0xFF);
		/* Ensures completion of the L2 inval */
		l2cc_cache_sync();
	}

	/* Inval of L1; This is broadcast within the cluster */
	cp15_dcache_invalidate();
}

void l2cc_cache_maintenance(enum _maint_op maintenance)
{
	switch (maintenance) {
		case L2CC_DCACHE_CLEAN:
			l2cc_clean();
			break;
		case L2CC_DCACHE_INVAL:
			l2cc_invalidate();
			break;
		case L2CC_DCACHE_FLUSH:
			l2cc_clean_invalidate();
			break;
	}
}

void l2cc_invalidate_region(uint32_t start, uint32_t end)
{
	assert(start < end);
	uint32_t current = start & ~0x1fUL;
	if (l2cc_is_enabled()) {
		while (current <= end) {
			l2cc_invalidate_pal(current);
			current += 32;
		}
		l2cc_invalidate_pal(end);
	}
	cp15_invalidate_dcache_for_dma(start, end);
}

void l2cc_clean_region(uint32_t start, uint32_t end)
{
	assert(start < end);
	uint32_t current = start & ~0x1fUL;
	if (l2cc_is_enabled()) {
		while (current <= end) {
			l2cc_clean_pal(current);
			current += 32;
		}
		l2cc_clean_pal(end);
	}
	cp15_clean_dcache_for_dma(start, end);
}

void l2cc_configure(const struct _l2cc_control* cfg)
{
	l2cc_event_config(0, L2CC_ECFGR0_ESRC_SRC_DRHIT,
			  L2CC_ECFGR0_EIGEN_INT_DIS);
	l2cc_event_config(1, L2CC_ECFGR0_ESRC_SRC_DWHIT,
			  L2CC_ECFGR0_EIGEN_INT_DIS);

	l2cc_enable_reset_counter(L2CC_RESET_BOTH_COUNTER);
	l2cc_set_config(cfg);
	/* Enable Prefetch */
	l2cc_inst_prefetch_enable();
	l2cc_data_prefetch_enable();
	/* Invalidate whole L2CC */
	l2cc_invalidate_way(0xFF);
	/* Disable all L2CC Interrupt */
	l2cc_disable_it(0x1FF);
	/* Clear all L2CC Interrupt */
	l2cc_it_clear(0xFF);
	l2cc_exclusive_cache(true);
	l2cc_enable();
}
