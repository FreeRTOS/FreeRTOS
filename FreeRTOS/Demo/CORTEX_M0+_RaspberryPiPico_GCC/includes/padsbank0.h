#ifndef _PADSBANK0_H_
#define _PADSBANK0_H_

#include "address_mapped.h"
#include "platform_defs.h"
#include "regs/pads_bank0.h"

typedef struct {
    io_rw_32 voltage_select;
    io_rw_32 io[30];
} padsbank0_hw_t;

#define padsbank0_hw ((padsbank0_hw_t *)PADS_BANK0_BASE)

#endif