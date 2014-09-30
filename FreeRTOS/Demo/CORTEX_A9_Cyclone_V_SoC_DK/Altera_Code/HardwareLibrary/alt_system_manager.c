
/******************************************************************************
*
* alt_system_manager.c - API for the Altera SoC FPGA system manager
*
******************************************************************************/

/******************************************************************************
*
* Copyright 2013 Altera Corporation. All Rights Reserved.
* 
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
* 
* 1. Redistributions of source code must retain the above copyright notice,
* this list of conditions and the following disclaimer.
* 
* 2. Redistributions in binary form must reproduce the above copyright notice,
* this list of conditions and the following disclaimer in the documentation
* and/or other materials provided with the distribution.
* 
* 3. The name of the author may not be used to endorse or promote products
* derived from this software without specific prior written permission.
* 
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR
* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO
* EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
* OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
* INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
* CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
* IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
* OF SUCH DAMAGE.
* 
******************************************************************************/

#include "alt_system_manager.h"
#include "socal/alt_sysmgr.h"
#include "socal/socal.h"
#include "socal/hps.h"

/////


ALT_STATUS_CODE alt_fpga_interface_enable(ALT_FPGA_INTERFACE_t intfc)
{
    switch (intfc)
    {
    case ALT_FPGA_INTERFACE_GLOBAL:
        return alt_setbits_word(ALT_SYSMGR_FPGAINTF_GBL_ADDR,
                                ALT_SYSMGR_FPGAINTF_GBL_INTF_SET_MSK);

    case ALT_FPGA_INTERFACE_RESET_REQ:
        return alt_setbits_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR,
                                ALT_SYSMGR_FPGAINTF_INDIV_RSTREQINTF_SET_MSK);

    case ALT_FPGA_INTERFACE_JTAG_ENABLE:
        return alt_setbits_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR,
                                ALT_SYSMGR_FPGAINTF_INDIV_JTAGENINTF_SET_MSK);

    case ALT_FPGA_INTERFACE_CONFIG_IO:
        return alt_setbits_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR,
                                ALT_SYSMGR_FPGAINTF_INDIV_CFGIOINTF_SET_MSK);

    case ALT_FPGA_INTERFACE_BSCAN:
        return alt_setbits_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR,
                                ALT_SYSMGR_FPGAINTF_INDIV_BSCANINTF_SET_MSK);

    case ALT_FPGA_INTERFACE_TRACE:
        return alt_setbits_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR,
                                ALT_SYSMGR_FPGAINTF_INDIV_TRACEINTF_SET_MSK);

    case ALT_FPGA_INTERFACE_DBG_APB:
        return alt_setbits_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR,
                                1 << 5);

    case ALT_FPGA_INTERFACE_STM:
        return alt_setbits_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR,
                                ALT_SYSMGR_FPGAINTF_INDIV_STMEVENTINTF_SET_MSK);

    case ALT_FPGA_INTERFACE_CTI:
        return alt_setbits_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR,
                                ALT_SYSMGR_FPGAINTF_INDIV_CROSSTRIGINTF_SET_MSK);

    case ALT_FPGA_INTERFACE_EMAC0:
        return alt_setbits_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR,
                                ALT_SYSMGR_FPGAINTF_MODULE_EMAC_0_SET_MSK);

    case ALT_FPGA_INTERFACE_EMAC1:
        return alt_setbits_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR,
                                ALT_SYSMGR_FPGAINTF_MODULE_EMAC_1_SET_MSK);

    case ALT_FPGA_INTERFACE_SPIM0:
        return alt_setbits_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR,
                                1 << 0);

    case ALT_FPGA_INTERFACE_SPIM1:
        return alt_setbits_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR,
                                1 << 1);

    case ALT_FPGA_INTERFACE_NAND:
        return alt_setbits_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR,
                                1 << 4);

    case ALT_FPGA_INTERFACE_SDMMC:
        return alt_setbits_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR,
                                1 << 5);

    default:
        return ALT_E_BAD_ARG;
    }
}

ALT_STATUS_CODE alt_fpga_interface_disable(ALT_FPGA_INTERFACE_t intfc)
{
    switch (intfc)
    {
    case ALT_FPGA_INTERFACE_GLOBAL:
        return alt_clrbits_word(ALT_SYSMGR_FPGAINTF_GBL_ADDR,
                                ALT_SYSMGR_FPGAINTF_GBL_INTF_SET_MSK);

    case ALT_FPGA_INTERFACE_RESET_REQ:
        return alt_clrbits_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR,
                                ALT_SYSMGR_FPGAINTF_INDIV_RSTREQINTF_SET_MSK);

    case ALT_FPGA_INTERFACE_JTAG_ENABLE:
        return alt_clrbits_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR,
                                ALT_SYSMGR_FPGAINTF_INDIV_JTAGENINTF_SET_MSK);

    case ALT_FPGA_INTERFACE_CONFIG_IO:
        return alt_clrbits_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR,
                                ALT_SYSMGR_FPGAINTF_INDIV_CFGIOINTF_SET_MSK);

    case ALT_FPGA_INTERFACE_BSCAN:
        return alt_clrbits_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR,
                                ALT_SYSMGR_FPGAINTF_INDIV_BSCANINTF_SET_MSK);

    case ALT_FPGA_INTERFACE_TRACE:
        return alt_clrbits_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR,
                                ALT_SYSMGR_FPGAINTF_INDIV_TRACEINTF_SET_MSK);

    case ALT_FPGA_INTERFACE_DBG_APB:
        return alt_clrbits_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR,
                                1 << 5);

    case ALT_FPGA_INTERFACE_STM:
        return alt_clrbits_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR,
                                ALT_SYSMGR_FPGAINTF_INDIV_STMEVENTINTF_SET_MSK);

    case ALT_FPGA_INTERFACE_CTI:
        return alt_clrbits_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR,
                                ALT_SYSMGR_FPGAINTF_INDIV_CROSSTRIGINTF_SET_MSK);

    case ALT_FPGA_INTERFACE_EMAC0:
        return alt_clrbits_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR,
                                ALT_SYSMGR_FPGAINTF_MODULE_EMAC_0_SET_MSK);

    case ALT_FPGA_INTERFACE_EMAC1:
        return alt_clrbits_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR,
                                ALT_SYSMGR_FPGAINTF_MODULE_EMAC_1_SET_MSK);

    case ALT_FPGA_INTERFACE_SPIM0:
        return alt_clrbits_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR,
                                1 << 0);

    case ALT_FPGA_INTERFACE_SPIM1:
        return alt_clrbits_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR,
                                1 << 1);

    case ALT_FPGA_INTERFACE_NAND:
        return alt_clrbits_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR,
                                1 << 4);

    case ALT_FPGA_INTERFACE_SDMMC:
        return alt_clrbits_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR,
                                1 << 5);

    default:
        return ALT_E_BAD_ARG;
    }
}

ALT_STATUS_CODE alt_fpga_interface_is_enabled(ALT_FPGA_INTERFACE_t intfc)
{
    switch (intfc)
    {
    case ALT_FPGA_INTERFACE_GLOBAL:
        return ((alt_read_word(ALT_SYSMGR_FPGAINTF_GBL_ADDR) &
                               ALT_SYSMGR_FPGAINTF_GBL_INTF_SET_MSK) != 0)
            ? ALT_E_TRUE : ALT_E_FALSE;

    case ALT_FPGA_INTERFACE_RESET_REQ:
        return ((alt_read_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR) &
                               ALT_SYSMGR_FPGAINTF_INDIV_RSTREQINTF_SET_MSK) != 0)
            ? ALT_E_TRUE : ALT_E_FALSE;

    case ALT_FPGA_INTERFACE_JTAG_ENABLE:
        return ((alt_read_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR) &
                               ALT_SYSMGR_FPGAINTF_INDIV_JTAGENINTF_SET_MSK) != 0)
            ? ALT_E_TRUE : ALT_E_FALSE;

    case ALT_FPGA_INTERFACE_CONFIG_IO:
        return ((alt_read_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR) &
                               ALT_SYSMGR_FPGAINTF_INDIV_CFGIOINTF_SET_MSK) != 0)
            ? ALT_E_TRUE : ALT_E_FALSE;

    case ALT_FPGA_INTERFACE_BSCAN:
        return ((alt_read_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR) &
                               ALT_SYSMGR_FPGAINTF_INDIV_BSCANINTF_SET_MSK) != 0)
            ? ALT_E_TRUE : ALT_E_FALSE;

    case ALT_FPGA_INTERFACE_TRACE:
        return ((alt_read_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR) &
                               ALT_SYSMGR_FPGAINTF_INDIV_TRACEINTF_SET_MSK) != 0)
            ? ALT_E_TRUE : ALT_E_FALSE;

    case ALT_FPGA_INTERFACE_DBG_APB:
        return ((alt_read_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR) &
                               (1 << 5)) != 0) ? ALT_E_TRUE : ALT_E_FALSE;

    case ALT_FPGA_INTERFACE_STM:
        return ((alt_read_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR) &
                               ALT_SYSMGR_FPGAINTF_INDIV_STMEVENTINTF_SET_MSK) != 0)
            ? ALT_E_TRUE : ALT_E_FALSE;

    case ALT_FPGA_INTERFACE_CTI:
        return ((alt_read_word(ALT_SYSMGR_FPGAINTF_INDIV_ADDR) &
                               ALT_SYSMGR_FPGAINTF_INDIV_CROSSTRIGINTF_SET_MSK) != 0)
            ? ALT_E_TRUE : ALT_E_FALSE;

    case ALT_FPGA_INTERFACE_EMAC0:
        return ((alt_read_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR) &
                               ALT_SYSMGR_FPGAINTF_MODULE_EMAC_0_SET_MSK) != 0)
            ? ALT_E_TRUE : ALT_E_FALSE;

    case ALT_FPGA_INTERFACE_EMAC1:
        return ((alt_read_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR) &
                               ALT_SYSMGR_FPGAINTF_MODULE_EMAC_1_SET_MSK) != 0)
            ? ALT_E_TRUE : ALT_E_FALSE;

    case ALT_FPGA_INTERFACE_SPIM0:
        return ((alt_read_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR) &
                               (1 << 0)) != 0)
            ? ALT_E_TRUE : ALT_E_FALSE;

    case ALT_FPGA_INTERFACE_SPIM1:
        return ((alt_read_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR) &
                               (1 << 1)) != 0)
            ? ALT_E_TRUE : ALT_E_FALSE;

    case ALT_FPGA_INTERFACE_NAND:
        return ((alt_read_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR) &
                               (1 << 4)) != 0)
            ? ALT_E_TRUE : ALT_E_FALSE;

    case ALT_FPGA_INTERFACE_SDMMC:
        return ((alt_read_word(ALT_SYSMGR_FPGAINTF_MODULE_ADDR) &
                               (1 << 5)) != 0)
            ? ALT_E_TRUE : ALT_E_FALSE;

    default:
        return ALT_E_BAD_ARG;
    }
}
