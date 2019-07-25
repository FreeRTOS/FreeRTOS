/******************************************************************************
 *
 * alt_address_space.c - API for the Altera SoC FPGA address space.
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

#include <stddef.h>
#include "alt_address_space.h"
#include "socal/alt_l3.h"
#include "socal/socal.h"
#include "socal/alt_acpidmap.h"
#include "hwlib.h"


#define ALT_ACP_ID_MAX_INPUT_ID     7
#define ALT_ACP_ID_MAX_OUTPUT_ID    4096

/******************************************************************************/
ALT_STATUS_CODE alt_addr_space_remap(ALT_ADDR_SPACE_MPU_ATTR_t mpu_attr,
                                     ALT_ADDR_SPACE_NONMPU_ATTR_t nonmpu_attr,
                                     ALT_ADDR_SPACE_H2F_BRIDGE_ATTR_t h2f_bridge_attr,
                                     ALT_ADDR_SPACE_LWH2F_BRIDGE_ATTR_t lwh2f_bridge_attr)
{
    uint32_t remap_reg_val = 0;

    // Parameter checking and validation...
    if (mpu_attr == ALT_ADDR_SPACE_MPU_ZERO_AT_BOOTROM)
    {
        remap_reg_val |= ALT_L3_REMAP_MPUZERO_SET(ALT_L3_REMAP_MPUZERO_E_BOOTROM);
    }
    else if (mpu_attr == ALT_ADDR_SPACE_MPU_ZERO_AT_OCRAM)
    {
        remap_reg_val |= ALT_L3_REMAP_MPUZERO_SET(ALT_L3_REMAP_MPUZERO_E_OCRAM);
    }
    else
    {
        return ALT_E_INV_OPTION;
    }

    if (nonmpu_attr == ALT_ADDR_SPACE_NONMPU_ZERO_AT_SDRAM)
    {
        remap_reg_val |= ALT_L3_REMAP_NONMPUZERO_SET(ALT_L3_REMAP_NONMPUZERO_E_SDRAM);
    }
    else if (nonmpu_attr == ALT_ADDR_SPACE_NONMPU_ZERO_AT_OCRAM)
    {
        remap_reg_val |= ALT_L3_REMAP_NONMPUZERO_SET(ALT_L3_REMAP_NONMPUZERO_E_OCRAM);
    }
    else
    {
        return ALT_E_INV_OPTION;
    }

    if (h2f_bridge_attr == ALT_ADDR_SPACE_H2F_INACCESSIBLE)
    {
        remap_reg_val |= ALT_L3_REMAP_H2F_SET(ALT_L3_REMAP_H2F_E_INVISIBLE);
    }
    else if (h2f_bridge_attr == ALT_ADDR_SPACE_H2F_ACCESSIBLE)
    {
        remap_reg_val |= ALT_L3_REMAP_H2F_SET(ALT_L3_REMAP_H2F_E_VISIBLE);
    }
    else
    {
        return ALT_E_INV_OPTION;
    }

    if (lwh2f_bridge_attr == ALT_ADDR_SPACE_LWH2F_INACCESSIBLE)
    {
        remap_reg_val |= ALT_L3_REMAP_LWH2F_SET(ALT_L3_REMAP_LWH2F_E_INVISIBLE);
    }
    else if (lwh2f_bridge_attr == ALT_ADDR_SPACE_LWH2F_ACCESSIBLE)
    {
        remap_reg_val |= ALT_L3_REMAP_LWH2F_SET(ALT_L3_REMAP_LWH2F_E_VISIBLE);
    }
    else
    {
        return ALT_E_INV_OPTION;
    }

    // Perform the remap.
    alt_write_word(ALT_L3_REMAP_ADDR, remap_reg_val);

    return ALT_E_SUCCESS;
}

/******************************************************************************/
// Remap the MPU address space view of address 0 to access the SDRAM controller.
// This is done by setting the L2 cache address filtering register start address
// to 0 and leaving the address filtering address end address value
// unmodified. This causes all physical addresses in the range
// address_filter_start <= physical_address < address_filter_end to be directed
// to the to the AXI Master Port M1 which is connected to the SDRAM
// controller. All other addresses are directed to AXI Master Port M0 which
// connect the MPU subsystem to the L3 interconnect.
//
// It is unnecessary to modify the MPU remap options in the L3 remap register
// because those options only affect addresses in the MPU subsystem address
// ranges that are now redirected to the SDRAM controller and never reach the L3
// interconnect anyway.
ALT_STATUS_CODE alt_mpu_addr_space_remap_0_to_sdram(void)
{
    uint32_t addr_filt_end = (alt_read_word(L2_CACHE_ADDR_FILTERING_END_ADDR) &
                              L2_CACHE_ADDR_FILTERING_END_ADDR_MASK);
    return alt_l2_addr_filter_cfg_set(0x0, addr_filt_end);
}

/******************************************************************************/
// Return the L2 cache address filtering registers configuration settings in the
// user provided start and end address range out parameters.
ALT_STATUS_CODE alt_l2_addr_filter_cfg_get(uint32_t* addr_filt_start,
                                           uint32_t* addr_filt_end)
{
    if (addr_filt_start == NULL || addr_filt_end == NULL)
    {
        return ALT_E_BAD_ARG;
    }

    uint32_t addr_filt_start_reg = alt_read_word(L2_CACHE_ADDR_FILTERING_START_ADDR);
    uint32_t addr_filt_end_reg   = alt_read_word(L2_CACHE_ADDR_FILTERING_END_ADDR);

    *addr_filt_start = (addr_filt_start_reg & L2_CACHE_ADDR_FILTERING_START_ADDR_MASK);
    *addr_filt_end = (addr_filt_end_reg & L2_CACHE_ADDR_FILTERING_END_ADDR_MASK);
    return ALT_E_SUCCESS;
}

/******************************************************************************/
ALT_STATUS_CODE alt_l2_addr_filter_cfg_set(uint32_t addr_filt_start,
                                           uint32_t addr_filt_end)
{
    // Address filtering start and end values must be 1 MB aligned.
    if (  (addr_filt_start & ~L2_CACHE_ADDR_FILTERING_START_ADDR_MASK)
       || (addr_filt_end   & ~L2_CACHE_ADDR_FILTERING_END_ADDR_MASK)  )
    {
        return ALT_E_ARG_RANGE;
    }

    // While it is possible to set the address filtering end value above its
    // reset value and thereby access a larger SDRAM address range, it is not
    // recommended. Doing so would potentially obscure any mapped HPS to FPGA
    // bridge address spaces and peripherals on the L3 interconnect.
    if (addr_filt_end > L2_CACHE_ADDR_FILTERING_END_RESET)
    {
        return ALT_E_ARG_RANGE;
    }

    // NOTE: ARM (ARM DDI 0246F CoreLink Level 2 Cache Controller L2C-310 TRM)
    // recommends programming the Address Filtering End Register before the
    // Address Filtering Start Register to avoid unpredictable behavior between
    // the two writes.
    alt_write_word(L2_CACHE_ADDR_FILTERING_END_ADDR, addr_filt_end);
    // It is recommended that address filtering always remain enabled.
    addr_filt_start |= L2_CACHE_ADDR_FILTERING_ENABLE_MASK;
    alt_write_word(L2_CACHE_ADDR_FILTERING_START_ADDR, addr_filt_start);

    return ALT_E_SUCCESS;
}

/******************************************************************************/
ALT_STATUS_CODE alt_acp_id_map_fixed_read_set(const uint32_t input_id,
                                              const uint32_t output_id,
                                              const ALT_ACP_ID_MAP_PAGE_t page,
                                              const uint32_t aruser)
{
    if (input_id > ALT_ACP_ID_OUT_DYNAM_ID_7 || output_id == ALT_ACP_ID_MAX_OUTPUT_ID)
    {
        return ALT_E_BAD_ARG;
    }

    switch (output_id)
    {
    case ALT_ACP_ID_OUT_FIXED_ID_2:
        alt_write_word(ALT_ACPIDMAP_VID2RD_ADDR,
                         ALT_ACPIDMAP_VID2RD_MID_SET(input_id)
                       | ALT_ACPIDMAP_VID2RD_PAGE_SET(page)
                       | ALT_ACPIDMAP_VID2RD_USER_SET(aruser)
                       | ALT_ACPIDMAP_VID2RD_FORCE_SET(1UL));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_3:
        alt_write_word(ALT_ACPIDMAP_VID3RD_ADDR,
                         ALT_ACPIDMAP_VID3RD_MID_SET(input_id)
                       | ALT_ACPIDMAP_VID3RD_PAGE_SET(page)
                       | ALT_ACPIDMAP_VID3RD_USER_SET(aruser)
                       | ALT_ACPIDMAP_VID3RD_FORCE_SET(1UL));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_4:
        alt_write_word(ALT_ACPIDMAP_VID4RD_ADDR,
                         ALT_ACPIDMAP_VID4RD_MID_SET(input_id)
                       | ALT_ACPIDMAP_VID4RD_PAGE_SET(page)
                       | ALT_ACPIDMAP_VID4RD_USER_SET(aruser)
                       | ALT_ACPIDMAP_VID4RD_FORCE_SET(1UL));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_5:
        alt_write_word(ALT_ACPIDMAP_VID5RD_ADDR,
                         ALT_ACPIDMAP_VID5RD_MID_SET(input_id)
                       | ALT_ACPIDMAP_VID5RD_PAGE_SET(page)
                       | ALT_ACPIDMAP_VID5RD_USER_SET(aruser)
                       | ALT_ACPIDMAP_VID5RD_FORCE_SET(1UL));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_6:
        alt_write_word(ALT_ACPIDMAP_VID6RD_ADDR,
                         ALT_ACPIDMAP_VID6RD_MID_SET(input_id)
                       | ALT_ACPIDMAP_VID6RD_PAGE_SET(page)
                       | ALT_ACPIDMAP_VID6RD_USER_SET(aruser)
                       | ALT_ACPIDMAP_VID6RD_FORCE_SET(1UL));
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    return ALT_E_SUCCESS;
}

/******************************************************************************/
ALT_STATUS_CODE alt_acp_id_map_fixed_write_set(const uint32_t input_id,
                                               const uint32_t output_id,
                                               const ALT_ACP_ID_MAP_PAGE_t page,
                                               const uint32_t awuser)
{
    if (input_id > ALT_ACP_ID_OUT_DYNAM_ID_7 || output_id == ALT_ACP_ID_MAX_OUTPUT_ID)
    {
        return ALT_E_BAD_ARG;
    }

    switch (output_id)
    {
    case ALT_ACP_ID_OUT_FIXED_ID_2:
        alt_write_word(ALT_ACPIDMAP_VID2WR_ADDR,
                         ALT_ACPIDMAP_VID2WR_MID_SET(input_id)
                       | ALT_ACPIDMAP_VID2WR_PAGE_SET(page)
                       | ALT_ACPIDMAP_VID2WR_USER_SET(awuser)
                       | ALT_ACPIDMAP_VID2WR_FORCE_SET(1UL));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_3:
        alt_write_word(ALT_ACPIDMAP_VID3WR_ADDR,
                         ALT_ACPIDMAP_VID3WR_MID_SET(input_id)
                       | ALT_ACPIDMAP_VID3WR_PAGE_SET(page)
                       | ALT_ACPIDMAP_VID3WR_USER_SET(awuser)
                       | ALT_ACPIDMAP_VID3WR_FORCE_SET(1UL));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_4:
        alt_write_word(ALT_ACPIDMAP_VID4WR_ADDR,
                         ALT_ACPIDMAP_VID4WR_MID_SET(input_id)
                       | ALT_ACPIDMAP_VID4WR_PAGE_SET(page)
                       | ALT_ACPIDMAP_VID4WR_USER_SET(awuser)
                       | ALT_ACPIDMAP_VID4WR_FORCE_SET(1UL));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_5:
        alt_write_word(ALT_ACPIDMAP_VID5WR_ADDR,
                         ALT_ACPIDMAP_VID5WR_MID_SET(input_id)
                       | ALT_ACPIDMAP_VID5WR_PAGE_SET(page)
                       | ALT_ACPIDMAP_VID5WR_USER_SET(awuser)
                       | ALT_ACPIDMAP_VID5WR_FORCE_SET(1UL));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_6:
        alt_write_word(ALT_ACPIDMAP_VID6WR_ADDR,
                         ALT_ACPIDMAP_VID6WR_MID_SET(input_id)
                       | ALT_ACPIDMAP_VID6WR_PAGE_SET(page)
                       | ALT_ACPIDMAP_VID6WR_USER_SET(awuser)
                       | ALT_ACPIDMAP_VID6WR_FORCE_SET(1UL)
            );
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    return ALT_E_SUCCESS;
}

/******************************************************************************/
ALT_STATUS_CODE alt_acp_id_map_dynamic_read_set(const uint32_t output_id)
{
    if (output_id == ALT_ACP_ID_MAX_OUTPUT_ID)
    {
        return ALT_E_BAD_ARG;
    }

    uint32_t aruser, page;

    switch (output_id)
    {
    case ALT_ACP_ID_OUT_FIXED_ID_2:
        aruser = ALT_ACPIDMAP_VID2RD_USER_GET(alt_read_word(ALT_ACPIDMAP_VID2RD_ADDR));
        page = ALT_ACPIDMAP_VID2RD_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID2RD_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_3:
        aruser = ALT_ACPIDMAP_VID3RD_USER_GET(alt_read_word(ALT_ACPIDMAP_VID3RD_ADDR));
        page = ALT_ACPIDMAP_VID3RD_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID3RD_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_4:
        aruser = ALT_ACPIDMAP_VID4RD_USER_GET(alt_read_word(ALT_ACPIDMAP_VID4RD_ADDR));
        page = ALT_ACPIDMAP_VID4RD_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID4RD_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_5:
        aruser = ALT_ACPIDMAP_VID5RD_USER_GET(alt_read_word(ALT_ACPIDMAP_VID5RD_ADDR));
        page = ALT_ACPIDMAP_VID5RD_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID5RD_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_6:
        aruser = ALT_ACPIDMAP_VID6RD_USER_GET(alt_read_word(ALT_ACPIDMAP_VID6RD_ADDR));
        page = ALT_ACPIDMAP_VID6RD_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID6RD_ADDR));
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    alt_write_word(ALT_ACPIDMAP_DYNRD_ADDR,
                     ALT_ACPIDMAP_DYNRD_PAGE_SET(page)
                   | ALT_ACPIDMAP_DYNRD_USER_SET(aruser));
    return ALT_E_SUCCESS;
}

/******************************************************************************/
ALT_STATUS_CODE alt_acp_id_map_dynamic_write_set(const uint32_t output_id)
{
    if (output_id == ALT_ACP_ID_MAX_OUTPUT_ID)
    {
        return ALT_E_BAD_ARG;
    }

    uint32_t awuser, page;

    switch (output_id)
    {
    case ALT_ACP_ID_OUT_FIXED_ID_2:
        awuser = ALT_ACPIDMAP_VID2WR_USER_GET(alt_read_word(ALT_ACPIDMAP_VID2WR_ADDR));
        page   = ALT_ACPIDMAP_VID2WR_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID2WR_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_3:
        awuser = ALT_ACPIDMAP_VID3WR_USER_GET(alt_read_word(ALT_ACPIDMAP_VID3WR_ADDR));
        page   = ALT_ACPIDMAP_VID3WR_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID3WR_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_4:
        awuser = ALT_ACPIDMAP_VID4WR_USER_GET(alt_read_word(ALT_ACPIDMAP_VID4WR_ADDR));
        page   = ALT_ACPIDMAP_VID4WR_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID4WR_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_5:
        awuser = ALT_ACPIDMAP_VID5WR_USER_GET(alt_read_word(ALT_ACPIDMAP_VID5WR_ADDR));
        page   = ALT_ACPIDMAP_VID5WR_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID5WR_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_6:
        awuser = ALT_ACPIDMAP_VID6WR_USER_GET(alt_read_word(ALT_ACPIDMAP_VID6WR_ADDR));
        page   = ALT_ACPIDMAP_VID6WR_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID6WR_ADDR));
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    alt_write_word(ALT_ACPIDMAP_DYNWR_ADDR,
                     ALT_ACPIDMAP_DYNWR_PAGE_SET(page)
                   | ALT_ACPIDMAP_DYNWR_USER_SET(awuser));
    return ALT_E_SUCCESS;
}

/******************************************************************************/
ALT_STATUS_CODE alt_acp_id_map_dynamic_read_options_set(const ALT_ACP_ID_MAP_PAGE_t page,
                                                        const uint32_t aruser)
{
    alt_write_word(ALT_ACPIDMAP_DYNRD_ADDR,
                     ALT_ACPIDMAP_DYNRD_PAGE_SET(page)
                   | ALT_ACPIDMAP_DYNRD_USER_SET(aruser));
    return ALT_E_SUCCESS;
}

/******************************************************************************/
ALT_STATUS_CODE alt_acp_id_map_dynamic_write_options_set(const ALT_ACP_ID_MAP_PAGE_t page,
                                                         const uint32_t awuser)
{
    alt_write_word(ALT_ACPIDMAP_DYNWR_ADDR,
                     ALT_ACPIDMAP_DYNWR_PAGE_SET(page)
                   | ALT_ACPIDMAP_DYNWR_USER_SET(awuser));
    return ALT_E_SUCCESS;
}

/******************************************************************************/
ALT_STATUS_CODE alt_acp_id_map_read_options_get(const uint32_t output_id,
                                                bool * fixed,
                                                uint32_t * input_id,
                                                ALT_ACP_ID_MAP_PAGE_t * page,
                                                uint32_t * aruser)
{
    if (output_id == ALT_ACP_ID_MAX_OUTPUT_ID)
    {
        return ALT_E_BAD_ARG;
    }

    switch (output_id)
    {
    case ALT_ACP_ID_OUT_FIXED_ID_2:
        *aruser   = ALT_ACPIDMAP_VID2RD_S_USER_GET(alt_read_word(ALT_ACPIDMAP_VID2RD_S_ADDR));
        *page     = (ALT_ACP_ID_MAP_PAGE_t)ALT_ACPIDMAP_VID2RD_S_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID2RD_S_ADDR));
        *input_id = ALT_ACPIDMAP_VID2RD_S_MID_GET(alt_read_word(ALT_ACPIDMAP_VID2RD_S_ADDR));
        *fixed    = ALT_ACPIDMAP_VID2RD_S_FORCE_GET(alt_read_word(ALT_ACPIDMAP_VID2RD_S_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_3:
        *aruser   = ALT_ACPIDMAP_VID3RD_S_USER_GET(alt_read_word(ALT_ACPIDMAP_VID3RD_S_ADDR));
        *page     = (ALT_ACP_ID_MAP_PAGE_t)ALT_ACPIDMAP_VID3RD_S_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID3RD_S_ADDR));
        *input_id = ALT_ACPIDMAP_VID3RD_S_MID_GET(alt_read_word(ALT_ACPIDMAP_VID3RD_S_ADDR));
        *fixed    = ALT_ACPIDMAP_VID3RD_S_FORCE_GET(alt_read_word(ALT_ACPIDMAP_VID3RD_S_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_4:
        *aruser   = ALT_ACPIDMAP_VID4RD_S_USER_GET(alt_read_word(ALT_ACPIDMAP_VID4RD_S_ADDR));
        *page     = (ALT_ACP_ID_MAP_PAGE_t)ALT_ACPIDMAP_VID4RD_S_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID4RD_S_ADDR));
        *input_id = ALT_ACPIDMAP_VID4RD_S_MID_GET(alt_read_word(ALT_ACPIDMAP_VID4RD_S_ADDR));
        *fixed    = ALT_ACPIDMAP_VID4RD_S_FORCE_GET(alt_read_word(ALT_ACPIDMAP_VID4RD_S_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_5:
        *aruser   = ALT_ACPIDMAP_VID5RD_S_USER_GET(alt_read_word(ALT_ACPIDMAP_VID5RD_S_ADDR));
        *page     = (ALT_ACP_ID_MAP_PAGE_t)ALT_ACPIDMAP_VID5RD_S_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID5RD_S_ADDR));
        *input_id = ALT_ACPIDMAP_VID5RD_S_MID_GET(alt_read_word(ALT_ACPIDMAP_VID5RD_S_ADDR));
        *fixed    = ALT_ACPIDMAP_VID5RD_S_FORCE_GET(alt_read_word(ALT_ACPIDMAP_VID5RD_S_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_6:
        *aruser   = ALT_ACPIDMAP_VID6RD_S_USER_GET(alt_read_word(ALT_ACPIDMAP_VID6RD_S_ADDR));
        *page     = (ALT_ACP_ID_MAP_PAGE_t)ALT_ACPIDMAP_VID6RD_S_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID6RD_S_ADDR));
        *input_id = ALT_ACPIDMAP_VID6RD_S_MID_GET(alt_read_word(ALT_ACPIDMAP_VID6RD_S_ADDR));
        *fixed    = ALT_ACPIDMAP_VID6RD_S_FORCE_GET(alt_read_word(ALT_ACPIDMAP_VID6RD_S_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_7:
        *aruser   = ALT_ACPIDMAP_DYNRD_S_USER_GET(alt_read_word(ALT_ACPIDMAP_DYNRD_S_ADDR));
        *page     = (ALT_ACP_ID_MAP_PAGE_t)ALT_ACPIDMAP_DYNRD_S_PAGE_GET(alt_read_word(ALT_ACPIDMAP_DYNRD_S_ADDR));
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_acp_id_map_write_options_get(const uint32_t output_id,
                                                 bool * fixed,
                                                 uint32_t * input_id,
                                                 ALT_ACP_ID_MAP_PAGE_t * page,
                                                 uint32_t * awuser)
{
    if (output_id == ALT_ACP_ID_MAX_OUTPUT_ID)
    {
        return ALT_E_BAD_ARG;
    }

    switch (output_id)
    {
    case ALT_ACP_ID_OUT_FIXED_ID_2:
        *awuser   = ALT_ACPIDMAP_VID2WR_S_USER_GET(alt_read_word(ALT_ACPIDMAP_VID2WR_S_ADDR));
        *page     = (ALT_ACP_ID_MAP_PAGE_t)ALT_ACPIDMAP_VID2WR_S_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID2WR_S_ADDR));
        *input_id = ALT_ACPIDMAP_VID2WR_S_MID_GET(alt_read_word(ALT_ACPIDMAP_VID2WR_S_ADDR));
        *fixed    = ALT_ACPIDMAP_VID2WR_S_FORCE_GET(alt_read_word(ALT_ACPIDMAP_VID2WR_S_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_3:
        *awuser   = ALT_ACPIDMAP_VID3WR_S_USER_GET(alt_read_word(ALT_ACPIDMAP_VID3WR_S_ADDR));
        *page     = (ALT_ACP_ID_MAP_PAGE_t)ALT_ACPIDMAP_VID3WR_S_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID3WR_S_ADDR));
        *input_id = ALT_ACPIDMAP_VID3WR_S_MID_GET(alt_read_word(ALT_ACPIDMAP_VID3WR_S_ADDR));
        *fixed    = ALT_ACPIDMAP_VID3WR_S_FORCE_GET(alt_read_word(ALT_ACPIDMAP_VID3WR_S_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_4:
        *awuser   = ALT_ACPIDMAP_VID4WR_S_USER_GET(alt_read_word(ALT_ACPIDMAP_VID4WR_S_ADDR));
        *page     = (ALT_ACP_ID_MAP_PAGE_t)ALT_ACPIDMAP_VID4WR_S_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID4WR_S_ADDR));
        *input_id = ALT_ACPIDMAP_VID4WR_S_MID_GET(alt_read_word(ALT_ACPIDMAP_VID4WR_S_ADDR));
        *fixed    = ALT_ACPIDMAP_VID4WR_S_FORCE_GET(alt_read_word(ALT_ACPIDMAP_VID4WR_S_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_5:
        *awuser   = ALT_ACPIDMAP_VID5WR_S_USER_GET(alt_read_word(ALT_ACPIDMAP_VID5WR_S_ADDR));
        *page     = (ALT_ACP_ID_MAP_PAGE_t)ALT_ACPIDMAP_VID5WR_S_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID5WR_S_ADDR));
        *input_id = ALT_ACPIDMAP_VID5WR_S_MID_GET(alt_read_word(ALT_ACPIDMAP_VID5WR_S_ADDR));
        *fixed    = ALT_ACPIDMAP_VID5WR_S_FORCE_GET(alt_read_word(ALT_ACPIDMAP_VID5WR_S_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_6:
        *awuser   = ALT_ACPIDMAP_VID6WR_S_USER_GET(alt_read_word(ALT_ACPIDMAP_VID6WR_S_ADDR));
        *page     = (ALT_ACP_ID_MAP_PAGE_t)ALT_ACPIDMAP_VID6WR_S_PAGE_GET(alt_read_word(ALT_ACPIDMAP_VID6WR_S_ADDR));
        *input_id = ALT_ACPIDMAP_VID6WR_S_MID_GET(alt_read_word(ALT_ACPIDMAP_VID6WR_S_ADDR));
        *fixed    = ALT_ACPIDMAP_VID6WR_S_FORCE_GET(alt_read_word(ALT_ACPIDMAP_VID6WR_S_ADDR));
        break;
    case ALT_ACP_ID_OUT_DYNAM_ID_7:
        *awuser   = ALT_ACPIDMAP_DYNWR_S_USER_GET(alt_read_word(ALT_ACPIDMAP_DYNWR_S_ADDR));
        *page     = (ALT_ACP_ID_MAP_PAGE_t)ALT_ACPIDMAP_DYNWR_S_PAGE_GET(alt_read_word(ALT_ACPIDMAP_DYNWR_S_ADDR));
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    return ALT_E_SUCCESS;
}
