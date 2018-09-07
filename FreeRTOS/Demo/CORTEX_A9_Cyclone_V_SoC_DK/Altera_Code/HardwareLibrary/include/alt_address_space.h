/*! \file
 *  Altera - SoC FPGA Address Space Manager
 */

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

#ifndef __ALT_ADDRESS_SPACE_H__
#define __ALT_ADDRESS_SPACE_H__

#include <stdbool.h>
#include "hwlib.h"
#include "socal/hps.h"

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/******************************************************************************/
// ARM Level 2 Cache Controller L2C-310 Register Interface

// Address Filtering Start Register
// The Address Filtering Start Register is a read and write register.
// Bits     Field                       Description
// :-------|:--------------------------|:-----------------------------------------
// [31:20] | address_filtering_start   | Address filtering start address for
//         |                           | bits [31:20] of the filtering address.
// [19:1]  | Reserved                  | SBZ/RAZ
// [0]     | address_filtering_enable  | 0 - address filtering disabled
//         |                           | 1 - address filtering enabled.

// Address Filtering Start Register Address
#define L2_CACHE_ADDR_FILTERING_START_OFST      0xC00
#define L2_CACHE_ADDR_FILTERING_START_ADDR      (ALT_MPUL2_OFST + L2_CACHE_ADDR_FILTERING_START_OFST)
// Address Filtering Start Register - Start Value Mask
#define L2_CACHE_ADDR_FILTERING_START_ADDR_MASK 0xFFF00000
// Address Filtering Start Register - Reset Start Address Value (1 MB)
#define L2_CACHE_ADDR_FILTERING_START_RESET     0x100000
// Address Filtering Start Register - Enable Flag Mask
#define L2_CACHE_ADDR_FILTERING_ENABLE_MASK     0x00000001
// Address Filtering Start Register - Reset Enable Flag Value (Enabled)
#define L2_CACHE_ADDR_FILTERING_ENABLE_RESET    0x1

// Address Filtering End Register
// The Address Filtering End Register is a read and write register.
// Bits     Field                       Description
// :-------|:--------------------------|:-----------------------------------------
// [31:20] | address_filtering_end     | Address filtering end address for bits
//         |                           | [31:20] of the filtering address.
// [19:0]  | Reserved                  | SBZ/RAZ

// Address Filtering End Register Address
#define L2_CACHE_ADDR_FILTERING_END_OFST        0xC04
#define L2_CACHE_ADDR_FILTERING_END_ADDR        (ALT_MPUL2_OFST + L2_CACHE_ADDR_FILTERING_END_OFST)
// Address Filtering End Register - End Value Mask
#define L2_CACHE_ADDR_FILTERING_END_ADDR_MASK   0xFFF00000
// Address Filtering End Register - Reset End Address Value (3 GiB)
#define L2_CACHE_ADDR_FILTERING_END_RESET       0xC0000000

#ifndef __ASSEMBLY__

/******************************************************************************/
/*! \addtogroup ADDR_SPACE_MGR The Address Space Manager
 *
 * This module contains group APIs for managing the HPS address space. This
 * module contains group APIs to manage:
 * * Memory Map Control
 * * Memory Coherence
 * * Cache Managment
 * * MMU Managment
 *
 * @{
 */

/******************************************************************************/
/*! \addtogroup ADDR_SPACE_MGR_REMAP Address Space Mapping Control
 *
 * This group API provides functions to map and remap selected address ranges
 * into the accessible (visible) views of the MPU and non MPU address spaces.
 *
 * \b Caveats
 *
 * \b NOTE: Caution should be observed when remapping address 0 to different
 * memory.  The code performing the remapping operation should not be executing
 * in the address range being remapped to different memory.
 *
 * For example, if address 0 is presently mapped to OCRAM and the code is
 * preparing to remap address 0 to SDRAM, then the code must not be executing in
 * the range 0 to 64 KB as this address space is about to be remapped to
 * different memory. If the code performing the remap operation is executing
 * from OCRAM then it needs to be executing from its permanently mapped OCRAM
 * address range in upper memory (i.e. ALT_OCRAM_LB_ADDR to ALT_OCRAM_UB_ADDR).
 *
 * \b NOTE: The MPU address space view is controlled by two disparate hardware
 * control interfaces: the L3 remap register and the L2 cache address filtering
 * registers. To complicate matters, the L3 remap register is write-only which
 * means not only that current remap register state cannot be read but also that
 * a read-modify-write operation cannot be performed on the register.
 *
 * This should not present a problem in most use case scenarios except for the
 * case where a current MPU address space mapping of 0 to SDRAM is being changed
 * to to a mapping of 0 to Boot ROM or OCRAM.
 *
 * In this case, a two step process whereby the L3 remap register is first set
 * to the new desired MPU address 0 mapping and then the L2 cache address
 * filtering registers have their address ranges adjusted accordingly must be
 * followed. An example follows:
\verbatim
// 1 MB reset default value for address filtering start
#define L2_CACHE_ADDR_FILTERING_START_RESET     0x100000
uint32_t addr_filt_start;
uint32_t addr_filt_end;

// Perform L3 remap register programming first by setting the desired new MPU
// address space 0 mapping. Assume OCRAM for the example.
alt_addr_space_remap(ALT_ADDR_SPACE_MPU_ZERO_AT_OCRAM, ...);

// Next, adjust the L2 cache address filtering range. Set the start address to
// the default reset value and retain the existing end address configuration.
alt_l2_addr_filter_cfg_get(&addr_filt_start, &addr_filt_end);
if (addr_filt_start != L2_CACHE_ADDR_FILTERING_START_RESET)
{
    alt_l2_addr_filter_cfg_set(L2_CACHE_ADDR_FILTERING_START_RESET, addr_filt_end);
}
\endverbatim
 * @{
 */

/******************************************************************************/
/*!
 * This type definition enumerates the MPU address space attributes.
 *
 * The MPU address space consists of the ARM Cortex A9 processors and associated
 * processor peripherals (cache, MMU).
 */
typedef enum ALT_ADDR_SPACE_MPU_ATTR_e
{
    ALT_ADDR_SPACE_MPU_ZERO_AT_BOOTROM,     /*!< Maps the Boot ROM to address
                                             *   0x0 for the MPU L3 master. Note
                                             *   that the Boot ROM is also
                                             *   always mapped to address
                                             *   0xfffd_0000 for the MPU L3
                                             *   master independent of
                                             *   attribute.
                                             */

    ALT_ADDR_SPACE_MPU_ZERO_AT_OCRAM        /*!< Maps the On-chip RAM to address
                                             *   0x0 for the MPU L3 master. Note
                                             *   that the On-chip RAM is also
                                             *   always mapped to address
                                             *   0xffff_0000 for the MPU L3
                                             *   master independent of this
                                             *   attribute.
                                             */
} ALT_ADDR_SPACE_MPU_ATTR_t;

/******************************************************************************/
/*!
 * This type definition enumerates the non-MPU address space attributes.
 *
 * The non-MPU address space consists of the non-MPU L3 masters including the
 * DMA controllers (standalone and those built into peripherals), the F2H AXI
 * Bridge, and the DAP.
 */
typedef enum ALT_ADDR_SPACE_NONMPU_ATTR_e
{
    ALT_ADDR_SPACE_NONMPU_ZERO_AT_SDRAM,    /*!< Maps the SDRAM to address 0x0
                                             *   for the non-MPU L3 masters.
                                             */
    ALT_ADDR_SPACE_NONMPU_ZERO_AT_OCRAM     /*!< Maps the On-chip RAM to address
                                             *   0x0 for the non-MPU L3
                                             *   masters. Note that the On-chip
                                             *   RAM is also always mapped to
                                             *   address 0xffff_0000 for the
                                             *   non-MPU L3 masters independent
                                             *   of this attribute.
                                             */
} ALT_ADDR_SPACE_NONMPU_ATTR_t;

/******************************************************************************/
/*!
 * This type definition enumerates the HPS to FPGA bridge accessiblity
 * attributes.
 */
typedef enum ALT_ADDR_SPACE_H2F_BRIDGE_ATTR_e
{
    ALT_ADDR_SPACE_H2F_INACCESSIBLE,        /*!< The H2F AXI Bridge is not
                                             *   visible to L3 masters. Accesses
                                             *   to the associated address range
                                             *   return an AXI decode error to
                                             *   the master.
                                             */
    ALT_ADDR_SPACE_H2F_ACCESSIBLE           /*!< The H2F AXI Bridge is visible
                                             *   to L3 masters.
                                             */
} ALT_ADDR_SPACE_H2F_BRIDGE_ATTR_t;

/******************************************************************************/
/*!
 * This type definition enumerates the Lightweight HPS to FPGA bridge
 * accessiblity attributes.
 */
typedef enum ALT_ADDR_SPACE_LWH2F_BRIDGE_ATTR_e
{
    ALT_ADDR_SPACE_LWH2F_INACCESSIBLE,      /*!< The LWH2F AXI Bridge is not
                                             *   visible to L3 masters. Accesses
                                             *   to the associated address range
                                             *   return an AXI decode error to
                                             *   the master.
                                             */
    ALT_ADDR_SPACE_LWH2F_ACCESSIBLE         /*!< The LWH2F AXI Bridge is visible
                                             *   to L3 masters.
                                             */
} ALT_ADDR_SPACE_LWH2F_BRIDGE_ATTR_t;

/******************************************************************************/
/*!
 * Configures the mapped and accessible (visible) address ranges for the HPS
 * MPU, non-MPU, and Bridge address spaces.
 *
 * \param       mpu_attr
 *              The MPU address space configuration attributes.
 *              
 * \param       nonmpu_attr
 *              The non-MPU address space configuration attributes.
 *              
 * \param       h2f_attr
 *              The H2F Bridge attribute mapping and accessibility attributes.
 *              
 * \param       lwh2f_attr
 *              The Lightweight H2F Bridge attribute mapping and accessibility
 *              attributes.
 *              
 * 
 * \retval      ALT_E_SUCCESS       The operation was succesful.
 * \retval      ALT_E_ERROR         The operation failed.
 * \retval      ALT_E_INV_OPTION    One or more invalid attribute options were
 *                                  specified.
 */
ALT_STATUS_CODE alt_addr_space_remap(ALT_ADDR_SPACE_MPU_ATTR_t mpu_attr,
                                     ALT_ADDR_SPACE_NONMPU_ATTR_t nonmpu_attr,
                                     ALT_ADDR_SPACE_H2F_BRIDGE_ATTR_t h2f_attr,
                                     ALT_ADDR_SPACE_LWH2F_BRIDGE_ATTR_t lwh2f_attr);

/******************************************************************************/
/*!
 * Maps SDRAM to address 0x0 for the MPU address space view.
 *
 * When address 0x0 is mapped to the Boot ROM or on-chip RAM, only the lowest
 * 64KB of the boot region are accessible because the size of the Boot ROM and
 * on-chip RAM are only 64KB.  Addresses in the range 0x100000 (1MiB) to
 * 0xC0000000 (3GiB) access SDRAM and addresses in the range 0xC0000000 (3GiB) to
 * 0xFFFFFFFF access the L3 interconnect. Thus, the lowest 1MiB of SDRAM is not
 * accessible to the MPU unless address 0 is remapped to SDRAM after reset.
 *
 * This function remaps the addresses between 0x0 to 0x100000 (1MiB) to access
 * SDRAM.
 *
 * \internal
 * The remap to address 0x0 is achieved by configuring the L2 cache Address
 * Filtering Registers to redirect address 0x0 to \e sdram_end_addr to the SDRAM
 * AXI (M1) master port by calling:
 *
 * alt_l2_addr_filter_cfg_set(0x0, <current_addr_filt_end_value>);
 * 
 * See: <em>ARM DDI 0246F, CoreLink Level 2 Cache Controller L2C-310 Technical
 * Reference Manual, Section 3.3.12 Address Filtering </em>.
 * \endinternal
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_mpu_addr_space_remap_0_to_sdram(void);

/*! @} */

/******************************************************************************/
/*! \addtogroup L2_ADDR_FLTR L2 Cache Address Filter
 *
 * The L2 cache address filter controls where physical addresses within certain
 * ranges of the MPU address space are directed.
 *
 * The L2 cache has master port connections to the L3 interconnect and the SDRAM
 * controller. A programmable address filter controls which portions of the
 * 32-bit physical address space use each master.
 * 
 * When l2 address filtering is configured and enabled, a physical address will
 * be redirected to one master or the other based upon the address filter
 * configuration.
 *
 * If \b address_filter_start <= \e physical_address < \b address_filter_end:
 * * then redirect \e physical_address to AXI Master Port M1 (SDRAM controller)
 * * else redirect \e physical_address to AXI Master Port M0 (L3 interconnect)
 *
 * See: <em>ARM DDI 0246F, CoreLink Level 2 Cache Controller L2C-310 Technical
 * Reference Manual, Section 3.3.12 Address Filtering </em> for more information.
 * @{
 */

/******************************************************************************/
/*!
 * Get the L2 cache address filtering configuration settings.
 *
 * \param       addr_filt_start
 *              [out] An output parameter variable for the address filtering
 *              start address for the range of physical addresses redirected to
 *              the SDRAM AXI master port. The value returned is always a 1 MiB
 *              aligned address.
 *              
 * \param       addr_filt_end
 *              [out] An output parameter variable for the address filtering
 *              end address for the range of physical addresses redirected to
 *              the SDRAM AXI master port. The value returned is always a 1 MiB
 *              aligned address.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   An bad argument was passed. Either \e addr_filt_start
 *                              or \e addr_filt_end or both are invalid addresses.
 */
ALT_STATUS_CODE alt_l2_addr_filter_cfg_get(uint32_t* addr_filt_start,
                                           uint32_t* addr_filt_end);

/******************************************************************************/
/*!
 * Set the L2 cache address filtering configuration settings.
 *
 * Address filtering start and end values must be 1 MiB aligned.
 *
 * \param       addr_filt_start
 *              The address filtering start address for the range of physical
 *              addresses redirected to the SDRAM AXI master port. Only bits
 *              [31:20] of the address are valid. Any bits outside the range
 *              [31:20] are invalid and will cause an error status to be
 *              returned.
 *              
 * \param       addr_filt_end
 *              The address filtering end address for the range of physical
 *              addresses redirected to the SDRAM AXI master port. Only bits
 *              [31:20] of the address are valid. Any bits outside the range
 *              [31:20] are invalid and will cause an error status to be
 *              returned.
 *              
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_ARG_RANGE An argument violates a range constraint. One or
 *                              more address arguments do not satisfy the argument
 *                              constraints.
 */
ALT_STATUS_CODE alt_l2_addr_filter_cfg_set(uint32_t addr_filt_start,
                                           uint32_t addr_filt_end);

/*! @} */

/******************************************************************************/
/*! \addtogroup ADDR_SPACE_MGR_MEM_COHERENCE ACP Memory Coherence and ID Mapping
 *
 * This API provides management of the ACP ID Mapper that enables data coherent
 * access to the MPU address space by external masters. The set of external
 * masters include L3 master peripherals and FPGA soft IP.
 *
 * The Accelerator Coherency Port (ACP) allows peripherals - including FPGA
 * based soft IP - to maintain data coherency with the Cortex-A9 MPCore
 * processors and the Snoop Control Unit (SCU).
 *
 * The ACP supports up to six masters. However, soft IP implemented in the FPGA
 * fabric can have a larger number of masters that need to access the ACP. The
 * ACP ID Mapper expands the number of masters able to access the ACP.  The ACP
 * ID Mapper is situated between the interconnect and the ACP of the MPU
 * subsystem. It has the following characteristics:
 * * Support for up to six concurrent ID mappings.
 * * 1 GiB coherent window into 4 GiB MPU address space
 * * Remaps the 5-bit user sideband signals used by the Snoop Control Unit (SCU)
 *   and L2 cache.
 * 
 * The function of the ACP ID Mapper is to map 12-bit Advanced Microcontroller
 * Bus Architecture (AMBA) Advanced eXtensible Interface (AXI) IDs (input
 * identifiers) from the Level 3 (L3) interconnect to 3-bit AXI IDs (output
 * identifiers) required by the ACP slave port.
 *
 * The ACP ID Mapper supports the two ID mapping modes:
 * * Dynamic Mapping - In this mode an input ID is automatically mapped to an
 *   available output ID. The dynamic mode is more flexible because the hardware
 *   handles the mapping. The hardware mapping allows an output ID to be used
 *   for more than one input ID. Output IDs are assigned to input IDs on a
 *   first-come, first-served basis.
 * * Fixed Mapping - In this mode there is a one-to-one mapping from input IDs
 *   to output IDs.
 *
 * Out of the total of eight ACP output ID values, only six are available to the
 * ACP ID Mapper for remapping.  The first two output IDs (0 and 1) are
 * dedicated to the Cortex-A9 processor cores in the MPU subsystem, leaving the
 * last six output IDs (2-7) available to the ACP ID mapper. Output IDs 2-6
 * support fixed and dynamic modes of operation while output ID 7 supports
 * dynamic mode only.
 *
 * The following table summarizes the usage of the 3-bit ouput ID values by the
 * ACP ID Mapper and their settings at reset.
 *
 *  Output ID  | Usage                                             | Reset State     
 * :-----------|:--------------------------------------------------|:------------
 *         0   | Reserved for Cortex-A9 cores.                     | -               
 *         1   | Reserved for Cortex-A9 cores.                     | -               
 *         2   | Assigned to Debug Access Port (DAP) input ID at   | Fixed           
 * :           | reset. After reset, can be reconfigured to either | DAP Master
 * :           | fixed or dynamic.                                 |:
 *         3   | Configurable fixed or dynamic mode.               | Dynamic         
 *         4   | Configurable fixed or dynamic mode.               | Dynamic         
 *         5   | Configurable fixed or dynamic mode.               | Dynamic         
 *         6   | Configurable fixed or dynamic mode.               | Dynamic         
 *         7   | Dynamic mode only.                                | Dynamic         
 *
 * Where <em>Output ID</em> is the ACP ID Mapper output value that goes to the ACP.
 *
 * Additionally, for masters unable to drive the AXI user sideband signals of
 * incoming transactions, the ACP ID Mapper allows control of the AXI user
 * sideband signal values. Not all masters drive these signals, so the ACP ID
 * Mapper makes it possible to drive the 5-bit user sideband signal with either
 * a default value (in dynamic mode) or specific values (in fixed mode).
 *
 * The ACP ID Mapper can also control which 1 GiB coherent window into memory is
 * accessed by masters of the L3 interconnect. Each fixed mapping can be
 * assigned a different user sideband signal and memory window to allow specific
 * settings for different masters. All dynamic mappings share a common user
 * sideband signal and memory window setting.  One important exception, however,
 * is that the ACP ID mapper always allows user sideband signals from the
 * FPGA-to-HPS bridge to pass through to the ACP regardless of the configured
 * user sideband value associated with the ID.
 *
 * The ACP ID Mapper has a 1 GiB address window into the MPU address space, which
 * is by default a view into the bottom 1 GiB of SDRAM. The ACP ID Mapper allows
 * transactions to be routed to different 1 GiB-sized memory views, called pages,
 * in both dynamic and fixed modes.
 *
 * See: <em>Chapter 6: Cortex-A9 Microprocessor Unit Subsystem</em> in
 * <em>Volume 3: Hard Processor System Technical Reference Manual</em> of the
 * <em>Arria V or Cyclone V Device Handbook</em> for a complete discussion of
 * the operation and restrictions on the ACP and the ACP ID Mapper.
 *
 * @{
 */

/******************************************************************************/
/*!
 * \name External Master ID Macros
 *
 * These macros define the HPS external master identifiers that are 12-bit input
 * IDs to the ACP ID Mapper. Some of the masters have a range of identifier
 * values assigned to them and are distinguished by taking a <em>(var)\</em>
 * argument.
 * @{
 */

/*! Bit mask for the relevant 12 bits of an external master ID */
#define ALT_ACP_ID_MAP_MASTER_ID_MASK           0xfff

/*! Master ID for L2M0 */
#define ALT_ACP_ID_MAP_MASTER_ID_L2M0(var)      (0x00000002 | (0x000007f8 & (var)))
/*! Master ID for DMA */
#define ALT_ACP_ID_MAP_MASTER_ID_DMA(var)       (0x00000001 | (0x00000078 & (var)))
/*! Master ID for EMAC0 */
#define ALT_ACP_ID_MAP_MASTER_ID_EMAC0(var)     (0x00000801 | (0x00000878 & (var)))
/*! Master ID for EMAC1 */
#define ALT_ACP_ID_MAP_MASTER_ID_EMAC1(var)     (0x00000802 | (0x00000878 & (var)))
/*! Master ID for USB0 */
#define ALT_ACP_ID_MAP_MASTER_ID_USB0           0x00000803
/*! Master ID for USB1 */
#define ALT_ACP_ID_MAP_MASTER_ID_USB1           0x00000806
/*! Master ID for NAND controller */
#define ALT_ACP_ID_MAP_MASTER_ID_NAND(var)      (0x00000804 | (0x00000ff8 & (var)))
/*! Master ID for Embedded Trace Router (ETR) */
#define ALT_ACP_ID_MAP_MASTER_ID_TMC            0x00000800
/*! Master ID for  Debug Access Port (DAP) */
#define ALT_ACP_ID_MAP_MASTER_ID_DAP            0x00000004
/*! Master ID for  SD/MMC controller */
#define ALT_ACP_ID_MAP_MASTER_ID_SDMMC          0x00000805
/*! Master ID for FPGA to HPS (F2H) bridge - conduit for soft IP masters in FPGA fabric */
#define ALT_ACP_ID_MAP_MASTER_ID_F2H(var)       (0x00000000 | (0x000007f8 & (var)))
/*! @} */

/******************************************************************************/
/*!
  * This type defines the enumerations 3-bit output ids to ACP ID mapper.
 */
typedef enum ALT_ACP_ID_OUTPUT_ID_e
{
    ALT_ACP_ID_OUT_FIXED_ID_2 = 2,  /*!< Assigned to the input ID of the DAP at reset. 
                                     *   After reset, can be either fixed or dynamic, 
                                     *   programmed by software.
                                     */
    ALT_ACP_ID_OUT_DYNAM_ID_3 = 3,  /*!< Fixed or dynamic, programmed by software output id */
    ALT_ACP_ID_OUT_DYNAM_ID_4 = 4,  /*!< Fixed or dynamic, programmed by software output id */
    ALT_ACP_ID_OUT_DYNAM_ID_5 = 5,  /*!< Fixed or dynamic, programmed by software output id */
    ALT_ACP_ID_OUT_DYNAM_ID_6 = 6,  /*!< Fixed or dynamic, programmed by software output id */
    ALT_ACP_ID_OUT_DYNAM_ID_7 = 7   /*!< Dynamic mapping only */
} ALT_ACP_ID_OUTPUT_ID_t;

/*!
 * This type defines the enumerations used to specify the 1 GiB page view of the
 * MPU address space used by an ACP ID mapping configuration.
 */
typedef enum ALT_ACP_ID_MAP_PAGE_e
{
    ALT_ACP_ID_MAP_PAGE_0 = 0,  /*!< Page 0 - MPU address range 0x00000000 - 0x3FFFFFFF */
    ALT_ACP_ID_MAP_PAGE_1 = 1,  /*!< Page 1 - MPU address range 0x40000000 - 0x7FFFFFFF */
    ALT_ACP_ID_MAP_PAGE_2 = 2,  /*!< Page 2 - MPU address range 0x80000000 - 0xBFFFFFFF */
    ALT_ACP_ID_MAP_PAGE_3 = 3   /*!< Page 3 - MPU address range 0xC0000000 - 0xFFFFFFFF */
} ALT_ACP_ID_MAP_PAGE_t;

/******************************************************************************/
/*!
 * Configure a fixed ACP ID mapping for read transactions originating from
 * external masters identified by \e input_id. The \e input_id value is
 * translated to the specified 3-bit \e output_id required by the ACP slave
 * port.
 *
 * \param       input_id
 *              The 12 bit external master ID originating read transactions
 *              targeted for ID translation. Valid argument range must be 0 <=
 *              \e output_id <= 4095.
 *
 * \param       output_id
 *              The 3-bit output ID value the ACP ID Mapper translates read
 *              transactions identified by \e input_id to. This is the value
 *              propogated to the ACP slave port.  Valid argument values must be
 *              0 <= \e output_id <= 7.
 *
 * \param       page
 *              The MPU address space page view to use for the ACP window used
 *              by the ID tranlation mapping.
 *
 * \param       aruser
 *              The 5-bit AXI ARUSER read user sideband signal value to use for
 *              masters unable to drive the AXI user sideband signals.  Valid
 *              argument range is 0 <= \e aruser <= 31.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_RESERVED  The argument value is reserved or unavailable.
 * \retval      ALT_E_ARG_RANGE An argument violates a range constraint. One or
 *                              more of the \e input_id, and/or \e output_id
 *                              arguments violates its range constraint.
 * \retval      ALT_E_BAD_ARG   The \e page argument is invalid.
 */
ALT_STATUS_CODE alt_acp_id_map_fixed_read_set(const uint32_t input_id,
                                              const uint32_t output_id,
                                              const ALT_ACP_ID_MAP_PAGE_t page,
                                              const uint32_t aruser);

/******************************************************************************/
/*!
 * Configure a fixed ACP ID mapping for write transactions originating from
 * external masters identified by \e input_id. The \e input_id value is
 * translated to the specified 3-bit \e output_id required by the ACP slave
 * port.
 *
 * \param       input_id
 *              The 12 bit external master ID originating write transactions
 *              targeted for ID translation. Valid argument range must be 0 <=
 *              \e output_id <= 4095.
 *
 * \param       output_id
 *              The 3-bit output ID value the ACP ID Mapper translates write
 *              transactions identified by \e input_id to. This is the value
 *              propogated to the ACP slave port.  Valid argument values must be
 *              0 <= \e output_id <= 7.
 *
 * \param       page
 *              The MPU address space page view to use for the ACP window used
 *              by the ID tranlation mapping.
 *
 * \param       awuser
 *              The 5-bit AXI AWUSER write user sideband signal value to use for
 *              masters unable to drive the AXI user sideband signals.  Valid
 *              argument range is 0 <= \e awuser <= 31.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_RESERVED  The argument value is reserved or unavailable.
 * \retval      ALT_E_ARG_RANGE An argument violates a range constraint. One or
 *                              more of the \e input_id, and/or \e output_id
 *                              arguments violates its range constraint.
 * \retval      ALT_E_BAD_ARG   The \e page argument is invalid.
 */
ALT_STATUS_CODE alt_acp_id_map_fixed_write_set(const uint32_t input_id,
                                               const uint32_t output_id,
                                               const ALT_ACP_ID_MAP_PAGE_t page,
                                               const uint32_t awuser);

/******************************************************************************/
/*!
 * Configure the designated 3-bit output ID as an available identifier resource
 * for use by the dynamic ID mapping function of the ACP ID Mapper for read
 * transactions. The \e output_id value is available for dynamic assignment to
 * external master read transaction IDs that do not have an explicit fixed ID
 * mapping.
 *
 * \param       output_id
 *              The 3-bit output ID value designated as an available ID for use
 *              by the dynamic mapping function of the ACP ID Mapper. The \e
 *              ouput_id value is used exclusively for dynamic ID mapping until
 *              reconfigured as a fixed ID mapping by a call to
 *              alt_acp_id_map_fixed_read_set().  Valid argument values must be
 *              0 <= \e output_id <= 7.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_RESERVED  The argument value is reserved or unavailable.
 * \retval      ALT_E_ARG_RANGE An argument violates a range constraint.
 */
ALT_STATUS_CODE alt_acp_id_map_dynamic_read_set(const uint32_t output_id);

/******************************************************************************/
/*!
 * Configure the designated 3-bit output ID as an available identifier resource
 * for use by the dynamic ID mapping function of the ACP ID Mapper for write
 * transactions. The \e output_id value is available for dynamic assignment to
 * external master write transaction IDs that do not have an explicit fixed ID
 * mapping.
 *
 * \param       output_id
 *              The 3-bit output ID value designated as an available ID for use
 *              by the dynamic mapping function of the ACP ID Mapper. The \e
 *              ouput_id value is used exclusively for dynamic ID mapping until
 *              reconfigured as a fixed ID mapping by a call to
 *              alt_acp_id_map_fixed_write_set().  Valid argument values must be
 *              0 <= \e output_id <= 7.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_RESERVED  The argument value is reserved or unavailable.
 * \retval      ALT_E_ARG_RANGE An argument violates a range constraint.
 */
ALT_STATUS_CODE alt_acp_id_map_dynamic_write_set(const uint32_t output_id);

/******************************************************************************/
/*!
 * Configure the page and user read sideband signal options that are applied to
 * all read transactions that have their input IDs dynamically mapped.
 *
 * \param       page
 *              The MPU address space page view to use for the ACP window used
 *              by the dynamic ID tranlation mapping.
 *
 * \param       aruser
 *              The 5-bit AXI ARUSER read user sideband signal value to use for
 *              masters unable to drive the AXI user sideband signals.  Valid
 *              argument range is 0 <= \e aruser <= 31.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_RESERVED  The argument value is reserved or unavailable.
 * \retval      ALT_E_ARG_RANGE An argument violates a range constraint. One or
 *                              more of the \e page and/or \e aruser
 *                              arguments violates its range constraint.
 * \retval      ALT_E_BAD_ARG   The \e mid argument is not a valid master 
 *                              identifier.
 */
ALT_STATUS_CODE alt_acp_id_map_dynamic_read_options_set(const ALT_ACP_ID_MAP_PAGE_t page,
                                                        const uint32_t aruser);

/******************************************************************************/
/*!
 * Configure the page and user write sideband signal options that are applied to
 * all write transactions that have their input IDs dynamically mapped.
 *
 * \param       page
 *              The MPU address space page view to use for the ACP window used
 *              by the dynamic ID tranlation mapping.
 *
 * \param       awuser
 *              The 5-bit AXI AWUSER write user sideband signal value to use for
 *              masters unable to drive the AXI user sideband signals.  Valid
 *              argument range is 0 <= \e aruser <= 31.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_RESERVED  The argument value is reserved or unavailable.
 * \retval      ALT_E_ARG_RANGE An argument violates a range constraint. One or
 *                              more of the \e page and/or \e awuser
 *                              arguments violates its range constraint.
 * \retval      ALT_E_BAD_ARG   The \e mid argument is not a valid master 
 *                              identifier.
 */
ALT_STATUS_CODE alt_acp_id_map_dynamic_write_options_set(const ALT_ACP_ID_MAP_PAGE_t page,
                                                         const uint32_t awuser);

/******************************************************************************/
/*!
 * Return the current read transaction mapping configuration used by the ACP ID
 * Mapper for the specified output ID.
 *
 * If \e output_id is configured as a fixed mapping then \b true is returned in
 * the \e fixed output parameter and the translation mapping options configured
 * for that \e output_id are returned in the other output parameters.
 *
 * If \e output_id is configured as a dynamic mapping then \b false is returned
 * in the \e fixed output parameter and the translation mapping options
 * configured for all dynamically remapped output IDs are returned in the other
 * output parameters.
 *
 * \param       output_id
 *              The output ID to return the mapping configuration for. 0 <= \e
 *              output_id <= 7.
 *
 * \param       fixed
 *              [out] Set to \b true if the specified \e output_id is a fixed ID
 *              mapping configuration. Set to \b false if the mapping
 *              configuration is dynamic.
 *
 * \param       input_id
 *              [out] The input ID of the external master that a fixed ID
 *              mapping is applied to for the \e output_id. If \e fixed is \b
 *              false then this output parameter is set to 0 and its value
 *              should be considered as not applicable.
 *
 * \param       page
 *              [out] The MPU address space page view used by the mapping
 *              configuration.
 *
 * \param       aruser
 *              [out] The 5-bit AXI ARUSER read user sideband signal value used
 *              by the mapping configuration when masters are unable to drive
 *              the AXI user sideband signals.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_RESERVED  The argument value is reserved or unavailable.
 * \retval      ALT_E_ARG_RANGE An argument violates a range constraint. The \e 
 *                              output_id argument violates its range constraint.
 */
ALT_STATUS_CODE alt_acp_id_map_read_options_get(const uint32_t output_id,
                                                bool* fixed,
                                                uint32_t* input_id,
                                                ALT_ACP_ID_MAP_PAGE_t* page,
                                                uint32_t* aruser);

/******************************************************************************/
/*!
 * Return the current write transaction mapping configuration used by the ACP ID
 * Mapper for the specified output ID.
 *
 * If \e output_id is configured as a fixed mapping then \b true is returned in
 * the \e fixed output parameter and the translation mapping options configured
 * for that \e output_id are returned in the other output parameters.
 *
 * If \e output_id is configured as a dynamic mapping then \b false is returned
 * in the \e fixed output parameter and the translation mapping options
 * configured for all dynamically remapped output IDs are returned in the other
 * output parameters.
 *
 * \param       output_id
 *              The output ID to return the mapping configuration for. 0 <= \e
 *              output_id <= 7.
 *
 * \param       fixed
 *              [out] Set to \b true if the specified \e output_id is a fixed ID
 *              mapping configuration. Set to \b false if the mapping
 *              configuration is dynamic.
 *
 * \param       input_id
 *              [out] The input ID of the external master that a fixed ID
 *              mapping is applied to for the \e output_id. If \e fixed is \b
 *              false then this output parameter is set to 0 and its value
 *              should be considered as not applicable.
 *
 * \param       page
 *              [out] The MPU address space page view used by the mapping
 *              configuration.
 *
 * \param       awuser
 *              [out] The 5-bit AXI AWUSER write user sideband signal value used
 *              by the mapping configuration when masters are unable to drive
 *              the AXI user sideband signals.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_RESERVED  The argument value is reserved or unavailable.
 * \retval      ALT_E_ARG_RANGE An argument violates a range constraint. The \e 
 *                              output_id argument violates its range constraint.
 */
ALT_STATUS_CODE alt_acp_id_map_write_options_get(const uint32_t output_id,
                                                 bool* fixed,
                                                 uint32_t* input_id,
                                                 ALT_ACP_ID_MAP_PAGE_t* page,
                                                 uint32_t* awuser);

/*! @} */

/*! @} */

#endif  /* __ASSEMBLY__ */

#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALT_ADDRESS_SPACE_H__ */
