/*
 * Copyright (c) 2007-2013 Xilinx, Inc.  All rights reserved.
 *
 * Xilinx, Inc.
 * XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION "AS IS" AS A
 * COURTESY TO YOU.  BY PROVIDING THIS DESIGN, CODE, OR INFORMATION AS
 * ONE POSSIBLE   IMPLEMENTATION OF THIS FEATURE, APPLICATION OR
 * STANDARD, XILINX IS MAKING NO REPRESENTATION THAT THIS IMPLEMENTATION
 * IS FREE FROM ANY CLAIMS OF INFRINGEMENT, AND YOU ARE RESPONSIBLE
 * FOR OBTAINING ANY RIGHTS YOU MAY REQUIRE FOR YOUR IMPLEMENTATION.
 * XILINX EXPRESSLY DISCLAIMS ANY WARRANTY WHATSOEVER WITH RESPECT TO
 * THE ADEQUACY OF THE IMPLEMENTATION, INCLUDING BUT NOT LIMITED TO
 * ANY WARRANTIES OR REPRESENTATIONS THAT THIS IMPLEMENTATION IS FREE
 * FROM CLAIMS OF INFRINGEMENT, IMPLIED WARRANTIES OF MERCHANTABILITY
 * AND FITNESS FOR A PARTICULAR PURPOSE.
 *
 */

#ifndef __XTOPOLOGY_H_
    #define __XTOPOLOGY_H_

    #ifdef __cplusplus
        extern "C" {
    #endif

    enum xemac_types
    {
        xemac_type_unknown = -1, xemac_type_xps_emaclite, xemac_type_xps_ll_temac, xemac_type_axi_ethernet, xemac_type_emacps
    };

    struct xtopology_t
    {
        unsigned emac_baseaddr;
        enum xemac_types emac_type;
        unsigned intc_baseaddr;
        unsigned intc_emac_intr;   /* valid only for xemac_type_xps_emaclite */
        unsigned scugic_baseaddr;  /* valid only for Zynq */
        unsigned scugic_emac_intr; /* valid only for GEM */
    };

    extern int x_topology_n_emacs;
    extern struct xtopology_t x_topology[];

    int x_topology_find_index( unsigned base );

    #ifdef __cplusplus
        }
    #endif

#endif /* ifndef __XTOPOLOGY_H_ */
