/* ### HEADER ### */

#ifndef __XFPD_SLCR_SECURE_H__
    #define __XFPD_SLCR_SECURE_H__


    #ifdef __cplusplus
    extern "C" {
    #endif

/**
 * XfpdSlcrSecure Base Address
 */
    #define XFPD_SLCR_SECURE_BASEADDR                   0xFD690000UL

/**
 * Register: XfpdSlcrSecCtrl
 */
    #define XFPD_SLCR_SEC_CTRL                          ( ( XFPD_SLCR_SECURE_BASEADDR ) +0x00000004UL )
    #define XFPD_SLCR_SEC_CTRL_RSTVAL                   0x00000000UL

    #define XFPD_SLCR_SEC_CTRL_SLVERR_EN_SHIFT          0UL
    #define XFPD_SLCR_SEC_CTRL_SLVERR_EN_WIDTH          1UL
    #define XFPD_SLCR_SEC_CTRL_SLVERR_EN_MASK           0x00000001UL
    #define XFPD_SLCR_SEC_CTRL_SLVERR_EN_DEFVAL         0x0UL

/**
 * Register: XfpdSlcrSecIsr
 */
    #define XFPD_SLCR_SEC_ISR                           ( ( XFPD_SLCR_SECURE_BASEADDR ) +0x00000008UL )
    #define XFPD_SLCR_SEC_ISR_RSTVAL                    0x00000000UL

    #define XFPD_SLCR_SEC_ISR_ADDR_DECD_ERR_SHIFT       0UL
    #define XFPD_SLCR_SEC_ISR_ADDR_DECD_ERR_WIDTH       1UL
    #define XFPD_SLCR_SEC_ISR_ADDR_DECD_ERR_MASK        0x00000001UL
    #define XFPD_SLCR_SEC_ISR_ADDR_DECD_ERR_DEFVAL      0x0UL

/**
 * Register: XfpdSlcrSecImr
 */
    #define XFPD_SLCR_SEC_IMR                           ( ( XFPD_SLCR_SECURE_BASEADDR ) +0x0000000CUL )
    #define XFPD_SLCR_SEC_IMR_RSTVAL                    0x00000001UL

    #define XFPD_SLCR_SEC_IMR_ADDR_DECD_ERR_SHIFT       0UL
    #define XFPD_SLCR_SEC_IMR_ADDR_DECD_ERR_WIDTH       1UL
    #define XFPD_SLCR_SEC_IMR_ADDR_DECD_ERR_MASK        0x00000001UL
    #define XFPD_SLCR_SEC_IMR_ADDR_DECD_ERR_DEFVAL      0x1UL

/**
 * Register: XfpdSlcrSecIer
 */
    #define XFPD_SLCR_SEC_IER                           ( ( XFPD_SLCR_SECURE_BASEADDR ) +0x00000010UL )
    #define XFPD_SLCR_SEC_IER_RSTVAL                    0x00000000UL

    #define XFPD_SLCR_SEC_IER_ADDR_DECD_ERR_SHIFT       0UL
    #define XFPD_SLCR_SEC_IER_ADDR_DECD_ERR_WIDTH       1UL
    #define XFPD_SLCR_SEC_IER_ADDR_DECD_ERR_MASK        0x00000001UL
    #define XFPD_SLCR_SEC_IER_ADDR_DECD_ERR_DEFVAL      0x0UL

/**
 * Register: XfpdSlcrSecIdr
 */
    #define XFPD_SLCR_SEC_IDR                           ( ( XFPD_SLCR_SECURE_BASEADDR ) +0x00000014UL )
    #define XFPD_SLCR_SEC_IDR_RSTVAL                    0x00000000UL

    #define XFPD_SLCR_SEC_IDR_ADDR_DECD_ERR_SHIFT       0UL
    #define XFPD_SLCR_SEC_IDR_ADDR_DECD_ERR_WIDTH       1UL
    #define XFPD_SLCR_SEC_IDR_ADDR_DECD_ERR_MASK        0x00000001UL
    #define XFPD_SLCR_SEC_IDR_ADDR_DECD_ERR_DEFVAL      0x0UL

/**
 * Register: XfpdSlcrSecItr
 */
    #define XFPD_SLCR_SEC_ITR                           ( ( XFPD_SLCR_SECURE_BASEADDR ) +0x00000018UL )
    #define XFPD_SLCR_SEC_ITR_RSTVAL                    0x00000000UL

    #define XFPD_SLCR_SEC_ITR_ADDR_DECD_ERR_SHIFT       0UL
    #define XFPD_SLCR_SEC_ITR_ADDR_DECD_ERR_WIDTH       1UL
    #define XFPD_SLCR_SEC_ITR_ADDR_DECD_ERR_MASK        0x00000001UL
    #define XFPD_SLCR_SEC_ITR_ADDR_DECD_ERR_DEFVAL      0x0UL

/**
 * Register: XfpdSlcrSecSata
 */
    #define XFPD_SLCR_SEC_SATA                          ( ( XFPD_SLCR_SECURE_BASEADDR ) +0x00000020UL )
    #define XFPD_SLCR_SEC_SATA_RSTVAL                   0x0000000eUL

    #define XFPD_SLCR_SEC_SATA_TZ_AXIMDMA1_SHIFT        3UL
    #define XFPD_SLCR_SEC_SATA_TZ_AXIMDMA1_WIDTH        1UL
    #define XFPD_SLCR_SEC_SATA_TZ_AXIMDMA1_MASK         0x00000008UL
    #define XFPD_SLCR_SEC_SATA_TZ_AXIMDMA1_DEFVAL       0x1UL

    #define XFPD_SLCR_SEC_SATA_TZ_AXIMDMA0_SHIFT        2UL
    #define XFPD_SLCR_SEC_SATA_TZ_AXIMDMA0_WIDTH        1UL
    #define XFPD_SLCR_SEC_SATA_TZ_AXIMDMA0_MASK         0x00000004UL
    #define XFPD_SLCR_SEC_SATA_TZ_AXIMDMA0_DEFVAL       0x1UL

    #define XFPD_SLCR_SEC_SATA_TZ_AXIS_SHIFT            1UL
    #define XFPD_SLCR_SEC_SATA_TZ_AXIS_WIDTH            1UL
    #define XFPD_SLCR_SEC_SATA_TZ_AXIS_MASK             0x00000002UL
    #define XFPD_SLCR_SEC_SATA_TZ_AXIS_DEFVAL           0x1UL

    #define XFPD_SLCR_SEC_SATA_TZ_EN_SHIFT              0UL
    #define XFPD_SLCR_SEC_SATA_TZ_EN_WIDTH              1UL
    #define XFPD_SLCR_SEC_SATA_TZ_EN_MASK               0x00000001UL
    #define XFPD_SLCR_SEC_SATA_TZ_EN_DEFVAL             0x0UL

/**
 * Register: XfpdSlcrSecPcie
 */
    #define XFPD_SLCR_SEC_PCIE                          ( ( XFPD_SLCR_SECURE_BASEADDR ) +0x00000030UL )
    #define XFPD_SLCR_SEC_PCIE_RSTVAL                   0x01ffffffUL

    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_3_SHIFT           24UL
    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_3_WIDTH           1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_3_MASK            0x01000000UL
    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_3_DEFVAL          0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_2_SHIFT           23UL
    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_2_WIDTH           1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_2_MASK            0x00800000UL
    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_2_DEFVAL          0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_1_SHIFT           22UL
    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_1_WIDTH           1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_1_MASK            0x00400000UL
    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_1_DEFVAL          0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_0_SHIFT           21UL
    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_0_WIDTH           1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_0_MASK            0x00200000UL
    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_0_DEFVAL          0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_7_SHIFT       20UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_7_WIDTH       1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_7_MASK        0x00100000UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_7_DEFVAL      0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_6_SHIFT       19UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_6_WIDTH       1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_6_MASK        0x00080000UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_6_DEFVAL      0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_5_SHIFT       18UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_5_WIDTH       1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_5_MASK        0x00040000UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_5_DEFVAL      0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_4_SHIFT       17UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_4_WIDTH       1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_4_MASK        0x00020000UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_4_DEFVAL      0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_3_SHIFT       16UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_3_WIDTH       1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_3_MASK        0x00010000UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_3_DEFVAL      0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_2_SHIFT       15UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_2_WIDTH       1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_2_MASK        0x00008000UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_2_DEFVAL      0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_1_SHIFT       14UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_1_WIDTH       1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_1_MASK        0x00004000UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_1_DEFVAL      0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_0_SHIFT       13UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_0_WIDTH       1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_0_MASK        0x00002000UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_INGR_0_DEFVAL      0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_7_SHIFT        12UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_7_WIDTH        1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_7_MASK         0x00001000UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_7_DEFVAL       0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_6_SHIFT        11UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_6_WIDTH        1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_6_MASK         0x00000800UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_6_DEFVAL       0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_5_SHIFT        10UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_5_WIDTH        1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_5_MASK         0x00000400UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_5_DEFVAL       0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_4_SHIFT        9UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_4_WIDTH        1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_4_MASK         0x00000200UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_4_DEFVAL       0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_3_SHIFT        8UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_3_WIDTH        1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_3_MASK         0x00000100UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_3_DEFVAL       0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_2_SHIFT        7UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_2_WIDTH        1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_2_MASK         0x00000080UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_2_DEFVAL       0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_1_SHIFT        6UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_1_WIDTH        1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_1_MASK         0x00000040UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_1_DEFVAL       0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_0_SHIFT        5UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_0_WIDTH        1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_0_MASK         0x00000020UL
    #define XFPD_SLCR_SEC_PCIE_TZ_AT_EGR_0_DEFVAL       0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_REGS_SHIFT        4UL
    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_REGS_WIDTH        1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_REGS_MASK         0x00000010UL
    #define XFPD_SLCR_SEC_PCIE_TZ_DMA_REGS_DEFVAL       0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_MSIX_PBA_SHIFT        3UL
    #define XFPD_SLCR_SEC_PCIE_TZ_MSIX_PBA_WIDTH        1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_MSIX_PBA_MASK         0x00000008UL
    #define XFPD_SLCR_SEC_PCIE_TZ_MSIX_PBA_DEFVAL       0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_MSIX_TABLE_SHIFT      2UL
    #define XFPD_SLCR_SEC_PCIE_TZ_MSIX_TABLE_WIDTH      1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_MSIX_TABLE_MASK       0x00000004UL
    #define XFPD_SLCR_SEC_PCIE_TZ_MSIX_TABLE_DEFVAL     0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_ECAM_SHIFT            1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_ECAM_WIDTH            1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_ECAM_MASK             0x00000002UL
    #define XFPD_SLCR_SEC_PCIE_TZ_ECAM_DEFVAL           0x1UL

    #define XFPD_SLCR_SEC_PCIE_TZ_BRIDGE_REGS_SHIFT     0UL
    #define XFPD_SLCR_SEC_PCIE_TZ_BRIDGE_REGS_WIDTH     1UL
    #define XFPD_SLCR_SEC_PCIE_TZ_BRIDGE_REGS_MASK      0x00000001UL
    #define XFPD_SLCR_SEC_PCIE_TZ_BRIDGE_REGS_DEFVAL    0x1UL

/**
 * Register: XfpdSlcrSecDpdma
 */
    #define XFPD_SLCR_SEC_DPDMA                         ( ( XFPD_SLCR_SECURE_BASEADDR ) +0x00000040UL )
    #define XFPD_SLCR_SEC_DPDMA_RSTVAL                  0x00000001UL

    #define XFPD_SLCR_SEC_DPDMA_TZ_SHIFT                0UL
    #define XFPD_SLCR_SEC_DPDMA_TZ_WIDTH                1UL
    #define XFPD_SLCR_SEC_DPDMA_TZ_MASK                 0x00000001UL
    #define XFPD_SLCR_SEC_DPDMA_TZ_DEFVAL               0x1UL

/**
 * Register: XfpdSlcrSecGdma
 */
    #define XFPD_SLCR_SEC_GDMA                          ( ( XFPD_SLCR_SECURE_BASEADDR ) +0x00000050UL )
    #define XFPD_SLCR_SEC_GDMA_RSTVAL                   0x000000ffUL

    #define XFPD_SLCR_SEC_GDMA_TZ_SHIFT                 0UL
    #define XFPD_SLCR_SEC_GDMA_TZ_WIDTH                 8UL
    #define XFPD_SLCR_SEC_GDMA_TZ_MASK                  0x000000ffUL
    #define XFPD_SLCR_SEC_GDMA_TZ_DEFVAL                0xffUL

/**
 * Register: XfpdSlcrSecGic
 */
    #define XFPD_SLCR_SEC_GIC                           ( ( XFPD_SLCR_SECURE_BASEADDR ) +0x00000060UL )
    #define XFPD_SLCR_SEC_GIC_RSTVAL                    0x00000000UL

    #define XFPD_SLCR_SEC_GIC_CFG_DIS_SHIFT             0UL
    #define XFPD_SLCR_SEC_GIC_CFG_DIS_WIDTH             1UL
    #define XFPD_SLCR_SEC_GIC_CFG_DIS_MASK              0x00000001UL
    #define XFPD_SLCR_SEC_GIC_CFG_DIS_DEFVAL            0x0UL


    #ifdef __cplusplus
}
    #endif

#endif /* __XFPD_SLCR_SECURE_H__ */
