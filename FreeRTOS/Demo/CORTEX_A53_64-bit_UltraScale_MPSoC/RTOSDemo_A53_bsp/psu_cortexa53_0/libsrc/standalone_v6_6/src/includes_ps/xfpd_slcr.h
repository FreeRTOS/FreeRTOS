/* ### HEADER ### */

#ifndef __XFPD_SLCR_H__
    #define __XFPD_SLCR_H__


    #ifdef __cplusplus
    extern "C" {
    #endif

/**
 * XfpdSlcr Base Address
 */
    #define XFPD_SLCR_BASEADDR                      0xFD610000UL

/**
 * Register: XfpdSlcrWprot0
 */
    #define XFPD_SLCR_WPROT0                        ( ( XFPD_SLCR_BASEADDR ) +0x00000000UL )
    #define XFPD_SLCR_WPROT0_RSTVAL                 0x00000001UL

    #define XFPD_SLCR_WPROT0_ACT_SHIFT              0UL
    #define XFPD_SLCR_WPROT0_ACT_WIDTH              1UL
    #define XFPD_SLCR_WPROT0_ACT_MASK               0x00000001UL
    #define XFPD_SLCR_WPROT0_ACT_DEFVAL             0x1UL

/**
 * Register: XfpdSlcrCtrl
 */
    #define XFPD_SLCR_CTRL                          ( ( XFPD_SLCR_BASEADDR ) +0x00000004UL )
    #define XFPD_SLCR_CTRL_RSTVAL                   0x00000000UL

    #define XFPD_SLCR_CTRL_SLVERR_EN_SHIFT          0UL
    #define XFPD_SLCR_CTRL_SLVERR_EN_WIDTH          1UL
    #define XFPD_SLCR_CTRL_SLVERR_EN_MASK           0x00000001UL
    #define XFPD_SLCR_CTRL_SLVERR_EN_DEFVAL         0x0UL

/**
 * Register: XfpdSlcrIsr
 */
    #define XFPD_SLCR_ISR                           ( ( XFPD_SLCR_BASEADDR ) +0x00000008UL )
    #define XFPD_SLCR_ISR_RSTVAL                    0x00000000UL

    #define XFPD_SLCR_ISR_ADDR_DECD_ERR_SHIFT       0UL
    #define XFPD_SLCR_ISR_ADDR_DECD_ERR_WIDTH       1UL
    #define XFPD_SLCR_ISR_ADDR_DECD_ERR_MASK        0x00000001UL
    #define XFPD_SLCR_ISR_ADDR_DECD_ERR_DEFVAL      0x0UL

/**
 * Register: XfpdSlcrImr
 */
    #define XFPD_SLCR_IMR                           ( ( XFPD_SLCR_BASEADDR ) +0x0000000CUL )
    #define XFPD_SLCR_IMR_RSTVAL                    0x00000001UL

    #define XFPD_SLCR_IMR_ADDR_DECD_ERR_SHIFT       0UL
    #define XFPD_SLCR_IMR_ADDR_DECD_ERR_WIDTH       1UL
    #define XFPD_SLCR_IMR_ADDR_DECD_ERR_MASK        0x00000001UL
    #define XFPD_SLCR_IMR_ADDR_DECD_ERR_DEFVAL      0x1UL

/**
 * Register: XfpdSlcrIer
 */
    #define XFPD_SLCR_IER                           ( ( XFPD_SLCR_BASEADDR ) +0x00000010UL )
    #define XFPD_SLCR_IER_RSTVAL                    0x00000000UL

    #define XFPD_SLCR_IER_ADDR_DECD_ERR_SHIFT       0UL
    #define XFPD_SLCR_IER_ADDR_DECD_ERR_WIDTH       1UL
    #define XFPD_SLCR_IER_ADDR_DECD_ERR_MASK        0x00000001UL
    #define XFPD_SLCR_IER_ADDR_DECD_ERR_DEFVAL      0x0UL

/**
 * Register: XfpdSlcrIdr
 */
    #define XFPD_SLCR_IDR                           ( ( XFPD_SLCR_BASEADDR ) +0x00000014UL )
    #define XFPD_SLCR_IDR_RSTVAL                    0x00000000UL

    #define XFPD_SLCR_IDR_ADDR_DECD_ERR_SHIFT       0UL
    #define XFPD_SLCR_IDR_ADDR_DECD_ERR_WIDTH       1UL
    #define XFPD_SLCR_IDR_ADDR_DECD_ERR_MASK        0x00000001UL
    #define XFPD_SLCR_IDR_ADDR_DECD_ERR_DEFVAL      0x0UL

/**
 * Register: XfpdSlcrItr
 */
    #define XFPD_SLCR_ITR                           ( ( XFPD_SLCR_BASEADDR ) +0x00000018UL )
    #define XFPD_SLCR_ITR_RSTVAL                    0x00000000UL

    #define XFPD_SLCR_ITR_ADDR_DECD_ERR_SHIFT       0UL
    #define XFPD_SLCR_ITR_ADDR_DECD_ERR_WIDTH       1UL
    #define XFPD_SLCR_ITR_ADDR_DECD_ERR_MASK        0x00000001UL
    #define XFPD_SLCR_ITR_ADDR_DECD_ERR_DEFVAL      0x0UL

/**
 * Register: XfpdSlcrWdtClkSel
 */
    #define XFPD_SLCR_WDT_CLK_SEL                   ( ( XFPD_SLCR_BASEADDR ) +0x00000100UL )
    #define XFPD_SLCR_WDT_CLK_SEL_RSTVAL            0x00000000UL

    #define XFPD_SLCR_WDT_CLK_SEL_SHIFT             0UL
    #define XFPD_SLCR_WDT_CLK_SEL_WIDTH             1UL
    #define XFPD_SLCR_WDT_CLK_SEL_MASK              0x00000001UL
    #define XFPD_SLCR_WDT_CLK_SEL_DEFVAL            0x0UL

/**
 * Register: XfpdSlcrIntFpd
 */
    #define XFPD_SLCR_INT_FPD                       ( ( XFPD_SLCR_BASEADDR ) +0x00000200UL )
    #define XFPD_SLCR_INT_FPD_RSTVAL                0x00000000UL

    #define XFPD_SLCR_INT_FPD_GFM_SEL_SHIFT         0UL
    #define XFPD_SLCR_INT_FPD_GFM_SEL_WIDTH         1UL
    #define XFPD_SLCR_INT_FPD_GFM_SEL_MASK          0x00000001UL
    #define XFPD_SLCR_INT_FPD_GFM_SEL_DEFVAL        0x0UL

/**
 * Register: XfpdSlcrGpu
 */
    #define XFPD_SLCR_GPU                           ( ( XFPD_SLCR_BASEADDR ) +0x0000100CUL )
    #define XFPD_SLCR_GPU_RSTVAL                    0x00000007UL

    #define XFPD_SLCR_GPU_ARCACHE_SHIFT             7UL
    #define XFPD_SLCR_GPU_ARCACHE_WIDTH             4UL
    #define XFPD_SLCR_GPU_ARCACHE_MASK              0x00000780UL
    #define XFPD_SLCR_GPU_ARCACHE_DEFVAL            0x0UL

    #define XFPD_SLCR_GPU_AWCACHE_SHIFT             3UL
    #define XFPD_SLCR_GPU_AWCACHE_WIDTH             4UL
    #define XFPD_SLCR_GPU_AWCACHE_MASK              0x00000078UL
    #define XFPD_SLCR_GPU_AWCACHE_DEFVAL            0x0UL

    #define XFPD_SLCR_GPU_PP1_IDLE_SHIFT            2UL
    #define XFPD_SLCR_GPU_PP1_IDLE_WIDTH            1UL
    #define XFPD_SLCR_GPU_PP1_IDLE_MASK             0x00000004UL
    #define XFPD_SLCR_GPU_PP1_IDLE_DEFVAL           0x1UL

    #define XFPD_SLCR_GPU_PP0_IDLE_SHIFT            1UL
    #define XFPD_SLCR_GPU_PP0_IDLE_WIDTH            1UL
    #define XFPD_SLCR_GPU_PP0_IDLE_MASK             0x00000002UL
    #define XFPD_SLCR_GPU_PP0_IDLE_DEFVAL           0x1UL

    #define XFPD_SLCR_GPU_IDLE_SHIFT                0UL
    #define XFPD_SLCR_GPU_IDLE_WIDTH                1UL
    #define XFPD_SLCR_GPU_IDLE_MASK                 0x00000001UL
    #define XFPD_SLCR_GPU_IDLE_DEFVAL               0x1UL

/**
 * Register: XfpdSlcrGdmaCfg
 */
    #define XFPD_SLCR_GDMA_CFG                      ( ( XFPD_SLCR_BASEADDR ) +0x00003000UL )
    #define XFPD_SLCR_GDMA_CFG_RSTVAL               0x00000048UL

    #define XFPD_SLCR_GDMA_CFG_BUS_WIDTH_SHIFT      5UL
    #define XFPD_SLCR_GDMA_CFG_BUS_WIDTH_WIDTH      2UL
    #define XFPD_SLCR_GDMA_CFG_BUS_WIDTH_MASK       0x00000060UL
    #define XFPD_SLCR_GDMA_CFG_BUS_WIDTH_DEFVAL     0x2UL

    #define XFPD_SLCR_GDMA_CFG_NUM_CH_SHIFT         0UL
    #define XFPD_SLCR_GDMA_CFG_NUM_CH_WIDTH         5UL
    #define XFPD_SLCR_GDMA_CFG_NUM_CH_MASK          0x0000001fUL
    #define XFPD_SLCR_GDMA_CFG_NUM_CH_DEFVAL        0x8UL

/**
 * Register: XfpdSlcrGdma
 */
    #define XFPD_SLCR_GDMA                          ( ( XFPD_SLCR_BASEADDR ) +0x00003010UL )
    #define XFPD_SLCR_GDMA_RSTVAL                   0x00003b3bUL

    #define XFPD_SLCR_GDMA_RAM1_EMAB_SHIFT          12UL
    #define XFPD_SLCR_GDMA_RAM1_EMAB_WIDTH          3UL
    #define XFPD_SLCR_GDMA_RAM1_EMAB_MASK           0x00007000UL
    #define XFPD_SLCR_GDMA_RAM1_EMAB_DEFVAL         0x3UL

    #define XFPD_SLCR_GDMA_RAM1_EMASA_SHIFT         11UL
    #define XFPD_SLCR_GDMA_RAM1_EMASA_WIDTH         1UL
    #define XFPD_SLCR_GDMA_RAM1_EMASA_MASK          0x00000800UL
    #define XFPD_SLCR_GDMA_RAM1_EMASA_DEFVAL        0x1UL

    #define XFPD_SLCR_GDMA_RAM1_EMAA_SHIFT          8UL
    #define XFPD_SLCR_GDMA_RAM1_EMAA_WIDTH          3UL
    #define XFPD_SLCR_GDMA_RAM1_EMAA_MASK           0x00000700UL
    #define XFPD_SLCR_GDMA_RAM1_EMAA_DEFVAL         0x3UL

    #define XFPD_SLCR_GDMA_RAM0_EMAB_SHIFT          4UL
    #define XFPD_SLCR_GDMA_RAM0_EMAB_WIDTH          3UL
    #define XFPD_SLCR_GDMA_RAM0_EMAB_MASK           0x00000070UL
    #define XFPD_SLCR_GDMA_RAM0_EMAB_DEFVAL         0x3UL

    #define XFPD_SLCR_GDMA_RAM0_EMASA_SHIFT         3UL
    #define XFPD_SLCR_GDMA_RAM0_EMASA_WIDTH         1UL
    #define XFPD_SLCR_GDMA_RAM0_EMASA_MASK          0x00000008UL
    #define XFPD_SLCR_GDMA_RAM0_EMASA_DEFVAL        0x1UL

    #define XFPD_SLCR_GDMA_RAM0_EMAA_SHIFT          0UL
    #define XFPD_SLCR_GDMA_RAM0_EMAA_WIDTH          3UL
    #define XFPD_SLCR_GDMA_RAM0_EMAA_MASK           0x00000007UL
    #define XFPD_SLCR_GDMA_RAM0_EMAA_DEFVAL         0x3UL

/**
 * Register: XfpdSlcrAfiFs
 */
    #define XFPD_SLCR_AFI_FS                        ( ( XFPD_SLCR_BASEADDR ) +0x00005000UL )
    #define XFPD_SLCR_AFI_FS_RSTVAL                 0x00000a00UL

    #define XFPD_SLCR_AFI_FS_DW_SS1_SEL_SHIFT       10UL
    #define XFPD_SLCR_AFI_FS_DW_SS1_SEL_WIDTH       2UL
    #define XFPD_SLCR_AFI_FS_DW_SS1_SEL_MASK        0x00000c00UL
    #define XFPD_SLCR_AFI_FS_DW_SS1_SEL_DEFVAL      0x2UL

    #define XFPD_SLCR_AFI_FS_DW_SS0_SEL_SHIFT       8UL
    #define XFPD_SLCR_AFI_FS_DW_SS0_SEL_WIDTH       2UL
    #define XFPD_SLCR_AFI_FS_DW_SS0_SEL_MASK        0x00000300UL
    #define XFPD_SLCR_AFI_FS_DW_SS0_SEL_DEFVAL      0x2UL

/**
 * Register: XfpdSlcrErrAtbIsr
 */
    #define XFPD_SLCR_ERR_ATB_ISR                   ( ( XFPD_SLCR_BASEADDR ) +0x00006000UL )
    #define XFPD_SLCR_ERR_ATB_ISR_RSTVAL            0x00000000UL

    #define XFPD_SLCR_ERR_ATB_ISR_AFIFS1_SHIFT      2UL
    #define XFPD_SLCR_ERR_ATB_ISR_AFIFS1_WIDTH      1UL
    #define XFPD_SLCR_ERR_ATB_ISR_AFIFS1_MASK       0x00000004UL
    #define XFPD_SLCR_ERR_ATB_ISR_AFIFS1_DEFVAL     0x0UL

    #define XFPD_SLCR_ERR_ATB_ISR_AFIFS0_SHIFT      1UL
    #define XFPD_SLCR_ERR_ATB_ISR_AFIFS0_WIDTH      1UL
    #define XFPD_SLCR_ERR_ATB_ISR_AFIFS0_MASK       0x00000002UL
    #define XFPD_SLCR_ERR_ATB_ISR_AFIFS0_DEFVAL     0x0UL

    #define XFPD_SLCR_ERR_ATB_ISR_FPDS_SHIFT        0UL
    #define XFPD_SLCR_ERR_ATB_ISR_FPDS_WIDTH        1UL
    #define XFPD_SLCR_ERR_ATB_ISR_FPDS_MASK         0x00000001UL
    #define XFPD_SLCR_ERR_ATB_ISR_FPDS_DEFVAL       0x0UL

/**
 * Register: XfpdSlcrErrAtbImr
 */
    #define XFPD_SLCR_ERR_ATB_IMR                   ( ( XFPD_SLCR_BASEADDR ) +0x00006004UL )
    #define XFPD_SLCR_ERR_ATB_IMR_RSTVAL            0x00000007UL

    #define XFPD_SLCR_ERR_ATB_IMR_AFIFS1_SHIFT      2UL
    #define XFPD_SLCR_ERR_ATB_IMR_AFIFS1_WIDTH      1UL
    #define XFPD_SLCR_ERR_ATB_IMR_AFIFS1_MASK       0x00000004UL
    #define XFPD_SLCR_ERR_ATB_IMR_AFIFS1_DEFVAL     0x1UL

    #define XFPD_SLCR_ERR_ATB_IMR_AFIFS0_SHIFT      1UL
    #define XFPD_SLCR_ERR_ATB_IMR_AFIFS0_WIDTH      1UL
    #define XFPD_SLCR_ERR_ATB_IMR_AFIFS0_MASK       0x00000002UL
    #define XFPD_SLCR_ERR_ATB_IMR_AFIFS0_DEFVAL     0x1UL

    #define XFPD_SLCR_ERR_ATB_IMR_FPDS_SHIFT        0UL
    #define XFPD_SLCR_ERR_ATB_IMR_FPDS_WIDTH        1UL
    #define XFPD_SLCR_ERR_ATB_IMR_FPDS_MASK         0x00000001UL
    #define XFPD_SLCR_ERR_ATB_IMR_FPDS_DEFVAL       0x1UL

/**
 * Register: XfpdSlcrErrAtbIer
 */
    #define XFPD_SLCR_ERR_ATB_IER                   ( ( XFPD_SLCR_BASEADDR ) +0x00006008UL )
    #define XFPD_SLCR_ERR_ATB_IER_RSTVAL            0x00000000UL

    #define XFPD_SLCR_ERR_ATB_IER_AFIFS1_SHIFT      2UL
    #define XFPD_SLCR_ERR_ATB_IER_AFIFS1_WIDTH      1UL
    #define XFPD_SLCR_ERR_ATB_IER_AFIFS1_MASK       0x00000004UL
    #define XFPD_SLCR_ERR_ATB_IER_AFIFS1_DEFVAL     0x0UL

    #define XFPD_SLCR_ERR_ATB_IER_AFIFS0_SHIFT      1UL
    #define XFPD_SLCR_ERR_ATB_IER_AFIFS0_WIDTH      1UL
    #define XFPD_SLCR_ERR_ATB_IER_AFIFS0_MASK       0x00000002UL
    #define XFPD_SLCR_ERR_ATB_IER_AFIFS0_DEFVAL     0x0UL

    #define XFPD_SLCR_ERR_ATB_IER_FPDS_SHIFT        0UL
    #define XFPD_SLCR_ERR_ATB_IER_FPDS_WIDTH        1UL
    #define XFPD_SLCR_ERR_ATB_IER_FPDS_MASK         0x00000001UL
    #define XFPD_SLCR_ERR_ATB_IER_FPDS_DEFVAL       0x0UL

/**
 * Register: XfpdSlcrErrAtbIdr
 */
    #define XFPD_SLCR_ERR_ATB_IDR                   ( ( XFPD_SLCR_BASEADDR ) +0x0000600CUL )
    #define XFPD_SLCR_ERR_ATB_IDR_RSTVAL            0x00000000UL

    #define XFPD_SLCR_ERR_ATB_IDR_AFIFS1_SHIFT      2UL
    #define XFPD_SLCR_ERR_ATB_IDR_AFIFS1_WIDTH      1UL
    #define XFPD_SLCR_ERR_ATB_IDR_AFIFS1_MASK       0x00000004UL
    #define XFPD_SLCR_ERR_ATB_IDR_AFIFS1_DEFVAL     0x0UL

    #define XFPD_SLCR_ERR_ATB_IDR_AFIFS0_SHIFT      1UL
    #define XFPD_SLCR_ERR_ATB_IDR_AFIFS0_WIDTH      1UL
    #define XFPD_SLCR_ERR_ATB_IDR_AFIFS0_MASK       0x00000002UL
    #define XFPD_SLCR_ERR_ATB_IDR_AFIFS0_DEFVAL     0x0UL

    #define XFPD_SLCR_ERR_ATB_IDR_FPDS_SHIFT        0UL
    #define XFPD_SLCR_ERR_ATB_IDR_FPDS_WIDTH        1UL
    #define XFPD_SLCR_ERR_ATB_IDR_FPDS_MASK         0x00000001UL
    #define XFPD_SLCR_ERR_ATB_IDR_FPDS_DEFVAL       0x0UL

/**
 * Register: XfpdSlcrAtbCmdstore
 */
    #define XFPD_SLCR_ATB_CMDSTORE                  ( ( XFPD_SLCR_BASEADDR ) +0x00006010UL )
    #define XFPD_SLCR_ATB_CMDSTORE_RSTVAL           0x00000007UL

    #define XFPD_SLCR_ATB_CMDSTORE_AFIFS1_SHIFT     2UL
    #define XFPD_SLCR_ATB_CMDSTORE_AFIFS1_WIDTH     1UL
    #define XFPD_SLCR_ATB_CMDSTORE_AFIFS1_MASK      0x00000004UL
    #define XFPD_SLCR_ATB_CMDSTORE_AFIFS1_DEFVAL    0x1UL

    #define XFPD_SLCR_ATB_CMDSTORE_AFIFS0_SHIFT     1UL
    #define XFPD_SLCR_ATB_CMDSTORE_AFIFS0_WIDTH     1UL
    #define XFPD_SLCR_ATB_CMDSTORE_AFIFS0_MASK      0x00000002UL
    #define XFPD_SLCR_ATB_CMDSTORE_AFIFS0_DEFVAL    0x1UL

    #define XFPD_SLCR_ATB_CMDSTORE_FPDS_SHIFT       0UL
    #define XFPD_SLCR_ATB_CMDSTORE_FPDS_WIDTH       1UL
    #define XFPD_SLCR_ATB_CMDSTORE_FPDS_MASK        0x00000001UL
    #define XFPD_SLCR_ATB_CMDSTORE_FPDS_DEFVAL      0x1UL

/**
 * Register: XfpdSlcrAtbRespEn
 */
    #define XFPD_SLCR_ATB_RESP_EN                   ( ( XFPD_SLCR_BASEADDR ) +0x00006014UL )
    #define XFPD_SLCR_ATB_RESP_EN_RSTVAL            0x00000000UL

    #define XFPD_SLCR_ATB_RESP_EN_AFIFS1_SHIFT      2UL
    #define XFPD_SLCR_ATB_RESP_EN_AFIFS1_WIDTH      1UL
    #define XFPD_SLCR_ATB_RESP_EN_AFIFS1_MASK       0x00000004UL
    #define XFPD_SLCR_ATB_RESP_EN_AFIFS1_DEFVAL     0x0UL

    #define XFPD_SLCR_ATB_RESP_EN_AFIFS0_SHIFT      1UL
    #define XFPD_SLCR_ATB_RESP_EN_AFIFS0_WIDTH      1UL
    #define XFPD_SLCR_ATB_RESP_EN_AFIFS0_MASK       0x00000002UL
    #define XFPD_SLCR_ATB_RESP_EN_AFIFS0_DEFVAL     0x0UL

    #define XFPD_SLCR_ATB_RESP_EN_FPDS_SHIFT        0UL
    #define XFPD_SLCR_ATB_RESP_EN_FPDS_WIDTH        1UL
    #define XFPD_SLCR_ATB_RESP_EN_FPDS_MASK         0x00000001UL
    #define XFPD_SLCR_ATB_RESP_EN_FPDS_DEFVAL       0x0UL

/**
 * Register: XfpdSlcrAtbResptype
 */
    #define XFPD_SLCR_ATB_RESPTYPE                  ( ( XFPD_SLCR_BASEADDR ) +0x00006018UL )
    #define XFPD_SLCR_ATB_RESPTYPE_RSTVAL           0x00000007UL

    #define XFPD_SLCR_ATB_RESPTYPE_AFIFS1_SHIFT     2UL
    #define XFPD_SLCR_ATB_RESPTYPE_AFIFS1_WIDTH     1UL
    #define XFPD_SLCR_ATB_RESPTYPE_AFIFS1_MASK      0x00000004UL
    #define XFPD_SLCR_ATB_RESPTYPE_AFIFS1_DEFVAL    0x1UL

    #define XFPD_SLCR_ATB_RESPTYPE_AFIFS0_SHIFT     1UL
    #define XFPD_SLCR_ATB_RESPTYPE_AFIFS0_WIDTH     1UL
    #define XFPD_SLCR_ATB_RESPTYPE_AFIFS0_MASK      0x00000002UL
    #define XFPD_SLCR_ATB_RESPTYPE_AFIFS0_DEFVAL    0x1UL

    #define XFPD_SLCR_ATB_RESPTYPE_FPDS_SHIFT       0UL
    #define XFPD_SLCR_ATB_RESPTYPE_FPDS_WIDTH       1UL
    #define XFPD_SLCR_ATB_RESPTYPE_FPDS_MASK        0x00000001UL
    #define XFPD_SLCR_ATB_RESPTYPE_FPDS_DEFVAL      0x1UL

/**
 * Register: XfpdSlcrAtbPrescale
 */
    #define XFPD_SLCR_ATB_PRESCALE                  ( ( XFPD_SLCR_BASEADDR ) +0x00006020UL )
    #define XFPD_SLCR_ATB_PRESCALE_RSTVAL           0x0000ffffUL

    #define XFPD_SLCR_ATB_PRESCALE_EN_SHIFT         16UL
    #define XFPD_SLCR_ATB_PRESCALE_EN_WIDTH         1UL
    #define XFPD_SLCR_ATB_PRESCALE_EN_MASK          0x00010000UL
    #define XFPD_SLCR_ATB_PRESCALE_EN_DEFVAL        0x0UL

    #define XFPD_SLCR_ATB_PRESCALE_VAL_SHIFT        0UL
    #define XFPD_SLCR_ATB_PRESCALE_VAL_WIDTH        16UL
    #define XFPD_SLCR_ATB_PRESCALE_VAL_MASK         0x0000ffffUL
    #define XFPD_SLCR_ATB_PRESCALE_VAL_DEFVAL       0xffffUL


    #ifdef __cplusplus
}
    #endif

#endif /* __XFPD_SLCR_H__ */
