/* ### HEADER ### */

#ifndef __XOCM_XMPU_CFG_H__
    #define __XOCM_XMPU_CFG_H__


    #ifdef __cplusplus
    extern "C" {
    #endif

/**
 * XocmXmpuCfg Base Address
 */
    #define XOCM_XMPU_CFG_BASEADDR                    0xFFA70000UL

/**
 * Register: XocmXmpuCfgCtrl
 */
    #define XOCM_XMPU_CFG_CTRL                        ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000000UL )
    #define XOCM_XMPU_CFG_CTRL_RSTVAL                 0x00000003UL

    #define XOCM_XMPU_CFG_CTRL_ALIGNCFG_SHIFT         3UL
    #define XOCM_XMPU_CFG_CTRL_ALIGNCFG_WIDTH         1UL
    #define XOCM_XMPU_CFG_CTRL_ALIGNCFG_MASK          0x00000008UL
    #define XOCM_XMPU_CFG_CTRL_ALIGNCFG_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_CTRL_POISONCFG_SHIFT        2UL
    #define XOCM_XMPU_CFG_CTRL_POISONCFG_WIDTH        1UL
    #define XOCM_XMPU_CFG_CTRL_POISONCFG_MASK         0x00000004UL
    #define XOCM_XMPU_CFG_CTRL_POISONCFG_DEFVAL       0x0UL

    #define XOCM_XMPU_CFG_CTRL_DEFWRALWD_SHIFT        1UL
    #define XOCM_XMPU_CFG_CTRL_DEFWRALWD_WIDTH        1UL
    #define XOCM_XMPU_CFG_CTRL_DEFWRALWD_MASK         0x00000002UL
    #define XOCM_XMPU_CFG_CTRL_DEFWRALWD_DEFVAL       0x1UL

    #define XOCM_XMPU_CFG_CTRL_DEFRDALWD_SHIFT        0UL
    #define XOCM_XMPU_CFG_CTRL_DEFRDALWD_WIDTH        1UL
    #define XOCM_XMPU_CFG_CTRL_DEFRDALWD_MASK         0x00000001UL
    #define XOCM_XMPU_CFG_CTRL_DEFRDALWD_DEFVAL       0x1UL

/**
 * Register: XocmXmpuCfgErrSts1
 */
    #define XOCM_XMPU_CFG_ERR_STS1                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000004UL )
    #define XOCM_XMPU_CFG_ERR_STS1_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_ERR_STS1_AXI_ADDR_SHIFT     0UL
    #define XOCM_XMPU_CFG_ERR_STS1_AXI_ADDR_WIDTH     32UL
    #define XOCM_XMPU_CFG_ERR_STS1_AXI_ADDR_MASK      0xffffffffUL
    #define XOCM_XMPU_CFG_ERR_STS1_AXI_ADDR_DEFVAL    0x0UL

/**
 * Register: XocmXmpuCfgErrSts2
 */
    #define XOCM_XMPU_CFG_ERR_STS2                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000008UL )
    #define XOCM_XMPU_CFG_ERR_STS2_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_ERR_STS2_AXI_ID_SHIFT       0UL
    #define XOCM_XMPU_CFG_ERR_STS2_AXI_ID_WIDTH       16UL
    #define XOCM_XMPU_CFG_ERR_STS2_AXI_ID_MASK        0x0000ffffUL
    #define XOCM_XMPU_CFG_ERR_STS2_AXI_ID_DEFVAL      0x0UL

/**
 * Register: XocmXmpuCfgPoison
 */
    #define XOCM_XMPU_CFG_POISON                      ( ( XOCM_XMPU_CFG_BASEADDR ) +0x0000000CUL )
    #define XOCM_XMPU_CFG_POISON_RSTVAL               0x00000000UL

    #define XOCM_XMPU_CFG_POISON_ATTRIB_SHIFT         20UL
    #define XOCM_XMPU_CFG_POISON_ATTRIB_WIDTH         12UL
    #define XOCM_XMPU_CFG_POISON_ATTRIB_MASK          0xfff00000UL
    #define XOCM_XMPU_CFG_POISON_ATTRIB_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_POISON_BASE_SHIFT           0UL
    #define XOCM_XMPU_CFG_POISON_BASE_WIDTH           20UL
    #define XOCM_XMPU_CFG_POISON_BASE_MASK            0x000fffffUL
    #define XOCM_XMPU_CFG_POISON_BASE_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgIsr
 */
    #define XOCM_XMPU_CFG_ISR                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000010UL )
    #define XOCM_XMPU_CFG_ISR_RSTVAL                  0x00000000UL

    #define XOCM_XMPU_CFG_ISR_SECURTYVIO_SHIFT        3UL
    #define XOCM_XMPU_CFG_ISR_SECURTYVIO_WIDTH        1UL
    #define XOCM_XMPU_CFG_ISR_SECURTYVIO_MASK         0x00000008UL
    #define XOCM_XMPU_CFG_ISR_SECURTYVIO_DEFVAL       0x0UL

    #define XOCM_XMPU_CFG_ISR_WRPERMVIO_SHIFT         2UL
    #define XOCM_XMPU_CFG_ISR_WRPERMVIO_WIDTH         1UL
    #define XOCM_XMPU_CFG_ISR_WRPERMVIO_MASK          0x00000004UL
    #define XOCM_XMPU_CFG_ISR_WRPERMVIO_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_ISR_RDPERMVIO_SHIFT         1UL
    #define XOCM_XMPU_CFG_ISR_RDPERMVIO_WIDTH         1UL
    #define XOCM_XMPU_CFG_ISR_RDPERMVIO_MASK          0x00000002UL
    #define XOCM_XMPU_CFG_ISR_RDPERMVIO_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_ISR_INV_APB_SHIFT           0UL
    #define XOCM_XMPU_CFG_ISR_INV_APB_WIDTH           1UL
    #define XOCM_XMPU_CFG_ISR_INV_APB_MASK            0x00000001UL
    #define XOCM_XMPU_CFG_ISR_INV_APB_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgImr
 */
    #define XOCM_XMPU_CFG_IMR                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000014UL )
    #define XOCM_XMPU_CFG_IMR_RSTVAL                  0x0000000fUL

    #define XOCM_XMPU_CFG_IMR_SECURTYVIO_SHIFT        3UL
    #define XOCM_XMPU_CFG_IMR_SECURTYVIO_WIDTH        1UL
    #define XOCM_XMPU_CFG_IMR_SECURTYVIO_MASK         0x00000008UL
    #define XOCM_XMPU_CFG_IMR_SECURTYVIO_DEFVAL       0x1UL

    #define XOCM_XMPU_CFG_IMR_WRPERMVIO_SHIFT         2UL
    #define XOCM_XMPU_CFG_IMR_WRPERMVIO_WIDTH         1UL
    #define XOCM_XMPU_CFG_IMR_WRPERMVIO_MASK          0x00000004UL
    #define XOCM_XMPU_CFG_IMR_WRPERMVIO_DEFVAL        0x1UL

    #define XOCM_XMPU_CFG_IMR_RDPERMVIO_SHIFT         1UL
    #define XOCM_XMPU_CFG_IMR_RDPERMVIO_WIDTH         1UL
    #define XOCM_XMPU_CFG_IMR_RDPERMVIO_MASK          0x00000002UL
    #define XOCM_XMPU_CFG_IMR_RDPERMVIO_DEFVAL        0x1UL

    #define XOCM_XMPU_CFG_IMR_INV_APB_SHIFT           0UL
    #define XOCM_XMPU_CFG_IMR_INV_APB_WIDTH           1UL
    #define XOCM_XMPU_CFG_IMR_INV_APB_MASK            0x00000001UL
    #define XOCM_XMPU_CFG_IMR_INV_APB_DEFVAL          0x1UL

/**
 * Register: XocmXmpuCfgIen
 */
    #define XOCM_XMPU_CFG_IEN                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000018UL )
    #define XOCM_XMPU_CFG_IEN_RSTVAL                  0x00000000UL

    #define XOCM_XMPU_CFG_IEN_SECURTYVIO_SHIFT        3UL
    #define XOCM_XMPU_CFG_IEN_SECURTYVIO_WIDTH        1UL
    #define XOCM_XMPU_CFG_IEN_SECURTYVIO_MASK         0x00000008UL
    #define XOCM_XMPU_CFG_IEN_SECURTYVIO_DEFVAL       0x0UL

    #define XOCM_XMPU_CFG_IEN_WRPERMVIO_SHIFT         2UL
    #define XOCM_XMPU_CFG_IEN_WRPERMVIO_WIDTH         1UL
    #define XOCM_XMPU_CFG_IEN_WRPERMVIO_MASK          0x00000004UL
    #define XOCM_XMPU_CFG_IEN_WRPERMVIO_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_IEN_RDPERMVIO_SHIFT         1UL
    #define XOCM_XMPU_CFG_IEN_RDPERMVIO_WIDTH         1UL
    #define XOCM_XMPU_CFG_IEN_RDPERMVIO_MASK          0x00000002UL
    #define XOCM_XMPU_CFG_IEN_RDPERMVIO_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_IEN_INV_APB_SHIFT           0UL
    #define XOCM_XMPU_CFG_IEN_INV_APB_WIDTH           1UL
    #define XOCM_XMPU_CFG_IEN_INV_APB_MASK            0x00000001UL
    #define XOCM_XMPU_CFG_IEN_INV_APB_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgIds
 */
    #define XOCM_XMPU_CFG_IDS                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x0000001CUL )
    #define XOCM_XMPU_CFG_IDS_RSTVAL                  0x00000000UL

    #define XOCM_XMPU_CFG_IDS_SECURTYVIO_SHIFT        3UL
    #define XOCM_XMPU_CFG_IDS_SECURTYVIO_WIDTH        1UL
    #define XOCM_XMPU_CFG_IDS_SECURTYVIO_MASK         0x00000008UL
    #define XOCM_XMPU_CFG_IDS_SECURTYVIO_DEFVAL       0x0UL

    #define XOCM_XMPU_CFG_IDS_WRPERMVIO_SHIFT         2UL
    #define XOCM_XMPU_CFG_IDS_WRPERMVIO_WIDTH         1UL
    #define XOCM_XMPU_CFG_IDS_WRPERMVIO_MASK          0x00000004UL
    #define XOCM_XMPU_CFG_IDS_WRPERMVIO_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_IDS_RDPERMVIO_SHIFT         1UL
    #define XOCM_XMPU_CFG_IDS_RDPERMVIO_WIDTH         1UL
    #define XOCM_XMPU_CFG_IDS_RDPERMVIO_MASK          0x00000002UL
    #define XOCM_XMPU_CFG_IDS_RDPERMVIO_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_IDS_INV_APB_SHIFT           0UL
    #define XOCM_XMPU_CFG_IDS_INV_APB_WIDTH           1UL
    #define XOCM_XMPU_CFG_IDS_INV_APB_MASK            0x00000001UL
    #define XOCM_XMPU_CFG_IDS_INV_APB_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgLock
 */
    #define XOCM_XMPU_CFG_LOCK                        ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000020UL )
    #define XOCM_XMPU_CFG_LOCK_RSTVAL                 0x00000000UL

    #define XOCM_XMPU_CFG_LOCK_REGWRDIS_SHIFT         0UL
    #define XOCM_XMPU_CFG_LOCK_REGWRDIS_WIDTH         1UL
    #define XOCM_XMPU_CFG_LOCK_REGWRDIS_MASK          0x00000001UL
    #define XOCM_XMPU_CFG_LOCK_REGWRDIS_DEFVAL        0x0UL

/**
 * Register: XocmXmpuCfgR00Strt
 */
    #define XOCM_XMPU_CFG_R00_STRT                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000100UL )
    #define XOCM_XMPU_CFG_R00_STRT_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R00_STRT_ADDR_SHIFT         0UL
    #define XOCM_XMPU_CFG_R00_STRT_ADDR_WIDTH         28UL
    #define XOCM_XMPU_CFG_R00_STRT_ADDR_MASK          0x0fffffffUL
    #define XOCM_XMPU_CFG_R00_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XocmXmpuCfgR00End
 */
    #define XOCM_XMPU_CFG_R00_END                     ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000104UL )
    #define XOCM_XMPU_CFG_R00_END_RSTVAL              0x00000000UL

    #define XOCM_XMPU_CFG_R00_END_ADDR_SHIFT          0UL
    #define XOCM_XMPU_CFG_R00_END_ADDR_WIDTH          28UL
    #define XOCM_XMPU_CFG_R00_END_ADDR_MASK           0x0fffffffUL
    #define XOCM_XMPU_CFG_R00_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XocmXmpuCfgR00Mstr
 */
    #define XOCM_XMPU_CFG_R00_MSTR                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000108UL )
    #define XOCM_XMPU_CFG_R00_MSTR_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R00_MSTR_MSK_SHIFT          16UL
    #define XOCM_XMPU_CFG_R00_MSTR_MSK_WIDTH          16UL
    #define XOCM_XMPU_CFG_R00_MSTR_MSK_MASK           0xffff0000UL
    #define XOCM_XMPU_CFG_R00_MSTR_MSK_DEFVAL         0x0UL

    #define XOCM_XMPU_CFG_R00_MSTR_ID_SHIFT           0UL
    #define XOCM_XMPU_CFG_R00_MSTR_ID_WIDTH           16UL
    #define XOCM_XMPU_CFG_R00_MSTR_ID_MASK            0x0000ffffUL
    #define XOCM_XMPU_CFG_R00_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgR00
 */
    #define XOCM_XMPU_CFG_R00                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x0000010CUL )
    #define XOCM_XMPU_CFG_R00_RSTVAL                  0x00000008UL

    #define XOCM_XMPU_CFG_R00_NSCHKTYPE_SHIFT         4UL
    #define XOCM_XMPU_CFG_R00_NSCHKTYPE_WIDTH         1UL
    #define XOCM_XMPU_CFG_R00_NSCHKTYPE_MASK          0x00000010UL
    #define XOCM_XMPU_CFG_R00_NSCHKTYPE_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_R00_REGNNS_SHIFT            3UL
    #define XOCM_XMPU_CFG_R00_REGNNS_WIDTH            1UL
    #define XOCM_XMPU_CFG_R00_REGNNS_MASK             0x00000008UL
    #define XOCM_XMPU_CFG_R00_REGNNS_DEFVAL           0x1UL

    #define XOCM_XMPU_CFG_R00_WRALWD_SHIFT            2UL
    #define XOCM_XMPU_CFG_R00_WRALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R00_WRALWD_MASK             0x00000004UL
    #define XOCM_XMPU_CFG_R00_WRALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R00_RDALWD_SHIFT            1UL
    #define XOCM_XMPU_CFG_R00_RDALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R00_RDALWD_MASK             0x00000002UL
    #define XOCM_XMPU_CFG_R00_RDALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R00_EN_SHIFT                0UL
    #define XOCM_XMPU_CFG_R00_EN_WIDTH                1UL
    #define XOCM_XMPU_CFG_R00_EN_MASK                 0x00000001UL
    #define XOCM_XMPU_CFG_R00_EN_DEFVAL               0x0UL

/**
 * Register: XocmXmpuCfgR01Strt
 */
    #define XOCM_XMPU_CFG_R01_STRT                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000110UL )
    #define XOCM_XMPU_CFG_R01_STRT_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R01_STRT_ADDR_SHIFT         0UL
    #define XOCM_XMPU_CFG_R01_STRT_ADDR_WIDTH         28UL
    #define XOCM_XMPU_CFG_R01_STRT_ADDR_MASK          0x0fffffffUL
    #define XOCM_XMPU_CFG_R01_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XocmXmpuCfgR01End
 */
    #define XOCM_XMPU_CFG_R01_END                     ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000114UL )
    #define XOCM_XMPU_CFG_R01_END_RSTVAL              0x00000000UL

    #define XOCM_XMPU_CFG_R01_END_ADDR_SHIFT          0UL
    #define XOCM_XMPU_CFG_R01_END_ADDR_WIDTH          28UL
    #define XOCM_XMPU_CFG_R01_END_ADDR_MASK           0x0fffffffUL
    #define XOCM_XMPU_CFG_R01_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XocmXmpuCfgR01Mstr
 */
    #define XOCM_XMPU_CFG_R01_MSTR                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000118UL )
    #define XOCM_XMPU_CFG_R01_MSTR_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R01_MSTR_MSK_SHIFT          16UL
    #define XOCM_XMPU_CFG_R01_MSTR_MSK_WIDTH          16UL
    #define XOCM_XMPU_CFG_R01_MSTR_MSK_MASK           0xffff0000UL
    #define XOCM_XMPU_CFG_R01_MSTR_MSK_DEFVAL         0x0UL

    #define XOCM_XMPU_CFG_R01_MSTR_ID_SHIFT           0UL
    #define XOCM_XMPU_CFG_R01_MSTR_ID_WIDTH           16UL
    #define XOCM_XMPU_CFG_R01_MSTR_ID_MASK            0x0000ffffUL
    #define XOCM_XMPU_CFG_R01_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgR01
 */
    #define XOCM_XMPU_CFG_R01                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x0000011CUL )
    #define XOCM_XMPU_CFG_R01_RSTVAL                  0x00000008UL

    #define XOCM_XMPU_CFG_R01_NSCHKTYPE_SHIFT         4UL
    #define XOCM_XMPU_CFG_R01_NSCHKTYPE_WIDTH         1UL
    #define XOCM_XMPU_CFG_R01_NSCHKTYPE_MASK          0x00000010UL
    #define XOCM_XMPU_CFG_R01_NSCHKTYPE_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_R01_REGNNS_SHIFT            3UL
    #define XOCM_XMPU_CFG_R01_REGNNS_WIDTH            1UL
    #define XOCM_XMPU_CFG_R01_REGNNS_MASK             0x00000008UL
    #define XOCM_XMPU_CFG_R01_REGNNS_DEFVAL           0x1UL

    #define XOCM_XMPU_CFG_R01_WRALWD_SHIFT            2UL
    #define XOCM_XMPU_CFG_R01_WRALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R01_WRALWD_MASK             0x00000004UL
    #define XOCM_XMPU_CFG_R01_WRALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R01_RDALWD_SHIFT            1UL
    #define XOCM_XMPU_CFG_R01_RDALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R01_RDALWD_MASK             0x00000002UL
    #define XOCM_XMPU_CFG_R01_RDALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R01_EN_SHIFT                0UL
    #define XOCM_XMPU_CFG_R01_EN_WIDTH                1UL
    #define XOCM_XMPU_CFG_R01_EN_MASK                 0x00000001UL
    #define XOCM_XMPU_CFG_R01_EN_DEFVAL               0x0UL

/**
 * Register: XocmXmpuCfgR02Strt
 */
    #define XOCM_XMPU_CFG_R02_STRT                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000120UL )
    #define XOCM_XMPU_CFG_R02_STRT_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R02_STRT_ADDR_SHIFT         0UL
    #define XOCM_XMPU_CFG_R02_STRT_ADDR_WIDTH         28UL
    #define XOCM_XMPU_CFG_R02_STRT_ADDR_MASK          0x0fffffffUL
    #define XOCM_XMPU_CFG_R02_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XocmXmpuCfgR02End
 */
    #define XOCM_XMPU_CFG_R02_END                     ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000124UL )
    #define XOCM_XMPU_CFG_R02_END_RSTVAL              0x00000000UL

    #define XOCM_XMPU_CFG_R02_END_ADDR_SHIFT          0UL
    #define XOCM_XMPU_CFG_R02_END_ADDR_WIDTH          28UL
    #define XOCM_XMPU_CFG_R02_END_ADDR_MASK           0x0fffffffUL
    #define XOCM_XMPU_CFG_R02_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XocmXmpuCfgR02Mstr
 */
    #define XOCM_XMPU_CFG_R02_MSTR                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000128UL )
    #define XOCM_XMPU_CFG_R02_MSTR_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R02_MSTR_MSK_SHIFT          16UL
    #define XOCM_XMPU_CFG_R02_MSTR_MSK_WIDTH          16UL
    #define XOCM_XMPU_CFG_R02_MSTR_MSK_MASK           0xffff0000UL
    #define XOCM_XMPU_CFG_R02_MSTR_MSK_DEFVAL         0x0UL

    #define XOCM_XMPU_CFG_R02_MSTR_ID_SHIFT           0UL
    #define XOCM_XMPU_CFG_R02_MSTR_ID_WIDTH           16UL
    #define XOCM_XMPU_CFG_R02_MSTR_ID_MASK            0x0000ffffUL
    #define XOCM_XMPU_CFG_R02_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgR02
 */
    #define XOCM_XMPU_CFG_R02                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x0000012CUL )
    #define XOCM_XMPU_CFG_R02_RSTVAL                  0x00000008UL

    #define XOCM_XMPU_CFG_R02_NSCHKTYPE_SHIFT         4UL
    #define XOCM_XMPU_CFG_R02_NSCHKTYPE_WIDTH         1UL
    #define XOCM_XMPU_CFG_R02_NSCHKTYPE_MASK          0x00000010UL
    #define XOCM_XMPU_CFG_R02_NSCHKTYPE_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_R02_REGNNS_SHIFT            3UL
    #define XOCM_XMPU_CFG_R02_REGNNS_WIDTH            1UL
    #define XOCM_XMPU_CFG_R02_REGNNS_MASK             0x00000008UL
    #define XOCM_XMPU_CFG_R02_REGNNS_DEFVAL           0x1UL

    #define XOCM_XMPU_CFG_R02_WRALWD_SHIFT            2UL
    #define XOCM_XMPU_CFG_R02_WRALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R02_WRALWD_MASK             0x00000004UL
    #define XOCM_XMPU_CFG_R02_WRALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R02_RDALWD_SHIFT            1UL
    #define XOCM_XMPU_CFG_R02_RDALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R02_RDALWD_MASK             0x00000002UL
    #define XOCM_XMPU_CFG_R02_RDALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R02_EN_SHIFT                0UL
    #define XOCM_XMPU_CFG_R02_EN_WIDTH                1UL
    #define XOCM_XMPU_CFG_R02_EN_MASK                 0x00000001UL
    #define XOCM_XMPU_CFG_R02_EN_DEFVAL               0x0UL

/**
 * Register: XocmXmpuCfgR03Strt
 */
    #define XOCM_XMPU_CFG_R03_STRT                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000130UL )
    #define XOCM_XMPU_CFG_R03_STRT_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R03_STRT_ADDR_SHIFT         0UL
    #define XOCM_XMPU_CFG_R03_STRT_ADDR_WIDTH         28UL
    #define XOCM_XMPU_CFG_R03_STRT_ADDR_MASK          0x0fffffffUL
    #define XOCM_XMPU_CFG_R03_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XocmXmpuCfgR03End
 */
    #define XOCM_XMPU_CFG_R03_END                     ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000134UL )
    #define XOCM_XMPU_CFG_R03_END_RSTVAL              0x00000000UL

    #define XOCM_XMPU_CFG_R03_END_ADDR_SHIFT          0UL
    #define XOCM_XMPU_CFG_R03_END_ADDR_WIDTH          28UL
    #define XOCM_XMPU_CFG_R03_END_ADDR_MASK           0x0fffffffUL
    #define XOCM_XMPU_CFG_R03_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XocmXmpuCfgR03Mstr
 */
    #define XOCM_XMPU_CFG_R03_MSTR                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000138UL )
    #define XOCM_XMPU_CFG_R03_MSTR_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R03_MSTR_MSK_SHIFT          16UL
    #define XOCM_XMPU_CFG_R03_MSTR_MSK_WIDTH          16UL
    #define XOCM_XMPU_CFG_R03_MSTR_MSK_MASK           0xffff0000UL
    #define XOCM_XMPU_CFG_R03_MSTR_MSK_DEFVAL         0x0UL

    #define XOCM_XMPU_CFG_R03_MSTR_ID_SHIFT           0UL
    #define XOCM_XMPU_CFG_R03_MSTR_ID_WIDTH           16UL
    #define XOCM_XMPU_CFG_R03_MSTR_ID_MASK            0x0000ffffUL
    #define XOCM_XMPU_CFG_R03_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgR03
 */
    #define XOCM_XMPU_CFG_R03                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x0000013CUL )
    #define XOCM_XMPU_CFG_R03_RSTVAL                  0x00000008UL

    #define XOCM_XMPU_CFG_R03_NSCHKTYPE_SHIFT         4UL
    #define XOCM_XMPU_CFG_R03_NSCHKTYPE_WIDTH         1UL
    #define XOCM_XMPU_CFG_R03_NSCHKTYPE_MASK          0x00000010UL
    #define XOCM_XMPU_CFG_R03_NSCHKTYPE_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_R03_REGNNS_SHIFT            3UL
    #define XOCM_XMPU_CFG_R03_REGNNS_WIDTH            1UL
    #define XOCM_XMPU_CFG_R03_REGNNS_MASK             0x00000008UL
    #define XOCM_XMPU_CFG_R03_REGNNS_DEFVAL           0x1UL

    #define XOCM_XMPU_CFG_R03_WRALWD_SHIFT            2UL
    #define XOCM_XMPU_CFG_R03_WRALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R03_WRALWD_MASK             0x00000004UL
    #define XOCM_XMPU_CFG_R03_WRALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R03_RDALWD_SHIFT            1UL
    #define XOCM_XMPU_CFG_R03_RDALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R03_RDALWD_MASK             0x00000002UL
    #define XOCM_XMPU_CFG_R03_RDALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R03_EN_SHIFT                0UL
    #define XOCM_XMPU_CFG_R03_EN_WIDTH                1UL
    #define XOCM_XMPU_CFG_R03_EN_MASK                 0x00000001UL
    #define XOCM_XMPU_CFG_R03_EN_DEFVAL               0x0UL

/**
 * Register: XocmXmpuCfgR04Strt
 */
    #define XOCM_XMPU_CFG_R04_STRT                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000140UL )
    #define XOCM_XMPU_CFG_R04_STRT_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R04_STRT_ADDR_SHIFT         0UL
    #define XOCM_XMPU_CFG_R04_STRT_ADDR_WIDTH         28UL
    #define XOCM_XMPU_CFG_R04_STRT_ADDR_MASK          0x0fffffffUL
    #define XOCM_XMPU_CFG_R04_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XocmXmpuCfgR04End
 */
    #define XOCM_XMPU_CFG_R04_END                     ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000144UL )
    #define XOCM_XMPU_CFG_R04_END_RSTVAL              0x00000000UL

    #define XOCM_XMPU_CFG_R04_END_ADDR_SHIFT          0UL
    #define XOCM_XMPU_CFG_R04_END_ADDR_WIDTH          28UL
    #define XOCM_XMPU_CFG_R04_END_ADDR_MASK           0x0fffffffUL
    #define XOCM_XMPU_CFG_R04_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XocmXmpuCfgR04Mstr
 */
    #define XOCM_XMPU_CFG_R04_MSTR                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000148UL )
    #define XOCM_XMPU_CFG_R04_MSTR_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R04_MSTR_MSK_SHIFT          16UL
    #define XOCM_XMPU_CFG_R04_MSTR_MSK_WIDTH          16UL
    #define XOCM_XMPU_CFG_R04_MSTR_MSK_MASK           0xffff0000UL
    #define XOCM_XMPU_CFG_R04_MSTR_MSK_DEFVAL         0x0UL

    #define XOCM_XMPU_CFG_R04_MSTR_ID_SHIFT           0UL
    #define XOCM_XMPU_CFG_R04_MSTR_ID_WIDTH           16UL
    #define XOCM_XMPU_CFG_R04_MSTR_ID_MASK            0x0000ffffUL
    #define XOCM_XMPU_CFG_R04_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgR04
 */
    #define XOCM_XMPU_CFG_R04                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x0000014CUL )
    #define XOCM_XMPU_CFG_R04_RSTVAL                  0x00000008UL

    #define XOCM_XMPU_CFG_R04_NSCHKTYPE_SHIFT         4UL
    #define XOCM_XMPU_CFG_R04_NSCHKTYPE_WIDTH         1UL
    #define XOCM_XMPU_CFG_R04_NSCHKTYPE_MASK          0x00000010UL
    #define XOCM_XMPU_CFG_R04_NSCHKTYPE_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_R04_REGNNS_SHIFT            3UL
    #define XOCM_XMPU_CFG_R04_REGNNS_WIDTH            1UL
    #define XOCM_XMPU_CFG_R04_REGNNS_MASK             0x00000008UL
    #define XOCM_XMPU_CFG_R04_REGNNS_DEFVAL           0x1UL

    #define XOCM_XMPU_CFG_R04_WRALWD_SHIFT            2UL
    #define XOCM_XMPU_CFG_R04_WRALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R04_WRALWD_MASK             0x00000004UL
    #define XOCM_XMPU_CFG_R04_WRALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R04_RDALWD_SHIFT            1UL
    #define XOCM_XMPU_CFG_R04_RDALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R04_RDALWD_MASK             0x00000002UL
    #define XOCM_XMPU_CFG_R04_RDALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R04_EN_SHIFT                0UL
    #define XOCM_XMPU_CFG_R04_EN_WIDTH                1UL
    #define XOCM_XMPU_CFG_R04_EN_MASK                 0x00000001UL
    #define XOCM_XMPU_CFG_R04_EN_DEFVAL               0x0UL

/**
 * Register: XocmXmpuCfgR05Strt
 */
    #define XOCM_XMPU_CFG_R05_STRT                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000150UL )
    #define XOCM_XMPU_CFG_R05_STRT_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R05_STRT_ADDR_SHIFT         0UL
    #define XOCM_XMPU_CFG_R05_STRT_ADDR_WIDTH         28UL
    #define XOCM_XMPU_CFG_R05_STRT_ADDR_MASK          0x0fffffffUL
    #define XOCM_XMPU_CFG_R05_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XocmXmpuCfgR05End
 */
    #define XOCM_XMPU_CFG_R05_END                     ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000154UL )
    #define XOCM_XMPU_CFG_R05_END_RSTVAL              0x00000000UL

    #define XOCM_XMPU_CFG_R05_END_ADDR_SHIFT          0UL
    #define XOCM_XMPU_CFG_R05_END_ADDR_WIDTH          28UL
    #define XOCM_XMPU_CFG_R05_END_ADDR_MASK           0x0fffffffUL
    #define XOCM_XMPU_CFG_R05_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XocmXmpuCfgR05Mstr
 */
    #define XOCM_XMPU_CFG_R05_MSTR                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000158UL )
    #define XOCM_XMPU_CFG_R05_MSTR_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R05_MSTR_MSK_SHIFT          16UL
    #define XOCM_XMPU_CFG_R05_MSTR_MSK_WIDTH          16UL
    #define XOCM_XMPU_CFG_R05_MSTR_MSK_MASK           0xffff0000UL
    #define XOCM_XMPU_CFG_R05_MSTR_MSK_DEFVAL         0x0UL

    #define XOCM_XMPU_CFG_R05_MSTR_ID_SHIFT           0UL
    #define XOCM_XMPU_CFG_R05_MSTR_ID_WIDTH           16UL
    #define XOCM_XMPU_CFG_R05_MSTR_ID_MASK            0x0000ffffUL
    #define XOCM_XMPU_CFG_R05_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgR05
 */
    #define XOCM_XMPU_CFG_R05                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x0000015CUL )
    #define XOCM_XMPU_CFG_R05_RSTVAL                  0x00000008UL

    #define XOCM_XMPU_CFG_R05_NSCHKTYPE_SHIFT         4UL
    #define XOCM_XMPU_CFG_R05_NSCHKTYPE_WIDTH         1UL
    #define XOCM_XMPU_CFG_R05_NSCHKTYPE_MASK          0x00000010UL
    #define XOCM_XMPU_CFG_R05_NSCHKTYPE_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_R05_REGNNS_SHIFT            3UL
    #define XOCM_XMPU_CFG_R05_REGNNS_WIDTH            1UL
    #define XOCM_XMPU_CFG_R05_REGNNS_MASK             0x00000008UL
    #define XOCM_XMPU_CFG_R05_REGNNS_DEFVAL           0x1UL

    #define XOCM_XMPU_CFG_R05_WRALWD_SHIFT            2UL
    #define XOCM_XMPU_CFG_R05_WRALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R05_WRALWD_MASK             0x00000004UL
    #define XOCM_XMPU_CFG_R05_WRALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R05_RDALWD_SHIFT            1UL
    #define XOCM_XMPU_CFG_R05_RDALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R05_RDALWD_MASK             0x00000002UL
    #define XOCM_XMPU_CFG_R05_RDALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R05_EN_SHIFT                0UL
    #define XOCM_XMPU_CFG_R05_EN_WIDTH                1UL
    #define XOCM_XMPU_CFG_R05_EN_MASK                 0x00000001UL
    #define XOCM_XMPU_CFG_R05_EN_DEFVAL               0x0UL

/**
 * Register: XocmXmpuCfgR06Strt
 */
    #define XOCM_XMPU_CFG_R06_STRT                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000160UL )
    #define XOCM_XMPU_CFG_R06_STRT_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R06_STRT_ADDR_SHIFT         0UL
    #define XOCM_XMPU_CFG_R06_STRT_ADDR_WIDTH         28UL
    #define XOCM_XMPU_CFG_R06_STRT_ADDR_MASK          0x0fffffffUL
    #define XOCM_XMPU_CFG_R06_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XocmXmpuCfgR06End
 */
    #define XOCM_XMPU_CFG_R06_END                     ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000164UL )
    #define XOCM_XMPU_CFG_R06_END_RSTVAL              0x00000000UL

    #define XOCM_XMPU_CFG_R06_END_ADDR_SHIFT          0UL
    #define XOCM_XMPU_CFG_R06_END_ADDR_WIDTH          28UL
    #define XOCM_XMPU_CFG_R06_END_ADDR_MASK           0x0fffffffUL
    #define XOCM_XMPU_CFG_R06_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XocmXmpuCfgR06Mstr
 */
    #define XOCM_XMPU_CFG_R06_MSTR                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000168UL )
    #define XOCM_XMPU_CFG_R06_MSTR_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R06_MSTR_MSK_SHIFT          16UL
    #define XOCM_XMPU_CFG_R06_MSTR_MSK_WIDTH          16UL
    #define XOCM_XMPU_CFG_R06_MSTR_MSK_MASK           0xffff0000UL
    #define XOCM_XMPU_CFG_R06_MSTR_MSK_DEFVAL         0x0UL

    #define XOCM_XMPU_CFG_R06_MSTR_ID_SHIFT           0UL
    #define XOCM_XMPU_CFG_R06_MSTR_ID_WIDTH           16UL
    #define XOCM_XMPU_CFG_R06_MSTR_ID_MASK            0x0000ffffUL
    #define XOCM_XMPU_CFG_R06_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgR06
 */
    #define XOCM_XMPU_CFG_R06                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x0000016CUL )
    #define XOCM_XMPU_CFG_R06_RSTVAL                  0x00000008UL

    #define XOCM_XMPU_CFG_R06_NSCHKTYPE_SHIFT         4UL
    #define XOCM_XMPU_CFG_R06_NSCHKTYPE_WIDTH         1UL
    #define XOCM_XMPU_CFG_R06_NSCHKTYPE_MASK          0x00000010UL
    #define XOCM_XMPU_CFG_R06_NSCHKTYPE_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_R06_REGNNS_SHIFT            3UL
    #define XOCM_XMPU_CFG_R06_REGNNS_WIDTH            1UL
    #define XOCM_XMPU_CFG_R06_REGNNS_MASK             0x00000008UL
    #define XOCM_XMPU_CFG_R06_REGNNS_DEFVAL           0x1UL

    #define XOCM_XMPU_CFG_R06_WRALWD_SHIFT            2UL
    #define XOCM_XMPU_CFG_R06_WRALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R06_WRALWD_MASK             0x00000004UL
    #define XOCM_XMPU_CFG_R06_WRALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R06_RDALWD_SHIFT            1UL
    #define XOCM_XMPU_CFG_R06_RDALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R06_RDALWD_MASK             0x00000002UL
    #define XOCM_XMPU_CFG_R06_RDALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R06_EN_SHIFT                0UL
    #define XOCM_XMPU_CFG_R06_EN_WIDTH                1UL
    #define XOCM_XMPU_CFG_R06_EN_MASK                 0x00000001UL
    #define XOCM_XMPU_CFG_R06_EN_DEFVAL               0x0UL

/**
 * Register: XocmXmpuCfgR07Strt
 */
    #define XOCM_XMPU_CFG_R07_STRT                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000170UL )
    #define XOCM_XMPU_CFG_R07_STRT_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R07_STRT_ADDR_SHIFT         0UL
    #define XOCM_XMPU_CFG_R07_STRT_ADDR_WIDTH         28UL
    #define XOCM_XMPU_CFG_R07_STRT_ADDR_MASK          0x0fffffffUL
    #define XOCM_XMPU_CFG_R07_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XocmXmpuCfgR07End
 */
    #define XOCM_XMPU_CFG_R07_END                     ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000174UL )
    #define XOCM_XMPU_CFG_R07_END_RSTVAL              0x00000000UL

    #define XOCM_XMPU_CFG_R07_END_ADDR_SHIFT          0UL
    #define XOCM_XMPU_CFG_R07_END_ADDR_WIDTH          28UL
    #define XOCM_XMPU_CFG_R07_END_ADDR_MASK           0x0fffffffUL
    #define XOCM_XMPU_CFG_R07_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XocmXmpuCfgR07Mstr
 */
    #define XOCM_XMPU_CFG_R07_MSTR                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000178UL )
    #define XOCM_XMPU_CFG_R07_MSTR_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R07_MSTR_MSK_SHIFT          16UL
    #define XOCM_XMPU_CFG_R07_MSTR_MSK_WIDTH          16UL
    #define XOCM_XMPU_CFG_R07_MSTR_MSK_MASK           0xffff0000UL
    #define XOCM_XMPU_CFG_R07_MSTR_MSK_DEFVAL         0x0UL

    #define XOCM_XMPU_CFG_R07_MSTR_ID_SHIFT           0UL
    #define XOCM_XMPU_CFG_R07_MSTR_ID_WIDTH           16UL
    #define XOCM_XMPU_CFG_R07_MSTR_ID_MASK            0x0000ffffUL
    #define XOCM_XMPU_CFG_R07_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgR07
 */
    #define XOCM_XMPU_CFG_R07                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x0000017CUL )
    #define XOCM_XMPU_CFG_R07_RSTVAL                  0x00000008UL

    #define XOCM_XMPU_CFG_R07_NSCHKTYPE_SHIFT         4UL
    #define XOCM_XMPU_CFG_R07_NSCHKTYPE_WIDTH         1UL
    #define XOCM_XMPU_CFG_R07_NSCHKTYPE_MASK          0x00000010UL
    #define XOCM_XMPU_CFG_R07_NSCHKTYPE_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_R07_REGNNS_SHIFT            3UL
    #define XOCM_XMPU_CFG_R07_REGNNS_WIDTH            1UL
    #define XOCM_XMPU_CFG_R07_REGNNS_MASK             0x00000008UL
    #define XOCM_XMPU_CFG_R07_REGNNS_DEFVAL           0x1UL

    #define XOCM_XMPU_CFG_R07_WRALWD_SHIFT            2UL
    #define XOCM_XMPU_CFG_R07_WRALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R07_WRALWD_MASK             0x00000004UL
    #define XOCM_XMPU_CFG_R07_WRALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R07_RDALWD_SHIFT            1UL
    #define XOCM_XMPU_CFG_R07_RDALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R07_RDALWD_MASK             0x00000002UL
    #define XOCM_XMPU_CFG_R07_RDALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R07_EN_SHIFT                0UL
    #define XOCM_XMPU_CFG_R07_EN_WIDTH                1UL
    #define XOCM_XMPU_CFG_R07_EN_MASK                 0x00000001UL
    #define XOCM_XMPU_CFG_R07_EN_DEFVAL               0x0UL

/**
 * Register: XocmXmpuCfgR08Strt
 */
    #define XOCM_XMPU_CFG_R08_STRT                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000180UL )
    #define XOCM_XMPU_CFG_R08_STRT_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R08_STRT_ADDR_SHIFT         0UL
    #define XOCM_XMPU_CFG_R08_STRT_ADDR_WIDTH         28UL
    #define XOCM_XMPU_CFG_R08_STRT_ADDR_MASK          0x0fffffffUL
    #define XOCM_XMPU_CFG_R08_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XocmXmpuCfgR08End
 */
    #define XOCM_XMPU_CFG_R08_END                     ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000184UL )
    #define XOCM_XMPU_CFG_R08_END_RSTVAL              0x00000000UL

    #define XOCM_XMPU_CFG_R08_END_ADDR_SHIFT          0UL
    #define XOCM_XMPU_CFG_R08_END_ADDR_WIDTH          28UL
    #define XOCM_XMPU_CFG_R08_END_ADDR_MASK           0x0fffffffUL
    #define XOCM_XMPU_CFG_R08_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XocmXmpuCfgR08Mstr
 */
    #define XOCM_XMPU_CFG_R08_MSTR                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000188UL )
    #define XOCM_XMPU_CFG_R08_MSTR_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R08_MSTR_MSK_SHIFT          16UL
    #define XOCM_XMPU_CFG_R08_MSTR_MSK_WIDTH          16UL
    #define XOCM_XMPU_CFG_R08_MSTR_MSK_MASK           0xffff0000UL
    #define XOCM_XMPU_CFG_R08_MSTR_MSK_DEFVAL         0x0UL

    #define XOCM_XMPU_CFG_R08_MSTR_ID_SHIFT           0UL
    #define XOCM_XMPU_CFG_R08_MSTR_ID_WIDTH           16UL
    #define XOCM_XMPU_CFG_R08_MSTR_ID_MASK            0x0000ffffUL
    #define XOCM_XMPU_CFG_R08_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgR08
 */
    #define XOCM_XMPU_CFG_R08                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x0000018CUL )
    #define XOCM_XMPU_CFG_R08_RSTVAL                  0x00000008UL

    #define XOCM_XMPU_CFG_R08_NSCHKTYPE_SHIFT         4UL
    #define XOCM_XMPU_CFG_R08_NSCHKTYPE_WIDTH         1UL
    #define XOCM_XMPU_CFG_R08_NSCHKTYPE_MASK          0x00000010UL
    #define XOCM_XMPU_CFG_R08_NSCHKTYPE_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_R08_REGNNS_SHIFT            3UL
    #define XOCM_XMPU_CFG_R08_REGNNS_WIDTH            1UL
    #define XOCM_XMPU_CFG_R08_REGNNS_MASK             0x00000008UL
    #define XOCM_XMPU_CFG_R08_REGNNS_DEFVAL           0x1UL

    #define XOCM_XMPU_CFG_R08_WRALWD_SHIFT            2UL
    #define XOCM_XMPU_CFG_R08_WRALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R08_WRALWD_MASK             0x00000004UL
    #define XOCM_XMPU_CFG_R08_WRALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R08_RDALWD_SHIFT            1UL
    #define XOCM_XMPU_CFG_R08_RDALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R08_RDALWD_MASK             0x00000002UL
    #define XOCM_XMPU_CFG_R08_RDALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R08_EN_SHIFT                0UL
    #define XOCM_XMPU_CFG_R08_EN_WIDTH                1UL
    #define XOCM_XMPU_CFG_R08_EN_MASK                 0x00000001UL
    #define XOCM_XMPU_CFG_R08_EN_DEFVAL               0x0UL

/**
 * Register: XocmXmpuCfgR09Strt
 */
    #define XOCM_XMPU_CFG_R09_STRT                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000190UL )
    #define XOCM_XMPU_CFG_R09_STRT_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R09_STRT_ADDR_SHIFT         0UL
    #define XOCM_XMPU_CFG_R09_STRT_ADDR_WIDTH         28UL
    #define XOCM_XMPU_CFG_R09_STRT_ADDR_MASK          0x0fffffffUL
    #define XOCM_XMPU_CFG_R09_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XocmXmpuCfgR09End
 */
    #define XOCM_XMPU_CFG_R09_END                     ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000194UL )
    #define XOCM_XMPU_CFG_R09_END_RSTVAL              0x00000000UL

    #define XOCM_XMPU_CFG_R09_END_ADDR_SHIFT          0UL
    #define XOCM_XMPU_CFG_R09_END_ADDR_WIDTH          28UL
    #define XOCM_XMPU_CFG_R09_END_ADDR_MASK           0x0fffffffUL
    #define XOCM_XMPU_CFG_R09_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XocmXmpuCfgR09Mstr
 */
    #define XOCM_XMPU_CFG_R09_MSTR                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x00000198UL )
    #define XOCM_XMPU_CFG_R09_MSTR_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R09_MSTR_MSK_SHIFT          16UL
    #define XOCM_XMPU_CFG_R09_MSTR_MSK_WIDTH          16UL
    #define XOCM_XMPU_CFG_R09_MSTR_MSK_MASK           0xffff0000UL
    #define XOCM_XMPU_CFG_R09_MSTR_MSK_DEFVAL         0x0UL

    #define XOCM_XMPU_CFG_R09_MSTR_ID_SHIFT           0UL
    #define XOCM_XMPU_CFG_R09_MSTR_ID_WIDTH           16UL
    #define XOCM_XMPU_CFG_R09_MSTR_ID_MASK            0x0000ffffUL
    #define XOCM_XMPU_CFG_R09_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgR09
 */
    #define XOCM_XMPU_CFG_R09                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x0000019CUL )
    #define XOCM_XMPU_CFG_R09_RSTVAL                  0x00000008UL

    #define XOCM_XMPU_CFG_R09_NSCHKTYPE_SHIFT         4UL
    #define XOCM_XMPU_CFG_R09_NSCHKTYPE_WIDTH         1UL
    #define XOCM_XMPU_CFG_R09_NSCHKTYPE_MASK          0x00000010UL
    #define XOCM_XMPU_CFG_R09_NSCHKTYPE_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_R09_REGNNS_SHIFT            3UL
    #define XOCM_XMPU_CFG_R09_REGNNS_WIDTH            1UL
    #define XOCM_XMPU_CFG_R09_REGNNS_MASK             0x00000008UL
    #define XOCM_XMPU_CFG_R09_REGNNS_DEFVAL           0x1UL

    #define XOCM_XMPU_CFG_R09_WRALWD_SHIFT            2UL
    #define XOCM_XMPU_CFG_R09_WRALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R09_WRALWD_MASK             0x00000004UL
    #define XOCM_XMPU_CFG_R09_WRALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R09_RDALWD_SHIFT            1UL
    #define XOCM_XMPU_CFG_R09_RDALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R09_RDALWD_MASK             0x00000002UL
    #define XOCM_XMPU_CFG_R09_RDALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R09_EN_SHIFT                0UL
    #define XOCM_XMPU_CFG_R09_EN_WIDTH                1UL
    #define XOCM_XMPU_CFG_R09_EN_MASK                 0x00000001UL
    #define XOCM_XMPU_CFG_R09_EN_DEFVAL               0x0UL

/**
 * Register: XocmXmpuCfgR10Strt
 */
    #define XOCM_XMPU_CFG_R10_STRT                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001A0UL )
    #define XOCM_XMPU_CFG_R10_STRT_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R10_STRT_ADDR_SHIFT         0UL
    #define XOCM_XMPU_CFG_R10_STRT_ADDR_WIDTH         28UL
    #define XOCM_XMPU_CFG_R10_STRT_ADDR_MASK          0x0fffffffUL
    #define XOCM_XMPU_CFG_R10_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XocmXmpuCfgR10End
 */
    #define XOCM_XMPU_CFG_R10_END                     ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001A4UL )
    #define XOCM_XMPU_CFG_R10_END_RSTVAL              0x00000000UL

    #define XOCM_XMPU_CFG_R10_END_ADDR_SHIFT          0UL
    #define XOCM_XMPU_CFG_R10_END_ADDR_WIDTH          28UL
    #define XOCM_XMPU_CFG_R10_END_ADDR_MASK           0x0fffffffUL
    #define XOCM_XMPU_CFG_R10_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XocmXmpuCfgR10Mstr
 */
    #define XOCM_XMPU_CFG_R10_MSTR                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001A8UL )
    #define XOCM_XMPU_CFG_R10_MSTR_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R10_MSTR_MSK_SHIFT          16UL
    #define XOCM_XMPU_CFG_R10_MSTR_MSK_WIDTH          16UL
    #define XOCM_XMPU_CFG_R10_MSTR_MSK_MASK           0xffff0000UL
    #define XOCM_XMPU_CFG_R10_MSTR_MSK_DEFVAL         0x0UL

    #define XOCM_XMPU_CFG_R10_MSTR_ID_SHIFT           0UL
    #define XOCM_XMPU_CFG_R10_MSTR_ID_WIDTH           16UL
    #define XOCM_XMPU_CFG_R10_MSTR_ID_MASK            0x0000ffffUL
    #define XOCM_XMPU_CFG_R10_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgR10
 */
    #define XOCM_XMPU_CFG_R10                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001ACUL )
    #define XOCM_XMPU_CFG_R10_RSTVAL                  0x00000008UL

    #define XOCM_XMPU_CFG_R10_NSCHKTYPE_SHIFT         4UL
    #define XOCM_XMPU_CFG_R10_NSCHKTYPE_WIDTH         1UL
    #define XOCM_XMPU_CFG_R10_NSCHKTYPE_MASK          0x00000010UL
    #define XOCM_XMPU_CFG_R10_NSCHKTYPE_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_R10_REGNNS_SHIFT            3UL
    #define XOCM_XMPU_CFG_R10_REGNNS_WIDTH            1UL
    #define XOCM_XMPU_CFG_R10_REGNNS_MASK             0x00000008UL
    #define XOCM_XMPU_CFG_R10_REGNNS_DEFVAL           0x1UL

    #define XOCM_XMPU_CFG_R10_WRALWD_SHIFT            2UL
    #define XOCM_XMPU_CFG_R10_WRALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R10_WRALWD_MASK             0x00000004UL
    #define XOCM_XMPU_CFG_R10_WRALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R10_RDALWD_SHIFT            1UL
    #define XOCM_XMPU_CFG_R10_RDALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R10_RDALWD_MASK             0x00000002UL
    #define XOCM_XMPU_CFG_R10_RDALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R10_EN_SHIFT                0UL
    #define XOCM_XMPU_CFG_R10_EN_WIDTH                1UL
    #define XOCM_XMPU_CFG_R10_EN_MASK                 0x00000001UL
    #define XOCM_XMPU_CFG_R10_EN_DEFVAL               0x0UL

/**
 * Register: XocmXmpuCfgR11Strt
 */
    #define XOCM_XMPU_CFG_R11_STRT                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001B0UL )
    #define XOCM_XMPU_CFG_R11_STRT_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R11_STRT_ADDR_SHIFT         0UL
    #define XOCM_XMPU_CFG_R11_STRT_ADDR_WIDTH         28UL
    #define XOCM_XMPU_CFG_R11_STRT_ADDR_MASK          0x0fffffffUL
    #define XOCM_XMPU_CFG_R11_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XocmXmpuCfgR11End
 */
    #define XOCM_XMPU_CFG_R11_END                     ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001B4UL )
    #define XOCM_XMPU_CFG_R11_END_RSTVAL              0x00000000UL

    #define XOCM_XMPU_CFG_R11_END_ADDR_SHIFT          0UL
    #define XOCM_XMPU_CFG_R11_END_ADDR_WIDTH          28UL
    #define XOCM_XMPU_CFG_R11_END_ADDR_MASK           0x0fffffffUL
    #define XOCM_XMPU_CFG_R11_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XocmXmpuCfgR11Mstr
 */
    #define XOCM_XMPU_CFG_R11_MSTR                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001B8UL )
    #define XOCM_XMPU_CFG_R11_MSTR_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R11_MSTR_MSK_SHIFT          16UL
    #define XOCM_XMPU_CFG_R11_MSTR_MSK_WIDTH          16UL
    #define XOCM_XMPU_CFG_R11_MSTR_MSK_MASK           0xffff0000UL
    #define XOCM_XMPU_CFG_R11_MSTR_MSK_DEFVAL         0x0UL

    #define XOCM_XMPU_CFG_R11_MSTR_ID_SHIFT           0UL
    #define XOCM_XMPU_CFG_R11_MSTR_ID_WIDTH           16UL
    #define XOCM_XMPU_CFG_R11_MSTR_ID_MASK            0x0000ffffUL
    #define XOCM_XMPU_CFG_R11_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgR11
 */
    #define XOCM_XMPU_CFG_R11                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001BCUL )
    #define XOCM_XMPU_CFG_R11_RSTVAL                  0x00000008UL

    #define XOCM_XMPU_CFG_R11_NSCHKTYPE_SHIFT         4UL
    #define XOCM_XMPU_CFG_R11_NSCHKTYPE_WIDTH         1UL
    #define XOCM_XMPU_CFG_R11_NSCHKTYPE_MASK          0x00000010UL
    #define XOCM_XMPU_CFG_R11_NSCHKTYPE_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_R11_REGNNS_SHIFT            3UL
    #define XOCM_XMPU_CFG_R11_REGNNS_WIDTH            1UL
    #define XOCM_XMPU_CFG_R11_REGNNS_MASK             0x00000008UL
    #define XOCM_XMPU_CFG_R11_REGNNS_DEFVAL           0x1UL

    #define XOCM_XMPU_CFG_R11_WRALWD_SHIFT            2UL
    #define XOCM_XMPU_CFG_R11_WRALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R11_WRALWD_MASK             0x00000004UL
    #define XOCM_XMPU_CFG_R11_WRALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R11_RDALWD_SHIFT            1UL
    #define XOCM_XMPU_CFG_R11_RDALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R11_RDALWD_MASK             0x00000002UL
    #define XOCM_XMPU_CFG_R11_RDALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R11_EN_SHIFT                0UL
    #define XOCM_XMPU_CFG_R11_EN_WIDTH                1UL
    #define XOCM_XMPU_CFG_R11_EN_MASK                 0x00000001UL
    #define XOCM_XMPU_CFG_R11_EN_DEFVAL               0x0UL

/**
 * Register: XocmXmpuCfgR12Strt
 */
    #define XOCM_XMPU_CFG_R12_STRT                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001C0UL )
    #define XOCM_XMPU_CFG_R12_STRT_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R12_STRT_ADDR_SHIFT         0UL
    #define XOCM_XMPU_CFG_R12_STRT_ADDR_WIDTH         28UL
    #define XOCM_XMPU_CFG_R12_STRT_ADDR_MASK          0x0fffffffUL
    #define XOCM_XMPU_CFG_R12_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XocmXmpuCfgR12End
 */
    #define XOCM_XMPU_CFG_R12_END                     ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001C4UL )
    #define XOCM_XMPU_CFG_R12_END_RSTVAL              0x00000000UL

    #define XOCM_XMPU_CFG_R12_END_ADDR_SHIFT          0UL
    #define XOCM_XMPU_CFG_R12_END_ADDR_WIDTH          28UL
    #define XOCM_XMPU_CFG_R12_END_ADDR_MASK           0x0fffffffUL
    #define XOCM_XMPU_CFG_R12_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XocmXmpuCfgR12Mstr
 */
    #define XOCM_XMPU_CFG_R12_MSTR                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001C8UL )
    #define XOCM_XMPU_CFG_R12_MSTR_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R12_MSTR_MSK_SHIFT          16UL
    #define XOCM_XMPU_CFG_R12_MSTR_MSK_WIDTH          16UL
    #define XOCM_XMPU_CFG_R12_MSTR_MSK_MASK           0xffff0000UL
    #define XOCM_XMPU_CFG_R12_MSTR_MSK_DEFVAL         0x0UL

    #define XOCM_XMPU_CFG_R12_MSTR_ID_SHIFT           0UL
    #define XOCM_XMPU_CFG_R12_MSTR_ID_WIDTH           16UL
    #define XOCM_XMPU_CFG_R12_MSTR_ID_MASK            0x0000ffffUL
    #define XOCM_XMPU_CFG_R12_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgR12
 */
    #define XOCM_XMPU_CFG_R12                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001CCUL )
    #define XOCM_XMPU_CFG_R12_RSTVAL                  0x00000008UL

    #define XOCM_XMPU_CFG_R12_NSCHKTYPE_SHIFT         4UL
    #define XOCM_XMPU_CFG_R12_NSCHKTYPE_WIDTH         1UL
    #define XOCM_XMPU_CFG_R12_NSCHKTYPE_MASK          0x00000010UL
    #define XOCM_XMPU_CFG_R12_NSCHKTYPE_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_R12_REGNNS_SHIFT            3UL
    #define XOCM_XMPU_CFG_R12_REGNNS_WIDTH            1UL
    #define XOCM_XMPU_CFG_R12_REGNNS_MASK             0x00000008UL
    #define XOCM_XMPU_CFG_R12_REGNNS_DEFVAL           0x1UL

    #define XOCM_XMPU_CFG_R12_WRALWD_SHIFT            2UL
    #define XOCM_XMPU_CFG_R12_WRALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R12_WRALWD_MASK             0x00000004UL
    #define XOCM_XMPU_CFG_R12_WRALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R12_RDALWD_SHIFT            1UL
    #define XOCM_XMPU_CFG_R12_RDALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R12_RDALWD_MASK             0x00000002UL
    #define XOCM_XMPU_CFG_R12_RDALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R12_EN_SHIFT                0UL
    #define XOCM_XMPU_CFG_R12_EN_WIDTH                1UL
    #define XOCM_XMPU_CFG_R12_EN_MASK                 0x00000001UL
    #define XOCM_XMPU_CFG_R12_EN_DEFVAL               0x0UL

/**
 * Register: XocmXmpuCfgR13Strt
 */
    #define XOCM_XMPU_CFG_R13_STRT                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001D0UL )
    #define XOCM_XMPU_CFG_R13_STRT_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R13_STRT_ADDR_SHIFT         0UL
    #define XOCM_XMPU_CFG_R13_STRT_ADDR_WIDTH         28UL
    #define XOCM_XMPU_CFG_R13_STRT_ADDR_MASK          0x0fffffffUL
    #define XOCM_XMPU_CFG_R13_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XocmXmpuCfgR13End
 */
    #define XOCM_XMPU_CFG_R13_END                     ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001D4UL )
    #define XOCM_XMPU_CFG_R13_END_RSTVAL              0x00000000UL

    #define XOCM_XMPU_CFG_R13_END_ADDR_SHIFT          0UL
    #define XOCM_XMPU_CFG_R13_END_ADDR_WIDTH          28UL
    #define XOCM_XMPU_CFG_R13_END_ADDR_MASK           0x0fffffffUL
    #define XOCM_XMPU_CFG_R13_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XocmXmpuCfgR13Mstr
 */
    #define XOCM_XMPU_CFG_R13_MSTR                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001D8UL )
    #define XOCM_XMPU_CFG_R13_MSTR_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R13_MSTR_MSK_SHIFT          16UL
    #define XOCM_XMPU_CFG_R13_MSTR_MSK_WIDTH          16UL
    #define XOCM_XMPU_CFG_R13_MSTR_MSK_MASK           0xffff0000UL
    #define XOCM_XMPU_CFG_R13_MSTR_MSK_DEFVAL         0x0UL

    #define XOCM_XMPU_CFG_R13_MSTR_ID_SHIFT           0UL
    #define XOCM_XMPU_CFG_R13_MSTR_ID_WIDTH           16UL
    #define XOCM_XMPU_CFG_R13_MSTR_ID_MASK            0x0000ffffUL
    #define XOCM_XMPU_CFG_R13_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgR13
 */
    #define XOCM_XMPU_CFG_R13                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001DCUL )
    #define XOCM_XMPU_CFG_R13_RSTVAL                  0x00000008UL

    #define XOCM_XMPU_CFG_R13_NSCHKTYPE_SHIFT         4UL
    #define XOCM_XMPU_CFG_R13_NSCHKTYPE_WIDTH         1UL
    #define XOCM_XMPU_CFG_R13_NSCHKTYPE_MASK          0x00000010UL
    #define XOCM_XMPU_CFG_R13_NSCHKTYPE_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_R13_REGNNS_SHIFT            3UL
    #define XOCM_XMPU_CFG_R13_REGNNS_WIDTH            1UL
    #define XOCM_XMPU_CFG_R13_REGNNS_MASK             0x00000008UL
    #define XOCM_XMPU_CFG_R13_REGNNS_DEFVAL           0x1UL

    #define XOCM_XMPU_CFG_R13_WRALWD_SHIFT            2UL
    #define XOCM_XMPU_CFG_R13_WRALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R13_WRALWD_MASK             0x00000004UL
    #define XOCM_XMPU_CFG_R13_WRALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R13_RDALWD_SHIFT            1UL
    #define XOCM_XMPU_CFG_R13_RDALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R13_RDALWD_MASK             0x00000002UL
    #define XOCM_XMPU_CFG_R13_RDALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R13_EN_SHIFT                0UL
    #define XOCM_XMPU_CFG_R13_EN_WIDTH                1UL
    #define XOCM_XMPU_CFG_R13_EN_MASK                 0x00000001UL
    #define XOCM_XMPU_CFG_R13_EN_DEFVAL               0x0UL

/**
 * Register: XocmXmpuCfgR14Strt
 */
    #define XOCM_XMPU_CFG_R14_STRT                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001E0UL )
    #define XOCM_XMPU_CFG_R14_STRT_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R14_STRT_ADDR_SHIFT         0UL
    #define XOCM_XMPU_CFG_R14_STRT_ADDR_WIDTH         28UL
    #define XOCM_XMPU_CFG_R14_STRT_ADDR_MASK          0x0fffffffUL
    #define XOCM_XMPU_CFG_R14_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XocmXmpuCfgR14End
 */
    #define XOCM_XMPU_CFG_R14_END                     ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001E4UL )
    #define XOCM_XMPU_CFG_R14_END_RSTVAL              0x00000000UL

    #define XOCM_XMPU_CFG_R14_END_ADDR_SHIFT          0UL
    #define XOCM_XMPU_CFG_R14_END_ADDR_WIDTH          28UL
    #define XOCM_XMPU_CFG_R14_END_ADDR_MASK           0x0fffffffUL
    #define XOCM_XMPU_CFG_R14_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XocmXmpuCfgR14Mstr
 */
    #define XOCM_XMPU_CFG_R14_MSTR                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001E8UL )
    #define XOCM_XMPU_CFG_R14_MSTR_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R14_MSTR_MSK_SHIFT          16UL
    #define XOCM_XMPU_CFG_R14_MSTR_MSK_WIDTH          16UL
    #define XOCM_XMPU_CFG_R14_MSTR_MSK_MASK           0xffff0000UL
    #define XOCM_XMPU_CFG_R14_MSTR_MSK_DEFVAL         0x0UL

    #define XOCM_XMPU_CFG_R14_MSTR_ID_SHIFT           0UL
    #define XOCM_XMPU_CFG_R14_MSTR_ID_WIDTH           16UL
    #define XOCM_XMPU_CFG_R14_MSTR_ID_MASK            0x0000ffffUL
    #define XOCM_XMPU_CFG_R14_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgR14
 */
    #define XOCM_XMPU_CFG_R14                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001ECUL )
    #define XOCM_XMPU_CFG_R14_RSTVAL                  0x00000008UL

    #define XOCM_XMPU_CFG_R14_NSCHKTYPE_SHIFT         4UL
    #define XOCM_XMPU_CFG_R14_NSCHKTYPE_WIDTH         1UL
    #define XOCM_XMPU_CFG_R14_NSCHKTYPE_MASK          0x00000010UL
    #define XOCM_XMPU_CFG_R14_NSCHKTYPE_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_R14_REGNNS_SHIFT            3UL
    #define XOCM_XMPU_CFG_R14_REGNNS_WIDTH            1UL
    #define XOCM_XMPU_CFG_R14_REGNNS_MASK             0x00000008UL
    #define XOCM_XMPU_CFG_R14_REGNNS_DEFVAL           0x1UL

    #define XOCM_XMPU_CFG_R14_WRALWD_SHIFT            2UL
    #define XOCM_XMPU_CFG_R14_WRALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R14_WRALWD_MASK             0x00000004UL
    #define XOCM_XMPU_CFG_R14_WRALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R14_RDALWD_SHIFT            1UL
    #define XOCM_XMPU_CFG_R14_RDALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R14_RDALWD_MASK             0x00000002UL
    #define XOCM_XMPU_CFG_R14_RDALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R14_EN_SHIFT                0UL
    #define XOCM_XMPU_CFG_R14_EN_WIDTH                1UL
    #define XOCM_XMPU_CFG_R14_EN_MASK                 0x00000001UL
    #define XOCM_XMPU_CFG_R14_EN_DEFVAL               0x0UL

/**
 * Register: XocmXmpuCfgR15Strt
 */
    #define XOCM_XMPU_CFG_R15_STRT                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001F0UL )
    #define XOCM_XMPU_CFG_R15_STRT_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R15_STRT_ADDR_SHIFT         0UL
    #define XOCM_XMPU_CFG_R15_STRT_ADDR_WIDTH         28UL
    #define XOCM_XMPU_CFG_R15_STRT_ADDR_MASK          0x0fffffffUL
    #define XOCM_XMPU_CFG_R15_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XocmXmpuCfgR15End
 */
    #define XOCM_XMPU_CFG_R15_END                     ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001F4UL )
    #define XOCM_XMPU_CFG_R15_END_RSTVAL              0x00000000UL

    #define XOCM_XMPU_CFG_R15_END_ADDR_SHIFT          0UL
    #define XOCM_XMPU_CFG_R15_END_ADDR_WIDTH          28UL
    #define XOCM_XMPU_CFG_R15_END_ADDR_MASK           0x0fffffffUL
    #define XOCM_XMPU_CFG_R15_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XocmXmpuCfgR15Mstr
 */
    #define XOCM_XMPU_CFG_R15_MSTR                    ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001F8UL )
    #define XOCM_XMPU_CFG_R15_MSTR_RSTVAL             0x00000000UL

    #define XOCM_XMPU_CFG_R15_MSTR_MSK_SHIFT          16UL
    #define XOCM_XMPU_CFG_R15_MSTR_MSK_WIDTH          16UL
    #define XOCM_XMPU_CFG_R15_MSTR_MSK_MASK           0xffff0000UL
    #define XOCM_XMPU_CFG_R15_MSTR_MSK_DEFVAL         0x0UL

    #define XOCM_XMPU_CFG_R15_MSTR_ID_SHIFT           0UL
    #define XOCM_XMPU_CFG_R15_MSTR_ID_WIDTH           16UL
    #define XOCM_XMPU_CFG_R15_MSTR_ID_MASK            0x0000ffffUL
    #define XOCM_XMPU_CFG_R15_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XocmXmpuCfgR15
 */
    #define XOCM_XMPU_CFG_R15                         ( ( XOCM_XMPU_CFG_BASEADDR ) +0x000001FCUL )
    #define XOCM_XMPU_CFG_R15_RSTVAL                  0x00000008UL

    #define XOCM_XMPU_CFG_R15_NSCHKTYPE_SHIFT         4UL
    #define XOCM_XMPU_CFG_R15_NSCHKTYPE_WIDTH         1UL
    #define XOCM_XMPU_CFG_R15_NSCHKTYPE_MASK          0x00000010UL
    #define XOCM_XMPU_CFG_R15_NSCHKTYPE_DEFVAL        0x0UL

    #define XOCM_XMPU_CFG_R15_REGNNS_SHIFT            3UL
    #define XOCM_XMPU_CFG_R15_REGNNS_WIDTH            1UL
    #define XOCM_XMPU_CFG_R15_REGNNS_MASK             0x00000008UL
    #define XOCM_XMPU_CFG_R15_REGNNS_DEFVAL           0x1UL

    #define XOCM_XMPU_CFG_R15_WRALWD_SHIFT            2UL
    #define XOCM_XMPU_CFG_R15_WRALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R15_WRALWD_MASK             0x00000004UL
    #define XOCM_XMPU_CFG_R15_WRALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R15_RDALWD_SHIFT            1UL
    #define XOCM_XMPU_CFG_R15_RDALWD_WIDTH            1UL
    #define XOCM_XMPU_CFG_R15_RDALWD_MASK             0x00000002UL
    #define XOCM_XMPU_CFG_R15_RDALWD_DEFVAL           0x0UL

    #define XOCM_XMPU_CFG_R15_EN_SHIFT                0UL
    #define XOCM_XMPU_CFG_R15_EN_WIDTH                1UL
    #define XOCM_XMPU_CFG_R15_EN_MASK                 0x00000001UL
    #define XOCM_XMPU_CFG_R15_EN_DEFVAL               0x0UL


    #ifdef __cplusplus
}
    #endif

#endif /* __XOCM_XMPU_CFG_H__ */
