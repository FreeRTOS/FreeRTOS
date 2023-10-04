/* ### HEADER ### */

#ifndef __XFPD_XMPU_CFG_H__
    #define __XFPD_XMPU_CFG_H__


    #ifdef __cplusplus
    extern "C" {
    #endif

/**
 * XfpdXmpuCfg Base Address
 */
    #define XFPD_XMPU_CFG_BASEADDR                    0xFD5D0000UL

/**
 * Register: XfpdXmpuCfgCtrl
 */
    #define XFPD_XMPU_CFG_CTRL                        ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000000UL )
    #define XFPD_XMPU_CFG_CTRL_RSTVAL                 0x00000003UL

    #define XFPD_XMPU_CFG_CTRL_ALIGNCFG_SHIFT         3UL
    #define XFPD_XMPU_CFG_CTRL_ALIGNCFG_WIDTH         1UL
    #define XFPD_XMPU_CFG_CTRL_ALIGNCFG_MASK          0x00000008UL
    #define XFPD_XMPU_CFG_CTRL_ALIGNCFG_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_CTRL_POISONCFG_SHIFT        2UL
    #define XFPD_XMPU_CFG_CTRL_POISONCFG_WIDTH        1UL
    #define XFPD_XMPU_CFG_CTRL_POISONCFG_MASK         0x00000004UL
    #define XFPD_XMPU_CFG_CTRL_POISONCFG_DEFVAL       0x0UL

    #define XFPD_XMPU_CFG_CTRL_DEFWRALWD_SHIFT        1UL
    #define XFPD_XMPU_CFG_CTRL_DEFWRALWD_WIDTH        1UL
    #define XFPD_XMPU_CFG_CTRL_DEFWRALWD_MASK         0x00000002UL
    #define XFPD_XMPU_CFG_CTRL_DEFWRALWD_DEFVAL       0x1UL

    #define XFPD_XMPU_CFG_CTRL_DEFRDALWD_SHIFT        0UL
    #define XFPD_XMPU_CFG_CTRL_DEFRDALWD_WIDTH        1UL
    #define XFPD_XMPU_CFG_CTRL_DEFRDALWD_MASK         0x00000001UL
    #define XFPD_XMPU_CFG_CTRL_DEFRDALWD_DEFVAL       0x1UL

/**
 * Register: XfpdXmpuCfgErrSts1
 */
    #define XFPD_XMPU_CFG_ERR_STS1                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000004UL )
    #define XFPD_XMPU_CFG_ERR_STS1_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_ERR_STS1_AXI_ADDR_SHIFT     0UL
    #define XFPD_XMPU_CFG_ERR_STS1_AXI_ADDR_WIDTH     32UL
    #define XFPD_XMPU_CFG_ERR_STS1_AXI_ADDR_MASK      0xffffffffUL
    #define XFPD_XMPU_CFG_ERR_STS1_AXI_ADDR_DEFVAL    0x0UL

/**
 * Register: XfpdXmpuCfgErrSts2
 */
    #define XFPD_XMPU_CFG_ERR_STS2                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000008UL )
    #define XFPD_XMPU_CFG_ERR_STS2_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_ERR_STS2_AXI_ID_SHIFT       0UL
    #define XFPD_XMPU_CFG_ERR_STS2_AXI_ID_WIDTH       16UL
    #define XFPD_XMPU_CFG_ERR_STS2_AXI_ID_MASK        0x0000ffffUL
    #define XFPD_XMPU_CFG_ERR_STS2_AXI_ID_DEFVAL      0x0UL

/**
 * Register: XfpdXmpuCfgPoison
 */
    #define XFPD_XMPU_CFG_POISON                      ( ( XFPD_XMPU_CFG_BASEADDR ) +0x0000000CUL )
    #define XFPD_XMPU_CFG_POISON_RSTVAL               0x00000000UL

    #define XFPD_XMPU_CFG_POISON_ATTRIB_SHIFT         20UL
    #define XFPD_XMPU_CFG_POISON_ATTRIB_WIDTH         12UL
    #define XFPD_XMPU_CFG_POISON_ATTRIB_MASK          0xfff00000UL
    #define XFPD_XMPU_CFG_POISON_ATTRIB_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_POISON_BASE_SHIFT           0UL
    #define XFPD_XMPU_CFG_POISON_BASE_WIDTH           20UL
    #define XFPD_XMPU_CFG_POISON_BASE_MASK            0x000fffffUL
    #define XFPD_XMPU_CFG_POISON_BASE_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgIsr
 */
    #define XFPD_XMPU_CFG_ISR                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000010UL )
    #define XFPD_XMPU_CFG_ISR_RSTVAL                  0x00000000UL

    #define XFPD_XMPU_CFG_ISR_SECURTYVIO_SHIFT        3UL
    #define XFPD_XMPU_CFG_ISR_SECURTYVIO_WIDTH        1UL
    #define XFPD_XMPU_CFG_ISR_SECURTYVIO_MASK         0x00000008UL
    #define XFPD_XMPU_CFG_ISR_SECURTYVIO_DEFVAL       0x0UL

    #define XFPD_XMPU_CFG_ISR_WRPERMVIO_SHIFT         2UL
    #define XFPD_XMPU_CFG_ISR_WRPERMVIO_WIDTH         1UL
    #define XFPD_XMPU_CFG_ISR_WRPERMVIO_MASK          0x00000004UL
    #define XFPD_XMPU_CFG_ISR_WRPERMVIO_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_ISR_RDPERMVIO_SHIFT         1UL
    #define XFPD_XMPU_CFG_ISR_RDPERMVIO_WIDTH         1UL
    #define XFPD_XMPU_CFG_ISR_RDPERMVIO_MASK          0x00000002UL
    #define XFPD_XMPU_CFG_ISR_RDPERMVIO_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_ISR_INV_APB_SHIFT           0UL
    #define XFPD_XMPU_CFG_ISR_INV_APB_WIDTH           1UL
    #define XFPD_XMPU_CFG_ISR_INV_APB_MASK            0x00000001UL
    #define XFPD_XMPU_CFG_ISR_INV_APB_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgImr
 */
    #define XFPD_XMPU_CFG_IMR                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000014UL )
    #define XFPD_XMPU_CFG_IMR_RSTVAL                  0x0000000fUL

    #define XFPD_XMPU_CFG_IMR_SECURTYVIO_SHIFT        3UL
    #define XFPD_XMPU_CFG_IMR_SECURTYVIO_WIDTH        1UL
    #define XFPD_XMPU_CFG_IMR_SECURTYVIO_MASK         0x00000008UL
    #define XFPD_XMPU_CFG_IMR_SECURTYVIO_DEFVAL       0x1UL

    #define XFPD_XMPU_CFG_IMR_WRPERMVIO_SHIFT         2UL
    #define XFPD_XMPU_CFG_IMR_WRPERMVIO_WIDTH         1UL
    #define XFPD_XMPU_CFG_IMR_WRPERMVIO_MASK          0x00000004UL
    #define XFPD_XMPU_CFG_IMR_WRPERMVIO_DEFVAL        0x1UL

    #define XFPD_XMPU_CFG_IMR_RDPERMVIO_SHIFT         1UL
    #define XFPD_XMPU_CFG_IMR_RDPERMVIO_WIDTH         1UL
    #define XFPD_XMPU_CFG_IMR_RDPERMVIO_MASK          0x00000002UL
    #define XFPD_XMPU_CFG_IMR_RDPERMVIO_DEFVAL        0x1UL

    #define XFPD_XMPU_CFG_IMR_INV_APB_SHIFT           0UL
    #define XFPD_XMPU_CFG_IMR_INV_APB_WIDTH           1UL
    #define XFPD_XMPU_CFG_IMR_INV_APB_MASK            0x00000001UL
    #define XFPD_XMPU_CFG_IMR_INV_APB_DEFVAL          0x1UL

/**
 * Register: XfpdXmpuCfgIen
 */
    #define XFPD_XMPU_CFG_IEN                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000018UL )
    #define XFPD_XMPU_CFG_IEN_RSTVAL                  0x00000000UL

    #define XFPD_XMPU_CFG_IEN_SECURTYVIO_SHIFT        3UL
    #define XFPD_XMPU_CFG_IEN_SECURTYVIO_WIDTH        1UL
    #define XFPD_XMPU_CFG_IEN_SECURTYVIO_MASK         0x00000008UL
    #define XFPD_XMPU_CFG_IEN_SECURTYVIO_DEFVAL       0x0UL

    #define XFPD_XMPU_CFG_IEN_WRPERMVIO_SHIFT         2UL
    #define XFPD_XMPU_CFG_IEN_WRPERMVIO_WIDTH         1UL
    #define XFPD_XMPU_CFG_IEN_WRPERMVIO_MASK          0x00000004UL
    #define XFPD_XMPU_CFG_IEN_WRPERMVIO_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_IEN_RDPERMVIO_SHIFT         1UL
    #define XFPD_XMPU_CFG_IEN_RDPERMVIO_WIDTH         1UL
    #define XFPD_XMPU_CFG_IEN_RDPERMVIO_MASK          0x00000002UL
    #define XFPD_XMPU_CFG_IEN_RDPERMVIO_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_IEN_INV_APB_SHIFT           0UL
    #define XFPD_XMPU_CFG_IEN_INV_APB_WIDTH           1UL
    #define XFPD_XMPU_CFG_IEN_INV_APB_MASK            0x00000001UL
    #define XFPD_XMPU_CFG_IEN_INV_APB_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgIds
 */
    #define XFPD_XMPU_CFG_IDS                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x0000001CUL )
    #define XFPD_XMPU_CFG_IDS_RSTVAL                  0x00000000UL

    #define XFPD_XMPU_CFG_IDS_SECURTYVIO_SHIFT        3UL
    #define XFPD_XMPU_CFG_IDS_SECURTYVIO_WIDTH        1UL
    #define XFPD_XMPU_CFG_IDS_SECURTYVIO_MASK         0x00000008UL
    #define XFPD_XMPU_CFG_IDS_SECURTYVIO_DEFVAL       0x0UL

    #define XFPD_XMPU_CFG_IDS_WRPERMVIO_SHIFT         2UL
    #define XFPD_XMPU_CFG_IDS_WRPERMVIO_WIDTH         1UL
    #define XFPD_XMPU_CFG_IDS_WRPERMVIO_MASK          0x00000004UL
    #define XFPD_XMPU_CFG_IDS_WRPERMVIO_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_IDS_RDPERMVIO_SHIFT         1UL
    #define XFPD_XMPU_CFG_IDS_RDPERMVIO_WIDTH         1UL
    #define XFPD_XMPU_CFG_IDS_RDPERMVIO_MASK          0x00000002UL
    #define XFPD_XMPU_CFG_IDS_RDPERMVIO_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_IDS_INV_APB_SHIFT           0UL
    #define XFPD_XMPU_CFG_IDS_INV_APB_WIDTH           1UL
    #define XFPD_XMPU_CFG_IDS_INV_APB_MASK            0x00000001UL
    #define XFPD_XMPU_CFG_IDS_INV_APB_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgLock
 */
    #define XFPD_XMPU_CFG_LOCK                        ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000020UL )
    #define XFPD_XMPU_CFG_LOCK_RSTVAL                 0x00000000UL

    #define XFPD_XMPU_CFG_LOCK_REGWRDIS_SHIFT         0UL
    #define XFPD_XMPU_CFG_LOCK_REGWRDIS_WIDTH         1UL
    #define XFPD_XMPU_CFG_LOCK_REGWRDIS_MASK          0x00000001UL
    #define XFPD_XMPU_CFG_LOCK_REGWRDIS_DEFVAL        0x0UL

/**
 * Register: XfpdXmpuCfgR00Strt
 */
    #define XFPD_XMPU_CFG_R00_STRT                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000100UL )
    #define XFPD_XMPU_CFG_R00_STRT_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R00_STRT_ADDR_SHIFT         0UL
    #define XFPD_XMPU_CFG_R00_STRT_ADDR_WIDTH         28UL
    #define XFPD_XMPU_CFG_R00_STRT_ADDR_MASK          0x0fffffffUL
    #define XFPD_XMPU_CFG_R00_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XfpdXmpuCfgR00End
 */
    #define XFPD_XMPU_CFG_R00_END                     ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000104UL )
    #define XFPD_XMPU_CFG_R00_END_RSTVAL              0x00000000UL

    #define XFPD_XMPU_CFG_R00_END_ADDR_SHIFT          0UL
    #define XFPD_XMPU_CFG_R00_END_ADDR_WIDTH          28UL
    #define XFPD_XMPU_CFG_R00_END_ADDR_MASK           0x0fffffffUL
    #define XFPD_XMPU_CFG_R00_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XfpdXmpuCfgR00Mstr
 */
    #define XFPD_XMPU_CFG_R00_MSTR                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000108UL )
    #define XFPD_XMPU_CFG_R00_MSTR_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R00_MSTR_MSK_SHIFT          16UL
    #define XFPD_XMPU_CFG_R00_MSTR_MSK_WIDTH          16UL
    #define XFPD_XMPU_CFG_R00_MSTR_MSK_MASK           0xffff0000UL
    #define XFPD_XMPU_CFG_R00_MSTR_MSK_DEFVAL         0x0UL

    #define XFPD_XMPU_CFG_R00_MSTR_ID_SHIFT           0UL
    #define XFPD_XMPU_CFG_R00_MSTR_ID_WIDTH           16UL
    #define XFPD_XMPU_CFG_R00_MSTR_ID_MASK            0x0000ffffUL
    #define XFPD_XMPU_CFG_R00_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgR00
 */
    #define XFPD_XMPU_CFG_R00                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x0000010CUL )
    #define XFPD_XMPU_CFG_R00_RSTVAL                  0x00000008UL

    #define XFPD_XMPU_CFG_R00_NSCHKTYPE_SHIFT         4UL
    #define XFPD_XMPU_CFG_R00_NSCHKTYPE_WIDTH         1UL
    #define XFPD_XMPU_CFG_R00_NSCHKTYPE_MASK          0x00000010UL
    #define XFPD_XMPU_CFG_R00_NSCHKTYPE_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_R00_REGNNS_SHIFT            3UL
    #define XFPD_XMPU_CFG_R00_REGNNS_WIDTH            1UL
    #define XFPD_XMPU_CFG_R00_REGNNS_MASK             0x00000008UL
    #define XFPD_XMPU_CFG_R00_REGNNS_DEFVAL           0x1UL

    #define XFPD_XMPU_CFG_R00_WRALWD_SHIFT            2UL
    #define XFPD_XMPU_CFG_R00_WRALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R00_WRALWD_MASK             0x00000004UL
    #define XFPD_XMPU_CFG_R00_WRALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R00_RDALWD_SHIFT            1UL
    #define XFPD_XMPU_CFG_R00_RDALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R00_RDALWD_MASK             0x00000002UL
    #define XFPD_XMPU_CFG_R00_RDALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R00_EN_SHIFT                0UL
    #define XFPD_XMPU_CFG_R00_EN_WIDTH                1UL
    #define XFPD_XMPU_CFG_R00_EN_MASK                 0x00000001UL
    #define XFPD_XMPU_CFG_R00_EN_DEFVAL               0x0UL

/**
 * Register: XfpdXmpuCfgR01Strt
 */
    #define XFPD_XMPU_CFG_R01_STRT                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000110UL )
    #define XFPD_XMPU_CFG_R01_STRT_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R01_STRT_ADDR_SHIFT         0UL
    #define XFPD_XMPU_CFG_R01_STRT_ADDR_WIDTH         28UL
    #define XFPD_XMPU_CFG_R01_STRT_ADDR_MASK          0x0fffffffUL
    #define XFPD_XMPU_CFG_R01_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XfpdXmpuCfgR01End
 */
    #define XFPD_XMPU_CFG_R01_END                     ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000114UL )
    #define XFPD_XMPU_CFG_R01_END_RSTVAL              0x00000000UL

    #define XFPD_XMPU_CFG_R01_END_ADDR_SHIFT          0UL
    #define XFPD_XMPU_CFG_R01_END_ADDR_WIDTH          28UL
    #define XFPD_XMPU_CFG_R01_END_ADDR_MASK           0x0fffffffUL
    #define XFPD_XMPU_CFG_R01_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XfpdXmpuCfgR01Mstr
 */
    #define XFPD_XMPU_CFG_R01_MSTR                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000118UL )
    #define XFPD_XMPU_CFG_R01_MSTR_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R01_MSTR_MSK_SHIFT          16UL
    #define XFPD_XMPU_CFG_R01_MSTR_MSK_WIDTH          16UL
    #define XFPD_XMPU_CFG_R01_MSTR_MSK_MASK           0xffff0000UL
    #define XFPD_XMPU_CFG_R01_MSTR_MSK_DEFVAL         0x0UL

    #define XFPD_XMPU_CFG_R01_MSTR_ID_SHIFT           0UL
    #define XFPD_XMPU_CFG_R01_MSTR_ID_WIDTH           16UL
    #define XFPD_XMPU_CFG_R01_MSTR_ID_MASK            0x0000ffffUL
    #define XFPD_XMPU_CFG_R01_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgR01
 */
    #define XFPD_XMPU_CFG_R01                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x0000011CUL )
    #define XFPD_XMPU_CFG_R01_RSTVAL                  0x00000008UL

    #define XFPD_XMPU_CFG_R01_NSCHKTYPE_SHIFT         4UL
    #define XFPD_XMPU_CFG_R01_NSCHKTYPE_WIDTH         1UL
    #define XFPD_XMPU_CFG_R01_NSCHKTYPE_MASK          0x00000010UL
    #define XFPD_XMPU_CFG_R01_NSCHKTYPE_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_R01_REGNNS_SHIFT            3UL
    #define XFPD_XMPU_CFG_R01_REGNNS_WIDTH            1UL
    #define XFPD_XMPU_CFG_R01_REGNNS_MASK             0x00000008UL
    #define XFPD_XMPU_CFG_R01_REGNNS_DEFVAL           0x1UL

    #define XFPD_XMPU_CFG_R01_WRALWD_SHIFT            2UL
    #define XFPD_XMPU_CFG_R01_WRALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R01_WRALWD_MASK             0x00000004UL
    #define XFPD_XMPU_CFG_R01_WRALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R01_RDALWD_SHIFT            1UL
    #define XFPD_XMPU_CFG_R01_RDALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R01_RDALWD_MASK             0x00000002UL
    #define XFPD_XMPU_CFG_R01_RDALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R01_EN_SHIFT                0UL
    #define XFPD_XMPU_CFG_R01_EN_WIDTH                1UL
    #define XFPD_XMPU_CFG_R01_EN_MASK                 0x00000001UL
    #define XFPD_XMPU_CFG_R01_EN_DEFVAL               0x0UL

/**
 * Register: XfpdXmpuCfgR02Strt
 */
    #define XFPD_XMPU_CFG_R02_STRT                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000120UL )
    #define XFPD_XMPU_CFG_R02_STRT_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R02_STRT_ADDR_SHIFT         0UL
    #define XFPD_XMPU_CFG_R02_STRT_ADDR_WIDTH         28UL
    #define XFPD_XMPU_CFG_R02_STRT_ADDR_MASK          0x0fffffffUL
    #define XFPD_XMPU_CFG_R02_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XfpdXmpuCfgR02End
 */
    #define XFPD_XMPU_CFG_R02_END                     ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000124UL )
    #define XFPD_XMPU_CFG_R02_END_RSTVAL              0x00000000UL

    #define XFPD_XMPU_CFG_R02_END_ADDR_SHIFT          0UL
    #define XFPD_XMPU_CFG_R02_END_ADDR_WIDTH          28UL
    #define XFPD_XMPU_CFG_R02_END_ADDR_MASK           0x0fffffffUL
    #define XFPD_XMPU_CFG_R02_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XfpdXmpuCfgR02Mstr
 */
    #define XFPD_XMPU_CFG_R02_MSTR                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000128UL )
    #define XFPD_XMPU_CFG_R02_MSTR_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R02_MSTR_MSK_SHIFT          16UL
    #define XFPD_XMPU_CFG_R02_MSTR_MSK_WIDTH          16UL
    #define XFPD_XMPU_CFG_R02_MSTR_MSK_MASK           0xffff0000UL
    #define XFPD_XMPU_CFG_R02_MSTR_MSK_DEFVAL         0x0UL

    #define XFPD_XMPU_CFG_R02_MSTR_ID_SHIFT           0UL
    #define XFPD_XMPU_CFG_R02_MSTR_ID_WIDTH           16UL
    #define XFPD_XMPU_CFG_R02_MSTR_ID_MASK            0x0000ffffUL
    #define XFPD_XMPU_CFG_R02_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgR02
 */
    #define XFPD_XMPU_CFG_R02                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x0000012CUL )
    #define XFPD_XMPU_CFG_R02_RSTVAL                  0x00000008UL

    #define XFPD_XMPU_CFG_R02_NSCHKTYPE_SHIFT         4UL
    #define XFPD_XMPU_CFG_R02_NSCHKTYPE_WIDTH         1UL
    #define XFPD_XMPU_CFG_R02_NSCHKTYPE_MASK          0x00000010UL
    #define XFPD_XMPU_CFG_R02_NSCHKTYPE_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_R02_REGNNS_SHIFT            3UL
    #define XFPD_XMPU_CFG_R02_REGNNS_WIDTH            1UL
    #define XFPD_XMPU_CFG_R02_REGNNS_MASK             0x00000008UL
    #define XFPD_XMPU_CFG_R02_REGNNS_DEFVAL           0x1UL

    #define XFPD_XMPU_CFG_R02_WRALWD_SHIFT            2UL
    #define XFPD_XMPU_CFG_R02_WRALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R02_WRALWD_MASK             0x00000004UL
    #define XFPD_XMPU_CFG_R02_WRALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R02_RDALWD_SHIFT            1UL
    #define XFPD_XMPU_CFG_R02_RDALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R02_RDALWD_MASK             0x00000002UL
    #define XFPD_XMPU_CFG_R02_RDALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R02_EN_SHIFT                0UL
    #define XFPD_XMPU_CFG_R02_EN_WIDTH                1UL
    #define XFPD_XMPU_CFG_R02_EN_MASK                 0x00000001UL
    #define XFPD_XMPU_CFG_R02_EN_DEFVAL               0x0UL

/**
 * Register: XfpdXmpuCfgR03Strt
 */
    #define XFPD_XMPU_CFG_R03_STRT                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000130UL )
    #define XFPD_XMPU_CFG_R03_STRT_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R03_STRT_ADDR_SHIFT         0UL
    #define XFPD_XMPU_CFG_R03_STRT_ADDR_WIDTH         28UL
    #define XFPD_XMPU_CFG_R03_STRT_ADDR_MASK          0x0fffffffUL
    #define XFPD_XMPU_CFG_R03_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XfpdXmpuCfgR03End
 */
    #define XFPD_XMPU_CFG_R03_END                     ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000134UL )
    #define XFPD_XMPU_CFG_R03_END_RSTVAL              0x00000000UL

    #define XFPD_XMPU_CFG_R03_END_ADDR_SHIFT          0UL
    #define XFPD_XMPU_CFG_R03_END_ADDR_WIDTH          28UL
    #define XFPD_XMPU_CFG_R03_END_ADDR_MASK           0x0fffffffUL
    #define XFPD_XMPU_CFG_R03_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XfpdXmpuCfgR03Mstr
 */
    #define XFPD_XMPU_CFG_R03_MSTR                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000138UL )
    #define XFPD_XMPU_CFG_R03_MSTR_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R03_MSTR_MSK_SHIFT          16UL
    #define XFPD_XMPU_CFG_R03_MSTR_MSK_WIDTH          16UL
    #define XFPD_XMPU_CFG_R03_MSTR_MSK_MASK           0xffff0000UL
    #define XFPD_XMPU_CFG_R03_MSTR_MSK_DEFVAL         0x0UL

    #define XFPD_XMPU_CFG_R03_MSTR_ID_SHIFT           0UL
    #define XFPD_XMPU_CFG_R03_MSTR_ID_WIDTH           16UL
    #define XFPD_XMPU_CFG_R03_MSTR_ID_MASK            0x0000ffffUL
    #define XFPD_XMPU_CFG_R03_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgR03
 */
    #define XFPD_XMPU_CFG_R03                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x0000013CUL )
    #define XFPD_XMPU_CFG_R03_RSTVAL                  0x00000008UL

    #define XFPD_XMPU_CFG_R03_NSCHKTYPE_SHIFT         4UL
    #define XFPD_XMPU_CFG_R03_NSCHKTYPE_WIDTH         1UL
    #define XFPD_XMPU_CFG_R03_NSCHKTYPE_MASK          0x00000010UL
    #define XFPD_XMPU_CFG_R03_NSCHKTYPE_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_R03_REGNNS_SHIFT            3UL
    #define XFPD_XMPU_CFG_R03_REGNNS_WIDTH            1UL
    #define XFPD_XMPU_CFG_R03_REGNNS_MASK             0x00000008UL
    #define XFPD_XMPU_CFG_R03_REGNNS_DEFVAL           0x1UL

    #define XFPD_XMPU_CFG_R03_WRALWD_SHIFT            2UL
    #define XFPD_XMPU_CFG_R03_WRALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R03_WRALWD_MASK             0x00000004UL
    #define XFPD_XMPU_CFG_R03_WRALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R03_RDALWD_SHIFT            1UL
    #define XFPD_XMPU_CFG_R03_RDALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R03_RDALWD_MASK             0x00000002UL
    #define XFPD_XMPU_CFG_R03_RDALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R03_EN_SHIFT                0UL
    #define XFPD_XMPU_CFG_R03_EN_WIDTH                1UL
    #define XFPD_XMPU_CFG_R03_EN_MASK                 0x00000001UL
    #define XFPD_XMPU_CFG_R03_EN_DEFVAL               0x0UL

/**
 * Register: XfpdXmpuCfgR04Strt
 */
    #define XFPD_XMPU_CFG_R04_STRT                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000140UL )
    #define XFPD_XMPU_CFG_R04_STRT_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R04_STRT_ADDR_SHIFT         0UL
    #define XFPD_XMPU_CFG_R04_STRT_ADDR_WIDTH         28UL
    #define XFPD_XMPU_CFG_R04_STRT_ADDR_MASK          0x0fffffffUL
    #define XFPD_XMPU_CFG_R04_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XfpdXmpuCfgR04End
 */
    #define XFPD_XMPU_CFG_R04_END                     ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000144UL )
    #define XFPD_XMPU_CFG_R04_END_RSTVAL              0x00000000UL

    #define XFPD_XMPU_CFG_R04_END_ADDR_SHIFT          0UL
    #define XFPD_XMPU_CFG_R04_END_ADDR_WIDTH          28UL
    #define XFPD_XMPU_CFG_R04_END_ADDR_MASK           0x0fffffffUL
    #define XFPD_XMPU_CFG_R04_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XfpdXmpuCfgR04Mstr
 */
    #define XFPD_XMPU_CFG_R04_MSTR                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000148UL )
    #define XFPD_XMPU_CFG_R04_MSTR_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R04_MSTR_MSK_SHIFT          16UL
    #define XFPD_XMPU_CFG_R04_MSTR_MSK_WIDTH          16UL
    #define XFPD_XMPU_CFG_R04_MSTR_MSK_MASK           0xffff0000UL
    #define XFPD_XMPU_CFG_R04_MSTR_MSK_DEFVAL         0x0UL

    #define XFPD_XMPU_CFG_R04_MSTR_ID_SHIFT           0UL
    #define XFPD_XMPU_CFG_R04_MSTR_ID_WIDTH           16UL
    #define XFPD_XMPU_CFG_R04_MSTR_ID_MASK            0x0000ffffUL
    #define XFPD_XMPU_CFG_R04_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgR04
 */
    #define XFPD_XMPU_CFG_R04                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x0000014CUL )
    #define XFPD_XMPU_CFG_R04_RSTVAL                  0x00000008UL

    #define XFPD_XMPU_CFG_R04_NSCHKTYPE_SHIFT         4UL
    #define XFPD_XMPU_CFG_R04_NSCHKTYPE_WIDTH         1UL
    #define XFPD_XMPU_CFG_R04_NSCHKTYPE_MASK          0x00000010UL
    #define XFPD_XMPU_CFG_R04_NSCHKTYPE_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_R04_REGNNS_SHIFT            3UL
    #define XFPD_XMPU_CFG_R04_REGNNS_WIDTH            1UL
    #define XFPD_XMPU_CFG_R04_REGNNS_MASK             0x00000008UL
    #define XFPD_XMPU_CFG_R04_REGNNS_DEFVAL           0x1UL

    #define XFPD_XMPU_CFG_R04_WRALWD_SHIFT            2UL
    #define XFPD_XMPU_CFG_R04_WRALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R04_WRALWD_MASK             0x00000004UL
    #define XFPD_XMPU_CFG_R04_WRALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R04_RDALWD_SHIFT            1UL
    #define XFPD_XMPU_CFG_R04_RDALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R04_RDALWD_MASK             0x00000002UL
    #define XFPD_XMPU_CFG_R04_RDALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R04_EN_SHIFT                0UL
    #define XFPD_XMPU_CFG_R04_EN_WIDTH                1UL
    #define XFPD_XMPU_CFG_R04_EN_MASK                 0x00000001UL
    #define XFPD_XMPU_CFG_R04_EN_DEFVAL               0x0UL

/**
 * Register: XfpdXmpuCfgR05Strt
 */
    #define XFPD_XMPU_CFG_R05_STRT                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000150UL )
    #define XFPD_XMPU_CFG_R05_STRT_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R05_STRT_ADDR_SHIFT         0UL
    #define XFPD_XMPU_CFG_R05_STRT_ADDR_WIDTH         28UL
    #define XFPD_XMPU_CFG_R05_STRT_ADDR_MASK          0x0fffffffUL
    #define XFPD_XMPU_CFG_R05_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XfpdXmpuCfgR05End
 */
    #define XFPD_XMPU_CFG_R05_END                     ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000154UL )
    #define XFPD_XMPU_CFG_R05_END_RSTVAL              0x00000000UL

    #define XFPD_XMPU_CFG_R05_END_ADDR_SHIFT          0UL
    #define XFPD_XMPU_CFG_R05_END_ADDR_WIDTH          28UL
    #define XFPD_XMPU_CFG_R05_END_ADDR_MASK           0x0fffffffUL
    #define XFPD_XMPU_CFG_R05_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XfpdXmpuCfgR05Mstr
 */
    #define XFPD_XMPU_CFG_R05_MSTR                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000158UL )
    #define XFPD_XMPU_CFG_R05_MSTR_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R05_MSTR_MSK_SHIFT          16UL
    #define XFPD_XMPU_CFG_R05_MSTR_MSK_WIDTH          16UL
    #define XFPD_XMPU_CFG_R05_MSTR_MSK_MASK           0xffff0000UL
    #define XFPD_XMPU_CFG_R05_MSTR_MSK_DEFVAL         0x0UL

    #define XFPD_XMPU_CFG_R05_MSTR_ID_SHIFT           0UL
    #define XFPD_XMPU_CFG_R05_MSTR_ID_WIDTH           16UL
    #define XFPD_XMPU_CFG_R05_MSTR_ID_MASK            0x0000ffffUL
    #define XFPD_XMPU_CFG_R05_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgR05
 */
    #define XFPD_XMPU_CFG_R05                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x0000015CUL )
    #define XFPD_XMPU_CFG_R05_RSTVAL                  0x00000008UL

    #define XFPD_XMPU_CFG_R05_NSCHKTYPE_SHIFT         4UL
    #define XFPD_XMPU_CFG_R05_NSCHKTYPE_WIDTH         1UL
    #define XFPD_XMPU_CFG_R05_NSCHKTYPE_MASK          0x00000010UL
    #define XFPD_XMPU_CFG_R05_NSCHKTYPE_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_R05_REGNNS_SHIFT            3UL
    #define XFPD_XMPU_CFG_R05_REGNNS_WIDTH            1UL
    #define XFPD_XMPU_CFG_R05_REGNNS_MASK             0x00000008UL
    #define XFPD_XMPU_CFG_R05_REGNNS_DEFVAL           0x1UL

    #define XFPD_XMPU_CFG_R05_WRALWD_SHIFT            2UL
    #define XFPD_XMPU_CFG_R05_WRALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R05_WRALWD_MASK             0x00000004UL
    #define XFPD_XMPU_CFG_R05_WRALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R05_RDALWD_SHIFT            1UL
    #define XFPD_XMPU_CFG_R05_RDALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R05_RDALWD_MASK             0x00000002UL
    #define XFPD_XMPU_CFG_R05_RDALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R05_EN_SHIFT                0UL
    #define XFPD_XMPU_CFG_R05_EN_WIDTH                1UL
    #define XFPD_XMPU_CFG_R05_EN_MASK                 0x00000001UL
    #define XFPD_XMPU_CFG_R05_EN_DEFVAL               0x0UL

/**
 * Register: XfpdXmpuCfgR06Strt
 */
    #define XFPD_XMPU_CFG_R06_STRT                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000160UL )
    #define XFPD_XMPU_CFG_R06_STRT_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R06_STRT_ADDR_SHIFT         0UL
    #define XFPD_XMPU_CFG_R06_STRT_ADDR_WIDTH         28UL
    #define XFPD_XMPU_CFG_R06_STRT_ADDR_MASK          0x0fffffffUL
    #define XFPD_XMPU_CFG_R06_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XfpdXmpuCfgR06End
 */
    #define XFPD_XMPU_CFG_R06_END                     ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000164UL )
    #define XFPD_XMPU_CFG_R06_END_RSTVAL              0x00000000UL

    #define XFPD_XMPU_CFG_R06_END_ADDR_SHIFT          0UL
    #define XFPD_XMPU_CFG_R06_END_ADDR_WIDTH          28UL
    #define XFPD_XMPU_CFG_R06_END_ADDR_MASK           0x0fffffffUL
    #define XFPD_XMPU_CFG_R06_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XfpdXmpuCfgR06Mstr
 */
    #define XFPD_XMPU_CFG_R06_MSTR                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000168UL )
    #define XFPD_XMPU_CFG_R06_MSTR_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R06_MSTR_MSK_SHIFT          16UL
    #define XFPD_XMPU_CFG_R06_MSTR_MSK_WIDTH          16UL
    #define XFPD_XMPU_CFG_R06_MSTR_MSK_MASK           0xffff0000UL
    #define XFPD_XMPU_CFG_R06_MSTR_MSK_DEFVAL         0x0UL

    #define XFPD_XMPU_CFG_R06_MSTR_ID_SHIFT           0UL
    #define XFPD_XMPU_CFG_R06_MSTR_ID_WIDTH           16UL
    #define XFPD_XMPU_CFG_R06_MSTR_ID_MASK            0x0000ffffUL
    #define XFPD_XMPU_CFG_R06_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgR06
 */
    #define XFPD_XMPU_CFG_R06                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x0000016CUL )
    #define XFPD_XMPU_CFG_R06_RSTVAL                  0x00000008UL

    #define XFPD_XMPU_CFG_R06_NSCHKTYPE_SHIFT         4UL
    #define XFPD_XMPU_CFG_R06_NSCHKTYPE_WIDTH         1UL
    #define XFPD_XMPU_CFG_R06_NSCHKTYPE_MASK          0x00000010UL
    #define XFPD_XMPU_CFG_R06_NSCHKTYPE_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_R06_REGNNS_SHIFT            3UL
    #define XFPD_XMPU_CFG_R06_REGNNS_WIDTH            1UL
    #define XFPD_XMPU_CFG_R06_REGNNS_MASK             0x00000008UL
    #define XFPD_XMPU_CFG_R06_REGNNS_DEFVAL           0x1UL

    #define XFPD_XMPU_CFG_R06_WRALWD_SHIFT            2UL
    #define XFPD_XMPU_CFG_R06_WRALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R06_WRALWD_MASK             0x00000004UL
    #define XFPD_XMPU_CFG_R06_WRALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R06_RDALWD_SHIFT            1UL
    #define XFPD_XMPU_CFG_R06_RDALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R06_RDALWD_MASK             0x00000002UL
    #define XFPD_XMPU_CFG_R06_RDALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R06_EN_SHIFT                0UL
    #define XFPD_XMPU_CFG_R06_EN_WIDTH                1UL
    #define XFPD_XMPU_CFG_R06_EN_MASK                 0x00000001UL
    #define XFPD_XMPU_CFG_R06_EN_DEFVAL               0x0UL

/**
 * Register: XfpdXmpuCfgR07Strt
 */
    #define XFPD_XMPU_CFG_R07_STRT                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000170UL )
    #define XFPD_XMPU_CFG_R07_STRT_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R07_STRT_ADDR_SHIFT         0UL
    #define XFPD_XMPU_CFG_R07_STRT_ADDR_WIDTH         28UL
    #define XFPD_XMPU_CFG_R07_STRT_ADDR_MASK          0x0fffffffUL
    #define XFPD_XMPU_CFG_R07_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XfpdXmpuCfgR07End
 */
    #define XFPD_XMPU_CFG_R07_END                     ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000174UL )
    #define XFPD_XMPU_CFG_R07_END_RSTVAL              0x00000000UL

    #define XFPD_XMPU_CFG_R07_END_ADDR_SHIFT          0UL
    #define XFPD_XMPU_CFG_R07_END_ADDR_WIDTH          28UL
    #define XFPD_XMPU_CFG_R07_END_ADDR_MASK           0x0fffffffUL
    #define XFPD_XMPU_CFG_R07_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XfpdXmpuCfgR07Mstr
 */
    #define XFPD_XMPU_CFG_R07_MSTR                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000178UL )
    #define XFPD_XMPU_CFG_R07_MSTR_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R07_MSTR_MSK_SHIFT          16UL
    #define XFPD_XMPU_CFG_R07_MSTR_MSK_WIDTH          16UL
    #define XFPD_XMPU_CFG_R07_MSTR_MSK_MASK           0xffff0000UL
    #define XFPD_XMPU_CFG_R07_MSTR_MSK_DEFVAL         0x0UL

    #define XFPD_XMPU_CFG_R07_MSTR_ID_SHIFT           0UL
    #define XFPD_XMPU_CFG_R07_MSTR_ID_WIDTH           16UL
    #define XFPD_XMPU_CFG_R07_MSTR_ID_MASK            0x0000ffffUL
    #define XFPD_XMPU_CFG_R07_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgR07
 */
    #define XFPD_XMPU_CFG_R07                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x0000017CUL )
    #define XFPD_XMPU_CFG_R07_RSTVAL                  0x00000008UL

    #define XFPD_XMPU_CFG_R07_NSCHKTYPE_SHIFT         4UL
    #define XFPD_XMPU_CFG_R07_NSCHKTYPE_WIDTH         1UL
    #define XFPD_XMPU_CFG_R07_NSCHKTYPE_MASK          0x00000010UL
    #define XFPD_XMPU_CFG_R07_NSCHKTYPE_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_R07_REGNNS_SHIFT            3UL
    #define XFPD_XMPU_CFG_R07_REGNNS_WIDTH            1UL
    #define XFPD_XMPU_CFG_R07_REGNNS_MASK             0x00000008UL
    #define XFPD_XMPU_CFG_R07_REGNNS_DEFVAL           0x1UL

    #define XFPD_XMPU_CFG_R07_WRALWD_SHIFT            2UL
    #define XFPD_XMPU_CFG_R07_WRALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R07_WRALWD_MASK             0x00000004UL
    #define XFPD_XMPU_CFG_R07_WRALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R07_RDALWD_SHIFT            1UL
    #define XFPD_XMPU_CFG_R07_RDALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R07_RDALWD_MASK             0x00000002UL
    #define XFPD_XMPU_CFG_R07_RDALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R07_EN_SHIFT                0UL
    #define XFPD_XMPU_CFG_R07_EN_WIDTH                1UL
    #define XFPD_XMPU_CFG_R07_EN_MASK                 0x00000001UL
    #define XFPD_XMPU_CFG_R07_EN_DEFVAL               0x0UL

/**
 * Register: XfpdXmpuCfgR08Strt
 */
    #define XFPD_XMPU_CFG_R08_STRT                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000180UL )
    #define XFPD_XMPU_CFG_R08_STRT_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R08_STRT_ADDR_SHIFT         0UL
    #define XFPD_XMPU_CFG_R08_STRT_ADDR_WIDTH         28UL
    #define XFPD_XMPU_CFG_R08_STRT_ADDR_MASK          0x0fffffffUL
    #define XFPD_XMPU_CFG_R08_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XfpdXmpuCfgR08End
 */
    #define XFPD_XMPU_CFG_R08_END                     ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000184UL )
    #define XFPD_XMPU_CFG_R08_END_RSTVAL              0x00000000UL

    #define XFPD_XMPU_CFG_R08_END_ADDR_SHIFT          0UL
    #define XFPD_XMPU_CFG_R08_END_ADDR_WIDTH          28UL
    #define XFPD_XMPU_CFG_R08_END_ADDR_MASK           0x0fffffffUL
    #define XFPD_XMPU_CFG_R08_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XfpdXmpuCfgR08Mstr
 */
    #define XFPD_XMPU_CFG_R08_MSTR                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000188UL )
    #define XFPD_XMPU_CFG_R08_MSTR_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R08_MSTR_MSK_SHIFT          16UL
    #define XFPD_XMPU_CFG_R08_MSTR_MSK_WIDTH          16UL
    #define XFPD_XMPU_CFG_R08_MSTR_MSK_MASK           0xffff0000UL
    #define XFPD_XMPU_CFG_R08_MSTR_MSK_DEFVAL         0x0UL

    #define XFPD_XMPU_CFG_R08_MSTR_ID_SHIFT           0UL
    #define XFPD_XMPU_CFG_R08_MSTR_ID_WIDTH           16UL
    #define XFPD_XMPU_CFG_R08_MSTR_ID_MASK            0x0000ffffUL
    #define XFPD_XMPU_CFG_R08_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgR08
 */
    #define XFPD_XMPU_CFG_R08                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x0000018CUL )
    #define XFPD_XMPU_CFG_R08_RSTVAL                  0x00000008UL

    #define XFPD_XMPU_CFG_R08_NSCHKTYPE_SHIFT         4UL
    #define XFPD_XMPU_CFG_R08_NSCHKTYPE_WIDTH         1UL
    #define XFPD_XMPU_CFG_R08_NSCHKTYPE_MASK          0x00000010UL
    #define XFPD_XMPU_CFG_R08_NSCHKTYPE_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_R08_REGNNS_SHIFT            3UL
    #define XFPD_XMPU_CFG_R08_REGNNS_WIDTH            1UL
    #define XFPD_XMPU_CFG_R08_REGNNS_MASK             0x00000008UL
    #define XFPD_XMPU_CFG_R08_REGNNS_DEFVAL           0x1UL

    #define XFPD_XMPU_CFG_R08_WRALWD_SHIFT            2UL
    #define XFPD_XMPU_CFG_R08_WRALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R08_WRALWD_MASK             0x00000004UL
    #define XFPD_XMPU_CFG_R08_WRALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R08_RDALWD_SHIFT            1UL
    #define XFPD_XMPU_CFG_R08_RDALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R08_RDALWD_MASK             0x00000002UL
    #define XFPD_XMPU_CFG_R08_RDALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R08_EN_SHIFT                0UL
    #define XFPD_XMPU_CFG_R08_EN_WIDTH                1UL
    #define XFPD_XMPU_CFG_R08_EN_MASK                 0x00000001UL
    #define XFPD_XMPU_CFG_R08_EN_DEFVAL               0x0UL

/**
 * Register: XfpdXmpuCfgR09Strt
 */
    #define XFPD_XMPU_CFG_R09_STRT                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000190UL )
    #define XFPD_XMPU_CFG_R09_STRT_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R09_STRT_ADDR_SHIFT         0UL
    #define XFPD_XMPU_CFG_R09_STRT_ADDR_WIDTH         28UL
    #define XFPD_XMPU_CFG_R09_STRT_ADDR_MASK          0x0fffffffUL
    #define XFPD_XMPU_CFG_R09_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XfpdXmpuCfgR09End
 */
    #define XFPD_XMPU_CFG_R09_END                     ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000194UL )
    #define XFPD_XMPU_CFG_R09_END_RSTVAL              0x00000000UL

    #define XFPD_XMPU_CFG_R09_END_ADDR_SHIFT          0UL
    #define XFPD_XMPU_CFG_R09_END_ADDR_WIDTH          28UL
    #define XFPD_XMPU_CFG_R09_END_ADDR_MASK           0x0fffffffUL
    #define XFPD_XMPU_CFG_R09_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XfpdXmpuCfgR09Mstr
 */
    #define XFPD_XMPU_CFG_R09_MSTR                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x00000198UL )
    #define XFPD_XMPU_CFG_R09_MSTR_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R09_MSTR_MSK_SHIFT          16UL
    #define XFPD_XMPU_CFG_R09_MSTR_MSK_WIDTH          16UL
    #define XFPD_XMPU_CFG_R09_MSTR_MSK_MASK           0xffff0000UL
    #define XFPD_XMPU_CFG_R09_MSTR_MSK_DEFVAL         0x0UL

    #define XFPD_XMPU_CFG_R09_MSTR_ID_SHIFT           0UL
    #define XFPD_XMPU_CFG_R09_MSTR_ID_WIDTH           16UL
    #define XFPD_XMPU_CFG_R09_MSTR_ID_MASK            0x0000ffffUL
    #define XFPD_XMPU_CFG_R09_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgR09
 */
    #define XFPD_XMPU_CFG_R09                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x0000019CUL )
    #define XFPD_XMPU_CFG_R09_RSTVAL                  0x00000008UL

    #define XFPD_XMPU_CFG_R09_NSCHKTYPE_SHIFT         4UL
    #define XFPD_XMPU_CFG_R09_NSCHKTYPE_WIDTH         1UL
    #define XFPD_XMPU_CFG_R09_NSCHKTYPE_MASK          0x00000010UL
    #define XFPD_XMPU_CFG_R09_NSCHKTYPE_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_R09_REGNNS_SHIFT            3UL
    #define XFPD_XMPU_CFG_R09_REGNNS_WIDTH            1UL
    #define XFPD_XMPU_CFG_R09_REGNNS_MASK             0x00000008UL
    #define XFPD_XMPU_CFG_R09_REGNNS_DEFVAL           0x1UL

    #define XFPD_XMPU_CFG_R09_WRALWD_SHIFT            2UL
    #define XFPD_XMPU_CFG_R09_WRALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R09_WRALWD_MASK             0x00000004UL
    #define XFPD_XMPU_CFG_R09_WRALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R09_RDALWD_SHIFT            1UL
    #define XFPD_XMPU_CFG_R09_RDALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R09_RDALWD_MASK             0x00000002UL
    #define XFPD_XMPU_CFG_R09_RDALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R09_EN_SHIFT                0UL
    #define XFPD_XMPU_CFG_R09_EN_WIDTH                1UL
    #define XFPD_XMPU_CFG_R09_EN_MASK                 0x00000001UL
    #define XFPD_XMPU_CFG_R09_EN_DEFVAL               0x0UL

/**
 * Register: XfpdXmpuCfgR10Strt
 */
    #define XFPD_XMPU_CFG_R10_STRT                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001A0UL )
    #define XFPD_XMPU_CFG_R10_STRT_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R10_STRT_ADDR_SHIFT         0UL
    #define XFPD_XMPU_CFG_R10_STRT_ADDR_WIDTH         28UL
    #define XFPD_XMPU_CFG_R10_STRT_ADDR_MASK          0x0fffffffUL
    #define XFPD_XMPU_CFG_R10_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XfpdXmpuCfgR10End
 */
    #define XFPD_XMPU_CFG_R10_END                     ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001A4UL )
    #define XFPD_XMPU_CFG_R10_END_RSTVAL              0x00000000UL

    #define XFPD_XMPU_CFG_R10_END_ADDR_SHIFT          0UL
    #define XFPD_XMPU_CFG_R10_END_ADDR_WIDTH          28UL
    #define XFPD_XMPU_CFG_R10_END_ADDR_MASK           0x0fffffffUL
    #define XFPD_XMPU_CFG_R10_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XfpdXmpuCfgR10Mstr
 */
    #define XFPD_XMPU_CFG_R10_MSTR                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001A8UL )
    #define XFPD_XMPU_CFG_R10_MSTR_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R10_MSTR_MSK_SHIFT          16UL
    #define XFPD_XMPU_CFG_R10_MSTR_MSK_WIDTH          16UL
    #define XFPD_XMPU_CFG_R10_MSTR_MSK_MASK           0xffff0000UL
    #define XFPD_XMPU_CFG_R10_MSTR_MSK_DEFVAL         0x0UL

    #define XFPD_XMPU_CFG_R10_MSTR_ID_SHIFT           0UL
    #define XFPD_XMPU_CFG_R10_MSTR_ID_WIDTH           16UL
    #define XFPD_XMPU_CFG_R10_MSTR_ID_MASK            0x0000ffffUL
    #define XFPD_XMPU_CFG_R10_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgR10
 */
    #define XFPD_XMPU_CFG_R10                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001ACUL )
    #define XFPD_XMPU_CFG_R10_RSTVAL                  0x00000008UL

    #define XFPD_XMPU_CFG_R10_NSCHKTYPE_SHIFT         4UL
    #define XFPD_XMPU_CFG_R10_NSCHKTYPE_WIDTH         1UL
    #define XFPD_XMPU_CFG_R10_NSCHKTYPE_MASK          0x00000010UL
    #define XFPD_XMPU_CFG_R10_NSCHKTYPE_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_R10_REGNNS_SHIFT            3UL
    #define XFPD_XMPU_CFG_R10_REGNNS_WIDTH            1UL
    #define XFPD_XMPU_CFG_R10_REGNNS_MASK             0x00000008UL
    #define XFPD_XMPU_CFG_R10_REGNNS_DEFVAL           0x1UL

    #define XFPD_XMPU_CFG_R10_WRALWD_SHIFT            2UL
    #define XFPD_XMPU_CFG_R10_WRALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R10_WRALWD_MASK             0x00000004UL
    #define XFPD_XMPU_CFG_R10_WRALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R10_RDALWD_SHIFT            1UL
    #define XFPD_XMPU_CFG_R10_RDALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R10_RDALWD_MASK             0x00000002UL
    #define XFPD_XMPU_CFG_R10_RDALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R10_EN_SHIFT                0UL
    #define XFPD_XMPU_CFG_R10_EN_WIDTH                1UL
    #define XFPD_XMPU_CFG_R10_EN_MASK                 0x00000001UL
    #define XFPD_XMPU_CFG_R10_EN_DEFVAL               0x0UL

/**
 * Register: XfpdXmpuCfgR11Strt
 */
    #define XFPD_XMPU_CFG_R11_STRT                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001B0UL )
    #define XFPD_XMPU_CFG_R11_STRT_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R11_STRT_ADDR_SHIFT         0UL
    #define XFPD_XMPU_CFG_R11_STRT_ADDR_WIDTH         28UL
    #define XFPD_XMPU_CFG_R11_STRT_ADDR_MASK          0x0fffffffUL
    #define XFPD_XMPU_CFG_R11_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XfpdXmpuCfgR11End
 */
    #define XFPD_XMPU_CFG_R11_END                     ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001B4UL )
    #define XFPD_XMPU_CFG_R11_END_RSTVAL              0x00000000UL

    #define XFPD_XMPU_CFG_R11_END_ADDR_SHIFT          0UL
    #define XFPD_XMPU_CFG_R11_END_ADDR_WIDTH          28UL
    #define XFPD_XMPU_CFG_R11_END_ADDR_MASK           0x0fffffffUL
    #define XFPD_XMPU_CFG_R11_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XfpdXmpuCfgR11Mstr
 */
    #define XFPD_XMPU_CFG_R11_MSTR                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001B8UL )
    #define XFPD_XMPU_CFG_R11_MSTR_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R11_MSTR_MSK_SHIFT          16UL
    #define XFPD_XMPU_CFG_R11_MSTR_MSK_WIDTH          16UL
    #define XFPD_XMPU_CFG_R11_MSTR_MSK_MASK           0xffff0000UL
    #define XFPD_XMPU_CFG_R11_MSTR_MSK_DEFVAL         0x0UL

    #define XFPD_XMPU_CFG_R11_MSTR_ID_SHIFT           0UL
    #define XFPD_XMPU_CFG_R11_MSTR_ID_WIDTH           16UL
    #define XFPD_XMPU_CFG_R11_MSTR_ID_MASK            0x0000ffffUL
    #define XFPD_XMPU_CFG_R11_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgR11
 */
    #define XFPD_XMPU_CFG_R11                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001BCUL )
    #define XFPD_XMPU_CFG_R11_RSTVAL                  0x00000008UL

    #define XFPD_XMPU_CFG_R11_NSCHKTYPE_SHIFT         4UL
    #define XFPD_XMPU_CFG_R11_NSCHKTYPE_WIDTH         1UL
    #define XFPD_XMPU_CFG_R11_NSCHKTYPE_MASK          0x00000010UL
    #define XFPD_XMPU_CFG_R11_NSCHKTYPE_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_R11_REGNNS_SHIFT            3UL
    #define XFPD_XMPU_CFG_R11_REGNNS_WIDTH            1UL
    #define XFPD_XMPU_CFG_R11_REGNNS_MASK             0x00000008UL
    #define XFPD_XMPU_CFG_R11_REGNNS_DEFVAL           0x1UL

    #define XFPD_XMPU_CFG_R11_WRALWD_SHIFT            2UL
    #define XFPD_XMPU_CFG_R11_WRALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R11_WRALWD_MASK             0x00000004UL
    #define XFPD_XMPU_CFG_R11_WRALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R11_RDALWD_SHIFT            1UL
    #define XFPD_XMPU_CFG_R11_RDALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R11_RDALWD_MASK             0x00000002UL
    #define XFPD_XMPU_CFG_R11_RDALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R11_EN_SHIFT                0UL
    #define XFPD_XMPU_CFG_R11_EN_WIDTH                1UL
    #define XFPD_XMPU_CFG_R11_EN_MASK                 0x00000001UL
    #define XFPD_XMPU_CFG_R11_EN_DEFVAL               0x0UL

/**
 * Register: XfpdXmpuCfgR12Strt
 */
    #define XFPD_XMPU_CFG_R12_STRT                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001C0UL )
    #define XFPD_XMPU_CFG_R12_STRT_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R12_STRT_ADDR_SHIFT         0UL
    #define XFPD_XMPU_CFG_R12_STRT_ADDR_WIDTH         28UL
    #define XFPD_XMPU_CFG_R12_STRT_ADDR_MASK          0x0fffffffUL
    #define XFPD_XMPU_CFG_R12_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XfpdXmpuCfgR12End
 */
    #define XFPD_XMPU_CFG_R12_END                     ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001C4UL )
    #define XFPD_XMPU_CFG_R12_END_RSTVAL              0x00000000UL

    #define XFPD_XMPU_CFG_R12_END_ADDR_SHIFT          0UL
    #define XFPD_XMPU_CFG_R12_END_ADDR_WIDTH          28UL
    #define XFPD_XMPU_CFG_R12_END_ADDR_MASK           0x0fffffffUL
    #define XFPD_XMPU_CFG_R12_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XfpdXmpuCfgR12Mstr
 */
    #define XFPD_XMPU_CFG_R12_MSTR                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001C8UL )
    #define XFPD_XMPU_CFG_R12_MSTR_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R12_MSTR_MSK_SHIFT          16UL
    #define XFPD_XMPU_CFG_R12_MSTR_MSK_WIDTH          16UL
    #define XFPD_XMPU_CFG_R12_MSTR_MSK_MASK           0xffff0000UL
    #define XFPD_XMPU_CFG_R12_MSTR_MSK_DEFVAL         0x0UL

    #define XFPD_XMPU_CFG_R12_MSTR_ID_SHIFT           0UL
    #define XFPD_XMPU_CFG_R12_MSTR_ID_WIDTH           16UL
    #define XFPD_XMPU_CFG_R12_MSTR_ID_MASK            0x0000ffffUL
    #define XFPD_XMPU_CFG_R12_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgR12
 */
    #define XFPD_XMPU_CFG_R12                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001CCUL )
    #define XFPD_XMPU_CFG_R12_RSTVAL                  0x00000008UL

    #define XFPD_XMPU_CFG_R12_NSCHKTYPE_SHIFT         4UL
    #define XFPD_XMPU_CFG_R12_NSCHKTYPE_WIDTH         1UL
    #define XFPD_XMPU_CFG_R12_NSCHKTYPE_MASK          0x00000010UL
    #define XFPD_XMPU_CFG_R12_NSCHKTYPE_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_R12_REGNNS_SHIFT            3UL
    #define XFPD_XMPU_CFG_R12_REGNNS_WIDTH            1UL
    #define XFPD_XMPU_CFG_R12_REGNNS_MASK             0x00000008UL
    #define XFPD_XMPU_CFG_R12_REGNNS_DEFVAL           0x1UL

    #define XFPD_XMPU_CFG_R12_WRALWD_SHIFT            2UL
    #define XFPD_XMPU_CFG_R12_WRALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R12_WRALWD_MASK             0x00000004UL
    #define XFPD_XMPU_CFG_R12_WRALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R12_RDALWD_SHIFT            1UL
    #define XFPD_XMPU_CFG_R12_RDALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R12_RDALWD_MASK             0x00000002UL
    #define XFPD_XMPU_CFG_R12_RDALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R12_EN_SHIFT                0UL
    #define XFPD_XMPU_CFG_R12_EN_WIDTH                1UL
    #define XFPD_XMPU_CFG_R12_EN_MASK                 0x00000001UL
    #define XFPD_XMPU_CFG_R12_EN_DEFVAL               0x0UL

/**
 * Register: XfpdXmpuCfgR13Strt
 */
    #define XFPD_XMPU_CFG_R13_STRT                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001D0UL )
    #define XFPD_XMPU_CFG_R13_STRT_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R13_STRT_ADDR_SHIFT         0UL
    #define XFPD_XMPU_CFG_R13_STRT_ADDR_WIDTH         28UL
    #define XFPD_XMPU_CFG_R13_STRT_ADDR_MASK          0x0fffffffUL
    #define XFPD_XMPU_CFG_R13_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XfpdXmpuCfgR13End
 */
    #define XFPD_XMPU_CFG_R13_END                     ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001D4UL )
    #define XFPD_XMPU_CFG_R13_END_RSTVAL              0x00000000UL

    #define XFPD_XMPU_CFG_R13_END_ADDR_SHIFT          0UL
    #define XFPD_XMPU_CFG_R13_END_ADDR_WIDTH          28UL
    #define XFPD_XMPU_CFG_R13_END_ADDR_MASK           0x0fffffffUL
    #define XFPD_XMPU_CFG_R13_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XfpdXmpuCfgR13Mstr
 */
    #define XFPD_XMPU_CFG_R13_MSTR                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001D8UL )
    #define XFPD_XMPU_CFG_R13_MSTR_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R13_MSTR_MSK_SHIFT          16UL
    #define XFPD_XMPU_CFG_R13_MSTR_MSK_WIDTH          16UL
    #define XFPD_XMPU_CFG_R13_MSTR_MSK_MASK           0xffff0000UL
    #define XFPD_XMPU_CFG_R13_MSTR_MSK_DEFVAL         0x0UL

    #define XFPD_XMPU_CFG_R13_MSTR_ID_SHIFT           0UL
    #define XFPD_XMPU_CFG_R13_MSTR_ID_WIDTH           16UL
    #define XFPD_XMPU_CFG_R13_MSTR_ID_MASK            0x0000ffffUL
    #define XFPD_XMPU_CFG_R13_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgR13
 */
    #define XFPD_XMPU_CFG_R13                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001DCUL )
    #define XFPD_XMPU_CFG_R13_RSTVAL                  0x00000008UL

    #define XFPD_XMPU_CFG_R13_NSCHKTYPE_SHIFT         4UL
    #define XFPD_XMPU_CFG_R13_NSCHKTYPE_WIDTH         1UL
    #define XFPD_XMPU_CFG_R13_NSCHKTYPE_MASK          0x00000010UL
    #define XFPD_XMPU_CFG_R13_NSCHKTYPE_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_R13_REGNNS_SHIFT            3UL
    #define XFPD_XMPU_CFG_R13_REGNNS_WIDTH            1UL
    #define XFPD_XMPU_CFG_R13_REGNNS_MASK             0x00000008UL
    #define XFPD_XMPU_CFG_R13_REGNNS_DEFVAL           0x1UL

    #define XFPD_XMPU_CFG_R13_WRALWD_SHIFT            2UL
    #define XFPD_XMPU_CFG_R13_WRALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R13_WRALWD_MASK             0x00000004UL
    #define XFPD_XMPU_CFG_R13_WRALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R13_RDALWD_SHIFT            1UL
    #define XFPD_XMPU_CFG_R13_RDALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R13_RDALWD_MASK             0x00000002UL
    #define XFPD_XMPU_CFG_R13_RDALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R13_EN_SHIFT                0UL
    #define XFPD_XMPU_CFG_R13_EN_WIDTH                1UL
    #define XFPD_XMPU_CFG_R13_EN_MASK                 0x00000001UL
    #define XFPD_XMPU_CFG_R13_EN_DEFVAL               0x0UL

/**
 * Register: XfpdXmpuCfgR14Strt
 */
    #define XFPD_XMPU_CFG_R14_STRT                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001E0UL )
    #define XFPD_XMPU_CFG_R14_STRT_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R14_STRT_ADDR_SHIFT         0UL
    #define XFPD_XMPU_CFG_R14_STRT_ADDR_WIDTH         28UL
    #define XFPD_XMPU_CFG_R14_STRT_ADDR_MASK          0x0fffffffUL
    #define XFPD_XMPU_CFG_R14_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XfpdXmpuCfgR14End
 */
    #define XFPD_XMPU_CFG_R14_END                     ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001E4UL )
    #define XFPD_XMPU_CFG_R14_END_RSTVAL              0x00000000UL

    #define XFPD_XMPU_CFG_R14_END_ADDR_SHIFT          0UL
    #define XFPD_XMPU_CFG_R14_END_ADDR_WIDTH          28UL
    #define XFPD_XMPU_CFG_R14_END_ADDR_MASK           0x0fffffffUL
    #define XFPD_XMPU_CFG_R14_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XfpdXmpuCfgR14Mstr
 */
    #define XFPD_XMPU_CFG_R14_MSTR                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001E8UL )
    #define XFPD_XMPU_CFG_R14_MSTR_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R14_MSTR_MSK_SHIFT          16UL
    #define XFPD_XMPU_CFG_R14_MSTR_MSK_WIDTH          16UL
    #define XFPD_XMPU_CFG_R14_MSTR_MSK_MASK           0xffff0000UL
    #define XFPD_XMPU_CFG_R14_MSTR_MSK_DEFVAL         0x0UL

    #define XFPD_XMPU_CFG_R14_MSTR_ID_SHIFT           0UL
    #define XFPD_XMPU_CFG_R14_MSTR_ID_WIDTH           16UL
    #define XFPD_XMPU_CFG_R14_MSTR_ID_MASK            0x0000ffffUL
    #define XFPD_XMPU_CFG_R14_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgR14
 */
    #define XFPD_XMPU_CFG_R14                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001ECUL )
    #define XFPD_XMPU_CFG_R14_RSTVAL                  0x00000008UL

    #define XFPD_XMPU_CFG_R14_NSCHKTYPE_SHIFT         4UL
    #define XFPD_XMPU_CFG_R14_NSCHKTYPE_WIDTH         1UL
    #define XFPD_XMPU_CFG_R14_NSCHKTYPE_MASK          0x00000010UL
    #define XFPD_XMPU_CFG_R14_NSCHKTYPE_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_R14_REGNNS_SHIFT            3UL
    #define XFPD_XMPU_CFG_R14_REGNNS_WIDTH            1UL
    #define XFPD_XMPU_CFG_R14_REGNNS_MASK             0x00000008UL
    #define XFPD_XMPU_CFG_R14_REGNNS_DEFVAL           0x1UL

    #define XFPD_XMPU_CFG_R14_WRALWD_SHIFT            2UL
    #define XFPD_XMPU_CFG_R14_WRALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R14_WRALWD_MASK             0x00000004UL
    #define XFPD_XMPU_CFG_R14_WRALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R14_RDALWD_SHIFT            1UL
    #define XFPD_XMPU_CFG_R14_RDALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R14_RDALWD_MASK             0x00000002UL
    #define XFPD_XMPU_CFG_R14_RDALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R14_EN_SHIFT                0UL
    #define XFPD_XMPU_CFG_R14_EN_WIDTH                1UL
    #define XFPD_XMPU_CFG_R14_EN_MASK                 0x00000001UL
    #define XFPD_XMPU_CFG_R14_EN_DEFVAL               0x0UL

/**
 * Register: XfpdXmpuCfgR15Strt
 */
    #define XFPD_XMPU_CFG_R15_STRT                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001F0UL )
    #define XFPD_XMPU_CFG_R15_STRT_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R15_STRT_ADDR_SHIFT         0UL
    #define XFPD_XMPU_CFG_R15_STRT_ADDR_WIDTH         28UL
    #define XFPD_XMPU_CFG_R15_STRT_ADDR_MASK          0x0fffffffUL
    #define XFPD_XMPU_CFG_R15_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XfpdXmpuCfgR15End
 */
    #define XFPD_XMPU_CFG_R15_END                     ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001F4UL )
    #define XFPD_XMPU_CFG_R15_END_RSTVAL              0x00000000UL

    #define XFPD_XMPU_CFG_R15_END_ADDR_SHIFT          0UL
    #define XFPD_XMPU_CFG_R15_END_ADDR_WIDTH          28UL
    #define XFPD_XMPU_CFG_R15_END_ADDR_MASK           0x0fffffffUL
    #define XFPD_XMPU_CFG_R15_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XfpdXmpuCfgR15Mstr
 */
    #define XFPD_XMPU_CFG_R15_MSTR                    ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001F8UL )
    #define XFPD_XMPU_CFG_R15_MSTR_RSTVAL             0x00000000UL

    #define XFPD_XMPU_CFG_R15_MSTR_MSK_SHIFT          16UL
    #define XFPD_XMPU_CFG_R15_MSTR_MSK_WIDTH          16UL
    #define XFPD_XMPU_CFG_R15_MSTR_MSK_MASK           0xffff0000UL
    #define XFPD_XMPU_CFG_R15_MSTR_MSK_DEFVAL         0x0UL

    #define XFPD_XMPU_CFG_R15_MSTR_ID_SHIFT           0UL
    #define XFPD_XMPU_CFG_R15_MSTR_ID_WIDTH           16UL
    #define XFPD_XMPU_CFG_R15_MSTR_ID_MASK            0x0000ffffUL
    #define XFPD_XMPU_CFG_R15_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XfpdXmpuCfgR15
 */
    #define XFPD_XMPU_CFG_R15                         ( ( XFPD_XMPU_CFG_BASEADDR ) +0x000001FCUL )
    #define XFPD_XMPU_CFG_R15_RSTVAL                  0x00000008UL

    #define XFPD_XMPU_CFG_R15_NSCHKTYPE_SHIFT         4UL
    #define XFPD_XMPU_CFG_R15_NSCHKTYPE_WIDTH         1UL
    #define XFPD_XMPU_CFG_R15_NSCHKTYPE_MASK          0x00000010UL
    #define XFPD_XMPU_CFG_R15_NSCHKTYPE_DEFVAL        0x0UL

    #define XFPD_XMPU_CFG_R15_REGNNS_SHIFT            3UL
    #define XFPD_XMPU_CFG_R15_REGNNS_WIDTH            1UL
    #define XFPD_XMPU_CFG_R15_REGNNS_MASK             0x00000008UL
    #define XFPD_XMPU_CFG_R15_REGNNS_DEFVAL           0x1UL

    #define XFPD_XMPU_CFG_R15_WRALWD_SHIFT            2UL
    #define XFPD_XMPU_CFG_R15_WRALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R15_WRALWD_MASK             0x00000004UL
    #define XFPD_XMPU_CFG_R15_WRALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R15_RDALWD_SHIFT            1UL
    #define XFPD_XMPU_CFG_R15_RDALWD_WIDTH            1UL
    #define XFPD_XMPU_CFG_R15_RDALWD_MASK             0x00000002UL
    #define XFPD_XMPU_CFG_R15_RDALWD_DEFVAL           0x0UL

    #define XFPD_XMPU_CFG_R15_EN_SHIFT                0UL
    #define XFPD_XMPU_CFG_R15_EN_WIDTH                1UL
    #define XFPD_XMPU_CFG_R15_EN_MASK                 0x00000001UL
    #define XFPD_XMPU_CFG_R15_EN_DEFVAL               0x0UL


    #ifdef __cplusplus
}
    #endif

#endif /* __XFPD_XMPU_CFG_H__ */
