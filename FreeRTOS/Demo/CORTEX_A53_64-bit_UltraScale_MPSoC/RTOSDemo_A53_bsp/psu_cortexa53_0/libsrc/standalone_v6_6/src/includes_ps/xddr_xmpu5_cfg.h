/* ### HEADER ### */

#ifndef __XDDR_XMPU5_CFG_H__
    #define __XDDR_XMPU5_CFG_H__


    #ifdef __cplusplus
    extern "C" {
    #endif

/**
 * XddrXmpu5Cfg Base Address
 */
    #define XDDR_XMPU5_CFG_BASEADDR                    0xFD050000UL

/**
 * Register: XddrXmpu5CfgCtrl
 */
    #define XDDR_XMPU5_CFG_CTRL                        ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000000UL )
    #define XDDR_XMPU5_CFG_CTRL_RSTVAL                 0x00000003UL

    #define XDDR_XMPU5_CFG_CTRL_ALIGNCFG_SHIFT         3UL
    #define XDDR_XMPU5_CFG_CTRL_ALIGNCFG_WIDTH         1UL
    #define XDDR_XMPU5_CFG_CTRL_ALIGNCFG_MASK          0x00000008UL
    #define XDDR_XMPU5_CFG_CTRL_ALIGNCFG_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_CTRL_POISONCFG_SHIFT        2UL
    #define XDDR_XMPU5_CFG_CTRL_POISONCFG_WIDTH        1UL
    #define XDDR_XMPU5_CFG_CTRL_POISONCFG_MASK         0x00000004UL
    #define XDDR_XMPU5_CFG_CTRL_POISONCFG_DEFVAL       0x0UL

    #define XDDR_XMPU5_CFG_CTRL_DEFWRALWD_SHIFT        1UL
    #define XDDR_XMPU5_CFG_CTRL_DEFWRALWD_WIDTH        1UL
    #define XDDR_XMPU5_CFG_CTRL_DEFWRALWD_MASK         0x00000002UL
    #define XDDR_XMPU5_CFG_CTRL_DEFWRALWD_DEFVAL       0x1UL

    #define XDDR_XMPU5_CFG_CTRL_DEFRDALWD_SHIFT        0UL
    #define XDDR_XMPU5_CFG_CTRL_DEFRDALWD_WIDTH        1UL
    #define XDDR_XMPU5_CFG_CTRL_DEFRDALWD_MASK         0x00000001UL
    #define XDDR_XMPU5_CFG_CTRL_DEFRDALWD_DEFVAL       0x1UL

/**
 * Register: XddrXmpu5CfgErrSts1
 */
    #define XDDR_XMPU5_CFG_ERR_STS1                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000004UL )
    #define XDDR_XMPU5_CFG_ERR_STS1_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_ERR_STS1_AXI_ADDR_SHIFT     0UL
    #define XDDR_XMPU5_CFG_ERR_STS1_AXI_ADDR_WIDTH     32UL
    #define XDDR_XMPU5_CFG_ERR_STS1_AXI_ADDR_MASK      0xffffffffUL
    #define XDDR_XMPU5_CFG_ERR_STS1_AXI_ADDR_DEFVAL    0x0UL

/**
 * Register: XddrXmpu5CfgErrSts2
 */
    #define XDDR_XMPU5_CFG_ERR_STS2                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000008UL )
    #define XDDR_XMPU5_CFG_ERR_STS2_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_ERR_STS2_AXI_ID_SHIFT       0UL
    #define XDDR_XMPU5_CFG_ERR_STS2_AXI_ID_WIDTH       16UL
    #define XDDR_XMPU5_CFG_ERR_STS2_AXI_ID_MASK        0x0000ffffUL
    #define XDDR_XMPU5_CFG_ERR_STS2_AXI_ID_DEFVAL      0x0UL

/**
 * Register: XddrXmpu5CfgPoison
 */
    #define XDDR_XMPU5_CFG_POISON                      ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x0000000CUL )
    #define XDDR_XMPU5_CFG_POISON_RSTVAL               0x00000000UL

    #define XDDR_XMPU5_CFG_POISON_ATTRIB_SHIFT         20UL
    #define XDDR_XMPU5_CFG_POISON_ATTRIB_WIDTH         12UL
    #define XDDR_XMPU5_CFG_POISON_ATTRIB_MASK          0xfff00000UL
    #define XDDR_XMPU5_CFG_POISON_ATTRIB_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_POISON_BASE_SHIFT           0UL
    #define XDDR_XMPU5_CFG_POISON_BASE_WIDTH           20UL
    #define XDDR_XMPU5_CFG_POISON_BASE_MASK            0x000fffffUL
    #define XDDR_XMPU5_CFG_POISON_BASE_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgIsr
 */
    #define XDDR_XMPU5_CFG_ISR                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000010UL )
    #define XDDR_XMPU5_CFG_ISR_RSTVAL                  0x00000000UL

    #define XDDR_XMPU5_CFG_ISR_SECURTYVIO_SHIFT        3UL
    #define XDDR_XMPU5_CFG_ISR_SECURTYVIO_WIDTH        1UL
    #define XDDR_XMPU5_CFG_ISR_SECURTYVIO_MASK         0x00000008UL
    #define XDDR_XMPU5_CFG_ISR_SECURTYVIO_DEFVAL       0x0UL

    #define XDDR_XMPU5_CFG_ISR_WRPERMVIO_SHIFT         2UL
    #define XDDR_XMPU5_CFG_ISR_WRPERMVIO_WIDTH         1UL
    #define XDDR_XMPU5_CFG_ISR_WRPERMVIO_MASK          0x00000004UL
    #define XDDR_XMPU5_CFG_ISR_WRPERMVIO_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_ISR_RDPERMVIO_SHIFT         1UL
    #define XDDR_XMPU5_CFG_ISR_RDPERMVIO_WIDTH         1UL
    #define XDDR_XMPU5_CFG_ISR_RDPERMVIO_MASK          0x00000002UL
    #define XDDR_XMPU5_CFG_ISR_RDPERMVIO_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_ISR_INV_APB_SHIFT           0UL
    #define XDDR_XMPU5_CFG_ISR_INV_APB_WIDTH           1UL
    #define XDDR_XMPU5_CFG_ISR_INV_APB_MASK            0x00000001UL
    #define XDDR_XMPU5_CFG_ISR_INV_APB_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgImr
 */
    #define XDDR_XMPU5_CFG_IMR                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000014UL )
    #define XDDR_XMPU5_CFG_IMR_RSTVAL                  0x0000000fUL

    #define XDDR_XMPU5_CFG_IMR_SECURTYVIO_SHIFT        3UL
    #define XDDR_XMPU5_CFG_IMR_SECURTYVIO_WIDTH        1UL
    #define XDDR_XMPU5_CFG_IMR_SECURTYVIO_MASK         0x00000008UL
    #define XDDR_XMPU5_CFG_IMR_SECURTYVIO_DEFVAL       0x1UL

    #define XDDR_XMPU5_CFG_IMR_WRPERMVIO_SHIFT         2UL
    #define XDDR_XMPU5_CFG_IMR_WRPERMVIO_WIDTH         1UL
    #define XDDR_XMPU5_CFG_IMR_WRPERMVIO_MASK          0x00000004UL
    #define XDDR_XMPU5_CFG_IMR_WRPERMVIO_DEFVAL        0x1UL

    #define XDDR_XMPU5_CFG_IMR_RDPERMVIO_SHIFT         1UL
    #define XDDR_XMPU5_CFG_IMR_RDPERMVIO_WIDTH         1UL
    #define XDDR_XMPU5_CFG_IMR_RDPERMVIO_MASK          0x00000002UL
    #define XDDR_XMPU5_CFG_IMR_RDPERMVIO_DEFVAL        0x1UL

    #define XDDR_XMPU5_CFG_IMR_INV_APB_SHIFT           0UL
    #define XDDR_XMPU5_CFG_IMR_INV_APB_WIDTH           1UL
    #define XDDR_XMPU5_CFG_IMR_INV_APB_MASK            0x00000001UL
    #define XDDR_XMPU5_CFG_IMR_INV_APB_DEFVAL          0x1UL

/**
 * Register: XddrXmpu5CfgIen
 */
    #define XDDR_XMPU5_CFG_IEN                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000018UL )
    #define XDDR_XMPU5_CFG_IEN_RSTVAL                  0x00000000UL

    #define XDDR_XMPU5_CFG_IEN_SECURTYVIO_SHIFT        3UL
    #define XDDR_XMPU5_CFG_IEN_SECURTYVIO_WIDTH        1UL
    #define XDDR_XMPU5_CFG_IEN_SECURTYVIO_MASK         0x00000008UL
    #define XDDR_XMPU5_CFG_IEN_SECURTYVIO_DEFVAL       0x0UL

    #define XDDR_XMPU5_CFG_IEN_WRPERMVIO_SHIFT         2UL
    #define XDDR_XMPU5_CFG_IEN_WRPERMVIO_WIDTH         1UL
    #define XDDR_XMPU5_CFG_IEN_WRPERMVIO_MASK          0x00000004UL
    #define XDDR_XMPU5_CFG_IEN_WRPERMVIO_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_IEN_RDPERMVIO_SHIFT         1UL
    #define XDDR_XMPU5_CFG_IEN_RDPERMVIO_WIDTH         1UL
    #define XDDR_XMPU5_CFG_IEN_RDPERMVIO_MASK          0x00000002UL
    #define XDDR_XMPU5_CFG_IEN_RDPERMVIO_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_IEN_INV_APB_SHIFT           0UL
    #define XDDR_XMPU5_CFG_IEN_INV_APB_WIDTH           1UL
    #define XDDR_XMPU5_CFG_IEN_INV_APB_MASK            0x00000001UL
    #define XDDR_XMPU5_CFG_IEN_INV_APB_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgIds
 */
    #define XDDR_XMPU5_CFG_IDS                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x0000001CUL )
    #define XDDR_XMPU5_CFG_IDS_RSTVAL                  0x00000000UL

    #define XDDR_XMPU5_CFG_IDS_SECURTYVIO_SHIFT        3UL
    #define XDDR_XMPU5_CFG_IDS_SECURTYVIO_WIDTH        1UL
    #define XDDR_XMPU5_CFG_IDS_SECURTYVIO_MASK         0x00000008UL
    #define XDDR_XMPU5_CFG_IDS_SECURTYVIO_DEFVAL       0x0UL

    #define XDDR_XMPU5_CFG_IDS_WRPERMVIO_SHIFT         2UL
    #define XDDR_XMPU5_CFG_IDS_WRPERMVIO_WIDTH         1UL
    #define XDDR_XMPU5_CFG_IDS_WRPERMVIO_MASK          0x00000004UL
    #define XDDR_XMPU5_CFG_IDS_WRPERMVIO_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_IDS_RDPERMVIO_SHIFT         1UL
    #define XDDR_XMPU5_CFG_IDS_RDPERMVIO_WIDTH         1UL
    #define XDDR_XMPU5_CFG_IDS_RDPERMVIO_MASK          0x00000002UL
    #define XDDR_XMPU5_CFG_IDS_RDPERMVIO_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_IDS_INV_APB_SHIFT           0UL
    #define XDDR_XMPU5_CFG_IDS_INV_APB_WIDTH           1UL
    #define XDDR_XMPU5_CFG_IDS_INV_APB_MASK            0x00000001UL
    #define XDDR_XMPU5_CFG_IDS_INV_APB_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgLock
 */
    #define XDDR_XMPU5_CFG_LOCK                        ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000020UL )
    #define XDDR_XMPU5_CFG_LOCK_RSTVAL                 0x00000000UL

    #define XDDR_XMPU5_CFG_LOCK_REGWRDIS_SHIFT         0UL
    #define XDDR_XMPU5_CFG_LOCK_REGWRDIS_WIDTH         1UL
    #define XDDR_XMPU5_CFG_LOCK_REGWRDIS_MASK          0x00000001UL
    #define XDDR_XMPU5_CFG_LOCK_REGWRDIS_DEFVAL        0x0UL

/**
 * Register: XddrXmpu5CfgR00Strt
 */
    #define XDDR_XMPU5_CFG_R00_STRT                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000100UL )
    #define XDDR_XMPU5_CFG_R00_STRT_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R00_STRT_ADDR_SHIFT         0UL
    #define XDDR_XMPU5_CFG_R00_STRT_ADDR_WIDTH         28UL
    #define XDDR_XMPU5_CFG_R00_STRT_ADDR_MASK          0x0fffffffUL
    #define XDDR_XMPU5_CFG_R00_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XddrXmpu5CfgR00End
 */
    #define XDDR_XMPU5_CFG_R00_END                     ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000104UL )
    #define XDDR_XMPU5_CFG_R00_END_RSTVAL              0x00000000UL

    #define XDDR_XMPU5_CFG_R00_END_ADDR_SHIFT          0UL
    #define XDDR_XMPU5_CFG_R00_END_ADDR_WIDTH          28UL
    #define XDDR_XMPU5_CFG_R00_END_ADDR_MASK           0x0fffffffUL
    #define XDDR_XMPU5_CFG_R00_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XddrXmpu5CfgR00Mstr
 */
    #define XDDR_XMPU5_CFG_R00_MSTR                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000108UL )
    #define XDDR_XMPU5_CFG_R00_MSTR_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R00_MSTR_MSK_SHIFT          16UL
    #define XDDR_XMPU5_CFG_R00_MSTR_MSK_WIDTH          16UL
    #define XDDR_XMPU5_CFG_R00_MSTR_MSK_MASK           0xffff0000UL
    #define XDDR_XMPU5_CFG_R00_MSTR_MSK_DEFVAL         0x0UL

    #define XDDR_XMPU5_CFG_R00_MSTR_ID_SHIFT           0UL
    #define XDDR_XMPU5_CFG_R00_MSTR_ID_WIDTH           16UL
    #define XDDR_XMPU5_CFG_R00_MSTR_ID_MASK            0x0000ffffUL
    #define XDDR_XMPU5_CFG_R00_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgR00
 */
    #define XDDR_XMPU5_CFG_R00                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x0000010CUL )
    #define XDDR_XMPU5_CFG_R00_RSTVAL                  0x00000008UL

    #define XDDR_XMPU5_CFG_R00_NSCHKTYPE_SHIFT         4UL
    #define XDDR_XMPU5_CFG_R00_NSCHKTYPE_WIDTH         1UL
    #define XDDR_XMPU5_CFG_R00_NSCHKTYPE_MASK          0x00000010UL
    #define XDDR_XMPU5_CFG_R00_NSCHKTYPE_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_R00_REGNNS_SHIFT            3UL
    #define XDDR_XMPU5_CFG_R00_REGNNS_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R00_REGNNS_MASK             0x00000008UL
    #define XDDR_XMPU5_CFG_R00_REGNNS_DEFVAL           0x1UL

    #define XDDR_XMPU5_CFG_R00_WRALWD_SHIFT            2UL
    #define XDDR_XMPU5_CFG_R00_WRALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R00_WRALWD_MASK             0x00000004UL
    #define XDDR_XMPU5_CFG_R00_WRALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R00_RDALWD_SHIFT            1UL
    #define XDDR_XMPU5_CFG_R00_RDALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R00_RDALWD_MASK             0x00000002UL
    #define XDDR_XMPU5_CFG_R00_RDALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R00_EN_SHIFT                0UL
    #define XDDR_XMPU5_CFG_R00_EN_WIDTH                1UL
    #define XDDR_XMPU5_CFG_R00_EN_MASK                 0x00000001UL
    #define XDDR_XMPU5_CFG_R00_EN_DEFVAL               0x0UL

/**
 * Register: XddrXmpu5CfgR01Strt
 */
    #define XDDR_XMPU5_CFG_R01_STRT                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000110UL )
    #define XDDR_XMPU5_CFG_R01_STRT_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R01_STRT_ADDR_SHIFT         0UL
    #define XDDR_XMPU5_CFG_R01_STRT_ADDR_WIDTH         28UL
    #define XDDR_XMPU5_CFG_R01_STRT_ADDR_MASK          0x0fffffffUL
    #define XDDR_XMPU5_CFG_R01_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XddrXmpu5CfgR01End
 */
    #define XDDR_XMPU5_CFG_R01_END                     ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000114UL )
    #define XDDR_XMPU5_CFG_R01_END_RSTVAL              0x00000000UL

    #define XDDR_XMPU5_CFG_R01_END_ADDR_SHIFT          0UL
    #define XDDR_XMPU5_CFG_R01_END_ADDR_WIDTH          28UL
    #define XDDR_XMPU5_CFG_R01_END_ADDR_MASK           0x0fffffffUL
    #define XDDR_XMPU5_CFG_R01_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XddrXmpu5CfgR01Mstr
 */
    #define XDDR_XMPU5_CFG_R01_MSTR                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000118UL )
    #define XDDR_XMPU5_CFG_R01_MSTR_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R01_MSTR_MSK_SHIFT          16UL
    #define XDDR_XMPU5_CFG_R01_MSTR_MSK_WIDTH          16UL
    #define XDDR_XMPU5_CFG_R01_MSTR_MSK_MASK           0xffff0000UL
    #define XDDR_XMPU5_CFG_R01_MSTR_MSK_DEFVAL         0x0UL

    #define XDDR_XMPU5_CFG_R01_MSTR_ID_SHIFT           0UL
    #define XDDR_XMPU5_CFG_R01_MSTR_ID_WIDTH           16UL
    #define XDDR_XMPU5_CFG_R01_MSTR_ID_MASK            0x0000ffffUL
    #define XDDR_XMPU5_CFG_R01_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgR01
 */
    #define XDDR_XMPU5_CFG_R01                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x0000011CUL )
    #define XDDR_XMPU5_CFG_R01_RSTVAL                  0x00000008UL

    #define XDDR_XMPU5_CFG_R01_NSCHKTYPE_SHIFT         4UL
    #define XDDR_XMPU5_CFG_R01_NSCHKTYPE_WIDTH         1UL
    #define XDDR_XMPU5_CFG_R01_NSCHKTYPE_MASK          0x00000010UL
    #define XDDR_XMPU5_CFG_R01_NSCHKTYPE_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_R01_REGNNS_SHIFT            3UL
    #define XDDR_XMPU5_CFG_R01_REGNNS_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R01_REGNNS_MASK             0x00000008UL
    #define XDDR_XMPU5_CFG_R01_REGNNS_DEFVAL           0x1UL

    #define XDDR_XMPU5_CFG_R01_WRALWD_SHIFT            2UL
    #define XDDR_XMPU5_CFG_R01_WRALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R01_WRALWD_MASK             0x00000004UL
    #define XDDR_XMPU5_CFG_R01_WRALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R01_RDALWD_SHIFT            1UL
    #define XDDR_XMPU5_CFG_R01_RDALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R01_RDALWD_MASK             0x00000002UL
    #define XDDR_XMPU5_CFG_R01_RDALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R01_EN_SHIFT                0UL
    #define XDDR_XMPU5_CFG_R01_EN_WIDTH                1UL
    #define XDDR_XMPU5_CFG_R01_EN_MASK                 0x00000001UL
    #define XDDR_XMPU5_CFG_R01_EN_DEFVAL               0x0UL

/**
 * Register: XddrXmpu5CfgR02Strt
 */
    #define XDDR_XMPU5_CFG_R02_STRT                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000120UL )
    #define XDDR_XMPU5_CFG_R02_STRT_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R02_STRT_ADDR_SHIFT         0UL
    #define XDDR_XMPU5_CFG_R02_STRT_ADDR_WIDTH         28UL
    #define XDDR_XMPU5_CFG_R02_STRT_ADDR_MASK          0x0fffffffUL
    #define XDDR_XMPU5_CFG_R02_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XddrXmpu5CfgR02End
 */
    #define XDDR_XMPU5_CFG_R02_END                     ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000124UL )
    #define XDDR_XMPU5_CFG_R02_END_RSTVAL              0x00000000UL

    #define XDDR_XMPU5_CFG_R02_END_ADDR_SHIFT          0UL
    #define XDDR_XMPU5_CFG_R02_END_ADDR_WIDTH          28UL
    #define XDDR_XMPU5_CFG_R02_END_ADDR_MASK           0x0fffffffUL
    #define XDDR_XMPU5_CFG_R02_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XddrXmpu5CfgR02Mstr
 */
    #define XDDR_XMPU5_CFG_R02_MSTR                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000128UL )
    #define XDDR_XMPU5_CFG_R02_MSTR_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R02_MSTR_MSK_SHIFT          16UL
    #define XDDR_XMPU5_CFG_R02_MSTR_MSK_WIDTH          16UL
    #define XDDR_XMPU5_CFG_R02_MSTR_MSK_MASK           0xffff0000UL
    #define XDDR_XMPU5_CFG_R02_MSTR_MSK_DEFVAL         0x0UL

    #define XDDR_XMPU5_CFG_R02_MSTR_ID_SHIFT           0UL
    #define XDDR_XMPU5_CFG_R02_MSTR_ID_WIDTH           16UL
    #define XDDR_XMPU5_CFG_R02_MSTR_ID_MASK            0x0000ffffUL
    #define XDDR_XMPU5_CFG_R02_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgR02
 */
    #define XDDR_XMPU5_CFG_R02                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x0000012CUL )
    #define XDDR_XMPU5_CFG_R02_RSTVAL                  0x00000008UL

    #define XDDR_XMPU5_CFG_R02_NSCHKTYPE_SHIFT         4UL
    #define XDDR_XMPU5_CFG_R02_NSCHKTYPE_WIDTH         1UL
    #define XDDR_XMPU5_CFG_R02_NSCHKTYPE_MASK          0x00000010UL
    #define XDDR_XMPU5_CFG_R02_NSCHKTYPE_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_R02_REGNNS_SHIFT            3UL
    #define XDDR_XMPU5_CFG_R02_REGNNS_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R02_REGNNS_MASK             0x00000008UL
    #define XDDR_XMPU5_CFG_R02_REGNNS_DEFVAL           0x1UL

    #define XDDR_XMPU5_CFG_R02_WRALWD_SHIFT            2UL
    #define XDDR_XMPU5_CFG_R02_WRALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R02_WRALWD_MASK             0x00000004UL
    #define XDDR_XMPU5_CFG_R02_WRALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R02_RDALWD_SHIFT            1UL
    #define XDDR_XMPU5_CFG_R02_RDALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R02_RDALWD_MASK             0x00000002UL
    #define XDDR_XMPU5_CFG_R02_RDALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R02_EN_SHIFT                0UL
    #define XDDR_XMPU5_CFG_R02_EN_WIDTH                1UL
    #define XDDR_XMPU5_CFG_R02_EN_MASK                 0x00000001UL
    #define XDDR_XMPU5_CFG_R02_EN_DEFVAL               0x0UL

/**
 * Register: XddrXmpu5CfgR03Strt
 */
    #define XDDR_XMPU5_CFG_R03_STRT                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000130UL )
    #define XDDR_XMPU5_CFG_R03_STRT_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R03_STRT_ADDR_SHIFT         0UL
    #define XDDR_XMPU5_CFG_R03_STRT_ADDR_WIDTH         28UL
    #define XDDR_XMPU5_CFG_R03_STRT_ADDR_MASK          0x0fffffffUL
    #define XDDR_XMPU5_CFG_R03_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XddrXmpu5CfgR03End
 */
    #define XDDR_XMPU5_CFG_R03_END                     ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000134UL )
    #define XDDR_XMPU5_CFG_R03_END_RSTVAL              0x00000000UL

    #define XDDR_XMPU5_CFG_R03_END_ADDR_SHIFT          0UL
    #define XDDR_XMPU5_CFG_R03_END_ADDR_WIDTH          28UL
    #define XDDR_XMPU5_CFG_R03_END_ADDR_MASK           0x0fffffffUL
    #define XDDR_XMPU5_CFG_R03_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XddrXmpu5CfgR03Mstr
 */
    #define XDDR_XMPU5_CFG_R03_MSTR                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000138UL )
    #define XDDR_XMPU5_CFG_R03_MSTR_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R03_MSTR_MSK_SHIFT          16UL
    #define XDDR_XMPU5_CFG_R03_MSTR_MSK_WIDTH          16UL
    #define XDDR_XMPU5_CFG_R03_MSTR_MSK_MASK           0xffff0000UL
    #define XDDR_XMPU5_CFG_R03_MSTR_MSK_DEFVAL         0x0UL

    #define XDDR_XMPU5_CFG_R03_MSTR_ID_SHIFT           0UL
    #define XDDR_XMPU5_CFG_R03_MSTR_ID_WIDTH           16UL
    #define XDDR_XMPU5_CFG_R03_MSTR_ID_MASK            0x0000ffffUL
    #define XDDR_XMPU5_CFG_R03_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgR03
 */
    #define XDDR_XMPU5_CFG_R03                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x0000013CUL )
    #define XDDR_XMPU5_CFG_R03_RSTVAL                  0x00000008UL

    #define XDDR_XMPU5_CFG_R03_NSCHKTYPE_SHIFT         4UL
    #define XDDR_XMPU5_CFG_R03_NSCHKTYPE_WIDTH         1UL
    #define XDDR_XMPU5_CFG_R03_NSCHKTYPE_MASK          0x00000010UL
    #define XDDR_XMPU5_CFG_R03_NSCHKTYPE_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_R03_REGNNS_SHIFT            3UL
    #define XDDR_XMPU5_CFG_R03_REGNNS_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R03_REGNNS_MASK             0x00000008UL
    #define XDDR_XMPU5_CFG_R03_REGNNS_DEFVAL           0x1UL

    #define XDDR_XMPU5_CFG_R03_WRALWD_SHIFT            2UL
    #define XDDR_XMPU5_CFG_R03_WRALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R03_WRALWD_MASK             0x00000004UL
    #define XDDR_XMPU5_CFG_R03_WRALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R03_RDALWD_SHIFT            1UL
    #define XDDR_XMPU5_CFG_R03_RDALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R03_RDALWD_MASK             0x00000002UL
    #define XDDR_XMPU5_CFG_R03_RDALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R03_EN_SHIFT                0UL
    #define XDDR_XMPU5_CFG_R03_EN_WIDTH                1UL
    #define XDDR_XMPU5_CFG_R03_EN_MASK                 0x00000001UL
    #define XDDR_XMPU5_CFG_R03_EN_DEFVAL               0x0UL

/**
 * Register: XddrXmpu5CfgR04Strt
 */
    #define XDDR_XMPU5_CFG_R04_STRT                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000140UL )
    #define XDDR_XMPU5_CFG_R04_STRT_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R04_STRT_ADDR_SHIFT         0UL
    #define XDDR_XMPU5_CFG_R04_STRT_ADDR_WIDTH         28UL
    #define XDDR_XMPU5_CFG_R04_STRT_ADDR_MASK          0x0fffffffUL
    #define XDDR_XMPU5_CFG_R04_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XddrXmpu5CfgR04End
 */
    #define XDDR_XMPU5_CFG_R04_END                     ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000144UL )
    #define XDDR_XMPU5_CFG_R04_END_RSTVAL              0x00000000UL

    #define XDDR_XMPU5_CFG_R04_END_ADDR_SHIFT          0UL
    #define XDDR_XMPU5_CFG_R04_END_ADDR_WIDTH          28UL
    #define XDDR_XMPU5_CFG_R04_END_ADDR_MASK           0x0fffffffUL
    #define XDDR_XMPU5_CFG_R04_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XddrXmpu5CfgR04Mstr
 */
    #define XDDR_XMPU5_CFG_R04_MSTR                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000148UL )
    #define XDDR_XMPU5_CFG_R04_MSTR_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R04_MSTR_MSK_SHIFT          16UL
    #define XDDR_XMPU5_CFG_R04_MSTR_MSK_WIDTH          16UL
    #define XDDR_XMPU5_CFG_R04_MSTR_MSK_MASK           0xffff0000UL
    #define XDDR_XMPU5_CFG_R04_MSTR_MSK_DEFVAL         0x0UL

    #define XDDR_XMPU5_CFG_R04_MSTR_ID_SHIFT           0UL
    #define XDDR_XMPU5_CFG_R04_MSTR_ID_WIDTH           16UL
    #define XDDR_XMPU5_CFG_R04_MSTR_ID_MASK            0x0000ffffUL
    #define XDDR_XMPU5_CFG_R04_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgR04
 */
    #define XDDR_XMPU5_CFG_R04                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x0000014CUL )
    #define XDDR_XMPU5_CFG_R04_RSTVAL                  0x00000008UL

    #define XDDR_XMPU5_CFG_R04_NSCHKTYPE_SHIFT         4UL
    #define XDDR_XMPU5_CFG_R04_NSCHKTYPE_WIDTH         1UL
    #define XDDR_XMPU5_CFG_R04_NSCHKTYPE_MASK          0x00000010UL
    #define XDDR_XMPU5_CFG_R04_NSCHKTYPE_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_R04_REGNNS_SHIFT            3UL
    #define XDDR_XMPU5_CFG_R04_REGNNS_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R04_REGNNS_MASK             0x00000008UL
    #define XDDR_XMPU5_CFG_R04_REGNNS_DEFVAL           0x1UL

    #define XDDR_XMPU5_CFG_R04_WRALWD_SHIFT            2UL
    #define XDDR_XMPU5_CFG_R04_WRALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R04_WRALWD_MASK             0x00000004UL
    #define XDDR_XMPU5_CFG_R04_WRALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R04_RDALWD_SHIFT            1UL
    #define XDDR_XMPU5_CFG_R04_RDALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R04_RDALWD_MASK             0x00000002UL
    #define XDDR_XMPU5_CFG_R04_RDALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R04_EN_SHIFT                0UL
    #define XDDR_XMPU5_CFG_R04_EN_WIDTH                1UL
    #define XDDR_XMPU5_CFG_R04_EN_MASK                 0x00000001UL
    #define XDDR_XMPU5_CFG_R04_EN_DEFVAL               0x0UL

/**
 * Register: XddrXmpu5CfgR05Strt
 */
    #define XDDR_XMPU5_CFG_R05_STRT                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000150UL )
    #define XDDR_XMPU5_CFG_R05_STRT_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R05_STRT_ADDR_SHIFT         0UL
    #define XDDR_XMPU5_CFG_R05_STRT_ADDR_WIDTH         28UL
    #define XDDR_XMPU5_CFG_R05_STRT_ADDR_MASK          0x0fffffffUL
    #define XDDR_XMPU5_CFG_R05_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XddrXmpu5CfgR05End
 */
    #define XDDR_XMPU5_CFG_R05_END                     ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000154UL )
    #define XDDR_XMPU5_CFG_R05_END_RSTVAL              0x00000000UL

    #define XDDR_XMPU5_CFG_R05_END_ADDR_SHIFT          0UL
    #define XDDR_XMPU5_CFG_R05_END_ADDR_WIDTH          28UL
    #define XDDR_XMPU5_CFG_R05_END_ADDR_MASK           0x0fffffffUL
    #define XDDR_XMPU5_CFG_R05_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XddrXmpu5CfgR05Mstr
 */
    #define XDDR_XMPU5_CFG_R05_MSTR                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000158UL )
    #define XDDR_XMPU5_CFG_R05_MSTR_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R05_MSTR_MSK_SHIFT          16UL
    #define XDDR_XMPU5_CFG_R05_MSTR_MSK_WIDTH          16UL
    #define XDDR_XMPU5_CFG_R05_MSTR_MSK_MASK           0xffff0000UL
    #define XDDR_XMPU5_CFG_R05_MSTR_MSK_DEFVAL         0x0UL

    #define XDDR_XMPU5_CFG_R05_MSTR_ID_SHIFT           0UL
    #define XDDR_XMPU5_CFG_R05_MSTR_ID_WIDTH           16UL
    #define XDDR_XMPU5_CFG_R05_MSTR_ID_MASK            0x0000ffffUL
    #define XDDR_XMPU5_CFG_R05_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgR05
 */
    #define XDDR_XMPU5_CFG_R05                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x0000015CUL )
    #define XDDR_XMPU5_CFG_R05_RSTVAL                  0x00000008UL

    #define XDDR_XMPU5_CFG_R05_NSCHKTYPE_SHIFT         4UL
    #define XDDR_XMPU5_CFG_R05_NSCHKTYPE_WIDTH         1UL
    #define XDDR_XMPU5_CFG_R05_NSCHKTYPE_MASK          0x00000010UL
    #define XDDR_XMPU5_CFG_R05_NSCHKTYPE_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_R05_REGNNS_SHIFT            3UL
    #define XDDR_XMPU5_CFG_R05_REGNNS_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R05_REGNNS_MASK             0x00000008UL
    #define XDDR_XMPU5_CFG_R05_REGNNS_DEFVAL           0x1UL

    #define XDDR_XMPU5_CFG_R05_WRALWD_SHIFT            2UL
    #define XDDR_XMPU5_CFG_R05_WRALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R05_WRALWD_MASK             0x00000004UL
    #define XDDR_XMPU5_CFG_R05_WRALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R05_RDALWD_SHIFT            1UL
    #define XDDR_XMPU5_CFG_R05_RDALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R05_RDALWD_MASK             0x00000002UL
    #define XDDR_XMPU5_CFG_R05_RDALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R05_EN_SHIFT                0UL
    #define XDDR_XMPU5_CFG_R05_EN_WIDTH                1UL
    #define XDDR_XMPU5_CFG_R05_EN_MASK                 0x00000001UL
    #define XDDR_XMPU5_CFG_R05_EN_DEFVAL               0x0UL

/**
 * Register: XddrXmpu5CfgR06Strt
 */
    #define XDDR_XMPU5_CFG_R06_STRT                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000160UL )
    #define XDDR_XMPU5_CFG_R06_STRT_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R06_STRT_ADDR_SHIFT         0UL
    #define XDDR_XMPU5_CFG_R06_STRT_ADDR_WIDTH         28UL
    #define XDDR_XMPU5_CFG_R06_STRT_ADDR_MASK          0x0fffffffUL
    #define XDDR_XMPU5_CFG_R06_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XddrXmpu5CfgR06End
 */
    #define XDDR_XMPU5_CFG_R06_END                     ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000164UL )
    #define XDDR_XMPU5_CFG_R06_END_RSTVAL              0x00000000UL

    #define XDDR_XMPU5_CFG_R06_END_ADDR_SHIFT          0UL
    #define XDDR_XMPU5_CFG_R06_END_ADDR_WIDTH          28UL
    #define XDDR_XMPU5_CFG_R06_END_ADDR_MASK           0x0fffffffUL
    #define XDDR_XMPU5_CFG_R06_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XddrXmpu5CfgR06Mstr
 */
    #define XDDR_XMPU5_CFG_R06_MSTR                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000168UL )
    #define XDDR_XMPU5_CFG_R06_MSTR_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R06_MSTR_MSK_SHIFT          16UL
    #define XDDR_XMPU5_CFG_R06_MSTR_MSK_WIDTH          16UL
    #define XDDR_XMPU5_CFG_R06_MSTR_MSK_MASK           0xffff0000UL
    #define XDDR_XMPU5_CFG_R06_MSTR_MSK_DEFVAL         0x0UL

    #define XDDR_XMPU5_CFG_R06_MSTR_ID_SHIFT           0UL
    #define XDDR_XMPU5_CFG_R06_MSTR_ID_WIDTH           16UL
    #define XDDR_XMPU5_CFG_R06_MSTR_ID_MASK            0x0000ffffUL
    #define XDDR_XMPU5_CFG_R06_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgR06
 */
    #define XDDR_XMPU5_CFG_R06                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x0000016CUL )
    #define XDDR_XMPU5_CFG_R06_RSTVAL                  0x00000008UL

    #define XDDR_XMPU5_CFG_R06_NSCHKTYPE_SHIFT         4UL
    #define XDDR_XMPU5_CFG_R06_NSCHKTYPE_WIDTH         1UL
    #define XDDR_XMPU5_CFG_R06_NSCHKTYPE_MASK          0x00000010UL
    #define XDDR_XMPU5_CFG_R06_NSCHKTYPE_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_R06_REGNNS_SHIFT            3UL
    #define XDDR_XMPU5_CFG_R06_REGNNS_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R06_REGNNS_MASK             0x00000008UL
    #define XDDR_XMPU5_CFG_R06_REGNNS_DEFVAL           0x1UL

    #define XDDR_XMPU5_CFG_R06_WRALWD_SHIFT            2UL
    #define XDDR_XMPU5_CFG_R06_WRALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R06_WRALWD_MASK             0x00000004UL
    #define XDDR_XMPU5_CFG_R06_WRALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R06_RDALWD_SHIFT            1UL
    #define XDDR_XMPU5_CFG_R06_RDALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R06_RDALWD_MASK             0x00000002UL
    #define XDDR_XMPU5_CFG_R06_RDALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R06_EN_SHIFT                0UL
    #define XDDR_XMPU5_CFG_R06_EN_WIDTH                1UL
    #define XDDR_XMPU5_CFG_R06_EN_MASK                 0x00000001UL
    #define XDDR_XMPU5_CFG_R06_EN_DEFVAL               0x0UL

/**
 * Register: XddrXmpu5CfgR07Strt
 */
    #define XDDR_XMPU5_CFG_R07_STRT                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000170UL )
    #define XDDR_XMPU5_CFG_R07_STRT_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R07_STRT_ADDR_SHIFT         0UL
    #define XDDR_XMPU5_CFG_R07_STRT_ADDR_WIDTH         28UL
    #define XDDR_XMPU5_CFG_R07_STRT_ADDR_MASK          0x0fffffffUL
    #define XDDR_XMPU5_CFG_R07_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XddrXmpu5CfgR07End
 */
    #define XDDR_XMPU5_CFG_R07_END                     ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000174UL )
    #define XDDR_XMPU5_CFG_R07_END_RSTVAL              0x00000000UL

    #define XDDR_XMPU5_CFG_R07_END_ADDR_SHIFT          0UL
    #define XDDR_XMPU5_CFG_R07_END_ADDR_WIDTH          28UL
    #define XDDR_XMPU5_CFG_R07_END_ADDR_MASK           0x0fffffffUL
    #define XDDR_XMPU5_CFG_R07_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XddrXmpu5CfgR07Mstr
 */
    #define XDDR_XMPU5_CFG_R07_MSTR                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000178UL )
    #define XDDR_XMPU5_CFG_R07_MSTR_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R07_MSTR_MSK_SHIFT          16UL
    #define XDDR_XMPU5_CFG_R07_MSTR_MSK_WIDTH          16UL
    #define XDDR_XMPU5_CFG_R07_MSTR_MSK_MASK           0xffff0000UL
    #define XDDR_XMPU5_CFG_R07_MSTR_MSK_DEFVAL         0x0UL

    #define XDDR_XMPU5_CFG_R07_MSTR_ID_SHIFT           0UL
    #define XDDR_XMPU5_CFG_R07_MSTR_ID_WIDTH           16UL
    #define XDDR_XMPU5_CFG_R07_MSTR_ID_MASK            0x0000ffffUL
    #define XDDR_XMPU5_CFG_R07_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgR07
 */
    #define XDDR_XMPU5_CFG_R07                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x0000017CUL )
    #define XDDR_XMPU5_CFG_R07_RSTVAL                  0x00000008UL

    #define XDDR_XMPU5_CFG_R07_NSCHKTYPE_SHIFT         4UL
    #define XDDR_XMPU5_CFG_R07_NSCHKTYPE_WIDTH         1UL
    #define XDDR_XMPU5_CFG_R07_NSCHKTYPE_MASK          0x00000010UL
    #define XDDR_XMPU5_CFG_R07_NSCHKTYPE_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_R07_REGNNS_SHIFT            3UL
    #define XDDR_XMPU5_CFG_R07_REGNNS_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R07_REGNNS_MASK             0x00000008UL
    #define XDDR_XMPU5_CFG_R07_REGNNS_DEFVAL           0x1UL

    #define XDDR_XMPU5_CFG_R07_WRALWD_SHIFT            2UL
    #define XDDR_XMPU5_CFG_R07_WRALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R07_WRALWD_MASK             0x00000004UL
    #define XDDR_XMPU5_CFG_R07_WRALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R07_RDALWD_SHIFT            1UL
    #define XDDR_XMPU5_CFG_R07_RDALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R07_RDALWD_MASK             0x00000002UL
    #define XDDR_XMPU5_CFG_R07_RDALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R07_EN_SHIFT                0UL
    #define XDDR_XMPU5_CFG_R07_EN_WIDTH                1UL
    #define XDDR_XMPU5_CFG_R07_EN_MASK                 0x00000001UL
    #define XDDR_XMPU5_CFG_R07_EN_DEFVAL               0x0UL

/**
 * Register: XddrXmpu5CfgR08Strt
 */
    #define XDDR_XMPU5_CFG_R08_STRT                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000180UL )
    #define XDDR_XMPU5_CFG_R08_STRT_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R08_STRT_ADDR_SHIFT         0UL
    #define XDDR_XMPU5_CFG_R08_STRT_ADDR_WIDTH         28UL
    #define XDDR_XMPU5_CFG_R08_STRT_ADDR_MASK          0x0fffffffUL
    #define XDDR_XMPU5_CFG_R08_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XddrXmpu5CfgR08End
 */
    #define XDDR_XMPU5_CFG_R08_END                     ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000184UL )
    #define XDDR_XMPU5_CFG_R08_END_RSTVAL              0x00000000UL

    #define XDDR_XMPU5_CFG_R08_END_ADDR_SHIFT          0UL
    #define XDDR_XMPU5_CFG_R08_END_ADDR_WIDTH          28UL
    #define XDDR_XMPU5_CFG_R08_END_ADDR_MASK           0x0fffffffUL
    #define XDDR_XMPU5_CFG_R08_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XddrXmpu5CfgR08Mstr
 */
    #define XDDR_XMPU5_CFG_R08_MSTR                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000188UL )
    #define XDDR_XMPU5_CFG_R08_MSTR_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R08_MSTR_MSK_SHIFT          16UL
    #define XDDR_XMPU5_CFG_R08_MSTR_MSK_WIDTH          16UL
    #define XDDR_XMPU5_CFG_R08_MSTR_MSK_MASK           0xffff0000UL
    #define XDDR_XMPU5_CFG_R08_MSTR_MSK_DEFVAL         0x0UL

    #define XDDR_XMPU5_CFG_R08_MSTR_ID_SHIFT           0UL
    #define XDDR_XMPU5_CFG_R08_MSTR_ID_WIDTH           16UL
    #define XDDR_XMPU5_CFG_R08_MSTR_ID_MASK            0x0000ffffUL
    #define XDDR_XMPU5_CFG_R08_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgR08
 */
    #define XDDR_XMPU5_CFG_R08                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x0000018CUL )
    #define XDDR_XMPU5_CFG_R08_RSTVAL                  0x00000008UL

    #define XDDR_XMPU5_CFG_R08_NSCHKTYPE_SHIFT         4UL
    #define XDDR_XMPU5_CFG_R08_NSCHKTYPE_WIDTH         1UL
    #define XDDR_XMPU5_CFG_R08_NSCHKTYPE_MASK          0x00000010UL
    #define XDDR_XMPU5_CFG_R08_NSCHKTYPE_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_R08_REGNNS_SHIFT            3UL
    #define XDDR_XMPU5_CFG_R08_REGNNS_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R08_REGNNS_MASK             0x00000008UL
    #define XDDR_XMPU5_CFG_R08_REGNNS_DEFVAL           0x1UL

    #define XDDR_XMPU5_CFG_R08_WRALWD_SHIFT            2UL
    #define XDDR_XMPU5_CFG_R08_WRALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R08_WRALWD_MASK             0x00000004UL
    #define XDDR_XMPU5_CFG_R08_WRALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R08_RDALWD_SHIFT            1UL
    #define XDDR_XMPU5_CFG_R08_RDALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R08_RDALWD_MASK             0x00000002UL
    #define XDDR_XMPU5_CFG_R08_RDALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R08_EN_SHIFT                0UL
    #define XDDR_XMPU5_CFG_R08_EN_WIDTH                1UL
    #define XDDR_XMPU5_CFG_R08_EN_MASK                 0x00000001UL
    #define XDDR_XMPU5_CFG_R08_EN_DEFVAL               0x0UL

/**
 * Register: XddrXmpu5CfgR09Strt
 */
    #define XDDR_XMPU5_CFG_R09_STRT                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000190UL )
    #define XDDR_XMPU5_CFG_R09_STRT_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R09_STRT_ADDR_SHIFT         0UL
    #define XDDR_XMPU5_CFG_R09_STRT_ADDR_WIDTH         28UL
    #define XDDR_XMPU5_CFG_R09_STRT_ADDR_MASK          0x0fffffffUL
    #define XDDR_XMPU5_CFG_R09_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XddrXmpu5CfgR09End
 */
    #define XDDR_XMPU5_CFG_R09_END                     ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000194UL )
    #define XDDR_XMPU5_CFG_R09_END_RSTVAL              0x00000000UL

    #define XDDR_XMPU5_CFG_R09_END_ADDR_SHIFT          0UL
    #define XDDR_XMPU5_CFG_R09_END_ADDR_WIDTH          28UL
    #define XDDR_XMPU5_CFG_R09_END_ADDR_MASK           0x0fffffffUL
    #define XDDR_XMPU5_CFG_R09_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XddrXmpu5CfgR09Mstr
 */
    #define XDDR_XMPU5_CFG_R09_MSTR                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x00000198UL )
    #define XDDR_XMPU5_CFG_R09_MSTR_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R09_MSTR_MSK_SHIFT          16UL
    #define XDDR_XMPU5_CFG_R09_MSTR_MSK_WIDTH          16UL
    #define XDDR_XMPU5_CFG_R09_MSTR_MSK_MASK           0xffff0000UL
    #define XDDR_XMPU5_CFG_R09_MSTR_MSK_DEFVAL         0x0UL

    #define XDDR_XMPU5_CFG_R09_MSTR_ID_SHIFT           0UL
    #define XDDR_XMPU5_CFG_R09_MSTR_ID_WIDTH           16UL
    #define XDDR_XMPU5_CFG_R09_MSTR_ID_MASK            0x0000ffffUL
    #define XDDR_XMPU5_CFG_R09_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgR09
 */
    #define XDDR_XMPU5_CFG_R09                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x0000019CUL )
    #define XDDR_XMPU5_CFG_R09_RSTVAL                  0x00000008UL

    #define XDDR_XMPU5_CFG_R09_NSCHKTYPE_SHIFT         4UL
    #define XDDR_XMPU5_CFG_R09_NSCHKTYPE_WIDTH         1UL
    #define XDDR_XMPU5_CFG_R09_NSCHKTYPE_MASK          0x00000010UL
    #define XDDR_XMPU5_CFG_R09_NSCHKTYPE_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_R09_REGNNS_SHIFT            3UL
    #define XDDR_XMPU5_CFG_R09_REGNNS_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R09_REGNNS_MASK             0x00000008UL
    #define XDDR_XMPU5_CFG_R09_REGNNS_DEFVAL           0x1UL

    #define XDDR_XMPU5_CFG_R09_WRALWD_SHIFT            2UL
    #define XDDR_XMPU5_CFG_R09_WRALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R09_WRALWD_MASK             0x00000004UL
    #define XDDR_XMPU5_CFG_R09_WRALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R09_RDALWD_SHIFT            1UL
    #define XDDR_XMPU5_CFG_R09_RDALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R09_RDALWD_MASK             0x00000002UL
    #define XDDR_XMPU5_CFG_R09_RDALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R09_EN_SHIFT                0UL
    #define XDDR_XMPU5_CFG_R09_EN_WIDTH                1UL
    #define XDDR_XMPU5_CFG_R09_EN_MASK                 0x00000001UL
    #define XDDR_XMPU5_CFG_R09_EN_DEFVAL               0x0UL

/**
 * Register: XddrXmpu5CfgR10Strt
 */
    #define XDDR_XMPU5_CFG_R10_STRT                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001A0UL )
    #define XDDR_XMPU5_CFG_R10_STRT_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R10_STRT_ADDR_SHIFT         0UL
    #define XDDR_XMPU5_CFG_R10_STRT_ADDR_WIDTH         28UL
    #define XDDR_XMPU5_CFG_R10_STRT_ADDR_MASK          0x0fffffffUL
    #define XDDR_XMPU5_CFG_R10_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XddrXmpu5CfgR10End
 */
    #define XDDR_XMPU5_CFG_R10_END                     ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001A4UL )
    #define XDDR_XMPU5_CFG_R10_END_RSTVAL              0x00000000UL

    #define XDDR_XMPU5_CFG_R10_END_ADDR_SHIFT          0UL
    #define XDDR_XMPU5_CFG_R10_END_ADDR_WIDTH          28UL
    #define XDDR_XMPU5_CFG_R10_END_ADDR_MASK           0x0fffffffUL
    #define XDDR_XMPU5_CFG_R10_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XddrXmpu5CfgR10Mstr
 */
    #define XDDR_XMPU5_CFG_R10_MSTR                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001A8UL )
    #define XDDR_XMPU5_CFG_R10_MSTR_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R10_MSTR_MSK_SHIFT          16UL
    #define XDDR_XMPU5_CFG_R10_MSTR_MSK_WIDTH          16UL
    #define XDDR_XMPU5_CFG_R10_MSTR_MSK_MASK           0xffff0000UL
    #define XDDR_XMPU5_CFG_R10_MSTR_MSK_DEFVAL         0x0UL

    #define XDDR_XMPU5_CFG_R10_MSTR_ID_SHIFT           0UL
    #define XDDR_XMPU5_CFG_R10_MSTR_ID_WIDTH           16UL
    #define XDDR_XMPU5_CFG_R10_MSTR_ID_MASK            0x0000ffffUL
    #define XDDR_XMPU5_CFG_R10_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgR10
 */
    #define XDDR_XMPU5_CFG_R10                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001ACUL )
    #define XDDR_XMPU5_CFG_R10_RSTVAL                  0x00000008UL

    #define XDDR_XMPU5_CFG_R10_NSCHKTYPE_SHIFT         4UL
    #define XDDR_XMPU5_CFG_R10_NSCHKTYPE_WIDTH         1UL
    #define XDDR_XMPU5_CFG_R10_NSCHKTYPE_MASK          0x00000010UL
    #define XDDR_XMPU5_CFG_R10_NSCHKTYPE_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_R10_REGNNS_SHIFT            3UL
    #define XDDR_XMPU5_CFG_R10_REGNNS_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R10_REGNNS_MASK             0x00000008UL
    #define XDDR_XMPU5_CFG_R10_REGNNS_DEFVAL           0x1UL

    #define XDDR_XMPU5_CFG_R10_WRALWD_SHIFT            2UL
    #define XDDR_XMPU5_CFG_R10_WRALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R10_WRALWD_MASK             0x00000004UL
    #define XDDR_XMPU5_CFG_R10_WRALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R10_RDALWD_SHIFT            1UL
    #define XDDR_XMPU5_CFG_R10_RDALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R10_RDALWD_MASK             0x00000002UL
    #define XDDR_XMPU5_CFG_R10_RDALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R10_EN_SHIFT                0UL
    #define XDDR_XMPU5_CFG_R10_EN_WIDTH                1UL
    #define XDDR_XMPU5_CFG_R10_EN_MASK                 0x00000001UL
    #define XDDR_XMPU5_CFG_R10_EN_DEFVAL               0x0UL

/**
 * Register: XddrXmpu5CfgR11Strt
 */
    #define XDDR_XMPU5_CFG_R11_STRT                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001B0UL )
    #define XDDR_XMPU5_CFG_R11_STRT_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R11_STRT_ADDR_SHIFT         0UL
    #define XDDR_XMPU5_CFG_R11_STRT_ADDR_WIDTH         28UL
    #define XDDR_XMPU5_CFG_R11_STRT_ADDR_MASK          0x0fffffffUL
    #define XDDR_XMPU5_CFG_R11_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XddrXmpu5CfgR11End
 */
    #define XDDR_XMPU5_CFG_R11_END                     ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001B4UL )
    #define XDDR_XMPU5_CFG_R11_END_RSTVAL              0x00000000UL

    #define XDDR_XMPU5_CFG_R11_END_ADDR_SHIFT          0UL
    #define XDDR_XMPU5_CFG_R11_END_ADDR_WIDTH          28UL
    #define XDDR_XMPU5_CFG_R11_END_ADDR_MASK           0x0fffffffUL
    #define XDDR_XMPU5_CFG_R11_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XddrXmpu5CfgR11Mstr
 */
    #define XDDR_XMPU5_CFG_R11_MSTR                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001B8UL )
    #define XDDR_XMPU5_CFG_R11_MSTR_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R11_MSTR_MSK_SHIFT          16UL
    #define XDDR_XMPU5_CFG_R11_MSTR_MSK_WIDTH          16UL
    #define XDDR_XMPU5_CFG_R11_MSTR_MSK_MASK           0xffff0000UL
    #define XDDR_XMPU5_CFG_R11_MSTR_MSK_DEFVAL         0x0UL

    #define XDDR_XMPU5_CFG_R11_MSTR_ID_SHIFT           0UL
    #define XDDR_XMPU5_CFG_R11_MSTR_ID_WIDTH           16UL
    #define XDDR_XMPU5_CFG_R11_MSTR_ID_MASK            0x0000ffffUL
    #define XDDR_XMPU5_CFG_R11_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgR11
 */
    #define XDDR_XMPU5_CFG_R11                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001BCUL )
    #define XDDR_XMPU5_CFG_R11_RSTVAL                  0x00000008UL

    #define XDDR_XMPU5_CFG_R11_NSCHKTYPE_SHIFT         4UL
    #define XDDR_XMPU5_CFG_R11_NSCHKTYPE_WIDTH         1UL
    #define XDDR_XMPU5_CFG_R11_NSCHKTYPE_MASK          0x00000010UL
    #define XDDR_XMPU5_CFG_R11_NSCHKTYPE_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_R11_REGNNS_SHIFT            3UL
    #define XDDR_XMPU5_CFG_R11_REGNNS_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R11_REGNNS_MASK             0x00000008UL
    #define XDDR_XMPU5_CFG_R11_REGNNS_DEFVAL           0x1UL

    #define XDDR_XMPU5_CFG_R11_WRALWD_SHIFT            2UL
    #define XDDR_XMPU5_CFG_R11_WRALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R11_WRALWD_MASK             0x00000004UL
    #define XDDR_XMPU5_CFG_R11_WRALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R11_RDALWD_SHIFT            1UL
    #define XDDR_XMPU5_CFG_R11_RDALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R11_RDALWD_MASK             0x00000002UL
    #define XDDR_XMPU5_CFG_R11_RDALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R11_EN_SHIFT                0UL
    #define XDDR_XMPU5_CFG_R11_EN_WIDTH                1UL
    #define XDDR_XMPU5_CFG_R11_EN_MASK                 0x00000001UL
    #define XDDR_XMPU5_CFG_R11_EN_DEFVAL               0x0UL

/**
 * Register: XddrXmpu5CfgR12Strt
 */
    #define XDDR_XMPU5_CFG_R12_STRT                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001C0UL )
    #define XDDR_XMPU5_CFG_R12_STRT_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R12_STRT_ADDR_SHIFT         0UL
    #define XDDR_XMPU5_CFG_R12_STRT_ADDR_WIDTH         28UL
    #define XDDR_XMPU5_CFG_R12_STRT_ADDR_MASK          0x0fffffffUL
    #define XDDR_XMPU5_CFG_R12_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XddrXmpu5CfgR12End
 */
    #define XDDR_XMPU5_CFG_R12_END                     ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001C4UL )
    #define XDDR_XMPU5_CFG_R12_END_RSTVAL              0x00000000UL

    #define XDDR_XMPU5_CFG_R12_END_ADDR_SHIFT          0UL
    #define XDDR_XMPU5_CFG_R12_END_ADDR_WIDTH          28UL
    #define XDDR_XMPU5_CFG_R12_END_ADDR_MASK           0x0fffffffUL
    #define XDDR_XMPU5_CFG_R12_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XddrXmpu5CfgR12Mstr
 */
    #define XDDR_XMPU5_CFG_R12_MSTR                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001C8UL )
    #define XDDR_XMPU5_CFG_R12_MSTR_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R12_MSTR_MSK_SHIFT          16UL
    #define XDDR_XMPU5_CFG_R12_MSTR_MSK_WIDTH          16UL
    #define XDDR_XMPU5_CFG_R12_MSTR_MSK_MASK           0xffff0000UL
    #define XDDR_XMPU5_CFG_R12_MSTR_MSK_DEFVAL         0x0UL

    #define XDDR_XMPU5_CFG_R12_MSTR_ID_SHIFT           0UL
    #define XDDR_XMPU5_CFG_R12_MSTR_ID_WIDTH           16UL
    #define XDDR_XMPU5_CFG_R12_MSTR_ID_MASK            0x0000ffffUL
    #define XDDR_XMPU5_CFG_R12_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgR12
 */
    #define XDDR_XMPU5_CFG_R12                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001CCUL )
    #define XDDR_XMPU5_CFG_R12_RSTVAL                  0x00000008UL

    #define XDDR_XMPU5_CFG_R12_NSCHKTYPE_SHIFT         4UL
    #define XDDR_XMPU5_CFG_R12_NSCHKTYPE_WIDTH         1UL
    #define XDDR_XMPU5_CFG_R12_NSCHKTYPE_MASK          0x00000010UL
    #define XDDR_XMPU5_CFG_R12_NSCHKTYPE_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_R12_REGNNS_SHIFT            3UL
    #define XDDR_XMPU5_CFG_R12_REGNNS_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R12_REGNNS_MASK             0x00000008UL
    #define XDDR_XMPU5_CFG_R12_REGNNS_DEFVAL           0x1UL

    #define XDDR_XMPU5_CFG_R12_WRALWD_SHIFT            2UL
    #define XDDR_XMPU5_CFG_R12_WRALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R12_WRALWD_MASK             0x00000004UL
    #define XDDR_XMPU5_CFG_R12_WRALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R12_RDALWD_SHIFT            1UL
    #define XDDR_XMPU5_CFG_R12_RDALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R12_RDALWD_MASK             0x00000002UL
    #define XDDR_XMPU5_CFG_R12_RDALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R12_EN_SHIFT                0UL
    #define XDDR_XMPU5_CFG_R12_EN_WIDTH                1UL
    #define XDDR_XMPU5_CFG_R12_EN_MASK                 0x00000001UL
    #define XDDR_XMPU5_CFG_R12_EN_DEFVAL               0x0UL

/**
 * Register: XddrXmpu5CfgR13Strt
 */
    #define XDDR_XMPU5_CFG_R13_STRT                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001D0UL )
    #define XDDR_XMPU5_CFG_R13_STRT_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R13_STRT_ADDR_SHIFT         0UL
    #define XDDR_XMPU5_CFG_R13_STRT_ADDR_WIDTH         28UL
    #define XDDR_XMPU5_CFG_R13_STRT_ADDR_MASK          0x0fffffffUL
    #define XDDR_XMPU5_CFG_R13_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XddrXmpu5CfgR13End
 */
    #define XDDR_XMPU5_CFG_R13_END                     ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001D4UL )
    #define XDDR_XMPU5_CFG_R13_END_RSTVAL              0x00000000UL

    #define XDDR_XMPU5_CFG_R13_END_ADDR_SHIFT          0UL
    #define XDDR_XMPU5_CFG_R13_END_ADDR_WIDTH          28UL
    #define XDDR_XMPU5_CFG_R13_END_ADDR_MASK           0x0fffffffUL
    #define XDDR_XMPU5_CFG_R13_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XddrXmpu5CfgR13Mstr
 */
    #define XDDR_XMPU5_CFG_R13_MSTR                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001D8UL )
    #define XDDR_XMPU5_CFG_R13_MSTR_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R13_MSTR_MSK_SHIFT          16UL
    #define XDDR_XMPU5_CFG_R13_MSTR_MSK_WIDTH          16UL
    #define XDDR_XMPU5_CFG_R13_MSTR_MSK_MASK           0xffff0000UL
    #define XDDR_XMPU5_CFG_R13_MSTR_MSK_DEFVAL         0x0UL

    #define XDDR_XMPU5_CFG_R13_MSTR_ID_SHIFT           0UL
    #define XDDR_XMPU5_CFG_R13_MSTR_ID_WIDTH           16UL
    #define XDDR_XMPU5_CFG_R13_MSTR_ID_MASK            0x0000ffffUL
    #define XDDR_XMPU5_CFG_R13_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgR13
 */
    #define XDDR_XMPU5_CFG_R13                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001DCUL )
    #define XDDR_XMPU5_CFG_R13_RSTVAL                  0x00000008UL

    #define XDDR_XMPU5_CFG_R13_NSCHKTYPE_SHIFT         4UL
    #define XDDR_XMPU5_CFG_R13_NSCHKTYPE_WIDTH         1UL
    #define XDDR_XMPU5_CFG_R13_NSCHKTYPE_MASK          0x00000010UL
    #define XDDR_XMPU5_CFG_R13_NSCHKTYPE_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_R13_REGNNS_SHIFT            3UL
    #define XDDR_XMPU5_CFG_R13_REGNNS_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R13_REGNNS_MASK             0x00000008UL
    #define XDDR_XMPU5_CFG_R13_REGNNS_DEFVAL           0x1UL

    #define XDDR_XMPU5_CFG_R13_WRALWD_SHIFT            2UL
    #define XDDR_XMPU5_CFG_R13_WRALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R13_WRALWD_MASK             0x00000004UL
    #define XDDR_XMPU5_CFG_R13_WRALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R13_RDALWD_SHIFT            1UL
    #define XDDR_XMPU5_CFG_R13_RDALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R13_RDALWD_MASK             0x00000002UL
    #define XDDR_XMPU5_CFG_R13_RDALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R13_EN_SHIFT                0UL
    #define XDDR_XMPU5_CFG_R13_EN_WIDTH                1UL
    #define XDDR_XMPU5_CFG_R13_EN_MASK                 0x00000001UL
    #define XDDR_XMPU5_CFG_R13_EN_DEFVAL               0x0UL

/**
 * Register: XddrXmpu5CfgR14Strt
 */
    #define XDDR_XMPU5_CFG_R14_STRT                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001E0UL )
    #define XDDR_XMPU5_CFG_R14_STRT_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R14_STRT_ADDR_SHIFT         0UL
    #define XDDR_XMPU5_CFG_R14_STRT_ADDR_WIDTH         28UL
    #define XDDR_XMPU5_CFG_R14_STRT_ADDR_MASK          0x0fffffffUL
    #define XDDR_XMPU5_CFG_R14_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XddrXmpu5CfgR14End
 */
    #define XDDR_XMPU5_CFG_R14_END                     ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001E4UL )
    #define XDDR_XMPU5_CFG_R14_END_RSTVAL              0x00000000UL

    #define XDDR_XMPU5_CFG_R14_END_ADDR_SHIFT          0UL
    #define XDDR_XMPU5_CFG_R14_END_ADDR_WIDTH          28UL
    #define XDDR_XMPU5_CFG_R14_END_ADDR_MASK           0x0fffffffUL
    #define XDDR_XMPU5_CFG_R14_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XddrXmpu5CfgR14Mstr
 */
    #define XDDR_XMPU5_CFG_R14_MSTR                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001E8UL )
    #define XDDR_XMPU5_CFG_R14_MSTR_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R14_MSTR_MSK_SHIFT          16UL
    #define XDDR_XMPU5_CFG_R14_MSTR_MSK_WIDTH          16UL
    #define XDDR_XMPU5_CFG_R14_MSTR_MSK_MASK           0xffff0000UL
    #define XDDR_XMPU5_CFG_R14_MSTR_MSK_DEFVAL         0x0UL

    #define XDDR_XMPU5_CFG_R14_MSTR_ID_SHIFT           0UL
    #define XDDR_XMPU5_CFG_R14_MSTR_ID_WIDTH           16UL
    #define XDDR_XMPU5_CFG_R14_MSTR_ID_MASK            0x0000ffffUL
    #define XDDR_XMPU5_CFG_R14_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgR14
 */
    #define XDDR_XMPU5_CFG_R14                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001ECUL )
    #define XDDR_XMPU5_CFG_R14_RSTVAL                  0x00000008UL

    #define XDDR_XMPU5_CFG_R14_NSCHKTYPE_SHIFT         4UL
    #define XDDR_XMPU5_CFG_R14_NSCHKTYPE_WIDTH         1UL
    #define XDDR_XMPU5_CFG_R14_NSCHKTYPE_MASK          0x00000010UL
    #define XDDR_XMPU5_CFG_R14_NSCHKTYPE_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_R14_REGNNS_SHIFT            3UL
    #define XDDR_XMPU5_CFG_R14_REGNNS_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R14_REGNNS_MASK             0x00000008UL
    #define XDDR_XMPU5_CFG_R14_REGNNS_DEFVAL           0x1UL

    #define XDDR_XMPU5_CFG_R14_WRALWD_SHIFT            2UL
    #define XDDR_XMPU5_CFG_R14_WRALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R14_WRALWD_MASK             0x00000004UL
    #define XDDR_XMPU5_CFG_R14_WRALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R14_RDALWD_SHIFT            1UL
    #define XDDR_XMPU5_CFG_R14_RDALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R14_RDALWD_MASK             0x00000002UL
    #define XDDR_XMPU5_CFG_R14_RDALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R14_EN_SHIFT                0UL
    #define XDDR_XMPU5_CFG_R14_EN_WIDTH                1UL
    #define XDDR_XMPU5_CFG_R14_EN_MASK                 0x00000001UL
    #define XDDR_XMPU5_CFG_R14_EN_DEFVAL               0x0UL

/**
 * Register: XddrXmpu5CfgR15Strt
 */
    #define XDDR_XMPU5_CFG_R15_STRT                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001F0UL )
    #define XDDR_XMPU5_CFG_R15_STRT_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R15_STRT_ADDR_SHIFT         0UL
    #define XDDR_XMPU5_CFG_R15_STRT_ADDR_WIDTH         28UL
    #define XDDR_XMPU5_CFG_R15_STRT_ADDR_MASK          0x0fffffffUL
    #define XDDR_XMPU5_CFG_R15_STRT_ADDR_DEFVAL        0x0UL

/**
 * Register: XddrXmpu5CfgR15End
 */
    #define XDDR_XMPU5_CFG_R15_END                     ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001F4UL )
    #define XDDR_XMPU5_CFG_R15_END_RSTVAL              0x00000000UL

    #define XDDR_XMPU5_CFG_R15_END_ADDR_SHIFT          0UL
    #define XDDR_XMPU5_CFG_R15_END_ADDR_WIDTH          28UL
    #define XDDR_XMPU5_CFG_R15_END_ADDR_MASK           0x0fffffffUL
    #define XDDR_XMPU5_CFG_R15_END_ADDR_DEFVAL         0x0UL

/**
 * Register: XddrXmpu5CfgR15Mstr
 */
    #define XDDR_XMPU5_CFG_R15_MSTR                    ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001F8UL )
    #define XDDR_XMPU5_CFG_R15_MSTR_RSTVAL             0x00000000UL

    #define XDDR_XMPU5_CFG_R15_MSTR_MSK_SHIFT          16UL
    #define XDDR_XMPU5_CFG_R15_MSTR_MSK_WIDTH          16UL
    #define XDDR_XMPU5_CFG_R15_MSTR_MSK_MASK           0xffff0000UL
    #define XDDR_XMPU5_CFG_R15_MSTR_MSK_DEFVAL         0x0UL

    #define XDDR_XMPU5_CFG_R15_MSTR_ID_SHIFT           0UL
    #define XDDR_XMPU5_CFG_R15_MSTR_ID_WIDTH           16UL
    #define XDDR_XMPU5_CFG_R15_MSTR_ID_MASK            0x0000ffffUL
    #define XDDR_XMPU5_CFG_R15_MSTR_ID_DEFVAL          0x0UL

/**
 * Register: XddrXmpu5CfgR15
 */
    #define XDDR_XMPU5_CFG_R15                         ( ( XDDR_XMPU5_CFG_BASEADDR ) +0x000001FCUL )
    #define XDDR_XMPU5_CFG_R15_RSTVAL                  0x00000008UL

    #define XDDR_XMPU5_CFG_R15_NSCHKTYPE_SHIFT         4UL
    #define XDDR_XMPU5_CFG_R15_NSCHKTYPE_WIDTH         1UL
    #define XDDR_XMPU5_CFG_R15_NSCHKTYPE_MASK          0x00000010UL
    #define XDDR_XMPU5_CFG_R15_NSCHKTYPE_DEFVAL        0x0UL

    #define XDDR_XMPU5_CFG_R15_REGNNS_SHIFT            3UL
    #define XDDR_XMPU5_CFG_R15_REGNNS_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R15_REGNNS_MASK             0x00000008UL
    #define XDDR_XMPU5_CFG_R15_REGNNS_DEFVAL           0x1UL

    #define XDDR_XMPU5_CFG_R15_WRALWD_SHIFT            2UL
    #define XDDR_XMPU5_CFG_R15_WRALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R15_WRALWD_MASK             0x00000004UL
    #define XDDR_XMPU5_CFG_R15_WRALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R15_RDALWD_SHIFT            1UL
    #define XDDR_XMPU5_CFG_R15_RDALWD_WIDTH            1UL
    #define XDDR_XMPU5_CFG_R15_RDALWD_MASK             0x00000002UL
    #define XDDR_XMPU5_CFG_R15_RDALWD_DEFVAL           0x0UL

    #define XDDR_XMPU5_CFG_R15_EN_SHIFT                0UL
    #define XDDR_XMPU5_CFG_R15_EN_WIDTH                1UL
    #define XDDR_XMPU5_CFG_R15_EN_MASK                 0x00000001UL
    #define XDDR_XMPU5_CFG_R15_EN_DEFVAL               0x0UL


    #ifdef __cplusplus
}
    #endif

#endif /* __XDDR_XMPU5_CFG_H__ */
