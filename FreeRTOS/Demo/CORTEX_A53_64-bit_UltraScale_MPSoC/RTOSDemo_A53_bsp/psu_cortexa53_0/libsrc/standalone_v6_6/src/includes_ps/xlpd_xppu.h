/* ### HEADER ### */

#ifndef __XLPD_XPPU_H__
    #define __XLPD_XPPU_H__


    #ifdef __cplusplus
    extern "C" {
    #endif

/**
 * XlpdXppu Base Address
 */
    #define XLPD_XPPU_BASEADDR                      0xFF980000UL

/**
 * Register: XlpdXppuCtrl
 */
    #define XLPD_XPPU_CTRL                          ( ( XLPD_XPPU_BASEADDR ) +0x00000000UL )
    #define XLPD_XPPU_CTRL_RSTVAL                   0x00000000UL

    #define XLPD_XPPU_CTRL_APER_PARITY_EN_SHIFT     2UL
    #define XLPD_XPPU_CTRL_APER_PARITY_EN_WIDTH     1UL
    #define XLPD_XPPU_CTRL_APER_PARITY_EN_MASK      0x00000004UL
    #define XLPD_XPPU_CTRL_APER_PARITY_EN_DEFVAL    0x0UL

    #define XLPD_XPPU_CTRL_MID_PARITY_EN_SHIFT      1UL
    #define XLPD_XPPU_CTRL_MID_PARITY_EN_WIDTH      1UL
    #define XLPD_XPPU_CTRL_MID_PARITY_EN_MASK       0x00000002UL
    #define XLPD_XPPU_CTRL_MID_PARITY_EN_DEFVAL     0x0UL

    #define XLPD_XPPU_CTRL_EN_SHIFT                 0UL
    #define XLPD_XPPU_CTRL_EN_WIDTH                 1UL
    #define XLPD_XPPU_CTRL_EN_MASK                  0x00000001UL
    #define XLPD_XPPU_CTRL_EN_DEFVAL                0x0UL

/**
 * Register: XlpdXppuErrSts1
 */
    #define XLPD_XPPU_ERR_STS1                      ( ( XLPD_XPPU_BASEADDR ) +0x00000004UL )
    #define XLPD_XPPU_ERR_STS1_RSTVAL               0x00000000UL

    #define XLPD_XPPU_ERR_STS1_AXI_ADDR_SHIFT       0UL
    #define XLPD_XPPU_ERR_STS1_AXI_ADDR_WIDTH       32UL
    #define XLPD_XPPU_ERR_STS1_AXI_ADDR_MASK        0xffffffffUL
    #define XLPD_XPPU_ERR_STS1_AXI_ADDR_DEFVAL      0x0UL

/**
 * Register: XlpdXppuErrSts2
 */
    #define XLPD_XPPU_ERR_STS2                      ( ( XLPD_XPPU_BASEADDR ) +0x00000008UL )
    #define XLPD_XPPU_ERR_STS2_RSTVAL               0x00000000UL

    #define XLPD_XPPU_ERR_STS2_AXI_ID_SHIFT         0UL
    #define XLPD_XPPU_ERR_STS2_AXI_ID_WIDTH         16UL
    #define XLPD_XPPU_ERR_STS2_AXI_ID_MASK          0x0000ffffUL
    #define XLPD_XPPU_ERR_STS2_AXI_ID_DEFVAL        0x0UL

/**
 * Register: XlpdXppuPoison
 */
    #define XLPD_XPPU_POISON                        ( ( XLPD_XPPU_BASEADDR ) +0x0000000CUL )
    #define XLPD_XPPU_POISON_RSTVAL                 0x00000000UL

    #define XLPD_XPPU_POISON_BASE_SHIFT             0UL
    #define XLPD_XPPU_POISON_BASE_WIDTH             20UL
    #define XLPD_XPPU_POISON_BASE_MASK              0x000fffffUL
    #define XLPD_XPPU_POISON_BASE_DEFVAL            0x0UL

/**
 * Register: XlpdXppuIsr
 */
    #define XLPD_XPPU_ISR                           ( ( XLPD_XPPU_BASEADDR ) +0x00000010UL )
    #define XLPD_XPPU_ISR_RSTVAL                    0x00000000UL

    #define XLPD_XPPU_ISR_APER_PARITY_SHIFT         7UL
    #define XLPD_XPPU_ISR_APER_PARITY_WIDTH         1UL
    #define XLPD_XPPU_ISR_APER_PARITY_MASK          0x00000080UL
    #define XLPD_XPPU_ISR_APER_PARITY_DEFVAL        0x0UL

    #define XLPD_XPPU_ISR_APER_TZ_SHIFT             6UL
    #define XLPD_XPPU_ISR_APER_TZ_WIDTH             1UL
    #define XLPD_XPPU_ISR_APER_TZ_MASK              0x00000040UL
    #define XLPD_XPPU_ISR_APER_TZ_DEFVAL            0x0UL

    #define XLPD_XPPU_ISR_APER_PERM_SHIFT           5UL
    #define XLPD_XPPU_ISR_APER_PERM_WIDTH           1UL
    #define XLPD_XPPU_ISR_APER_PERM_MASK            0x00000020UL
    #define XLPD_XPPU_ISR_APER_PERM_DEFVAL          0x0UL

    #define XLPD_XPPU_ISR_MID_PARITY_SHIFT          3UL
    #define XLPD_XPPU_ISR_MID_PARITY_WIDTH          1UL
    #define XLPD_XPPU_ISR_MID_PARITY_MASK           0x00000008UL
    #define XLPD_XPPU_ISR_MID_PARITY_DEFVAL         0x0UL

    #define XLPD_XPPU_ISR_MID_RO_SHIFT              2UL
    #define XLPD_XPPU_ISR_MID_RO_WIDTH              1UL
    #define XLPD_XPPU_ISR_MID_RO_MASK               0x00000004UL
    #define XLPD_XPPU_ISR_MID_RO_DEFVAL             0x0UL

    #define XLPD_XPPU_ISR_MID_MISS_SHIFT            1UL
    #define XLPD_XPPU_ISR_MID_MISS_WIDTH            1UL
    #define XLPD_XPPU_ISR_MID_MISS_MASK             0x00000002UL
    #define XLPD_XPPU_ISR_MID_MISS_DEFVAL           0x0UL

    #define XLPD_XPPU_ISR_INV_APB_SHIFT             0UL
    #define XLPD_XPPU_ISR_INV_APB_WIDTH             1UL
    #define XLPD_XPPU_ISR_INV_APB_MASK              0x00000001UL
    #define XLPD_XPPU_ISR_INV_APB_DEFVAL            0x0UL

/**
 * Register: XlpdXppuImr
 */
    #define XLPD_XPPU_IMR                           ( ( XLPD_XPPU_BASEADDR ) +0x00000014UL )
    #define XLPD_XPPU_IMR_RSTVAL                    0x000000efUL

    #define XLPD_XPPU_IMR_APER_PARITY_SHIFT         7UL
    #define XLPD_XPPU_IMR_APER_PARITY_WIDTH         1UL
    #define XLPD_XPPU_IMR_APER_PARITY_MASK          0x00000080UL
    #define XLPD_XPPU_IMR_APER_PARITY_DEFVAL        0x1UL

    #define XLPD_XPPU_IMR_APER_TZ_SHIFT             6UL
    #define XLPD_XPPU_IMR_APER_TZ_WIDTH             1UL
    #define XLPD_XPPU_IMR_APER_TZ_MASK              0x00000040UL
    #define XLPD_XPPU_IMR_APER_TZ_DEFVAL            0x1UL

    #define XLPD_XPPU_IMR_APER_PERM_SHIFT           5UL
    #define XLPD_XPPU_IMR_APER_PERM_WIDTH           1UL
    #define XLPD_XPPU_IMR_APER_PERM_MASK            0x00000020UL
    #define XLPD_XPPU_IMR_APER_PERM_DEFVAL          0x1UL

    #define XLPD_XPPU_IMR_MID_PARITY_SHIFT          3UL
    #define XLPD_XPPU_IMR_MID_PARITY_WIDTH          1UL
    #define XLPD_XPPU_IMR_MID_PARITY_MASK           0x00000008UL
    #define XLPD_XPPU_IMR_MID_PARITY_DEFVAL         0x1UL

    #define XLPD_XPPU_IMR_MID_RO_SHIFT              2UL
    #define XLPD_XPPU_IMR_MID_RO_WIDTH              1UL
    #define XLPD_XPPU_IMR_MID_RO_MASK               0x00000004UL
    #define XLPD_XPPU_IMR_MID_RO_DEFVAL             0x1UL

    #define XLPD_XPPU_IMR_MID_MISS_SHIFT            1UL
    #define XLPD_XPPU_IMR_MID_MISS_WIDTH            1UL
    #define XLPD_XPPU_IMR_MID_MISS_MASK             0x00000002UL
    #define XLPD_XPPU_IMR_MID_MISS_DEFVAL           0x1UL

    #define XLPD_XPPU_IMR_INV_APB_SHIFT             0UL
    #define XLPD_XPPU_IMR_INV_APB_WIDTH             1UL
    #define XLPD_XPPU_IMR_INV_APB_MASK              0x00000001UL
    #define XLPD_XPPU_IMR_INV_APB_DEFVAL            0x1UL

/**
 * Register: XlpdXppuIen
 */
    #define XLPD_XPPU_IEN                           ( ( XLPD_XPPU_BASEADDR ) +0x00000018UL )
    #define XLPD_XPPU_IEN_RSTVAL                    0x00000000UL

    #define XLPD_XPPU_IEN_APER_PARITY_SHIFT         7UL
    #define XLPD_XPPU_IEN_APER_PARITY_WIDTH         1UL
    #define XLPD_XPPU_IEN_APER_PARITY_MASK          0x00000080UL
    #define XLPD_XPPU_IEN_APER_PARITY_DEFVAL        0x0UL

    #define XLPD_XPPU_IEN_APER_TZ_SHIFT             6UL
    #define XLPD_XPPU_IEN_APER_TZ_WIDTH             1UL
    #define XLPD_XPPU_IEN_APER_TZ_MASK              0x00000040UL
    #define XLPD_XPPU_IEN_APER_TZ_DEFVAL            0x0UL

    #define XLPD_XPPU_IEN_APER_PERM_SHIFT           5UL
    #define XLPD_XPPU_IEN_APER_PERM_WIDTH           1UL
    #define XLPD_XPPU_IEN_APER_PERM_MASK            0x00000020UL
    #define XLPD_XPPU_IEN_APER_PERM_DEFVAL          0x0UL

    #define XLPD_XPPU_IEN_MID_PARITY_SHIFT          3UL
    #define XLPD_XPPU_IEN_MID_PARITY_WIDTH          1UL
    #define XLPD_XPPU_IEN_MID_PARITY_MASK           0x00000008UL
    #define XLPD_XPPU_IEN_MID_PARITY_DEFVAL         0x0UL

    #define XLPD_XPPU_IEN_MID_RO_SHIFT              2UL
    #define XLPD_XPPU_IEN_MID_RO_WIDTH              1UL
    #define XLPD_XPPU_IEN_MID_RO_MASK               0x00000004UL
    #define XLPD_XPPU_IEN_MID_RO_DEFVAL             0x0UL

    #define XLPD_XPPU_IEN_MID_MISS_SHIFT            1UL
    #define XLPD_XPPU_IEN_MID_MISS_WIDTH            1UL
    #define XLPD_XPPU_IEN_MID_MISS_MASK             0x00000002UL
    #define XLPD_XPPU_IEN_MID_MISS_DEFVAL           0x0UL

    #define XLPD_XPPU_IEN_INV_APB_SHIFT             0UL
    #define XLPD_XPPU_IEN_INV_APB_WIDTH             1UL
    #define XLPD_XPPU_IEN_INV_APB_MASK              0x00000001UL
    #define XLPD_XPPU_IEN_INV_APB_DEFVAL            0x0UL

/**
 * Register: XlpdXppuIds
 */
    #define XLPD_XPPU_IDS                           ( ( XLPD_XPPU_BASEADDR ) +0x0000001CUL )
    #define XLPD_XPPU_IDS_RSTVAL                    0x00000000UL

    #define XLPD_XPPU_IDS_APER_PARITY_SHIFT         7UL
    #define XLPD_XPPU_IDS_APER_PARITY_WIDTH         1UL
    #define XLPD_XPPU_IDS_APER_PARITY_MASK          0x00000080UL
    #define XLPD_XPPU_IDS_APER_PARITY_DEFVAL        0x0UL

    #define XLPD_XPPU_IDS_APER_TZ_SHIFT             6UL
    #define XLPD_XPPU_IDS_APER_TZ_WIDTH             1UL
    #define XLPD_XPPU_IDS_APER_TZ_MASK              0x00000040UL
    #define XLPD_XPPU_IDS_APER_TZ_DEFVAL            0x0UL

    #define XLPD_XPPU_IDS_APER_PERM_SHIFT           5UL
    #define XLPD_XPPU_IDS_APER_PERM_WIDTH           1UL
    #define XLPD_XPPU_IDS_APER_PERM_MASK            0x00000020UL
    #define XLPD_XPPU_IDS_APER_PERM_DEFVAL          0x0UL

    #define XLPD_XPPU_IDS_MID_PARITY_SHIFT          3UL
    #define XLPD_XPPU_IDS_MID_PARITY_WIDTH          1UL
    #define XLPD_XPPU_IDS_MID_PARITY_MASK           0x00000008UL
    #define XLPD_XPPU_IDS_MID_PARITY_DEFVAL         0x0UL

    #define XLPD_XPPU_IDS_MID_RO_SHIFT              2UL
    #define XLPD_XPPU_IDS_MID_RO_WIDTH              1UL
    #define XLPD_XPPU_IDS_MID_RO_MASK               0x00000004UL
    #define XLPD_XPPU_IDS_MID_RO_DEFVAL             0x0UL

    #define XLPD_XPPU_IDS_MID_MISS_SHIFT            1UL
    #define XLPD_XPPU_IDS_MID_MISS_WIDTH            1UL
    #define XLPD_XPPU_IDS_MID_MISS_MASK             0x00000002UL
    #define XLPD_XPPU_IDS_MID_MISS_DEFVAL           0x0UL

    #define XLPD_XPPU_IDS_INV_APB_SHIFT             0UL
    #define XLPD_XPPU_IDS_INV_APB_WIDTH             1UL
    #define XLPD_XPPU_IDS_INV_APB_MASK              0x00000001UL
    #define XLPD_XPPU_IDS_INV_APB_DEFVAL            0x0UL

/**
 * Register: XlpdXppuMMstrIds
 */
    #define XLPD_XPPU_M_MSTR_IDS                    ( ( XLPD_XPPU_BASEADDR ) +0x0000003CUL )
    #define XLPD_XPPU_M_MSTR_IDS_RSTVAL             0x00000014UL

    #define XLPD_XPPU_M_MSTR_IDS_NO_SHIFT           0UL
    #define XLPD_XPPU_M_MSTR_IDS_NO_WIDTH           32UL
    #define XLPD_XPPU_M_MSTR_IDS_NO_MASK            0xffffffffUL
    #define XLPD_XPPU_M_MSTR_IDS_NO_DEFVAL          0x14UL

/**
 * Register: XlpdXppuMAperture32b
 */
    #define XLPD_XPPU_M_APERTURE_32B                ( ( XLPD_XPPU_BASEADDR ) +0x00000040UL )
    #define XLPD_XPPU_M_APERTURE_32B_RSTVAL         0x00000080UL

    #define XLPD_XPPU_M_APERTURE_32B_NO_SHIFT       0UL
    #define XLPD_XPPU_M_APERTURE_32B_NO_WIDTH       32UL
    #define XLPD_XPPU_M_APERTURE_32B_NO_MASK        0xffffffffUL
    #define XLPD_XPPU_M_APERTURE_32B_NO_DEFVAL      0x80UL

/**
 * Register: XlpdXppuMAperture64kb
 */
    #define XLPD_XPPU_M_APERTURE_64KB               ( ( XLPD_XPPU_BASEADDR ) +0x00000044UL )
    #define XLPD_XPPU_M_APERTURE_64KB_RSTVAL        0x00000100UL

    #define XLPD_XPPU_M_APERTURE_64KB_NO_SHIFT      0UL
    #define XLPD_XPPU_M_APERTURE_64KB_NO_WIDTH      32UL
    #define XLPD_XPPU_M_APERTURE_64KB_NO_MASK       0xffffffffUL
    #define XLPD_XPPU_M_APERTURE_64KB_NO_DEFVAL     0x100UL

/**
 * Register: XlpdXppuMAperture1mb
 */
    #define XLPD_XPPU_M_APERTURE_1MB                ( ( XLPD_XPPU_BASEADDR ) +0x00000048UL )
    #define XLPD_XPPU_M_APERTURE_1MB_RSTVAL         0x00000010UL

    #define XLPD_XPPU_M_APERTURE_1MB_NO_SHIFT       0UL
    #define XLPD_XPPU_M_APERTURE_1MB_NO_WIDTH       32UL
    #define XLPD_XPPU_M_APERTURE_1MB_NO_MASK        0xffffffffUL
    #define XLPD_XPPU_M_APERTURE_1MB_NO_DEFVAL      0x10UL

/**
 * Register: XlpdXppuMAperture512mb
 */
    #define XLPD_XPPU_M_APERTURE_512MB              ( ( XLPD_XPPU_BASEADDR ) +0x0000004CUL )
    #define XLPD_XPPU_M_APERTURE_512MB_RSTVAL       0x00000001UL

    #define XLPD_XPPU_M_APERTURE_512MB_NO_SHIFT     0UL
    #define XLPD_XPPU_M_APERTURE_512MB_NO_WIDTH     32UL
    #define XLPD_XPPU_M_APERTURE_512MB_NO_MASK      0xffffffffUL
    #define XLPD_XPPU_M_APERTURE_512MB_NO_DEFVAL    0x1UL

/**
 * Register: XlpdXppuBase32b
 */
    #define XLPD_XPPU_BASE_32B                      ( ( XLPD_XPPU_BASEADDR ) +0x00000050UL )
    #define XLPD_XPPU_BASE_32B_RSTVAL               0xff990000UL

    #define XLPD_XPPU_BASE_32B_ADDR_SHIFT           0UL
    #define XLPD_XPPU_BASE_32B_ADDR_WIDTH           32UL
    #define XLPD_XPPU_BASE_32B_ADDR_MASK            0xffffffffUL
    #define XLPD_XPPU_BASE_32B_ADDR_DEFVAL          0xff990000UL

/**
 * Register: XlpdXppuBase64kb
 */
    #define XLPD_XPPU_BASE_64KB                     ( ( XLPD_XPPU_BASEADDR ) +0x00000054UL )
    #define XLPD_XPPU_BASE_64KB_RSTVAL              0xff000000UL

    #define XLPD_XPPU_BASE_64KB_ADDR_SHIFT          0UL
    #define XLPD_XPPU_BASE_64KB_ADDR_WIDTH          32UL
    #define XLPD_XPPU_BASE_64KB_ADDR_MASK           0xffffffffUL
    #define XLPD_XPPU_BASE_64KB_ADDR_DEFVAL         0xff000000UL

/**
 * Register: XlpdXppuBase1mb
 */
    #define XLPD_XPPU_BASE_1MB                      ( ( XLPD_XPPU_BASEADDR ) +0x00000058UL )
    #define XLPD_XPPU_BASE_1MB_RSTVAL               0xfe000000UL

    #define XLPD_XPPU_BASE_1MB_ADDR_SHIFT           0UL
    #define XLPD_XPPU_BASE_1MB_ADDR_WIDTH           32UL
    #define XLPD_XPPU_BASE_1MB_ADDR_MASK            0xffffffffUL
    #define XLPD_XPPU_BASE_1MB_ADDR_DEFVAL          0xfe000000UL

/**
 * Register: XlpdXppuBase512mb
 */
    #define XLPD_XPPU_BASE_512MB                    ( ( XLPD_XPPU_BASEADDR ) +0x0000005CUL )
    #define XLPD_XPPU_BASE_512MB_RSTVAL             0xc0000000UL

    #define XLPD_XPPU_BASE_512MB_ADDR_SHIFT         0UL
    #define XLPD_XPPU_BASE_512MB_ADDR_WIDTH         32UL
    #define XLPD_XPPU_BASE_512MB_ADDR_MASK          0xffffffffUL
    #define XLPD_XPPU_BASE_512MB_ADDR_DEFVAL        0xc0000000UL

/**
 * Register: XlpdXppuMstrId00
 */
    #define XLPD_XPPU_MSTR_ID00                     ( ( XLPD_XPPU_BASEADDR ) +0x00000100UL )
    #define XLPD_XPPU_MSTR_ID00_RSTVAL              0x83ff0040UL

    #define XLPD_XPPU_MSTR_ID00_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID00_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID00_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID00_MIDP_DEFVAL         0x1UL

    #define XLPD_XPPU_MSTR_ID00_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID00_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID00_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID00_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID00_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID00_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID00_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID00_MIDM_DEFVAL         0x3ffUL

    #define XLPD_XPPU_MSTR_ID00_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID00_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID00_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID00_MID_DEFVAL          0x40UL

/**
 * Register: XlpdXppuMstrId01
 */
    #define XLPD_XPPU_MSTR_ID01                     ( ( XLPD_XPPU_BASEADDR ) +0x00000104UL )
    #define XLPD_XPPU_MSTR_ID01_RSTVAL              0x03f00000UL

    #define XLPD_XPPU_MSTR_ID01_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID01_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID01_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID01_MIDP_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID01_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID01_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID01_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID01_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID01_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID01_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID01_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID01_MIDM_DEFVAL         0x3f0UL

    #define XLPD_XPPU_MSTR_ID01_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID01_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID01_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID01_MID_DEFVAL          0x0UL

/**
 * Register: XlpdXppuMstrId02
 */
    #define XLPD_XPPU_MSTR_ID02                     ( ( XLPD_XPPU_BASEADDR ) +0x00000108UL )
    #define XLPD_XPPU_MSTR_ID02_RSTVAL              0x83f00010UL

    #define XLPD_XPPU_MSTR_ID02_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID02_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID02_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID02_MIDP_DEFVAL         0x1UL

    #define XLPD_XPPU_MSTR_ID02_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID02_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID02_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID02_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID02_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID02_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID02_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID02_MIDM_DEFVAL         0x3f0UL

    #define XLPD_XPPU_MSTR_ID02_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID02_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID02_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID02_MID_DEFVAL          0x10UL

/**
 * Register: XlpdXppuMstrId03
 */
    #define XLPD_XPPU_MSTR_ID03                     ( ( XLPD_XPPU_BASEADDR ) +0x0000010CUL )
    #define XLPD_XPPU_MSTR_ID03_RSTVAL              0x83c00080UL

    #define XLPD_XPPU_MSTR_ID03_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID03_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID03_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID03_MIDP_DEFVAL         0x1UL

    #define XLPD_XPPU_MSTR_ID03_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID03_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID03_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID03_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID03_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID03_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID03_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID03_MIDM_DEFVAL         0x3c0UL

    #define XLPD_XPPU_MSTR_ID03_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID03_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID03_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID03_MID_DEFVAL          0x80UL

/**
 * Register: XlpdXppuMstrId04
 */
    #define XLPD_XPPU_MSTR_ID04                     ( ( XLPD_XPPU_BASEADDR ) +0x00000110UL )
    #define XLPD_XPPU_MSTR_ID04_RSTVAL              0x83c30080UL

    #define XLPD_XPPU_MSTR_ID04_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID04_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID04_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID04_MIDP_DEFVAL         0x1UL

    #define XLPD_XPPU_MSTR_ID04_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID04_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID04_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID04_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID04_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID04_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID04_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID04_MIDM_DEFVAL         0x3c3UL

    #define XLPD_XPPU_MSTR_ID04_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID04_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID04_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID04_MID_DEFVAL          0x80UL

/**
 * Register: XlpdXppuMstrId05
 */
    #define XLPD_XPPU_MSTR_ID05                     ( ( XLPD_XPPU_BASEADDR ) +0x00000114UL )
    #define XLPD_XPPU_MSTR_ID05_RSTVAL              0x03c30081UL

    #define XLPD_XPPU_MSTR_ID05_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID05_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID05_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID05_MIDP_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID05_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID05_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID05_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID05_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID05_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID05_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID05_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID05_MIDM_DEFVAL         0x3c3UL

    #define XLPD_XPPU_MSTR_ID05_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID05_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID05_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID05_MID_DEFVAL          0x81UL

/**
 * Register: XlpdXppuMstrId06
 */
    #define XLPD_XPPU_MSTR_ID06                     ( ( XLPD_XPPU_BASEADDR ) +0x00000118UL )
    #define XLPD_XPPU_MSTR_ID06_RSTVAL              0x03c30082UL

    #define XLPD_XPPU_MSTR_ID06_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID06_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID06_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID06_MIDP_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID06_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID06_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID06_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID06_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID06_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID06_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID06_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID06_MIDM_DEFVAL         0x3c3UL

    #define XLPD_XPPU_MSTR_ID06_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID06_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID06_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID06_MID_DEFVAL          0x82UL

/**
 * Register: XlpdXppuMstrId07
 */
    #define XLPD_XPPU_MSTR_ID07                     ( ( XLPD_XPPU_BASEADDR ) +0x0000011CUL )
    #define XLPD_XPPU_MSTR_ID07_RSTVAL              0x83c30083UL

    #define XLPD_XPPU_MSTR_ID07_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID07_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID07_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID07_MIDP_DEFVAL         0x1UL

    #define XLPD_XPPU_MSTR_ID07_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID07_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID07_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID07_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID07_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID07_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID07_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID07_MIDM_DEFVAL         0x3c3UL

    #define XLPD_XPPU_MSTR_ID07_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID07_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID07_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID07_MID_DEFVAL          0x83UL

/**
 * Register: XlpdXppuMstrId08
 */
    #define XLPD_XPPU_MSTR_ID08                     ( ( XLPD_XPPU_BASEADDR ) +0x00000120UL )
    #define XLPD_XPPU_MSTR_ID08_RSTVAL              0x00000000UL

    #define XLPD_XPPU_MSTR_ID08_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID08_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID08_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID08_MIDP_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID08_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID08_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID08_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID08_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID08_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID08_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID08_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID08_MIDM_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID08_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID08_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID08_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID08_MID_DEFVAL          0x0UL

/**
 * Register: XlpdXppuMstrId09
 */
    #define XLPD_XPPU_MSTR_ID09                     ( ( XLPD_XPPU_BASEADDR ) +0x00000124UL )
    #define XLPD_XPPU_MSTR_ID09_RSTVAL              0x00000000UL

    #define XLPD_XPPU_MSTR_ID09_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID09_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID09_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID09_MIDP_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID09_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID09_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID09_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID09_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID09_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID09_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID09_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID09_MIDM_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID09_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID09_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID09_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID09_MID_DEFVAL          0x0UL

/**
 * Register: XlpdXppuMstrId10
 */
    #define XLPD_XPPU_MSTR_ID10                     ( ( XLPD_XPPU_BASEADDR ) +0x00000128UL )
    #define XLPD_XPPU_MSTR_ID10_RSTVAL              0x00000000UL

    #define XLPD_XPPU_MSTR_ID10_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID10_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID10_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID10_MIDP_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID10_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID10_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID10_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID10_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID10_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID10_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID10_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID10_MIDM_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID10_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID10_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID10_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID10_MID_DEFVAL          0x0UL

/**
 * Register: XlpdXppuMstrId11
 */
    #define XLPD_XPPU_MSTR_ID11                     ( ( XLPD_XPPU_BASEADDR ) +0x0000012CUL )
    #define XLPD_XPPU_MSTR_ID11_RSTVAL              0x00000000UL

    #define XLPD_XPPU_MSTR_ID11_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID11_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID11_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID11_MIDP_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID11_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID11_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID11_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID11_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID11_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID11_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID11_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID11_MIDM_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID11_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID11_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID11_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID11_MID_DEFVAL          0x0UL

/**
 * Register: XlpdXppuMstrId12
 */
    #define XLPD_XPPU_MSTR_ID12                     ( ( XLPD_XPPU_BASEADDR ) +0x00000130UL )
    #define XLPD_XPPU_MSTR_ID12_RSTVAL              0x00000000UL

    #define XLPD_XPPU_MSTR_ID12_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID12_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID12_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID12_MIDP_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID12_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID12_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID12_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID12_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID12_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID12_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID12_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID12_MIDM_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID12_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID12_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID12_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID12_MID_DEFVAL          0x0UL

/**
 * Register: XlpdXppuMstrId13
 */
    #define XLPD_XPPU_MSTR_ID13                     ( ( XLPD_XPPU_BASEADDR ) +0x00000134UL )
    #define XLPD_XPPU_MSTR_ID13_RSTVAL              0x00000000UL

    #define XLPD_XPPU_MSTR_ID13_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID13_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID13_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID13_MIDP_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID13_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID13_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID13_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID13_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID13_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID13_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID13_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID13_MIDM_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID13_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID13_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID13_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID13_MID_DEFVAL          0x0UL

/**
 * Register: XlpdXppuMstrId14
 */
    #define XLPD_XPPU_MSTR_ID14                     ( ( XLPD_XPPU_BASEADDR ) +0x00000138UL )
    #define XLPD_XPPU_MSTR_ID14_RSTVAL              0x00000000UL

    #define XLPD_XPPU_MSTR_ID14_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID14_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID14_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID14_MIDP_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID14_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID14_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID14_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID14_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID14_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID14_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID14_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID14_MIDM_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID14_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID14_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID14_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID14_MID_DEFVAL          0x0UL

/**
 * Register: XlpdXppuMstrId15
 */
    #define XLPD_XPPU_MSTR_ID15                     ( ( XLPD_XPPU_BASEADDR ) +0x0000013CUL )
    #define XLPD_XPPU_MSTR_ID15_RSTVAL              0x00000000UL

    #define XLPD_XPPU_MSTR_ID15_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID15_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID15_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID15_MIDP_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID15_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID15_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID15_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID15_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID15_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID15_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID15_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID15_MIDM_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID15_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID15_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID15_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID15_MID_DEFVAL          0x0UL

/**
 * Register: XlpdXppuMstrId16
 */
    #define XLPD_XPPU_MSTR_ID16                     ( ( XLPD_XPPU_BASEADDR ) +0x00000140UL )
    #define XLPD_XPPU_MSTR_ID16_RSTVAL              0x00000000UL

    #define XLPD_XPPU_MSTR_ID16_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID16_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID16_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID16_MIDP_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID16_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID16_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID16_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID16_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID16_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID16_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID16_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID16_MIDM_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID16_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID16_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID16_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID16_MID_DEFVAL          0x0UL

/**
 * Register: XlpdXppuMstrId17
 */
    #define XLPD_XPPU_MSTR_ID17                     ( ( XLPD_XPPU_BASEADDR ) +0x00000144UL )
    #define XLPD_XPPU_MSTR_ID17_RSTVAL              0x00000000UL

    #define XLPD_XPPU_MSTR_ID17_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID17_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID17_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID17_MIDP_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID17_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID17_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID17_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID17_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID17_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID17_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID17_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID17_MIDM_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID17_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID17_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID17_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID17_MID_DEFVAL          0x0UL

/**
 * Register: XlpdXppuMstrId18
 */
    #define XLPD_XPPU_MSTR_ID18                     ( ( XLPD_XPPU_BASEADDR ) +0x00000148UL )
    #define XLPD_XPPU_MSTR_ID18_RSTVAL              0x00000000UL

    #define XLPD_XPPU_MSTR_ID18_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID18_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID18_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID18_MIDP_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID18_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID18_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID18_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID18_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID18_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID18_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID18_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID18_MIDM_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID18_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID18_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID18_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID18_MID_DEFVAL          0x0UL

/**
 * Register: XlpdXppuMstrId19
 */
    #define XLPD_XPPU_MSTR_ID19                     ( ( XLPD_XPPU_BASEADDR ) +0x0000014CUL )
    #define XLPD_XPPU_MSTR_ID19_RSTVAL              0x00000000UL

    #define XLPD_XPPU_MSTR_ID19_MIDP_SHIFT          31UL
    #define XLPD_XPPU_MSTR_ID19_MIDP_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID19_MIDP_MASK           0x80000000UL
    #define XLPD_XPPU_MSTR_ID19_MIDP_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID19_MIDR_SHIFT          30UL
    #define XLPD_XPPU_MSTR_ID19_MIDR_WIDTH          1UL
    #define XLPD_XPPU_MSTR_ID19_MIDR_MASK           0x40000000UL
    #define XLPD_XPPU_MSTR_ID19_MIDR_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID19_MIDM_SHIFT          16UL
    #define XLPD_XPPU_MSTR_ID19_MIDM_WIDTH          10UL
    #define XLPD_XPPU_MSTR_ID19_MIDM_MASK           0x03ff0000UL
    #define XLPD_XPPU_MSTR_ID19_MIDM_DEFVAL         0x0UL

    #define XLPD_XPPU_MSTR_ID19_MID_SHIFT           0UL
    #define XLPD_XPPU_MSTR_ID19_MID_WIDTH           10UL
    #define XLPD_XPPU_MSTR_ID19_MID_MASK            0x000003ffUL
    #define XLPD_XPPU_MSTR_ID19_MID_DEFVAL          0x0UL


    #ifdef __cplusplus
}
    #endif

#endif /* __XLPD_XPPU_H__ */
