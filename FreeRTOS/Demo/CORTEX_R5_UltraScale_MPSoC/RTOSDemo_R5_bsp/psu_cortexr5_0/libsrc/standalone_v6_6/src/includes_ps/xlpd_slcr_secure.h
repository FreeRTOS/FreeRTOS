/* ### HEADER ### */

#ifndef __XLPD_SLCR_SECURE_H__
    #define __XLPD_SLCR_SECURE_H__


    #ifdef __cplusplus
    extern "C" {
    #endif

/**
 * XlpdSlcrSecure Base Address
 */
    #define XLPD_SLCR_SECURE_BASEADDR                 0xFF4B0000UL

/**
 * Register: XlpdSlcrSecCtrl
 */
    #define XLPD_SLCR_SEC_CTRL                        ( ( XLPD_SLCR_SECURE_BASEADDR ) +0x00000004UL )
    #define XLPD_SLCR_SEC_CTRL_RSTVAL                 0x00000000UL

    #define XLPD_SLCR_SEC_CTRL_SLVERR_EN_SHIFT        0UL
    #define XLPD_SLCR_SEC_CTRL_SLVERR_EN_WIDTH        1UL
    #define XLPD_SLCR_SEC_CTRL_SLVERR_EN_MASK         0x00000001UL
    #define XLPD_SLCR_SEC_CTRL_SLVERR_EN_DEFVAL       0x0UL

/**
 * Register: XlpdSlcrSecIsr
 */
    #define XLPD_SLCR_SEC_ISR                         ( ( XLPD_SLCR_SECURE_BASEADDR ) +0x00000008UL )
    #define XLPD_SLCR_SEC_ISR_RSTVAL                  0x00000000UL

    #define XLPD_SLCR_SEC_ISR_ADDR_DECD_ERR_SHIFT     0UL
    #define XLPD_SLCR_SEC_ISR_ADDR_DECD_ERR_WIDTH     1UL
    #define XLPD_SLCR_SEC_ISR_ADDR_DECD_ERR_MASK      0x00000001UL
    #define XLPD_SLCR_SEC_ISR_ADDR_DECD_ERR_DEFVAL    0x0UL

/**
 * Register: XlpdSlcrSecImr
 */
    #define XLPD_SLCR_SEC_IMR                         ( ( XLPD_SLCR_SECURE_BASEADDR ) +0x0000000CUL )
    #define XLPD_SLCR_SEC_IMR_RSTVAL                  0x00000001UL

    #define XLPD_SLCR_SEC_IMR_ADDR_DECD_ERR_SHIFT     0UL
    #define XLPD_SLCR_SEC_IMR_ADDR_DECD_ERR_WIDTH     1UL
    #define XLPD_SLCR_SEC_IMR_ADDR_DECD_ERR_MASK      0x00000001UL
    #define XLPD_SLCR_SEC_IMR_ADDR_DECD_ERR_DEFVAL    0x1UL

/**
 * Register: XlpdSlcrSecIer
 */
    #define XLPD_SLCR_SEC_IER                         ( ( XLPD_SLCR_SECURE_BASEADDR ) +0x00000010UL )
    #define XLPD_SLCR_SEC_IER_RSTVAL                  0x00000000UL

    #define XLPD_SLCR_SEC_IER_ADDR_DECD_ERR_SHIFT     0UL
    #define XLPD_SLCR_SEC_IER_ADDR_DECD_ERR_WIDTH     1UL
    #define XLPD_SLCR_SEC_IER_ADDR_DECD_ERR_MASK      0x00000001UL
    #define XLPD_SLCR_SEC_IER_ADDR_DECD_ERR_DEFVAL    0x0UL

/**
 * Register: XlpdSlcrSecIdr
 */
    #define XLPD_SLCR_SEC_IDR                         ( ( XLPD_SLCR_SECURE_BASEADDR ) +0x00000014UL )
    #define XLPD_SLCR_SEC_IDR_RSTVAL                  0x00000000UL

    #define XLPD_SLCR_SEC_IDR_ADDR_DECD_ERR_SHIFT     0UL
    #define XLPD_SLCR_SEC_IDR_ADDR_DECD_ERR_WIDTH     1UL
    #define XLPD_SLCR_SEC_IDR_ADDR_DECD_ERR_MASK      0x00000001UL
    #define XLPD_SLCR_SEC_IDR_ADDR_DECD_ERR_DEFVAL    0x0UL

/**
 * Register: XlpdSlcrSecItr
 */
    #define XLPD_SLCR_SEC_ITR                         ( ( XLPD_SLCR_SECURE_BASEADDR ) +0x00000018UL )
    #define XLPD_SLCR_SEC_ITR_RSTVAL                  0x00000000UL

    #define XLPD_SLCR_SEC_ITR_ADDR_DECD_ERR_SHIFT     0UL
    #define XLPD_SLCR_SEC_ITR_ADDR_DECD_ERR_WIDTH     1UL
    #define XLPD_SLCR_SEC_ITR_ADDR_DECD_ERR_MASK      0x00000001UL
    #define XLPD_SLCR_SEC_ITR_ADDR_DECD_ERR_DEFVAL    0x0UL

/**
 * Register: XlpdSlcrSecRpu
 */
    #define XLPD_SLCR_SEC_RPU                         ( ( XLPD_SLCR_SECURE_BASEADDR ) +0x00000020UL )
    #define XLPD_SLCR_SEC_RPU_RSTVAL                  0x00000000UL

    #define XLPD_SLCR_SEC_RPU_TZ_R5_1_SHIFT           1UL
    #define XLPD_SLCR_SEC_RPU_TZ_R5_1_WIDTH           1UL
    #define XLPD_SLCR_SEC_RPU_TZ_R5_1_MASK            0x00000002UL
    #define XLPD_SLCR_SEC_RPU_TZ_R5_1_DEFVAL          0x0UL

    #define XLPD_SLCR_SEC_RPU_TZ_R5_0_SHIFT           0UL
    #define XLPD_SLCR_SEC_RPU_TZ_R5_0_WIDTH           1UL
    #define XLPD_SLCR_SEC_RPU_TZ_R5_0_MASK            0x00000001UL
    #define XLPD_SLCR_SEC_RPU_TZ_R5_0_DEFVAL          0x0UL

/**
 * Register: XlpdSlcrSecAdma
 */
    #define XLPD_SLCR_SEC_ADMA                        ( ( XLPD_SLCR_SECURE_BASEADDR ) +0x00000024UL )
    #define XLPD_SLCR_SEC_ADMA_RSTVAL                 0x00000000UL

    #define XLPD_SLCR_SEC_ADMA_TZ_SHIFT               0UL
    #define XLPD_SLCR_SEC_ADMA_TZ_WIDTH               8UL
    #define XLPD_SLCR_SEC_ADMA_TZ_MASK                0x000000ffUL
    #define XLPD_SLCR_SEC_ADMA_TZ_DEFVAL              0x0UL

/**
 * Register: XlpdSlcrSecSafetyChk
 */
    #define XLPD_SLCR_SEC_SAFETY_CHK                  ( ( XLPD_SLCR_SECURE_BASEADDR ) +0x00000030UL )
    #define XLPD_SLCR_SEC_SAFETY_CHK_RSTVAL           0x00000000UL

    #define XLPD_SLCR_SEC_SAFETY_CHK_VAL_SHIFT        0UL
    #define XLPD_SLCR_SEC_SAFETY_CHK_VAL_WIDTH        32UL
    #define XLPD_SLCR_SEC_SAFETY_CHK_VAL_MASK         0xffffffffUL
    #define XLPD_SLCR_SEC_SAFETY_CHK_VAL_DEFVAL       0x0UL

/**
 * Register: XlpdSlcrSecUsb
 */
    #define XLPD_SLCR_SEC_USB                         ( ( XLPD_SLCR_SECURE_BASEADDR ) +0x00000034UL )
    #define XLPD_SLCR_SEC_USB_RSTVAL                  0x00000003UL

    #define XLPD_SLCR_SEC_USB_TZ_USB3_1_SHIFT         1UL
    #define XLPD_SLCR_SEC_USB_TZ_USB3_1_WIDTH         1UL
    #define XLPD_SLCR_SEC_USB_TZ_USB3_1_MASK          0x00000002UL
    #define XLPD_SLCR_SEC_USB_TZ_USB3_1_DEFVAL        0x1UL

    #define XLPD_SLCR_SEC_USB_TZ_USB3_0_SHIFT         0UL
    #define XLPD_SLCR_SEC_USB_TZ_USB3_0_WIDTH         1UL
    #define XLPD_SLCR_SEC_USB_TZ_USB3_0_MASK          0x00000001UL
    #define XLPD_SLCR_SEC_USB_TZ_USB3_0_DEFVAL        0x1UL


    #ifdef __cplusplus
}
    #endif

#endif /* __XLPD_SLCR_SECURE_H__ */
