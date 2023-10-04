/* ### HEADER ### */

#ifndef __XFPD_XMPU_SINK_H__
    #define __XFPD_XMPU_SINK_H__


    #ifdef __cplusplus
    extern "C" {
    #endif

/**
 * XfpdXmpuSink Base Address
 */
    #define XFPD_XMPU_SINK_BASEADDR                 0xFD4F0000UL

/**
 * Register: XfpdXmpuSinkErrSts
 */
    #define XFPD_XMPU_SINK_ERR_STS                  ( ( XFPD_XMPU_SINK_BASEADDR ) +0x0000FF00UL )
    #define XFPD_XMPU_SINK_ERR_STS_RSTVAL           0x00000000UL

    #define XFPD_XMPU_SINK_ERR_STS_RDWR_SHIFT       31UL
    #define XFPD_XMPU_SINK_ERR_STS_RDWR_WIDTH       1UL
    #define XFPD_XMPU_SINK_ERR_STS_RDWR_MASK        0x80000000UL
    #define XFPD_XMPU_SINK_ERR_STS_RDWR_DEFVAL      0x0UL

    #define XFPD_XMPU_SINK_ERR_STS_ADDR_SHIFT       0UL
    #define XFPD_XMPU_SINK_ERR_STS_ADDR_WIDTH       12UL
    #define XFPD_XMPU_SINK_ERR_STS_ADDR_MASK        0x00000fffUL
    #define XFPD_XMPU_SINK_ERR_STS_ADDR_DEFVAL      0x0UL

/**
 * Register: XfpdXmpuSinkIsr
 */
    #define XFPD_XMPU_SINK_ISR                      ( ( XFPD_XMPU_SINK_BASEADDR ) +0x0000FF10UL )
    #define XFPD_XMPU_SINK_ISR_RSTVAL               0x00000000UL

    #define XFPD_XMPU_SINK_ISRADDRDECDERR_SHIFT     0UL
    #define XFPD_XMPU_SINK_ISRADDRDECDERR_WIDTH     1UL
    #define XFPD_XMPU_SINK_ISRADDRDECDERR_MASK      0x00000001UL
    #define XFPD_XMPU_SINK_ISRADDRDECDERR_DEFVAL    0x0UL

/**
 * Register: XfpdXmpuSinkImr
 */
    #define XFPD_XMPU_SINK_IMR                      ( ( XFPD_XMPU_SINK_BASEADDR ) +0x0000FF14UL )
    #define XFPD_XMPU_SINK_IMR_RSTVAL               0x00000001UL

    #define XFPD_XMPU_SINK_IMRADDRDECDERR_SHIFT     0UL
    #define XFPD_XMPU_SINK_IMRADDRDECDERR_WIDTH     1UL
    #define XFPD_XMPU_SINK_IMRADDRDECDERR_MASK      0x00000001UL
    #define XFPD_XMPU_SINK_IMRADDRDECDERR_DEFVAL    0x1UL

/**
 * Register: XfpdXmpuSinkIer
 */
    #define XFPD_XMPU_SINK_IER                      ( ( XFPD_XMPU_SINK_BASEADDR ) +0x0000FF18UL )
    #define XFPD_XMPU_SINK_IER_RSTVAL               0x00000000UL

    #define XFPD_XMPU_SINK_IERADDRDECDERR_SHIFT     0UL
    #define XFPD_XMPU_SINK_IERADDRDECDERR_WIDTH     1UL
    #define XFPD_XMPU_SINK_IERADDRDECDERR_MASK      0x00000001UL
    #define XFPD_XMPU_SINK_IERADDRDECDERR_DEFVAL    0x0UL

/**
 * Register: XfpdXmpuSinkIdr
 */
    #define XFPD_XMPU_SINK_IDR                      ( ( XFPD_XMPU_SINK_BASEADDR ) +0x0000FF1CUL )
    #define XFPD_XMPU_SINK_IDR_RSTVAL               0x00000000UL

    #define XFPD_XMPU_SINK_IDRADDRDECDERR_SHIFT     0UL
    #define XFPD_XMPU_SINK_IDRADDRDECDERR_WIDTH     1UL
    #define XFPD_XMPU_SINK_IDRADDRDECDERR_MASK      0x00000001UL
    #define XFPD_XMPU_SINK_IDRADDRDECDERR_DEFVAL    0x0UL


    #ifdef __cplusplus
}
    #endif

#endif /* __XFPD_XMPU_SINK_H__ */
