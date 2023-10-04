/* ### HEADER ### */

#ifndef __XIOU_SLCR_H__
    #define __XIOU_SLCR_H__


    #ifdef __cplusplus
    extern "C" {
    #endif

/**
 * XiouSlcr Base Address
 */
    #define XIOU_SLCR_BASEADDR                                    0xFF180000UL

/**
 * Register: XiouSlcrMioPin0
 */
    #define XIOU_SLCR_MIO_PIN_0                                   ( ( XIOU_SLCR_BASEADDR ) +0x00000000UL )
    #define XIOU_SLCR_MIO_PIN_0_RSTVAL                            0x00000000UL

    #define XIOU_SLCR_MIO_PIN_0_L3_SEL_SHIFT                      5UL
    #define XIOU_SLCR_MIO_PIN_0_L3_SEL_WIDTH                      3UL
    #define XIOU_SLCR_MIO_PIN_0_L3_SEL_MASK                       0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_0_L3_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_0_L2_SEL_SHIFT                      3UL
    #define XIOU_SLCR_MIO_PIN_0_L2_SEL_WIDTH                      2UL
    #define XIOU_SLCR_MIO_PIN_0_L2_SEL_MASK                       0x00000018UL
    #define XIOU_SLCR_MIO_PIN_0_L2_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_0_L1_SEL_SHIFT                      2UL
    #define XIOU_SLCR_MIO_PIN_0_L1_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_0_L1_SEL_MASK                       0x00000004UL
    #define XIOU_SLCR_MIO_PIN_0_L1_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_0_L0_SEL_SHIFT                      1UL
    #define XIOU_SLCR_MIO_PIN_0_L0_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_0_L0_SEL_MASK                       0x00000002UL
    #define XIOU_SLCR_MIO_PIN_0_L0_SEL_DEFVAL                     0x0UL

/**
 * Register: XiouSlcrMioPin1
 */
    #define XIOU_SLCR_MIO_PIN_1                                   ( ( XIOU_SLCR_BASEADDR ) +0x00000004UL )
    #define XIOU_SLCR_MIO_PIN_1_RSTVAL                            0x00000000UL

    #define XIOU_SLCR_MIO_PIN_1_L3_SEL_SHIFT                      5UL
    #define XIOU_SLCR_MIO_PIN_1_L3_SEL_WIDTH                      3UL
    #define XIOU_SLCR_MIO_PIN_1_L3_SEL_MASK                       0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_1_L3_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_1_L2_SEL_SHIFT                      3UL
    #define XIOU_SLCR_MIO_PIN_1_L2_SEL_WIDTH                      2UL
    #define XIOU_SLCR_MIO_PIN_1_L2_SEL_MASK                       0x00000018UL
    #define XIOU_SLCR_MIO_PIN_1_L2_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_1_L1_SEL_SHIFT                      2UL
    #define XIOU_SLCR_MIO_PIN_1_L1_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_1_L1_SEL_MASK                       0x00000004UL
    #define XIOU_SLCR_MIO_PIN_1_L1_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_1_L0_SEL_SHIFT                      1UL
    #define XIOU_SLCR_MIO_PIN_1_L0_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_1_L0_SEL_MASK                       0x00000002UL
    #define XIOU_SLCR_MIO_PIN_1_L0_SEL_DEFVAL                     0x0UL

/**
 * Register: XiouSlcrMioPin2
 */
    #define XIOU_SLCR_MIO_PIN_2                                   ( ( XIOU_SLCR_BASEADDR ) +0x00000008UL )
    #define XIOU_SLCR_MIO_PIN_2_RSTVAL                            0x00000000UL

    #define XIOU_SLCR_MIO_PIN_2_L3_SEL_SHIFT                      5UL
    #define XIOU_SLCR_MIO_PIN_2_L3_SEL_WIDTH                      3UL
    #define XIOU_SLCR_MIO_PIN_2_L3_SEL_MASK                       0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_2_L3_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_2_L2_SEL_SHIFT                      3UL
    #define XIOU_SLCR_MIO_PIN_2_L2_SEL_WIDTH                      2UL
    #define XIOU_SLCR_MIO_PIN_2_L2_SEL_MASK                       0x00000018UL
    #define XIOU_SLCR_MIO_PIN_2_L2_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_2_L1_SEL_SHIFT                      2UL
    #define XIOU_SLCR_MIO_PIN_2_L1_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_2_L1_SEL_MASK                       0x00000004UL
    #define XIOU_SLCR_MIO_PIN_2_L1_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_2_L0_SEL_SHIFT                      1UL
    #define XIOU_SLCR_MIO_PIN_2_L0_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_2_L0_SEL_MASK                       0x00000002UL
    #define XIOU_SLCR_MIO_PIN_2_L0_SEL_DEFVAL                     0x0UL

/**
 * Register: XiouSlcrMioPin3
 */
    #define XIOU_SLCR_MIO_PIN_3                                   ( ( XIOU_SLCR_BASEADDR ) +0x0000000CUL )
    #define XIOU_SLCR_MIO_PIN_3_RSTVAL                            0x00000000UL

    #define XIOU_SLCR_MIO_PIN_3_L3_SEL_SHIFT                      5UL
    #define XIOU_SLCR_MIO_PIN_3_L3_SEL_WIDTH                      3UL
    #define XIOU_SLCR_MIO_PIN_3_L3_SEL_MASK                       0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_3_L3_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_3_L2_SEL_SHIFT                      3UL
    #define XIOU_SLCR_MIO_PIN_3_L2_SEL_WIDTH                      2UL
    #define XIOU_SLCR_MIO_PIN_3_L2_SEL_MASK                       0x00000018UL
    #define XIOU_SLCR_MIO_PIN_3_L2_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_3_L1_SEL_SHIFT                      2UL
    #define XIOU_SLCR_MIO_PIN_3_L1_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_3_L1_SEL_MASK                       0x00000004UL
    #define XIOU_SLCR_MIO_PIN_3_L1_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_3_L0_SEL_SHIFT                      1UL
    #define XIOU_SLCR_MIO_PIN_3_L0_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_3_L0_SEL_MASK                       0x00000002UL
    #define XIOU_SLCR_MIO_PIN_3_L0_SEL_DEFVAL                     0x0UL

/**
 * Register: XiouSlcrMioPin4
 */
    #define XIOU_SLCR_MIO_PIN_4                                   ( ( XIOU_SLCR_BASEADDR ) +0x00000010UL )
    #define XIOU_SLCR_MIO_PIN_4_RSTVAL                            0x00000000UL

    #define XIOU_SLCR_MIO_PIN_4_L3_SEL_SHIFT                      5UL
    #define XIOU_SLCR_MIO_PIN_4_L3_SEL_WIDTH                      3UL
    #define XIOU_SLCR_MIO_PIN_4_L3_SEL_MASK                       0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_4_L3_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_4_L2_SEL_SHIFT                      3UL
    #define XIOU_SLCR_MIO_PIN_4_L2_SEL_WIDTH                      2UL
    #define XIOU_SLCR_MIO_PIN_4_L2_SEL_MASK                       0x00000018UL
    #define XIOU_SLCR_MIO_PIN_4_L2_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_4_L1_SEL_SHIFT                      2UL
    #define XIOU_SLCR_MIO_PIN_4_L1_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_4_L1_SEL_MASK                       0x00000004UL
    #define XIOU_SLCR_MIO_PIN_4_L1_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_4_L0_SEL_SHIFT                      1UL
    #define XIOU_SLCR_MIO_PIN_4_L0_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_4_L0_SEL_MASK                       0x00000002UL
    #define XIOU_SLCR_MIO_PIN_4_L0_SEL_DEFVAL                     0x0UL

/**
 * Register: XiouSlcrMioPin5
 */
    #define XIOU_SLCR_MIO_PIN_5                                   ( ( XIOU_SLCR_BASEADDR ) +0x00000014UL )
    #define XIOU_SLCR_MIO_PIN_5_RSTVAL                            0x00000000UL

    #define XIOU_SLCR_MIO_PIN_5_L3_SEL_SHIFT                      5UL
    #define XIOU_SLCR_MIO_PIN_5_L3_SEL_WIDTH                      3UL
    #define XIOU_SLCR_MIO_PIN_5_L3_SEL_MASK                       0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_5_L3_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_5_L2_SEL_SHIFT                      3UL
    #define XIOU_SLCR_MIO_PIN_5_L2_SEL_WIDTH                      2UL
    #define XIOU_SLCR_MIO_PIN_5_L2_SEL_MASK                       0x00000018UL
    #define XIOU_SLCR_MIO_PIN_5_L2_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_5_L1_SEL_SHIFT                      2UL
    #define XIOU_SLCR_MIO_PIN_5_L1_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_5_L1_SEL_MASK                       0x00000004UL
    #define XIOU_SLCR_MIO_PIN_5_L1_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_5_L0_SEL_SHIFT                      1UL
    #define XIOU_SLCR_MIO_PIN_5_L0_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_5_L0_SEL_MASK                       0x00000002UL
    #define XIOU_SLCR_MIO_PIN_5_L0_SEL_DEFVAL                     0x0UL

/**
 * Register: XiouSlcrMioPin6
 */
    #define XIOU_SLCR_MIO_PIN_6                                   ( ( XIOU_SLCR_BASEADDR ) +0x00000018UL )
    #define XIOU_SLCR_MIO_PIN_6_RSTVAL                            0x00000000UL

    #define XIOU_SLCR_MIO_PIN_6_L3_SEL_SHIFT                      5UL
    #define XIOU_SLCR_MIO_PIN_6_L3_SEL_WIDTH                      3UL
    #define XIOU_SLCR_MIO_PIN_6_L3_SEL_MASK                       0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_6_L3_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_6_L2_SEL_SHIFT                      3UL
    #define XIOU_SLCR_MIO_PIN_6_L2_SEL_WIDTH                      2UL
    #define XIOU_SLCR_MIO_PIN_6_L2_SEL_MASK                       0x00000018UL
    #define XIOU_SLCR_MIO_PIN_6_L2_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_6_L1_SEL_SHIFT                      2UL
    #define XIOU_SLCR_MIO_PIN_6_L1_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_6_L1_SEL_MASK                       0x00000004UL
    #define XIOU_SLCR_MIO_PIN_6_L1_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_6_L0_SEL_SHIFT                      1UL
    #define XIOU_SLCR_MIO_PIN_6_L0_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_6_L0_SEL_MASK                       0x00000002UL
    #define XIOU_SLCR_MIO_PIN_6_L0_SEL_DEFVAL                     0x0UL

/**
 * Register: XiouSlcrMioPin7
 */
    #define XIOU_SLCR_MIO_PIN_7                                   ( ( XIOU_SLCR_BASEADDR ) +0x0000001CUL )
    #define XIOU_SLCR_MIO_PIN_7_RSTVAL                            0x00000000UL

    #define XIOU_SLCR_MIO_PIN_7_L3_SEL_SHIFT                      5UL
    #define XIOU_SLCR_MIO_PIN_7_L3_SEL_WIDTH                      3UL
    #define XIOU_SLCR_MIO_PIN_7_L3_SEL_MASK                       0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_7_L3_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_7_L2_SEL_SHIFT                      3UL
    #define XIOU_SLCR_MIO_PIN_7_L2_SEL_WIDTH                      2UL
    #define XIOU_SLCR_MIO_PIN_7_L2_SEL_MASK                       0x00000018UL
    #define XIOU_SLCR_MIO_PIN_7_L2_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_7_L1_SEL_SHIFT                      2UL
    #define XIOU_SLCR_MIO_PIN_7_L1_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_7_L1_SEL_MASK                       0x00000004UL
    #define XIOU_SLCR_MIO_PIN_7_L1_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_7_L0_SEL_SHIFT                      1UL
    #define XIOU_SLCR_MIO_PIN_7_L0_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_7_L0_SEL_MASK                       0x00000002UL
    #define XIOU_SLCR_MIO_PIN_7_L0_SEL_DEFVAL                     0x0UL

/**
 * Register: XiouSlcrMioPin8
 */
    #define XIOU_SLCR_MIO_PIN_8                                   ( ( XIOU_SLCR_BASEADDR ) +0x00000020UL )
    #define XIOU_SLCR_MIO_PIN_8_RSTVAL                            0x00000000UL

    #define XIOU_SLCR_MIO_PIN_8_L3_SEL_SHIFT                      5UL
    #define XIOU_SLCR_MIO_PIN_8_L3_SEL_WIDTH                      3UL
    #define XIOU_SLCR_MIO_PIN_8_L3_SEL_MASK                       0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_8_L3_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_8_L2_SEL_SHIFT                      3UL
    #define XIOU_SLCR_MIO_PIN_8_L2_SEL_WIDTH                      2UL
    #define XIOU_SLCR_MIO_PIN_8_L2_SEL_MASK                       0x00000018UL
    #define XIOU_SLCR_MIO_PIN_8_L2_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_8_L1_SEL_SHIFT                      2UL
    #define XIOU_SLCR_MIO_PIN_8_L1_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_8_L1_SEL_MASK                       0x00000004UL
    #define XIOU_SLCR_MIO_PIN_8_L1_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_8_L0_SEL_SHIFT                      1UL
    #define XIOU_SLCR_MIO_PIN_8_L0_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_8_L0_SEL_MASK                       0x00000002UL
    #define XIOU_SLCR_MIO_PIN_8_L0_SEL_DEFVAL                     0x0UL

/**
 * Register: XiouSlcrMioPin9
 */
    #define XIOU_SLCR_MIO_PIN_9                                   ( ( XIOU_SLCR_BASEADDR ) +0x00000024UL )
    #define XIOU_SLCR_MIO_PIN_9_RSTVAL                            0x00000000UL

    #define XIOU_SLCR_MIO_PIN_9_L3_SEL_SHIFT                      5UL
    #define XIOU_SLCR_MIO_PIN_9_L3_SEL_WIDTH                      3UL
    #define XIOU_SLCR_MIO_PIN_9_L3_SEL_MASK                       0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_9_L3_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_9_L2_SEL_SHIFT                      3UL
    #define XIOU_SLCR_MIO_PIN_9_L2_SEL_WIDTH                      2UL
    #define XIOU_SLCR_MIO_PIN_9_L2_SEL_MASK                       0x00000018UL
    #define XIOU_SLCR_MIO_PIN_9_L2_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_9_L1_SEL_SHIFT                      2UL
    #define XIOU_SLCR_MIO_PIN_9_L1_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_9_L1_SEL_MASK                       0x00000004UL
    #define XIOU_SLCR_MIO_PIN_9_L1_SEL_DEFVAL                     0x0UL

    #define XIOU_SLCR_MIO_PIN_9_L0_SEL_SHIFT                      1UL
    #define XIOU_SLCR_MIO_PIN_9_L0_SEL_WIDTH                      1UL
    #define XIOU_SLCR_MIO_PIN_9_L0_SEL_MASK                       0x00000002UL
    #define XIOU_SLCR_MIO_PIN_9_L0_SEL_DEFVAL                     0x0UL

/**
 * Register: XiouSlcrMioPin10
 */
    #define XIOU_SLCR_MIO_PIN_10                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000028UL )
    #define XIOU_SLCR_MIO_PIN_10_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_10_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_10_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_10_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_10_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_10_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_10_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_10_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_10_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_10_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_10_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_10_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_10_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_10_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_10_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_10_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_10_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin11
 */
    #define XIOU_SLCR_MIO_PIN_11                                  ( ( XIOU_SLCR_BASEADDR ) +0x0000002CUL )
    #define XIOU_SLCR_MIO_PIN_11_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_11_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_11_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_11_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_11_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_11_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_11_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_11_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_11_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_11_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_11_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_11_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_11_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_11_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_11_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_11_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_11_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin12
 */
    #define XIOU_SLCR_MIO_PIN_12                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000030UL )
    #define XIOU_SLCR_MIO_PIN_12_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_12_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_12_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_12_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_12_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_12_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_12_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_12_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_12_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_12_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_12_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_12_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_12_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_12_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_12_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_12_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_12_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin13
 */
    #define XIOU_SLCR_MIO_PIN_13                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000034UL )
    #define XIOU_SLCR_MIO_PIN_13_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_13_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_13_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_13_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_13_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_13_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_13_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_13_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_13_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_13_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_13_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_13_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_13_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_13_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_13_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_13_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_13_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin14
 */
    #define XIOU_SLCR_MIO_PIN_14                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000038UL )
    #define XIOU_SLCR_MIO_PIN_14_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_14_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_14_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_14_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_14_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_14_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_14_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_14_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_14_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_14_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_14_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_14_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_14_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_14_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_14_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_14_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_14_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin15
 */
    #define XIOU_SLCR_MIO_PIN_15                                  ( ( XIOU_SLCR_BASEADDR ) +0x0000003CUL )
    #define XIOU_SLCR_MIO_PIN_15_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_15_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_15_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_15_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_15_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_15_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_15_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_15_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_15_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_15_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_15_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_15_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_15_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_15_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_15_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_15_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_15_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin16
 */
    #define XIOU_SLCR_MIO_PIN_16                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000040UL )
    #define XIOU_SLCR_MIO_PIN_16_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_16_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_16_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_16_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_16_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_16_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_16_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_16_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_16_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_16_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_16_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_16_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_16_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_16_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_16_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_16_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_16_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin17
 */
    #define XIOU_SLCR_MIO_PIN_17                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000044UL )
    #define XIOU_SLCR_MIO_PIN_17_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_17_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_17_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_17_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_17_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_17_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_17_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_17_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_17_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_17_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_17_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_17_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_17_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_17_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_17_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_17_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_17_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin18
 */
    #define XIOU_SLCR_MIO_PIN_18                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000048UL )
    #define XIOU_SLCR_MIO_PIN_18_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_18_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_18_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_18_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_18_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_18_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_18_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_18_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_18_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_18_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_18_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_18_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_18_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_18_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_18_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_18_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_18_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin19
 */
    #define XIOU_SLCR_MIO_PIN_19                                  ( ( XIOU_SLCR_BASEADDR ) +0x0000004CUL )
    #define XIOU_SLCR_MIO_PIN_19_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_19_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_19_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_19_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_19_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_19_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_19_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_19_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_19_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_19_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_19_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_19_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_19_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_19_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_19_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_19_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_19_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin20
 */
    #define XIOU_SLCR_MIO_PIN_20                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000050UL )
    #define XIOU_SLCR_MIO_PIN_20_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_20_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_20_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_20_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_20_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_20_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_20_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_20_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_20_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_20_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_20_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_20_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_20_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_20_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_20_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_20_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_20_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin21
 */
    #define XIOU_SLCR_MIO_PIN_21                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000054UL )
    #define XIOU_SLCR_MIO_PIN_21_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_21_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_21_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_21_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_21_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_21_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_21_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_21_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_21_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_21_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_21_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_21_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_21_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_21_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_21_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_21_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_21_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin22
 */
    #define XIOU_SLCR_MIO_PIN_22                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000058UL )
    #define XIOU_SLCR_MIO_PIN_22_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_22_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_22_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_22_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_22_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_22_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_22_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_22_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_22_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_22_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_22_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_22_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_22_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_22_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_22_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_22_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_22_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin23
 */
    #define XIOU_SLCR_MIO_PIN_23                                  ( ( XIOU_SLCR_BASEADDR ) +0x0000005CUL )
    #define XIOU_SLCR_MIO_PIN_23_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_23_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_23_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_23_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_23_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_23_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_23_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_23_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_23_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_23_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_23_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_23_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_23_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_23_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_23_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_23_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_23_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin24
 */
    #define XIOU_SLCR_MIO_PIN_24                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000060UL )
    #define XIOU_SLCR_MIO_PIN_24_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_24_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_24_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_24_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_24_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_24_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_24_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_24_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_24_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_24_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_24_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_24_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_24_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_24_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_24_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_24_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_24_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin25
 */
    #define XIOU_SLCR_MIO_PIN_25                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000064UL )
    #define XIOU_SLCR_MIO_PIN_25_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_25_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_25_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_25_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_25_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_25_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_25_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_25_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_25_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_25_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_25_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_25_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_25_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_25_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_25_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_25_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_25_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin26
 */
    #define XIOU_SLCR_MIO_PIN_26                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000068UL )
    #define XIOU_SLCR_MIO_PIN_26_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_26_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_26_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_26_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_26_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_26_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_26_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_26_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_26_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_26_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_26_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_26_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_26_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_26_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_26_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_26_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_26_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin27
 */
    #define XIOU_SLCR_MIO_PIN_27                                  ( ( XIOU_SLCR_BASEADDR ) +0x0000006CUL )
    #define XIOU_SLCR_MIO_PIN_27_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_27_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_27_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_27_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_27_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_27_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_27_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_27_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_27_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_27_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_27_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_27_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_27_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_27_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_27_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_27_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_27_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin28
 */
    #define XIOU_SLCR_MIO_PIN_28                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000070UL )
    #define XIOU_SLCR_MIO_PIN_28_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_28_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_28_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_28_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_28_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_28_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_28_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_28_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_28_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_28_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_28_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_28_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_28_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_28_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_28_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_28_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_28_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin29
 */
    #define XIOU_SLCR_MIO_PIN_29                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000074UL )
    #define XIOU_SLCR_MIO_PIN_29_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_29_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_29_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_29_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_29_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_29_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_29_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_29_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_29_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_29_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_29_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_29_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_29_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_29_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_29_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_29_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_29_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin30
 */
    #define XIOU_SLCR_MIO_PIN_30                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000078UL )
    #define XIOU_SLCR_MIO_PIN_30_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_30_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_30_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_30_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_30_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_30_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_30_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_30_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_30_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_30_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_30_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_30_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_30_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_30_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_30_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_30_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_30_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin31
 */
    #define XIOU_SLCR_MIO_PIN_31                                  ( ( XIOU_SLCR_BASEADDR ) +0x0000007CUL )
    #define XIOU_SLCR_MIO_PIN_31_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_31_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_31_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_31_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_31_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_31_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_31_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_31_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_31_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_31_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_31_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_31_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_31_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_31_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_31_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_31_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_31_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin32
 */
    #define XIOU_SLCR_MIO_PIN_32                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000080UL )
    #define XIOU_SLCR_MIO_PIN_32_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_32_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_32_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_32_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_32_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_32_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_32_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_32_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_32_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_32_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_32_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_32_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_32_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_32_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_32_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_32_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_32_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin33
 */
    #define XIOU_SLCR_MIO_PIN_33                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000084UL )
    #define XIOU_SLCR_MIO_PIN_33_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_33_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_33_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_33_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_33_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_33_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_33_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_33_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_33_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_33_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_33_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_33_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_33_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_33_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_33_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_33_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_33_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin34
 */
    #define XIOU_SLCR_MIO_PIN_34                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000088UL )
    #define XIOU_SLCR_MIO_PIN_34_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_34_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_34_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_34_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_34_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_34_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_34_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_34_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_34_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_34_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_34_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_34_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_34_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_34_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_34_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_34_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_34_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin35
 */
    #define XIOU_SLCR_MIO_PIN_35                                  ( ( XIOU_SLCR_BASEADDR ) +0x0000008CUL )
    #define XIOU_SLCR_MIO_PIN_35_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_35_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_35_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_35_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_35_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_35_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_35_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_35_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_35_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_35_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_35_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_35_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_35_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_35_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_35_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_35_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_35_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin36
 */
    #define XIOU_SLCR_MIO_PIN_36                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000090UL )
    #define XIOU_SLCR_MIO_PIN_36_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_36_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_36_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_36_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_36_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_36_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_36_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_36_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_36_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_36_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_36_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_36_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_36_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_36_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_36_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_36_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_36_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin37
 */
    #define XIOU_SLCR_MIO_PIN_37                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000094UL )
    #define XIOU_SLCR_MIO_PIN_37_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_37_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_37_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_37_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_37_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_37_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_37_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_37_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_37_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_37_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_37_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_37_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_37_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_37_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_37_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_37_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_37_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin38
 */
    #define XIOU_SLCR_MIO_PIN_38                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000098UL )
    #define XIOU_SLCR_MIO_PIN_38_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_38_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_38_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_38_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_38_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_38_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_38_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_38_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_38_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_38_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_38_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_38_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_38_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_38_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_38_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_38_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_38_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin39
 */
    #define XIOU_SLCR_MIO_PIN_39                                  ( ( XIOU_SLCR_BASEADDR ) +0x0000009CUL )
    #define XIOU_SLCR_MIO_PIN_39_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_39_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_39_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_39_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_39_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_39_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_39_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_39_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_39_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_39_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_39_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_39_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_39_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_39_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_39_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_39_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_39_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin40
 */
    #define XIOU_SLCR_MIO_PIN_40                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000A0UL )
    #define XIOU_SLCR_MIO_PIN_40_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_40_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_40_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_40_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_40_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_40_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_40_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_40_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_40_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_40_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_40_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_40_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_40_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_40_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_40_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_40_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_40_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin41
 */
    #define XIOU_SLCR_MIO_PIN_41                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000A4UL )
    #define XIOU_SLCR_MIO_PIN_41_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_41_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_41_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_41_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_41_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_41_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_41_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_41_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_41_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_41_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_41_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_41_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_41_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_41_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_41_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_41_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_41_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin42
 */
    #define XIOU_SLCR_MIO_PIN_42                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000A8UL )
    #define XIOU_SLCR_MIO_PIN_42_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_42_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_42_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_42_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_42_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_42_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_42_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_42_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_42_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_42_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_42_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_42_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_42_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_42_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_42_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_42_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_42_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin43
 */
    #define XIOU_SLCR_MIO_PIN_43                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000ACUL )
    #define XIOU_SLCR_MIO_PIN_43_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_43_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_43_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_43_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_43_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_43_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_43_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_43_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_43_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_43_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_43_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_43_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_43_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_43_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_43_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_43_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_43_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin44
 */
    #define XIOU_SLCR_MIO_PIN_44                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000B0UL )
    #define XIOU_SLCR_MIO_PIN_44_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_44_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_44_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_44_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_44_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_44_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_44_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_44_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_44_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_44_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_44_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_44_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_44_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_44_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_44_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_44_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_44_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin45
 */
    #define XIOU_SLCR_MIO_PIN_45                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000B4UL )
    #define XIOU_SLCR_MIO_PIN_45_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_45_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_45_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_45_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_45_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_45_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_45_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_45_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_45_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_45_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_45_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_45_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_45_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_45_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_45_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_45_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_45_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin46
 */
    #define XIOU_SLCR_MIO_PIN_46                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000B8UL )
    #define XIOU_SLCR_MIO_PIN_46_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_46_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_46_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_46_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_46_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_46_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_46_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_46_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_46_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_46_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_46_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_46_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_46_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_46_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_46_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_46_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_46_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin47
 */
    #define XIOU_SLCR_MIO_PIN_47                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000BCUL )
    #define XIOU_SLCR_MIO_PIN_47_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_47_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_47_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_47_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_47_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_47_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_47_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_47_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_47_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_47_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_47_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_47_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_47_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_47_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_47_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_47_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_47_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin48
 */
    #define XIOU_SLCR_MIO_PIN_48                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000C0UL )
    #define XIOU_SLCR_MIO_PIN_48_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_48_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_48_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_48_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_48_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_48_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_48_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_48_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_48_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_48_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_48_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_48_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_48_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_48_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_48_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_48_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_48_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin49
 */
    #define XIOU_SLCR_MIO_PIN_49                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000C4UL )
    #define XIOU_SLCR_MIO_PIN_49_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_49_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_49_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_49_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_49_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_49_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_49_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_49_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_49_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_49_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_49_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_49_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_49_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_49_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_49_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_49_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_49_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin50
 */
    #define XIOU_SLCR_MIO_PIN_50                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000C8UL )
    #define XIOU_SLCR_MIO_PIN_50_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_50_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_50_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_50_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_50_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_50_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_50_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_50_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_50_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_50_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_50_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_50_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_50_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_50_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_50_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_50_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_50_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin51
 */
    #define XIOU_SLCR_MIO_PIN_51                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000CCUL )
    #define XIOU_SLCR_MIO_PIN_51_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_51_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_51_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_51_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_51_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_51_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_51_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_51_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_51_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_51_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_51_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_51_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_51_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_51_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_51_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_51_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_51_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin52
 */
    #define XIOU_SLCR_MIO_PIN_52                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000D0UL )
    #define XIOU_SLCR_MIO_PIN_52_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_52_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_52_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_52_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_52_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_52_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_52_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_52_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_52_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_52_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_52_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_52_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_52_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_52_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_52_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_52_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_52_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin53
 */
    #define XIOU_SLCR_MIO_PIN_53                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000D4UL )
    #define XIOU_SLCR_MIO_PIN_53_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_53_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_53_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_53_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_53_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_53_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_53_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_53_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_53_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_53_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_53_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_53_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_53_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_53_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_53_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_53_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_53_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin54
 */
    #define XIOU_SLCR_MIO_PIN_54                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000D8UL )
    #define XIOU_SLCR_MIO_PIN_54_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_54_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_54_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_54_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_54_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_54_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_54_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_54_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_54_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_54_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_54_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_54_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_54_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_54_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_54_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_54_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_54_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin55
 */
    #define XIOU_SLCR_MIO_PIN_55                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000DCUL )
    #define XIOU_SLCR_MIO_PIN_55_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_55_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_55_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_55_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_55_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_55_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_55_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_55_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_55_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_55_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_55_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_55_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_55_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_55_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_55_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_55_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_55_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin56
 */
    #define XIOU_SLCR_MIO_PIN_56                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000E0UL )
    #define XIOU_SLCR_MIO_PIN_56_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_56_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_56_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_56_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_56_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_56_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_56_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_56_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_56_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_56_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_56_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_56_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_56_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_56_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_56_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_56_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_56_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin57
 */
    #define XIOU_SLCR_MIO_PIN_57                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000E4UL )
    #define XIOU_SLCR_MIO_PIN_57_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_57_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_57_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_57_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_57_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_57_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_57_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_57_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_57_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_57_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_57_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_57_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_57_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_57_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_57_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_57_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_57_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin58
 */
    #define XIOU_SLCR_MIO_PIN_58                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000E8UL )
    #define XIOU_SLCR_MIO_PIN_58_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_58_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_58_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_58_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_58_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_58_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_58_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_58_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_58_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_58_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_58_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_58_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_58_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_58_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_58_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_58_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_58_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin59
 */
    #define XIOU_SLCR_MIO_PIN_59                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000ECUL )
    #define XIOU_SLCR_MIO_PIN_59_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_59_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_59_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_59_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_59_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_59_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_59_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_59_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_59_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_59_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_59_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_59_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_59_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_59_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_59_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_59_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_59_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin60
 */
    #define XIOU_SLCR_MIO_PIN_60                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000F0UL )
    #define XIOU_SLCR_MIO_PIN_60_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_60_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_60_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_60_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_60_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_60_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_60_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_60_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_60_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_60_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_60_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_60_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_60_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_60_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_60_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_60_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_60_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin61
 */
    #define XIOU_SLCR_MIO_PIN_61                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000F4UL )
    #define XIOU_SLCR_MIO_PIN_61_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_61_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_61_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_61_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_61_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_61_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_61_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_61_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_61_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_61_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_61_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_61_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_61_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_61_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_61_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_61_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_61_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin62
 */
    #define XIOU_SLCR_MIO_PIN_62                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000F8UL )
    #define XIOU_SLCR_MIO_PIN_62_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_62_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_62_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_62_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_62_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_62_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_62_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_62_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_62_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_62_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_62_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_62_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_62_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_62_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_62_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_62_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_62_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin63
 */
    #define XIOU_SLCR_MIO_PIN_63                                  ( ( XIOU_SLCR_BASEADDR ) +0x000000FCUL )
    #define XIOU_SLCR_MIO_PIN_63_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_63_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_63_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_63_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_63_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_63_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_63_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_63_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_63_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_63_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_63_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_63_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_63_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_63_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_63_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_63_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_63_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin64
 */
    #define XIOU_SLCR_MIO_PIN_64                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000100UL )
    #define XIOU_SLCR_MIO_PIN_64_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_64_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_64_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_64_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_64_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_64_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_64_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_64_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_64_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_64_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_64_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_64_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_64_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_64_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_64_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_64_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_64_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin65
 */
    #define XIOU_SLCR_MIO_PIN_65                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000104UL )
    #define XIOU_SLCR_MIO_PIN_65_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_65_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_65_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_65_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_65_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_65_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_65_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_65_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_65_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_65_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_65_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_65_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_65_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_65_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_65_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_65_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_65_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin66
 */
    #define XIOU_SLCR_MIO_PIN_66                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000108UL )
    #define XIOU_SLCR_MIO_PIN_66_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_66_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_66_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_66_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_66_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_66_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_66_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_66_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_66_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_66_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_66_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_66_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_66_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_66_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_66_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_66_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_66_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin67
 */
    #define XIOU_SLCR_MIO_PIN_67                                  ( ( XIOU_SLCR_BASEADDR ) +0x0000010CUL )
    #define XIOU_SLCR_MIO_PIN_67_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_67_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_67_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_67_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_67_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_67_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_67_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_67_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_67_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_67_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_67_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_67_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_67_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_67_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_67_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_67_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_67_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin68
 */
    #define XIOU_SLCR_MIO_PIN_68                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000110UL )
    #define XIOU_SLCR_MIO_PIN_68_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_68_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_68_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_68_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_68_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_68_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_68_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_68_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_68_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_68_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_68_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_68_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_68_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_68_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_68_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_68_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_68_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin69
 */
    #define XIOU_SLCR_MIO_PIN_69                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000114UL )
    #define XIOU_SLCR_MIO_PIN_69_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_69_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_69_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_69_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_69_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_69_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_69_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_69_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_69_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_69_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_69_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_69_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_69_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_69_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_69_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_69_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_69_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin70
 */
    #define XIOU_SLCR_MIO_PIN_70                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000118UL )
    #define XIOU_SLCR_MIO_PIN_70_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_70_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_70_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_70_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_70_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_70_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_70_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_70_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_70_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_70_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_70_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_70_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_70_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_70_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_70_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_70_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_70_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin71
 */
    #define XIOU_SLCR_MIO_PIN_71                                  ( ( XIOU_SLCR_BASEADDR ) +0x0000011CUL )
    #define XIOU_SLCR_MIO_PIN_71_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_71_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_71_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_71_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_71_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_71_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_71_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_71_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_71_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_71_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_71_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_71_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_71_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_71_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_71_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_71_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_71_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin72
 */
    #define XIOU_SLCR_MIO_PIN_72                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000120UL )
    #define XIOU_SLCR_MIO_PIN_72_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_72_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_72_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_72_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_72_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_72_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_72_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_72_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_72_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_72_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_72_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_72_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_72_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_72_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_72_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_72_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_72_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin73
 */
    #define XIOU_SLCR_MIO_PIN_73                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000124UL )
    #define XIOU_SLCR_MIO_PIN_73_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_73_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_73_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_73_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_73_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_73_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_73_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_73_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_73_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_73_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_73_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_73_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_73_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_73_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_73_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_73_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_73_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin74
 */
    #define XIOU_SLCR_MIO_PIN_74                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000128UL )
    #define XIOU_SLCR_MIO_PIN_74_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_74_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_74_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_74_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_74_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_74_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_74_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_74_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_74_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_74_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_74_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_74_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_74_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_74_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_74_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_74_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_74_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin75
 */
    #define XIOU_SLCR_MIO_PIN_75                                  ( ( XIOU_SLCR_BASEADDR ) +0x0000012CUL )
    #define XIOU_SLCR_MIO_PIN_75_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_75_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_75_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_75_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_75_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_75_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_75_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_75_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_75_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_75_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_75_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_75_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_75_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_75_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_75_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_75_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_75_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin76
 */
    #define XIOU_SLCR_MIO_PIN_76                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000130UL )
    #define XIOU_SLCR_MIO_PIN_76_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_76_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_76_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_76_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_76_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_76_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_76_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_76_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_76_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_76_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_76_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_76_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_76_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_76_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_76_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_76_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_76_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrMioPin77
 */
    #define XIOU_SLCR_MIO_PIN_77                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000134UL )
    #define XIOU_SLCR_MIO_PIN_77_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_MIO_PIN_77_L3_SEL_SHIFT                     5UL
    #define XIOU_SLCR_MIO_PIN_77_L3_SEL_WIDTH                     3UL
    #define XIOU_SLCR_MIO_PIN_77_L3_SEL_MASK                      0x000000e0UL
    #define XIOU_SLCR_MIO_PIN_77_L3_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_77_L2_SEL_SHIFT                     3UL
    #define XIOU_SLCR_MIO_PIN_77_L2_SEL_WIDTH                     2UL
    #define XIOU_SLCR_MIO_PIN_77_L2_SEL_MASK                      0x00000018UL
    #define XIOU_SLCR_MIO_PIN_77_L2_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_77_L1_SEL_SHIFT                     2UL
    #define XIOU_SLCR_MIO_PIN_77_L1_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_77_L1_SEL_MASK                      0x00000004UL
    #define XIOU_SLCR_MIO_PIN_77_L1_SEL_DEFVAL                    0x0UL

    #define XIOU_SLCR_MIO_PIN_77_L0_SEL_SHIFT                     1UL
    #define XIOU_SLCR_MIO_PIN_77_L0_SEL_WIDTH                     1UL
    #define XIOU_SLCR_MIO_PIN_77_L0_SEL_MASK                      0x00000002UL
    #define XIOU_SLCR_MIO_PIN_77_L0_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrBank0Ctrl0
 */
    #define XIOU_SLCR_BANK0_CTRL0                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000138UL )
    #define XIOU_SLCR_BANK0_CTRL0_RSTVAL                          0x03ffffffUL

    #define XIOU_SLCR_BANK0_CTRL0_DRIVE0_SHIFT                    0UL
    #define XIOU_SLCR_BANK0_CTRL0_DRIVE0_WIDTH                    26UL
    #define XIOU_SLCR_BANK0_CTRL0_DRIVE0_MASK                     0x03ffffffUL
    #define XIOU_SLCR_BANK0_CTRL0_DRIVE0_DEFVAL                   0x3ffffffUL

/**
 * Register: XiouSlcrBank0Ctrl1
 */
    #define XIOU_SLCR_BANK0_CTRL1                                 ( ( XIOU_SLCR_BASEADDR ) +0x0000013CUL )
    #define XIOU_SLCR_BANK0_CTRL1_RSTVAL                          0x00000000UL

    #define XIOU_SLCR_BANK0_CTRL1_DRIVE1_SHIFT                    0UL
    #define XIOU_SLCR_BANK0_CTRL1_DRIVE1_WIDTH                    26UL
    #define XIOU_SLCR_BANK0_CTRL1_DRIVE1_MASK                     0x03ffffffUL
    #define XIOU_SLCR_BANK0_CTRL1_DRIVE1_DEFVAL                   0x0UL

/**
 * Register: XiouSlcrBank0Ctrl3
 */
    #define XIOU_SLCR_BANK0_CTRL3                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000140UL )
    #define XIOU_SLCR_BANK0_CTRL3_RSTVAL                          0x00000000UL

    #define XIOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_SHIFT            0UL
    #define XIOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_WIDTH            26UL
    #define XIOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_MASK             0x03ffffffUL
    #define XIOU_SLCR_BANK0_CTRL3_SCHMITT_CMOS_N_DEFVAL           0x0UL

/**
 * Register: XiouSlcrBank0Ctrl4
 */
    #define XIOU_SLCR_BANK0_CTRL4                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000144UL )
    #define XIOU_SLCR_BANK0_CTRL4_RSTVAL                          0x03ffffffUL

    #define XIOU_SLCR_BANK0_CTRL4_PULLHILO_N_SHIFT                0UL
    #define XIOU_SLCR_BANK0_CTRL4_PULLHILO_N_WIDTH                26UL
    #define XIOU_SLCR_BANK0_CTRL4_PULLHILO_N_MASK                 0x03ffffffUL
    #define XIOU_SLCR_BANK0_CTRL4_PULLHILO_N_DEFVAL               0x3ffffffUL

/**
 * Register: XiouSlcrBank0Ctrl5
 */
    #define XIOU_SLCR_BANK0_CTRL5                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000148UL )
    #define XIOU_SLCR_BANK0_CTRL5_RSTVAL                          0x03ffffffUL

    #define XIOU_SLCR_BANK0_CTRL5_PULL_EN_SHIFT                   0UL
    #define XIOU_SLCR_BANK0_CTRL5_PULL_EN_WIDTH                   26UL
    #define XIOU_SLCR_BANK0_CTRL5_PULL_EN_MASK                    0x03ffffffUL
    #define XIOU_SLCR_BANK0_CTRL5_PULL_EN_DEFVAL                  0x3ffffffUL

/**
 * Register: XiouSlcrBank0Ctrl6
 */
    #define XIOU_SLCR_BANK0_CTRL6                                 ( ( XIOU_SLCR_BASEADDR ) +0x0000014CUL )
    #define XIOU_SLCR_BANK0_CTRL6_RSTVAL                          0x00000000UL

    #define XIOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_SHIFT          0UL
    #define XIOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_WIDTH          26UL
    #define XIOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_MASK           0x03ffffffUL
    #define XIOU_SLCR_BANK0_CTRL6_SLOW_FAST_SLEW_N_DEFVAL         0x0UL

/**
 * Register: XiouSlcrBank0Sts
 */
    #define XIOU_SLCR_BANK0_STS                                   ( ( XIOU_SLCR_BASEADDR ) +0x00000150UL )
    #define XIOU_SLCR_BANK0_STS_RSTVAL                            0x00000000UL

    #define XIOU_SLCR_BANK0_STS_VOLTAGE_MODE_SHIFT                0UL
    #define XIOU_SLCR_BANK0_STS_VOLTAGE_MODE_WIDTH                1UL
    #define XIOU_SLCR_BANK0_STS_VOLTAGE_MODE_MASK                 0x00000001UL
    #define XIOU_SLCR_BANK0_STS_VOLTAGE_MODE_DEFVAL               0x0UL

/**
 * Register: XiouSlcrBank1Ctrl0
 */
    #define XIOU_SLCR_BANK1_CTRL0                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000154UL )
    #define XIOU_SLCR_BANK1_CTRL0_RSTVAL                          0x03ffffffUL

    #define XIOU_SLCR_BANK1_CTRL0_DRIVE0_SHIFT                    0UL
    #define XIOU_SLCR_BANK1_CTRL0_DRIVE0_WIDTH                    26UL
    #define XIOU_SLCR_BANK1_CTRL0_DRIVE0_MASK                     0x03ffffffUL
    #define XIOU_SLCR_BANK1_CTRL0_DRIVE0_DEFVAL                   0x3ffffffUL

/**
 * Register: XiouSlcrBank1Ctrl1
 */
    #define XIOU_SLCR_BANK1_CTRL1                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000158UL )
    #define XIOU_SLCR_BANK1_CTRL1_RSTVAL                          0x00000000UL

    #define XIOU_SLCR_BANK1_CTRL1_DRIVE1_SHIFT                    0UL
    #define XIOU_SLCR_BANK1_CTRL1_DRIVE1_WIDTH                    26UL
    #define XIOU_SLCR_BANK1_CTRL1_DRIVE1_MASK                     0x03ffffffUL
    #define XIOU_SLCR_BANK1_CTRL1_DRIVE1_DEFVAL                   0x0UL

/**
 * Register: XiouSlcrBank1Ctrl3
 */
    #define XIOU_SLCR_BANK1_CTRL3                                 ( ( XIOU_SLCR_BASEADDR ) +0x0000015CUL )
    #define XIOU_SLCR_BANK1_CTRL3_RSTVAL                          0x00000000UL

    #define XIOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_SHIFT            0UL
    #define XIOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_WIDTH            26UL
    #define XIOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_MASK             0x03ffffffUL
    #define XIOU_SLCR_BANK1_CTRL3_SCHMITT_CMOS_N_DEFVAL           0x0UL

/**
 * Register: XiouSlcrBank1Ctrl4
 */
    #define XIOU_SLCR_BANK1_CTRL4                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000160UL )
    #define XIOU_SLCR_BANK1_CTRL4_RSTVAL                          0x03ffffffUL

    #define XIOU_SLCR_BANK1_CTRL4_PULLHILO_N_SHIFT                0UL
    #define XIOU_SLCR_BANK1_CTRL4_PULLHILO_N_WIDTH                26UL
    #define XIOU_SLCR_BANK1_CTRL4_PULLHILO_N_MASK                 0x03ffffffUL
    #define XIOU_SLCR_BANK1_CTRL4_PULLHILO_N_DEFVAL               0x3ffffffUL

/**
 * Register: XiouSlcrBank1Ctrl5
 */
    #define XIOU_SLCR_BANK1_CTRL5                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000164UL )
    #define XIOU_SLCR_BANK1_CTRL5_RSTVAL                          0x03ffffffUL

    #define XIOU_SLCR_BANK1_CTRL5_PULL_EN_SHIFT                   0UL
    #define XIOU_SLCR_BANK1_CTRL5_PULL_EN_WIDTH                   26UL
    #define XIOU_SLCR_BANK1_CTRL5_PULL_EN_MASK                    0x03ffffffUL
    #define XIOU_SLCR_BANK1_CTRL5_PULL_EN_DEFVAL                  0x3ffffffUL

/**
 * Register: XiouSlcrBank1Ctrl6
 */
    #define XIOU_SLCR_BANK1_CTRL6                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000168UL )
    #define XIOU_SLCR_BANK1_CTRL6_RSTVAL                          0x00000000UL

    #define XIOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_SHIFT          0UL
    #define XIOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_WIDTH          26UL
    #define XIOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_MASK           0x03ffffffUL
    #define XIOU_SLCR_BANK1_CTRL6_SLOW_FAST_SLEW_N_DEFVAL         0x0UL

/**
 * Register: XiouSlcrBank1Sts
 */
    #define XIOU_SLCR_BANK1_STS                                   ( ( XIOU_SLCR_BASEADDR ) +0x0000016CUL )
    #define XIOU_SLCR_BANK1_STS_RSTVAL                            0x00000000UL

    #define XIOU_SLCR_BANK1_STS_VOLTAGE_MODE_SHIFT                0UL
    #define XIOU_SLCR_BANK1_STS_VOLTAGE_MODE_WIDTH                1UL
    #define XIOU_SLCR_BANK1_STS_VOLTAGE_MODE_MASK                 0x00000001UL
    #define XIOU_SLCR_BANK1_STS_VOLTAGE_MODE_DEFVAL               0x0UL

/**
 * Register: XiouSlcrBank2Ctrl0
 */
    #define XIOU_SLCR_BANK2_CTRL0                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000170UL )
    #define XIOU_SLCR_BANK2_CTRL0_RSTVAL                          0x03ffffffUL

    #define XIOU_SLCR_BANK2_CTRL0_DRIVE0_SHIFT                    0UL
    #define XIOU_SLCR_BANK2_CTRL0_DRIVE0_WIDTH                    26UL
    #define XIOU_SLCR_BANK2_CTRL0_DRIVE0_MASK                     0x03ffffffUL
    #define XIOU_SLCR_BANK2_CTRL0_DRIVE0_DEFVAL                   0x3ffffffUL

/**
 * Register: XiouSlcrBank2Ctrl1
 */
    #define XIOU_SLCR_BANK2_CTRL1                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000174UL )
    #define XIOU_SLCR_BANK2_CTRL1_RSTVAL                          0x00000000UL

    #define XIOU_SLCR_BANK2_CTRL1_DRIVE1_SHIFT                    0UL
    #define XIOU_SLCR_BANK2_CTRL1_DRIVE1_WIDTH                    26UL
    #define XIOU_SLCR_BANK2_CTRL1_DRIVE1_MASK                     0x03ffffffUL
    #define XIOU_SLCR_BANK2_CTRL1_DRIVE1_DEFVAL                   0x0UL

/**
 * Register: XiouSlcrBank2Ctrl3
 */
    #define XIOU_SLCR_BANK2_CTRL3                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000178UL )
    #define XIOU_SLCR_BANK2_CTRL3_RSTVAL                          0x00000000UL

    #define XIOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_SHIFT            0UL
    #define XIOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_WIDTH            26UL
    #define XIOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_MASK             0x03ffffffUL
    #define XIOU_SLCR_BANK2_CTRL3_SCHMITT_CMOS_N_DEFVAL           0x0UL

/**
 * Register: XiouSlcrBank2Ctrl4
 */
    #define XIOU_SLCR_BANK2_CTRL4                                 ( ( XIOU_SLCR_BASEADDR ) +0x0000017CUL )
    #define XIOU_SLCR_BANK2_CTRL4_RSTVAL                          0x03ffffffUL

    #define XIOU_SLCR_BANK2_CTRL4_PULLHILO_N_SHIFT                0UL
    #define XIOU_SLCR_BANK2_CTRL4_PULLHILO_N_WIDTH                26UL
    #define XIOU_SLCR_BANK2_CTRL4_PULLHILO_N_MASK                 0x03ffffffUL
    #define XIOU_SLCR_BANK2_CTRL4_PULLHILO_N_DEFVAL               0x3ffffffUL

/**
 * Register: XiouSlcrBank2Ctrl5
 */
    #define XIOU_SLCR_BANK2_CTRL5                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000180UL )
    #define XIOU_SLCR_BANK2_CTRL5_RSTVAL                          0x03ffffffUL

    #define XIOU_SLCR_BANK2_CTRL5_PULL_EN_SHIFT                   0UL
    #define XIOU_SLCR_BANK2_CTRL5_PULL_EN_WIDTH                   26UL
    #define XIOU_SLCR_BANK2_CTRL5_PULL_EN_MASK                    0x03ffffffUL
    #define XIOU_SLCR_BANK2_CTRL5_PULL_EN_DEFVAL                  0x3ffffffUL

/**
 * Register: XiouSlcrBank2Ctrl6
 */
    #define XIOU_SLCR_BANK2_CTRL6                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000184UL )
    #define XIOU_SLCR_BANK2_CTRL6_RSTVAL                          0x00000000UL

    #define XIOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_SHIFT          0UL
    #define XIOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_WIDTH          26UL
    #define XIOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_MASK           0x03ffffffUL
    #define XIOU_SLCR_BANK2_CTRL6_SLOW_FAST_SLEW_N_DEFVAL         0x0UL

/**
 * Register: XiouSlcrBank2Sts
 */
    #define XIOU_SLCR_BANK2_STS                                   ( ( XIOU_SLCR_BASEADDR ) +0x00000188UL )
    #define XIOU_SLCR_BANK2_STS_RSTVAL                            0x00000000UL

    #define XIOU_SLCR_BANK2_STS_VOLTAGE_MODE_SHIFT                0UL
    #define XIOU_SLCR_BANK2_STS_VOLTAGE_MODE_WIDTH                1UL
    #define XIOU_SLCR_BANK2_STS_VOLTAGE_MODE_MASK                 0x00000001UL
    #define XIOU_SLCR_BANK2_STS_VOLTAGE_MODE_DEFVAL               0x0UL

/**
 * Register: XiouSlcrMioLpbck
 */
    #define XIOU_SLCR_MIO_LPBCK                                   ( ( XIOU_SLCR_BASEADDR ) +0x00000200UL )
    #define XIOU_SLCR_MIO_LPBCK_RSTVAL                            0x00000000UL

    #define XIOU_SLCR_MIO_LPBCK_XI2CPS_LOOP_SHIFT                 3UL
    #define XIOU_SLCR_MIO_LPBCK_XI2CPS_LOOP_WIDTH                 1UL
    #define XIOU_SLCR_MIO_LPBCK_XI2CPS_LOOP_MASK                  0x00000008UL
    #define XIOU_SLCR_MIO_LPBCK_XI2CPS_LOOP_DEFVAL                0x0UL

    #define XIOU_SLCR_MIO_LPBCK_CAN0_LOOP_CAN1_SHIFT              2UL
    #define XIOU_SLCR_MIO_LPBCK_CAN0_LOOP_CAN1_WIDTH              1UL
    #define XIOU_SLCR_MIO_LPBCK_CAN0_LOOP_CAN1_MASK               0x00000004UL
    #define XIOU_SLCR_MIO_LPBCK_CAN0_LOOP_CAN1_DEFVAL             0x0UL

    #define XIOU_SLCR_MIO_LPBCK_UA0_LOOP_UA1_SHIFT                1UL
    #define XIOU_SLCR_MIO_LPBCK_UA0_LOOP_UA1_WIDTH                1UL
    #define XIOU_SLCR_MIO_LPBCK_UA0_LOOP_UA1_MASK                 0x00000002UL
    #define XIOU_SLCR_MIO_LPBCK_UA0_LOOP_UA1_DEFVAL               0x0UL

    #define XIOU_SLCR_MIO_LPBCK_XSPIPS_LOOP_SHIFT                 0UL
    #define XIOU_SLCR_MIO_LPBCK_XSPIPS_LOOP_WIDTH                 1UL
    #define XIOU_SLCR_MIO_LPBCK_XSPIPS_LOOP_MASK                  0x00000001UL
    #define XIOU_SLCR_MIO_LPBCK_XSPIPS_LOOP_DEFVAL                0x0UL

/**
 * Register: XiouSlcrMioMstTri0
 */
    #define XIOU_SLCR_MIO_MST_TRI0                                ( ( XIOU_SLCR_BASEADDR ) +0x00000204UL )
    #define XIOU_SLCR_MIO_MST_TRI0_RSTVAL                         0xffffffffUL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_31_TRI_SHIFT               31UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_31_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_31_TRI_MASK                0x80000000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_31_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_30_TRI_SHIFT               30UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_30_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_30_TRI_MASK                0x40000000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_30_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_29_TRI_SHIFT               29UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_29_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_29_TRI_MASK                0x20000000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_29_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_28_TRI_SHIFT               28UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_28_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_28_TRI_MASK                0x10000000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_28_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_27_TRI_SHIFT               27UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_27_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_27_TRI_MASK                0x08000000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_27_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_26_TRI_SHIFT               26UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_26_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_26_TRI_MASK                0x04000000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_26_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_25_TRI_SHIFT               25UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_25_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_25_TRI_MASK                0x02000000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_25_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_24_TRI_SHIFT               24UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_24_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_24_TRI_MASK                0x01000000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_24_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_23_TRI_SHIFT               23UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_23_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_23_TRI_MASK                0x00800000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_23_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_22_TRI_SHIFT               22UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_22_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_22_TRI_MASK                0x00400000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_22_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_21_TRI_SHIFT               21UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_21_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_21_TRI_MASK                0x00200000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_21_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_20_TRI_SHIFT               20UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_20_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_20_TRI_MASK                0x00100000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_20_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_19_TRI_SHIFT               19UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_19_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_19_TRI_MASK                0x00080000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_19_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_18_TRI_SHIFT               18UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_18_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_18_TRI_MASK                0x00040000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_18_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_17_TRI_SHIFT               17UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_17_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_17_TRI_MASK                0x00020000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_17_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_16_TRI_SHIFT               16UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_16_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_16_TRI_MASK                0x00010000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_16_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_15_TRI_SHIFT               15UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_15_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_15_TRI_MASK                0x00008000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_15_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_14_TRI_SHIFT               14UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_14_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_14_TRI_MASK                0x00004000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_14_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_13_TRI_SHIFT               13UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_13_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_13_TRI_MASK                0x00002000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_13_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_12_TRI_SHIFT               12UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_12_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_12_TRI_MASK                0x00001000UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_12_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_11_TRI_SHIFT               11UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_11_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_11_TRI_MASK                0x00000800UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_11_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_10_TRI_SHIFT               10UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_10_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_10_TRI_MASK                0x00000400UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_10_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_09_TRI_SHIFT               9UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_09_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_09_TRI_MASK                0x00000200UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_09_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_08_TRI_SHIFT               8UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_08_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_08_TRI_MASK                0x00000100UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_08_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_07_TRI_SHIFT               7UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_07_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_07_TRI_MASK                0x00000080UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_07_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_06_TRI_SHIFT               6UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_06_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_06_TRI_MASK                0x00000040UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_06_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_05_TRI_SHIFT               5UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_05_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_05_TRI_MASK                0x00000020UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_05_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_04_TRI_SHIFT               4UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_04_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_04_TRI_MASK                0x00000010UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_04_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_03_TRI_SHIFT               3UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_03_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_03_TRI_MASK                0x00000008UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_03_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_02_TRI_SHIFT               2UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_02_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_02_TRI_MASK                0x00000004UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_02_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_01_TRI_SHIFT               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_01_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_01_TRI_MASK                0x00000002UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_01_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI0_PIN_00_TRI_SHIFT               0UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_00_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_00_TRI_MASK                0x00000001UL
    #define XIOU_SLCR_MIO_MST_TRI0_PIN_00_TRI_DEFVAL              0x1UL

/**
 * Register: XiouSlcrMioMstTri1
 */
    #define XIOU_SLCR_MIO_MST_TRI1                                ( ( XIOU_SLCR_BASEADDR ) +0x00000208UL )
    #define XIOU_SLCR_MIO_MST_TRI1_RSTVAL                         0xffffffffUL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_63_TRI_SHIFT               31UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_63_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_63_TRI_MASK                0x80000000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_63_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_62_TRI_SHIFT               30UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_62_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_62_TRI_MASK                0x40000000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_62_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_61_TRI_SHIFT               29UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_61_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_61_TRI_MASK                0x20000000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_61_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_60_TRI_SHIFT               28UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_60_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_60_TRI_MASK                0x10000000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_60_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_59_TRI_SHIFT               27UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_59_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_59_TRI_MASK                0x08000000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_59_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_58_TRI_SHIFT               26UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_58_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_58_TRI_MASK                0x04000000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_58_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_57_TRI_SHIFT               25UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_57_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_57_TRI_MASK                0x02000000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_57_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_56_TRI_SHIFT               24UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_56_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_56_TRI_MASK                0x01000000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_56_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_55_TRI_SHIFT               23UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_55_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_55_TRI_MASK                0x00800000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_55_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_54_TRI_SHIFT               22UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_54_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_54_TRI_MASK                0x00400000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_54_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_53_TRI_SHIFT               21UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_53_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_53_TRI_MASK                0x00200000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_53_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_52_TRI_SHIFT               20UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_52_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_52_TRI_MASK                0x00100000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_52_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_51_TRI_SHIFT               19UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_51_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_51_TRI_MASK                0x00080000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_51_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_50_TRI_SHIFT               18UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_50_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_50_TRI_MASK                0x00040000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_50_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_49_TRI_SHIFT               17UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_49_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_49_TRI_MASK                0x00020000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_49_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_48_TRI_SHIFT               16UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_48_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_48_TRI_MASK                0x00010000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_48_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_47_TRI_SHIFT               15UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_47_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_47_TRI_MASK                0x00008000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_47_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_46_TRI_SHIFT               14UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_46_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_46_TRI_MASK                0x00004000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_46_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_45_TRI_SHIFT               13UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_45_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_45_TRI_MASK                0x00002000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_45_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_44_TRI_SHIFT               12UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_44_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_44_TRI_MASK                0x00001000UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_44_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_43_TRI_SHIFT               11UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_43_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_43_TRI_MASK                0x00000800UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_43_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_42_TRI_SHIFT               10UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_42_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_42_TRI_MASK                0x00000400UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_42_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_41_TRI_SHIFT               9UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_41_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_41_TRI_MASK                0x00000200UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_41_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_40_TRI_SHIFT               8UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_40_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_40_TRI_MASK                0x00000100UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_40_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_39_TRI_SHIFT               7UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_39_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_39_TRI_MASK                0x00000080UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_39_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_38_TRI_SHIFT               6UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_38_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_38_TRI_MASK                0x00000040UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_38_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_37_TRI_SHIFT               5UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_37_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_37_TRI_MASK                0x00000020UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_37_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_36_TRI_SHIFT               4UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_36_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_36_TRI_MASK                0x00000010UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_36_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_35_TRI_SHIFT               3UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_35_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_35_TRI_MASK                0x00000008UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_35_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_34_TRI_SHIFT               2UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_34_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_34_TRI_MASK                0x00000004UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_34_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_33_TRI_SHIFT               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_33_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_33_TRI_MASK                0x00000002UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_33_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI1_PIN_32_TRI_SHIFT               0UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_32_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_32_TRI_MASK                0x00000001UL
    #define XIOU_SLCR_MIO_MST_TRI1_PIN_32_TRI_DEFVAL              0x1UL

/**
 * Register: XiouSlcrMioMstTri2
 */
    #define XIOU_SLCR_MIO_MST_TRI2                                ( ( XIOU_SLCR_BASEADDR ) +0x0000020CUL )
    #define XIOU_SLCR_MIO_MST_TRI2_RSTVAL                         0x00003fffUL

    #define XIOU_SLCR_MIO_MST_TRI2_PIN_77_TRI_SHIFT               13UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_77_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_77_TRI_MASK                0x00002000UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_77_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI2_PIN_76_TRI_SHIFT               12UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_76_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_76_TRI_MASK                0x00001000UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_76_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI2_PIN_75_TRI_SHIFT               11UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_75_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_75_TRI_MASK                0x00000800UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_75_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI2_PIN_74_TRI_SHIFT               10UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_74_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_74_TRI_MASK                0x00000400UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_74_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI2_PIN_73_TRI_SHIFT               9UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_73_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_73_TRI_MASK                0x00000200UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_73_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI2_PIN_72_TRI_SHIFT               8UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_72_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_72_TRI_MASK                0x00000100UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_72_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI2_PIN_71_TRI_SHIFT               7UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_71_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_71_TRI_MASK                0x00000080UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_71_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI2_PIN_70_TRI_SHIFT               6UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_70_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_70_TRI_MASK                0x00000040UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_70_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI2_PIN_69_TRI_SHIFT               5UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_69_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_69_TRI_MASK                0x00000020UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_69_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI2_PIN_68_TRI_SHIFT               4UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_68_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_68_TRI_MASK                0x00000010UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_68_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI2_PIN_67_TRI_SHIFT               3UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_67_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_67_TRI_MASK                0x00000008UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_67_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI2_PIN_66_TRI_SHIFT               2UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_66_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_66_TRI_MASK                0x00000004UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_66_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI2_PIN_65_TRI_SHIFT               1UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_65_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_65_TRI_MASK                0x00000002UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_65_TRI_DEFVAL              0x1UL

    #define XIOU_SLCR_MIO_MST_TRI2_PIN_64_TRI_SHIFT               0UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_64_TRI_WIDTH               1UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_64_TRI_MASK                0x00000001UL
    #define XIOU_SLCR_MIO_MST_TRI2_PIN_64_TRI_DEFVAL              0x1UL

/**
 * Register: XiouSlcrWdtClkSel
 */
    #define XIOU_SLCR_WDT_CLK_SEL                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000300UL )
    #define XIOU_SLCR_WDT_CLK_SEL_RSTVAL                          0x00000000UL

    #define XIOU_SLCR_WDT_CLK_SEL_SHIFT                           0UL
    #define XIOU_SLCR_WDT_CLK_SEL_WIDTH                           1UL
    #define XIOU_SLCR_WDT_CLK_SEL_MASK                            0x00000001UL
    #define XIOU_SLCR_WDT_CLK_SEL_DEFVAL                          0x0UL

/**
 * Register: XiouSlcrCanMioCtrl
 */
    #define XIOU_SLCR_CAN_MIO_CTRL                                ( ( XIOU_SLCR_BASEADDR ) +0x00000304UL )
    #define XIOU_SLCR_CAN_MIO_CTRL_RSTVAL                         0x00000000UL

    #define XIOU_SLCR_CAN_MIO_CTRL_CAN1_RXIN_REG_SHIFT            23UL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN1_RXIN_REG_WIDTH            1UL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN1_RXIN_REG_MASK             0x00800000UL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN1_RXIN_REG_DEFVAL           0x0UL

    #define XIOU_SLCR_CAN_MIO_CTRL_CAN1_REF_SEL_SHIFT             22UL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN1_REF_SEL_WIDTH             1UL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN1_REF_SEL_MASK              0x00400000UL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN1_REF_SEL_DEFVAL            0x0UL

    #define XIOU_SLCR_CAN_MIO_CTRL_CAN1_MUX_SHIFT                 15UL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN1_MUX_WIDTH                 7UL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN1_MUX_MASK                  0x003f8000UL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN1_MUX_DEFVAL                0x0UL

    #define XIOU_SLCR_CAN_MIO_CTRL_CAN0_RXIN_REG_SHIFT            8UL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN0_RXIN_REG_WIDTH            1UL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN0_RXIN_REG_MASK             0x00000100UL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN0_RXIN_REG_DEFVAL           0x0UL

    #define XIOU_SLCR_CAN_MIO_CTRL_CAN0_REF_SEL_SHIFT             7UL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN0_REF_SEL_WIDTH             1UL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN0_REF_SEL_MASK              0x00000080UL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN0_REF_SEL_DEFVAL            0x0UL

    #define XIOU_SLCR_CAN_MIO_CTRL_CAN0_MUX_SHIFT                 0UL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN0_MUX_WIDTH                 7UL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN0_MUX_MASK                  0x0000007fUL
    #define XIOU_SLCR_CAN_MIO_CTRL_CAN0_MUX_DEFVAL                0x0UL

/**
 * Register: XiouSlcrGemClkCtrl
 */
    #define XIOU_SLCR_GEM_CLK_CTRL                                ( ( XIOU_SLCR_BASEADDR ) +0x00000308UL )
    #define XIOU_SLCR_GEM_CLK_CTRL_RSTVAL                         0x00000000UL

    #define XIOU_SLCR_GEM_CLK_CTRL_TSU_LB_SEL_SHIFT               22UL
    #define XIOU_SLCR_GEM_CLK_CTRL_TSU_LB_SEL_WIDTH               1UL
    #define XIOU_SLCR_GEM_CLK_CTRL_TSU_LB_SEL_MASK                0x00400000UL
    #define XIOU_SLCR_GEM_CLK_CTRL_TSU_LB_SEL_DEFVAL              0x0UL

    #define XIOU_SLCR_GEM_CLK_CTRL_TSU_SEL_SHIFT                  20UL
    #define XIOU_SLCR_GEM_CLK_CTRL_TSU_SEL_WIDTH                  2UL
    #define XIOU_SLCR_GEM_CLK_CTRL_TSU_SEL_MASK                   0x00300000UL
    #define XIOU_SLCR_GEM_CLK_CTRL_TSU_SEL_DEFVAL                 0x0UL

    #define XIOU_SLCR_GEM3_CLK_CTRL_XEMACPS_FIFO_SEL_SHIFT        18UL
    #define XIOU_SLCR_GEM3_CLK_CTRL_XEMACPS_FIFO_SEL_WIDTH        1UL
    #define XIOU_SLCR_GEM3_CLK_CTRL_XEMACPS_FIFO_SEL_MASK         0x00040000UL
    #define XIOU_SLCR_GEM3_CLK_CTRL_XEMACPS_FIFO_SEL_DEFVAL       0x0UL

    #define XIOU_SLCR_GEM3_CLK_CTRL_XEMACPS_SGMII_MODE_SHIFT      17UL
    #define XIOU_SLCR_GEM3_CLK_CTRL_XEMACPS_SGMII_MODE_WIDTH      1UL
    #define XIOU_SLCR_GEM3_CLK_CTRL_XEMACPS_SGMII_MODE_MASK       0x00020000UL
    #define XIOU_SLCR_GEM3_CLK_CTRL_XEMACPS_SGMII_MODE_DEFVAL     0x0UL

    #define XIOU_SLCR_GEM3_CLK_CTRL_XEMACPS_REF_SRC_SEL_SHIFT     16UL
    #define XIOU_SLCR_GEM3_CLK_CTRL_XEMACPS_REF_SRC_SEL_WIDTH     1UL
    #define XIOU_SLCR_GEM3_CLK_CTRL_XEMACPS_REF_SRC_SEL_MASK      0x00010000UL
    #define XIOU_SLCR_GEM3_CLK_CTRL_XEMACPS_REF_SRC_SEL_DEFVAL    0x0UL

    #define XIOU_SLCR_GEM3_CLK_CTRL_XEMACPS_RX_SRC_SEL_SHIFT      15UL
    #define XIOU_SLCR_GEM3_CLK_CTRL_XEMACPS_RX_SRC_SEL_WIDTH      1UL
    #define XIOU_SLCR_GEM3_CLK_CTRL_XEMACPS_RX_SRC_SEL_MASK       0x00008000UL
    #define XIOU_SLCR_GEM3_CLK_CTRL_XEMACPS_RX_SRC_SEL_DEFVAL     0x0UL

    #define XIOU_SLCR_GEM2_CLK_CTRL_XEMACPS_FIFO_SEL_SHIFT        13UL
    #define XIOU_SLCR_GEM2_CLK_CTRL_XEMACPS_FIFO_SEL_WIDTH        1UL
    #define XIOU_SLCR_GEM2_CLK_CTRL_XEMACPS_FIFO_SEL_MASK         0x00002000UL
    #define XIOU_SLCR_GEM2_CLK_CTRL_XEMACPS_FIFO_SEL_DEFVAL       0x0UL

    #define XIOU_SLCR_GEM2_CLK_CTRL_XEMACPS_SGMII_MODE_SHIFT      12UL
    #define XIOU_SLCR_GEM2_CLK_CTRL_XEMACPS_SGMII_MODE_WIDTH      1UL
    #define XIOU_SLCR_GEM2_CLK_CTRL_XEMACPS_SGMII_MODE_MASK       0x00001000UL
    #define XIOU_SLCR_GEM2_CLK_CTRL_XEMACPS_SGMII_MODE_DEFVAL     0x0UL

    #define XIOU_SLCR_GEM2_CLK_CTRL_XEMACPS_REF_SRC_SEL_SHIFT     11UL
    #define XIOU_SLCR_GEM2_CLK_CTRL_XEMACPS_REF_SRC_SEL_WIDTH     1UL
    #define XIOU_SLCR_GEM2_CLK_CTRL_XEMACPS_REF_SRC_SEL_MASK      0x00000800UL
    #define XIOU_SLCR_GEM2_CLK_CTRL_XEMACPS_REF_SRC_SEL_DEFVAL    0x0UL

    #define XIOU_SLCR_GEM2_CLK_CTRL_XEMACPS_RX_SRC_SEL_SHIFT      10UL
    #define XIOU_SLCR_GEM2_CLK_CTRL_XEMACPS_RX_SRC_SEL_WIDTH      1UL
    #define XIOU_SLCR_GEM2_CLK_CTRL_XEMACPS_RX_SRC_SEL_MASK       0x00000400UL
    #define XIOU_SLCR_GEM2_CLK_CTRL_XEMACPS_RX_SRC_SEL_DEFVAL     0x0UL

    #define XIOU_SLCR_GEM1_CLK_CTRL_XEMACPS_FIFO_SEL_SHIFT        8UL
    #define XIOU_SLCR_GEM1_CLK_CTRL_XEMACPS_FIFO_SEL_WIDTH        1UL
    #define XIOU_SLCR_GEM1_CLK_CTRL_XEMACPS_FIFO_SEL_MASK         0x00000100UL
    #define XIOU_SLCR_GEM1_CLK_CTRL_XEMACPS_FIFO_SEL_DEFVAL       0x0UL

    #define XIOU_SLCR_GEM1_CLK_CTRL_XEMACPS_SGMII_MODE_SHIFT      7UL
    #define XIOU_SLCR_GEM1_CLK_CTRL_XEMACPS_SGMII_MODE_WIDTH      1UL
    #define XIOU_SLCR_GEM1_CLK_CTRL_XEMACPS_SGMII_MODE_MASK       0x00000080UL
    #define XIOU_SLCR_GEM1_CLK_CTRL_XEMACPS_SGMII_MODE_DEFVAL     0x0UL

    #define XIOU_SLCR_GEM1_CLK_CTRL_XEMACPS_REF_SRC_SEL_SHIFT     6UL
    #define XIOU_SLCR_GEM1_CLK_CTRL_XEMACPS_REF_SRC_SEL_WIDTH     1UL
    #define XIOU_SLCR_GEM1_CLK_CTRL_XEMACPS_REF_SRC_SEL_MASK      0x00000040UL
    #define XIOU_SLCR_GEM1_CLK_CTRL_XEMACPS_REF_SRC_SEL_DEFVAL    0x0UL

    #define XIOU_SLCR_GEM1_CLK_CTRL_XEMACPS_RX_SRC_SEL_SHIFT      5UL
    #define XIOU_SLCR_GEM1_CLK_CTRL_XEMACPS_RX_SRC_SEL_WIDTH      1UL
    #define XIOU_SLCR_GEM1_CLK_CTRL_XEMACPS_RX_SRC_SEL_MASK       0x00000020UL
    #define XIOU_SLCR_GEM1_CLK_CTRL_XEMACPS_RX_SRC_SEL_DEFVAL     0x0UL

    #define XIOU_SLCR_GEM0_CLK_CTRL_XEMACPS_FIFO_SEL_SHIFT        3UL
    #define XIOU_SLCR_GEM0_CLK_CTRL_XEMACPS_FIFO_SEL_WIDTH        1UL
    #define XIOU_SLCR_GEM0_CLK_CTRL_XEMACPS_FIFO_SEL_MASK         0x00000008UL
    #define XIOU_SLCR_GEM0_CLK_CTRL_XEMACPS_FIFO_SEL_DEFVAL       0x0UL

    #define XIOU_SLCR_GEM0_CLK_CTRL_XEMACPS_SGMII_MODE_SHIFT      2UL
    #define XIOU_SLCR_GEM0_CLK_CTRL_XEMACPS_SGMII_MODE_WIDTH      1UL
    #define XIOU_SLCR_GEM0_CLK_CTRL_XEMACPS_SGMII_MODE_MASK       0x00000004UL
    #define XIOU_SLCR_GEM0_CLK_CTRL_XEMACPS_SGMII_MODE_DEFVAL     0x0UL

    #define XIOU_SLCR_GEM0_CLK_CTRL_XEMACPS_REF_SRC_SEL_SHIFT     1UL
    #define XIOU_SLCR_GEM0_CLK_CTRL_XEMACPS_REF_SRC_SEL_WIDTH     1UL
    #define XIOU_SLCR_GEM0_CLK_CTRL_XEMACPS_REF_SRC_SEL_MASK      0x00000002UL
    #define XIOU_SLCR_GEM0_CLK_CTRL_XEMACPS_REF_SRC_SEL_DEFVAL    0x0UL

    #define XIOU_SLCR_GEM0_CLK_CTRL_XEMACPS_RX_SRC_SEL_SHIFT      0UL
    #define XIOU_SLCR_GEM0_CLK_CTRL_XEMACPS_RX_SRC_SEL_WIDTH      1UL
    #define XIOU_SLCR_GEM0_CLK_CTRL_XEMACPS_RX_SRC_SEL_MASK       0x00000001UL
    #define XIOU_SLCR_GEM0_CLK_CTRL_XEMACPS_RX_SRC_SEL_DEFVAL     0x0UL

/**
 * Register: XiouSlcrSdioClkCtrl
 */
    #define XIOU_SLCR_SDIO_CLK_CTRL                               ( ( XIOU_SLCR_BASEADDR ) +0x0000030CUL )
    #define XIOU_SLCR_SDIO_CLK_CTRL_RSTVAL                        0x00000000UL

    #define XIOU_SLCR_SDIO_CLK_CTRL_SDIO1_FBCLK_SEL_SHIFT         18UL
    #define XIOU_SLCR_SDIO_CLK_CTRL_SDIO1_FBCLK_SEL_WIDTH         1UL
    #define XIOU_SLCR_SDIO_CLK_CTRL_SDIO1_FBCLK_SEL_MASK          0x00040000UL
    #define XIOU_SLCR_SDIO_CLK_CTRL_SDIO1_FBCLK_SEL_DEFVAL        0x0UL

    #define XIOU_SLCR_SDIO_CLK_CTRL_SDIO1_RX_SRC_SEL_SHIFT        17UL
    #define XIOU_SLCR_SDIO_CLK_CTRL_SDIO1_RX_SRC_SEL_WIDTH        1UL
    #define XIOU_SLCR_SDIO_CLK_CTRL_SDIO1_RX_SRC_SEL_MASK         0x00020000UL
    #define XIOU_SLCR_SDIO_CLK_CTRL_SDIO1_RX_SRC_SEL_DEFVAL       0x0UL

    #define XIOU_SLCR_SDIO_CLK_CTRL_SDIO0_FBCLK_SEL_SHIFT         2UL
    #define XIOU_SLCR_SDIO_CLK_CTRL_SDIO0_FBCLK_SEL_WIDTH         1UL
    #define XIOU_SLCR_SDIO_CLK_CTRL_SDIO0_FBCLK_SEL_MASK          0x00000004UL
    #define XIOU_SLCR_SDIO_CLK_CTRL_SDIO0_FBCLK_SEL_DEFVAL        0x0UL

    #define XIOU_SLCR_SDIO_CLK_CTRL_SDIO0_RX_SRC_SEL_SHIFT        0UL
    #define XIOU_SLCR_SDIO_CLK_CTRL_SDIO0_RX_SRC_SEL_WIDTH        2UL
    #define XIOU_SLCR_SDIO_CLK_CTRL_SDIO0_RX_SRC_SEL_MASK         0x00000003UL
    #define XIOU_SLCR_SDIO_CLK_CTRL_SDIO0_RX_SRC_SEL_DEFVAL       0x0UL

/**
 * Register: XiouSlcrCtrlRegSd
 */
    #define XIOU_SLCR_CTRL_REG_SD                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000310UL )
    #define XIOU_SLCR_CTRL_REG_SD_RSTVAL                          0x00000000UL

    #define XIOU_SLCR_CTRL_REG_SD1_XSDPS_EMMC_SEL_SHIFT           15UL
    #define XIOU_SLCR_CTRL_REG_SD1_XSDPS_EMMC_SEL_WIDTH           1UL
    #define XIOU_SLCR_CTRL_REG_SD1_XSDPS_EMMC_SEL_MASK            0x00008000UL
    #define XIOU_SLCR_CTRL_REG_SD1_XSDPS_EMMC_SEL_DEFVAL          0x0UL

    #define XIOU_SLCR_CTRL_REG_SD0_XSDPS_EMMC_SEL_SHIFT           0UL
    #define XIOU_SLCR_CTRL_REG_SD0_XSDPS_EMMC_SEL_WIDTH           1UL
    #define XIOU_SLCR_CTRL_REG_SD0_XSDPS_EMMC_SEL_MASK            0x00000001UL
    #define XIOU_SLCR_CTRL_REG_SD0_XSDPS_EMMC_SEL_DEFVAL          0x0UL

/**
 * Register: XiouSlcrSdItapdly
 */
    #define XIOU_SLCR_SD_ITAPDLY                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000314UL )
    #define XIOU_SLCR_SD_ITAPDLY_RSTVAL                           0x00000000UL

    #define XIOU_SLCR_SD1_ITAPDLY_XSDPS_ITAPCHGWIN_SHIFT          25UL
    #define XIOU_SLCR_SD1_ITAPDLY_XSDPS_ITAPCHGWIN_WIDTH          1UL
    #define XIOU_SLCR_SD1_ITAPDLY_XSDPS_ITAPCHGWIN_MASK           0x02000000UL
    #define XIOU_SLCR_SD1_ITAPDLY_XSDPS_ITAPCHGWIN_DEFVAL         0x0UL

    #define XIOU_SLCR_SD1_ITAPDLY_XSDPS_ITAPDLYENA_SHIFT          24UL
    #define XIOU_SLCR_SD1_ITAPDLY_XSDPS_ITAPDLYENA_WIDTH          1UL
    #define XIOU_SLCR_SD1_ITAPDLY_XSDPS_ITAPDLYENA_MASK           0x01000000UL
    #define XIOU_SLCR_SD1_ITAPDLY_XSDPS_ITAPDLYENA_DEFVAL         0x0UL

    #define XIOU_SLCR_SD1_ITAPDLY_XSDPS_ITAPDLYSEL_SHIFT          16UL
    #define XIOU_SLCR_SD1_ITAPDLY_XSDPS_ITAPDLYSEL_WIDTH          8UL
    #define XIOU_SLCR_SD1_ITAPDLY_XSDPS_ITAPDLYSEL_MASK           0x00ff0000UL
    #define XIOU_SLCR_SD1_ITAPDLY_XSDPS_ITAPDLYSEL_DEFVAL         0x0UL

    #define XIOU_SLCR_SD0_ITAPDLY_XSDPS_ITAPCHGWIN_SHIFT          9UL
    #define XIOU_SLCR_SD0_ITAPDLY_XSDPS_ITAPCHGWIN_WIDTH          1UL
    #define XIOU_SLCR_SD0_ITAPDLY_XSDPS_ITAPCHGWIN_MASK           0x00000200UL
    #define XIOU_SLCR_SD0_ITAPDLY_XSDPS_ITAPCHGWIN_DEFVAL         0x0UL

    #define XIOU_SLCR_SD0_ITAPDLY_XSDPS_ITAPDLYENA_SHIFT          8UL
    #define XIOU_SLCR_SD0_ITAPDLY_XSDPS_ITAPDLYENA_WIDTH          1UL
    #define XIOU_SLCR_SD0_ITAPDLY_XSDPS_ITAPDLYENA_MASK           0x00000100UL
    #define XIOU_SLCR_SD0_ITAPDLY_XSDPS_ITAPDLYENA_DEFVAL         0x0UL

    #define XIOU_SLCR_SD0_ITAPDLY_XSDPS_ITAPDLYSEL_SHIFT          0UL
    #define XIOU_SLCR_SD0_ITAPDLY_XSDPS_ITAPDLYSEL_WIDTH          8UL
    #define XIOU_SLCR_SD0_ITAPDLY_XSDPS_ITAPDLYSEL_MASK           0x000000ffUL
    #define XIOU_SLCR_SD0_ITAPDLY_XSDPS_ITAPDLYSEL_DEFVAL         0x0UL

/**
 * Register: XiouSlcrSdOtapdlysel
 */
    #define XIOU_SLCR_SD_OTAPDLYSEL                               ( ( XIOU_SLCR_BASEADDR ) +0x00000318UL )
    #define XIOU_SLCR_SD_OTAPDLYSEL_RSTVAL                        0x00000000UL

    #define XIOU_SLCR_SD1_OTAPDLYSEL_XSDPS_OTAPDLYENA_SHIFT       22UL
    #define XIOU_SLCR_SD1_OTAPDLYSEL_XSDPS_OTAPDLYENA_WIDTH       1UL
    #define XIOU_SLCR_SD1_OTAPDLYSEL_XSDPS_OTAPDLYENA_MASK        0x00400000UL
    #define XIOU_SLCR_SD1_OTAPDLYSEL_XSDPS_OTAPDLYENA_DEFVAL      0x0UL

    #define XIOU_SLCR_SD1_OTAPDLYSEL_XSDPS_SHIFT                  16UL
    #define XIOU_SLCR_SD1_OTAPDLYSEL_XSDPS_WIDTH                  6UL
    #define XIOU_SLCR_SD1_OTAPDLYSEL_XSDPS_MASK                   0x003f0000UL
    #define XIOU_SLCR_SD1_OTAPDLYSEL_XSDPS_DEFVAL                 0x0UL

    #define XIOU_SLCR_SD0_OTAPDLYSEL_XSDPS_OTAPDLYENA_SHIFT       6UL
    #define XIOU_SLCR_SD0_OTAPDLYSEL_XSDPS_OTAPDLYENA_WIDTH       1UL
    #define XIOU_SLCR_SD0_OTAPDLYSEL_XSDPS_OTAPDLYENA_MASK        0x00000040UL
    #define XIOU_SLCR_SD0_OTAPDLYSEL_XSDPS_OTAPDLYENA_DEFVAL      0x0UL

    #define XIOU_SLCR_SD0_OTAPDLYSEL_XSDPS_SHIFT                  0UL
    #define XIOU_SLCR_SD0_OTAPDLYSEL_XSDPS_WIDTH                  6UL
    #define XIOU_SLCR_SD0_OTAPDLYSEL_XSDPS_MASK                   0x0000003fUL
    #define XIOU_SLCR_SD0_OTAPDLYSEL_XSDPS_DEFVAL                 0x0UL

/**
 * Register: XiouSlcrSdCfgReg1
 */
    #define XIOU_SLCR_SD_CFG_REG1                                 ( ( XIOU_SLCR_BASEADDR ) +0x0000031CUL )
    #define XIOU_SLCR_SD_CFG_REG1_RSTVAL                          0x32403240UL

    #define XIOU_SLCR_SD1_CFG_REG1_XSDPS_BASECLK_SHIFT            23UL
    #define XIOU_SLCR_SD1_CFG_REG1_XSDPS_BASECLK_WIDTH            8UL
    #define XIOU_SLCR_SD1_CFG_REG1_XSDPS_BASECLK_MASK             0x7f800000UL
    #define XIOU_SLCR_SD1_CFG_REG1_XSDPS_BASECLK_DEFVAL           0x64UL

    #define XIOU_SLCR_SD1_CFG_REG1_XSDPS_TUNIGCOUNT_SHIFT         17UL
    #define XIOU_SLCR_SD1_CFG_REG1_XSDPS_TUNIGCOUNT_WIDTH         6UL
    #define XIOU_SLCR_SD1_CFG_REG1_XSDPS_TUNIGCOUNT_MASK          0x007e0000UL
    #define XIOU_SLCR_SD1_CFG_REG1_XSDPS_TUNIGCOUNT_DEFVAL        0x20UL

    #define XIOU_SLCR_SD1_CFG_REG1_XSDPS_ASYNCWKPENA_SHIFT        16UL
    #define XIOU_SLCR_SD1_CFG_REG1_XSDPS_ASYNCWKPENA_WIDTH        1UL
    #define XIOU_SLCR_SD1_CFG_REG1_XSDPS_ASYNCWKPENA_MASK         0x00010000UL
    #define XIOU_SLCR_SD1_CFG_REG1_XSDPS_ASYNCWKPENA_DEFVAL       0x0UL

    #define XIOU_SLCR_SD0_CFG_REG1_XSDPS_BASECLK_SHIFT            7UL
    #define XIOU_SLCR_SD0_CFG_REG1_XSDPS_BASECLK_WIDTH            8UL
    #define XIOU_SLCR_SD0_CFG_REG1_XSDPS_BASECLK_MASK             0x00007f80UL
    #define XIOU_SLCR_SD0_CFG_REG1_XSDPS_BASECLK_DEFVAL           0x64UL

    #define XIOU_SLCR_SD0_CFG_REG1_XSDPS_TUNIGCOUNT_SHIFT         1UL
    #define XIOU_SLCR_SD0_CFG_REG1_XSDPS_TUNIGCOUNT_WIDTH         6UL
    #define XIOU_SLCR_SD0_CFG_REG1_XSDPS_TUNIGCOUNT_MASK          0x0000007eUL
    #define XIOU_SLCR_SD0_CFG_REG1_XSDPS_TUNIGCOUNT_DEFVAL        0x20UL

    #define XIOU_SLCR_SD0_CFG_REG1_XSDPS_ASYNCWKPENA_SHIFT        0UL
    #define XIOU_SLCR_SD0_CFG_REG1_XSDPS_ASYNCWKPENA_WIDTH        1UL
    #define XIOU_SLCR_SD0_CFG_REG1_XSDPS_ASYNCWKPENA_MASK         0x00000001UL
    #define XIOU_SLCR_SD0_CFG_REG1_XSDPS_ASYNCWKPENA_DEFVAL       0x0UL

/**
 * Register: XiouSlcrSdCfgReg2
 */
    #define XIOU_SLCR_SD_CFG_REG2                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000320UL )
    #define XIOU_SLCR_SD_CFG_REG2_RSTVAL                          0x0ffc0ffcUL

    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_SLOTTYPE_SHIFT           28UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_SLOTTYPE_WIDTH           2UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_SLOTTYPE_MASK            0x30000000UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_SLOTTYPE_DEFVAL          0x0UL

    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_ASYCINTR_SHIFT           27UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_ASYCINTR_WIDTH           1UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_ASYCINTR_MASK            0x08000000UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_ASYCINTR_DEFVAL          0x1UL

    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_64BIT_SHIFT              26UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_64BIT_WIDTH              1UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_64BIT_MASK               0x04000000UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_64BIT_DEFVAL             0x1UL

    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_1P8V_SHIFT               25UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_1P8V_WIDTH               1UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_1P8V_MASK                0x02000000UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_1P8V_DEFVAL              0x1UL

    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_3P0V_SHIFT               24UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_3P0V_WIDTH               1UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_3P0V_MASK                0x01000000UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_3P0V_DEFVAL              0x1UL

    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_3P3V_SHIFT               23UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_3P3V_WIDTH               1UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_3P3V_MASK                0x00800000UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_3P3V_DEFVAL              0x1UL

    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_SUSPRES_SHIFT            22UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_SUSPRES_WIDTH            1UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_SUSPRES_MASK             0x00400000UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_SUSPRES_DEFVAL           0x1UL

    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_SDMA_SHIFT               21UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_SDMA_WIDTH               1UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_SDMA_MASK                0x00200000UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_SDMA_DEFVAL              0x1UL

    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_HIGHSPEED_SHIFT          20UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_HIGHSPEED_WIDTH          1UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_HIGHSPEED_MASK           0x00100000UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_HIGHSPEED_DEFVAL         0x1UL

    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_ADMA2_SHIFT              19UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_ADMA2_WIDTH              1UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_ADMA2_MASK               0x00080000UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_ADMA2_DEFVAL             0x1UL

    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_8BIT_SHIFT               18UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_8BIT_WIDTH               1UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_8BIT_MASK                0x00040000UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_8BIT_DEFVAL              0x1UL

    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_MAXBLK_SHIFT             16UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_MAXBLK_WIDTH             2UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_MAXBLK_MASK              0x00030000UL
    #define XIOU_SLCR_SD1_CFG_REG2_XSDPS_MAXBLK_DEFVAL            0x0UL

    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_SLOTTYPE_SHIFT           12UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_SLOTTYPE_WIDTH           2UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_SLOTTYPE_MASK            0x00003000UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_SLOTTYPE_DEFVAL          0x0UL

    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_ASYCINTR_SHIFT           11UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_ASYCINTR_WIDTH           1UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_ASYCINTR_MASK            0x00000800UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_ASYCINTR_DEFVAL          0x1UL

    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_64BIT_SHIFT              10UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_64BIT_WIDTH              1UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_64BIT_MASK               0x00000400UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_64BIT_DEFVAL             0x1UL

    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_1P8V_SHIFT               9UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_1P8V_WIDTH               1UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_1P8V_MASK                0x00000200UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_1P8V_DEFVAL              0x1UL

    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_3P0V_SHIFT               8UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_3P0V_WIDTH               1UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_3P0V_MASK                0x00000100UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_3P0V_DEFVAL              0x1UL

    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_3P3V_SHIFT               7UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_3P3V_WIDTH               1UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_3P3V_MASK                0x00000080UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_3P3V_DEFVAL              0x1UL

    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_SUSPRES_SHIFT            6UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_SUSPRES_WIDTH            1UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_SUSPRES_MASK             0x00000040UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_SUSPRES_DEFVAL           0x1UL

    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_SDMA_SHIFT               5UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_SDMA_WIDTH               1UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_SDMA_MASK                0x00000020UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_SDMA_DEFVAL              0x1UL

    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_HIGHSPEED_SHIFT          4UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_HIGHSPEED_WIDTH          1UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_HIGHSPEED_MASK           0x00000010UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_HIGHSPEED_DEFVAL         0x1UL

    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_ADMA2_SHIFT              3UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_ADMA2_WIDTH              1UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_ADMA2_MASK               0x00000008UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_ADMA2_DEFVAL             0x1UL

    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_8BIT_SHIFT               2UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_8BIT_WIDTH               1UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_8BIT_MASK                0x00000004UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_8BIT_DEFVAL              0x1UL

    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_MAXBLK_SHIFT             0UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_MAXBLK_WIDTH             2UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_MAXBLK_MASK              0x00000003UL
    #define XIOU_SLCR_SD0_CFG_REG2_XSDPS_MAXBLK_DEFVAL            0x0UL

/**
 * Register: XiouSlcrSdCfgReg3
 */
    #define XIOU_SLCR_SD_CFG_REG3                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000324UL )
    #define XIOU_SLCR_SD_CFG_REG3_RSTVAL                          0x06070607UL

    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_TUNINGSDR50_SHIFT        26UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_TUNINGSDR50_WIDTH        1UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_TUNINGSDR50_MASK         0x04000000UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_TUNINGSDR50_DEFVAL       0x1UL

    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_RETUNETMR_SHIFT          22UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_RETUNETMR_WIDTH          4UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_RETUNETMR_MASK           0x03c00000UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_RETUNETMR_DEFVAL         0x8UL

    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_DDRIVER_SHIFT            21UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_DDRIVER_WIDTH            1UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_DDRIVER_MASK             0x00200000UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_DDRIVER_DEFVAL           0x0UL

    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_CDRIVER_SHIFT            20UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_CDRIVER_WIDTH            1UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_CDRIVER_MASK             0x00100000UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_CDRIVER_DEFVAL           0x0UL

    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_ADRIVER_SHIFT            19UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_ADRIVER_WIDTH            1UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_ADRIVER_MASK             0x00080000UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_ADRIVER_DEFVAL           0x0UL

    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_DDR50_SHIFT              18UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_DDR50_WIDTH              1UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_DDR50_MASK               0x00040000UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_DDR50_DEFVAL             0x1UL

    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_SDR104_SHIFT             17UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_SDR104_WIDTH             1UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_SDR104_MASK              0x00020000UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_SDR104_DEFVAL            0x1UL

    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_SDR50_SHIFT              16UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_SDR50_WIDTH              1UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_SDR50_MASK               0x00010000UL
    #define XIOU_SLCR_SD1_CFG_REG3_XSDPS_SDR50_DEFVAL             0x1UL

    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_TUNINGSDR50_SHIFT        10UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_TUNINGSDR50_WIDTH        1UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_TUNINGSDR50_MASK         0x00000400UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_TUNINGSDR50_DEFVAL       0x1UL

    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_RETUNETMR_SHIFT          6UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_RETUNETMR_WIDTH          4UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_RETUNETMR_MASK           0x000003c0UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_RETUNETMR_DEFVAL         0x8UL

    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_DDRIVER_SHIFT            5UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_DDRIVER_WIDTH            1UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_DDRIVER_MASK             0x00000020UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_DDRIVER_DEFVAL           0x0UL

    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_CDRIVER_SHIFT            4UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_CDRIVER_WIDTH            1UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_CDRIVER_MASK             0x00000010UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_CDRIVER_DEFVAL           0x0UL

    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_ADRIVER_SHIFT            3UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_ADRIVER_WIDTH            1UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_ADRIVER_MASK             0x00000008UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_ADRIVER_DEFVAL           0x0UL

    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_DDR50_SHIFT              2UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_DDR50_WIDTH              1UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_DDR50_MASK               0x00000004UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_DDR50_DEFVAL             0x1UL

    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_SDR104_SHIFT             1UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_SDR104_WIDTH             1UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_SDR104_MASK              0x00000002UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_SDR104_DEFVAL            0x1UL

    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_SDR50_SHIFT              0UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_SDR50_WIDTH              1UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_SDR50_MASK               0x00000001UL
    #define XIOU_SLCR_SD0_CFG_REG3_XSDPS_SDR50_DEFVAL             0x1UL

/**
 * Register: XiouSlcrSdInitpreset
 */
    #define XIOU_SLCR_SD_INITPRESET                               ( ( XIOU_SLCR_BASEADDR ) +0x00000328UL )
    #define XIOU_SLCR_SD_INITPRESET_RSTVAL                        0x01000100UL

    #define XIOU_SLCR_SD1_INITPRESET_XSDPS_SHIFT                  16UL
    #define XIOU_SLCR_SD1_INITPRESET_XSDPS_WIDTH                  13UL
    #define XIOU_SLCR_SD1_INITPRESET_XSDPS_MASK                   0x1fff0000UL
    #define XIOU_SLCR_SD1_INITPRESET_XSDPS_DEFVAL                 0x100UL

    #define XIOU_SLCR_SD0_INITPRESET_XSDPS_SHIFT                  0UL
    #define XIOU_SLCR_SD0_INITPRESET_XSDPS_WIDTH                  13UL
    #define XIOU_SLCR_SD0_INITPRESET_XSDPS_MASK                   0x00001fffUL
    #define XIOU_SLCR_SD0_INITPRESET_XSDPS_DEFVAL                 0x100UL

/**
 * Register: XiouSlcrSdDsppreset
 */
    #define XIOU_SLCR_SD_DSPPRESET                                ( ( XIOU_SLCR_BASEADDR ) +0x0000032CUL )
    #define XIOU_SLCR_SD_DSPPRESET_RSTVAL                         0x00040004UL

    #define XIOU_SLCR_SD1_DSPPRESET_XSDPS_SHIFT                   16UL
    #define XIOU_SLCR_SD1_DSPPRESET_XSDPS_WIDTH                   13UL
    #define XIOU_SLCR_SD1_DSPPRESET_XSDPS_MASK                    0x1fff0000UL
    #define XIOU_SLCR_SD1_DSPPRESET_XSDPS_DEFVAL                  0x4UL

    #define XIOU_SLCR_SD0_DSPPRESET_XSDPS_SHIFT                   0UL
    #define XIOU_SLCR_SD0_DSPPRESET_XSDPS_WIDTH                   13UL
    #define XIOU_SLCR_SD0_DSPPRESET_XSDPS_MASK                    0x00001fffUL
    #define XIOU_SLCR_SD0_DSPPRESET_XSDPS_DEFVAL                  0x4UL

/**
 * Register: XiouSlcrSdHspdpreset
 */
    #define XIOU_SLCR_SD_HSPDPRESET                               ( ( XIOU_SLCR_BASEADDR ) +0x00000330UL )
    #define XIOU_SLCR_SD_HSPDPRESET_RSTVAL                        0x00020002UL

    #define XIOU_SLCR_SD1_HSPDPRESET_XSDPS_SHIFT                  16UL
    #define XIOU_SLCR_SD1_HSPDPRESET_XSDPS_WIDTH                  13UL
    #define XIOU_SLCR_SD1_HSPDPRESET_XSDPS_MASK                   0x1fff0000UL
    #define XIOU_SLCR_SD1_HSPDPRESET_XSDPS_DEFVAL                 0x2UL

    #define XIOU_SLCR_SD0_HSPDPRESET_XSDPS_SHIFT                  0UL
    #define XIOU_SLCR_SD0_HSPDPRESET_XSDPS_WIDTH                  13UL
    #define XIOU_SLCR_SD0_HSPDPRESET_XSDPS_MASK                   0x00001fffUL
    #define XIOU_SLCR_SD0_HSPDPRESET_XSDPS_DEFVAL                 0x2UL

/**
 * Register: XiouSlcrSdSdr12preset
 */
    #define XIOU_SLCR_SD_SDR12PRESET                              ( ( XIOU_SLCR_BASEADDR ) +0x00000334UL )
    #define XIOU_SLCR_SD_SDR12PRESET_RSTVAL                       0x00040004UL

    #define XIOU_SLCR_SD1_SDR12PRESET_XSDPS_SHIFT                 16UL
    #define XIOU_SLCR_SD1_SDR12PRESET_XSDPS_WIDTH                 13UL
    #define XIOU_SLCR_SD1_SDR12PRESET_XSDPS_MASK                  0x1fff0000UL
    #define XIOU_SLCR_SD1_SDR12PRESET_XSDPS_DEFVAL                0x4UL

    #define XIOU_SLCR_SD0_SDR12PRESET_XSDPS_SHIFT                 0UL
    #define XIOU_SLCR_SD0_SDR12PRESET_XSDPS_WIDTH                 13UL
    #define XIOU_SLCR_SD0_SDR12PRESET_XSDPS_MASK                  0x00001fffUL
    #define XIOU_SLCR_SD0_SDR12PRESET_XSDPS_DEFVAL                0x4UL

/**
 * Register: XiouSlcrSdSdr25preset
 */
    #define XIOU_SLCR_SD_SDR25PRESET                              ( ( XIOU_SLCR_BASEADDR ) +0x00000338UL )
    #define XIOU_SLCR_SD_SDR25PRESET_RSTVAL                       0x00020002UL

    #define XIOU_SLCR_SD1_SDR25PRESET_XSDPS_SHIFT                 16UL
    #define XIOU_SLCR_SD1_SDR25PRESET_XSDPS_WIDTH                 13UL
    #define XIOU_SLCR_SD1_SDR25PRESET_XSDPS_MASK                  0x1fff0000UL
    #define XIOU_SLCR_SD1_SDR25PRESET_XSDPS_DEFVAL                0x2UL

    #define XIOU_SLCR_SD0_SDR25PRESET_XSDPS_SHIFT                 0UL
    #define XIOU_SLCR_SD0_SDR25PRESET_XSDPS_WIDTH                 13UL
    #define XIOU_SLCR_SD0_SDR25PRESET_XSDPS_MASK                  0x00001fffUL
    #define XIOU_SLCR_SD0_SDR25PRESET_XSDPS_DEFVAL                0x2UL

/**
 * Register: XiouSlcrSdSdr50prset
 */
    #define XIOU_SLCR_SD_SDR50PRSET                               ( ( XIOU_SLCR_BASEADDR ) +0x0000033CUL )
    #define XIOU_SLCR_SD_SDR50PRSET_RSTVAL                        0x00010001UL

    #define XIOU_SLCR_SD1_SDR50PRSET_XSDPS_SDR50PRESET_SHIFT      16UL
    #define XIOU_SLCR_SD1_SDR50PRSET_XSDPS_SDR50PRESET_WIDTH      13UL
    #define XIOU_SLCR_SD1_SDR50PRSET_XSDPS_SDR50PRESET_MASK       0x1fff0000UL
    #define XIOU_SLCR_SD1_SDR50PRSET_XSDPS_SDR50PRESET_DEFVAL     0x1UL

    #define XIOU_SLCR_SD0_SDR50PRSET_XSDPS_SDR50PRESET_SHIFT      0UL
    #define XIOU_SLCR_SD0_SDR50PRSET_XSDPS_SDR50PRESET_WIDTH      13UL
    #define XIOU_SLCR_SD0_SDR50PRSET_XSDPS_SDR50PRESET_MASK       0x00001fffUL
    #define XIOU_SLCR_SD0_SDR50PRSET_XSDPS_SDR50PRESET_DEFVAL     0x1UL

/**
 * Register: XiouSlcrSdSdr104prst
 */
    #define XIOU_SLCR_SD_SDR104PRST                               ( ( XIOU_SLCR_BASEADDR ) +0x00000340UL )
    #define XIOU_SLCR_SD_SDR104PRST_RSTVAL                        0x00000000UL

    #define XIOU_SLCR_SD1_SDR104PRST_XSDPS_SDR104PRESET_SHIFT     16UL
    #define XIOU_SLCR_SD1_SDR104PRST_XSDPS_SDR104PRESET_WIDTH     13UL
    #define XIOU_SLCR_SD1_SDR104PRST_XSDPS_SDR104PRESET_MASK      0x1fff0000UL
    #define XIOU_SLCR_SD1_SDR104PRST_XSDPS_SDR104PRESET_DEFVAL    0x0UL

    #define XIOU_SLCR_SD0_SDR104PRST_XSDPS_SDR104PRESET_SHIFT     0UL
    #define XIOU_SLCR_SD0_SDR104PRST_XSDPS_SDR104PRESET_WIDTH     13UL
    #define XIOU_SLCR_SD0_SDR104PRST_XSDPS_SDR104PRESET_MASK      0x00001fffUL
    #define XIOU_SLCR_SD0_SDR104PRST_XSDPS_SDR104PRESET_DEFVAL    0x0UL

/**
 * Register: XiouSlcrSdDdr50preset
 */
    #define XIOU_SLCR_SD_DDR50PRESET                              ( ( XIOU_SLCR_BASEADDR ) +0x00000344UL )
    #define XIOU_SLCR_SD_DDR50PRESET_RSTVAL                       0x00020002UL

    #define XIOU_SLCR_SD1_DDR50PRESET_XSDPS_SHIFT                 16UL
    #define XIOU_SLCR_SD1_DDR50PRESET_XSDPS_WIDTH                 13UL
    #define XIOU_SLCR_SD1_DDR50PRESET_XSDPS_MASK                  0x1fff0000UL
    #define XIOU_SLCR_SD1_DDR50PRESET_XSDPS_DEFVAL                0x2UL

    #define XIOU_SLCR_SD0_DDR50PRESET_XSDPS_SHIFT                 0UL
    #define XIOU_SLCR_SD0_DDR50PRESET_XSDPS_WIDTH                 13UL
    #define XIOU_SLCR_SD0_DDR50PRESET_XSDPS_MASK                  0x00001fffUL
    #define XIOU_SLCR_SD0_DDR50PRESET_XSDPS_DEFVAL                0x2UL

/**
 * Register: XiouSlcrSdMaxcur1p8
 */
    #define XIOU_SLCR_SD_MAXCUR1P8                                ( ( XIOU_SLCR_BASEADDR ) +0x0000034CUL )
    #define XIOU_SLCR_SD_MAXCUR1P8_RSTVAL                         0x00000000UL

    #define XIOU_SLCR_SD1_MAXCUR1P8_XSDPS_SHIFT                   16UL
    #define XIOU_SLCR_SD1_MAXCUR1P8_XSDPS_WIDTH                   8UL
    #define XIOU_SLCR_SD1_MAXCUR1P8_XSDPS_MASK                    0x00ff0000UL
    #define XIOU_SLCR_SD1_MAXCUR1P8_XSDPS_DEFVAL                  0x0UL

    #define XIOU_SLCR_SD0_MAXCUR1P8_XSDPS_SHIFT                   0UL
    #define XIOU_SLCR_SD0_MAXCUR1P8_XSDPS_WIDTH                   8UL
    #define XIOU_SLCR_SD0_MAXCUR1P8_XSDPS_MASK                    0x000000ffUL
    #define XIOU_SLCR_SD0_MAXCUR1P8_XSDPS_DEFVAL                  0x0UL

/**
 * Register: XiouSlcrSdMaxcur3p0
 */
    #define XIOU_SLCR_SD_MAXCUR3P0                                ( ( XIOU_SLCR_BASEADDR ) +0x00000350UL )
    #define XIOU_SLCR_SD_MAXCUR3P0_RSTVAL                         0x00000000UL

    #define XIOU_SLCR_SD1_MAXCUR3P0_XSDPS_SHIFT                   16UL
    #define XIOU_SLCR_SD1_MAXCUR3P0_XSDPS_WIDTH                   8UL
    #define XIOU_SLCR_SD1_MAXCUR3P0_XSDPS_MASK                    0x00ff0000UL
    #define XIOU_SLCR_SD1_MAXCUR3P0_XSDPS_DEFVAL                  0x0UL

    #define XIOU_SLCR_SD0_MAXCUR3P0_XSDPS_SHIFT                   0UL
    #define XIOU_SLCR_SD0_MAXCUR3P0_XSDPS_WIDTH                   8UL
    #define XIOU_SLCR_SD0_MAXCUR3P0_XSDPS_MASK                    0x000000ffUL
    #define XIOU_SLCR_SD0_MAXCUR3P0_XSDPS_DEFVAL                  0x0UL

/**
 * Register: XiouSlcrSdMaxcur3p3
 */
    #define XIOU_SLCR_SD_MAXCUR3P3                                ( ( XIOU_SLCR_BASEADDR ) +0x00000354UL )
    #define XIOU_SLCR_SD_MAXCUR3P3_RSTVAL                         0x00000000UL

    #define XIOU_SLCR_SD1_MAXCUR3P3_XSDPS_SHIFT                   16UL
    #define XIOU_SLCR_SD1_MAXCUR3P3_XSDPS_WIDTH                   8UL
    #define XIOU_SLCR_SD1_MAXCUR3P3_XSDPS_MASK                    0x00ff0000UL
    #define XIOU_SLCR_SD1_MAXCUR3P3_XSDPS_DEFVAL                  0x0UL

    #define XIOU_SLCR_SD0_MAXCUR3P3_XSDPS_SHIFT                   0UL
    #define XIOU_SLCR_SD0_MAXCUR3P3_XSDPS_WIDTH                   8UL
    #define XIOU_SLCR_SD0_MAXCUR3P3_XSDPS_MASK                    0x000000ffUL
    #define XIOU_SLCR_SD0_MAXCUR3P3_XSDPS_DEFVAL                  0x0UL

/**
 * Register: XiouSlcrSdDllCtrl
 */
    #define XIOU_SLCR_SD_DLL_CTRL                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000358UL )
    #define XIOU_SLCR_SD_DLL_CTRL_RSTVAL                          0x00000000UL

    #define XIOU_SLCR_SD1_DLL_CTRL_XSDPS_RST_SHIFT                18UL
    #define XIOU_SLCR_SD1_DLL_CTRL_XSDPS_RST_WIDTH                1UL
    #define XIOU_SLCR_SD1_DLL_CTRL_XSDPS_RST_MASK                 0x00040000UL
    #define XIOU_SLCR_SD1_DLL_CTRL_XSDPS_RST_DEFVAL               0x0UL

    #define XIOU_SLCR_SD1_DLL_CTRL_XSDPS_TESTMODE_SHIFT           17UL
    #define XIOU_SLCR_SD1_DLL_CTRL_XSDPS_TESTMODE_WIDTH           1UL
    #define XIOU_SLCR_SD1_DLL_CTRL_XSDPS_TESTMODE_MASK            0x00020000UL
    #define XIOU_SLCR_SD1_DLL_CTRL_XSDPS_TESTMODE_DEFVAL          0x0UL

    #define XIOU_SLCR_SD1_DLL_CTRL_XSDPS_LOCK_SHIFT               16UL
    #define XIOU_SLCR_SD1_DLL_CTRL_XSDPS_LOCK_WIDTH               1UL
    #define XIOU_SLCR_SD1_DLL_CTRL_XSDPS_LOCK_MASK                0x00010000UL
    #define XIOU_SLCR_SD1_DLL_CTRL_XSDPS_LOCK_DEFVAL              0x0UL

    #define XIOU_SLCR_SD0_DLL_CTRL_XSDPS_RST_SHIFT                2UL
    #define XIOU_SLCR_SD0_DLL_CTRL_XSDPS_RST_WIDTH                1UL
    #define XIOU_SLCR_SD0_DLL_CTRL_XSDPS_RST_MASK                 0x00000004UL
    #define XIOU_SLCR_SD0_DLL_CTRL_XSDPS_RST_DEFVAL               0x0UL

    #define XIOU_SLCR_SD0_DLL_CTRL_XSDPS_TESTMODE_SHIFT           1UL
    #define XIOU_SLCR_SD0_DLL_CTRL_XSDPS_TESTMODE_WIDTH           1UL
    #define XIOU_SLCR_SD0_DLL_CTRL_XSDPS_TESTMODE_MASK            0x00000002UL
    #define XIOU_SLCR_SD0_DLL_CTRL_XSDPS_TESTMODE_DEFVAL          0x0UL

    #define XIOU_SLCR_SD0_DLL_CTRL_XSDPS_LOCK_SHIFT               0UL
    #define XIOU_SLCR_SD0_DLL_CTRL_XSDPS_LOCK_WIDTH               1UL
    #define XIOU_SLCR_SD0_DLL_CTRL_XSDPS_LOCK_MASK                0x00000001UL
    #define XIOU_SLCR_SD0_DLL_CTRL_XSDPS_LOCK_DEFVAL              0x0UL

/**
 * Register: XiouSlcrSdCdnCtrl
 */
    #define XIOU_SLCR_SD_CDN_CTRL                                 ( ( XIOU_SLCR_BASEADDR ) +0x0000035CUL )
    #define XIOU_SLCR_SD_CDN_CTRL_RSTVAL                          0x00000000UL

    #define XIOU_SLCR_SD1_CDN_CTRL_XSDPS_SHIFT                    16UL
    #define XIOU_SLCR_SD1_CDN_CTRL_XSDPS_WIDTH                    1UL
    #define XIOU_SLCR_SD1_CDN_CTRL_XSDPS_MASK                     0x00010000UL
    #define XIOU_SLCR_SD1_CDN_CTRL_XSDPS_DEFVAL                   0x0UL

    #define XIOU_SLCR_SD0_CDN_CTRL_XSDPS_SHIFT                    0UL
    #define XIOU_SLCR_SD0_CDN_CTRL_XSDPS_WIDTH                    1UL
    #define XIOU_SLCR_SD0_CDN_CTRL_XSDPS_MASK                     0x00000001UL
    #define XIOU_SLCR_SD0_CDN_CTRL_XSDPS_DEFVAL                   0x0UL

/**
 * Register: XiouSlcrGemCtrl
 */
    #define XIOU_SLCR_GEM_CTRL                                    ( ( XIOU_SLCR_BASEADDR ) +0x00000360UL )
    #define XIOU_SLCR_GEM_CTRL_RSTVAL                             0x00000000UL

    #define XIOU_SLCR_GEM3_CTRL_XEMACPS_SGMII_SD_SHIFT            6UL
    #define XIOU_SLCR_GEM3_CTRL_XEMACPS_SGMII_SD_WIDTH            2UL
    #define XIOU_SLCR_GEM3_CTRL_XEMACPS_SGMII_SD_MASK             0x000000c0UL
    #define XIOU_SLCR_GEM3_CTRL_XEMACPS_SGMII_SD_DEFVAL           0x0UL

    #define XIOU_SLCR_GEM2_CTRL_XEMACPS_SGMII_SD_SHIFT            4UL
    #define XIOU_SLCR_GEM2_CTRL_XEMACPS_SGMII_SD_WIDTH            2UL
    #define XIOU_SLCR_GEM2_CTRL_XEMACPS_SGMII_SD_MASK             0x00000030UL
    #define XIOU_SLCR_GEM2_CTRL_XEMACPS_SGMII_SD_DEFVAL           0x0UL

    #define XIOU_SLCR_GEM1_CTRL_XEMACPS_SGMII_SD_SHIFT            2UL
    #define XIOU_SLCR_GEM1_CTRL_XEMACPS_SGMII_SD_WIDTH            2UL
    #define XIOU_SLCR_GEM1_CTRL_XEMACPS_SGMII_SD_MASK             0x0000000cUL
    #define XIOU_SLCR_GEM1_CTRL_XEMACPS_SGMII_SD_DEFVAL           0x0UL

    #define XIOU_SLCR_GEM0_CTRL_XEMACPS_SGMII_SD_SHIFT            0UL
    #define XIOU_SLCR_GEM0_CTRL_XEMACPS_SGMII_SD_WIDTH            2UL
    #define XIOU_SLCR_GEM0_CTRL_XEMACPS_SGMII_SD_MASK             0x00000003UL
    #define XIOU_SLCR_GEM0_CTRL_XEMACPS_SGMII_SD_DEFVAL           0x0UL

/**
 * Register: XiouSlcrTtcApbClk
 */
    #define XIOU_SLCR_TTC_APB_CLK                                 ( ( XIOU_SLCR_BASEADDR ) +0x00000380UL )
    #define XIOU_SLCR_TTC_APB_CLK_RSTVAL                          0x00000000UL

    #define XIOU_SLCR_TTC_APB_CLK_TTC3_SEL_SHIFT                  6UL
    #define XIOU_SLCR_TTC_APB_CLK_TTC3_SEL_WIDTH                  2UL
    #define XIOU_SLCR_TTC_APB_CLK_TTC3_SEL_MASK                   0x000000c0UL
    #define XIOU_SLCR_TTC_APB_CLK_TTC3_SEL_DEFVAL                 0x0UL

    #define XIOU_SLCR_TTC_APB_CLK_TTC2_SEL_SHIFT                  4UL
    #define XIOU_SLCR_TTC_APB_CLK_TTC2_SEL_WIDTH                  2UL
    #define XIOU_SLCR_TTC_APB_CLK_TTC2_SEL_MASK                   0x00000030UL
    #define XIOU_SLCR_TTC_APB_CLK_TTC2_SEL_DEFVAL                 0x0UL

    #define XIOU_SLCR_TTC_APB_CLK_TTC1_SEL_SHIFT                  2UL
    #define XIOU_SLCR_TTC_APB_CLK_TTC1_SEL_WIDTH                  2UL
    #define XIOU_SLCR_TTC_APB_CLK_TTC1_SEL_MASK                   0x0000000cUL
    #define XIOU_SLCR_TTC_APB_CLK_TTC1_SEL_DEFVAL                 0x0UL

    #define XIOU_SLCR_TTC_APB_CLK_TTC0_SEL_SHIFT                  0UL
    #define XIOU_SLCR_TTC_APB_CLK_TTC0_SEL_WIDTH                  2UL
    #define XIOU_SLCR_TTC_APB_CLK_TTC0_SEL_MASK                   0x00000003UL
    #define XIOU_SLCR_TTC_APB_CLK_TTC0_SEL_DEFVAL                 0x0UL

/**
 * Register: XiouSlcrTapdlyBypass
 */
    #define XIOU_SLCR_TAPDLY_BYPASS                               ( ( XIOU_SLCR_BASEADDR ) +0x00000390UL )
    #define XIOU_SLCR_TAPDLY_BYPASS_RSTVAL                        0x00000007UL

    #define XIOU_SLCR_TAPDLY_BYPASS_LQSPI_RX_SHIFT                2UL
    #define XIOU_SLCR_TAPDLY_BYPASS_LQSPI_RX_WIDTH                1UL
    #define XIOU_SLCR_TAPDLY_BYPASS_LQSPI_RX_MASK                 0x00000004UL
    #define XIOU_SLCR_TAPDLY_BYPASS_LQSPI_RX_DEFVAL               0x1UL

    #define XIOU_SLCR_TAPDLY_BYPASS_XNANDPS8_DQS_OUT_SHIFT        1UL
    #define XIOU_SLCR_TAPDLY_BYPASS_XNANDPS8_DQS_OUT_WIDTH        1UL
    #define XIOU_SLCR_TAPDLY_BYPASS_XNANDPS8_DQS_OUT_MASK         0x00000002UL
    #define XIOU_SLCR_TAPDLY_BYPASS_XNANDPS8_DQS_OUT_DEFVAL       0x1UL

    #define XIOU_SLCR_TAPDLY_BYPASS_XNANDPS8_DQS_IN_SHIFT         0UL
    #define XIOU_SLCR_TAPDLY_BYPASS_XNANDPS8_DQS_IN_WIDTH         1UL
    #define XIOU_SLCR_TAPDLY_BYPASS_XNANDPS8_DQS_IN_MASK          0x00000001UL
    #define XIOU_SLCR_TAPDLY_BYPASS_XNANDPS8_DQS_IN_DEFVAL        0x1UL

/**
 * Register: XiouSlcrCoherentCtrl
 */
    #define XIOU_SLCR_COHERENT_CTRL                               ( ( XIOU_SLCR_BASEADDR ) +0x00000400UL )
    #define XIOU_SLCR_COHERENT_CTRL_RSTVAL                        0x00000000UL

    #define XIOU_SLCR_COHERENT_CTRL_XQSPIPSAXI_COH_SHIFT          28UL
    #define XIOU_SLCR_COHERENT_CTRL_XQSPIPSAXI_COH_WIDTH          4UL
    #define XIOU_SLCR_COHERENT_CTRL_XQSPIPSAXI_COH_MASK           0xf0000000UL
    #define XIOU_SLCR_COHERENT_CTRL_XQSPIPSAXI_COH_DEFVAL         0x0UL

    #define XIOU_SLCR_COHERENT_CTRL_XNANDPS8_AXI_COH_SHIFT        24UL
    #define XIOU_SLCR_COHERENT_CTRL_XNANDPS8_AXI_COH_WIDTH        4UL
    #define XIOU_SLCR_COHERENT_CTRL_XNANDPS8_AXI_COH_MASK         0x0f000000UL
    #define XIOU_SLCR_COHERENT_CTRL_XNANDPS8_AXI_COH_DEFVAL       0x0UL

    #define XIOU_SLCR_COHERENT_CTRL_XSDPS1_AXI_COH_SHIFT          20UL
    #define XIOU_SLCR_COHERENT_CTRL_XSDPS1_AXI_COH_WIDTH          4UL
    #define XIOU_SLCR_COHERENT_CTRL_XSDPS1_AXI_COH_MASK           0x00f00000UL
    #define XIOU_SLCR_COHERENT_CTRL_XSDPS1_AXI_COH_DEFVAL         0x0UL

    #define XIOU_SLCR_COHERENT_CTRL_XSDPS0_AXI_COH_SHIFT          16UL
    #define XIOU_SLCR_COHERENT_CTRL_XSDPS0_AXI_COH_WIDTH          4UL
    #define XIOU_SLCR_COHERENT_CTRL_XSDPS0_AXI_COH_MASK           0x000f0000UL
    #define XIOU_SLCR_COHERENT_CTRL_XSDPS0_AXI_COH_DEFVAL         0x0UL

    #define XIOU_SLCR_COHERENT_CTRL_GEM3_AXI_COH_SHIFT            12UL
    #define XIOU_SLCR_COHERENT_CTRL_GEM3_AXI_COH_WIDTH            4UL
    #define XIOU_SLCR_COHERENT_CTRL_GEM3_AXI_COH_MASK             0x0000f000UL
    #define XIOU_SLCR_COHERENT_CTRL_GEM3_AXI_COH_DEFVAL           0x0UL

    #define XIOU_SLCR_COHERENT_CTRL_GEM2_AXI_COH_SHIFT            8UL
    #define XIOU_SLCR_COHERENT_CTRL_GEM2_AXI_COH_WIDTH            4UL
    #define XIOU_SLCR_COHERENT_CTRL_GEM2_AXI_COH_MASK             0x00000f00UL
    #define XIOU_SLCR_COHERENT_CTRL_GEM2_AXI_COH_DEFVAL           0x0UL

    #define XIOU_SLCR_COHERENT_CTRL_GEM1_AXI_COH_SHIFT            4UL
    #define XIOU_SLCR_COHERENT_CTRL_GEM1_AXI_COH_WIDTH            4UL
    #define XIOU_SLCR_COHERENT_CTRL_GEM1_AXI_COH_MASK             0x000000f0UL
    #define XIOU_SLCR_COHERENT_CTRL_GEM1_AXI_COH_DEFVAL           0x0UL

    #define XIOU_SLCR_COHERENT_CTRL_GEM0_AXI_COH_SHIFT            0UL
    #define XIOU_SLCR_COHERENT_CTRL_GEM0_AXI_COH_WIDTH            4UL
    #define XIOU_SLCR_COHERENT_CTRL_GEM0_AXI_COH_MASK             0x0000000fUL
    #define XIOU_SLCR_COHERENT_CTRL_GEM0_AXI_COH_DEFVAL           0x0UL

/**
 * Register: XiouSlcrVideoPssClkSel
 */
    #define XIOU_SLCR_VIDEO_PSS_CLK_SEL                           ( ( XIOU_SLCR_BASEADDR ) +0x00000404UL )
    #define XIOU_SLCR_VIDEO_PSS_CLK_SEL_RSTVAL                    0x00000000UL

    #define XIOU_SLCR_VIDEO_PSS_CLK_SEL_ALT_SHIFT                 1UL
    #define XIOU_SLCR_VIDEO_PSS_CLK_SEL_ALT_WIDTH                 1UL
    #define XIOU_SLCR_VIDEO_PSS_CLK_SEL_ALT_MASK                  0x00000002UL
    #define XIOU_SLCR_VIDEO_PSS_CLK_SEL_ALT_DEFVAL                0x0UL

    #define XIOU_SLCR_VIDEO_PSS_CLK_SEL_SHIFT                     0UL
    #define XIOU_SLCR_VIDEO_PSS_CLK_SEL_WIDTH                     1UL
    #define XIOU_SLCR_VIDEO_PSS_CLK_SEL_MASK                      0x00000001UL
    #define XIOU_SLCR_VIDEO_PSS_CLK_SEL_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrInterconnectRoute
 */
    #define XIOU_SLCR_INTERCONNECT_ROUTE                          ( ( XIOU_SLCR_BASEADDR ) +0x00000408UL )
    #define XIOU_SLCR_INTERCONNECT_ROUTE_RSTVAL                   0x00000000UL

    #define XIOU_SLCR_INTERCONNECT_ROUTE_XNANDPS8_SHIFT           7UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_XNANDPS8_WIDTH           1UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_XNANDPS8_MASK            0x00000080UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_XNANDPS8_DEFVAL          0x0UL

    #define XIOU_SLCR_INTERCONNECT_ROUTE_QSPI_SHIFT               6UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_QSPI_WIDTH               1UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_QSPI_MASK                0x00000040UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_QSPI_DEFVAL              0x0UL

    #define XIOU_SLCR_INTERCONNECT_ROUTE_XSDPS1_SHIFT             5UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_XSDPS1_WIDTH             1UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_XSDPS1_MASK              0x00000020UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_XSDPS1_DEFVAL            0x0UL

    #define XIOU_SLCR_INTERCONNECT_ROUTE_XSDPS0_SHIFT             4UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_XSDPS0_WIDTH             1UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_XSDPS0_MASK              0x00000010UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_XSDPS0_DEFVAL            0x0UL

    #define XIOU_SLCR_INTERCONNECT_ROUTE_GEM3_SHIFT               3UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_GEM3_WIDTH               1UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_GEM3_MASK                0x00000008UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_GEM3_DEFVAL              0x0UL

    #define XIOU_SLCR_INTERCONNECT_ROUTE_GEM2_SHIFT               2UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_GEM2_WIDTH               1UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_GEM2_MASK                0x00000004UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_GEM2_DEFVAL              0x0UL

    #define XIOU_SLCR_INTERCONNECT_ROUTE_GEM1_SHIFT               1UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_GEM1_WIDTH               1UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_GEM1_MASK                0x00000002UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_GEM1_DEFVAL              0x0UL

    #define XIOU_SLCR_INTERCONNECT_ROUTE_GEM0_SHIFT               0UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_GEM0_WIDTH               1UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_GEM0_MASK                0x00000001UL
    #define XIOU_SLCR_INTERCONNECT_ROUTE_GEM0_DEFVAL              0x0UL

/**
 * Register: XiouSlcrRamGem0
 */
    #define XIOU_SLCR_RAM_GEM0                                    ( ( XIOU_SLCR_BASEADDR ) +0x00000500UL )
    #define XIOU_SLCR_RAM_GEM0_RSTVAL                             0x00005b5bUL

    #define XIOU_SLCR_RAM_GEM0_EMASA1_SHIFT                       14UL
    #define XIOU_SLCR_RAM_GEM0_EMASA1_WIDTH                       1UL
    #define XIOU_SLCR_RAM_GEM0_EMASA1_MASK                        0x00004000UL
    #define XIOU_SLCR_RAM_GEM0_EMASA1_DEFVAL                      0x1UL

    #define XIOU_SLCR_RAM_GEM0_EMAB1_SHIFT                        11UL
    #define XIOU_SLCR_RAM_GEM0_EMAB1_WIDTH                        3UL
    #define XIOU_SLCR_RAM_GEM0_EMAB1_MASK                         0x00003800UL
    #define XIOU_SLCR_RAM_GEM0_EMAB1_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_GEM0_EMAA1_SHIFT                        8UL
    #define XIOU_SLCR_RAM_GEM0_EMAA1_WIDTH                        3UL
    #define XIOU_SLCR_RAM_GEM0_EMAA1_MASK                         0x00000700UL
    #define XIOU_SLCR_RAM_GEM0_EMAA1_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_GEM0_EMASA0_SHIFT                       6UL
    #define XIOU_SLCR_RAM_GEM0_EMASA0_WIDTH                       1UL
    #define XIOU_SLCR_RAM_GEM0_EMASA0_MASK                        0x00000040UL
    #define XIOU_SLCR_RAM_GEM0_EMASA0_DEFVAL                      0x1UL

    #define XIOU_SLCR_RAM_GEM0_EMAB0_SHIFT                        3UL
    #define XIOU_SLCR_RAM_GEM0_EMAB0_WIDTH                        3UL
    #define XIOU_SLCR_RAM_GEM0_EMAB0_MASK                         0x00000038UL
    #define XIOU_SLCR_RAM_GEM0_EMAB0_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_GEM0_EMAA0_SHIFT                        0UL
    #define XIOU_SLCR_RAM_GEM0_EMAA0_WIDTH                        3UL
    #define XIOU_SLCR_RAM_GEM0_EMAA0_MASK                         0x00000007UL
    #define XIOU_SLCR_RAM_GEM0_EMAA0_DEFVAL                       0x3UL

/**
 * Register: XiouSlcrRamgem1
 */
    #define XIOU_SLCR_RAM_GEM1                                    ( ( XIOU_SLCR_BASEADDR ) +0x00000504UL )
    #define XIOU_SLCR_RAM_GEM1_RSTVAL                             0x00005b5bUL

    #define XIOU_SLCR_RAM_GEM1_EMASA1_SHIFT                       14UL
    #define XIOU_SLCR_RAM_GEM1_EMASA1_WIDTH                       1UL
    #define XIOU_SLCR_RAM_GEM1_EMASA1_MASK                        0x00004000UL
    #define XIOU_SLCR_RAM_GEM1_EMASA1_DEFVAL                      0x1UL

    #define XIOU_SLCR_RAM_GEM1_EMAB1_SHIFT                        11UL
    #define XIOU_SLCR_RAM_GEM1_EMAB1_WIDTH                        3UL
    #define XIOU_SLCR_RAM_GEM1_EMAB1_MASK                         0x00003800UL
    #define XIOU_SLCR_RAM_GEM1_EMAB1_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_GEM1_EMAA1_SHIFT                        8UL
    #define XIOU_SLCR_RAM_GEM1_EMAA1_WIDTH                        3UL
    #define XIOU_SLCR_RAM_GEM1_EMAA1_MASK                         0x00000700UL
    #define XIOU_SLCR_RAM_GEM1_EMAA1_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_GEM1_EMASA0_SHIFT                       6UL
    #define XIOU_SLCR_RAM_GEM1_EMASA0_WIDTH                       1UL
    #define XIOU_SLCR_RAM_GEM1_EMASA0_MASK                        0x00000040UL
    #define XIOU_SLCR_RAM_GEM1_EMASA0_DEFVAL                      0x1UL

    #define XIOU_SLCR_RAM_GEM1_EMAB0_SHIFT                        3UL
    #define XIOU_SLCR_RAM_GEM1_EMAB0_WIDTH                        3UL
    #define XIOU_SLCR_RAM_GEM1_EMAB0_MASK                         0x00000038UL
    #define XIOU_SLCR_RAM_GEM1_EMAB0_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_GEM1_EMAA0_SHIFT                        0UL
    #define XIOU_SLCR_RAM_GEM1_EMAA0_WIDTH                        3UL
    #define XIOU_SLCR_RAM_GEM1_EMAA0_MASK                         0x00000007UL
    #define XIOU_SLCR_RAM_GEM1_EMAA0_DEFVAL                       0x3UL

/**
 * Register: XiouSlcrRamGem2
 */
    #define XIOU_SLCR_RAM_GEM2                                    ( ( XIOU_SLCR_BASEADDR ) +0x00000508UL )
    #define XIOU_SLCR_RAM_GEM2_RSTVAL                             0x00005b5bUL

    #define XIOU_SLCR_RAM_GEM2_EMASA1_SHIFT                       14UL
    #define XIOU_SLCR_RAM_GEM2_EMASA1_WIDTH                       1UL
    #define XIOU_SLCR_RAM_GEM2_EMASA1_MASK                        0x00004000UL
    #define XIOU_SLCR_RAM_GEM2_EMASA1_DEFVAL                      0x1UL

    #define XIOU_SLCR_RAM_GEM2_EMAB1_SHIFT                        11UL
    #define XIOU_SLCR_RAM_GEM2_EMAB1_WIDTH                        3UL
    #define XIOU_SLCR_RAM_GEM2_EMAB1_MASK                         0x00003800UL
    #define XIOU_SLCR_RAM_GEM2_EMAB1_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_GEM2_EMAA1_SHIFT                        8UL
    #define XIOU_SLCR_RAM_GEM2_EMAA1_WIDTH                        3UL
    #define XIOU_SLCR_RAM_GEM2_EMAA1_MASK                         0x00000700UL
    #define XIOU_SLCR_RAM_GEM2_EMAA1_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_GEM2_EMASA0_SHIFT                       6UL
    #define XIOU_SLCR_RAM_GEM2_EMASA0_WIDTH                       1UL
    #define XIOU_SLCR_RAM_GEM2_EMASA0_MASK                        0x00000040UL
    #define XIOU_SLCR_RAM_GEM2_EMASA0_DEFVAL                      0x1UL

    #define XIOU_SLCR_RAM_GEM2_EMAB0_SHIFT                        3UL
    #define XIOU_SLCR_RAM_GEM2_EMAB0_WIDTH                        3UL
    #define XIOU_SLCR_RAM_GEM2_EMAB0_MASK                         0x00000038UL
    #define XIOU_SLCR_RAM_GEM2_EMAB0_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_GEM2_EMAA0_SHIFT                        0UL
    #define XIOU_SLCR_RAM_GEM2_EMAA0_WIDTH                        3UL
    #define XIOU_SLCR_RAM_GEM2_EMAA0_MASK                         0x00000007UL
    #define XIOU_SLCR_RAM_GEM2_EMAA0_DEFVAL                       0x3UL

/**
 * Register: XiouSlcrRamGem3
 */
    #define XIOU_SLCR_RAM_GEM3                                    ( ( XIOU_SLCR_BASEADDR ) +0x0000050CUL )
    #define XIOU_SLCR_RAM_GEM3_RSTVAL                             0x00005b5bUL

    #define XIOU_SLCR_RAM_GEM3_EMASA1_SHIFT                       14UL
    #define XIOU_SLCR_RAM_GEM3_EMASA1_WIDTH                       1UL
    #define XIOU_SLCR_RAM_GEM3_EMASA1_MASK                        0x00004000UL
    #define XIOU_SLCR_RAM_GEM3_EMASA1_DEFVAL                      0x1UL

    #define XIOU_SLCR_RAM_GEM3_EMAB1_SHIFT                        11UL
    #define XIOU_SLCR_RAM_GEM3_EMAB1_WIDTH                        3UL
    #define XIOU_SLCR_RAM_GEM3_EMAB1_MASK                         0x00003800UL
    #define XIOU_SLCR_RAM_GEM3_EMAB1_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_GEM3_EMAA1_SHIFT                        8UL
    #define XIOU_SLCR_RAM_GEM3_EMAA1_WIDTH                        3UL
    #define XIOU_SLCR_RAM_GEM3_EMAA1_MASK                         0x00000700UL
    #define XIOU_SLCR_RAM_GEM3_EMAA1_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_GEM3_EMASA0_SHIFT                       6UL
    #define XIOU_SLCR_RAM_GEM3_EMASA0_WIDTH                       1UL
    #define XIOU_SLCR_RAM_GEM3_EMASA0_MASK                        0x00000040UL
    #define XIOU_SLCR_RAM_GEM3_EMASA0_DEFVAL                      0x1UL

    #define XIOU_SLCR_RAM_GEM3_EMAB0_SHIFT                        3UL
    #define XIOU_SLCR_RAM_GEM3_EMAB0_WIDTH                        3UL
    #define XIOU_SLCR_RAM_GEM3_EMAB0_MASK                         0x00000038UL
    #define XIOU_SLCR_RAM_GEM3_EMAB0_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_GEM3_EMAA0_SHIFT                        0UL
    #define XIOU_SLCR_RAM_GEM3_EMAA0_WIDTH                        3UL
    #define XIOU_SLCR_RAM_GEM3_EMAA0_MASK                         0x00000007UL
    #define XIOU_SLCR_RAM_GEM3_EMAA0_DEFVAL                       0x3UL

/**
 * Register: XiouSlcrRamXsdps0
 */
    #define XIOU_SLCR_RAM_XSDPS0                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000510UL )
    #define XIOU_SLCR_RAM_XSDPS0_RSTVAL                           0x0000005bUL

    #define XIOU_SLCR_RAM_XSDPS0_EMASA0_SHIFT                     6UL
    #define XIOU_SLCR_RAM_XSDPS0_EMASA0_WIDTH                     1UL
    #define XIOU_SLCR_RAM_XSDPS0_EMASA0_MASK                      0x00000040UL
    #define XIOU_SLCR_RAM_XSDPS0_EMASA0_DEFVAL                    0x1UL

    #define XIOU_SLCR_RAM_XSDPS0_EMAB0_SHIFT                      3UL
    #define XIOU_SLCR_RAM_XSDPS0_EMAB0_WIDTH                      3UL
    #define XIOU_SLCR_RAM_XSDPS0_EMAB0_MASK                       0x00000038UL
    #define XIOU_SLCR_RAM_XSDPS0_EMAB0_DEFVAL                     0x3UL

    #define XIOU_SLCR_RAM_XSDPS0_EMAA0_SHIFT                      0UL
    #define XIOU_SLCR_RAM_XSDPS0_EMAA0_WIDTH                      3UL
    #define XIOU_SLCR_RAM_XSDPS0_EMAA0_MASK                       0x00000007UL
    #define XIOU_SLCR_RAM_XSDPS0_EMAA0_DEFVAL                     0x3UL

/**
 * Register: XiouSlcrRamXsdps1
 */
    #define XIOU_SLCR_RAM_XSDPS1                                  ( ( XIOU_SLCR_BASEADDR ) +0x00000514UL )
    #define XIOU_SLCR_RAM_XSDPS1_RSTVAL                           0x0000005bUL

    #define XIOU_SLCR_RAM_XSDPS1_EMASA0_SHIFT                     6UL
    #define XIOU_SLCR_RAM_XSDPS1_EMASA0_WIDTH                     1UL
    #define XIOU_SLCR_RAM_XSDPS1_EMASA0_MASK                      0x00000040UL
    #define XIOU_SLCR_RAM_XSDPS1_EMASA0_DEFVAL                    0x1UL

    #define XIOU_SLCR_RAM_XSDPS1_EMAB0_SHIFT                      3UL
    #define XIOU_SLCR_RAM_XSDPS1_EMAB0_WIDTH                      3UL
    #define XIOU_SLCR_RAM_XSDPS1_EMAB0_MASK                       0x00000038UL
    #define XIOU_SLCR_RAM_XSDPS1_EMAB0_DEFVAL                     0x3UL

    #define XIOU_SLCR_RAM_XSDPS1_EMAA0_SHIFT                      0UL
    #define XIOU_SLCR_RAM_XSDPS1_EMAA0_WIDTH                      3UL
    #define XIOU_SLCR_RAM_XSDPS1_EMAA0_MASK                       0x00000007UL
    #define XIOU_SLCR_RAM_XSDPS1_EMAA0_DEFVAL                     0x3UL

/**
 * Register: XiouSlcrRamCan0
 */
    #define XIOU_SLCR_RAM_CAN0                                    ( ( XIOU_SLCR_BASEADDR ) +0x00000518UL )
    #define XIOU_SLCR_RAM_CAN0_RSTVAL                             0x005b5b5bUL

    #define XIOU_SLCR_RAM_CAN0_EMASA2_SHIFT                       22UL
    #define XIOU_SLCR_RAM_CAN0_EMASA2_WIDTH                       1UL
    #define XIOU_SLCR_RAM_CAN0_EMASA2_MASK                        0x00400000UL
    #define XIOU_SLCR_RAM_CAN0_EMASA2_DEFVAL                      0x1UL

    #define XIOU_SLCR_RAM_CAN0_EMAB2_SHIFT                        19UL
    #define XIOU_SLCR_RAM_CAN0_EMAB2_WIDTH                        3UL
    #define XIOU_SLCR_RAM_CAN0_EMAB2_MASK                         0x00380000UL
    #define XIOU_SLCR_RAM_CAN0_EMAB2_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_CAN0_EMAA2_SHIFT                        16UL
    #define XIOU_SLCR_RAM_CAN0_EMAA2_WIDTH                        3UL
    #define XIOU_SLCR_RAM_CAN0_EMAA2_MASK                         0x00070000UL
    #define XIOU_SLCR_RAM_CAN0_EMAA2_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_CAN0_EMASA1_SHIFT                       14UL
    #define XIOU_SLCR_RAM_CAN0_EMASA1_WIDTH                       1UL
    #define XIOU_SLCR_RAM_CAN0_EMASA1_MASK                        0x00004000UL
    #define XIOU_SLCR_RAM_CAN0_EMASA1_DEFVAL                      0x1UL

    #define XIOU_SLCR_RAM_CAN0_EMAB1_SHIFT                        11UL
    #define XIOU_SLCR_RAM_CAN0_EMAB1_WIDTH                        3UL
    #define XIOU_SLCR_RAM_CAN0_EMAB1_MASK                         0x00003800UL
    #define XIOU_SLCR_RAM_CAN0_EMAB1_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_CAN0_EMAA1_SHIFT                        8UL
    #define XIOU_SLCR_RAM_CAN0_EMAA1_WIDTH                        3UL
    #define XIOU_SLCR_RAM_CAN0_EMAA1_MASK                         0x00000700UL
    #define XIOU_SLCR_RAM_CAN0_EMAA1_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_CAN0_EMASA0_SHIFT                       6UL
    #define XIOU_SLCR_RAM_CAN0_EMASA0_WIDTH                       1UL
    #define XIOU_SLCR_RAM_CAN0_EMASA0_MASK                        0x00000040UL
    #define XIOU_SLCR_RAM_CAN0_EMASA0_DEFVAL                      0x1UL

    #define XIOU_SLCR_RAM_CAN0_EMAB0_SHIFT                        3UL
    #define XIOU_SLCR_RAM_CAN0_EMAB0_WIDTH                        3UL
    #define XIOU_SLCR_RAM_CAN0_EMAB0_MASK                         0x00000038UL
    #define XIOU_SLCR_RAM_CAN0_EMAB0_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_CAN0_EMAA0_SHIFT                        0UL
    #define XIOU_SLCR_RAM_CAN0_EMAA0_WIDTH                        3UL
    #define XIOU_SLCR_RAM_CAN0_EMAA0_MASK                         0x00000007UL
    #define XIOU_SLCR_RAM_CAN0_EMAA0_DEFVAL                       0x3UL

/**
 * Register: XiouSlcrRamCan1
 */
    #define XIOU_SLCR_RAM_CAN1                                    ( ( XIOU_SLCR_BASEADDR ) +0x0000051CUL )
    #define XIOU_SLCR_RAM_CAN1_RSTVAL                             0x005b5b5bUL

    #define XIOU_SLCR_RAM_CAN1_EMASA2_SHIFT                       22UL
    #define XIOU_SLCR_RAM_CAN1_EMASA2_WIDTH                       1UL
    #define XIOU_SLCR_RAM_CAN1_EMASA2_MASK                        0x00400000UL
    #define XIOU_SLCR_RAM_CAN1_EMASA2_DEFVAL                      0x1UL

    #define XIOU_SLCR_RAM_CAN1_EMAB2_SHIFT                        19UL
    #define XIOU_SLCR_RAM_CAN1_EMAB2_WIDTH                        3UL
    #define XIOU_SLCR_RAM_CAN1_EMAB2_MASK                         0x00380000UL
    #define XIOU_SLCR_RAM_CAN1_EMAB2_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_CAN1_EMAA2_SHIFT                        16UL
    #define XIOU_SLCR_RAM_CAN1_EMAA2_WIDTH                        3UL
    #define XIOU_SLCR_RAM_CAN1_EMAA2_MASK                         0x00070000UL
    #define XIOU_SLCR_RAM_CAN1_EMAA2_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_CAN1_EMASA1_SHIFT                       14UL
    #define XIOU_SLCR_RAM_CAN1_EMASA1_WIDTH                       1UL
    #define XIOU_SLCR_RAM_CAN1_EMASA1_MASK                        0x00004000UL
    #define XIOU_SLCR_RAM_CAN1_EMASA1_DEFVAL                      0x1UL

    #define XIOU_SLCR_RAM_CAN1_EMAB1_SHIFT                        11UL
    #define XIOU_SLCR_RAM_CAN1_EMAB1_WIDTH                        3UL
    #define XIOU_SLCR_RAM_CAN1_EMAB1_MASK                         0x00003800UL
    #define XIOU_SLCR_RAM_CAN1_EMAB1_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_CAN1_EMAA1_SHIFT                        8UL
    #define XIOU_SLCR_RAM_CAN1_EMAA1_WIDTH                        3UL
    #define XIOU_SLCR_RAM_CAN1_EMAA1_MASK                         0x00000700UL
    #define XIOU_SLCR_RAM_CAN1_EMAA1_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_CAN1_EMASA0_SHIFT                       6UL
    #define XIOU_SLCR_RAM_CAN1_EMASA0_WIDTH                       1UL
    #define XIOU_SLCR_RAM_CAN1_EMASA0_MASK                        0x00000040UL
    #define XIOU_SLCR_RAM_CAN1_EMASA0_DEFVAL                      0x1UL

    #define XIOU_SLCR_RAM_CAN1_EMAB0_SHIFT                        3UL
    #define XIOU_SLCR_RAM_CAN1_EMAB0_WIDTH                        3UL
    #define XIOU_SLCR_RAM_CAN1_EMAB0_MASK                         0x00000038UL
    #define XIOU_SLCR_RAM_CAN1_EMAB0_DEFVAL                       0x3UL

    #define XIOU_SLCR_RAM_CAN1_EMAA0_SHIFT                        0UL
    #define XIOU_SLCR_RAM_CAN1_EMAA0_WIDTH                        3UL
    #define XIOU_SLCR_RAM_CAN1_EMAA0_MASK                         0x00000007UL
    #define XIOU_SLCR_RAM_CAN1_EMAA0_DEFVAL                       0x3UL

/**
 * Register: XiouSlcrRamLqspi
 */
    #define XIOU_SLCR_RAM_LQSPI                                   ( ( XIOU_SLCR_BASEADDR ) +0x00000520UL )
    #define XIOU_SLCR_RAM_LQSPI_RSTVAL                            0x00002ddbUL

    #define XIOU_SLCR_RAM_LQSPI_EMASA1_SHIFT                      13UL
    #define XIOU_SLCR_RAM_LQSPI_EMASA1_WIDTH                      1UL
    #define XIOU_SLCR_RAM_LQSPI_EMASA1_MASK                       0x00002000UL
    #define XIOU_SLCR_RAM_LQSPI_EMASA1_DEFVAL                     0x1UL

    #define XIOU_SLCR_RAM_LQSPI_EMAB1_SHIFT                       10UL
    #define XIOU_SLCR_RAM_LQSPI_EMAB1_WIDTH                       3UL
    #define XIOU_SLCR_RAM_LQSPI_EMAB1_MASK                        0x00001c00UL
    #define XIOU_SLCR_RAM_LQSPI_EMAB1_DEFVAL                      0x3UL

    #define XIOU_SLCR_RAM_LQSPI_EMAA1_SHIFT                       7UL
    #define XIOU_SLCR_RAM_LQSPI_EMAA1_WIDTH                       3UL
    #define XIOU_SLCR_RAM_LQSPI_EMAA1_MASK                        0x00000380UL
    #define XIOU_SLCR_RAM_LQSPI_EMAA1_DEFVAL                      0x3UL

    #define XIOU_SLCR_RAM_LQSPI_EMASA0_SHIFT                      6UL
    #define XIOU_SLCR_RAM_LQSPI_EMASA0_WIDTH                      1UL
    #define XIOU_SLCR_RAM_LQSPI_EMASA0_MASK                       0x00000040UL
    #define XIOU_SLCR_RAM_LQSPI_EMASA0_DEFVAL                     0x1UL

    #define XIOU_SLCR_RAM_LQSPI_EMAB0_SHIFT                       3UL
    #define XIOU_SLCR_RAM_LQSPI_EMAB0_WIDTH                       3UL
    #define XIOU_SLCR_RAM_LQSPI_EMAB0_MASK                        0x00000038UL
    #define XIOU_SLCR_RAM_LQSPI_EMAB0_DEFVAL                      0x3UL

    #define XIOU_SLCR_RAM_LQSPI_EMAA0_SHIFT                       0UL
    #define XIOU_SLCR_RAM_LQSPI_EMAA0_WIDTH                       3UL
    #define XIOU_SLCR_RAM_LQSPI_EMAA0_MASK                        0x00000007UL
    #define XIOU_SLCR_RAM_LQSPI_EMAA0_DEFVAL                      0x3UL

/**
 * Register: XiouSlcrRamXnandps8
 */
    #define XIOU_SLCR_RAM_XNANDPS8                                ( ( XIOU_SLCR_BASEADDR ) +0x00000524UL )
    #define XIOU_SLCR_RAM_XNANDPS8_RSTVAL                         0x0000005bUL

    #define XIOU_SLCR_RAM_XNANDPS8_EMASA0_SHIFT                   6UL
    #define XIOU_SLCR_RAM_XNANDPS8_EMASA0_WIDTH                   1UL
    #define XIOU_SLCR_RAM_XNANDPS8_EMASA0_MASK                    0x00000040UL
    #define XIOU_SLCR_RAM_XNANDPS8_EMASA0_DEFVAL                  0x1UL

    #define XIOU_SLCR_RAM_XNANDPS8_EMAB0_SHIFT                    3UL
    #define XIOU_SLCR_RAM_XNANDPS8_EMAB0_WIDTH                    3UL
    #define XIOU_SLCR_RAM_XNANDPS8_EMAB0_MASK                     0x00000038UL
    #define XIOU_SLCR_RAM_XNANDPS8_EMAB0_DEFVAL                   0x3UL

    #define XIOU_SLCR_RAM_XNANDPS8_EMAA0_SHIFT                    0UL
    #define XIOU_SLCR_RAM_XNANDPS8_EMAA0_WIDTH                    3UL
    #define XIOU_SLCR_RAM_XNANDPS8_EMAA0_MASK                     0x00000007UL
    #define XIOU_SLCR_RAM_XNANDPS8_EMAA0_DEFVAL                   0x3UL

/**
 * Register: XiouSlcrCtrl
 */
    #define XIOU_SLCR_CTRL                                        ( ( XIOU_SLCR_BASEADDR ) +0x00000600UL )
    #define XIOU_SLCR_CTRL_RSTVAL                                 0x00000000UL

    #define XIOU_SLCR_CTRL_SLVERR_EN_SHIFT                        0UL
    #define XIOU_SLCR_CTRL_SLVERR_EN_WIDTH                        1UL
    #define XIOU_SLCR_CTRL_SLVERR_EN_MASK                         0x00000001UL
    #define XIOU_SLCR_CTRL_SLVERR_EN_DEFVAL                       0x0UL

/**
 * Register: XiouSlcrIsr
 */
    #define XIOU_SLCR_ISR                                         ( ( XIOU_SLCR_BASEADDR ) +0x00000700UL )
    #define XIOU_SLCR_ISR_RSTVAL                                  0x00000000UL

    #define XIOU_SLCR_ISR_ADDR_DECD_ERR_SHIFT                     0UL
    #define XIOU_SLCR_ISR_ADDR_DECD_ERR_WIDTH                     1UL
    #define XIOU_SLCR_ISR_ADDR_DECD_ERR_MASK                      0x00000001UL
    #define XIOU_SLCR_ISR_ADDR_DECD_ERR_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrImr
 */
    #define XIOU_SLCR_IMR                                         ( ( XIOU_SLCR_BASEADDR ) +0x00000704UL )
    #define XIOU_SLCR_IMR_RSTVAL                                  0x00000001UL

    #define XIOU_SLCR_IMR_ADDR_DECD_ERR_SHIFT                     0UL
    #define XIOU_SLCR_IMR_ADDR_DECD_ERR_WIDTH                     1UL
    #define XIOU_SLCR_IMR_ADDR_DECD_ERR_MASK                      0x00000001UL
    #define XIOU_SLCR_IMR_ADDR_DECD_ERR_DEFVAL                    0x1UL

/**
 * Register: XiouSlcrIer
 */
    #define XIOU_SLCR_IER                                         ( ( XIOU_SLCR_BASEADDR ) +0x00000708UL )
    #define XIOU_SLCR_IER_RSTVAL                                  0x00000000UL

    #define XIOU_SLCR_IER_ADDR_DECD_ERR_SHIFT                     0UL
    #define XIOU_SLCR_IER_ADDR_DECD_ERR_WIDTH                     1UL
    #define XIOU_SLCR_IER_ADDR_DECD_ERR_MASK                      0x00000001UL
    #define XIOU_SLCR_IER_ADDR_DECD_ERR_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrIdr
 */
    #define XIOU_SLCR_IDR                                         ( ( XIOU_SLCR_BASEADDR ) +0x0000070CUL )
    #define XIOU_SLCR_IDR_RSTVAL                                  0x00000000UL

    #define XIOU_SLCR_IDR_ADDR_DECD_ERR_SHIFT                     0UL
    #define XIOU_SLCR_IDR_ADDR_DECD_ERR_WIDTH                     1UL
    #define XIOU_SLCR_IDR_ADDR_DECD_ERR_MASK                      0x00000001UL
    #define XIOU_SLCR_IDR_ADDR_DECD_ERR_DEFVAL                    0x0UL

/**
 * Register: XiouSlcrItr
 */
    #define XIOU_SLCR_ITR                                         ( ( XIOU_SLCR_BASEADDR ) +0x00000710UL )
    #define XIOU_SLCR_ITR_RSTVAL                                  0x00000000UL

    #define XIOU_SLCR_ITR_ADDR_DECD_ERR_SHIFT                     0UL
    #define XIOU_SLCR_ITR_ADDR_DECD_ERR_WIDTH                     1UL
    #define XIOU_SLCR_ITR_ADDR_DECD_ERR_MASK                      0x00000001UL
    #define XIOU_SLCR_ITR_ADDR_DECD_ERR_DEFVAL                    0x0UL


    #ifdef __cplusplus
}
    #endif

#endif /* __XIOU_SLCR_H__ */
