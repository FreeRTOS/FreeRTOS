#ifndef __GPIO_H__
#define __GPIO_H__

/* Generated automatically for XMC4500_QFP144 on: Mon Jan 14 10:10:13 2013*/

#include <XMC4500.h>

#define INPUT           0x00U
#define INPUT_PD        0x08U
#define INPUT_PU        0x10U
#define INPUT_PPS       0x18U
#define INPUT_INV       0x20U
#define INPUT_INV_PD    0x28U
#define INPUT_INV_PU    0x30U
#define INPUT_INV_PPS   0x38U
#define OUTPUT_PP_GP    0x80U
#define OUTPUT_PP_AF1   0x88U
#define OUTPUT_PP_AF2   0x90U
#define OUTPUT_PP_AF3   0x98U
#define OUTPUT_PP_AF4   0xA0U
#define OUTPUT_OD_GP    0xC0U
#define OUTPUT_OD_AF1   0xC8U
#define OUTPUT_OD_AF2   0xD0U
#define OUTPUT_OD_AF3   0xD8U
#define OUTPUT_OD_AF4   0XE0U

#define WEAK            0x7UL
#define MEDIUM          0x4UL
#define STRONG          0x2UL
#define VERYSTRONG      0x0UL

#define SOFTWARE        0x0UL
#define HW0             0x1UL
#define HW1             0x2UL

__STATIC_INLINE void P0_0_set_mode(uint8_t mode){
    PORT0->IOCR0 &= ~0x000000f8UL;
    PORT0->IOCR0 |= mode << 0;
}

__STATIC_INLINE void P0_0_set_driver_strength(uint8_t strength){
    PORT0->PDR0 &= ~0x00000007UL;
    PORT0->PDR0 |= strength << 0;
}

__STATIC_INLINE void P0_0_set_hwsel(uint32_t config){
    PORT0->HWSEL &= ~0x00000003UL;
    PORT0->HWSEL |= config << 0;
}

__STATIC_INLINE void P0_0_set(void){
    PORT0->OMR = 0x00000001UL;
}

__STATIC_INLINE void P0_0_reset(void){
    PORT0->OMR = 0x00010000UL;
}

__STATIC_INLINE void P0_0_toggle(void){
    PORT0->OMR = 0x00010001UL;
}

__STATIC_INLINE uint32_t P0_0_read(void){
    return(PORT0->IN & 0x00000001UL);
}

__STATIC_INLINE void P0_1_set_mode(uint8_t mode){
    PORT0->IOCR0 &= ~0x0000f800UL;
    PORT0->IOCR0 |= mode << 8;
}

__STATIC_INLINE void P0_1_set_driver_strength(uint8_t strength){
    PORT0->PDR0 &= ~0x00000070UL;
    PORT0->PDR0 |= strength << 4;
}

__STATIC_INLINE void P0_1_set_hwsel(uint32_t config){
    PORT0->HWSEL &= ~0x0000000cUL;
    PORT0->HWSEL |= config << 2;
}

__STATIC_INLINE void P0_1_set(void){
    PORT0->OMR = 0x00000002UL;
}

__STATIC_INLINE void P0_1_reset(void){
    PORT0->OMR = 0x00020000UL;
}

__STATIC_INLINE void P0_1_toggle(void){
    PORT0->OMR = 0x00020002UL;
}

__STATIC_INLINE uint32_t P0_1_read(void){
    return(PORT0->IN & 0x00000002UL);
}

__STATIC_INLINE void P0_2_set_mode(uint8_t mode){
    PORT0->IOCR0 &= ~0x00f80000UL;
    PORT0->IOCR0 |= mode << 16;
}

__STATIC_INLINE void P0_2_set_driver_strength(uint8_t strength){
    PORT0->PDR0 &= ~0x00000700UL;
    PORT0->PDR0 |= strength << 8;
}

__STATIC_INLINE void P0_2_set_hwsel(uint32_t config){
    PORT0->HWSEL &= ~0x00000030UL;
    PORT0->HWSEL |= config << 4;
}

__STATIC_INLINE void P0_2_set(void){
    PORT0->OMR = 0x00000004UL;
}

__STATIC_INLINE void P0_2_reset(void){
    PORT0->OMR = 0x00040000UL;
}

__STATIC_INLINE void P0_2_toggle(void){
    PORT0->OMR = 0x00040004UL;
}

__STATIC_INLINE uint32_t P0_2_read(void){
    return(PORT0->IN & 0x00000004UL);
}

__STATIC_INLINE void P0_3_set_mode(uint8_t mode){
    PORT0->IOCR0 &= ~0xf8000000UL;
    PORT0->IOCR0 |= mode << 24;
}

__STATIC_INLINE void P0_3_set_driver_strength(uint8_t strength){
    PORT0->PDR0 &= ~0x00007000UL;
    PORT0->PDR0 |= strength << 12;
}

__STATIC_INLINE void P0_3_set_hwsel(uint32_t config){
    PORT0->HWSEL &= ~0x000000c0UL;
    PORT0->HWSEL |= config << 6;
}

__STATIC_INLINE void P0_3_set(void){
    PORT0->OMR = 0x00000008UL;
}

__STATIC_INLINE void P0_3_reset(void){
    PORT0->OMR = 0x00080000UL;
}

__STATIC_INLINE void P0_3_toggle(void){
    PORT0->OMR = 0x00080008UL;
}

__STATIC_INLINE uint32_t P0_3_read(void){
    return(PORT0->IN & 0x00000008UL);
}

__STATIC_INLINE void P0_4_set_mode(uint8_t mode){
    PORT0->IOCR4 &= ~0x000000f8UL;
    PORT0->IOCR4 |= mode << 0;
}

__STATIC_INLINE void P0_4_set_driver_strength(uint8_t strength){
    PORT0->PDR0 &= ~0x00070000UL;
    PORT0->PDR0 |= strength << 16;
}

__STATIC_INLINE void P0_4_set_hwsel(uint32_t config){
    PORT0->HWSEL &= ~0x00000300UL;
    PORT0->HWSEL |= config << 8;
}

__STATIC_INLINE void P0_4_set(void){
    PORT0->OMR = 0x00000010UL;
}

__STATIC_INLINE void P0_4_reset(void){
    PORT0->OMR = 0x00100000UL;
}

__STATIC_INLINE void P0_4_toggle(void){
    PORT0->OMR = 0x00100010UL;
}

__STATIC_INLINE uint32_t P0_4_read(void){
    return(PORT0->IN & 0x00000010UL);
}

__STATIC_INLINE void P0_5_set_mode(uint8_t mode){
    PORT0->IOCR4 &= ~0x0000f800UL;
    PORT0->IOCR4 |= mode << 8;
}

__STATIC_INLINE void P0_5_set_driver_strength(uint8_t strength){
    PORT0->PDR0 &= ~0x00700000UL;
    PORT0->PDR0 |= strength << 20;
}

__STATIC_INLINE void P0_5_set_hwsel(uint32_t config){
    PORT0->HWSEL &= ~0x00000c00UL;
    PORT0->HWSEL |= config << 10;
}

__STATIC_INLINE void P0_5_set(void){
    PORT0->OMR = 0x00000020UL;
}

__STATIC_INLINE void P0_5_reset(void){
    PORT0->OMR = 0x00200000UL;
}

__STATIC_INLINE void P0_5_toggle(void){
    PORT0->OMR = 0x00200020UL;
}

__STATIC_INLINE uint32_t P0_5_read(void){
    return(PORT0->IN & 0x00000020UL);
}

__STATIC_INLINE void P0_6_set_mode(uint8_t mode){
    PORT0->IOCR4 &= ~0x00f80000UL;
    PORT0->IOCR4 |= mode << 16;
}

__STATIC_INLINE void P0_6_set_driver_strength(uint8_t strength){
    PORT0->PDR0 &= ~0x07000000UL;
    PORT0->PDR0 |= strength << 24;
}

__STATIC_INLINE void P0_6_set_hwsel(uint32_t config){
    PORT0->HWSEL &= ~0x00003000UL;
    PORT0->HWSEL |= config << 12;
}

__STATIC_INLINE void P0_6_set(void){
    PORT0->OMR = 0x00000040UL;
}

__STATIC_INLINE void P0_6_reset(void){
    PORT0->OMR = 0x00400000UL;
}

__STATIC_INLINE void P0_6_toggle(void){
    PORT0->OMR = 0x00400040UL;
}

__STATIC_INLINE uint32_t P0_6_read(void){
    return(PORT0->IN & 0x00000040UL);
}

__STATIC_INLINE void P0_7_set_mode(uint8_t mode){
    PORT0->IOCR4 &= ~0xf8000000UL;
    PORT0->IOCR4 |= mode << 24;
}

__STATIC_INLINE void P0_7_set_driver_strength(uint8_t strength){
    PORT0->PDR0 &= ~0x70000000UL;
    PORT0->PDR0 |= strength << 28;
}

__STATIC_INLINE void P0_7_set_hwsel(uint32_t config){
    PORT0->HWSEL &= ~0x0000c000UL;
    PORT0->HWSEL |= config << 14;
}

__STATIC_INLINE void P0_7_set(void){
    PORT0->OMR = 0x00000080UL;
}

__STATIC_INLINE void P0_7_reset(void){
    PORT0->OMR = 0x00800000UL;
}

__STATIC_INLINE void P0_7_toggle(void){
    PORT0->OMR = 0x00800080UL;
}

__STATIC_INLINE uint32_t P0_7_read(void){
    return(PORT0->IN & 0x00000080UL);
}

__STATIC_INLINE void P0_8_set_mode(uint8_t mode){
    PORT0->IOCR8 &= ~0x000000f8UL;
    PORT0->IOCR8 |= mode << 0;
}

__STATIC_INLINE void P0_8_set_driver_strength(uint8_t strength){
    PORT0->PDR1 &= ~0x00000007UL;
    PORT0->PDR1 |= strength << 0;
}

__STATIC_INLINE void P0_8_set_hwsel(uint32_t config){
    PORT0->HWSEL &= ~0x00030000UL;
    PORT0->HWSEL |= config << 16;
}

__STATIC_INLINE void P0_8_set(void){
    PORT0->OMR = 0x00000100UL;
}

__STATIC_INLINE void P0_8_reset(void){
    PORT0->OMR = 0x01000000UL;
}

__STATIC_INLINE void P0_8_toggle(void){
    PORT0->OMR = 0x01000100UL;
}

__STATIC_INLINE uint32_t P0_8_read(void){
    return(PORT0->IN & 0x00000100UL);
}

__STATIC_INLINE void P0_9_set_mode(uint8_t mode){
    PORT0->IOCR8 &= ~0x0000f800UL;
    PORT0->IOCR8 |= mode << 8;
}

__STATIC_INLINE void P0_9_set_driver_strength(uint8_t strength){
    PORT0->PDR1 &= ~0x00000070UL;
    PORT0->PDR1 |= strength << 4;
}

__STATIC_INLINE void P0_9_set_hwsel(uint32_t config){
    PORT0->HWSEL &= ~0x000c0000UL;
    PORT0->HWSEL |= config << 18;
}

__STATIC_INLINE void P0_9_set(void){
    PORT0->OMR = 0x00000200UL;
}

__STATIC_INLINE void P0_9_reset(void){
    PORT0->OMR = 0x02000000UL;
}

__STATIC_INLINE void P0_9_toggle(void){
    PORT0->OMR = 0x02000200UL;
}

__STATIC_INLINE uint32_t P0_9_read(void){
    return(PORT0->IN & 0x00000200UL);
}

__STATIC_INLINE void P0_10_set_mode(uint8_t mode){
    PORT0->IOCR8 &= ~0x00f80000UL;
    PORT0->IOCR8 |= mode << 16;
}

__STATIC_INLINE void P0_10_set_driver_strength(uint8_t strength){
    PORT0->PDR1 &= ~0x00000700UL;
    PORT0->PDR1 |= strength << 8;
}

__STATIC_INLINE void P0_10_set_hwsel(uint32_t config){
    PORT0->HWSEL &= ~0x00300000UL;
    PORT0->HWSEL |= config << 20;
}

__STATIC_INLINE void P0_10_set(void){
    PORT0->OMR = 0x00000400UL;
}

__STATIC_INLINE void P0_10_reset(void){
    PORT0->OMR = 0x04000000UL;
}

__STATIC_INLINE void P0_10_toggle(void){
    PORT0->OMR = 0x04000400UL;
}

__STATIC_INLINE uint32_t P0_10_read(void){
    return(PORT0->IN & 0x00000400UL);
}

__STATIC_INLINE void P0_11_set_mode(uint8_t mode){
    PORT0->IOCR8 &= ~0xf8000000UL;
    PORT0->IOCR8 |= mode << 24;
}

__STATIC_INLINE void P0_11_set_driver_strength(uint8_t strength){
    PORT0->PDR1 &= ~0x00007000UL;
    PORT0->PDR1 |= strength << 12;
}

__STATIC_INLINE void P0_11_set_hwsel(uint32_t config){
    PORT0->HWSEL &= ~0x00c00000UL;
    PORT0->HWSEL |= config << 22;
}

__STATIC_INLINE void P0_11_set(void){
    PORT0->OMR = 0x00000800UL;
}

__STATIC_INLINE void P0_11_reset(void){
    PORT0->OMR = 0x08000000UL;
}

__STATIC_INLINE void P0_11_toggle(void){
    PORT0->OMR = 0x08000800UL;
}

__STATIC_INLINE uint32_t P0_11_read(void){
    return(PORT0->IN & 0x00000800UL);
}

__STATIC_INLINE void P0_12_set_mode(uint8_t mode){
    PORT0->IOCR12 &= ~0x000000f8UL;
    PORT0->IOCR12 |= mode << 0;
}

__STATIC_INLINE void P0_12_set_driver_strength(uint8_t strength){
    PORT0->PDR1 &= ~0x00070000UL;
    PORT0->PDR1 |= strength << 16;
}

__STATIC_INLINE void P0_12_set_hwsel(uint32_t config){
    PORT0->HWSEL &= ~0x03000000UL;
    PORT0->HWSEL |= config << 24;
}

__STATIC_INLINE void P0_12_set(void){
    PORT0->OMR = 0x00001000UL;
}

__STATIC_INLINE void P0_12_reset(void){
    PORT0->OMR = 0x10000000UL;
}

__STATIC_INLINE void P0_12_toggle(void){
    PORT0->OMR = 0x10001000UL;
}

__STATIC_INLINE uint32_t P0_12_read(void){
    return(PORT0->IN & 0x00001000UL);
}

__STATIC_INLINE void P0_13_set_mode(uint8_t mode){
    PORT0->IOCR12 &= ~0x0000f800UL;
    PORT0->IOCR12 |= mode << 8;
}

__STATIC_INLINE void P0_13_set_driver_strength(uint8_t strength){
    PORT0->PDR1 &= ~0x00700000UL;
    PORT0->PDR1 |= strength << 20;
}

__STATIC_INLINE void P0_13_set_hwsel(uint32_t config){
    PORT0->HWSEL &= ~0x0c000000UL;
    PORT0->HWSEL |= config << 26;
}

__STATIC_INLINE void P0_13_set(void){
    PORT0->OMR = 0x00002000UL;
}

__STATIC_INLINE void P0_13_reset(void){
    PORT0->OMR = 0x20000000UL;
}

__STATIC_INLINE void P0_13_toggle(void){
    PORT0->OMR = 0x20002000UL;
}

__STATIC_INLINE uint32_t P0_13_read(void){
    return(PORT0->IN & 0x00002000UL);
}

__STATIC_INLINE void P0_14_set_mode(uint8_t mode){
    PORT0->IOCR12 &= ~0x00f80000UL;
    PORT0->IOCR12 |= mode << 16;
}

__STATIC_INLINE void P0_14_set_driver_strength(uint8_t strength){
    PORT0->PDR1 &= ~0x07000000UL;
    PORT0->PDR1 |= strength << 24;
}

__STATIC_INLINE void P0_14_set_hwsel(uint32_t config){
    PORT0->HWSEL &= ~0x30000000UL;
    PORT0->HWSEL |= config << 28;
}

__STATIC_INLINE void P0_14_set(void){
    PORT0->OMR = 0x00004000UL;
}

__STATIC_INLINE void P0_14_reset(void){
    PORT0->OMR = 0x40000000UL;
}

__STATIC_INLINE void P0_14_toggle(void){
    PORT0->OMR = 0x40004000UL;
}

__STATIC_INLINE uint32_t P0_14_read(void){
    return(PORT0->IN & 0x00004000UL);
}

__STATIC_INLINE void P0_15_set_mode(uint8_t mode){
    PORT0->IOCR12 &= ~0xf8000000UL;
    PORT0->IOCR12 |= mode << 24;
}

__STATIC_INLINE void P0_15_set_driver_strength(uint8_t strength){
    PORT0->PDR1 &= ~0x70000000UL;
    PORT0->PDR1 |= strength << 28;
}

__STATIC_INLINE void P0_15_set_hwsel(uint32_t config){
    PORT0->HWSEL &= ~0xc0000000UL;
    PORT0->HWSEL |= config << 30;
}

__STATIC_INLINE void P0_15_set(void){
    PORT0->OMR = 0x00008000UL;
}

__STATIC_INLINE void P0_15_reset(void){
    PORT0->OMR = 0x80000000UL;
}

__STATIC_INLINE void P0_15_toggle(void){
    PORT0->OMR = 0x80008000UL;
}

__STATIC_INLINE uint32_t P0_15_read(void){
    return(PORT0->IN & 0x00008000UL);
}

__STATIC_INLINE void P1_0_set_mode(uint8_t mode){
    PORT1->IOCR0 &= ~0x000000f8UL;
    PORT1->IOCR0 |= mode << 0;
}

__STATIC_INLINE void P1_0_set_driver_strength(uint8_t strength){
    PORT1->PDR0 &= ~0x00000007UL;
    PORT1->PDR0 |= strength << 0;
}

__STATIC_INLINE void P1_0_set_hwsel(uint32_t config){
    PORT1->HWSEL &= ~0x00000003UL;
    PORT1->HWSEL |= config << 0;
}

__STATIC_INLINE void P1_0_set(void){
    PORT1->OMR = 0x00000001UL;
}

__STATIC_INLINE void P1_0_reset(void){
    PORT1->OMR = 0x00010000UL;
}

__STATIC_INLINE void P1_0_toggle(void){
    PORT1->OMR = 0x00010001UL;
}

__STATIC_INLINE uint32_t P1_0_read(void){
    return(PORT1->IN & 0x00000001UL);
}

__STATIC_INLINE void P1_1_set_mode(uint8_t mode){
    PORT1->IOCR0 &= ~0x0000f800UL;
    PORT1->IOCR0 |= mode << 8;
}

__STATIC_INLINE void P1_1_set_driver_strength(uint8_t strength){
    PORT1->PDR0 &= ~0x00000070UL;
    PORT1->PDR0 |= strength << 4;
}

__STATIC_INLINE void P1_1_set_hwsel(uint32_t config){
    PORT1->HWSEL &= ~0x0000000cUL;
    PORT1->HWSEL |= config << 2;
}

__STATIC_INLINE void P1_1_set(void){
    PORT1->OMR = 0x00000002UL;
}

__STATIC_INLINE void P1_1_reset(void){
    PORT1->OMR = 0x00020000UL;
}

__STATIC_INLINE void P1_1_toggle(void){
    PORT1->OMR = 0x00020002UL;
}

__STATIC_INLINE uint32_t P1_1_read(void){
    return(PORT1->IN & 0x00000002UL);
}

__STATIC_INLINE void P1_2_set_mode(uint8_t mode){
    PORT1->IOCR0 &= ~0x00f80000UL;
    PORT1->IOCR0 |= mode << 16;
}

__STATIC_INLINE void P1_2_set_driver_strength(uint8_t strength){
    PORT1->PDR0 &= ~0x00000700UL;
    PORT1->PDR0 |= strength << 8;
}

__STATIC_INLINE void P1_2_set_hwsel(uint32_t config){
    PORT1->HWSEL &= ~0x00000030UL;
    PORT1->HWSEL |= config << 4;
}

__STATIC_INLINE void P1_2_set(void){
    PORT1->OMR = 0x00000004UL;
}

__STATIC_INLINE void P1_2_reset(void){
    PORT1->OMR = 0x00040000UL;
}

__STATIC_INLINE void P1_2_toggle(void){
    PORT1->OMR = 0x00040004UL;
}

__STATIC_INLINE uint32_t P1_2_read(void){
    return(PORT1->IN & 0x00000004UL);
}

__STATIC_INLINE void P1_3_set_mode(uint8_t mode){
    PORT1->IOCR0 &= ~0xf8000000UL;
    PORT1->IOCR0 |= mode << 24;
}

__STATIC_INLINE void P1_3_set_driver_strength(uint8_t strength){
    PORT1->PDR0 &= ~0x00007000UL;
    PORT1->PDR0 |= strength << 12;
}

__STATIC_INLINE void P1_3_set_hwsel(uint32_t config){
    PORT1->HWSEL &= ~0x000000c0UL;
    PORT1->HWSEL |= config << 6;
}

__STATIC_INLINE void P1_3_set(void){
    PORT1->OMR = 0x00000008UL;
}

__STATIC_INLINE void P1_3_reset(void){
    PORT1->OMR = 0x00080000UL;
}

__STATIC_INLINE void P1_3_toggle(void){
    PORT1->OMR = 0x00080008UL;
}

__STATIC_INLINE uint32_t P1_3_read(void){
    return(PORT1->IN & 0x00000008UL);
}

__STATIC_INLINE void P1_4_set_mode(uint8_t mode){
    PORT1->IOCR4 &= ~0x000000f8UL;
    PORT1->IOCR4 |= mode << 0;
}

__STATIC_INLINE void P1_4_set_driver_strength(uint8_t strength){
    PORT1->PDR0 &= ~0x00070000UL;
    PORT1->PDR0 |= strength << 16;
}

__STATIC_INLINE void P1_4_set_hwsel(uint32_t config){
    PORT1->HWSEL &= ~0x00000300UL;
    PORT1->HWSEL |= config << 8;
}

__STATIC_INLINE void P1_4_set(void){
    PORT1->OMR = 0x00000010UL;
}

__STATIC_INLINE void P1_4_reset(void){
    PORT1->OMR = 0x00100000UL;
}

__STATIC_INLINE void P1_4_toggle(void){
    PORT1->OMR = 0x00100010UL;
}

__STATIC_INLINE uint32_t P1_4_read(void){
    return(PORT1->IN & 0x00000010UL);
}

__STATIC_INLINE void P1_5_set_mode(uint8_t mode){
    PORT1->IOCR4 &= ~0x0000f800UL;
    PORT1->IOCR4 |= mode << 8;
}

__STATIC_INLINE void P1_5_set_driver_strength(uint8_t strength){
    PORT1->PDR0 &= ~0x00700000UL;
    PORT1->PDR0 |= strength << 20;
}

__STATIC_INLINE void P1_5_set_hwsel(uint32_t config){
    PORT1->HWSEL &= ~0x00000c00UL;
    PORT1->HWSEL |= config << 10;
}

__STATIC_INLINE void P1_5_set(void){
    PORT1->OMR = 0x00000020UL;
}

__STATIC_INLINE void P1_5_reset(void){
    PORT1->OMR = 0x00200000UL;
}

__STATIC_INLINE void P1_5_toggle(void){
    PORT1->OMR = 0x00200020UL;
}

__STATIC_INLINE uint32_t P1_5_read(void){
    return(PORT1->IN & 0x00000020UL);
}

__STATIC_INLINE void P1_6_set_mode(uint8_t mode){
    PORT1->IOCR4 &= ~0x00f80000UL;
    PORT1->IOCR4 |= mode << 16;
}

__STATIC_INLINE void P1_6_set_driver_strength(uint8_t strength){
    PORT1->PDR0 &= ~0x07000000UL;
    PORT1->PDR0 |= strength << 24;
}

__STATIC_INLINE void P1_6_set_hwsel(uint32_t config){
    PORT1->HWSEL &= ~0x00003000UL;
    PORT1->HWSEL |= config << 12;
}

__STATIC_INLINE void P1_6_set(void){
    PORT1->OMR = 0x00000040UL;
}

__STATIC_INLINE void P1_6_reset(void){
    PORT1->OMR = 0x00400000UL;
}

__STATIC_INLINE void P1_6_toggle(void){
    PORT1->OMR = 0x00400040UL;
}

__STATIC_INLINE uint32_t P1_6_read(void){
    return(PORT1->IN & 0x00000040UL);
}

__STATIC_INLINE void P1_7_set_mode(uint8_t mode){
    PORT1->IOCR4 &= ~0xf8000000UL;
    PORT1->IOCR4 |= mode << 24;
}

__STATIC_INLINE void P1_7_set_driver_strength(uint8_t strength){
    PORT1->PDR0 &= ~0x70000000UL;
    PORT1->PDR0 |= strength << 28;
}

__STATIC_INLINE void P1_7_set_hwsel(uint32_t config){
    PORT1->HWSEL &= ~0x0000c000UL;
    PORT1->HWSEL |= config << 14;
}

__STATIC_INLINE void P1_7_set(void){
    PORT1->OMR = 0x00000080UL;
}

__STATIC_INLINE void P1_7_reset(void){
    PORT1->OMR = 0x00800000UL;
}

__STATIC_INLINE void P1_7_toggle(void){
    PORT1->OMR = 0x00800080UL;
}

__STATIC_INLINE uint32_t P1_7_read(void){
    return(PORT1->IN & 0x00000080UL);
}

__STATIC_INLINE void P1_8_set_mode(uint8_t mode){
    PORT1->IOCR8 &= ~0x000000f8UL;
    PORT1->IOCR8 |= mode << 0;
}

__STATIC_INLINE void P1_8_set_driver_strength(uint8_t strength){
    PORT1->PDR1 &= ~0x00000007UL;
    PORT1->PDR1 |= strength << 0;
}

__STATIC_INLINE void P1_8_set_hwsel(uint32_t config){
    PORT1->HWSEL &= ~0x00030000UL;
    PORT1->HWSEL |= config << 16;
}

__STATIC_INLINE void P1_8_set(void){
    PORT1->OMR = 0x00000100UL;
}

__STATIC_INLINE void P1_8_reset(void){
    PORT1->OMR = 0x01000000UL;
}

__STATIC_INLINE void P1_8_toggle(void){
    PORT1->OMR = 0x01000100UL;
}

__STATIC_INLINE uint32_t P1_8_read(void){
    return(PORT1->IN & 0x00000100UL);
}

__STATIC_INLINE void P1_9_set_mode(uint8_t mode){
    PORT1->IOCR8 &= ~0x0000f800UL;
    PORT1->IOCR8 |= mode << 8;
}

__STATIC_INLINE void P1_9_set_driver_strength(uint8_t strength){
    PORT1->PDR1 &= ~0x00000070UL;
    PORT1->PDR1 |= strength << 4;
}

__STATIC_INLINE void P1_9_set_hwsel(uint32_t config){
    PORT1->HWSEL &= ~0x000c0000UL;
    PORT1->HWSEL |= config << 18;
}

__STATIC_INLINE void P1_9_set(void){
    PORT1->OMR = 0x00000200UL;
}

__STATIC_INLINE void P1_9_reset(void){
    PORT1->OMR = 0x02000000UL;
}

__STATIC_INLINE void P1_9_toggle(void){
    PORT1->OMR = 0x02000200UL;
}

__STATIC_INLINE uint32_t P1_9_read(void){
    return(PORT1->IN & 0x00000200UL);
}

__STATIC_INLINE void P1_10_set_mode(uint8_t mode){
    PORT1->IOCR8 &= ~0x00f80000UL;
    PORT1->IOCR8 |= mode << 16;
}

__STATIC_INLINE void P1_10_set_driver_strength(uint8_t strength){
    PORT1->PDR1 &= ~0x00000700UL;
    PORT1->PDR1 |= strength << 8;
}

__STATIC_INLINE void P1_10_set_hwsel(uint32_t config){
    PORT1->HWSEL &= ~0x00300000UL;
    PORT1->HWSEL |= config << 20;
}

__STATIC_INLINE void P1_10_set(void){
    PORT1->OMR = 0x00000400UL;
}

__STATIC_INLINE void P1_10_reset(void){
    PORT1->OMR = 0x04000000UL;
}

__STATIC_INLINE void P1_10_toggle(void){
    PORT1->OMR = 0x04000400UL;
}

__STATIC_INLINE uint32_t P1_10_read(void){
    return(PORT1->IN & 0x00000400UL);
}

__STATIC_INLINE void P1_11_set_mode(uint8_t mode){
    PORT1->IOCR8 &= ~0xf8000000UL;
    PORT1->IOCR8 |= mode << 24;
}

__STATIC_INLINE void P1_11_set_driver_strength(uint8_t strength){
    PORT1->PDR1 &= ~0x00007000UL;
    PORT1->PDR1 |= strength << 12;
}

__STATIC_INLINE void P1_11_set_hwsel(uint32_t config){
    PORT1->HWSEL &= ~0x00c00000UL;
    PORT1->HWSEL |= config << 22;
}

__STATIC_INLINE void P1_11_set(void){
    PORT1->OMR = 0x00000800UL;
}

__STATIC_INLINE void P1_11_reset(void){
    PORT1->OMR = 0x08000000UL;
}

__STATIC_INLINE void P1_11_toggle(void){
    PORT1->OMR = 0x08000800UL;
}

__STATIC_INLINE uint32_t P1_11_read(void){
    return(PORT1->IN & 0x00000800UL);
}

__STATIC_INLINE void P1_12_set_mode(uint8_t mode){
    PORT1->IOCR12 &= ~0x000000f8UL;
    PORT1->IOCR12 |= mode << 0;
}

__STATIC_INLINE void P1_12_set_driver_strength(uint8_t strength){
    PORT1->PDR1 &= ~0x00070000UL;
    PORT1->PDR1 |= strength << 16;
}

__STATIC_INLINE void P1_12_set_hwsel(uint32_t config){
    PORT1->HWSEL &= ~0x03000000UL;
    PORT1->HWSEL |= config << 24;
}

__STATIC_INLINE void P1_12_set(void){
    PORT1->OMR = 0x00001000UL;
}

__STATIC_INLINE void P1_12_reset(void){
    PORT1->OMR = 0x10000000UL;
}

__STATIC_INLINE void P1_12_toggle(void){
    PORT1->OMR = 0x10001000UL;
}

__STATIC_INLINE uint32_t P1_12_read(void){
    return(PORT1->IN & 0x00001000UL);
}

__STATIC_INLINE void P1_13_set_mode(uint8_t mode){
    PORT1->IOCR12 &= ~0x0000f800UL;
    PORT1->IOCR12 |= mode << 8;
}

__STATIC_INLINE void P1_13_set_driver_strength(uint8_t strength){
    PORT1->PDR1 &= ~0x00700000UL;
    PORT1->PDR1 |= strength << 20;
}

__STATIC_INLINE void P1_13_set_hwsel(uint32_t config){
    PORT1->HWSEL &= ~0x0c000000UL;
    PORT1->HWSEL |= config << 26;
}

__STATIC_INLINE void P1_13_set(void){
    PORT1->OMR = 0x00002000UL;
}

__STATIC_INLINE void P1_13_reset(void){
    PORT1->OMR = 0x20000000UL;
}

__STATIC_INLINE void P1_13_toggle(void){
    PORT1->OMR = 0x20002000UL;
}

__STATIC_INLINE uint32_t P1_13_read(void){
    return(PORT1->IN & 0x00002000UL);
}

__STATIC_INLINE void P1_14_set_mode(uint8_t mode){
    PORT1->IOCR12 &= ~0x00f80000UL;
    PORT1->IOCR12 |= mode << 16;
}

__STATIC_INLINE void P1_14_set_driver_strength(uint8_t strength){
    PORT1->PDR1 &= ~0x07000000UL;
    PORT1->PDR1 |= strength << 24;
}

__STATIC_INLINE void P1_14_set_hwsel(uint32_t config){
    PORT1->HWSEL &= ~0x30000000UL;
    PORT1->HWSEL |= config << 28;
}

__STATIC_INLINE void P1_14_set(void){
    PORT1->OMR = 0x00004000UL;
}

__STATIC_INLINE void P1_14_reset(void){
    PORT1->OMR = 0x40000000UL;
}

__STATIC_INLINE void P1_14_toggle(void){
    PORT1->OMR = 0x40004000UL;
}

__STATIC_INLINE uint32_t P1_14_read(void){
    return(PORT1->IN & 0x00004000UL);
}

__STATIC_INLINE void P1_15_set_mode(uint8_t mode){
    PORT1->IOCR12 &= ~0xf8000000UL;
    PORT1->IOCR12 |= mode << 24;
}

__STATIC_INLINE void P1_15_set_driver_strength(uint8_t strength){
    PORT1->PDR1 &= ~0x70000000UL;
    PORT1->PDR1 |= strength << 28;
}

__STATIC_INLINE void P1_15_set_hwsel(uint32_t config){
    PORT1->HWSEL &= ~0xc0000000UL;
    PORT1->HWSEL |= config << 30;
}

__STATIC_INLINE void P1_15_set(void){
    PORT1->OMR = 0x00008000UL;
}

__STATIC_INLINE void P1_15_reset(void){
    PORT1->OMR = 0x80000000UL;
}

__STATIC_INLINE void P1_15_toggle(void){
    PORT1->OMR = 0x80008000UL;
}

__STATIC_INLINE uint32_t P1_15_read(void){
    return(PORT1->IN & 0x00008000UL);
}

__STATIC_INLINE void P2_0_set_mode(uint8_t mode){
    PORT2->IOCR0 &= ~0x000000f8UL;
    PORT2->IOCR0 |= mode << 0;
}

__STATIC_INLINE void P2_0_set_driver_strength(uint8_t strength){
    PORT2->PDR0 &= ~0x00000007UL;
    PORT2->PDR0 |= strength << 0;
}

__STATIC_INLINE void P2_0_set_hwsel(uint32_t config){
    PORT2->HWSEL &= ~0x00000003UL;
    PORT2->HWSEL |= config << 0;
}

__STATIC_INLINE void P2_0_set(void){
    PORT2->OMR = 0x00000001UL;
}

__STATIC_INLINE void P2_0_reset(void){
    PORT2->OMR = 0x00010000UL;
}

__STATIC_INLINE void P2_0_toggle(void){
    PORT2->OMR = 0x00010001UL;
}

__STATIC_INLINE uint32_t P2_0_read(void){
    return(PORT2->IN & 0x00000001UL);
}

__STATIC_INLINE void P2_1_set_mode(uint8_t mode){
    PORT2->IOCR0 &= ~0x0000f800UL;
    PORT2->IOCR0 |= mode << 8;
}

__STATIC_INLINE void P2_1_set_driver_strength(uint8_t strength){
    PORT2->PDR0 &= ~0x00000070UL;
    PORT2->PDR0 |= strength << 4;
}

__STATIC_INLINE void P2_1_set_hwsel(uint32_t config){
    PORT2->HWSEL &= ~0x0000000cUL;
    PORT2->HWSEL |= config << 2;
}

__STATIC_INLINE void P2_1_set(void){
    PORT2->OMR = 0x00000002UL;
}

__STATIC_INLINE void P2_1_reset(void){
    PORT2->OMR = 0x00020000UL;
}

__STATIC_INLINE void P2_1_toggle(void){
    PORT2->OMR = 0x00020002UL;
}

__STATIC_INLINE uint32_t P2_1_read(void){
    return(PORT2->IN & 0x00000002UL);
}

__STATIC_INLINE void P2_2_set_mode(uint8_t mode){
    PORT2->IOCR0 &= ~0x00f80000UL;
    PORT2->IOCR0 |= mode << 16;
}

__STATIC_INLINE void P2_2_set_driver_strength(uint8_t strength){
    PORT2->PDR0 &= ~0x00000700UL;
    PORT2->PDR0 |= strength << 8;
}

__STATIC_INLINE void P2_2_set_hwsel(uint32_t config){
    PORT2->HWSEL &= ~0x00000030UL;
    PORT2->HWSEL |= config << 4;
}

__STATIC_INLINE void P2_2_set(void){
    PORT2->OMR = 0x00000004UL;
}

__STATIC_INLINE void P2_2_reset(void){
    PORT2->OMR = 0x00040000UL;
}

__STATIC_INLINE void P2_2_toggle(void){
    PORT2->OMR = 0x00040004UL;
}

__STATIC_INLINE uint32_t P2_2_read(void){
    return(PORT2->IN & 0x00000004UL);
}

__STATIC_INLINE void P2_3_set_mode(uint8_t mode){
    PORT2->IOCR0 &= ~0xf8000000UL;
    PORT2->IOCR0 |= mode << 24;
}

__STATIC_INLINE void P2_3_set_driver_strength(uint8_t strength){
    PORT2->PDR0 &= ~0x00007000UL;
    PORT2->PDR0 |= strength << 12;
}

__STATIC_INLINE void P2_3_set_hwsel(uint32_t config){
    PORT2->HWSEL &= ~0x000000c0UL;
    PORT2->HWSEL |= config << 6;
}

__STATIC_INLINE void P2_3_set(void){
    PORT2->OMR = 0x00000008UL;
}

__STATIC_INLINE void P2_3_reset(void){
    PORT2->OMR = 0x00080000UL;
}

__STATIC_INLINE void P2_3_toggle(void){
    PORT2->OMR = 0x00080008UL;
}

__STATIC_INLINE uint32_t P2_3_read(void){
    return(PORT2->IN & 0x00000008UL);
}

__STATIC_INLINE void P2_4_set_mode(uint8_t mode){
    PORT2->IOCR4 &= ~0x000000f8UL;
    PORT2->IOCR4 |= mode << 0;
}

__STATIC_INLINE void P2_4_set_driver_strength(uint8_t strength){
    PORT2->PDR0 &= ~0x00070000UL;
    PORT2->PDR0 |= strength << 16;
}

__STATIC_INLINE void P2_4_set_hwsel(uint32_t config){
    PORT2->HWSEL &= ~0x00000300UL;
    PORT2->HWSEL |= config << 8;
}

__STATIC_INLINE void P2_4_set(void){
    PORT2->OMR = 0x00000010UL;
}

__STATIC_INLINE void P2_4_reset(void){
    PORT2->OMR = 0x00100000UL;
}

__STATIC_INLINE void P2_4_toggle(void){
    PORT2->OMR = 0x00100010UL;
}

__STATIC_INLINE uint32_t P2_4_read(void){
    return(PORT2->IN & 0x00000010UL);
}

__STATIC_INLINE void P2_5_set_mode(uint8_t mode){
    PORT2->IOCR4 &= ~0x0000f800UL;
    PORT2->IOCR4 |= mode << 8;
}

__STATIC_INLINE void P2_5_set_driver_strength(uint8_t strength){
    PORT2->PDR0 &= ~0x00700000UL;
    PORT2->PDR0 |= strength << 20;
}

__STATIC_INLINE void P2_5_set_hwsel(uint32_t config){
    PORT2->HWSEL &= ~0x00000c00UL;
    PORT2->HWSEL |= config << 10;
}

__STATIC_INLINE void P2_5_set(void){
    PORT2->OMR = 0x00000020UL;
}

__STATIC_INLINE void P2_5_reset(void){
    PORT2->OMR = 0x00200000UL;
}

__STATIC_INLINE void P2_5_toggle(void){
    PORT2->OMR = 0x00200020UL;
}

__STATIC_INLINE uint32_t P2_5_read(void){
    return(PORT2->IN & 0x00000020UL);
}

__STATIC_INLINE void P2_6_set_mode(uint8_t mode){
    PORT2->IOCR4 &= ~0x00f80000UL;
    PORT2->IOCR4 |= mode << 16;
}

__STATIC_INLINE void P2_6_set_driver_strength(uint8_t strength){
    PORT2->PDR0 &= ~0x07000000UL;
    PORT2->PDR0 |= strength << 24;
}

__STATIC_INLINE void P2_6_set_hwsel(uint32_t config){
    PORT2->HWSEL &= ~0x00003000UL;
    PORT2->HWSEL |= config << 12;
}

__STATIC_INLINE void P2_6_set(void){
    PORT2->OMR = 0x00000040UL;
}

__STATIC_INLINE void P2_6_reset(void){
    PORT2->OMR = 0x00400000UL;
}

__STATIC_INLINE void P2_6_toggle(void){
    PORT2->OMR = 0x00400040UL;
}

__STATIC_INLINE uint32_t P2_6_read(void){
    return(PORT2->IN & 0x00000040UL);
}

__STATIC_INLINE void P2_7_set_mode(uint8_t mode){
    PORT2->IOCR4 &= ~0xf8000000UL;
    PORT2->IOCR4 |= mode << 24;
}

__STATIC_INLINE void P2_7_set_driver_strength(uint8_t strength){
    PORT2->PDR0 &= ~0x70000000UL;
    PORT2->PDR0 |= strength << 28;
}

__STATIC_INLINE void P2_7_set_hwsel(uint32_t config){
    PORT2->HWSEL &= ~0x0000c000UL;
    PORT2->HWSEL |= config << 14;
}

__STATIC_INLINE void P2_7_set(void){
    PORT2->OMR = 0x00000080UL;
}

__STATIC_INLINE void P2_7_reset(void){
    PORT2->OMR = 0x00800000UL;
}

__STATIC_INLINE void P2_7_toggle(void){
    PORT2->OMR = 0x00800080UL;
}

__STATIC_INLINE uint32_t P2_7_read(void){
    return(PORT2->IN & 0x00000080UL);
}

__STATIC_INLINE void P2_8_set_mode(uint8_t mode){
    PORT2->IOCR8 &= ~0x000000f8UL;
    PORT2->IOCR8 |= mode << 0;
}

__STATIC_INLINE void P2_8_set_driver_strength(uint8_t strength){
    PORT2->PDR1 &= ~0x00000007UL;
    PORT2->PDR1 |= strength << 0;
}

__STATIC_INLINE void P2_8_set_hwsel(uint32_t config){
    PORT2->HWSEL &= ~0x00030000UL;
    PORT2->HWSEL |= config << 16;
}

__STATIC_INLINE void P2_8_set(void){
    PORT2->OMR = 0x00000100UL;
}

__STATIC_INLINE void P2_8_reset(void){
    PORT2->OMR = 0x01000000UL;
}

__STATIC_INLINE void P2_8_toggle(void){
    PORT2->OMR = 0x01000100UL;
}

__STATIC_INLINE uint32_t P2_8_read(void){
    return(PORT2->IN & 0x00000100UL);
}

__STATIC_INLINE void P2_9_set_mode(uint8_t mode){
    PORT2->IOCR8 &= ~0x0000f800UL;
    PORT2->IOCR8 |= mode << 8;
}

__STATIC_INLINE void P2_9_set_driver_strength(uint8_t strength){
    PORT2->PDR1 &= ~0x00000070UL;
    PORT2->PDR1 |= strength << 4;
}

__STATIC_INLINE void P2_9_set_hwsel(uint32_t config){
    PORT2->HWSEL &= ~0x000c0000UL;
    PORT2->HWSEL |= config << 18;
}

__STATIC_INLINE void P2_9_set(void){
    PORT2->OMR = 0x00000200UL;
}

__STATIC_INLINE void P2_9_reset(void){
    PORT2->OMR = 0x02000000UL;
}

__STATIC_INLINE void P2_9_toggle(void){
    PORT2->OMR = 0x02000200UL;
}

__STATIC_INLINE uint32_t P2_9_read(void){
    return(PORT2->IN & 0x00000200UL);
}

__STATIC_INLINE void P2_10_set_mode(uint8_t mode){
    PORT2->IOCR8 &= ~0x00f80000UL;
    PORT2->IOCR8 |= mode << 16;
}

__STATIC_INLINE void P2_10_set_driver_strength(uint8_t strength){
    PORT2->PDR1 &= ~0x00000700UL;
    PORT2->PDR1 |= strength << 8;
}

__STATIC_INLINE void P2_10_set_hwsel(uint32_t config){
    PORT2->HWSEL &= ~0x00300000UL;
    PORT2->HWSEL |= config << 20;
}

__STATIC_INLINE void P2_10_set(void){
    PORT2->OMR = 0x00000400UL;
}

__STATIC_INLINE void P2_10_reset(void){
    PORT2->OMR = 0x04000000UL;
}

__STATIC_INLINE void P2_10_toggle(void){
    PORT2->OMR = 0x04000400UL;
}

__STATIC_INLINE uint32_t P2_10_read(void){
    return(PORT2->IN & 0x00000400UL);
}

__STATIC_INLINE void P2_11_set_mode(uint8_t mode){
    PORT2->IOCR8 &= ~0xf8000000UL;
    PORT2->IOCR8 |= mode << 24;
}

__STATIC_INLINE void P2_11_set_driver_strength(uint8_t strength){
    PORT2->PDR1 &= ~0x00007000UL;
    PORT2->PDR1 |= strength << 12;
}

__STATIC_INLINE void P2_11_set_hwsel(uint32_t config){
    PORT2->HWSEL &= ~0x00c00000UL;
    PORT2->HWSEL |= config << 22;
}

__STATIC_INLINE void P2_11_set(void){
    PORT2->OMR = 0x00000800UL;
}

__STATIC_INLINE void P2_11_reset(void){
    PORT2->OMR = 0x08000000UL;
}

__STATIC_INLINE void P2_11_toggle(void){
    PORT2->OMR = 0x08000800UL;
}

__STATIC_INLINE uint32_t P2_11_read(void){
    return(PORT2->IN & 0x00000800UL);
}

__STATIC_INLINE void P2_12_set_mode(uint8_t mode){
    PORT2->IOCR12 &= ~0x000000f8UL;
    PORT2->IOCR12 |= mode << 0;
}

__STATIC_INLINE void P2_12_set_driver_strength(uint8_t strength){
    PORT2->PDR1 &= ~0x00070000UL;
    PORT2->PDR1 |= strength << 16;
}

__STATIC_INLINE void P2_12_set_hwsel(uint32_t config){
    PORT2->HWSEL &= ~0x03000000UL;
    PORT2->HWSEL |= config << 24;
}

__STATIC_INLINE void P2_12_set(void){
    PORT2->OMR = 0x00001000UL;
}

__STATIC_INLINE void P2_12_reset(void){
    PORT2->OMR = 0x10000000UL;
}

__STATIC_INLINE void P2_12_toggle(void){
    PORT2->OMR = 0x10001000UL;
}

__STATIC_INLINE uint32_t P2_12_read(void){
    return(PORT2->IN & 0x00001000UL);
}

__STATIC_INLINE void P2_13_set_mode(uint8_t mode){
    PORT2->IOCR12 &= ~0x0000f800UL;
    PORT2->IOCR12 |= mode << 8;
}

__STATIC_INLINE void P2_13_set_driver_strength(uint8_t strength){
    PORT2->PDR1 &= ~0x00700000UL;
    PORT2->PDR1 |= strength << 20;
}

__STATIC_INLINE void P2_13_set_hwsel(uint32_t config){
    PORT2->HWSEL &= ~0x0c000000UL;
    PORT2->HWSEL |= config << 26;
}

__STATIC_INLINE void P2_13_set(void){
    PORT2->OMR = 0x00002000UL;
}

__STATIC_INLINE void P2_13_reset(void){
    PORT2->OMR = 0x20000000UL;
}

__STATIC_INLINE void P2_13_toggle(void){
    PORT2->OMR = 0x20002000UL;
}

__STATIC_INLINE uint32_t P2_13_read(void){
    return(PORT2->IN & 0x00002000UL);
}

__STATIC_INLINE void P2_14_set_mode(uint8_t mode){
    PORT2->IOCR12 &= ~0x00f80000UL;
    PORT2->IOCR12 |= mode << 16;
}

__STATIC_INLINE void P2_14_set_driver_strength(uint8_t strength){
    PORT2->PDR1 &= ~0x07000000UL;
    PORT2->PDR1 |= strength << 24;
}

__STATIC_INLINE void P2_14_set_hwsel(uint32_t config){
    PORT2->HWSEL &= ~0x30000000UL;
    PORT2->HWSEL |= config << 28;
}

__STATIC_INLINE void P2_14_set(void){
    PORT2->OMR = 0x00004000UL;
}

__STATIC_INLINE void P2_14_reset(void){
    PORT2->OMR = 0x40000000UL;
}

__STATIC_INLINE void P2_14_toggle(void){
    PORT2->OMR = 0x40004000UL;
}

__STATIC_INLINE uint32_t P2_14_read(void){
    return(PORT2->IN & 0x00004000UL);
}

__STATIC_INLINE void P2_15_set_mode(uint8_t mode){
    PORT2->IOCR12 &= ~0xf8000000UL;
    PORT2->IOCR12 |= mode << 24;
}

__STATIC_INLINE void P2_15_set_driver_strength(uint8_t strength){
    PORT2->PDR1 &= ~0x70000000UL;
    PORT2->PDR1 |= strength << 28;
}

__STATIC_INLINE void P2_15_set_hwsel(uint32_t config){
    PORT2->HWSEL &= ~0xc0000000UL;
    PORT2->HWSEL |= config << 30;
}

__STATIC_INLINE void P2_15_set(void){
    PORT2->OMR = 0x00008000UL;
}

__STATIC_INLINE void P2_15_reset(void){
    PORT2->OMR = 0x80000000UL;
}

__STATIC_INLINE void P2_15_toggle(void){
    PORT2->OMR = 0x80008000UL;
}

__STATIC_INLINE uint32_t P2_15_read(void){
    return(PORT2->IN & 0x00008000UL);
}

__STATIC_INLINE void P3_0_set_mode(uint8_t mode){
    PORT3->IOCR0 &= ~0x000000f8UL;
    PORT3->IOCR0 |= mode << 0;
}

__STATIC_INLINE void P3_0_set_driver_strength(uint8_t strength){
    PORT3->PDR0 &= ~0x00000007UL;
    PORT3->PDR0 |= strength << 0;
}

__STATIC_INLINE void P3_0_set_hwsel(uint32_t config){
    PORT3->HWSEL &= ~0x00000003UL;
    PORT3->HWSEL |= config << 0;
}

__STATIC_INLINE void P3_0_set(void){
    PORT3->OMR = 0x00000001UL;
}

__STATIC_INLINE void P3_0_reset(void){
    PORT3->OMR = 0x00010000UL;
}

__STATIC_INLINE void P3_0_toggle(void){
    PORT3->OMR = 0x00010001UL;
}

__STATIC_INLINE uint32_t P3_0_read(void){
    return(PORT3->IN & 0x00000001UL);
}

__STATIC_INLINE void P3_1_set_mode(uint8_t mode){
    PORT3->IOCR0 &= ~0x0000f800UL;
    PORT3->IOCR0 |= mode << 8;
}

__STATIC_INLINE void P3_1_set_driver_strength(uint8_t strength){
    PORT3->PDR0 &= ~0x00000070UL;
    PORT3->PDR0 |= strength << 4;
}

__STATIC_INLINE void P3_1_set_hwsel(uint32_t config){
    PORT3->HWSEL &= ~0x0000000cUL;
    PORT3->HWSEL |= config << 2;
}

__STATIC_INLINE void P3_1_set(void){
    PORT3->OMR = 0x00000002UL;
}

__STATIC_INLINE void P3_1_reset(void){
    PORT3->OMR = 0x00020000UL;
}

__STATIC_INLINE void P3_1_toggle(void){
    PORT3->OMR = 0x00020002UL;
}

__STATIC_INLINE uint32_t P3_1_read(void){
    return(PORT3->IN & 0x00000002UL);
}

__STATIC_INLINE void P3_2_set_mode(uint8_t mode){
    PORT3->IOCR0 &= ~0x00f80000UL;
    PORT3->IOCR0 |= mode << 16;
}

__STATIC_INLINE void P3_2_set_driver_strength(uint8_t strength){
    PORT3->PDR0 &= ~0x00000700UL;
    PORT3->PDR0 |= strength << 8;
}

__STATIC_INLINE void P3_2_set_hwsel(uint32_t config){
    PORT3->HWSEL &= ~0x00000030UL;
    PORT3->HWSEL |= config << 4;
}

__STATIC_INLINE void P3_2_set(void){
    PORT3->OMR = 0x00000004UL;
}

__STATIC_INLINE void P3_2_reset(void){
    PORT3->OMR = 0x00040000UL;
}

__STATIC_INLINE void P3_2_toggle(void){
    PORT3->OMR = 0x00040004UL;
}

__STATIC_INLINE uint32_t P3_2_read(void){
    return(PORT3->IN & 0x00000004UL);
}

__STATIC_INLINE void P3_3_set_mode(uint8_t mode){
    PORT3->IOCR0 &= ~0xf8000000UL;
    PORT3->IOCR0 |= mode << 24;
}

__STATIC_INLINE void P3_3_set_driver_strength(uint8_t strength){
    PORT3->PDR0 &= ~0x00007000UL;
    PORT3->PDR0 |= strength << 12;
}

__STATIC_INLINE void P3_3_set_hwsel(uint32_t config){
    PORT3->HWSEL &= ~0x000000c0UL;
    PORT3->HWSEL |= config << 6;
}

__STATIC_INLINE void P3_3_set(void){
    PORT3->OMR = 0x00000008UL;
}

__STATIC_INLINE void P3_3_reset(void){
    PORT3->OMR = 0x00080000UL;
}

__STATIC_INLINE void P3_3_toggle(void){
    PORT3->OMR = 0x00080008UL;
}

__STATIC_INLINE uint32_t P3_3_read(void){
    return(PORT3->IN & 0x00000008UL);
}

__STATIC_INLINE void P3_4_set_mode(uint8_t mode){
    PORT3->IOCR4 &= ~0x000000f8UL;
    PORT3->IOCR4 |= mode << 0;
}

__STATIC_INLINE void P3_4_set_driver_strength(uint8_t strength){
    PORT3->PDR0 &= ~0x00070000UL;
    PORT3->PDR0 |= strength << 16;
}

__STATIC_INLINE void P3_4_set_hwsel(uint32_t config){
    PORT3->HWSEL &= ~0x00000300UL;
    PORT3->HWSEL |= config << 8;
}

__STATIC_INLINE void P3_4_set(void){
    PORT3->OMR = 0x00000010UL;
}

__STATIC_INLINE void P3_4_reset(void){
    PORT3->OMR = 0x00100000UL;
}

__STATIC_INLINE void P3_4_toggle(void){
    PORT3->OMR = 0x00100010UL;
}

__STATIC_INLINE uint32_t P3_4_read(void){
    return(PORT3->IN & 0x00000010UL);
}

__STATIC_INLINE void P3_5_set_mode(uint8_t mode){
    PORT3->IOCR4 &= ~0x0000f800UL;
    PORT3->IOCR4 |= mode << 8;
}

__STATIC_INLINE void P3_5_set_driver_strength(uint8_t strength){
    PORT3->PDR0 &= ~0x00700000UL;
    PORT3->PDR0 |= strength << 20;
}

__STATIC_INLINE void P3_5_set_hwsel(uint32_t config){
    PORT3->HWSEL &= ~0x00000c00UL;
    PORT3->HWSEL |= config << 10;
}

__STATIC_INLINE void P3_5_set(void){
    PORT3->OMR = 0x00000020UL;
}

__STATIC_INLINE void P3_5_reset(void){
    PORT3->OMR = 0x00200000UL;
}

__STATIC_INLINE void P3_5_toggle(void){
    PORT3->OMR = 0x00200020UL;
}

__STATIC_INLINE uint32_t P3_5_read(void){
    return(PORT3->IN & 0x00000020UL);
}

__STATIC_INLINE void P3_6_set_mode(uint8_t mode){
    PORT3->IOCR4 &= ~0x00f80000UL;
    PORT3->IOCR4 |= mode << 16;
}

__STATIC_INLINE void P3_6_set_driver_strength(uint8_t strength){
    PORT3->PDR0 &= ~0x07000000UL;
    PORT3->PDR0 |= strength << 24;
}

__STATIC_INLINE void P3_6_set_hwsel(uint32_t config){
    PORT3->HWSEL &= ~0x00003000UL;
    PORT3->HWSEL |= config << 12;
}

__STATIC_INLINE void P3_6_set(void){
    PORT3->OMR = 0x00000040UL;
}

__STATIC_INLINE void P3_6_reset(void){
    PORT3->OMR = 0x00400000UL;
}

__STATIC_INLINE void P3_6_toggle(void){
    PORT3->OMR = 0x00400040UL;
}

__STATIC_INLINE uint32_t P3_6_read(void){
    return(PORT3->IN & 0x00000040UL);
}

__STATIC_INLINE void P3_7_set_mode(uint8_t mode){
    PORT3->IOCR4 &= ~0xf8000000UL;
    PORT3->IOCR4 |= mode << 24;
}

__STATIC_INLINE void P3_7_set_driver_strength(uint8_t strength){
    PORT3->PDR0 &= ~0x70000000UL;
    PORT3->PDR0 |= strength << 28;
}

__STATIC_INLINE void P3_7_set_hwsel(uint32_t config){
    PORT3->HWSEL &= ~0x0000c000UL;
    PORT3->HWSEL |= config << 14;
}

__STATIC_INLINE void P3_7_set(void){
    PORT3->OMR = 0x00000080UL;
}

__STATIC_INLINE void P3_7_reset(void){
    PORT3->OMR = 0x00800000UL;
}

__STATIC_INLINE void P3_7_toggle(void){
    PORT3->OMR = 0x00800080UL;
}

__STATIC_INLINE uint32_t P3_7_read(void){
    return(PORT3->IN & 0x00000080UL);
}

__STATIC_INLINE void P3_8_set_mode(uint8_t mode){
    PORT3->IOCR8 &= ~0x000000f8UL;
    PORT3->IOCR8 |= mode << 0;
}

__STATIC_INLINE void P3_8_set_driver_strength(uint8_t strength){
    PORT3->PDR1 &= ~0x00000007UL;
    PORT3->PDR1 |= strength << 0;
}

__STATIC_INLINE void P3_8_set_hwsel(uint32_t config){
    PORT3->HWSEL &= ~0x00030000UL;
    PORT3->HWSEL |= config << 16;
}

__STATIC_INLINE void P3_8_set(void){
    PORT3->OMR = 0x00000100UL;
}

__STATIC_INLINE void P3_8_reset(void){
    PORT3->OMR = 0x01000000UL;
}

__STATIC_INLINE void P3_8_toggle(void){
    PORT3->OMR = 0x01000100UL;
}

__STATIC_INLINE uint32_t P3_8_read(void){
    return(PORT3->IN & 0x00000100UL);
}

__STATIC_INLINE void P3_9_set_mode(uint8_t mode){
    PORT3->IOCR8 &= ~0x0000f800UL;
    PORT3->IOCR8 |= mode << 8;
}

__STATIC_INLINE void P3_9_set_driver_strength(uint8_t strength){
    PORT3->PDR1 &= ~0x00000070UL;
    PORT3->PDR1 |= strength << 4;
}

__STATIC_INLINE void P3_9_set_hwsel(uint32_t config){
    PORT3->HWSEL &= ~0x000c0000UL;
    PORT3->HWSEL |= config << 18;
}

__STATIC_INLINE void P3_9_set(void){
    PORT3->OMR = 0x00000200UL;
}

__STATIC_INLINE void P3_9_reset(void){
    PORT3->OMR = 0x02000000UL;
}

__STATIC_INLINE void P3_9_toggle(void){
    PORT3->OMR = 0x02000200UL;
}

__STATIC_INLINE uint32_t P3_9_read(void){
    return(PORT3->IN & 0x00000200UL);
}

__STATIC_INLINE void P3_10_set_mode(uint8_t mode){
    PORT3->IOCR8 &= ~0x00f80000UL;
    PORT3->IOCR8 |= mode << 16;
}

__STATIC_INLINE void P3_10_set_driver_strength(uint8_t strength){
    PORT3->PDR1 &= ~0x00000700UL;
    PORT3->PDR1 |= strength << 8;
}

__STATIC_INLINE void P3_10_set_hwsel(uint32_t config){
    PORT3->HWSEL &= ~0x00300000UL;
    PORT3->HWSEL |= config << 20;
}

__STATIC_INLINE void P3_10_set(void){
    PORT3->OMR = 0x00000400UL;
}

__STATIC_INLINE void P3_10_reset(void){
    PORT3->OMR = 0x04000000UL;
}

__STATIC_INLINE void P3_10_toggle(void){
    PORT3->OMR = 0x04000400UL;
}

__STATIC_INLINE uint32_t P3_10_read(void){
    return(PORT3->IN & 0x00000400UL);
}

__STATIC_INLINE void P3_11_set_mode(uint8_t mode){
    PORT3->IOCR8 &= ~0xf8000000UL;
    PORT3->IOCR8 |= mode << 24;
}

__STATIC_INLINE void P3_11_set_driver_strength(uint8_t strength){
    PORT3->PDR1 &= ~0x00007000UL;
    PORT3->PDR1 |= strength << 12;
}

__STATIC_INLINE void P3_11_set_hwsel(uint32_t config){
    PORT3->HWSEL &= ~0x00c00000UL;
    PORT3->HWSEL |= config << 22;
}

__STATIC_INLINE void P3_11_set(void){
    PORT3->OMR = 0x00000800UL;
}

__STATIC_INLINE void P3_11_reset(void){
    PORT3->OMR = 0x08000000UL;
}

__STATIC_INLINE void P3_11_toggle(void){
    PORT3->OMR = 0x08000800UL;
}

__STATIC_INLINE uint32_t P3_11_read(void){
    return(PORT3->IN & 0x00000800UL);
}

__STATIC_INLINE void P3_12_set_mode(uint8_t mode){
    PORT3->IOCR12 &= ~0x000000f8UL;
    PORT3->IOCR12 |= mode << 0;
}

__STATIC_INLINE void P3_12_set_driver_strength(uint8_t strength){
    PORT3->PDR1 &= ~0x00070000UL;
    PORT3->PDR1 |= strength << 16;
}

__STATIC_INLINE void P3_12_set_hwsel(uint32_t config){
    PORT3->HWSEL &= ~0x03000000UL;
    PORT3->HWSEL |= config << 24;
}

__STATIC_INLINE void P3_12_set(void){
    PORT3->OMR = 0x00001000UL;
}

__STATIC_INLINE void P3_12_reset(void){
    PORT3->OMR = 0x10000000UL;
}

__STATIC_INLINE void P3_12_toggle(void){
    PORT3->OMR = 0x10001000UL;
}

__STATIC_INLINE uint32_t P3_12_read(void){
    return(PORT3->IN & 0x00001000UL);
}

__STATIC_INLINE void P3_13_set_mode(uint8_t mode){
    PORT3->IOCR12 &= ~0x0000f800UL;
    PORT3->IOCR12 |= mode << 8;
}

__STATIC_INLINE void P3_13_set_driver_strength(uint8_t strength){
    PORT3->PDR1 &= ~0x00700000UL;
    PORT3->PDR1 |= strength << 20;
}

__STATIC_INLINE void P3_13_set_hwsel(uint32_t config){
    PORT3->HWSEL &= ~0x0c000000UL;
    PORT3->HWSEL |= config << 26;
}

__STATIC_INLINE void P3_13_set(void){
    PORT3->OMR = 0x00002000UL;
}

__STATIC_INLINE void P3_13_reset(void){
    PORT3->OMR = 0x20000000UL;
}

__STATIC_INLINE void P3_13_toggle(void){
    PORT3->OMR = 0x20002000UL;
}

__STATIC_INLINE uint32_t P3_13_read(void){
    return(PORT3->IN & 0x00002000UL);
}

__STATIC_INLINE void P3_14_set_mode(uint8_t mode){
    PORT3->IOCR12 &= ~0x00f80000UL;
    PORT3->IOCR12 |= mode << 16;
}

__STATIC_INLINE void P3_14_set_driver_strength(uint8_t strength){
    PORT3->PDR1 &= ~0x07000000UL;
    PORT3->PDR1 |= strength << 24;
}

__STATIC_INLINE void P3_14_set_hwsel(uint32_t config){
    PORT3->HWSEL &= ~0x30000000UL;
    PORT3->HWSEL |= config << 28;
}

__STATIC_INLINE void P3_14_set(void){
    PORT3->OMR = 0x00004000UL;
}

__STATIC_INLINE void P3_14_reset(void){
    PORT3->OMR = 0x40000000UL;
}

__STATIC_INLINE void P3_14_toggle(void){
    PORT3->OMR = 0x40004000UL;
}

__STATIC_INLINE uint32_t P3_14_read(void){
    return(PORT3->IN & 0x00004000UL);
}

__STATIC_INLINE void P3_15_set_mode(uint8_t mode){
    PORT3->IOCR12 &= ~0xf8000000UL;
    PORT3->IOCR12 |= mode << 24;
}

__STATIC_INLINE void P3_15_set_driver_strength(uint8_t strength){
    PORT3->PDR1 &= ~0x70000000UL;
    PORT3->PDR1 |= strength << 28;
}

__STATIC_INLINE void P3_15_set_hwsel(uint32_t config){
    PORT3->HWSEL &= ~0xc0000000UL;
    PORT3->HWSEL |= config << 30;
}

__STATIC_INLINE void P3_15_set(void){
    PORT3->OMR = 0x00008000UL;
}

__STATIC_INLINE void P3_15_reset(void){
    PORT3->OMR = 0x80000000UL;
}

__STATIC_INLINE void P3_15_toggle(void){
    PORT3->OMR = 0x80008000UL;
}

__STATIC_INLINE uint32_t P3_15_read(void){
    return(PORT3->IN & 0x00008000UL);
}

__STATIC_INLINE void P4_0_set_mode(uint8_t mode){
    PORT4->IOCR0 &= ~0x000000f8UL;
    PORT4->IOCR0 |= mode << 0;
}

__STATIC_INLINE void P4_0_set_driver_strength(uint8_t strength){
    PORT4->PDR0 &= ~0x00000007UL;
    PORT4->PDR0 |= strength << 0;
}

__STATIC_INLINE void P4_0_set_hwsel(uint32_t config){
    PORT4->HWSEL &= ~0x00000003UL;
    PORT4->HWSEL |= config << 0;
}

__STATIC_INLINE void P4_0_set(void){
    PORT4->OMR = 0x00000001UL;
}

__STATIC_INLINE void P4_0_reset(void){
    PORT4->OMR = 0x00010000UL;
}

__STATIC_INLINE void P4_0_toggle(void){
    PORT4->OMR = 0x00010001UL;
}

__STATIC_INLINE uint32_t P4_0_read(void){
    return(PORT4->IN & 0x00000001UL);
}

__STATIC_INLINE void P4_1_set_mode(uint8_t mode){
    PORT4->IOCR0 &= ~0x0000f800UL;
    PORT4->IOCR0 |= mode << 8;
}

__STATIC_INLINE void P4_1_set_driver_strength(uint8_t strength){
    PORT4->PDR0 &= ~0x00000070UL;
    PORT4->PDR0 |= strength << 4;
}

__STATIC_INLINE void P4_1_set_hwsel(uint32_t config){
    PORT4->HWSEL &= ~0x0000000cUL;
    PORT4->HWSEL |= config << 2;
}

__STATIC_INLINE void P4_1_set(void){
    PORT4->OMR = 0x00000002UL;
}

__STATIC_INLINE void P4_1_reset(void){
    PORT4->OMR = 0x00020000UL;
}

__STATIC_INLINE void P4_1_toggle(void){
    PORT4->OMR = 0x00020002UL;
}

__STATIC_INLINE uint32_t P4_1_read(void){
    return(PORT4->IN & 0x00000002UL);
}

__STATIC_INLINE void P4_2_set_mode(uint8_t mode){
    PORT4->IOCR0 &= ~0x00f80000UL;
    PORT4->IOCR0 |= mode << 16;
}

__STATIC_INLINE void P4_2_set_driver_strength(uint8_t strength){
    PORT4->PDR0 &= ~0x00000700UL;
    PORT4->PDR0 |= strength << 8;
}

__STATIC_INLINE void P4_2_set_hwsel(uint32_t config){
    PORT4->HWSEL &= ~0x00000030UL;
    PORT4->HWSEL |= config << 4;
}

__STATIC_INLINE void P4_2_set(void){
    PORT4->OMR = 0x00000004UL;
}

__STATIC_INLINE void P4_2_reset(void){
    PORT4->OMR = 0x00040000UL;
}

__STATIC_INLINE void P4_2_toggle(void){
    PORT4->OMR = 0x00040004UL;
}

__STATIC_INLINE uint32_t P4_2_read(void){
    return(PORT4->IN & 0x00000004UL);
}

__STATIC_INLINE void P4_3_set_mode(uint8_t mode){
    PORT4->IOCR0 &= ~0xf8000000UL;
    PORT4->IOCR0 |= mode << 24;
}

__STATIC_INLINE void P4_3_set_driver_strength(uint8_t strength){
    PORT4->PDR0 &= ~0x00007000UL;
    PORT4->PDR0 |= strength << 12;
}

__STATIC_INLINE void P4_3_set_hwsel(uint32_t config){
    PORT4->HWSEL &= ~0x000000c0UL;
    PORT4->HWSEL |= config << 6;
}

__STATIC_INLINE void P4_3_set(void){
    PORT4->OMR = 0x00000008UL;
}

__STATIC_INLINE void P4_3_reset(void){
    PORT4->OMR = 0x00080000UL;
}

__STATIC_INLINE void P4_3_toggle(void){
    PORT4->OMR = 0x00080008UL;
}

__STATIC_INLINE uint32_t P4_3_read(void){
    return(PORT4->IN & 0x00000008UL);
}

__STATIC_INLINE void P4_4_set_mode(uint8_t mode){
    PORT4->IOCR4 &= ~0x000000f8UL;
    PORT4->IOCR4 |= mode << 0;
}

__STATIC_INLINE void P4_4_set_driver_strength(uint8_t strength){
    PORT4->PDR0 &= ~0x00070000UL;
    PORT4->PDR0 |= strength << 16;
}

__STATIC_INLINE void P4_4_set_hwsel(uint32_t config){
    PORT4->HWSEL &= ~0x00000300UL;
    PORT4->HWSEL |= config << 8;
}

__STATIC_INLINE void P4_4_set(void){
    PORT4->OMR = 0x00000010UL;
}

__STATIC_INLINE void P4_4_reset(void){
    PORT4->OMR = 0x00100000UL;
}

__STATIC_INLINE void P4_4_toggle(void){
    PORT4->OMR = 0x00100010UL;
}

__STATIC_INLINE uint32_t P4_4_read(void){
    return(PORT4->IN & 0x00000010UL);
}

__STATIC_INLINE void P4_5_set_mode(uint8_t mode){
    PORT4->IOCR4 &= ~0x0000f800UL;
    PORT4->IOCR4 |= mode << 8;
}

__STATIC_INLINE void P4_5_set_driver_strength(uint8_t strength){
    PORT4->PDR0 &= ~0x00700000UL;
    PORT4->PDR0 |= strength << 20;
}

__STATIC_INLINE void P4_5_set_hwsel(uint32_t config){
    PORT4->HWSEL &= ~0x00000c00UL;
    PORT4->HWSEL |= config << 10;
}

__STATIC_INLINE void P4_5_set(void){
    PORT4->OMR = 0x00000020UL;
}

__STATIC_INLINE void P4_5_reset(void){
    PORT4->OMR = 0x00200000UL;
}

__STATIC_INLINE void P4_5_toggle(void){
    PORT4->OMR = 0x00200020UL;
}

__STATIC_INLINE uint32_t P4_5_read(void){
    return(PORT4->IN & 0x00000020UL);
}

__STATIC_INLINE void P4_6_set_mode(uint8_t mode){
    PORT4->IOCR4 &= ~0x00f80000UL;
    PORT4->IOCR4 |= mode << 16;
}

__STATIC_INLINE void P4_6_set_driver_strength(uint8_t strength){
    PORT4->PDR0 &= ~0x07000000UL;
    PORT4->PDR0 |= strength << 24;
}

__STATIC_INLINE void P4_6_set_hwsel(uint32_t config){
    PORT4->HWSEL &= ~0x00003000UL;
    PORT4->HWSEL |= config << 12;
}

__STATIC_INLINE void P4_6_set(void){
    PORT4->OMR = 0x00000040UL;
}

__STATIC_INLINE void P4_6_reset(void){
    PORT4->OMR = 0x00400000UL;
}

__STATIC_INLINE void P4_6_toggle(void){
    PORT4->OMR = 0x00400040UL;
}

__STATIC_INLINE uint32_t P4_6_read(void){
    return(PORT4->IN & 0x00000040UL);
}

__STATIC_INLINE void P4_7_set_mode(uint8_t mode){
    PORT4->IOCR4 &= ~0xf8000000UL;
    PORT4->IOCR4 |= mode << 24;
}

__STATIC_INLINE void P4_7_set_driver_strength(uint8_t strength){
    PORT4->PDR0 &= ~0x70000000UL;
    PORT4->PDR0 |= strength << 28;
}

__STATIC_INLINE void P4_7_set_hwsel(uint32_t config){
    PORT4->HWSEL &= ~0x0000c000UL;
    PORT4->HWSEL |= config << 14;
}

__STATIC_INLINE void P4_7_set(void){
    PORT4->OMR = 0x00000080UL;
}

__STATIC_INLINE void P4_7_reset(void){
    PORT4->OMR = 0x00800000UL;
}

__STATIC_INLINE void P4_7_toggle(void){
    PORT4->OMR = 0x00800080UL;
}

__STATIC_INLINE uint32_t P4_7_read(void){
    return(PORT4->IN & 0x00000080UL);
}

__STATIC_INLINE void P5_0_set_mode(uint8_t mode){
    PORT5->IOCR0 &= ~0x000000f8UL;
    PORT5->IOCR0 |= mode << 0;
}

__STATIC_INLINE void P5_0_set_driver_strength(uint8_t strength){
    PORT5->PDR0 &= ~0x00000007UL;
    PORT5->PDR0 |= strength << 0;
}

__STATIC_INLINE void P5_0_set_hwsel(uint32_t config){
    PORT5->HWSEL &= ~0x00000003UL;
    PORT5->HWSEL |= config << 0;
}

__STATIC_INLINE void P5_0_set(void){
    PORT5->OMR = 0x00000001UL;
}

__STATIC_INLINE void P5_0_reset(void){
    PORT5->OMR = 0x00010000UL;
}

__STATIC_INLINE void P5_0_toggle(void){
    PORT5->OMR = 0x00010001UL;
}

__STATIC_INLINE uint32_t P5_0_read(void){
    return(PORT5->IN & 0x00000001UL);
}

__STATIC_INLINE void P5_1_set_mode(uint8_t mode){
    PORT5->IOCR0 &= ~0x0000f800UL;
    PORT5->IOCR0 |= mode << 8;
}

__STATIC_INLINE void P5_1_set_driver_strength(uint8_t strength){
    PORT5->PDR0 &= ~0x00000070UL;
    PORT5->PDR0 |= strength << 4;
}

__STATIC_INLINE void P5_1_set_hwsel(uint32_t config){
    PORT5->HWSEL &= ~0x0000000cUL;
    PORT5->HWSEL |= config << 2;
}

__STATIC_INLINE void P5_1_set(void){
    PORT5->OMR = 0x00000002UL;
}

__STATIC_INLINE void P5_1_reset(void){
    PORT5->OMR = 0x00020000UL;
}

__STATIC_INLINE void P5_1_toggle(void){
    PORT5->OMR = 0x00020002UL;
}

__STATIC_INLINE uint32_t P5_1_read(void){
    return(PORT5->IN & 0x00000002UL);
}

__STATIC_INLINE void P5_2_set_mode(uint8_t mode){
    PORT5->IOCR0 &= ~0x00f80000UL;
    PORT5->IOCR0 |= mode << 16;
}

__STATIC_INLINE void P5_2_set_driver_strength(uint8_t strength){
    PORT5->PDR0 &= ~0x00000700UL;
    PORT5->PDR0 |= strength << 8;
}

__STATIC_INLINE void P5_2_set_hwsel(uint32_t config){
    PORT5->HWSEL &= ~0x00000030UL;
    PORT5->HWSEL |= config << 4;
}

__STATIC_INLINE void P5_2_set(void){
    PORT5->OMR = 0x00000004UL;
}

__STATIC_INLINE void P5_2_reset(void){
    PORT5->OMR = 0x00040000UL;
}

__STATIC_INLINE void P5_2_toggle(void){
    PORT5->OMR = 0x00040004UL;
}

__STATIC_INLINE uint32_t P5_2_read(void){
    return(PORT5->IN & 0x00000004UL);
}

__STATIC_INLINE void P5_3_set_mode(uint8_t mode){
    PORT5->IOCR0 &= ~0xf8000000UL;
    PORT5->IOCR0 |= mode << 24;
}

__STATIC_INLINE void P5_3_set_driver_strength(uint8_t strength){
    PORT5->PDR0 &= ~0x00007000UL;
    PORT5->PDR0 |= strength << 12;
}

__STATIC_INLINE void P5_3_set_hwsel(uint32_t config){
    PORT5->HWSEL &= ~0x000000c0UL;
    PORT5->HWSEL |= config << 6;
}

__STATIC_INLINE void P5_3_set(void){
    PORT5->OMR = 0x00000008UL;
}

__STATIC_INLINE void P5_3_reset(void){
    PORT5->OMR = 0x00080000UL;
}

__STATIC_INLINE void P5_3_toggle(void){
    PORT5->OMR = 0x00080008UL;
}

__STATIC_INLINE uint32_t P5_3_read(void){
    return(PORT5->IN & 0x00000008UL);
}

__STATIC_INLINE void P5_4_set_mode(uint8_t mode){
    PORT5->IOCR4 &= ~0x000000f8UL;
    PORT5->IOCR4 |= mode << 0;
}

__STATIC_INLINE void P5_4_set_driver_strength(uint8_t strength){
    PORT5->PDR0 &= ~0x00070000UL;
    PORT5->PDR0 |= strength << 16;
}

__STATIC_INLINE void P5_4_set_hwsel(uint32_t config){
    PORT5->HWSEL &= ~0x00000300UL;
    PORT5->HWSEL |= config << 8;
}

__STATIC_INLINE void P5_4_set(void){
    PORT5->OMR = 0x00000010UL;
}

__STATIC_INLINE void P5_4_reset(void){
    PORT5->OMR = 0x00100000UL;
}

__STATIC_INLINE void P5_4_toggle(void){
    PORT5->OMR = 0x00100010UL;
}

__STATIC_INLINE uint32_t P5_4_read(void){
    return(PORT5->IN & 0x00000010UL);
}

__STATIC_INLINE void P5_5_set_mode(uint8_t mode){
    PORT5->IOCR4 &= ~0x0000f800UL;
    PORT5->IOCR4 |= mode << 8;
}

__STATIC_INLINE void P5_5_set_driver_strength(uint8_t strength){
    PORT5->PDR0 &= ~0x00700000UL;
    PORT5->PDR0 |= strength << 20;
}

__STATIC_INLINE void P5_5_set_hwsel(uint32_t config){
    PORT5->HWSEL &= ~0x00000c00UL;
    PORT5->HWSEL |= config << 10;
}

__STATIC_INLINE void P5_5_set(void){
    PORT5->OMR = 0x00000020UL;
}

__STATIC_INLINE void P5_5_reset(void){
    PORT5->OMR = 0x00200000UL;
}

__STATIC_INLINE void P5_5_toggle(void){
    PORT5->OMR = 0x00200020UL;
}

__STATIC_INLINE uint32_t P5_5_read(void){
    return(PORT5->IN & 0x00000020UL);
}

__STATIC_INLINE void P5_6_set_mode(uint8_t mode){
    PORT5->IOCR4 &= ~0x00f80000UL;
    PORT5->IOCR4 |= mode << 16;
}

__STATIC_INLINE void P5_6_set_driver_strength(uint8_t strength){
    PORT5->PDR0 &= ~0x07000000UL;
    PORT5->PDR0 |= strength << 24;
}

__STATIC_INLINE void P5_6_set_hwsel(uint32_t config){
    PORT5->HWSEL &= ~0x00003000UL;
    PORT5->HWSEL |= config << 12;
}

__STATIC_INLINE void P5_6_set(void){
    PORT5->OMR = 0x00000040UL;
}

__STATIC_INLINE void P5_6_reset(void){
    PORT5->OMR = 0x00400000UL;
}

__STATIC_INLINE void P5_6_toggle(void){
    PORT5->OMR = 0x00400040UL;
}

__STATIC_INLINE uint32_t P5_6_read(void){
    return(PORT5->IN & 0x00000040UL);
}

__STATIC_INLINE void P5_7_set_mode(uint8_t mode){
    PORT5->IOCR4 &= ~0xf8000000UL;
    PORT5->IOCR4 |= mode << 24;
}

__STATIC_INLINE void P5_7_set_driver_strength(uint8_t strength){
    PORT5->PDR0 &= ~0x70000000UL;
    PORT5->PDR0 |= strength << 28;
}

__STATIC_INLINE void P5_7_set_hwsel(uint32_t config){
    PORT5->HWSEL &= ~0x0000c000UL;
    PORT5->HWSEL |= config << 14;
}

__STATIC_INLINE void P5_7_set(void){
    PORT5->OMR = 0x00000080UL;
}

__STATIC_INLINE void P5_7_reset(void){
    PORT5->OMR = 0x00800000UL;
}

__STATIC_INLINE void P5_7_toggle(void){
    PORT5->OMR = 0x00800080UL;
}

__STATIC_INLINE uint32_t P5_7_read(void){
    return(PORT5->IN & 0x00000080UL);
}

__STATIC_INLINE void P5_8_set_mode(uint8_t mode){
    PORT5->IOCR8 &= ~0x000000f8UL;
    PORT5->IOCR8 |= mode << 0;
}

__STATIC_INLINE void P5_8_set_driver_strength(uint8_t strength){
    PORT5->PDR1 &= ~0x00000007UL;
    PORT5->PDR1 |= strength << 0;
}

__STATIC_INLINE void P5_8_set_hwsel(uint32_t config){
    PORT5->HWSEL &= ~0x00030000UL;
    PORT5->HWSEL |= config << 16;
}

__STATIC_INLINE void P5_8_set(void){
    PORT5->OMR = 0x00000100UL;
}

__STATIC_INLINE void P5_8_reset(void){
    PORT5->OMR = 0x01000000UL;
}

__STATIC_INLINE void P5_8_toggle(void){
    PORT5->OMR = 0x01000100UL;
}

__STATIC_INLINE uint32_t P5_8_read(void){
    return(PORT5->IN & 0x00000100UL);
}

__STATIC_INLINE void P5_9_set_mode(uint8_t mode){
    PORT5->IOCR8 &= ~0x0000f800UL;
    PORT5->IOCR8 |= mode << 8;
}

__STATIC_INLINE void P5_9_set_driver_strength(uint8_t strength){
    PORT5->PDR1 &= ~0x00000070UL;
    PORT5->PDR1 |= strength << 4;
}

__STATIC_INLINE void P5_9_set_hwsel(uint32_t config){
    PORT5->HWSEL &= ~0x000c0000UL;
    PORT5->HWSEL |= config << 18;
}

__STATIC_INLINE void P5_9_set(void){
    PORT5->OMR = 0x00000200UL;
}

__STATIC_INLINE void P5_9_reset(void){
    PORT5->OMR = 0x02000000UL;
}

__STATIC_INLINE void P5_9_toggle(void){
    PORT5->OMR = 0x02000200UL;
}

__STATIC_INLINE uint32_t P5_9_read(void){
    return(PORT5->IN & 0x00000200UL);
}

__STATIC_INLINE void P5_10_set_mode(uint8_t mode){
    PORT5->IOCR8 &= ~0x00f80000UL;
    PORT5->IOCR8 |= mode << 16;
}

__STATIC_INLINE void P5_10_set_driver_strength(uint8_t strength){
    PORT5->PDR1 &= ~0x00000700UL;
    PORT5->PDR1 |= strength << 8;
}

__STATIC_INLINE void P5_10_set_hwsel(uint32_t config){
    PORT5->HWSEL &= ~0x00300000UL;
    PORT5->HWSEL |= config << 20;
}

__STATIC_INLINE void P5_10_set(void){
    PORT5->OMR = 0x00000400UL;
}

__STATIC_INLINE void P5_10_reset(void){
    PORT5->OMR = 0x04000000UL;
}

__STATIC_INLINE void P5_10_toggle(void){
    PORT5->OMR = 0x04000400UL;
}

__STATIC_INLINE uint32_t P5_10_read(void){
    return(PORT5->IN & 0x00000400UL);
}

__STATIC_INLINE void P5_11_set_mode(uint8_t mode){
    PORT5->IOCR8 &= ~0xf8000000UL;
    PORT5->IOCR8 |= mode << 24;
}

__STATIC_INLINE void P5_11_set_driver_strength(uint8_t strength){
    PORT5->PDR1 &= ~0x00007000UL;
    PORT5->PDR1 |= strength << 12;
}

__STATIC_INLINE void P5_11_set_hwsel(uint32_t config){
    PORT5->HWSEL &= ~0x00c00000UL;
    PORT5->HWSEL |= config << 22;
}

__STATIC_INLINE void P5_11_set(void){
    PORT5->OMR = 0x00000800UL;
}

__STATIC_INLINE void P5_11_reset(void){
    PORT5->OMR = 0x08000000UL;
}

__STATIC_INLINE void P5_11_toggle(void){
    PORT5->OMR = 0x08000800UL;
}

__STATIC_INLINE uint32_t P5_11_read(void){
    return(PORT5->IN & 0x00000800UL);
}

__STATIC_INLINE void P6_0_set_mode(uint8_t mode){
    PORT6->IOCR0 &= ~0x000000f8UL;
    PORT6->IOCR0 |= mode << 0;
}

__STATIC_INLINE void P6_0_set_driver_strength(uint8_t strength){
    PORT6->PDR0 &= ~0x00000007UL;
    PORT6->PDR0 |= strength << 0;
}

__STATIC_INLINE void P6_0_set_hwsel(uint32_t config){
    PORT6->HWSEL &= ~0x00000003UL;
    PORT6->HWSEL |= config << 0;
}

__STATIC_INLINE void P6_0_set(void){
    PORT6->OMR = 0x00000001UL;
}

__STATIC_INLINE void P6_0_reset(void){
    PORT6->OMR = 0x00010000UL;
}

__STATIC_INLINE void P6_0_toggle(void){
    PORT6->OMR = 0x00010001UL;
}

__STATIC_INLINE uint32_t P6_0_read(void){
    return(PORT6->IN & 0x00000001UL);
}

__STATIC_INLINE void P6_1_set_mode(uint8_t mode){
    PORT6->IOCR0 &= ~0x0000f800UL;
    PORT6->IOCR0 |= mode << 8;
}

__STATIC_INLINE void P6_1_set_driver_strength(uint8_t strength){
    PORT6->PDR0 &= ~0x00000070UL;
    PORT6->PDR0 |= strength << 4;
}

__STATIC_INLINE void P6_1_set_hwsel(uint32_t config){
    PORT6->HWSEL &= ~0x0000000cUL;
    PORT6->HWSEL |= config << 2;
}

__STATIC_INLINE void P6_1_set(void){
    PORT6->OMR = 0x00000002UL;
}

__STATIC_INLINE void P6_1_reset(void){
    PORT6->OMR = 0x00020000UL;
}

__STATIC_INLINE void P6_1_toggle(void){
    PORT6->OMR = 0x00020002UL;
}

__STATIC_INLINE uint32_t P6_1_read(void){
    return(PORT6->IN & 0x00000002UL);
}

__STATIC_INLINE void P6_2_set_mode(uint8_t mode){
    PORT6->IOCR0 &= ~0x00f80000UL;
    PORT6->IOCR0 |= mode << 16;
}

__STATIC_INLINE void P6_2_set_driver_strength(uint8_t strength){
    PORT6->PDR0 &= ~0x00000700UL;
    PORT6->PDR0 |= strength << 8;
}

__STATIC_INLINE void P6_2_set_hwsel(uint32_t config){
    PORT6->HWSEL &= ~0x00000030UL;
    PORT6->HWSEL |= config << 4;
}

__STATIC_INLINE void P6_2_set(void){
    PORT6->OMR = 0x00000004UL;
}

__STATIC_INLINE void P6_2_reset(void){
    PORT6->OMR = 0x00040000UL;
}

__STATIC_INLINE void P6_2_toggle(void){
    PORT6->OMR = 0x00040004UL;
}

__STATIC_INLINE uint32_t P6_2_read(void){
    return(PORT6->IN & 0x00000004UL);
}

__STATIC_INLINE void P6_3_set_mode(uint8_t mode){
    PORT6->IOCR0 &= ~0xf8000000UL;
    PORT6->IOCR0 |= mode << 24;
}

__STATIC_INLINE void P6_3_set_driver_strength(uint8_t strength){
    PORT6->PDR0 &= ~0x00007000UL;
    PORT6->PDR0 |= strength << 12;
}

__STATIC_INLINE void P6_3_set_hwsel(uint32_t config){
    PORT6->HWSEL &= ~0x000000c0UL;
    PORT6->HWSEL |= config << 6;
}

__STATIC_INLINE void P6_3_set(void){
    PORT6->OMR = 0x00000008UL;
}

__STATIC_INLINE void P6_3_reset(void){
    PORT6->OMR = 0x00080000UL;
}

__STATIC_INLINE void P6_3_toggle(void){
    PORT6->OMR = 0x00080008UL;
}

__STATIC_INLINE uint32_t P6_3_read(void){
    return(PORT6->IN & 0x00000008UL);
}

__STATIC_INLINE void P6_4_set_mode(uint8_t mode){
    PORT6->IOCR4 &= ~0x000000f8UL;
    PORT6->IOCR4 |= mode << 0;
}

__STATIC_INLINE void P6_4_set_driver_strength(uint8_t strength){
    PORT6->PDR0 &= ~0x00070000UL;
    PORT6->PDR0 |= strength << 16;
}

__STATIC_INLINE void P6_4_set_hwsel(uint32_t config){
    PORT6->HWSEL &= ~0x00000300UL;
    PORT6->HWSEL |= config << 8;
}

__STATIC_INLINE void P6_4_set(void){
    PORT6->OMR = 0x00000010UL;
}

__STATIC_INLINE void P6_4_reset(void){
    PORT6->OMR = 0x00100000UL;
}

__STATIC_INLINE void P6_4_toggle(void){
    PORT6->OMR = 0x00100010UL;
}

__STATIC_INLINE uint32_t P6_4_read(void){
    return(PORT6->IN & 0x00000010UL);
}

__STATIC_INLINE void P6_5_set_mode(uint8_t mode){
    PORT6->IOCR4 &= ~0x0000f800UL;
    PORT6->IOCR4 |= mode << 8;
}

__STATIC_INLINE void P6_5_set_driver_strength(uint8_t strength){
    PORT6->PDR0 &= ~0x00700000UL;
    PORT6->PDR0 |= strength << 20;
}

__STATIC_INLINE void P6_5_set_hwsel(uint32_t config){
    PORT6->HWSEL &= ~0x00000c00UL;
    PORT6->HWSEL |= config << 10;
}

__STATIC_INLINE void P6_5_set(void){
    PORT6->OMR = 0x00000020UL;
}

__STATIC_INLINE void P6_5_reset(void){
    PORT6->OMR = 0x00200000UL;
}

__STATIC_INLINE void P6_5_toggle(void){
    PORT6->OMR = 0x00200020UL;
}

__STATIC_INLINE uint32_t P6_5_read(void){
    return(PORT6->IN & 0x00000020UL);
}

__STATIC_INLINE void P6_6_set_mode(uint8_t mode){
    PORT6->IOCR4 &= ~0x00f80000UL;
    PORT6->IOCR4 |= mode << 16;
}

__STATIC_INLINE void P6_6_set_driver_strength(uint8_t strength){
    PORT6->PDR0 &= ~0x07000000UL;
    PORT6->PDR0 |= strength << 24;
}

__STATIC_INLINE void P6_6_set_hwsel(uint32_t config){
    PORT6->HWSEL &= ~0x00003000UL;
    PORT6->HWSEL |= config << 12;
}

__STATIC_INLINE void P6_6_set(void){
    PORT6->OMR = 0x00000040UL;
}

__STATIC_INLINE void P6_6_reset(void){
    PORT6->OMR = 0x00400000UL;
}

__STATIC_INLINE void P6_6_toggle(void){
    PORT6->OMR = 0x00400040UL;
}

__STATIC_INLINE uint32_t P6_6_read(void){
    return(PORT6->IN & 0x00000040UL);
}

__STATIC_INLINE void P14_0_set_mode(uint8_t mode){
    PORT14->IOCR0 &= ~0x000000f8UL;
    PORT14->IOCR0 |= mode << 0;
}

__STATIC_INLINE void P14_0_enable_digital(void){
    PORT14->PDISC &= ~0x00000001UL;
}

__STATIC_INLINE void P14_0_disable_digital(void){
    PORT14->PDISC |= 0x00000001UL;
}

__STATIC_INLINE uint32_t P14_0_read(void){
    return(PORT14->IN & 0x00000001UL);
}

__STATIC_INLINE void P14_1_set_mode(uint8_t mode){
    PORT14->IOCR0 &= ~0x0000f800UL;
    PORT14->IOCR0 |= mode << 8;
}

__STATIC_INLINE void P14_1_enable_digital(void){
    PORT14->PDISC &= ~0x00000002UL;
}

__STATIC_INLINE void P14_1_disable_digital(void){
    PORT14->PDISC |= 0x00000002UL;
}

__STATIC_INLINE uint32_t P14_1_read(void){
    return(PORT14->IN & 0x00000002UL);
}

__STATIC_INLINE void P14_2_set_mode(uint8_t mode){
    PORT14->IOCR0 &= ~0x00f80000UL;
    PORT14->IOCR0 |= mode << 16;
}

__STATIC_INLINE void P14_2_enable_digital(void){
    PORT14->PDISC &= ~0x00000004UL;
}

__STATIC_INLINE void P14_2_disable_digital(void){
    PORT14->PDISC |= 0x00000004UL;
}

__STATIC_INLINE uint32_t P14_2_read(void){
    return(PORT14->IN & 0x00000004UL);
}

__STATIC_INLINE void P14_3_set_mode(uint8_t mode){
    PORT14->IOCR0 &= ~0xf8000000UL;
    PORT14->IOCR0 |= mode << 24;
}

__STATIC_INLINE void P14_3_enable_digital(void){
    PORT14->PDISC &= ~0x00000008UL;
}

__STATIC_INLINE void P14_3_disable_digital(void){
    PORT14->PDISC |= 0x00000008UL;
}

__STATIC_INLINE uint32_t P14_3_read(void){
    return(PORT14->IN & 0x00000008UL);
}

__STATIC_INLINE void P14_4_set_mode(uint8_t mode){
    PORT14->IOCR4 &= ~0x000000f8UL;
    PORT14->IOCR4 |= mode << 0;
}

__STATIC_INLINE void P14_4_enable_digital(void){
    PORT14->PDISC &= ~0x00000010UL;
}

__STATIC_INLINE void P14_4_disable_digital(void){
    PORT14->PDISC |= 0x00000010UL;
}

__STATIC_INLINE uint32_t P14_4_read(void){
    return(PORT14->IN & 0x00000010UL);
}

__STATIC_INLINE void P14_5_set_mode(uint8_t mode){
    PORT14->IOCR4 &= ~0x0000f800UL;
    PORT14->IOCR4 |= mode << 8;
}

__STATIC_INLINE void P14_5_enable_digital(void){
    PORT14->PDISC &= ~0x00000020UL;
}

__STATIC_INLINE void P14_5_disable_digital(void){
    PORT14->PDISC |= 0x00000020UL;
}

__STATIC_INLINE uint32_t P14_5_read(void){
    return(PORT14->IN & 0x00000020UL);
}

__STATIC_INLINE void P14_6_set_mode(uint8_t mode){
    PORT14->IOCR4 &= ~0x00f80000UL;
    PORT14->IOCR4 |= mode << 16;
}

__STATIC_INLINE void P14_6_enable_digital(void){
    PORT14->PDISC &= ~0x00000040UL;
}

__STATIC_INLINE void P14_6_disable_digital(void){
    PORT14->PDISC |= 0x00000040UL;
}

__STATIC_INLINE uint32_t P14_6_read(void){
    return(PORT14->IN & 0x00000040UL);
}

__STATIC_INLINE void P14_7_set_mode(uint8_t mode){
    PORT14->IOCR4 &= ~0xf8000000UL;
    PORT14->IOCR4 |= mode << 24;
}

__STATIC_INLINE void P14_7_enable_digital(void){
    PORT14->PDISC &= ~0x00000080UL;
}

__STATIC_INLINE void P14_7_disable_digital(void){
    PORT14->PDISC |= 0x00000080UL;
}

__STATIC_INLINE uint32_t P14_7_read(void){
    return(PORT14->IN & 0x00000080UL);
}

__STATIC_INLINE void P14_8_set_mode(uint8_t mode){
    PORT14->IOCR8 &= ~0x000000f8UL;
    PORT14->IOCR8 |= mode << 0;
}

__STATIC_INLINE void P14_8_enable_digital(void){
    PORT14->PDISC &= ~0x00000100UL;
}

__STATIC_INLINE void P14_8_disable_digital(void){
    PORT14->PDISC |= 0x00000100UL;
}

__STATIC_INLINE uint32_t P14_8_read(void){
    return(PORT14->IN & 0x00000100UL);
}

__STATIC_INLINE void P14_9_set_mode(uint8_t mode){
    PORT14->IOCR8 &= ~0x0000f800UL;
    PORT14->IOCR8 |= mode << 8;
}

__STATIC_INLINE void P14_9_enable_digital(void){
    PORT14->PDISC &= ~0x00000200UL;
}

__STATIC_INLINE void P14_9_disable_digital(void){
    PORT14->PDISC |= 0x00000200UL;
}

__STATIC_INLINE uint32_t P14_9_read(void){
    return(PORT14->IN & 0x00000200UL);
}

__STATIC_INLINE void P14_12_set_mode(uint8_t mode){
    PORT14->IOCR12 &= ~0x000000f8UL;
    PORT14->IOCR12 |= mode << 0;
}

__STATIC_INLINE void P14_12_enable_digital(void){
    PORT14->PDISC &= ~0x00001000UL;
}

__STATIC_INLINE void P14_12_disable_digital(void){
    PORT14->PDISC |= 0x00001000UL;
}

__STATIC_INLINE uint32_t P14_12_read(void){
    return(PORT14->IN & 0x00001000UL);
}

__STATIC_INLINE void P14_13_set_mode(uint8_t mode){
    PORT14->IOCR12 &= ~0x0000f800UL;
    PORT14->IOCR12 |= mode << 8;
}

__STATIC_INLINE void P14_13_enable_digital(void){
    PORT14->PDISC &= ~0x00002000UL;
}

__STATIC_INLINE void P14_13_disable_digital(void){
    PORT14->PDISC |= 0x00002000UL;
}

__STATIC_INLINE uint32_t P14_13_read(void){
    return(PORT14->IN & 0x00002000UL);
}

__STATIC_INLINE void P14_14_set_mode(uint8_t mode){
    PORT14->IOCR12 &= ~0x00f80000UL;
    PORT14->IOCR12 |= mode << 16;
}

__STATIC_INLINE void P14_14_enable_digital(void){
    PORT14->PDISC &= ~0x00004000UL;
}

__STATIC_INLINE void P14_14_disable_digital(void){
    PORT14->PDISC |= 0x00004000UL;
}

__STATIC_INLINE uint32_t P14_14_read(void){
    return(PORT14->IN & 0x00004000UL);
}

__STATIC_INLINE void P14_15_set_mode(uint8_t mode){
    PORT14->IOCR12 &= ~0xf8000000UL;
    PORT14->IOCR12 |= mode << 24;
}

__STATIC_INLINE void P14_15_enable_digital(void){
    PORT14->PDISC &= ~0x00008000UL;
}

__STATIC_INLINE void P14_15_disable_digital(void){
    PORT14->PDISC |= 0x00008000UL;
}

__STATIC_INLINE uint32_t P14_15_read(void){
    return(PORT14->IN & 0x00008000UL);
}

__STATIC_INLINE void P15_2_set_mode(uint8_t mode){
    PORT15->IOCR0 &= ~0x00f80000UL;
    PORT15->IOCR0 |= mode << 16;
}

__STATIC_INLINE void P15_2_enable_digital(void){
    PORT15->PDISC &= ~0x00000004UL;
}

__STATIC_INLINE void P15_2_disable_digital(void){
    PORT15->PDISC |= 0x00000004UL;
}

__STATIC_INLINE uint32_t P15_2_read(void){
    return(PORT15->IN & 0x00000004UL);
}

__STATIC_INLINE void P15_3_set_mode(uint8_t mode){
    PORT15->IOCR0 &= ~0xf8000000UL;
    PORT15->IOCR0 |= mode << 24;
}

__STATIC_INLINE void P15_3_enable_digital(void){
    PORT15->PDISC &= ~0x00000008UL;
}

__STATIC_INLINE void P15_3_disable_digital(void){
    PORT15->PDISC |= 0x00000008UL;
}

__STATIC_INLINE uint32_t P15_3_read(void){
    return(PORT15->IN & 0x00000008UL);
}

__STATIC_INLINE void P15_4_set_mode(uint8_t mode){
    PORT15->IOCR4 &= ~0x000000f8UL;
    PORT15->IOCR4 |= mode << 0;
}

__STATIC_INLINE void P15_4_enable_digital(void){
    PORT15->PDISC &= ~0x00000010UL;
}

__STATIC_INLINE void P15_4_disable_digital(void){
    PORT15->PDISC |= 0x00000010UL;
}

__STATIC_INLINE uint32_t P15_4_read(void){
    return(PORT15->IN & 0x00000010UL);
}

__STATIC_INLINE void P15_5_set_mode(uint8_t mode){
    PORT15->IOCR4 &= ~0x0000f800UL;
    PORT15->IOCR4 |= mode << 8;
}

__STATIC_INLINE void P15_5_enable_digital(void){
    PORT15->PDISC &= ~0x00000020UL;
}

__STATIC_INLINE void P15_5_disable_digital(void){
    PORT15->PDISC |= 0x00000020UL;
}

__STATIC_INLINE uint32_t P15_5_read(void){
    return(PORT15->IN & 0x00000020UL);
}

__STATIC_INLINE void P15_6_set_mode(uint8_t mode){
    PORT15->IOCR4 &= ~0x00f80000UL;
    PORT15->IOCR4 |= mode << 16;
}

__STATIC_INLINE void P15_6_enable_digital(void){
    PORT15->PDISC &= ~0x00000040UL;
}

__STATIC_INLINE void P15_6_disable_digital(void){
    PORT15->PDISC |= 0x00000040UL;
}

__STATIC_INLINE uint32_t P15_6_read(void){
    return(PORT15->IN & 0x00000040UL);
}

__STATIC_INLINE void P15_7_set_mode(uint8_t mode){
    PORT15->IOCR4 &= ~0xf8000000UL;
    PORT15->IOCR4 |= mode << 24;
}

__STATIC_INLINE void P15_7_enable_digital(void){
    PORT15->PDISC &= ~0x00000080UL;
}

__STATIC_INLINE void P15_7_disable_digital(void){
    PORT15->PDISC |= 0x00000080UL;
}

__STATIC_INLINE uint32_t P15_7_read(void){
    return(PORT15->IN & 0x00000080UL);
}

__STATIC_INLINE void P15_8_set_mode(uint8_t mode){
    PORT15->IOCR8 &= ~0x000000f8UL;
    PORT15->IOCR8 |= mode << 0;
}

__STATIC_INLINE void P15_8_enable_digital(void){
    PORT15->PDISC &= ~0x00000100UL;
}

__STATIC_INLINE void P15_8_disable_digital(void){
    PORT15->PDISC |= 0x00000100UL;
}

__STATIC_INLINE uint32_t P15_8_read(void){
    return(PORT15->IN & 0x00000100UL);
}

__STATIC_INLINE void P15_9_set_mode(uint8_t mode){
    PORT15->IOCR8 &= ~0x0000f800UL;
    PORT15->IOCR8 |= mode << 8;
}

__STATIC_INLINE void P15_9_enable_digital(void){
    PORT15->PDISC &= ~0x00000200UL;
}

__STATIC_INLINE void P15_9_disable_digital(void){
    PORT15->PDISC |= 0x00000200UL;
}

__STATIC_INLINE uint32_t P15_9_read(void){
    return(PORT15->IN & 0x00000200UL);
}

__STATIC_INLINE void P15_12_set_mode(uint8_t mode){
    PORT15->IOCR12 &= ~0x000000f8UL;
    PORT15->IOCR12 |= mode << 0;
}

__STATIC_INLINE void P15_12_enable_digital(void){
    PORT15->PDISC &= ~0x00001000UL;
}

__STATIC_INLINE void P15_12_disable_digital(void){
    PORT15->PDISC |= 0x00001000UL;
}

__STATIC_INLINE uint32_t P15_12_read(void){
    return(PORT15->IN & 0x00001000UL);
}

__STATIC_INLINE void P15_13_set_mode(uint8_t mode){
    PORT15->IOCR12 &= ~0x0000f800UL;
    PORT15->IOCR12 |= mode << 8;
}

__STATIC_INLINE void P15_13_enable_digital(void){
    PORT15->PDISC &= ~0x00002000UL;
}

__STATIC_INLINE void P15_13_disable_digital(void){
    PORT15->PDISC |= 0x00002000UL;
}

__STATIC_INLINE uint32_t P15_13_read(void){
    return(PORT15->IN & 0x00002000UL);
}

__STATIC_INLINE void P15_14_set_mode(uint8_t mode){
    PORT15->IOCR12 &= ~0x00f80000UL;
    PORT15->IOCR12 |= mode << 16;
}

__STATIC_INLINE void P15_14_enable_digital(void){
    PORT15->PDISC &= ~0x00004000UL;
}

__STATIC_INLINE void P15_14_disable_digital(void){
    PORT15->PDISC |= 0x00004000UL;
}

__STATIC_INLINE uint32_t P15_14_read(void){
    return(PORT15->IN & 0x00004000UL);
}

__STATIC_INLINE void P15_15_set_mode(uint8_t mode){
    PORT15->IOCR12 &= ~0xf8000000UL;
    PORT15->IOCR12 |= mode << 24;
}

__STATIC_INLINE void P15_15_enable_digital(void){
    PORT15->PDISC &= ~0x00008000UL;
}

__STATIC_INLINE void P15_15_disable_digital(void){
    PORT15->PDISC |= 0x00008000UL;
}

__STATIC_INLINE uint32_t P15_15_read(void){
    return(PORT15->IN & 0x00008000UL);
}

#endif
