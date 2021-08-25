/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 *
 * @file mss_hart_ints.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief MPFS local interrupt definitions
 *
 * Definitions and functions associated with local interrupts for each hart.
 *
 */
#ifndef MSS_HART_INTS_H
#define MSS_HART_INTS_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct BEU_Type_
{
    volatile uint64_t CAUSE;
    volatile uint64_t VALUE;
    volatile uint64_t ENABLE;
    volatile uint64_t PLIC_INT;
    volatile uint64_t ACCRUED;
    volatile uint64_t LOCAL_INT;
    volatile uint64_t reserved2[((0x1000U/8U) - 0x6U)];
} BEU_Type;

typedef struct BEU_Types_
{
    volatile BEU_Type regs[5];
} BEU_Types;

#define        MSS_BUS_ERROR_UNIT_H0                0x01700000UL
#define        MSS_BUS_ERROR_UNIT_H1                0x01701000UL
#define        MSS_BUS_ERROR_UNIT_H2                0x01702000UL
#define        MSS_BUS_ERROR_UNIT_H3                0x01703000UL
#define        MSS_BUS_ERROR_UNIT_H4                0x01704000UL

#define BEU    ((BEU_Types *)MSS_BUS_ERROR_UNIT_H0)

/*
 * Interrupt numbers U0
 */

#define    MAINTENANCE_E51_INT               0
#define    USOC_SMB_INTERRUPT_E51_INT        1
#define    USOC_VC_INTERRUPT_E51_INT         2
#define    G5C_MESSAGE_E51_INT               3
#define    G5C_DEVRST_E51_INT                4
#define    WDOG4_TOUT_E51_INT                5
#define    WDOG3_TOUT_E51_INT                6
#define    WDOG2_TOUT_E51_INT                7
#define    WDOG1_TOUT_E51_INT                8
#define    WDOG0_TOUT_E51_INT                9
#define    WDOG0_MVRP_E51_INT               10
#define    MMUART0_E51_INT                  11
#define    ENVM_E51_INT                     12
#define    ECC_CORRECT_E51_INT              13
#define    ECC_ERROR_E51_INT                14
#define    scb_INTERRUPT_E51_INT            15
#define    FABRIC_F2H_32_E51_INT            16
#define    FABRIC_F2H_33_E51_INT            17
#define    FABRIC_F2H_34_E51_INT            18
#define    FABRIC_F2H_35_E51_INT            19
#define    FABRIC_F2H_36_E51_INT            20
#define    FABRIC_F2H_37_E51_INT            21
#define    FABRIC_F2H_38_E51_INT            22
#define    FABRIC_F2H_39_E51_INT            23
#define    FABRIC_F2H_40_E51_INT            24
#define    FABRIC_F2H_41_E51_INT            25

#define    FABRIC_F2H_42_E51_INT            26
#define    FABRIC_F2H_43_E51_INT            27
#define    FABRIC_F2H_44_E51_INT            28
#define    FABRIC_F2H_45_E51_INT            29
#define    FABRIC_F2H_46_E51_INT            30
#define    FABRIC_F2H_47_E51_INT            31
#define    FABRIC_F2H_48_E51_INT            32
#define    FABRIC_F2H_49_E51_INT            33
#define    FABRIC_F2H_50_E51_INT            34
#define    FABRIC_F2H_51_E51_INT            35

#define    FABRIC_F2H_52_E51_INT            36
#define    FABRIC_F2H_53_E51_INT            37
#define    FABRIC_F2H_54_E51_INT            38
#define    FABRIC_F2H_55_E51_INT            39
#define    FABRIC_F2H_56_E51_INT            40
#define    FABRIC_F2H_57_E51_INT            41
#define    FABRIC_F2H_58_E51_INT            42
#define    FABRIC_F2H_59_E51_INT            43
#define    FABRIC_F2H_60_E51_INT            44
#define    FABRIC_F2H_61_E51_INT            45

#define    FABRIC_F2H_62_E51_INT            46
#define    FABRIC_F2H_63_E51_INT            47

#define    LOCAL_INT_MAX                    47U  /* Highest numbered */
#define    LOCAL_INT_UNUSED                 127U /* Signifies unused interrupt */
/*
 * Interrupts associated with
 * MAINTENANCE_E51_INT
 *
 * A group of interrupt events are grouped into a single maintenance interrupt to the E51 CPU,
 * on receiving this interrupt the E51 should read the maintenance system register to find out
 * the interrupt source. The maintenance interrupts are defined below
 */
#define MAINTENANCE_E51_pll_INT                            0
#define MAINTENANCE_E51_mpu_INT                            1
#define MAINTENANCE_E51_lp_state_enter_INT                 2
#define MAINTENANCE_E51_lp_state_exit_INT                  3
#define MAINTENANCE_E51_ff_start_INT                       4
#define MAINTENANCE_E51_ff_end_INT                         5
#define MAINTENANCE_E51_fpga_on_INT                        6
#define MAINTENANCE_E51_fpga_off_INT                       7
#define MAINTENANCE_E51_scb_error_INT                      8
#define MAINTENANCE_E51_scb_fault_INT                      9
#define MAINTENANCE_E51_mesh_error_INT                     10
#define MAINTENANCE_E51_io_bank_b2_on_INT                  12
#define MAINTENANCE_E51_io_bank_b4_on_INT                  13
#define MAINTENANCE_E51_io_bank_b5_on_INT                  14
#define MAINTENANCE_E51_io_bank_b6_on_INT                  15
#define MAINTENANCE_E51_io_bank_b2_off_INT                 16
#define MAINTENANCE_E51_io_bank_b4_off_INT                 17
#define MAINTENANCE_E51_io_bank_b5_off_INT                 18
#define MAINTENANCE_E51_io_bank_b6_off_INT                 19


/*
 * E51-0 is Maintenance Interrupt CPU needs to read status register to determine exact cause:
 * These defines added here for clarity need to replay with status register defines
 * for determining interrupt cause
 */
#ifndef FOR_CLARITY
#  define FOR_CLARITY 0
#endif

#if FOR_CLARITY
#  define     mpu_fail_plic             0
#  define     lp_state_enter_plic       1
#  define     lp_state_exit_plic        2
#  define     ff_start_plic             3
#  define     ff_end_plic               4
#  define     fpga_on_plic              5
#  define     fpga_off_plic             6
#  define     scb_error_plic            7
#  define     scb_fault_plic            8
#  define     mesh_fail_plic            9
#endif

/*
 * Interrupt numbers U54's
 */

/* U0 (first U54) and U1 connected to mac0 */
#define    MAC0_INT_U54_INT                 8    /* determine source mac using hart ID */
#define    MAC0_QUEUE1_U54_INT              7
#define    MAC0_QUEUE2_U54_INT              6
#define    MAC0_QUEUE3_U54_INT              5
#define    MAC0_EMAC_U54_INT                4
#define    MAC0_MMSL_U54_INT                3

/* U2 and U3 connected to mac1 */
#define    MAC1_INT_U54_INT                 8    /* determine source mac using hart ID */
#define    MAC1_QUEUE1_U54_INT              7
#define    MAC1_QUEUE2_U54_INT              6
#define    MAC1_QUEUE3_U54_INT              5
#define    MAC1_EMAC_U54_INT                4
#define    MAC1_MMSL_U54_INT                3

/* MMUART1 connected to U54 0 */
/* MMUART2 connected to U54 1 */
/* MMUART3 connected to U54 2 */
/* MMUART4 connected to U54 3 */
#define    MMUARTx_U54_INT                  11    /* MMUART1 connected to U54 0 */
#define    WDOGx_MVRP_U54_INT               10    /* determine source mac using hart ID */
#define    WDOGx_TOUT_U54_INT                9    /* determine source mac using hart ID */

#define    H2_FABRIC_F2H_0_U54_INT          16
#define    H2_FABRIC_F2H_1_U54_INT          17
#define    H2_FABRIC_F2H_2_U54_INT          18
#define    H2_FABRIC_F2H_3_U54_INT          19
#define    H2_FABRIC_F2H_4_U54_INT          20
#define    H2_FABRIC_F2H_5_U54_INT          21
#define    H2_FABRIC_F2H_6_U54_INT          22
#define    H2_FABRIC_F2H_7_U54_INT          23
#define    H2_FABRIC_F2H_8_U54_INT          24
#define    H2_FABRIC_F2H_9_U54_INT          25

#define    H2_FABRIC_F2H_10_U54_INT         26
#define    H2_FABRIC_F2H_11_U54_INT         27
#define    H2_FABRIC_F2H_12_U54_INT         28
#define    H2_FABRIC_F2H_13_U54_INT         29
#define    H2_FABRIC_F2H_14_U54_INT         30
#define    H2_FABRIC_F2H_15_U54_INT         31
#define    H2_FABRIC_F2H_16_U54_INT         32
#define    H2_FABRIC_F2H_17_U54_INT         33
#define    H2_FABRIC_F2H_18_U54_INT         34
#define    H2_FABRIC_F2H_19_U54_INT         35

#define    H2_FABRIC_F2H_20_U54_INT         36
#define    H2_FABRIC_F2H_21_U54_INT         37
#define    H2_FABRIC_F2H_22_U54_INT         38
#define    H2_FABRIC_F2H_23_U54_INT         39
#define    H2_FABRIC_F2H_24_U54_INT         40
#define    H2_FABRIC_F2H_25_U54_INT         41
#define    H2_FABRIC_F2H_26_U54_INT         42
#define    H2_FABRIC_F2H_27_U54_INT         43
#define    H2_FABRIC_F2H_28_U54_INT         44
#define    H2_FABRIC_F2H_29_U54_INT         45

#define    H2_FABRIC_F2H_30_U54_INT         46
#define    H2_FABRIC_F2H_31_U54_INT         47


void handle_m_ext_interrupt(void);
void Software_h0_IRQHandler(void);
void Software_h1_IRQHandler(void);
void Software_h2_IRQHandler(void);
void Software_h3_IRQHandler(void);
void Software_h4_IRQHandler(void);
void SysTick_Handler_h0_IRQHandler(void);
void SysTick_Handler_h1_IRQHandler(void);
void SysTick_Handler_h2_IRQHandler(void);
void SysTick_Handler_h3_IRQHandler(void);
void SysTick_Handler_h4_IRQHandler(void);

/*
 *
 *   Local interrupt defines
 *
 */
void maintenance_e51_local_IRQHandler_0(void);
void usoc_smb_interrupt_e51_local_IRQHandler_1(void);
void usoc_vc_interrupt_e51_local_IRQHandler_2(void);
void g5c_message_e51_local_IRQHandler_3(void);
void g5c_devrst_e51_local_IRQHandler_4(void);
void wdog4_tout_e51_local_IRQHandler_5(void);
void wdog3_tout_e51_local_IRQHandler_6(void);
void wdog2_tout_e51_local_IRQHandler_7(void);
void wdog1_tout_e51_local_IRQHandler_8(void);
void wdog0_tout_e51_local_IRQHandler_9(void);
void wdog0_mvrp_e51_local_IRQHandler_10(void);
void mmuart0_e51_local_IRQHandler_11(void);
void envm_e51_local_IRQHandler_12(void);
void ecc_correct_e51_local_IRQHandler_13(void);
void ecc_error_e51_local_IRQHandler_14(void);
void scb_interrupt_e51_local_IRQHandler_15(void);
void fabric_f2h_32_e51_local_IRQHandler_16(void);
void fabric_f2h_33_e51_local_IRQHandler_17(void);
void fabric_f2h_34_e51_local_IRQHandler_18(void);
void fabric_f2h_35_e51_local_IRQHandler_19(void);
void fabric_f2h_36_e51_local_IRQHandler_20(void);
void fabric_f2h_37_e51_local_IRQHandler_21(void);
void fabric_f2h_38_e51_local_IRQHandler_22(void);
void fabric_f2h_39_e51_local_IRQHandler_23(void);
void fabric_f2h_40_e51_local_IRQHandler_24(void);
void fabric_f2h_41_e51_local_IRQHandler_25(void);
void fabric_f2h_42_e51_local_IRQHandler_26(void);
void fabric_f2h_43_e51_local_IRQHandler_27(void);
void fabric_f2h_44_e51_local_IRQHandler_28(void);
void fabric_f2h_45_e51_local_IRQHandler_29(void);
void fabric_f2h_46_e51_local_IRQHandler_30(void);
void fabric_f2h_47_e51_local_IRQHandler_31(void);
void fabric_f2h_48_e51_local_IRQHandler_32(void);
void fabric_f2h_49_e51_local_IRQHandler_33(void);
void fabric_f2h_50_e51_local_IRQHandler_34(void);
void fabric_f2h_51_e51_local_IRQHandler_35(void);
void fabric_f2h_52_e51_local_IRQHandler_36(void);
void fabric_f2h_53_e51_local_IRQHandler_37(void);
void fabric_f2h_54_e51_local_IRQHandler_38(void);
void fabric_f2h_55_e51_local_IRQHandler_39(void);
void fabric_f2h_56_e51_local_IRQHandler_40(void);
void fabric_f2h_57_e51_local_IRQHandler_41(void);
void fabric_f2h_58_e51_local_IRQHandler_42(void);
void fabric_f2h_59_e51_local_IRQHandler_43(void);
void fabric_f2h_60_e51_local_IRQHandler_44(void);
void fabric_f2h_61_e51_local_IRQHandler_45(void);
void fabric_f2h_62_e51_local_IRQHandler_46(void);
void fabric_f2h_63_e51_local_IRQHandler_47(void);

/*
 * U54
 */
void spare_u54_local_IRQHandler_0(void);
void spare_u54_local_IRQHandler_1(void);
void spare_u54_local_IRQHandler_2(void);

void mac_mmsl_u54_1_local_IRQHandler_3(void);
void mac_emac_u54_1_local_IRQHandler_4(void);
void mac_queue3_u54_1_local_IRQHandler_5(void);
void mac_queue2_u54_1_local_IRQHandler_6(void);
void mac_queue1_u54_1_local_IRQHandler_7(void);
void mac_int_u54_1_local_IRQHandler_8(void);

void mac_mmsl_u54_2_local_IRQHandler_3(void);
void mac_emac_u54_2_local_IRQHandler_4(void);
void mac_queue3_u54_2_local_IRQHandler_5(void);
void mac_queue2_u54_2_local_IRQHandler_6(void);
void mac_queue1_u54_2_local_IRQHandler_7(void);
void mac_int_u54_2_local_IRQHandler_8(void);

void mac_mmsl_u54_3_local_IRQHandler_3(void);
void mac_emac_u54_3_local_IRQHandler_4(void);
void mac_queue3_u54_3_local_IRQHandler_5(void);
void mac_queue2_u54_3_local_IRQHandler_6(void);
void mac_queue1_u54_3_local_IRQHandler_7(void);
void mac_int_u54_3_local_IRQHandler_8(void);

void mac_mmsl_u54_4_local_IRQHandler_3(void);
void mac_emac_u54_4_local_IRQHandler_4(void);
void mac_queue3_u54_4_local_IRQHandler_5(void);
void mac_queue2_u54_4_local_IRQHandler_6(void);
void mac_queue1_u54_4_local_IRQHandler_7(void);
void mac_int_u54_4_local_IRQHandler_8(void);

void wdog_tout_u54_h1_local_IRQHandler_9(void);
void wdog_tout_u54_h2_local_IRQHandler_9(void);
void wdog_tout_u54_h3_local_IRQHandler_9(void);
void wdog_tout_u54_h4_local_IRQHandler_9(void);
void mvrp_u54_local_IRQHandler_10(void);
void mmuart_u54_h1_local_IRQHandler_11(void);
void mmuart_u54_h2_local_IRQHandler_11(void);
void mmuart_u54_h3_local_IRQHandler_11(void);
void mmuart_u54_h4_local_IRQHandler_11(void);
void spare_u54_local_IRQHandler_12(void);
void spare_u54_local_IRQHandler_13(void);
void spare_u54_local_IRQHandler_14(void);
void spare_u54_local_IRQHandler_15(void);
void fabric_f2h_0_u54_local_IRQHandler_16(void);
void fabric_f2h_1_u54_local_IRQHandler_17(void);
void fabric_f2h_2_u54_local_IRQHandler_18(void);
void fabric_f2h_3_u54_local_IRQHandler_19(void);
void fabric_f2h_4_u54_local_IRQHandler_20(void);
void fabric_f2h_5_u54_local_IRQHandler_21(void);
void fabric_f2h_6_u54_local_IRQHandler_22(void);
void fabric_f2h_7_u54_local_IRQHandler_23(void);
void fabric_f2h_8_u54_local_IRQHandler_24(void);
void fabric_f2h_9_u54_local_IRQHandler_25(void);
void fabric_f2h_10_u54_local_IRQHandler_26(void);
void fabric_f2h_11_u54_local_IRQHandler_27(void);
void fabric_f2h_12_u54_local_IRQHandler_28(void);
void fabric_f2h_13_u54_local_IRQHandler_29(void);
void fabric_f2h_14_u54_local_IRQHandler_30(void);
void fabric_f2h_15_u54_local_IRQHandler_31(void);
void fabric_f2h_16_u54_local_IRQHandler_32(void);
void fabric_f2h_17_u54_local_IRQHandler_33(void);
void fabric_f2h_18_u54_local_IRQHandler_34(void);
void fabric_f2h_19_u54_local_IRQHandler_35(void);
void fabric_f2h_20_u54_local_IRQHandler_36(void);
void fabric_f2h_21_u54_local_IRQHandler_37(void);
void fabric_f2h_22_u54_local_IRQHandler_38(void);
void fabric_f2h_23_u54_local_IRQHandler_39(void);
void fabric_f2h_24_u54_local_IRQHandler_40(void);
void fabric_f2h_25_u54_local_IRQHandler_41(void);
void fabric_f2h_26_u54_local_IRQHandler_42(void);
void fabric_f2h_27_u54_local_IRQHandler_43(void);
void fabric_f2h_28_u54_local_IRQHandler_44(void);
void fabric_f2h_29_u54_local_IRQHandler_45(void);
void fabric_f2h_30_u54_local_IRQHandler_46(void);
void fabric_f2h_31_u54_local_IRQHandler_47(void);

#ifdef __cplusplus
}
#endif

#endif  /* MSS_HART_INTS_H */
