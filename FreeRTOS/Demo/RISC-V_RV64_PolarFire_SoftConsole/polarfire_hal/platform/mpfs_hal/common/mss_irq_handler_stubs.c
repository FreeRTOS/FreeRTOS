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
 * @file mss_irq_handler_stubs.c
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief MPFS MSS Interrupt Function stubs.
 *
 * The functions below will only be linked with the application code if the user
 * does not provide an implementation for these functions. These functions are
 * defined with weak linking so that they can be overridden by a function with
 * same prototype in the user's application code.
 *
 */
#include <stdint.h>
#include "mpfs_hal/mss_hal.h"


__attribute__((weak)) void handle_m_ext_interrupt(void)
{

}

__attribute__((weak)) void Software_h0_IRQHandler(void)
{

}

__attribute__((weak)) void Software_h1_IRQHandler(void)
{

}

__attribute__((weak)) void Software_h2_IRQHandler(void)
{

}

__attribute__((weak)) void Software_h3_IRQHandler(void)
{

}

__attribute__((weak)) void Software_h4_IRQHandler(void)
{

}

__attribute__((weak)) void SysTick_Handler_h0_IRQHandler(void)
{

}

__attribute__((weak)) void SysTick_Handler_h1_IRQHandler(void)
{

}

__attribute__((weak)) void SysTick_Handler_h2_IRQHandler(void)
{

}

__attribute__((weak)) void SysTick_Handler_h3_IRQHandler(void)
{

}

__attribute__((weak)) void SysTick_Handler_h4_IRQHandler(void)
{

}

__attribute__((weak))  uint8_t Invalid_IRQHandler(void)
{
    return(0U);
}
#ifdef SIFIVE_HIFIVE_UNLEASHED
__attribute__((weak))  uint8_t External_1_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_2_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_3_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t USART0_plic_4_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_5_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_6_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_7_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_8_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_9_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_10_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_11_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_12_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_13_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_14_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_15_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_16_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_17_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_18_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_19_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_20_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_21_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_22_IRQHandler(void)
{
    return(0U);
}
#endif

__attribute__((weak))  uint8_t dma_ch0_DONE_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t dma_ch0_ERR_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t dma_ch1_DONE_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t dma_ch1_ERR_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t dma_ch2_DONE_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t dma_ch2_ERR_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t dma_ch3_DONE_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t dma_ch3_ERR_IRQHandler(void)
{
    return(0U);
}
#ifdef SIFIVE_HIFIVE_UNLEASHED
__attribute__((weak))  uint8_t External_31_IRQHandler(void)
{
    return(0U);
}


__attribute__((weak))  uint8_t External_32_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_33_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_34_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_35_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_36_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_37_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_38_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_39_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_40_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_41_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_42_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_43_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_44_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_45_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_46_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_47_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_48_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_49_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_50_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_51_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t External_52_IRQHandler(void)
{
    return(0U);
}


__attribute__((weak))  uint8_t MAC0_plic_53_IRQHandler(void)
{
    return(0U);
}
#endif

#ifndef SIFIVE_HIFIVE_UNLEASHED
__attribute__((weak))  uint8_t  l2_metadata_corr_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  l2_metadata_uncorr_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  l2_data_corr_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  l2_data_uncorr_IRQHandler(void)
{
    return(0U);
}
#endif  /* ifndef SIFIVE_HIFIVE_UNLEASHED */



#ifndef SIFIVE_HIFIVE_UNLEASHED
__attribute__((weak))  uint8_t gpio0_bit0_or_gpio2_bit13_plic_0_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t gpio0_bit1_or_gpio2_bit13_plic_1_IRQHandler(void)
        {
            return(0U);
        }

__attribute__((weak))  uint8_t  gpio0_bit2_or_gpio2_bit13_plic_2_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio0_bit3_or_gpio2_bit13_plic_3_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio0_bit4_or_gpio2_bit13_plic_4_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio0_bit5_or_gpio2_bit13_plic_5_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio0_bit6_or_gpio2_bit13_plic_6_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio0_bit7_or_gpio2_bit13_plic_7_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio0_bit8_or_gpio2_bit13_plic_8_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio0_bit9_or_gpio2_bit13_plic_9_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio0_bit10_or_gpio2_bit13_plic_10_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio0_bit11_or_gpio2_bit13_plic_11_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio0_bit12_or_gpio2_bit13_plic_12_IRQHandler(void)
{
    return(0U);
}


__attribute__((weak))  uint8_t  gpio0_bit13_or_gpio2_bit13_plic_13_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit0_or_gpio2_bit14_plic_14_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit1_or_gpio2_bit15_plic_15_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit2_or_gpio2_bit16_plic_16_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit3_or_gpio2_bit17_plic_17_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit4_or_gpio2_bit18_plic_18_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit5_or_gpio2_bit19_plic_19_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit6_or_gpio2_bit20_plic_20_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit7_or_gpio2_bit21_plic_21_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit8_or_gpio2_bit22_plic_22_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit9_or_gpio2_bit23_plic_23_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit10_or_gpio2_bit24_plic_24_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit11_or_gpio2_bit25_plic_25_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit12_or_gpio2_bit26_plic_26_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit13_or_gpio2_bit27_plic_27_IRQHandler(void)
{
    return(0U);
}


__attribute__((weak))  uint8_t  gpio1_bit14_or_gpio2_bit28_plic_28_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit15_or_gpio2_bit29_plic_29_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit16_or_gpio2_bit30_plic_30_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit17_or_gpio2_bit31_plic_31_IRQHandler(void)
{
    return(0U);
}


__attribute__((weak))  uint8_t  gpio1_bit18_plic_32_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit19_plic_33_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit20_plic_34_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit21_plic_35_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit22_plic_36_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_bit23_plic_37_IRQHandler(void)
{
    return(0U);
}


__attribute__((weak))  uint8_t  gpio0_non_direct_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio1_non_direct_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  gpio2_non_direct_plic_IRQHandler(void)
{
    return(0U);
}


__attribute__((weak))  uint8_t  spi0_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  spi1_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  external_can0_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  can1_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  External_i2c0_main_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  External_i2c0_alert_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  i2c0_sus_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  i2c1_main_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  i2c1_alert_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  i2c1_sus_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mac0_int_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mac0_queue1_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mac0_queue2_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mac0_queue3_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mac0_emac_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mac0_mmsl_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mac1_int_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mac1_queue1_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mac1_queue2_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mac1_queue3_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mac1_emac_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mac1_mmsl_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  ddrc_train_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  scb_interrupt_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  ecc_error_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  ecc_correct_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  rtc_wakeup_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  rtc_match_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  timer1_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  timer2_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  envm_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  qspi_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  usb_dma_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  usb_mc_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mmc_main_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mmc_wakeup_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mmuart0_plic_77_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mmuart1_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mmuart2_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mmuart3_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  mmuart4_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  g5c_devrst_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak))  uint8_t  g5c_message_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  usoc_vc_interrupt_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  usoc_smb_interrupt_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak)) uint8_t  e51_0_Maintence_plic_IRQHandler(void)
{
    return(0U);
}


__attribute__((weak)) uint8_t  wdog0_mvrp_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak)) uint8_t  wdog1_mvrp_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak)) uint8_t  wdog2_mvrp_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak)) uint8_t  wdog3_mvrp_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak)) uint8_t  wdog4_mvrp_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak)) uint8_t  wdog0_tout_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak)) uint8_t  wdog1_tout_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak)) uint8_t  wdog2_tout_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak)) uint8_t  wdog3_tout_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak)) uint8_t  wdog4_tout_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak)) uint8_t  g5c_mss_spi_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak)) uint8_t  volt_temp_alarm_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak))  uint8_t  athena_complete_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak))  uint8_t  athena_alarm_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak))  uint8_t  athena_bus_error_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak))  uint8_t  usoc_axic_us_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak))  uint8_t  usoc_axic_ds_plic_IRQHandler(void)
{
    return(0U);
}
__attribute__((weak))  uint8_t  reserved_104_plic_IRQHandler(void)
{
    return(0U);
}



__attribute__((weak))  uint8_t  fabric_f2h_0_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_1_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_2_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_3_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_4_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_5_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_6_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_7_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_8_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_9_plic_IRQHandler(void)
{
    return(0U);
}


__attribute__((weak))  uint8_t  fabric_f2h_10_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_11_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_12_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_13_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_14_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_15_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_16_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_17_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_18_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_19_plic_IRQHandler(void)
{
    return(0U);
}


__attribute__((weak))  uint8_t  fabric_f2h_20_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_21_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_22_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_23_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_24_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_25_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_26_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_27_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_28_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_29_plic_IRQHandler(void)
{
    return(0U);
}


__attribute__((weak))  uint8_t  fabric_f2h_30_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_31_plic_IRQHandler(void)
{
    return(0U);
}


__attribute__((weak))  uint8_t  fabric_f2h_32_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_33_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_34_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_35_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_36_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_37_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_38_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_39_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_40_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t  fabric_f2h_41_plic_IRQHandler(void)
{
    return(0U);
}


__attribute__((weak))  uint8_t fabric_f2h_42_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_43_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_44_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_45_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_46_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_47_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_48_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_49_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_50_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_51_plic_IRQHandler(void)
{
    return(0U);
}


__attribute__((weak))  uint8_t fabric_f2h_52_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_53_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_54_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_55_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_56_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_57_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_58_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_59_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_60_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_61_plic_IRQHandler(void)
{
    return(0U);
}


__attribute__((weak))  uint8_t fabric_f2h_62_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t fabric_f2h_63_plic_IRQHandler(void)
{
    return(0U);
}


__attribute__((weak))  uint8_t bus_error_unit_hart_0_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t bus_error_unit_hart_1_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t bus_error_unit_hart_2_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t bus_error_unit_hart_3_plic_IRQHandler(void)
{
    return(0U);
}

__attribute__((weak))  uint8_t bus_error_unit_hart_4_plic_IRQHandler(void)
{
    return(0U);
}


/* Local interrupt stubs */
__attribute__((weak))  void maintenance_e51_local_IRQHandler_0(void)
{
}
__attribute__((weak))  void usoc_smb_interrupt_e51_local_IRQHandler_1(void)
{
}
__attribute__((weak))  void usoc_vc_interrupt_e51_local_IRQHandler_2(void)
{
}
__attribute__((weak))  void g5c_message_e51_local_IRQHandler_3(void)
{
}
__attribute__((weak))  void g5c_devrst_e51_local_IRQHandler_4(void)
{
}
__attribute__((weak))  void wdog4_tout_e51_local_IRQHandler_5(void)
{
}
__attribute__((weak))  void wdog3_tout_e51_local_IRQHandler_6(void)
{
}
__attribute__((weak))  void wdog2_tout_e51_local_IRQHandler_7(void)
{
}
__attribute__((weak))  void wdog1_tout_e51_local_IRQHandler_8(void)
{
}
__attribute__((weak))  void wdog0_tout_e51_local_IRQHandler_9(void)
{
}
__attribute__((weak))  void wdog0_mvrp_e51_local_IRQHandler_10(void)
{
}

__attribute__((weak))  void mmuart0_e51_local_IRQHandler_11(void)
{
}

__attribute__((weak))  void envm_e51_local_IRQHandler_12(void)
{
}

__attribute__((weak))  void ecc_correct_e51_local_IRQHandler_13(void)
{
}

__attribute__((weak))  void ecc_error_e51_local_IRQHandler_14(void)
{
}

__attribute__((weak))  void scb_interrupt_e51_local_IRQHandler_15(void)
{
}

__attribute__((weak))  void fabric_f2h_32_e51_local_IRQHandler_16(void)
{
}

__attribute__((weak))  void fabric_f2h_33_e51_local_IRQHandler_17(void)
{
}

__attribute__((weak))  void fabric_f2h_34_e51_local_IRQHandler_18(void)
{
}

__attribute__((weak))  void fabric_f2h_35_e51_local_IRQHandler_19(void)
{
}

__attribute__((weak))  void fabric_f2h_36_e51_local_IRQHandler_20(void)
{
}

__attribute__((weak))  void fabric_f2h_37_e51_local_IRQHandler_21(void)
{
}

__attribute__((weak))  void fabric_f2h_38_e51_local_IRQHandler_22(void)
{
}

__attribute__((weak))  void fabric_f2h_39_e51_local_IRQHandler_23(void)
{
}

__attribute__((weak))  void fabric_f2h_40_e51_local_IRQHandler_24(void)
{
}

__attribute__((weak))  void fabric_f2h_41_e51_local_IRQHandler_25(void)
{
}

__attribute__((weak))  void fabric_f2h_42_e51_local_IRQHandler_26(void)
{
}

__attribute__((weak))  void fabric_f2h_43_e51_local_IRQHandler_27(void)
{
}

__attribute__((weak))  void fabric_f2h_44_e51_local_IRQHandler_28(void)
{
}

__attribute__((weak))  void fabric_f2h_45_e51_local_IRQHandler_29(void)
{
}

__attribute__((weak))  void fabric_f2h_46_e51_local_IRQHandler_30(void)
{
}

__attribute__((weak))  void fabric_f2h_47_e51_local_IRQHandler_31(void)
{
}

__attribute__((weak))  void fabric_f2h_48_e51_local_IRQHandler_32(void)
{
}

__attribute__((weak))  void fabric_f2h_49_e51_local_IRQHandler_33(void)
{
}

__attribute__((weak))  void fabric_f2h_50_e51_local_IRQHandler_34(void)
{
}

__attribute__((weak))  void fabric_f2h_51_e51_local_IRQHandler_35(void)
{
}

__attribute__((weak))  void fabric_f2h_52_e51_local_IRQHandler_36(void)
{
}

__attribute__((weak))  void fabric_f2h_53_e51_local_IRQHandler_37(void)
{
}

__attribute__((weak))  void fabric_f2h_54_e51_local_IRQHandler_38(void)
{
}

__attribute__((weak))  void fabric_f2h_55_e51_local_IRQHandler_39(void)
{
}

__attribute__((weak))  void fabric_f2h_56_e51_local_IRQHandler_40(void)
{
}

__attribute__((weak))  void fabric_f2h_57_e51_local_IRQHandler_41(void)
{
}

__attribute__((weak))  void fabric_f2h_58_e51_local_IRQHandler_42(void)
{
}

__attribute__((weak))  void fabric_f2h_59_e51_local_IRQHandler_43(void)
{
}

__attribute__((weak))  void fabric_f2h_60_e51_local_IRQHandler_44(void)
{
}

__attribute__((weak))  void fabric_f2h_61_e51_local_IRQHandler_45(void)
{
}

__attribute__((weak))  void fabric_f2h_62_e51_local_IRQHandler_46(void)
{
}

__attribute__((weak))  void fabric_f2h_63_e51_local_IRQHandler_47(void)
{
}


/*
 * U54
 */
__attribute__((weak))  void spare_u54_local_IRQHandler_0(void)
{
}
__attribute__((weak))  void spare_u54_local_IRQHandler_1(void)
{
}
__attribute__((weak))  void spare_u54_local_IRQHandler_2(void)
{
}

/* Ethernet MACs - GEM0 is on U54s 1 and 2, GEM1 is on U54s 3 and 4 */

/* U54 1 */
__attribute__((weak))  void mac_mmsl_u54_1_local_IRQHandler_3(void)
{
}
__attribute__((weak))  void mac_emac_u54_1_local_IRQHandler_4(void)
{
}
__attribute__((weak))  void mac_queue3_u54_1_local_IRQHandler_5(void)
{
}
__attribute__((weak))  void mac_queue2_u54_1_local_IRQHandler_6(void)
{
}
__attribute__((weak))  void mac_queue1_u54_1_local_IRQHandler_7(void)
{
}
__attribute__((weak))  void mac_int_u54_1_local_IRQHandler_8(void)
{
}

/* U54 2 */
__attribute__((weak))  void mac_mmsl_u54_2_local_IRQHandler_3(void)
{
}
__attribute__((weak))  void mac_emac_u54_2_local_IRQHandler_4(void)
{
}
__attribute__((weak))  void mac_queue3_u54_2_local_IRQHandler_5(void)
{
}
__attribute__((weak))  void mac_queue2_u54_2_local_IRQHandler_6(void)
{
}
__attribute__((weak))  void mac_queue1_u54_2_local_IRQHandler_7(void)
{
}
__attribute__((weak))  void mac_int_u54_2_local_IRQHandler_8(void)
{
}

/* U54 3 */
__attribute__((weak))  void mac_mmsl_u54_3_local_IRQHandler_3(void)
{
}
__attribute__((weak))  void mac_emac_u54_3_local_IRQHandler_4(void)
{
}
__attribute__((weak))  void mac_queue3_u54_3_local_IRQHandler_5(void)
{
}
__attribute__((weak))  void mac_queue2_u54_3_local_IRQHandler_6(void)
{
}
__attribute__((weak))  void mac_queue1_u54_3_local_IRQHandler_7(void)
{
}
__attribute__((weak))  void mac_int_u54_3_local_IRQHandler_8(void)
{
}

/* U54 4 */
__attribute__((weak))  void mac_mmsl_u54_4_local_IRQHandler_3(void)
{
}
__attribute__((weak))  void mac_emac_u54_4_local_IRQHandler_4(void)
{
}
__attribute__((weak))  void mac_queue3_u54_4_local_IRQHandler_5(void)
{
}
__attribute__((weak))  void mac_queue2_u54_4_local_IRQHandler_6(void)
{
}
__attribute__((weak))  void mac_queue1_u54_4_local_IRQHandler_7(void)
{
}
__attribute__((weak))  void mac_int_u54_4_local_IRQHandler_8(void)
{
}
__attribute__((weak))  void wdog_tout_u54_h1_local_IRQHandler_9(void)
{
}
__attribute__((weak))  void wdog_tout_u54_h2_local_IRQHandler_9(void)
{
}
__attribute__((weak))  void wdog_tout_u54_h3_local_IRQHandler_9(void)
{
}
__attribute__((weak))  void wdog_tout_u54_h4_local_IRQHandler_9(void)
{
}
__attribute__((weak))  void mvrp_u54_local_IRQHandler_10(void)
{
}
__attribute__((weak))  void mmuart_u54_h1_local_IRQHandler_11(void)
{
}
__attribute__((weak))  void mmuart_u54_h2_local_IRQHandler_11(void)
{
}
__attribute__((weak))  void mmuart_u54_h3_local_IRQHandler_11(void)
{
}
__attribute__((weak))  void mmuart_u54_h4_local_IRQHandler_11(void)
{
}
__attribute__((weak))  void spare_u54_local_IRQHandler_12(void)
{
}
__attribute__((weak))  void spare_u54_local_IRQHandler_13(void)
{
}
__attribute__((weak))  void spare_u54_local_IRQHandler_14(void)
{
}
__attribute__((weak))  void spare_u54_local_IRQHandler_15(void)
{
}
__attribute__((weak))  void fabric_f2h_0_u54_local_IRQHandler_16(void)
{
}
__attribute__((weak))  void fabric_f2h_1_u54_local_IRQHandler_17(void)
{
}
__attribute__((weak))  void fabric_f2h_2_u54_local_IRQHandler_18(void)
{
}
__attribute__((weak))  void fabric_f2h_3_u54_local_IRQHandler_19(void)
{
}
__attribute__((weak))  void fabric_f2h_4_u54_local_IRQHandler_20(void)
{
}
__attribute__((weak))  void fabric_f2h_5_u54_local_IRQHandler_21(void)
{
}
__attribute__((weak))  void fabric_f2h_6_u54_local_IRQHandler_22(void)
{
}
__attribute__((weak))  void fabric_f2h_7_u54_local_IRQHandler_23(void)
{
}
__attribute__((weak))  void fabric_f2h_8_u54_local_IRQHandler_24(void)
{
}
__attribute__((weak))  void fabric_f2h_9_u54_local_IRQHandler_25(void)
{
}
__attribute__((weak))  void fabric_f2h_10_u54_local_IRQHandler_26(void)
{
}
__attribute__((weak))  void fabric_f2h_11_u54_local_IRQHandler_27(void)
{
}
__attribute__((weak))  void fabric_f2h_12_u54_local_IRQHandler_28(void)
{
}
__attribute__((weak))  void fabric_f2h_13_u54_local_IRQHandler_29(void)
{
}
__attribute__((weak))  void fabric_f2h_14_u54_local_IRQHandler_30(void)
{
}
__attribute__((weak))  void fabric_f2h_15_u54_local_IRQHandler_31(void)
{
}
__attribute__((weak))  void fabric_f2h_16_u54_local_IRQHandler_32(void)
{
}
__attribute__((weak))  void fabric_f2h_17_u54_local_IRQHandler_33(void)
{
}
__attribute__((weak))  void fabric_f2h_18_u54_local_IRQHandler_34(void)
{
}
__attribute__((weak))  void fabric_f2h_19_u54_local_IRQHandler_35(void)
{
}
__attribute__((weak))  void fabric_f2h_20_u54_local_IRQHandler_36(void)
{
}
__attribute__((weak))  void fabric_f2h_21_u54_local_IRQHandler_37(void)
{
}
__attribute__((weak))  void fabric_f2h_22_u54_local_IRQHandler_38(void)
{
}
__attribute__((weak))  void fabric_f2h_23_u54_local_IRQHandler_39(void)
{
}
__attribute__((weak))  void fabric_f2h_24_u54_local_IRQHandler_40(void)
{
}
__attribute__((weak))  void fabric_f2h_25_u54_local_IRQHandler_41(void)
{
}
__attribute__((weak))  void fabric_f2h_26_u54_local_IRQHandler_42(void)
{
}
__attribute__((weak))  void fabric_f2h_27_u54_local_IRQHandler_43(void)
{
}
__attribute__((weak))  void fabric_f2h_28_u54_local_IRQHandler_44(void)
{
}
__attribute__((weak))  void fabric_f2h_29_u54_local_IRQHandler_45(void)
{
}

__attribute__((weak))  void fabric_f2h_30_u54_local_IRQHandler_46(void)
{
}
__attribute__((weak))  void fabric_f2h_31_u54_local_IRQHandler_47(void)
{
}
#endif  /* ifndef SIFIVE_HIFIVE_UNLEASHED */
