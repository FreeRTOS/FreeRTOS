/* ---------------------------------------------------------------------------- */
/*                  Atmel Microcontroller Software Support                      */
/*                       SAM Software Package License                           */
/* ---------------------------------------------------------------------------- */
/* Copyright (c) 2015, Atmel Corporation                                        */
/*                                                                              */
/* All rights reserved.                                                         */
/*                                                                              */
/* Redistribution and use in source and binary forms, with or without           */
/* modification, are permitted provided that the following condition is met:    */
/*                                                                              */
/* - Redistributions of source code must retain the above copyright notice,     */
/* this list of conditions and the disclaimer below.                            */
/*                                                                              */
/* Atmel's name may not be used to endorse or promote products derived from     */
/* this software without specific prior written permission.                     */
/*                                                                              */
/* DISCLAIMER:  THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR   */
/* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF */
/* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE   */
/* DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,      */
/* INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT */
/* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,  */
/* OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF    */
/* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING         */
/* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, */
/* EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                           */
/* ---------------------------------------------------------------------------- */

#ifndef _SAMA5D27_PIO_
#define _SAMA5D27_PIO_

#define PIO_PA0                (1u << 0)  /**< \brief Pin Controlled by PA0 */
#define PIO_PA1                (1u << 1)  /**< \brief Pin Controlled by PA1 */
#define PIO_PA2                (1u << 2)  /**< \brief Pin Controlled by PA2 */
#define PIO_PA3                (1u << 3)  /**< \brief Pin Controlled by PA3 */
#define PIO_PA4                (1u << 4)  /**< \brief Pin Controlled by PA4 */
#define PIO_PA5                (1u << 5)  /**< \brief Pin Controlled by PA5 */
#define PIO_PA6                (1u << 6)  /**< \brief Pin Controlled by PA6 */
#define PIO_PA7                (1u << 7)  /**< \brief Pin Controlled by PA7 */
#define PIO_PA8                (1u << 8)  /**< \brief Pin Controlled by PA8 */
#define PIO_PA9                (1u << 9)  /**< \brief Pin Controlled by PA9 */
#define PIO_PA10               (1u << 10) /**< \brief Pin Controlled by PA10 */
#define PIO_PA11               (1u << 11) /**< \brief Pin Controlled by PA11 */
#define PIO_PA12               (1u << 12) /**< \brief Pin Controlled by PA12 */
#define PIO_PA13               (1u << 13) /**< \brief Pin Controlled by PA13 */
#define PIO_PA14               (1u << 14) /**< \brief Pin Controlled by PA14 */
#define PIO_PA15               (1u << 15) /**< \brief Pin Controlled by PA15 */
#define PIO_PA16               (1u << 16) /**< \brief Pin Controlled by PA16 */
#define PIO_PA17               (1u << 17) /**< \brief Pin Controlled by PA17 */
#define PIO_PA18               (1u << 18) /**< \brief Pin Controlled by PA18 */
#define PIO_PA19               (1u << 19) /**< \brief Pin Controlled by PA19 */
#define PIO_PA20               (1u << 20) /**< \brief Pin Controlled by PA20 */
#define PIO_PA21               (1u << 21) /**< \brief Pin Controlled by PA21 */
#define PIO_PA22               (1u << 22) /**< \brief Pin Controlled by PA22 */
#define PIO_PA23               (1u << 23) /**< \brief Pin Controlled by PA23 */
#define PIO_PA24               (1u << 24) /**< \brief Pin Controlled by PA24 */
#define PIO_PA25               (1u << 25) /**< \brief Pin Controlled by PA25 */
#define PIO_PA26               (1u << 26) /**< \brief Pin Controlled by PA26 */
#define PIO_PA27               (1u << 27) /**< \brief Pin Controlled by PA27 */
#define PIO_PA28               (1u << 28) /**< \brief Pin Controlled by PA28 */
#define PIO_PA29               (1u << 29) /**< \brief Pin Controlled by PA29 */
#define PIO_PA30               (1u << 30) /**< \brief Pin Controlled by PA30 */
#define PIO_PA31               (1u << 31) /**< \brief Pin Controlled by PA31 */
#define PIO_PB0                (1u << 0)  /**< \brief Pin Controlled by PB0 */
#define PIO_PB1                (1u << 1)  /**< \brief Pin Controlled by PB1 */
#define PIO_PB2                (1u << 2)  /**< \brief Pin Controlled by PB2 */
#define PIO_PB3                (1u << 3)  /**< \brief Pin Controlled by PB3 */
#define PIO_PB4                (1u << 4)  /**< \brief Pin Controlled by PB4 */
#define PIO_PB5                (1u << 5)  /**< \brief Pin Controlled by PB5 */
#define PIO_PB6                (1u << 6)  /**< \brief Pin Controlled by PB6 */
#define PIO_PB7                (1u << 7)  /**< \brief Pin Controlled by PB7 */
#define PIO_PB8                (1u << 8)  /**< \brief Pin Controlled by PB8 */
#define PIO_PB9                (1u << 9)  /**< \brief Pin Controlled by PB9 */
#define PIO_PB10               (1u << 10) /**< \brief Pin Controlled by PB10 */
#define PIO_PB11               (1u << 11) /**< \brief Pin Controlled by PB11 */
#define PIO_PB12               (1u << 12) /**< \brief Pin Controlled by PB12 */
#define PIO_PB13               (1u << 13) /**< \brief Pin Controlled by PB13 */
#define PIO_PB14               (1u << 14) /**< \brief Pin Controlled by PB14 */
#define PIO_PB15               (1u << 15) /**< \brief Pin Controlled by PB15 */
#define PIO_PB16               (1u << 16) /**< \brief Pin Controlled by PB16 */
#define PIO_PB17               (1u << 17) /**< \brief Pin Controlled by PB17 */
#define PIO_PB18               (1u << 18) /**< \brief Pin Controlled by PB18 */
#define PIO_PB19               (1u << 19) /**< \brief Pin Controlled by PB19 */
#define PIO_PB20               (1u << 20) /**< \brief Pin Controlled by PB20 */
#define PIO_PB21               (1u << 21) /**< \brief Pin Controlled by PB21 */
#define PIO_PB22               (1u << 22) /**< \brief Pin Controlled by PB22 */
#define PIO_PB23               (1u << 23) /**< \brief Pin Controlled by PB23 */
#define PIO_PB24               (1u << 24) /**< \brief Pin Controlled by PB24 */
#define PIO_PB25               (1u << 25) /**< \brief Pin Controlled by PB25 */
#define PIO_PB26               (1u << 26) /**< \brief Pin Controlled by PB26 */
#define PIO_PB27               (1u << 27) /**< \brief Pin Controlled by PB27 */
#define PIO_PB28               (1u << 28) /**< \brief Pin Controlled by PB28 */
#define PIO_PB29               (1u << 29) /**< \brief Pin Controlled by PB29 */
#define PIO_PB30               (1u << 30) /**< \brief Pin Controlled by PB30 */
#define PIO_PB31               (1u << 31) /**< \brief Pin Controlled by PB31 */
#define PIO_PC0                (1u << 0)  /**< \brief Pin Controlled by PC0 */
#define PIO_PC1                (1u << 1)  /**< \brief Pin Controlled by PC1 */
#define PIO_PC2                (1u << 2)  /**< \brief Pin Controlled by PC2 */
#define PIO_PC3                (1u << 3)  /**< \brief Pin Controlled by PC3 */
#define PIO_PC4                (1u << 4)  /**< \brief Pin Controlled by PC4 */
#define PIO_PC5                (1u << 5)  /**< \brief Pin Controlled by PC5 */
#define PIO_PC6                (1u << 6)  /**< \brief Pin Controlled by PC6 */
#define PIO_PC7                (1u << 7)  /**< \brief Pin Controlled by PC7 */
#define PIO_PC8                (1u << 8)  /**< \brief Pin Controlled by PC8 */
#define PIO_PC9                (1u << 9)  /**< \brief Pin Controlled by PC9 */
#define PIO_PC10               (1u << 10) /**< \brief Pin Controlled by PC10 */
#define PIO_PC11               (1u << 11) /**< \brief Pin Controlled by PC11 */
#define PIO_PC12               (1u << 12) /**< \brief Pin Controlled by PC12 */
#define PIO_PC13               (1u << 13) /**< \brief Pin Controlled by PC13 */
#define PIO_PC14               (1u << 14) /**< \brief Pin Controlled by PC14 */
#define PIO_PC15               (1u << 15) /**< \brief Pin Controlled by PC15 */
#define PIO_PC16               (1u << 16) /**< \brief Pin Controlled by PC16 */
#define PIO_PC17               (1u << 17) /**< \brief Pin Controlled by PC17 */
#define PIO_PC18               (1u << 18) /**< \brief Pin Controlled by PC18 */
#define PIO_PC19               (1u << 19) /**< \brief Pin Controlled by PC19 */
#define PIO_PC20               (1u << 20) /**< \brief Pin Controlled by PC20 */
#define PIO_PC21               (1u << 21) /**< \brief Pin Controlled by PC21 */
#define PIO_PC22               (1u << 22) /**< \brief Pin Controlled by PC22 */
#define PIO_PC23               (1u << 23) /**< \brief Pin Controlled by PC23 */
#define PIO_PC24               (1u << 24) /**< \brief Pin Controlled by PC24 */
#define PIO_PC25               (1u << 25) /**< \brief Pin Controlled by PC25 */
#define PIO_PC26               (1u << 26) /**< \brief Pin Controlled by PC26 */
#define PIO_PC27               (1u << 27) /**< \brief Pin Controlled by PC27 */
#define PIO_PC28               (1u << 28) /**< \brief Pin Controlled by PC28 */
#define PIO_PC29               (1u << 29) /**< \brief Pin Controlled by PC29 */
#define PIO_PC30               (1u << 30) /**< \brief Pin Controlled by PC30 */
#define PIO_PC31               (1u << 31) /**< \brief Pin Controlled by PC31 */
#define PIO_PD0                (1u << 0)  /**< \brief Pin Controlled by PD0 */
#define PIO_PD1                (1u << 1)  /**< \brief Pin Controlled by PD1 */
#define PIO_PD2                (1u << 2)  /**< \brief Pin Controlled by PD2 */
#define PIO_PD3                (1u << 3)  /**< \brief Pin Controlled by PD3 */
#define PIO_PD4                (1u << 4)  /**< \brief Pin Controlled by PD4 */
#define PIO_PD5                (1u << 5)  /**< \brief Pin Controlled by PD5 */
#define PIO_PD6                (1u << 6)  /**< \brief Pin Controlled by PD6 */
#define PIO_PD7                (1u << 7)  /**< \brief Pin Controlled by PD7 */
#define PIO_PD8                (1u << 8)  /**< \brief Pin Controlled by PD8 */
#define PIO_PD9                (1u << 9)  /**< \brief Pin Controlled by PD9 */
#define PIO_PD10               (1u << 10) /**< \brief Pin Controlled by PD10 */
#define PIO_PD11               (1u << 11) /**< \brief Pin Controlled by PD11 */
#define PIO_PD12               (1u << 12) /**< \brief Pin Controlled by PD12 */
#define PIO_PD13               (1u << 13) /**< \brief Pin Controlled by PD13 */
#define PIO_PD14               (1u << 14) /**< \brief Pin Controlled by PD14 */
#define PIO_PD15               (1u << 15) /**< \brief Pin Controlled by PD15 */
#define PIO_PD16               (1u << 16) /**< \brief Pin Controlled by PD16 */
#define PIO_PD17               (1u << 17) /**< \brief Pin Controlled by PD17 */
#define PIO_PD18               (1u << 18) /**< \brief Pin Controlled by PD18 */
#define PIO_PD19               (1u << 19) /**< \brief Pin Controlled by PD19 */
#define PIO_PD20               (1u << 20) /**< \brief Pin Controlled by PD20 */
#define PIO_PD21               (1u << 21) /**< \brief Pin Controlled by PD21 */
#define PIO_PD22               (1u << 22) /**< \brief Pin Controlled by PD22 */
#define PIO_PD23               (1u << 23) /**< \brief Pin Controlled by PD23 */
#define PIO_PD24               (1u << 24) /**< \brief Pin Controlled by PD24 */
#define PIO_PD25               (1u << 25) /**< \brief Pin Controlled by PD25 */
#define PIO_PD26               (1u << 26) /**< \brief Pin Controlled by PD26 */
#define PIO_PD27               (1u << 27) /**< \brief Pin Controlled by PD27 */
#define PIO_PD28               (1u << 28) /**< \brief Pin Controlled by PD28 */
#define PIO_PD29               (1u << 29) /**< \brief Pin Controlled by PD29 */
#define PIO_PD30               (1u << 30) /**< \brief Pin Controlled by PD30 */
#define PIO_PD31               (1u << 31) /**< \brief Pin Controlled by PD31 */
/* ========== Pio definition for ADC peripheral ========== */
#define PIO_PD19X1_AD0         (1u << 19) /**< \brief Adc signal: AD0 */
#define PIO_PD20X1_AD1         (1u << 20) /**< \brief Adc signal: AD1 */
#define PIO_PD29X1_AD10        (1u << 29) /**< \brief Adc signal: AD10 */
#define PIO_PD30X1_AD11        (1u << 30) /**< \brief Adc signal: AD11 */
#define PIO_PD21X1_AD2         (1u << 21) /**< \brief Adc signal: AD2 */
#define PIO_PD22X1_AD3         (1u << 22) /**< \brief Adc signal: AD3 */
#define PIO_PD23X1_AD4         (1u << 23) /**< \brief Adc signal: AD4 */
#define PIO_PD24X1_AD5         (1u << 24) /**< \brief Adc signal: AD5 */
#define PIO_PD25X1_AD6         (1u << 25) /**< \brief Adc signal: AD6 */
#define PIO_PD26X1_AD7         (1u << 26) /**< \brief Adc signal: AD7 */
#define PIO_PD27X1_AD8         (1u << 27) /**< \brief Adc signal: AD8 */
#define PIO_PD28X1_AD9         (1u << 28) /**< \brief Adc signal: AD9 */
#define PIO_PD31A_ADTRG        (1u << 31) /**< \brief Adc signal: ADTRG */
/* ========== Pio definition for AIC peripheral ========== */
#define PIO_PB4C_FIQ           (1u << 4)  /**< \brief Aic signal: FIQ */
#define PIO_PC8C_FIQ           (1u << 8)  /**< \brief Aic signal: FIQ */
#define PIO_PC9A_FIQ           (1u << 9)  /**< \brief Aic signal: FIQ */
#define PIO_PD3B_FIQ           (1u << 3)  /**< \brief Aic signal: FIQ */
#define PIO_PA12B_IRQ          (1u << 12) /**< \brief Aic signal: IRQ */
#define PIO_PA21A_IRQ          (1u << 21) /**< \brief Aic signal: IRQ */
#define PIO_PB3C_IRQ           (1u << 3)  /**< \brief Aic signal: IRQ */
#define PIO_PD31C_IRQ          (1u << 31) /**< \brief Aic signal: IRQ */
/* ========== Pio definition for ARM peripheral ========== */
#define PIO_PA26C_NTRST        (1u << 26) /**< \brief Arm signal: NTRST */
#define PIO_PD10A_NTRST        (1u << 10) /**< \brief Arm signal: NTRST */
#define PIO_PD18A_NTRST        (1u << 18) /**< \brief Arm signal: NTRST */
#define PIO_PD31B_NTRST        (1u << 31) /**< \brief Arm signal: NTRST */
#define PIO_PA22C_TCK          (1u << 22) /**< \brief Arm signal: TCK */
#define PIO_PD6A_TCK           (1u << 6)  /**< \brief Arm signal: TCK */
#define PIO_PD14A_TCK          (1u << 14) /**< \brief Arm signal: TCK */
#define PIO_PD27B_TCK          (1u << 27) /**< \brief Arm signal: TCK */
#define PIO_PA23C_TDI          (1u << 23) /**< \brief Arm signal: TDI */
#define PIO_PD7A_TDI           (1u << 7)  /**< \brief Arm signal: TDI */
#define PIO_PD15A_TDI          (1u << 15) /**< \brief Arm signal: TDI */
#define PIO_PD28B_TDI          (1u << 28) /**< \brief Arm signal: TDI */
#define PIO_PA24C_TDO          (1u << 24) /**< \brief Arm signal: TDO */
#define PIO_PD8A_TDO           (1u << 8)  /**< \brief Arm signal: TDO */
#define PIO_PD16A_TDO          (1u << 16) /**< \brief Arm signal: TDO */
#define PIO_PD29B_TDO          (1u << 29) /**< \brief Arm signal: TDO */
#define PIO_PA25C_TMS          (1u << 25) /**< \brief Arm signal: TMS */
#define PIO_PD9A_TMS           (1u << 9)  /**< \brief Arm signal: TMS */
#define PIO_PD17A_TMS          (1u << 17) /**< \brief Arm signal: TMS */
#define PIO_PD30B_TMS          (1u << 30) /**< \brief Arm signal: TMS */
/* ========== Pio definition for CLASSD peripheral ========== */
#define PIO_PA28F_CLASSD_L0    (1u << 28) /**< \brief Classd signal: CLASSD_L0 */
#define PIO_PA29F_CLASSD_L1    (1u << 29) /**< \brief Classd signal: CLASSD_L1 */
#define PIO_PA30F_CLASSD_L2    (1u << 30) /**< \brief Classd signal: CLASSD_L2 */
#define PIO_PA31F_CLASSD_L3    (1u << 31) /**< \brief Classd signal: CLASSD_L3 */
#define PIO_PB1F_CLASSD_R0     (1u << 1)  /**< \brief Classd signal: CLASSD_R0 */
#define PIO_PB2F_CLASSD_R1     (1u << 2)  /**< \brief Classd signal: CLASSD_R1 */
#define PIO_PB3F_CLASSD_R2     (1u << 3)  /**< \brief Classd signal: CLASSD_R2 */
#define PIO_PB4F_CLASSD_R3     (1u << 4)  /**< \brief Classd signal: CLASSD_R3 */
/* ========== Pio definition for EBI peripheral ========== */
#define PIO_PB11B_A0           (1u << 11) /**< \brief Ebi signal: A0/NBS0 */
#define PIO_PB11B_NBS0         (1u << 11) /**< \brief Ebi signal: A0/NBS0 */
#define PIO_PC11F_A0           (1u << 11) /**< \brief Ebi signal: A0/NBS0 */
#define PIO_PC11F_NBS0         (1u << 11) /**< \brief Ebi signal: A0/NBS0 */
#define PIO_PB12B_A1           (1u << 12) /**< \brief Ebi signal: A1 */
#define PIO_PC12F_A1           (1u << 12) /**< \brief Ebi signal: A1 */
#define PIO_PB21B_A10          (1u << 21) /**< \brief Ebi signal: A10 */
#define PIO_PC21F_A10          (1u << 21) /**< \brief Ebi signal: A10 */
#define PIO_PB22B_A11          (1u << 22) /**< \brief Ebi signal: A11 */
#define PIO_PC22F_A11          (1u << 22) /**< \brief Ebi signal: A11 */
#define PIO_PB23B_A12          (1u << 23) /**< \brief Ebi signal: A12 */
#define PIO_PC23F_A12          (1u << 23) /**< \brief Ebi signal: A12 */
#define PIO_PB24B_A13          (1u << 24) /**< \brief Ebi signal: A13 */
#define PIO_PC24F_A13          (1u << 24) /**< \brief Ebi signal: A13 */
#define PIO_PB25B_A14          (1u << 25) /**< \brief Ebi signal: A14 */
#define PIO_PC25F_A14          (1u << 25) /**< \brief Ebi signal: A14 */
#define PIO_PB26B_A15          (1u << 26) /**< \brief Ebi signal: A15 */
#define PIO_PC26F_A15          (1u << 26) /**< \brief Ebi signal: A15 */
#define PIO_PB27B_A16          (1u << 27) /**< \brief Ebi signal: A16 */
#define PIO_PC27F_A16          (1u << 27) /**< \brief Ebi signal: A16 */
#define PIO_PB28B_A17          (1u << 28) /**< \brief Ebi signal: A17 */
#define PIO_PC28F_A17          (1u << 28) /**< \brief Ebi signal: A17 */
#define PIO_PB29B_A18          (1u << 29) /**< \brief Ebi signal: A18 */
#define PIO_PC29F_A18          (1u << 29) /**< \brief Ebi signal: A18 */
#define PIO_PB30B_A19          (1u << 30) /**< \brief Ebi signal: A19 */
#define PIO_PC30F_A19          (1u << 30) /**< \brief Ebi signal: A19 */
#define PIO_PB13B_A2           (1u << 13) /**< \brief Ebi signal: A2 */
#define PIO_PC13F_A2           (1u << 13) /**< \brief Ebi signal: A2 */
#define PIO_PB31B_A20          (1u << 31) /**< \brief Ebi signal: A20 */
#define PIO_PC31F_A20          (1u << 31) /**< \brief Ebi signal: A20 */
#define PIO_PA10F_A21          (1u << 10) /**< \brief Ebi signal: A21/NANDALE */
#define PIO_PA10F_NANDALE      (1u << 10) /**< \brief Ebi signal: A21/NANDALE */
#define PIO_PB0B_A21           (1u << 0)  /**< \brief Ebi signal: A21/NANDALE */
#define PIO_PB0B_NANDALE       (1u << 0)  /**< \brief Ebi signal: A21/NANDALE */
#define PIO_PA11F_A22          (1u << 11) /**< \brief Ebi signal: A22/NANDCLE */
#define PIO_PA11F_NANDCLE      (1u << 11) /**< \brief Ebi signal: A22/NANDCLE */
#define PIO_PB1B_A22           (1u << 1)  /**< \brief Ebi signal: A22/NANDCLE */
#define PIO_PB1B_NANDCLE       (1u << 1)  /**< \brief Ebi signal: A22/NANDCLE */
#define PIO_PC0B_A23           (1u << 0)  /**< \brief Ebi signal: A23 */
#define PIO_PD0F_A23           (1u << 0)  /**< \brief Ebi signal: A23 */
#define PIO_PC1B_A24           (1u << 1)  /**< \brief Ebi signal: A24 */
#define PIO_PD1F_A24           (1u << 1)  /**< \brief Ebi signal: A24 */
#define PIO_PC2B_A25           (1u << 2)  /**< \brief Ebi signal: A25 */
#define PIO_PD2F_A25           (1u << 2)  /**< \brief Ebi signal: A25 */
#define PIO_PB14B_A3           (1u << 14) /**< \brief Ebi signal: A3 */
#define PIO_PC14F_A3           (1u << 14) /**< \brief Ebi signal: A3 */
#define PIO_PB15B_A4           (1u << 15) /**< \brief Ebi signal: A4 */
#define PIO_PC15F_A4           (1u << 15) /**< \brief Ebi signal: A4 */
#define PIO_PB16B_A5           (1u << 16) /**< \brief Ebi signal: A5 */
#define PIO_PC16F_A5           (1u << 16) /**< \brief Ebi signal: A5 */
#define PIO_PB17B_A6           (1u << 17) /**< \brief Ebi signal: A6 */
#define PIO_PC17F_A6           (1u << 17) /**< \brief Ebi signal: A6 */
#define PIO_PB18B_A7           (1u << 18) /**< \brief Ebi signal: A7 */
#define PIO_PC18F_A7           (1u << 18) /**< \brief Ebi signal: A7 */
#define PIO_PB19B_A8           (1u << 19) /**< \brief Ebi signal: A8 */
#define PIO_PC19F_A8           (1u << 19) /**< \brief Ebi signal: A8 */
#define PIO_PB20B_A9           (1u << 20) /**< \brief Ebi signal: A9 */
#define PIO_PC20F_A9           (1u << 20) /**< \brief Ebi signal: A9 */
#define PIO_PA0F_D0            (1u << 0)  /**< \brief Ebi signal: D0 */
#define PIO_PA22B_D0           (1u << 22) /**< \brief Ebi signal: D0 */
#define PIO_PA1F_D1            (1u << 1)  /**< \brief Ebi signal: D1 */
#define PIO_PA23B_D1           (1u << 23) /**< \brief Ebi signal: D1 */
#define PIO_PA15F_D10          (1u << 15) /**< \brief Ebi signal: D10 */
#define PIO_PB5B_D10           (1u << 5)  /**< \brief Ebi signal: D10 */
#define PIO_PA16F_D11          (1u << 16) /**< \brief Ebi signal: D11 */
#define PIO_PB6B_D11           (1u << 6)  /**< \brief Ebi signal: D11 */
#define PIO_PA17F_D12          (1u << 17) /**< \brief Ebi signal: D12 */
#define PIO_PB7B_D12           (1u << 7)  /**< \brief Ebi signal: D12 */
#define PIO_PA18F_D13          (1u << 18) /**< \brief Ebi signal: D13 */
#define PIO_PB8B_D13           (1u << 8)  /**< \brief Ebi signal: D13 */
#define PIO_PA19F_D14          (1u << 19) /**< \brief Ebi signal: D14 */
#define PIO_PB9B_D14           (1u << 9)  /**< \brief Ebi signal: D14 */
#define PIO_PA20F_D15          (1u << 20) /**< \brief Ebi signal: D15 */
#define PIO_PB10B_D15          (1u << 10) /**< \brief Ebi signal: D15 */
#define PIO_PA2F_D2            (1u << 2)  /**< \brief Ebi signal: D2 */
#define PIO_PA24B_D2           (1u << 24) /**< \brief Ebi signal: D2 */
#define PIO_PA3F_D3            (1u << 3)  /**< \brief Ebi signal: D3 */
#define PIO_PA25B_D3           (1u << 25) /**< \brief Ebi signal: D3 */
#define PIO_PA4F_D4            (1u << 4)  /**< \brief Ebi signal: D4 */
#define PIO_PA26B_D4           (1u << 26) /**< \brief Ebi signal: D4 */
#define PIO_PA5F_D5            (1u << 5)  /**< \brief Ebi signal: D5 */
#define PIO_PA27B_D5           (1u << 27) /**< \brief Ebi signal: D5 */
#define PIO_PA6F_D6            (1u << 6)  /**< \brief Ebi signal: D6 */
#define PIO_PA28B_D6           (1u << 28) /**< \brief Ebi signal: D6 */
#define PIO_PA7F_D7            (1u << 7)  /**< \brief Ebi signal: D7 */
#define PIO_PA29B_D7           (1u << 29) /**< \brief Ebi signal: D7 */
#define PIO_PA13F_D8           (1u << 13) /**< \brief Ebi signal: D8 */
#define PIO_PB3B_D8            (1u << 3)  /**< \brief Ebi signal: D8 */
#define PIO_PA14F_D9           (1u << 14) /**< \brief Ebi signal: D9 */
#define PIO_PB4B_D9            (1u << 4)  /**< \brief Ebi signal: D9 */
#define PIO_PA21F_NANDRDY      (1u << 21) /**< \brief Ebi signal: NANDRDY */
#define PIO_PC8B_NANDRDY       (1u << 8)  /**< \brief Ebi signal: NANDRDY */
#define PIO_PD8F_NANDRDY       (1u << 8)  /**< \brief Ebi signal: NANDRDY */
#define PIO_PC5B_NCS0          (1u << 5)  /**< \brief Ebi signal: NCS0 */
#define PIO_PD4F_NCS0          (1u << 4)  /**< \brief Ebi signal: NCS0 */
#define PIO_PC6B_NCS1          (1u << 6)  /**< \brief Ebi signal: NCS1 */
#define PIO_PD5F_NCS1          (1u << 5)  /**< \brief Ebi signal: NCS1 */
#define PIO_PC7B_NCS2          (1u << 7)  /**< \brief Ebi signal: NCS2 */
#define PIO_PD6F_NCS2          (1u << 6)  /**< \brief Ebi signal: NCS2 */
#define PIO_PA9F_NCS3          (1u << 9)  /**< \brief Ebi signal: NCS3 */
#define PIO_PA31B_NCS3         (1u << 31) /**< \brief Ebi signal: NCS3 */
#define PIO_PA12F_NRD          (1u << 12) /**< \brief Ebi signal: NRD/NANDOE */
#define PIO_PA12F_NANDOE       (1u << 12) /**< \brief Ebi signal: NRD/NANDOE */
#define PIO_PB2B_NRD           (1u << 2)  /**< \brief Ebi signal: NRD/NANDOE */
#define PIO_PB2B_NANDOE        (1u << 2)  /**< \brief Ebi signal: NRD/NANDOE */
#define PIO_PC3B_NWAIT         (1u << 3)  /**< \brief Ebi signal: NWAIT */
#define PIO_PD3F_NWAIT         (1u << 3)  /**< \brief Ebi signal: NWAIT */
#define PIO_PA8F_NWE           (1u << 8)  /**< \brief Ebi signal: NWE/NANDWE */
#define PIO_PA8F_NANDWE        (1u << 8)  /**< \brief Ebi signal: NWE/NANDWE */
#define PIO_PA30B_NWE          (1u << 30) /**< \brief Ebi signal: NWE/NANDWE */
#define PIO_PA30B_NANDWE       (1u << 30) /**< \brief Ebi signal: NWE/NANDWE */
#define PIO_PC4B_NWR1          (1u << 4)  /**< \brief Ebi signal: NWR1/NBS1 */
#define PIO_PC4B_NBS1          (1u << 4)  /**< \brief Ebi signal: NWR1/NBS1 */
#define PIO_PD7F_NWR1          (1u << 7)  /**< \brief Ebi signal: NWR1/NBS1 */
#define PIO_PD7F_NBS1          (1u << 7)  /**< \brief Ebi signal: NWR1/NBS1 */
/* ========== Pio definition for FLEXCOM0 peripheral ========== */
#define PIO_PB28C_FLEXCOM0_IO0 (1u << 28) /**< \brief Flexcom0 signal: FLEXCOM0_IO0 */
#define PIO_PB29C_FLEXCOM0_IO1 (1u << 29) /**< \brief Flexcom0 signal: FLEXCOM0_IO1 */
#define PIO_PB30C_FLEXCOM0_IO2 (1u << 30) /**< \brief Flexcom0 signal: FLEXCOM0_IO2 */
#define PIO_PB31C_FLEXCOM0_IO3 (1u << 31) /**< \brief Flexcom0 signal: FLEXCOM0_IO3 */
#define PIO_PC0C_FLEXCOM0_IO4  (1u << 0)  /**< \brief Flexcom0 signal: FLEXCOM0_IO4 */
/* ========== Pio definition for FLEXCOM1 peripheral ========== */
#define PIO_PA24A_FLEXCOM1_IO0 (1u << 24) /**< \brief Flexcom1 signal: FLEXCOM1_IO0 */
#define PIO_PA23A_FLEXCOM1_IO1 (1u << 23) /**< \brief Flexcom1 signal: FLEXCOM1_IO1 */
#define PIO_PA22A_FLEXCOM1_IO2 (1u << 22) /**< \brief Flexcom1 signal: FLEXCOM1_IO2 */
#define PIO_PA25A_FLEXCOM1_IO3 (1u << 25) /**< \brief Flexcom1 signal: FLEXCOM1_IO3 */
#define PIO_PA26A_FLEXCOM1_IO4 (1u << 26) /**< \brief Flexcom1 signal: FLEXCOM1_IO4 */
/* ========== Pio definition for FLEXCOM2 peripheral ========== */
#define PIO_PA6E_FLEXCOM2_IO0  (1u << 6)  /**< \brief Flexcom2 signal: FLEXCOM2_IO0 */
#define PIO_PD26C_FLEXCOM2_IO0 (1u << 26) /**< \brief Flexcom2 signal: FLEXCOM2_IO0 */
#define PIO_PA7E_FLEXCOM2_IO1  (1u << 7)  /**< \brief Flexcom2 signal: FLEXCOM2_IO1 */
#define PIO_PD27C_FLEXCOM2_IO1 (1u << 27) /**< \brief Flexcom2 signal: FLEXCOM2_IO1 */
#define PIO_PA8E_FLEXCOM2_IO2  (1u << 8)  /**< \brief Flexcom2 signal: FLEXCOM2_IO2 */
#define PIO_PD28C_FLEXCOM2_IO2 (1u << 28) /**< \brief Flexcom2 signal: FLEXCOM2_IO2 */
#define PIO_PA9E_FLEXCOM2_IO3  (1u << 9)  /**< \brief Flexcom2 signal: FLEXCOM2_IO3 */
#define PIO_PD29C_FLEXCOM2_IO3 (1u << 29) /**< \brief Flexcom2 signal: FLEXCOM2_IO3 */
#define PIO_PA10E_FLEXCOM2_IO4 (1u << 10) /**< \brief Flexcom2 signal: FLEXCOM2_IO4 */
#define PIO_PD30C_FLEXCOM2_IO4 (1u << 30) /**< \brief Flexcom2 signal: FLEXCOM2_IO4 */
/* ========== Pio definition for FLEXCOM3 peripheral ========== */
#define PIO_PA15E_FLEXCOM3_IO0 (1u << 15) /**< \brief Flexcom3 signal: FLEXCOM3_IO0 */
#define PIO_PB23E_FLEXCOM3_IO0 (1u << 23) /**< \brief Flexcom3 signal: FLEXCOM3_IO0 */
#define PIO_PC20E_FLEXCOM3_IO0 (1u << 20) /**< \brief Flexcom3 signal: FLEXCOM3_IO0 */
#define PIO_PA13E_FLEXCOM3_IO1 (1u << 13) /**< \brief Flexcom3 signal: FLEXCOM3_IO1 */
#define PIO_PB22E_FLEXCOM3_IO1 (1u << 22) /**< \brief Flexcom3 signal: FLEXCOM3_IO1 */
#define PIO_PC19E_FLEXCOM3_IO1 (1u << 19) /**< \brief Flexcom3 signal: FLEXCOM3_IO1 */
#define PIO_PA14E_FLEXCOM3_IO2 (1u << 14) /**< \brief Flexcom3 signal: FLEXCOM3_IO2 */
#define PIO_PB21E_FLEXCOM3_IO2 (1u << 21) /**< \brief Flexcom3 signal: FLEXCOM3_IO2 */
#define PIO_PC18E_FLEXCOM3_IO2 (1u << 18) /**< \brief Flexcom3 signal: FLEXCOM3_IO2 */
#define PIO_PA16E_FLEXCOM3_IO3 (1u << 16) /**< \brief Flexcom3 signal: FLEXCOM3_IO3 */
#define PIO_PB24E_FLEXCOM3_IO3 (1u << 24) /**< \brief Flexcom3 signal: FLEXCOM3_IO3 */
#define PIO_PC21E_FLEXCOM3_IO3 (1u << 21) /**< \brief Flexcom3 signal: FLEXCOM3_IO3 */
#define PIO_PA17E_FLEXCOM3_IO4 (1u << 17) /**< \brief Flexcom3 signal: FLEXCOM3_IO4 */
#define PIO_PB25E_FLEXCOM3_IO4 (1u << 25) /**< \brief Flexcom3 signal: FLEXCOM3_IO4 */
#define PIO_PC22E_FLEXCOM3_IO4 (1u << 22) /**< \brief Flexcom3 signal: FLEXCOM3_IO4 */
/* ========== Pio definition for FLEXCOM4 peripheral ========== */
#define PIO_PC28B_FLEXCOM4_IO0 (1u << 28) /**< \brief Flexcom4 signal: FLEXCOM4_IO0 */
#define PIO_PD12B_FLEXCOM4_IO0 (1u << 12) /**< \brief Flexcom4 signal: FLEXCOM4_IO0 */
#define PIO_PD21C_FLEXCOM4_IO0 (1u << 21) /**< \brief Flexcom4 signal: FLEXCOM4_IO0 */
#define PIO_PC29B_FLEXCOM4_IO1 (1u << 29) /**< \brief Flexcom4 signal: FLEXCOM4_IO1 */
#define PIO_PD13B_FLEXCOM4_IO1 (1u << 13) /**< \brief Flexcom4 signal: FLEXCOM4_IO1 */
#define PIO_PD22C_FLEXCOM4_IO1 (1u << 22) /**< \brief Flexcom4 signal: FLEXCOM4_IO1 */
#define PIO_PC30B_FLEXCOM4_IO2 (1u << 30) /**< \brief Flexcom4 signal: FLEXCOM4_IO2 */
#define PIO_PD14B_FLEXCOM4_IO2 (1u << 14) /**< \brief Flexcom4 signal: FLEXCOM4_IO2 */
#define PIO_PD23C_FLEXCOM4_IO2 (1u << 23) /**< \brief Flexcom4 signal: FLEXCOM4_IO2 */
#define PIO_PC31B_FLEXCOM4_IO3 (1u << 31) /**< \brief Flexcom4 signal: FLEXCOM4_IO3 */
#define PIO_PD15B_FLEXCOM4_IO3 (1u << 15) /**< \brief Flexcom4 signal: FLEXCOM4_IO3 */
#define PIO_PD24C_FLEXCOM4_IO3 (1u << 24) /**< \brief Flexcom4 signal: FLEXCOM4_IO3 */
#define PIO_PD0B_FLEXCOM4_IO4  (1u << 0)  /**< \brief Flexcom4 signal: FLEXCOM4_IO4 */
#define PIO_PD16B_FLEXCOM4_IO4 (1u << 16) /**< \brief Flexcom4 signal: FLEXCOM4_IO4 */
#define PIO_PD25C_FLEXCOM4_IO4 (1u << 25) /**< \brief Flexcom4 signal: FLEXCOM4_IO4 */
/* ========== Pio definition for GMAC peripheral ========== */
#define PIO_PB9F_GCOL          (1u << 9)  /**< \brief Gmac signal: GCOL */
#define PIO_PC23B_GCOL         (1u << 23) /**< \brief Gmac signal: GCOL */
#define PIO_PD4D_GCOL          (1u << 4)  /**< \brief Gmac signal: GCOL */
#define PIO_PB8F_GCRS          (1u << 8)  /**< \brief Gmac signal: GCRS */
#define PIO_PC22B_GCRS         (1u << 22) /**< \brief Gmac signal: GCRS */
#define PIO_PD3D_GCRS          (1u << 3)  /**< \brief Gmac signal: GCRS */
#define PIO_PB22F_GMDC         (1u << 22) /**< \brief Gmac signal: GMDC */
#define PIO_PC18B_GMDC         (1u << 18) /**< \brief Gmac signal: GMDC */
#define PIO_PD17D_GMDC         (1u << 17) /**< \brief Gmac signal: GMDC */
#define PIO_PB23F_GMDIO        (1u << 23) /**< \brief Gmac signal: GMDIO */
#define PIO_PC19B_GMDIO        (1u << 19) /**< \brief Gmac signal: GMDIO */
#define PIO_PD18D_GMDIO        (1u << 18) /**< \brief Gmac signal: GMDIO */
#define PIO_PB18F_GRX0         (1u << 18) /**< \brief Gmac signal: GRX0 */
#define PIO_PC14B_GRX0         (1u << 14) /**< \brief Gmac signal: GRX0 */
#define PIO_PD13D_GRX0         (1u << 13) /**< \brief Gmac signal: GRX0 */
#define PIO_PB19F_GRX1         (1u << 19) /**< \brief Gmac signal: GRX1 */
#define PIO_PC15B_GRX1         (1u << 15) /**< \brief Gmac signal: GRX1 */
#define PIO_PD14D_GRX1         (1u << 14) /**< \brief Gmac signal: GRX1 */
#define PIO_PB10F_GRX2         (1u << 10) /**< \brief Gmac signal: GRX2 */
#define PIO_PC24B_GRX2         (1u << 24) /**< \brief Gmac signal: GRX2 */
#define PIO_PD5D_GRX2          (1u << 5)  /**< \brief Gmac signal: GRX2 */
#define PIO_PB11F_GRX3         (1u << 11) /**< \brief Gmac signal: GRX3 */
#define PIO_PC25B_GRX3         (1u << 25) /**< \brief Gmac signal: GRX3 */
#define PIO_PD6D_GRX3          (1u << 6)  /**< \brief Gmac signal: GRX3 */
#define PIO_PB7F_GRXCK         (1u << 7)  /**< \brief Gmac signal: GRXCK */
#define PIO_PC20B_GRXCK        (1u << 20) /**< \brief Gmac signal: GRXCK */
#define PIO_PD1D_GRXCK         (1u << 1)  /**< \brief Gmac signal: GRXCK */
#define PIO_PB16F_GRXDV        (1u << 16) /**< \brief Gmac signal: GRXDV */
#define PIO_PC12B_GRXDV        (1u << 12) /**< \brief Gmac signal: GRXDV */
#define PIO_PD11D_GRXDV        (1u << 11) /**< \brief Gmac signal: GRXDV */
#define PIO_PB17F_GRXER        (1u << 17) /**< \brief Gmac signal: GRXER */
#define PIO_PC13B_GRXER        (1u << 13) /**< \brief Gmac signal: GRXER */
#define PIO_PD12D_GRXER        (1u << 12) /**< \brief Gmac signal: GRXER */
#define PIO_PB5F_GTSUCOMP      (1u << 5)  /**< \brief Gmac signal: GTSUCOMP */
#define PIO_PC9B_GTSUCOMP      (1u << 9)  /**< \brief Gmac signal: GTSUCOMP */
#define PIO_PD0D_GTSUCOMP      (1u << 0)  /**< \brief Gmac signal: GTSUCOMP */
#define PIO_PB20F_GTX0         (1u << 20) /**< \brief Gmac signal: GTX0 */
#define PIO_PC16B_GTX0         (1u << 16) /**< \brief Gmac signal: GTX0 */
#define PIO_PD15D_GTX0         (1u << 15) /**< \brief Gmac signal: GTX0 */
#define PIO_PB21F_GTX1         (1u << 21) /**< \brief Gmac signal: GTX1 */
#define PIO_PC17B_GTX1         (1u << 17) /**< \brief Gmac signal: GTX1 */
#define PIO_PD16D_GTX1         (1u << 16) /**< \brief Gmac signal: GTX1 */
#define PIO_PB12F_GTX2         (1u << 12) /**< \brief Gmac signal: GTX2 */
#define PIO_PC26B_GTX2         (1u << 26) /**< \brief Gmac signal: GTX2 */
#define PIO_PD7D_GTX2          (1u << 7)  /**< \brief Gmac signal: GTX2 */
#define PIO_PB13F_GTX3         (1u << 13) /**< \brief Gmac signal: GTX3 */
#define PIO_PC27B_GTX3         (1u << 27) /**< \brief Gmac signal: GTX3 */
#define PIO_PD8D_GTX3          (1u << 8)  /**< \brief Gmac signal: GTX3 */
#define PIO_PB14F_GTXCK        (1u << 14) /**< \brief Gmac signal: GTXCK */
#define PIO_PC10B_GTXCK        (1u << 10) /**< \brief Gmac signal: GTXCK */
#define PIO_PD9D_GTXCK         (1u << 9)  /**< \brief Gmac signal: GTXCK */
#define PIO_PB15F_GTXEN        (1u << 15) /**< \brief Gmac signal: GTXEN */
#define PIO_PC11B_GTXEN        (1u << 11) /**< \brief Gmac signal: GTXEN */
#define PIO_PD10D_GTXEN        (1u << 10) /**< \brief Gmac signal: GTXEN */
#define PIO_PB6F_GTXER         (1u << 6)  /**< \brief Gmac signal: GTXER */
#define PIO_PC21B_GTXER        (1u << 21) /**< \brief Gmac signal: GTXER */
#define PIO_PD2D_GTXER         (1u << 2)  /**< \brief Gmac signal: GTXER */
/* ========== Pio definition for I2SC0 peripheral ========== */
#define PIO_PC1E_I2SC0_CK      (1u << 1)  /**< \brief I2sc0 signal: I2SC0_CK */
#define PIO_PD19E_I2SC0_CK     (1u << 19) /**< \brief I2sc0 signal: I2SC0_CK */
#define PIO_PC4E_I2SC0_DI0     (1u << 4)  /**< \brief I2sc0 signal: I2SC0_DI0 */
#define PIO_PD22E_I2SC0_DI0    (1u << 22) /**< \brief I2sc0 signal: I2SC0_DI0 */
#define PIO_PC5E_I2SC0_DO0     (1u << 5)  /**< \brief I2sc0 signal: I2SC0_DO0 */
#define PIO_PD23E_I2SC0_DO0    (1u << 23) /**< \brief I2sc0 signal: I2SC0_DO0 */
#define PIO_PC2E_I2SC0_MCK     (1u << 2)  /**< \brief I2sc0 signal: I2SC0_MCK */
#define PIO_PD20E_I2SC0_MCK    (1u << 20) /**< \brief I2sc0 signal: I2SC0_MCK */
#define PIO_PC3E_I2SC0_WS      (1u << 3)  /**< \brief I2sc0 signal: I2SC0_WS */
#define PIO_PD21E_I2SC0_WS     (1u << 21) /**< \brief I2sc0 signal: I2SC0_WS */
/* ========== Pio definition for I2SC1 peripheral ========== */
#define PIO_PA15D_I2SC1_CK     (1u << 15) /**< \brief I2sc1 signal: I2SC1_CK */
#define PIO_PB15D_I2SC1_CK     (1u << 15) /**< \brief I2sc1 signal: I2SC1_CK */
#define PIO_PA17D_I2SC1_DI0    (1u << 17) /**< \brief I2sc1 signal: I2SC1_DI0 */
#define PIO_PB17D_I2SC1_DI0    (1u << 17) /**< \brief I2sc1 signal: I2SC1_DI0 */
#define PIO_PA18D_I2SC1_DO0    (1u << 18) /**< \brief I2sc1 signal: I2SC1_DO0 */
#define PIO_PB18D_I2SC1_DO0    (1u << 18) /**< \brief I2sc1 signal: I2SC1_DO0 */
#define PIO_PA14D_I2SC1_MCK    (1u << 14) /**< \brief I2sc1 signal: I2SC1_MCK */
#define PIO_PB14D_I2SC1_MCK    (1u << 14) /**< \brief I2sc1 signal: I2SC1_MCK */
#define PIO_PA16D_I2SC1_WS     (1u << 16) /**< \brief I2sc1 signal: I2SC1_WS */
#define PIO_PB16D_I2SC1_WS     (1u << 16) /**< \brief I2sc1 signal: I2SC1_WS */
/* ========== Pio definition for ISC peripheral ========== */
#define PIO_PB26F_ISC_D0       (1u << 26) /**< \brief Isc signal: ISC_D0 */
#define PIO_PC9C_ISC_D0        (1u << 9)  /**< \brief Isc signal: ISC_D0 */
#define PIO_PD7E_ISC_D0        (1u << 7)  /**< \brief Isc signal: ISC_D0 */
#define PIO_PB27F_ISC_D1       (1u << 27) /**< \brief Isc signal: ISC_D1 */
#define PIO_PC10C_ISC_D1       (1u << 10) /**< \brief Isc signal: ISC_D1 */
#define PIO_PD8E_ISC_D1        (1u << 8)  /**< \brief Isc signal: ISC_D1 */
#define PIO_PB24F_ISC_D10      (1u << 24) /**< \brief Isc signal: ISC_D10 */
#define PIO_PC19C_ISC_D10      (1u << 19) /**< \brief Isc signal: ISC_D10 */
#define PIO_PD4E_ISC_D10       (1u << 4)  /**< \brief Isc signal: ISC_D10 */
#define PIO_PD18F_ISC_D10      (1u << 18) /**< \brief Isc signal: ISC_D10 */
#define PIO_PB25F_ISC_D11      (1u << 25) /**< \brief Isc signal: ISC_D11 */
#define PIO_PC20C_ISC_D11      (1u << 20) /**< \brief Isc signal: ISC_D11 */
#define PIO_PD3E_ISC_D11       (1u << 3)  /**< \brief Isc signal: ISC_D11 */
#define PIO_PD19F_ISC_D11      (1u << 19) /**< \brief Isc signal: ISC_D11 */
#define PIO_PB28F_ISC_D2       (1u << 28) /**< \brief Isc signal: ISC_D2 */
#define PIO_PC11C_ISC_D2       (1u << 11) /**< \brief Isc signal: ISC_D2 */
#define PIO_PD9E_ISC_D2        (1u << 9)  /**< \brief Isc signal: ISC_D2 */
#define PIO_PB29F_ISC_D3       (1u << 29) /**< \brief Isc signal: ISC_D3 */
#define PIO_PC12C_ISC_D3       (1u << 12) /**< \brief Isc signal: ISC_D3 */
#define PIO_PD10E_ISC_D3       (1u << 10) /**< \brief Isc signal: ISC_D3 */
#define PIO_PB30F_ISC_D4       (1u << 30) /**< \brief Isc signal: ISC_D4 */
#define PIO_PC13C_ISC_D4       (1u << 13) /**< \brief Isc signal: ISC_D4 */
#define PIO_PD11E_ISC_D4       (1u << 11) /**< \brief Isc signal: ISC_D4 */
#define PIO_PD12F_ISC_D4       (1u << 12) /**< \brief Isc signal: ISC_D4 */
#define PIO_PB31F_ISC_D5       (1u << 31) /**< \brief Isc signal: ISC_D5 */
#define PIO_PC14C_ISC_D5       (1u << 14) /**< \brief Isc signal: ISC_D5 */
#define PIO_PD12E_ISC_D5       (1u << 12) /**< \brief Isc signal: ISC_D5 */
#define PIO_PD13F_ISC_D5       (1u << 13) /**< \brief Isc signal: ISC_D5 */
#define PIO_PC0F_ISC_D6        (1u << 0)  /**< \brief Isc signal: ISC_D6 */
#define PIO_PC15C_ISC_D6       (1u << 15) /**< \brief Isc signal: ISC_D6 */
#define PIO_PD13E_ISC_D6       (1u << 13) /**< \brief Isc signal: ISC_D6 */
#define PIO_PD14F_ISC_D6       (1u << 14) /**< \brief Isc signal: ISC_D6 */
#define PIO_PC1F_ISC_D7        (1u << 1)  /**< \brief Isc signal: ISC_D7 */
#define PIO_PC16C_ISC_D7       (1u << 16) /**< \brief Isc signal: ISC_D7 */
#define PIO_PD14E_ISC_D7       (1u << 14) /**< \brief Isc signal: ISC_D7 */
#define PIO_PD15F_ISC_D7       (1u << 15) /**< \brief Isc signal: ISC_D7 */
#define PIO_PC2F_ISC_D8        (1u << 2)  /**< \brief Isc signal: ISC_D8 */
#define PIO_PC17C_ISC_D8       (1u << 17) /**< \brief Isc signal: ISC_D8 */
#define PIO_PD6E_ISC_D8        (1u << 6)  /**< \brief Isc signal: ISC_D8 */
#define PIO_PD16F_ISC_D8       (1u << 16) /**< \brief Isc signal: ISC_D8 */
#define PIO_PC3F_ISC_D9        (1u << 3)  /**< \brief Isc signal: ISC_D9 */
#define PIO_PC18C_ISC_D9       (1u << 18) /**< \brief Isc signal: ISC_D9 */
#define PIO_PD5E_ISC_D9        (1u << 5)  /**< \brief Isc signal: ISC_D9 */
#define PIO_PD17F_ISC_D9       (1u << 17) /**< \brief Isc signal: ISC_D9 */
#define PIO_PC8F_ISC_FIELD     (1u << 8)  /**< \brief Isc signal: ISC_FIELD */
#define PIO_PC25C_ISC_FIELD    (1u << 25) /**< \brief Isc signal: ISC_FIELD */
#define PIO_PD18E_ISC_FIELD    (1u << 18) /**< \brief Isc signal: ISC_FIELD */
#define PIO_PD23F_ISC_FIELD    (1u << 23) /**< \brief Isc signal: ISC_FIELD */
#define PIO_PC6F_ISC_HSYNC     (1u << 6)  /**< \brief Isc signal: ISC_HSYNC */
#define PIO_PC23C_ISC_HSYNC    (1u << 23) /**< \brief Isc signal: ISC_HSYNC */
#define PIO_PD17E_ISC_HSYNC    (1u << 17) /**< \brief Isc signal: ISC_HSYNC */
#define PIO_PD22F_ISC_HSYNC    (1u << 22) /**< \brief Isc signal: ISC_HSYNC */
#define PIO_PC7F_ISC_MCK       (1u << 7)  /**< \brief Isc signal: ISC_MCK */
#define PIO_PC24C_ISC_MCK      (1u << 24) /**< \brief Isc signal: ISC_MCK */
#define PIO_PD2E_ISC_MCK       (1u << 2)  /**< \brief Isc signal: ISC_MCK */
#define PIO_PD11F_ISC_MCK      (1u << 11) /**< \brief Isc signal: ISC_MCK */
#define PIO_PC4F_ISC_PCK       (1u << 4)  /**< \brief Isc signal: ISC_PCK */
#define PIO_PC21C_ISC_PCK      (1u << 21) /**< \brief Isc signal: ISC_PCK */
#define PIO_PD15E_ISC_PCK      (1u << 15) /**< \brief Isc signal: ISC_PCK */
#define PIO_PD20F_ISC_PCK      (1u << 20) /**< \brief Isc signal: ISC_PCK */
#define PIO_PC5F_ISC_VSYNC     (1u << 5)  /**< \brief Isc signal: ISC_VSYNC */
#define PIO_PC22C_ISC_VSYNC    (1u << 22) /**< \brief Isc signal: ISC_VSYNC */
#define PIO_PD16E_ISC_VSYNC    (1u << 16) /**< \brief Isc signal: ISC_VSYNC */
#define PIO_PD21F_ISC_VSYNC    (1u << 21) /**< \brief Isc signal: ISC_VSYNC */
/* ========== Pio definition for LCDC peripheral ========== */
#define PIO_PB11A_LCDDAT0      (1u << 11) /**< \brief Lcdc signal: LCDDAT0 */
#define PIO_PB12A_LCDDAT1      (1u << 12) /**< \brief Lcdc signal: LCDDAT1 */
#define PIO_PB21A_LCDDAT10     (1u << 21) /**< \brief Lcdc signal: LCDDAT10 */
#define PIO_PC16A_LCDDAT10     (1u << 16) /**< \brief Lcdc signal: LCDDAT10 */
#define PIO_PB22A_LCDDAT11     (1u << 22) /**< \brief Lcdc signal: LCDDAT11 */
#define PIO_PC17A_LCDDAT11     (1u << 17) /**< \brief Lcdc signal: LCDDAT11 */
#define PIO_PB23A_LCDDAT12     (1u << 23) /**< \brief Lcdc signal: LCDDAT12 */
#define PIO_PC18A_LCDDAT12     (1u << 18) /**< \brief Lcdc signal: LCDDAT12 */
#define PIO_PB24A_LCDDAT13     (1u << 24) /**< \brief Lcdc signal: LCDDAT13 */
#define PIO_PC19A_LCDDAT13     (1u << 19) /**< \brief Lcdc signal: LCDDAT13 */
#define PIO_PB25A_LCDDAT14     (1u << 25) /**< \brief Lcdc signal: LCDDAT14 */
#define PIO_PC20A_LCDDAT14     (1u << 20) /**< \brief Lcdc signal: LCDDAT14 */
#define PIO_PB26A_LCDDAT15     (1u << 26) /**< \brief Lcdc signal: LCDDAT15 */
#define PIO_PC21A_LCDDAT15     (1u << 21) /**< \brief Lcdc signal: LCDDAT15 */
#define PIO_PB27A_LCDDAT16     (1u << 27) /**< \brief Lcdc signal: LCDDAT16 */
#define PIO_PB28A_LCDDAT17     (1u << 28) /**< \brief Lcdc signal: LCDDAT17 */
#define PIO_PB29A_LCDDAT18     (1u << 29) /**< \brief Lcdc signal: LCDDAT18 */
#define PIO_PC22A_LCDDAT18     (1u << 22) /**< \brief Lcdc signal: LCDDAT18 */
#define PIO_PB30A_LCDDAT19     (1u << 30) /**< \brief Lcdc signal: LCDDAT19 */
#define PIO_PC23A_LCDDAT19     (1u << 23) /**< \brief Lcdc signal: LCDDAT19 */
#define PIO_PB13A_LCDDAT2      (1u << 13) /**< \brief Lcdc signal: LCDDAT2 */
#define PIO_PC10A_LCDDAT2      (1u << 10) /**< \brief Lcdc signal: LCDDAT2 */
#define PIO_PB31A_LCDDAT20     (1u << 31) /**< \brief Lcdc signal: LCDDAT20 */
#define PIO_PC24A_LCDDAT20     (1u << 24) /**< \brief Lcdc signal: LCDDAT20 */
#define PIO_PC0A_LCDDAT21      (1u << 0)  /**< \brief Lcdc signal: LCDDAT21 */
#define PIO_PC25A_LCDDAT21     (1u << 25) /**< \brief Lcdc signal: LCDDAT21 */
#define PIO_PC1A_LCDDAT22      (1u << 1)  /**< \brief Lcdc signal: LCDDAT22 */
#define PIO_PC26A_LCDDAT22     (1u << 26) /**< \brief Lcdc signal: LCDDAT22 */
#define PIO_PC2A_LCDDAT23      (1u << 2)  /**< \brief Lcdc signal: LCDDAT23 */
#define PIO_PC27A_LCDDAT23     (1u << 27) /**< \brief Lcdc signal: LCDDAT23 */
#define PIO_PB14A_LCDDAT3      (1u << 14) /**< \brief Lcdc signal: LCDDAT3 */
#define PIO_PC11A_LCDDAT3      (1u << 11) /**< \brief Lcdc signal: LCDDAT3 */
#define PIO_PB15A_LCDDAT4      (1u << 15) /**< \brief Lcdc signal: LCDDAT4 */
#define PIO_PC12A_LCDDAT4      (1u << 12) /**< \brief Lcdc signal: LCDDAT4 */
#define PIO_PB16A_LCDDAT5      (1u << 16) /**< \brief Lcdc signal: LCDDAT5 */
#define PIO_PC13A_LCDDAT5      (1u << 13) /**< \brief Lcdc signal: LCDDAT5 */
#define PIO_PB17A_LCDDAT6      (1u << 17) /**< \brief Lcdc signal: LCDDAT6 */
#define PIO_PC14A_LCDDAT6      (1u << 14) /**< \brief Lcdc signal: LCDDAT6 */
#define PIO_PB18A_LCDDAT7      (1u << 18) /**< \brief Lcdc signal: LCDDAT7 */
#define PIO_PC15A_LCDDAT7      (1u << 15) /**< \brief Lcdc signal: LCDDAT7 */
#define PIO_PB19A_LCDDAT8      (1u << 19) /**< \brief Lcdc signal: LCDDAT8 */
#define PIO_PB20A_LCDDAT9      (1u << 20) /**< \brief Lcdc signal: LCDDAT9 */
#define PIO_PC8A_LCDDEN        (1u << 8)  /**< \brief Lcdc signal: LCDDEN */
#define PIO_PD1A_LCDDEN        (1u << 1)  /**< \brief Lcdc signal: LCDDEN */
#define PIO_PC4A_LCDDISP       (1u << 4)  /**< \brief Lcdc signal: LCDDISP */
#define PIO_PC29A_LCDDISP      (1u << 29) /**< \brief Lcdc signal: LCDDISP */
#define PIO_PC6A_LCDHSYNC      (1u << 6)  /**< \brief Lcdc signal: LCDHSYNC */
#define PIO_PC31A_LCDHSYNC     (1u << 31) /**< \brief Lcdc signal: LCDHSYNC */
#define PIO_PC7A_LCDPCK        (1u << 7)  /**< \brief Lcdc signal: LCDPCK */
#define PIO_PD0A_LCDPCK        (1u << 0)  /**< \brief Lcdc signal: LCDPCK */
#define PIO_PC3A_LCDPWM        (1u << 3)  /**< \brief Lcdc signal: LCDPWM */
#define PIO_PC28A_LCDPWM       (1u << 28) /**< \brief Lcdc signal: LCDPWM */
#define PIO_PC5A_LCDVSYNC      (1u << 5)  /**< \brief Lcdc signal: LCDVSYNC */
#define PIO_PC30A_LCDVSYNC     (1u << 30) /**< \brief Lcdc signal: LCDVSYNC */
/* ========== Pio definition for MCAN0 peripheral ========== */
#define PIO_PC2C_CANRX0        (1u << 2)  /**< \brief Mcan0 signal: CANRX0 */
#define PIO_PC11E_CANRX0       (1u << 11) /**< \brief Mcan0 signal: CANRX0 */
#define PIO_PC1C_CANTX0        (1u << 1)  /**< \brief Mcan0 signal: CANTX0 */
#define PIO_PC10E_CANTX0       (1u << 10) /**< \brief Mcan0 signal: CANTX0 */
/* ========== Pio definition for MCAN1 peripheral ========== */
#define PIO_PC27D_CANRX1       (1u << 27) /**< \brief Mcan1 signal: CANRX1 */
#define PIO_PC26D_CANTX1       (1u << 26) /**< \brief Mcan1 signal: CANTX1 */
/* ========== Pio definition for PDMIC peripheral ========== */
#define PIO_PB12D_PDMIC_CLK    (1u << 12) /**< \brief Pdmic signal: PDMIC_CLK */
#define PIO_PB27D_PDMIC_CLK    (1u << 27) /**< \brief Pdmic signal: PDMIC_CLK */
#define PIO_PB11D_PDMIC_DAT    (1u << 11) /**< \brief Pdmic signal: PDMIC_DAT */
#define PIO_PB26D_PDMIC_DAT    (1u << 26) /**< \brief Pdmic signal: PDMIC_DAT */
/* ========== Pio definition for PMC peripheral ========== */
#define PIO_PC8D_PCK0          (1u << 8)  /**< \brief Pmc signal: PCK0 */
#define PIO_PD19A_PCK0         (1u << 19) /**< \brief Pmc signal: PCK0 */
#define PIO_PD31E_PCK0         (1u << 31) /**< \brief Pmc signal: PCK0 */
#define PIO_PB13C_PCK1         (1u << 13) /**< \brief Pmc signal: PCK1 */
#define PIO_PB20E_PCK1         (1u << 20) /**< \brief Pmc signal: PCK1 */
#define PIO_PC27C_PCK1         (1u << 27) /**< \brief Pmc signal: PCK1 */
#define PIO_PD6B_PCK1          (1u << 6)  /**< \brief Pmc signal: PCK1 */
#define PIO_PA21B_PCK2         (1u << 21) /**< \brief Pmc signal: PCK2 */
#define PIO_PC28C_PCK2         (1u << 28) /**< \brief Pmc signal: PCK2 */
#define PIO_PD11B_PCK2         (1u << 11) /**< \brief Pmc signal: PCK2 */
/* ========== Pio definition for PWM peripheral ========== */
#define PIO_PB3D_PWMEXTRG0     (1u << 3)  /**< \brief Pwm signal: PWMEXTRG0 */
#define PIO_PB10C_PWMEXTRG1    (1u << 10) /**< \brief Pwm signal: PWMEXTRG1 */
#define PIO_PB2D_PWMFI0        (1u << 2)  /**< \brief Pwm signal: PWMFI0 */
#define PIO_PB9C_PWMFI1        (1u << 9)  /**< \brief Pwm signal: PWMFI1 */
#define PIO_PA30D_PWMH0        (1u << 30) /**< \brief Pwm signal: PWMH0 */
#define PIO_PB0D_PWMH1         (1u << 0)  /**< \brief Pwm signal: PWMH1 */
#define PIO_PB5C_PWMH2         (1u << 5)  /**< \brief Pwm signal: PWMH2 */
#define PIO_PB7C_PWMH3         (1u << 7)  /**< \brief Pwm signal: PWMH3 */
#define PIO_PA31D_PWML0        (1u << 31) /**< \brief Pwm signal: PWML0 */
#define PIO_PB1D_PWML1         (1u << 1)  /**< \brief Pwm signal: PWML1 */
#define PIO_PB6C_PWML2         (1u << 6)  /**< \brief Pwm signal: PWML2 */
#define PIO_PB8C_PWML3         (1u << 8)  /**< \brief Pwm signal: PWML3 */
/* ========== Pio definition for QSPI0 peripheral ========== */
#define PIO_PA1B_QSPI0_CS      (1u << 1)  /**< \brief Qspi0 signal: QSPI0_CS */
#define PIO_PA15C_QSPI0_CS     (1u << 15) /**< \brief Qspi0 signal: QSPI0_CS */
#define PIO_PA23F_QSPI0_CS     (1u << 23) /**< \brief Qspi0 signal: QSPI0_CS */
#define PIO_PA2B_QSPI0_IO0     (1u << 2)  /**< \brief Qspi0 signal: QSPI0_IO0 */
#define PIO_PA16C_QSPI0_IO0    (1u << 16) /**< \brief Qspi0 signal: QSPI0_IO0 */
#define PIO_PA24F_QSPI0_IO0    (1u << 24) /**< \brief Qspi0 signal: QSPI0_IO0 */
#define PIO_PA3B_QSPI0_IO1     (1u << 3)  /**< \brief Qspi0 signal: QSPI0_IO1 */
#define PIO_PA17C_QSPI0_IO1    (1u << 17) /**< \brief Qspi0 signal: QSPI0_IO1 */
#define PIO_PA25F_QSPI0_IO1    (1u << 25) /**< \brief Qspi0 signal: QSPI0_IO1 */
#define PIO_PA4B_QSPI0_IO2     (1u << 4)  /**< \brief Qspi0 signal: QSPI0_IO2 */
#define PIO_PA18C_QSPI0_IO2    (1u << 18) /**< \brief Qspi0 signal: QSPI0_IO2 */
#define PIO_PA26F_QSPI0_IO2    (1u << 26) /**< \brief Qspi0 signal: QSPI0_IO2 */
#define PIO_PA5B_QSPI0_IO3     (1u << 5)  /**< \brief Qspi0 signal: QSPI0_IO3 */
#define PIO_PA19C_QSPI0_IO3    (1u << 19) /**< \brief Qspi0 signal: QSPI0_IO3 */
#define PIO_PA27F_QSPI0_IO3    (1u << 27) /**< \brief Qspi0 signal: QSPI0_IO3 */
#define PIO_PA0B_QSPI0_SCK     (1u << 0)  /**< \brief Qspi0 signal: QSPI0_SCK */
#define PIO_PA14C_QSPI0_SCK    (1u << 14) /**< \brief Qspi0 signal: QSPI0_SCK */
#define PIO_PA22F_QSPI0_SCK    (1u << 22) /**< \brief Qspi0 signal: QSPI0_SCK */
/* ========== Pio definition for QSPI1 peripheral ========== */
#define PIO_PA11B_QSPI1_CS     (1u << 11) /**< \brief Qspi1 signal: QSPI1_CS */
#define PIO_PB6D_QSPI1_CS      (1u << 6)  /**< \brief Qspi1 signal: QSPI1_CS */
#define PIO_PB15E_QSPI1_CS     (1u << 15) /**< \brief Qspi1 signal: QSPI1_CS */
#define PIO_PA7B_QSPI1_IO0     (1u << 7)  /**< \brief Qspi1 signal: QSPI1_IO0 */
#define PIO_PB7D_QSPI1_IO0     (1u << 7)  /**< \brief Qspi1 signal: QSPI1_IO0 */
#define PIO_PB16E_QSPI1_IO0    (1u << 16) /**< \brief Qspi1 signal: QSPI1_IO0 */
#define PIO_PA8B_QSPI1_IO1     (1u << 8)  /**< \brief Qspi1 signal: QSPI1_IO1 */
#define PIO_PB8D_QSPI1_IO1     (1u << 8)  /**< \brief Qspi1 signal: QSPI1_IO1 */
#define PIO_PB17E_QSPI1_IO1    (1u << 17) /**< \brief Qspi1 signal: QSPI1_IO1 */
#define PIO_PA9B_QSPI1_IO2     (1u << 9)  /**< \brief Qspi1 signal: QSPI1_IO2 */
#define PIO_PB9D_QSPI1_IO2     (1u << 9)  /**< \brief Qspi1 signal: QSPI1_IO2 */
#define PIO_PB18E_QSPI1_IO2    (1u << 18) /**< \brief Qspi1 signal: QSPI1_IO2 */
#define PIO_PA10B_QSPI1_IO3    (1u << 10) /**< \brief Qspi1 signal: QSPI1_IO3 */
#define PIO_PB10D_QSPI1_IO3    (1u << 10) /**< \brief Qspi1 signal: QSPI1_IO3 */
#define PIO_PB19E_QSPI1_IO3    (1u << 19) /**< \brief Qspi1 signal: QSPI1_IO3 */
#define PIO_PA6B_QSPI1_SCK     (1u << 6)  /**< \brief Qspi1 signal: QSPI1_SCK */
#define PIO_PB5D_QSPI1_SCK     (1u << 5)  /**< \brief Qspi1 signal: QSPI1_SCK */
#define PIO_PB14E_QSPI1_SCK    (1u << 14) /**< \brief Qspi1 signal: QSPI1_SCK */
/* ========== Pio definition for SDMMC0 peripheral ========== */
#define PIO_PA13A_SDMMC0_CD    (1u << 13) /**< \brief Sdmmc0 signal: SDMMC0_CD */
#define PIO_PA11A_SDMMC0_VDDSEL (1u << 11)/**< \brief Sdmmc0 signal: SDMMC0_VDDSEL */
#define PIO_PA10A_SDMMC0_RSTN  (1u << 10) /**< \brief Sdmmc0 signal: SDMMC0_RSTN */
#define PIO_PA0A_SDMMC0_CK     (1u << 0)  /**< \brief Sdmmc0 signal: SDMMC0_CK */
#define PIO_PA1A_SDMMC0_CMD    (1u << 1)  /**< \brief Sdmmc0 signal: SDMMC0_CMD */
#define PIO_PA12A_SDMMC0_WP    (1u << 12) /**< \brief Sdmmc0 signal: SDMMC0_WP */
#define PIO_PA2A_SDMMC0_DAT0   (1u << 2)  /**< \brief Sdmmc0 signal: SDMMC0_DAT0 */
#define PIO_PA3A_SDMMC0_DAT1   (1u << 3)  /**< \brief Sdmmc0 signal: SDMMC0_DAT1 */
#define PIO_PA4A_SDMMC0_DAT2   (1u << 4)  /**< \brief Sdmmc0 signal: SDMMC0_DAT2 */
#define PIO_PA5A_SDMMC0_DAT3   (1u << 5)  /**< \brief Sdmmc0 signal: SDMMC0_DAT3 */
#define PIO_PA6A_SDMMC0_DAT4   (1u << 6)  /**< \brief Sdmmc0 signal: SDMMC0_DAT4 */
#define PIO_PA7A_SDMMC0_DAT5   (1u << 7)  /**< \brief Sdmmc0 signal: SDMMC0_DAT5 */
#define PIO_PA8A_SDMMC0_DAT6   (1u << 8)  /**< \brief Sdmmc0 signal: SDMMC0_DAT6 */
#define PIO_PA9A_SDMMC0_DAT7   (1u << 9)  /**< \brief Sdmmc0 signal: SDMMC0_DAT7 */
/* ========== Pio definition for SDMMC1 peripheral ========== */
#define PIO_PA30E_SDMMC1_CD    (1u << 30) /**< \brief Sdmmc1 signal: SDMMC1_CD */
#define PIO_PA27E_SDMMC1_RSTN  (1u << 27) /**< \brief Sdmmc1 signal: SDMMC1_RSTN */
#define PIO_PA22E_SDMMC1_CK    (1u << 22) /**< \brief Sdmmc1 signal: SDMMC1_CK */
#define PIO_PA28E_SDMMC1_CMD   (1u << 28) /**< \brief Sdmmc1 signal: SDMMC1_CMD */
#define PIO_PA29E_SDMMC1_WP    (1u << 29) /**< \brief Sdmmc1 signal: SDMMC1_WP */
#define PIO_PA18E_SDMMC1_DAT0  (1u << 18) /**< \brief Sdmmc1 signal: SDMMC1_DAT0 */
#define PIO_PA19E_SDMMC1_DAT1  (1u << 19) /**< \brief Sdmmc1 signal: SDMMC1_DAT1 */
#define PIO_PA20E_SDMMC1_DAT2  (1u << 20) /**< \brief Sdmmc1 signal: SDMMC1_DAT2 */
#define PIO_PA21E_SDMMC1_DAT3  (1u << 21) /**< \brief Sdmmc1 signal: SDMMC1_DAT3 */
/* ========== Pio definition for SPI0 peripheral ========== */
#define PIO_PA16A_SPI0_MISO    (1u << 16) /**< \brief Spi0 signal: SPI0_MISO */
#define PIO_PA31C_SPI0_MISO    (1u << 31) /**< \brief Spi0 signal: SPI0_MISO */
#define PIO_PA15A_SPI0_MOSI    (1u << 15) /**< \brief Spi0 signal: SPI0_MOSI */
#define PIO_PB0C_SPI0_MOSI     (1u << 0)  /**< \brief Spi0 signal: SPI0_MOSI */
#define PIO_PA17A_SPI0_NPCS0   (1u << 17) /**< \brief Spi0 signal: SPI0_NPCS0 */
#define PIO_PA30C_SPI0_NPCS0   (1u << 30) /**< \brief Spi0 signal: SPI0_NPCS0 */
#define PIO_PA18A_SPI0_NPCS1   (1u << 18) /**< \brief Spi0 signal: SPI0_NPCS1 */
#define PIO_PA29C_SPI0_NPCS1   (1u << 29) /**< \brief Spi0 signal: SPI0_NPCS1 */
#define PIO_PA19A_SPI0_NPCS2   (1u << 19) /**< \brief Spi0 signal: SPI0_NPCS2 */
#define PIO_PA27C_SPI0_NPCS2   (1u << 27) /**< \brief Spi0 signal: SPI0_NPCS2 */
#define PIO_PA20A_SPI0_NPCS3   (1u << 20) /**< \brief Spi0 signal: SPI0_NPCS3 */
#define PIO_PA28C_SPI0_NPCS3   (1u << 28) /**< \brief Spi0 signal: SPI0_NPCS3 */
#define PIO_PA14A_SPI0_SPCK    (1u << 14) /**< \brief Spi0 signal: SPI0_SPCK */
#define PIO_PB1C_SPI0_SPCK     (1u << 1)  /**< \brief Spi0 signal: SPI0_SPCK */
/* ========== Pio definition for SPI1 peripheral ========== */
#define PIO_PA24D_SPI1_MISO    (1u << 24) /**< \brief Spi1 signal: SPI1_MISO */
#define PIO_PC3D_SPI1_MISO     (1u << 3)  /**< \brief Spi1 signal: SPI1_MISO */
#define PIO_PD27A_SPI1_MISO    (1u << 27) /**< \brief Spi1 signal: SPI1_MISO */
#define PIO_PA23D_SPI1_MOSI    (1u << 23) /**< \brief Spi1 signal: SPI1_MOSI */
#define PIO_PC2D_SPI1_MOSI     (1u << 2)  /**< \brief Spi1 signal: SPI1_MOSI */
#define PIO_PD26A_SPI1_MOSI    (1u << 26) /**< \brief Spi1 signal: SPI1_MOSI */
#define PIO_PA25D_SPI1_NPCS0   (1u << 25) /**< \brief Spi1 signal: SPI1_NPCS0 */
#define PIO_PC4D_SPI1_NPCS0    (1u << 4)  /**< \brief Spi1 signal: SPI1_NPCS0 */
#define PIO_PD28A_SPI1_NPCS0   (1u << 28) /**< \brief Spi1 signal: SPI1_NPCS0 */
#define PIO_PA26D_SPI1_NPCS1   (1u << 26) /**< \brief Spi1 signal: SPI1_NPCS1 */
#define PIO_PC5D_SPI1_NPCS1    (1u << 5)  /**< \brief Spi1 signal: SPI1_NPCS1 */
#define PIO_PD29A_SPI1_NPCS1   (1u << 29) /**< \brief Spi1 signal: SPI1_NPCS1 */
#define PIO_PA27D_SPI1_NPCS2   (1u << 27) /**< \brief Spi1 signal: SPI1_NPCS2 */
#define PIO_PC6D_SPI1_NPCS2    (1u << 6)  /**< \brief Spi1 signal: SPI1_NPCS2 */
#define PIO_PD30A_SPI1_NPCS2   (1u << 30) /**< \brief Spi1 signal: SPI1_NPCS2 */
#define PIO_PA28D_SPI1_NPCS3   (1u << 28) /**< \brief Spi1 signal: SPI1_NPCS3 */
#define PIO_PC7D_SPI1_NPCS3    (1u << 7)  /**< \brief Spi1 signal: SPI1_NPCS3 */
#define PIO_PA22D_SPI1_SPCK    (1u << 22) /**< \brief Spi1 signal: SPI1_SPCK */
#define PIO_PC1D_SPI1_SPCK     (1u << 1)  /**< \brief Spi1 signal: SPI1_SPCK */
#define PIO_PD25A_SPI1_SPCK    (1u << 25) /**< \brief Spi1 signal: SPI1_SPCK */
/* ========== Pio definition for SSC0 peripheral ========== */
#define PIO_PB23C_RD0          (1u << 23) /**< \brief Ssc0 signal: RD0 */
#define PIO_PC15E_RD0          (1u << 15) /**< \brief Ssc0 signal: RD0 */
#define PIO_PB25C_RF0          (1u << 25) /**< \brief Ssc0 signal: RF0 */
#define PIO_PC17E_RF0          (1u << 17) /**< \brief Ssc0 signal: RF0 */
#define PIO_PB24C_RK0          (1u << 24) /**< \brief Ssc0 signal: RK0 */
#define PIO_PC16E_RK0          (1u << 16) /**< \brief Ssc0 signal: RK0 */
#define PIO_PB22C_TD0          (1u << 22) /**< \brief Ssc0 signal: TD0 */
#define PIO_PC14E_TD0          (1u << 14) /**< \brief Ssc0 signal: TD0 */
#define PIO_PB21C_TF0          (1u << 21) /**< \brief Ssc0 signal: TF0 */
#define PIO_PC13E_TF0          (1u << 13) /**< \brief Ssc0 signal: TF0 */
#define PIO_PB20C_TK0          (1u << 20) /**< \brief Ssc0 signal: TK0 */
#define PIO_PC12E_TK0          (1u << 12) /**< \brief Ssc0 signal: TK0 */
/* ========== Pio definition for SSC1 peripheral ========== */
#define PIO_PA17B_RD1          (1u << 17) /**< \brief Ssc1 signal: RD1 */
#define PIO_PB17C_RD1          (1u << 17) /**< \brief Ssc1 signal: RD1 */
#define PIO_PA19B_RF1          (1u << 19) /**< \brief Ssc1 signal: RF1 */
#define PIO_PB19C_RF1          (1u << 19) /**< \brief Ssc1 signal: RF1 */
#define PIO_PA18B_RK1          (1u << 18) /**< \brief Ssc1 signal: RK1 */
#define PIO_PB18C_RK1          (1u << 18) /**< \brief Ssc1 signal: RK1 */
#define PIO_PA16B_TD1          (1u << 16) /**< \brief Ssc1 signal: TD1 */
#define PIO_PB16C_TD1          (1u << 16) /**< \brief Ssc1 signal: TD1 */
#define PIO_PA15B_TF1          (1u << 15) /**< \brief Ssc1 signal: TF1 */
#define PIO_PB15C_TF1          (1u << 15) /**< \brief Ssc1 signal: TF1 */
#define PIO_PA14B_TK1          (1u << 14) /**< \brief Ssc1 signal: TK1 */
#define PIO_PB14C_TK1          (1u << 14) /**< \brief Ssc1 signal: TK1 */
/* ========== Pio definition for TC0 peripheral ========== */
#define PIO_PA21D_TCLK0        (1u << 21) /**< \brief Tc0 signal: TCLK0 */
#define PIO_PA29A_TCLK1        (1u << 29) /**< \brief Tc0 signal: TCLK1 */
#define PIO_PC5C_TCLK1         (1u << 5)  /**< \brief Tc0 signal: TCLK1 */
#define PIO_PD13A_TCLK1        (1u << 13) /**< \brief Tc0 signal: TCLK1 */
#define PIO_PB5A_TCLK2         (1u << 5)  /**< \brief Tc0 signal: TCLK2 */
#define PIO_PB24D_TCLK2        (1u << 24) /**< \brief Tc0 signal: TCLK2 */
#define PIO_PD22A_TCLK2        (1u << 22) /**< \brief Tc0 signal: TCLK2 */
#define PIO_PA19D_TIOA0        (1u << 19) /**< \brief Tc0 signal: TIOA0 */
#define PIO_PA27A_TIOA1        (1u << 27) /**< \brief Tc0 signal: TIOA1 */
#define PIO_PC3C_TIOA1         (1u << 3)  /**< \brief Tc0 signal: TIOA1 */
#define PIO_PD11A_TIOA1        (1u << 11) /**< \brief Tc0 signal: TIOA1 */
#define PIO_PB6A_TIOA2         (1u << 6)  /**< \brief Tc0 signal: TIOA2 */
#define PIO_PB22D_TIOA2        (1u << 22) /**< \brief Tc0 signal: TIOA2 */
#define PIO_PD20A_TIOA2        (1u << 20) /**< \brief Tc0 signal: TIOA2 */
#define PIO_PA20D_TIOB0        (1u << 20) /**< \brief Tc0 signal: TIOB0 */
#define PIO_PA28A_TIOB1        (1u << 28) /**< \brief Tc0 signal: TIOB1 */
#define PIO_PC4C_TIOB1         (1u << 4)  /**< \brief Tc0 signal: TIOB1 */
#define PIO_PD12A_TIOB1        (1u << 12) /**< \brief Tc0 signal: TIOB1 */
#define PIO_PB7A_TIOB2         (1u << 7)  /**< \brief Tc0 signal: TIOB2 */
#define PIO_PB23D_TIOB2        (1u << 23) /**< \brief Tc0 signal: TIOB2 */
#define PIO_PD21A_TIOB2        (1u << 21) /**< \brief Tc0 signal: TIOB2 */
/* ========== Pio definition for TC1 peripheral ========== */
#define PIO_PB8A_TCLK3         (1u << 8)  /**< \brief Tc1 signal: TCLK3 */
#define PIO_PB21D_TCLK3        (1u << 21) /**< \brief Tc1 signal: TCLK3 */
#define PIO_PD31D_TCLK3        (1u << 31) /**< \brief Tc1 signal: TCLK3 */
#define PIO_PA11D_TCLK4        (1u << 11) /**< \brief Tc1 signal: TCLK4 */
#define PIO_PC11D_TCLK4        (1u << 11) /**< \brief Tc1 signal: TCLK4 */
#define PIO_PA8D_TCLK5         (1u << 8)  /**< \brief Tc1 signal: TCLK5 */
#define PIO_PB30D_TCLK5        (1u << 30) /**< \brief Tc1 signal: TCLK5 */
#define PIO_PB9A_TIOA3         (1u << 9)  /**< \brief Tc1 signal: TIOA3 */
#define PIO_PB19D_TIOA3        (1u << 19) /**< \brief Tc1 signal: TIOA3 */
#define PIO_PD29D_TIOA3        (1u << 29) /**< \brief Tc1 signal: TIOA3 */
#define PIO_PA9D_TIOA4         (1u << 9)  /**< \brief Tc1 signal: TIOA4 */
#define PIO_PC9D_TIOA4         (1u << 9)  /**< \brief Tc1 signal: TIOA4 */
#define PIO_PA6D_TIOA5         (1u << 6)  /**< \brief Tc1 signal: TIOA5 */
#define PIO_PB28D_TIOA5        (1u << 28) /**< \brief Tc1 signal: TIOA5 */
#define PIO_PB10A_TIOB3        (1u << 10) /**< \brief Tc1 signal: TIOB3 */
#define PIO_PB20D_TIOB3        (1u << 20) /**< \brief Tc1 signal: TIOB3 */
#define PIO_PD30D_TIOB3        (1u << 30) /**< \brief Tc1 signal: TIOB3 */
#define PIO_PA10D_TIOB4        (1u << 10) /**< \brief Tc1 signal: TIOB4 */
#define PIO_PC10D_TIOB4        (1u << 10) /**< \brief Tc1 signal: TIOB4 */
#define PIO_PA7D_TIOB5         (1u << 7)  /**< \brief Tc1 signal: TIOB5 */
#define PIO_PB29D_TIOB5        (1u << 29) /**< \brief Tc1 signal: TIOB5 */
/* ========== Pio definition for TWIHS0 peripheral ========== */
#define PIO_PC0D_TWCK0         (1u << 0)  /**< \brief Twihs0 signal: TWCK0 */
#define PIO_PC28E_TWCK0        (1u << 28) /**< \brief Twihs0 signal: TWCK0 */
#define PIO_PD22B_TWCK0        (1u << 22) /**< \brief Twihs0 signal: TWCK0 */
#define PIO_PD30E_TWCK0        (1u << 30) /**< \brief Twihs0 signal: TWCK0 */
#define PIO_PB31D_TWD0         (1u << 31) /**< \brief Twihs0 signal: TWD0 */
#define PIO_PC27E_TWD0         (1u << 27) /**< \brief Twihs0 signal: TWD0 */
#define PIO_PD21B_TWD0         (1u << 21) /**< \brief Twihs0 signal: TWD0 */
#define PIO_PD29E_TWD0         (1u << 29) /**< \brief Twihs0 signal: TWD0 */
/* ========== Pio definition for TWIHS1 peripheral ========== */
#define PIO_PC7C_TWCK1         (1u << 7)  /**< \brief Twihs1 signal: TWCK1 */
#define PIO_PD5A_TWCK1         (1u << 5)  /**< \brief Twihs1 signal: TWCK1 */
#define PIO_PD20B_TWCK1        (1u << 20) /**< \brief Twihs1 signal: TWCK1 */
#define PIO_PC6C_TWD1          (1u << 6)  /**< \brief Twihs1 signal: TWD1 */
#define PIO_PD4A_TWD1          (1u << 4)  /**< \brief Twihs1 signal: TWD1 */
#define PIO_PD19B_TWD1         (1u << 19) /**< \brief Twihs1 signal: TWD1 */
/* ========== Pio definition for UART0 peripheral ========== */
#define PIO_PB26C_URXD0        (1u << 26) /**< \brief Uart0 signal: URXD0 */
#define PIO_PB27C_UTXD0        (1u << 27) /**< \brief Uart0 signal: UTXD0 */
/* ========== Pio definition for UART1 peripheral ========== */
#define PIO_PC7E_URXD1         (1u << 7)  /**< \brief Uart1 signal: URXD1 */
#define PIO_PD2A_URXD1         (1u << 2)  /**< \brief Uart1 signal: URXD1 */
#define PIO_PC8E_UTXD1         (1u << 8)  /**< \brief Uart1 signal: UTXD1 */
#define PIO_PD3A_UTXD1         (1u << 3)  /**< \brief Uart1 signal: UTXD1 */
/* ========== Pio definition for UART2 peripheral ========== */
#define PIO_PD4B_URXD2         (1u << 4)  /**< \brief Uart2 signal: URXD2 */
#define PIO_PD19C_URXD2        (1u << 19) /**< \brief Uart2 signal: URXD2 */
#define PIO_PD23A_URXD2        (1u << 23) /**< \brief Uart2 signal: URXD2 */
#define PIO_PD5B_UTXD2         (1u << 5)  /**< \brief Uart2 signal: UTXD2 */
#define PIO_PD20C_UTXD2        (1u << 20) /**< \brief Uart2 signal: UTXD2 */
#define PIO_PD24A_UTXD2        (1u << 24) /**< \brief Uart2 signal: UTXD2 */
/* ========== Pio definition for UART3 peripheral ========== */
#define PIO_PB11C_URXD3        (1u << 11) /**< \brief Uart3 signal: URXD3 */
#define PIO_PC12D_URXD3        (1u << 12) /**< \brief Uart3 signal: URXD3 */
#define PIO_PC31C_URXD3        (1u << 31) /**< \brief Uart3 signal: URXD3 */
#define PIO_PB12C_UTXD3        (1u << 12) /**< \brief Uart3 signal: UTXD3 */
#define PIO_PC13D_UTXD3        (1u << 13) /**< \brief Uart3 signal: UTXD3 */
#define PIO_PD0C_UTXD3         (1u << 0)  /**< \brief Uart3 signal: UTXD3 */
/* ========== Pio definition for UART4 peripheral ========== */
#define PIO_PB3A_URXD4         (1u << 3)  /**< \brief Uart4 signal: URXD4 */
#define PIO_PB4A_UTXD4         (1u << 4)  /**< \brief Uart4 signal: UTXD4 */
/* ========== Pio indexes ========== */
#define PIO_PA0_IDX            0
#define PIO_PA1_IDX            1
#define PIO_PA2_IDX            2
#define PIO_PA3_IDX            3
#define PIO_PA4_IDX            4
#define PIO_PA5_IDX            5
#define PIO_PA6_IDX            6
#define PIO_PA7_IDX            7
#define PIO_PA8_IDX            8
#define PIO_PA9_IDX            9
#define PIO_PA10_IDX           10
#define PIO_PA11_IDX           11
#define PIO_PA12_IDX           12
#define PIO_PA13_IDX           13
#define PIO_PA14_IDX           14
#define PIO_PA15_IDX           15
#define PIO_PA16_IDX           16
#define PIO_PA17_IDX           17
#define PIO_PA18_IDX           18
#define PIO_PA19_IDX           19
#define PIO_PA20_IDX           20
#define PIO_PA21_IDX           21
#define PIO_PA22_IDX           22
#define PIO_PA23_IDX           23
#define PIO_PA24_IDX           24
#define PIO_PA25_IDX           25
#define PIO_PA26_IDX           26
#define PIO_PA27_IDX           27
#define PIO_PA28_IDX           28
#define PIO_PA29_IDX           29
#define PIO_PA30_IDX           30
#define PIO_PA31_IDX           31
#define PIO_PB0_IDX            32
#define PIO_PB1_IDX            33
#define PIO_PB2_IDX            34
#define PIO_PB3_IDX            35
#define PIO_PB4_IDX            36
#define PIO_PB5_IDX            37
#define PIO_PB6_IDX            38
#define PIO_PB7_IDX            39
#define PIO_PB8_IDX            40
#define PIO_PB9_IDX            41
#define PIO_PB10_IDX           42
#define PIO_PB11_IDX           43
#define PIO_PB12_IDX           44
#define PIO_PB13_IDX           45
#define PIO_PB14_IDX           46
#define PIO_PB15_IDX           47
#define PIO_PB16_IDX           48
#define PIO_PB17_IDX           49
#define PIO_PB18_IDX           50
#define PIO_PB19_IDX           51
#define PIO_PB20_IDX           52
#define PIO_PB21_IDX           53
#define PIO_PB22_IDX           54
#define PIO_PB23_IDX           55
#define PIO_PB24_IDX           56
#define PIO_PB25_IDX           57
#define PIO_PB26_IDX           58
#define PIO_PB27_IDX           59
#define PIO_PB28_IDX           60
#define PIO_PB29_IDX           61
#define PIO_PB30_IDX           62
#define PIO_PB31_IDX           63
#define PIO_PC0_IDX            64
#define PIO_PC1_IDX            65
#define PIO_PC2_IDX            66
#define PIO_PC3_IDX            67
#define PIO_PC4_IDX            68
#define PIO_PC5_IDX            69
#define PIO_PC6_IDX            70
#define PIO_PC7_IDX            71
#define PIO_PC8_IDX            72
#define PIO_PC9_IDX            73
#define PIO_PC10_IDX           74
#define PIO_PC11_IDX           75
#define PIO_PC12_IDX           76
#define PIO_PC13_IDX           77
#define PIO_PC14_IDX           78
#define PIO_PC15_IDX           79
#define PIO_PC16_IDX           80
#define PIO_PC17_IDX           81
#define PIO_PC18_IDX           82
#define PIO_PC19_IDX           83
#define PIO_PC20_IDX           84
#define PIO_PC21_IDX           85
#define PIO_PC22_IDX           86
#define PIO_PC23_IDX           87
#define PIO_PC24_IDX           88
#define PIO_PC25_IDX           89
#define PIO_PC26_IDX           90
#define PIO_PC27_IDX           91
#define PIO_PC28_IDX           92
#define PIO_PC29_IDX           93
#define PIO_PC30_IDX           94
#define PIO_PC31_IDX           95
#define PIO_PD0_IDX            96
#define PIO_PD1_IDX            97
#define PIO_PD2_IDX            98
#define PIO_PD3_IDX            99
#define PIO_PD4_IDX            100
#define PIO_PD5_IDX            101
#define PIO_PD6_IDX            102
#define PIO_PD7_IDX            103
#define PIO_PD8_IDX            104
#define PIO_PD9_IDX            105
#define PIO_PD10_IDX           106
#define PIO_PD11_IDX           107
#define PIO_PD12_IDX           108
#define PIO_PD13_IDX           109
#define PIO_PD14_IDX           110
#define PIO_PD15_IDX           111
#define PIO_PD16_IDX           112
#define PIO_PD17_IDX           113
#define PIO_PD18_IDX           114
#define PIO_PD19_IDX           115
#define PIO_PD20_IDX           116
#define PIO_PD21_IDX           117
#define PIO_PD22_IDX           118
#define PIO_PD23_IDX           119
#define PIO_PD24_IDX           120
#define PIO_PD25_IDX           121
#define PIO_PD26_IDX           122
#define PIO_PD27_IDX           123
#define PIO_PD28_IDX           124
#define PIO_PD29_IDX           125
#define PIO_PD30_IDX           126
#define PIO_PD31_IDX           127

#endif /* _SAMA5D27_PIO_ */
