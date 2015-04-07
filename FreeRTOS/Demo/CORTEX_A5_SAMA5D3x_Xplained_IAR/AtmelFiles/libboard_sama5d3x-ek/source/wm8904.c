/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
  * \file
  *
  * Implementation WM8904 driver.
  *
  */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Read data from WM8904 Register.
 *
 * \param pTwid   Pointer to twi driver structure
 * \param device  Twi slave address.
 * \param regAddr Register address to read.
 * \return value in the given register.
 */
uint16_t WM8904_Read(Twid *pTwid,
                     uint32_t device,
                     uint32_t regAddr)
{
    uint16_t bitsDataRegister;
    uint8_t Tdata[2]={0,0};

    TWID_Read(pTwid, device, regAddr, 1, Tdata, 2, 0);
    bitsDataRegister = (Tdata[0] << 8) | Tdata[1];
    return bitsDataRegister;
}

/**
 * \brief  Write data to WM8904 Register.
 *
 * \param pTwid   Pointer to twi driver structure
 * \param device  Twi slave address.
 * \param regAddr Register address to read.
 * \param data    Data to write
 */
void WM8904_Write(Twid *pTwid,
                  uint32_t device,
                  uint32_t regAddr,
                  uint16_t data)
{
    uint8_t tmpData[2];
    
    tmpData[0] = (data & 0xff00) >> 8;
    tmpData[1] = data & 0xff;
    TWID_Write(pTwid, device, regAddr, 1, tmpData, 2, 0);
}

/**
 * \brief  Init WM8904 to DAC mode.
 *
 * \param pTwid   Pointer to twi driver structure
 * \param device  Twi slave address.
  * \return 0.
 */
uint8_t WM8904_Init(Twid     *pTwid,
                    uint32_t device)
 
{
    /* Software reset */
    WM8904_Write(pTwid, device, WM8904_REG_RESET, 0x0000);

    /* POBCTRL=1, ISEL=10, STARTUP_BIAS_ENA=0, BIAS_ENA=1  */
    WM8904_Write(pTwid, device, WM8904_REG_BIAS_CTRL0, 0x0019);

    /* VMID_BUF_ENA=1, VMID_RES=01, VMID_ENA=1   */
    WM8904_Write(pTwid, device, WM8904_REG_VMID_CTRL0, 0x0043);
    
    /* MICDET_ENA=1, MICBIAS_ENA=1   */
    WM8904_Write(pTwid, device, WM8904_REG_MICBIAS_CTRL0, 0x0003);

    /* ?  */
    WM8904_Write(pTwid, device, WM8904_REG_BIAS_CTRL1, 0xC000);

    /* INL_ENA=1, INR_ENA=1  */
    WM8904_Write(pTwid, device, WM8904_REG_POWER_MANG0, 0x0003);

    /* HPL_PGA_ENA=1, HPR_PGA_ENA=1  */
    WM8904_Write(pTwid, device, WM8904_REG_POWER_MANG2, 0x0003);

    /* DACL_ENA=1, DACR_ENA=1, ADCL_ENA=1, ADCR_ENA=1  */
    WM8904_Write(pTwid, device, WM8904_REG_POWER_MANG6, 0x000F);

    /* TOCLK_RATE_DIV16=0,TOCLK_RATE_X4=0, SR_MODE=0, MCLK_DIV=0  */
    WM8904_Write(pTwid, device, WM8904_REG_CLOCK_RATE0, 0x845E);

    /* SYSCLK_SRC=1, CLK_SYS_ENA=1, CLK_DSP_ENA=1  */
    WM8904_Write(pTwid, device, WM8904_REG_CLOCK_RATE2, 0x4006);

    /* AIFADC_TCM=0, AIFADC_TCM_CHAN=0, BCLK_DIR=1 */
    WM8904_Write(pTwid, device, WM8904_REG_AUD_INF1, 0x404A);

    /* LRCLK=1, LRCLK_RATE=0x40 */
    WM8904_Write(pTwid, device, WM8904_REG_AUD_INF3, 0x0840);

    /* DAC_MCNO=0, DAC_SB_FILT=0, DAC_MUTERATE=0, DAC_MUTE=0 */
    WM8904_Write(pTwid, device, WM8904_REG_ADC_DIG1, 0x0000);

    /* LINMUTE=0, LIN_VOL= 0 db */
    WM8904_Write(pTwid, device, WM8904_REG_ANALOGUE_LIN0, 0x0005);

    /* RINMUTE=0, RIN_VOL= 0 db */
    WM8904_Write(pTwid, device, WM8904_REG_ANALOGUE_RIN0, 0x0005);

    /* IN2L */
    WM8904_Write(pTwid, device, WM8904_REG_ANALOGUE_LIN1, 0x0010);

    /* IN2R*/
    WM8904_Write(pTwid, device, WM8904_REG_ANALOGUE_RIN1, 0x0010);

    /* HPOUTR_MUTE=1, HPOUTRZC=1, HPOUTR_VOL=0x1D */
    WM8904_Write(pTwid, device, WM8904_REG_ANALOGUE_ROUT1, 0x00AD);

    /* DCS_ENA_CHAN_1=1, DCS_ENA_CHAN_0=1 */
    WM8904_Write(pTwid, device, WM8904_REG_DC_SERVO0, 0x0003);

    /* HPL_RMV_SHORT=1, HPL_ENA_OUTp=1, HPL_ENA_DLY=1, HPL_ENA=1
       HPR_RMV_SHORT=1, HPR_ENA_OUTp=1, HPR_ENA_DLY=1, HPR_ENA=1 */
    WM8904_Write(pTwid, device, WM8904_REG_ANALOGUE_HP0, 0x00FF);

    /* CP_ENA=1 */
    WM8904_Write(pTwid, device, WM8904_REG_CHARGE_PUMP0, 0x0001);

    /* CP_DYN_PWR=1 */
    WM8904_Write(pTwid, device, WM8904_REG_CLASS0, 0x0005);

    /* FLL_FRACN_ENA=0, FLL_ENA=0 */
    WM8904_Write(pTwid, device, WM8904_REG_FLL_CRTL1, 0x0000);
    /* FLL_FRACN_ENA=1, FLL_ENA=1 */
    WM8904_Write(pTwid, device, WM8904_REG_FLL_CRTL1, 0x0005);
    /* FLL_FRATIO=4, FLL_OUTDIV= 7 */
    WM8904_Write(pTwid, device, WM8904_REG_FLL_CRTL2, 0x0704);
    /* Fractional multiply for Fref = 0x8000 */
    WM8904_Write(pTwid, device, WM8904_REG_FLL_CRTL3, 0x8000);
    /* FLL_GAIN=0, FLL_N=0x176 */
    WM8904_Write(pTwid, device, WM8904_REG_FLL_CRTL4, 0x1760);
    WM8904_Write(pTwid, device, WM8904_REG_END, 0x55AA);
    return 0;
}  

void WM8904_IN2R_IN1L(Twid *pTwid, uint32_t device)
{
    //{ 0x0005, 44},  /** R44  - Analogue Left Input 0 */ 
    //{ 0x0005, 45},  /** R45  - Analogue Right Input 0 */ 
    //{ 0x0000, 46},  /** R46  - Analogue Left Input 1 */ 
    //{ 0x0010, 47},  /** R47  - Analogue Right Input 1 */
    WM8904_Write(pTwid, device, 0x2C, 0x0008);
    WM8904_Write(pTwid, device, 0x2D, 0x0005);
    WM8904_Write(pTwid, device, 0x2E, 0x0000);
    WM8904_Write(pTwid, device, 0x2F, 0x0010);
}
