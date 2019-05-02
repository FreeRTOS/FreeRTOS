/**************************************************************************//**
 * @file     sys.c
 * @version  V3.00
 * @brief    M2351 series System Manager (SYS) driver source file
 *
 * @note
 * Copyright (C) 2016 Nuvoton Technology Corp. All rights reserved.
*****************************************************************************/
#include "NuMicro.h"
/** @addtogroup Standard_Driver Standard Driver
  @{
*/

/** @addtogroup SYS_Driver SYS Driver
  @{
*/


/** @addtogroup SYS_EXPORTED_FUNCTIONS SYS Exported Functions
  @{
*/

/**
  * @brief      Clear reset source
  * @param[in]  u32Src is system reset source. Including :
  *             - \ref SYS_RSTSTS_CPULKRF_Msk
  *             - \ref SYS_RSTSTS_CPURF_Msk
  *             - \ref SYS_RSTSTS_SYSRF_Msk
  *             - \ref SYS_RSTSTS_BODRF_Msk
  *             - \ref SYS_RSTSTS_LVRF_Msk
  *             - \ref SYS_RSTSTS_WDTRF_Msk
  *             - \ref SYS_RSTSTS_PINRF_Msk
  *             - \ref SYS_RSTSTS_PORF_Msk
  * @return     None
  * @details    This function clear the selected system reset source.
  */
void SYS_ClearResetSrc(uint32_t u32Src)
{
    SYS->RSTSTS = u32Src;
}

/**
  * @brief      Get Brown-out detector output status
  * @param      None
  * @retval     0 System voltage is higher than BODVL setting or BODEN is 0.
  * @retval     1 System voltage is lower than BODVL setting.
  * @details    This function get Brown-out detector output status.
  */
uint32_t SYS_GetBODStatus(void)
{
    return ((SYS->BODCTL & SYS_BODCTL_BODOUT_Msk) >> SYS_BODCTL_BODOUT_Pos);
}

/**
  * @brief      Get reset status register value
  * @param      None
  * @return     Reset source
  * @details    This function get the system reset status register value.
  */
uint32_t SYS_GetResetSrc(void)
{
    return (SYS->RSTSTS);
}

/**
  * @brief      Check if register is locked nor not
  * @param      None
  * @retval     0 Write-protection function is disabled.
  *             1 Write-protection function is enabled.
  * @details    This function check register write-protection bit setting.
  */
uint32_t SYS_IsRegLocked(void)
{
    return SYS->REGLCTL & 1UL ? 0UL : 1UL;
}

/**
  * @brief      Get product ID
  * @param      None
  * @return     Product ID
  * @details    This function get product ID.
  */
uint32_t  SYS_ReadPDID(void)
{
    return SYS->PDID;
}

/**
  * @brief      Reset chip with chip reset
  * @param      None
  * @return     None
  * @details    This function reset chip with chip reset.
  *             The register write-protection function should be disabled before using this function.
  */
void SYS_ResetChip(void)
{
    SYS->IPRST0 |= SYS_IPRST0_CHIPRST_Msk;
}

/**
  * @brief      Reset chip with CPU reset
  * @param      None
  * @return     None
  * @details    This function reset CPU with CPU reset.
  *             The register write-protection function should be disabled before using this function.
  */
void SYS_ResetCPU(void)
{
    SYS->IPRST0 |= SYS_IPRST0_CPURST_Msk;
}

/**
  * @brief      Reset selected module
  * @param[in]  u32ModuleIndex is module index. Including :
  *             - \ref PDMA0_RST
  *             - \ref PDMA1_RST
  *             - \ref EBI_RST
  *             - \ref USBH_RST
  *             - \ref SDH0_RST
  *             - \ref CRC_RST
  *             - \ref CRPT_RST
  *             - \ref GPIO_RST
  *             - \ref TMR0_RST
  *             - \ref TMR1_RST
  *             - \ref TMR2_RST
  *             - \ref TMR3_RST
  *             - \ref ACMP01_RST
  *             - \ref I2C0_RST
  *             - \ref I2C1_RST
  *             - \ref I2C2_RST
  *             - \ref QSPI0_RST
  *             - \ref SPI0_RST
  *             - \ref SPI1_RST
  *             - \ref SPI2_RST
  *             - \ref SPI3_RST
  *             - \ref UART0_RST
  *             - \ref UART1_RST
  *             - \ref UART2_RST
  *             - \ref UART3_RST
  *             - \ref UART4_RST
  *             - \ref UART5_RST
  *             - \ref CAN0_RST
  *             - \ref OTG_RST
  *             - \ref USBD_RST
  *             - \ref EADC_RST
  *             - \ref I2S0_RST
  *             - \ref TRNG_RST
  *             - \ref SC0_RST
  *             - \ref SC1_RST
  *             - \ref SC2_RST
  *             - \ref USCI0_RST
  *             - \ref USCI1_RST
  *             - \ref DAC_RST
  *             - \ref EPWM0_RST
  *             - \ref EPWM1_RST
  *             - \ref BPWM0_RST
  *             - \ref BPWM1_RST
  *             - \ref QEI0_RST
  *             - \ref QEI1_RST
  *             - \ref ECAP0_RST
  *             - \ref ECAP1_RST
  * @return     None
  * @details    This function reset selected module.
  */
void SYS_ResetModule(uint32_t u32ModuleIndex)
{
    uint32_t u32TmpVal = 0UL, u32TmpAddr = 0UL;

    /* Generate reset signal to the corresponding module */
    u32TmpVal = (1UL << (u32ModuleIndex & 0x00ffffffUL));
    u32TmpAddr = (uint32_t)&SYS->IPRST0 + ((u32ModuleIndex >> 24UL));
    *(uint32_t *)u32TmpAddr |= u32TmpVal;

    /* Release corresponding module from reset state */
    u32TmpVal = ~(1UL << (u32ModuleIndex & 0x00ffffffUL));
    *(uint32_t *)u32TmpAddr &= u32TmpVal;
}

/**
  * @brief      Enable and configure Brown-out detector function
  * @param[in]  i32Mode is reset or interrupt mode. Including :
  *             - \ref SYS_BODCTL_BOD_RST_EN
  *             - \ref SYS_BODCTL_BOD_INTERRUPT_EN
  * @param[in]  u32BODLevel is Brown-out voltage level. Including :
  *             - \ref SYS_BODCTL_BODVL_1_6V
  *             - \ref SYS_BODCTL_BODVL_1_8V
  *             - \ref SYS_BODCTL_BODVL_2_0V
  *             - \ref SYS_BODCTL_BODVL_2_2V
  *             - \ref SYS_BODCTL_BODVL_2_4V
  *             - \ref SYS_BODCTL_BODVL_2_6V
  *             - \ref SYS_BODCTL_BODVL_2_8V
  *             - \ref SYS_BODCTL_BODVL_3_0V
  * @return     None
  * @details    This function configure Brown-out detector reset or interrupt mode, enable Brown-out function and set Brown-out voltage level.
  *             The register write-protection function should be disabled before using this function.
  */
void SYS_EnableBOD(int32_t i32Mode, uint32_t u32BODLevel)
{
    /* Enable Brown-out Detector function */
    SYS->BODCTL |= SYS_BODCTL_BODEN_Msk;

    /* Enable Brown-out interrupt or reset function */
    SYS->BODCTL = (SYS->BODCTL & ~SYS_BODCTL_BODRSTEN_Msk) | (uint32_t)i32Mode;

    /* Select Brown-out Detector threshold voltage */
    SYS->BODCTL = (SYS->BODCTL & ~SYS_BODCTL_BODVL_Msk) | u32BODLevel;
}

/**
  * @brief      Disable Brown-out detector function
  * @param      None
  * @return     None
  * @details    This function disable Brown-out detector function.
  *             The register write-protection function should be disabled before using this function.
  */
void SYS_DisableBOD(void)
{
    SYS->BODCTL &= ~SYS_BODCTL_BODEN_Msk;
}


/**
  * @brief      Set Power Level
  * @param[in]  u32PowerLevel is power level setting. Including :
  *             - \ref SYS_PLCTL_PLSEL_PL0
  *             - \ref SYS_PLCTL_PLSEL_PL1
  * @return     None
  * @details    This function select power level.
  *             The register write-protection function should be disabled before using this function.
  */
void SYS_SetPowerLevel(uint32_t u32PowerLevel)
{
    /* Set power voltage level */
    SYS->PLCTL = (SYS->PLCTL & (~SYS_PLCTL_PLSEL_Msk)) | (u32PowerLevel);
}


/**
  * @brief      Set Main Voltage Regulator Type
  * @param[in]  u32PowerRegulator is main voltage regulator type. Including :
  *             - \ref SYS_PLCTL_MVRS_LDO
  *             - \ref SYS_PLCTL_MVRS_DCDC
  * @retval     0  main voltage regulator type setting is not finished
  * @retval     1  main voltage regulator type setting is finished
  * @details    This function set main voltage regulator type.
  *             The main voltage regulator type setting to DCDC cannot finished if the inductor is not detected.
  *             The register write-protection function should be disabled before using this function.
  */
uint32_t SYS_SetPowerRegulator(uint32_t u32PowerRegulator)
{
    int32_t i32TimeOutCnt = 400;
    uint32_t u32Ret = 1U;
    uint32_t u32PowerRegStatus;

    /* Get main voltage regulator type status */
    u32PowerRegStatus = SYS->PLSTS & SYS_PLSTS_CURMVR_Msk;

    /* Set main voltage regulator type */
    if((u32PowerRegulator == SYS_PLCTL_MVRS_DCDC) && (u32PowerRegStatus == SYS_PLSTS_CURMVR_LDO))
    {

        /* Set main voltage regulator type to DCDC if status is LDO */
        SYS->PLCTL |= SYS_PLCTL_MVRS_Msk;

        /* Wait induction detection and main voltage regulator type change ready */
        while((SYS->PLSTS & SYS_PLSTS_CURMVR_Msk) != SYS_PLSTS_CURMVR_DCDC)
        {
            if(i32TimeOutCnt-- <= 0)
            {
                u32Ret = 0U;    /* Main voltage regulator type change time-out */
                break;
            }
        }

    }
    else if(u32PowerRegulator == SYS_PLCTL_MVRS_LDO)
    {

        /* Set main voltage regulator type to LDO if status is DCDC */
        SYS->PLCTL &= (~SYS_PLCTL_MVRS_Msk);

        /* Wait main voltage regulator type change ready */
        while((SYS->PLSTS & SYS_PLSTS_CURMVR_Msk) != SYS_PLSTS_CURMVR_LDO)
        {
            if(i32TimeOutCnt-- <= 0)
            {
                u32Ret = 0U;    /* Main voltage regulator type change time-out */
                break;
            }
        }

    }

    /* Clear main voltage regulator type change error flag */
    if(SYS->PLSTS & SYS_PLSTS_MVRCERR_Msk)
    {
        SYS->PLSTS = SYS_PLSTS_MVRCERR_Msk;
        u32Ret = 0U;
    }

    return u32Ret;
}

/**
  * @brief      Set System SRAM Power Mode
  * @param[in]  u32SRAMSel is SRAM region selection. Including :
  *             - \ref SYS_SRAMPCTL_SRAM0PM0_Msk
  *             - \ref SYS_SRAMPCTL_SRAM0PM1_Msk
  *             - \ref SYS_SRAMPCTL_SRAM0PM2_Msk
  *             - \ref SYS_SRAMPCTL_SRAM0PM3_Msk
  *             - \ref SYS_SRAMPCTL_SRAM1PM0_Msk
  *             - \ref SYS_SRAMPCTL_SRAM1PM1_Msk
  *             - \ref SYS_SRAMPCTL_SRAM1PM2_Msk
  *             - \ref SYS_SRAMPCTL_SRAM1PM3_Msk
  * @param[in]  u32PowerMode is SRAM power mode. Including :
  *             - \ref SYS_SRAMPCTL_SRAM_NORMAL
  *             - \ref SYS_SRAMPCTL_SRAM_RETENTION
  *             - \ref SYS_SRAMPCTL_SRAM_POWER_SHUT_DOWN
  * @return     None
  * @details    This function set system SRAM power mode.
  *             The register write-protection function should be disabled before using this function.
  */
void SYS_SetSSRAMPowerMode(uint32_t u32SRAMSel, uint32_t u32PowerMode)
{
    uint32_t u32SRAMSelPos = 8UL;

    /* Get system SRAM power mode setting position */
    while(u32SRAMSelPos < 24UL)
    {
        if(u32SRAMSel & (1 << u32SRAMSelPos))
        {
            break;
        }
        else
        {
            u32SRAMSelPos++;
        }
    }

    /* Set system SRAM power mode setting */
    SYS->SRAMPCTL = (SYS->SRAMPCTL & (~u32SRAMSel)) | (u32PowerMode << u32SRAMSelPos);
}

/**
  * @brief      Set Peripheral SRAM Power Mode
  * @param[in]  u32SRAMSel is SRAM region selection. Including :
  *             - \ref SYS_SRAMPPCT_CAN_Msk
  *             - \ref SYS_SRAMPPCT_USBD_Msk
  *             - \ref SYS_SRAMPPCT_PDMA0_Msk
  *             - \ref SYS_SRAMPPCT_PDMA1_Msk
  *             - \ref SYS_SRAMPPCT_FMC_Msk
  * @param[in]  u32PowerMode is SRAM power mode. Including :
  *             - \ref SYS_SRAMPPCT_SRAM_NORMAL
  *             - \ref SYS_SRAMPPCT_SRAM_RETENTION
  *             - \ref SYS_SRAMPPCT_SRAM_POWER_SHUT_DOWN
  * @return     None
  * @details    This function set peripheral SRAM power mode.
  *             The register write-protection function should be disabled before using this function.
  */
void SYS_SetPSRAMPowerMode(uint32_t u32SRAMSel, uint32_t u32PowerMode)
{
    uint32_t u32SRAMSelPos = 0UL;

    /* Get peripheral SRAM power mode setting position */
    while(u32SRAMSelPos < 10UL)
    {
        if(u32SRAMSel & (1 << u32SRAMSelPos))
        {
            break;
        }
        else
        {
            u32SRAMSelPos++;
        }
    }

    /* Set peripheral SRAM power mode setting */
    SYS->SRAMPPCT = (SYS->SRAMPPCT & (~u32SRAMSel)) | (u32PowerMode << u32SRAMSelPos);
}


/*@}*/ /* end of group SYS_EXPORTED_FUNCTIONS */

/*@}*/ /* end of group SYS_Driver */

/*@}*/ /* end of group Standard_Driver */

/*** (C) COPYRIGHT 2016 Nuvoton Technology Corp. ***/
