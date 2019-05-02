/**************************************************************************//**
 * @file     fmc.c
 * @version  V3.00
 * $Revision: 1 $
 * $Date: 16/07/07 7:50p $
 * @brief    M2351 Series Flash Memory Controller(FMC) driver source file
 *
 * @note
 * Copyright (C) 2016 Nuvoton Technology Corp. All rights reserved.
 *****************************************************************************/
#include <stdio.h>
#include "NuMicro.h"

/** @addtogroup Standard_Driver Standard Driver
  @{
*/

/** @addtogroup FMC_Driver FMC Driver
  @{
*/

/** @addtogroup FMC_EXPORTED_FUNCTIONS FMC Exported Functions
  @{
*/

/**
  * @brief Run flash all one verification and get result.
  *
  * @param[in] u32addr   Starting flash address. It must be a page aligned address.
  * @param[in] u32count  Byte count of flash to be calculated. It must be multiple of 512 bytes.
  *
  * @retval   READ_ALLONE_YES       The contents of verified flash area are 0xA11FFFFF.
  * @retval   READ_ALLONE_NOT       Some contents of verified flash area are not 0xA1100000.
  * @retval   READ_ALLONE_CMD_FAIL  Unexpected error occurred.
  *
  * @details  Run ISP check all one command to check specify area is all one or not.
  */
uint32_t  FMC_CheckAllOne(uint32_t u32addr, uint32_t u32count)
{
    uint32_t  ret = READ_ALLONE_CMD_FAIL;

    FMC->ISPSTS = 0x80UL;   /* clear check all one bit */

    FMC->ISPCMD   = FMC_ISPCMD_RUN_ALL1;
    FMC->ISPADDR  = u32addr;
    FMC->ISPDAT   = u32count;
    FMC->ISPTRG   = FMC_ISPTRG_ISPGO_Msk;

    while(FMC->ISPSTS & FMC_ISPSTS_ISPBUSY_Msk) { }

    do
    {
        FMC->ISPCMD = FMC_ISPCMD_READ_ALL1;
        FMC->ISPADDR    = u32addr;
        FMC->ISPTRG = FMC_ISPTRG_ISPGO_Msk;
        while(FMC->ISPSTS & FMC_ISPSTS_ISPBUSY_Msk) { }
    }
    while(FMC->ISPDAT == 0UL);

    if(FMC->ISPDAT == READ_ALLONE_YES)
    {
        ret = FMC->ISPDAT;
    }

    if(FMC->ISPDAT == READ_ALLONE_NOT)
    {
        ret = FMC->ISPDAT;
    }

    return ret;
}

/**
  * @brief    Disable ISP Functions
  *
  * @param    None
  *
  * @return   None
  *
  * @details  This function will clear ISPEN bit of ISPCON to disable ISP function
  *
  */
void FMC_Close(void)
{
    FMC->ISPCTL &= ~FMC_ISPCTL_ISPEN_Msk;
}

/**
  * @brief     Config XOM Region
  * @param[in] u32XomNum    The XOM number(0~3)
  * @param[in] u32XomBase   The XOM region base address.
  * @param[in] u8XomPage   The XOM page number of region size.
  *
  * @retval   0   Success
  * @retval   1   XOM is has already actived.
  * @retval   -1  Program failed.
  * @retval   -2  Invalid XOM number.
  *
  * @details  Program XOM base address and XOM size(page)
  */
int32_t FMC_ConfigXOM(uint32_t u32XomNum, uint32_t u32XomBase, uint8_t u8XomPage)
{
    int32_t  ret = 0;

    if(u32XomNum >= 4UL)
    {
        ret = -2;
    }

    if(ret == 0)
    {
        ret = FMC_GetXOMState(u32XomNum);
    }

    if(ret == 0)
    {
        FMC->ISPCMD = FMC_ISPCMD_PROGRAM;
        FMC->ISPADDR = FMC_XOM_BASE + (u32XomNum * 0x10u);
        FMC->ISPDAT = u32XomBase;
        FMC->ISPTRG = FMC_ISPTRG_ISPGO_Msk;
        while(FMC->ISPTRG & FMC_ISPTRG_ISPGO_Msk) {}

        if(FMC->ISPSTS & FMC_ISPSTS_ISPFF_Msk)
        {
            FMC->ISPSTS |= FMC_ISPSTS_ISPFF_Msk;
            ret = -1;
        }
    }

    if(ret == 0)
    {
        FMC->ISPCMD = FMC_ISPCMD_PROGRAM;
        FMC->ISPADDR = FMC_XOM_BASE + (u32XomNum * 0x10u + 0x04u);
        FMC->ISPDAT = u8XomPage;
        FMC->ISPTRG = FMC_ISPTRG_ISPGO_Msk;
        while(FMC->ISPTRG & FMC_ISPTRG_ISPGO_Msk) {}

        if(FMC->ISPSTS & FMC_ISPSTS_ISPFF_Msk)
        {
            FMC->ISPSTS |= FMC_ISPSTS_ISPFF_Msk;
            ret = -1;
        }
    }

    if(ret == 0)
    {
        FMC->ISPCMD = FMC_ISPCMD_PROGRAM;
        FMC->ISPADDR = FMC_XOM_BASE + (u32XomNum * 0x10u + 0x08u);
        FMC->ISPDAT = 0u;
        FMC->ISPTRG = FMC_ISPTRG_ISPGO_Msk;
        while(FMC->ISPTRG & FMC_ISPTRG_ISPGO_Msk) {}

        if(FMC->ISPSTS & FMC_ISPSTS_ISPFF_Msk)
        {
            FMC->ISPSTS |= FMC_ISPSTS_ISPFF_Msk;
            ret = -1;
        }
    }

    return ret;
}

/**
  * @brief      Execute Flash Page erase
  *
  * @param[in]  u32PageAddr Address of the flash page to be erased.
  *             It must be a 2048 bytes aligned address.
  *
  * @return     ISP page erase success or not.
  * @retval     0  Success
  * @retval     -1  Erase failed
  *
  * @details    Execute FMC_ISPCMD_PAGE_ERASE command to erase a flash page. The page size is 2048 bytes.
  */
int32_t FMC_Erase(uint32_t u32PageAddr)
{
    int32_t  ret = 0;

    if(ret == 0)
    {
        FMC->ISPCMD = FMC_ISPCMD_PAGE_ERASE;
        FMC->ISPADDR = u32PageAddr;
        FMC->ISPTRG = FMC_ISPTRG_ISPGO_Msk;

        while(FMC->ISPTRG & FMC_ISPTRG_ISPGO_Msk) { }

        if(FMC->ISPCTL & FMC_ISPCTL_ISPFF_Msk)
        {
            FMC->ISPCTL |= FMC_ISPCTL_ISPFF_Msk;
            ret = -1;
        }
    }
    return ret;
}

/**
  * @brief      Execute Flash Bank erase
  *
  * @param[in]  u32BankAddr Base address of the flash bank to be erased.
  *
  * @return     ISP bank erase success or not.
  * @retval     0  Success
  * @retval     -1  Erase failed
  *
  * @details  Execute FMC_ISPCMD_BANK_ERASE command to erase a flash block.
  */
int32_t FMC_Erase_Bank(uint32_t u32BankAddr)
{
    int32_t  ret = 0;

    FMC->ISPCMD = FMC_ISPCMD_BANK_ERASE;
    FMC->ISPADDR = u32BankAddr;
    FMC->ISPTRG = FMC_ISPTRG_ISPGO_Msk;

    while(FMC->ISPTRG & FMC_ISPTRG_ISPGO_Msk) {}

    if(FMC->ISPCTL & FMC_ISPCTL_ISPFF_Msk)
    {
        FMC->ISPCTL |= FMC_ISPCTL_ISPFF_Msk;
        ret = -1;
    }
    return ret;
}

/**
  * @brief      Execute Flash Block erase
  *
  * @param[in]  u32BlockAddr  Address of the flash block to be erased.
  *                           It must be a 4 pages aligned address.
  *
  * @return     ISP block erase success or not.
  * @retval     0  Success
  * @retval     -1  Erase failed
  *
  * @details Execute FMC_ISPCMD_BLOCK_ERASE command to erase a flash block. The block size is 4 pages.
  */
int32_t FMC_Erase_Block(uint32_t u32BlockAddr)
{
    int32_t  ret = 0;

    FMC->ISPCMD = FMC_ISPCMD_BLOCK_ERASE;
    FMC->ISPADDR = u32BlockAddr;
    FMC->ISPTRG = FMC_ISPTRG_ISPGO_Msk;

    while(FMC->ISPTRG & FMC_ISPTRG_ISPGO_Msk) {}

    if(FMC->ISPCTL & FMC_ISPCTL_ISPFF_Msk)
    {
        FMC->ISPCTL |= FMC_ISPCTL_ISPFF_Msk;
        ret = -1;
    }
    return ret;
}

/**
  * @brief  Execute Erase XOM Region
  *
  * @param[in]  u32XomNum  The XOMRn(n=0~3)
  *
  * @return   XOM erase success or not.
  * @retval    0  Success
  * @retval   -1  Erase failed
  * @retval   -2  Invalid XOM number.
  *
  * @details Execute FMC_ISPCMD_PAGE_ERASE command to erase XOM.
  */
int32_t FMC_EraseXOM(uint32_t u32XomNum)
{
    uint32_t u32Addr;
    int32_t i32Active, err = 0;

    if(u32XomNum >= 4UL)
    {
        err = -2;
    }

    if(err == 0)
    {
        i32Active = FMC_GetXOMState(u32XomNum);

        if(i32Active)
        {
            switch(u32XomNum)
            {
                case 0u:
                    u32Addr = (FMC->XOMR0STS & 0xFFFFFF00u) >> 8u;
                    break;
                case 1u:
                    u32Addr = (FMC->XOMR1STS & 0xFFFFFF00u) >> 8u;
                    break;
                case 2u:
                    u32Addr = (FMC->XOMR2STS & 0xFFFFFF00u) >> 8u;
                    break;
                case 3u:
                    u32Addr = (FMC->XOMR3STS & 0xFFFFFF00u) >> 8u;
                    break;
                default:
                    break;
            }
            FMC->ISPCMD = FMC_ISPCMD_PAGE_ERASE;
            FMC->ISPADDR = u32Addr;
            FMC->ISPDAT = 0x55aa03u;
            FMC->ISPTRG = 0x1u;
#if ISBEN
            __ISB();
#endif
            while(FMC->ISPTRG) {}

            /* Check ISPFF flag to know whether erase OK or fail. */
            if(FMC->ISPCTL & FMC_ISPCTL_ISPFF_Msk)
            {
                FMC->ISPCTL |= FMC_ISPCTL_ISPFF_Msk;
                err = -1;
            }
        }
        else
        {
            err = -1;
        }
    }
    return err;
}

/**
  * @brief    Get the current boot source
  *
  * @param    None
  *
  * @return   The current boot source.
  * @retval   0 This chip is currently booting from APROM
  * @retval   1 This chip is currently booting from LDROM
  *
  * @note     This function only show the boot source.
  *           User need to read ISPSTA register to know if IAP mode supported or not in relative boot.
  */
int32_t FMC_GetBootSource(void)
{
    int32_t  ret = 0;

    if(FMC->ISPCTL & FMC_ISPCTL_BS_Msk)
    {
        ret = 1;
    }

    return ret;
}

/**
  * @brief     Run CRC32 checksum calculation and get result.
  *
  * @param[in] u32addr   Starting flash address. It must be a page aligned address.
  * @param[in] u32count  Byte count of flash to be calculated. It must be multiple of 2048bytes.
  *
  * @return    Success or not.
  * @retval    0           Success.
  * @retval    0xFFFFFFFF  Invalid parameter.
  *
  * @details  Run ISP CRC32 checksum command to calculate checksum then get and return checksum data.
  */
uint32_t  FMC_GetChkSum(uint32_t u32addr, uint32_t u32count)
{
    uint32_t   ret;

    if((u32addr % 2048UL) || (u32count % 2048UL))
    {
        ret = 0xFFFFFFFF;
    }
    else
    {
        FMC->ISPCMD  = FMC_ISPCMD_RUN_CKS;
        FMC->ISPADDR = u32addr;
        FMC->ISPDAT  = u32count;
        FMC->ISPTRG  = FMC_ISPTRG_ISPGO_Msk;

        while(FMC->ISPSTS & FMC_ISPSTS_ISPBUSY_Msk) { }

        FMC->ISPCMD = FMC_ISPCMD_READ_CKS;
        FMC->ISPADDR    = u32addr;
        FMC->ISPTRG = FMC_ISPTRG_ISPGO_Msk;

        while(FMC->ISPSTS & FMC_ISPSTS_ISPBUSY_Msk) { }

        ret = FMC->ISPDAT;
    }

    return ret;
}

/**
  * @brief  Check the OTP is locked or not.
  *
  * @param[in] u32OtpNum    The OTP number.
  *
  * @retval   1   OTP is locked.
  * @retval   0   OTP is not locked.
  * @retval   -1  Failed to read OTP lock bits.
  * @retval   -2  Invalid OTP number.
  *
  * @details To get specify OTP lock status
  */
int32_t FMC_Is_OTP_Locked(uint32_t u32OtpNum)
{
    int32_t  ret = 0;

    if(u32OtpNum > 255UL)
    {
        ret = -2;
    }

    if(ret == 0)
    {
        FMC->ISPCMD = FMC_ISPCMD_READ;
        FMC->ISPADDR = FMC_OTP_BASE + 0x800UL + u32OtpNum * 4UL;
        FMC->ISPTRG = FMC_ISPTRG_ISPGO_Msk;

        while(FMC->ISPTRG & FMC_ISPTRG_ISPGO_Msk) { }

        if(FMC->ISPSTS & FMC_ISPSTS_ISPFF_Msk)
        {
            FMC->ISPSTS |= FMC_ISPSTS_ISPFF_Msk;
            ret = -1;
        }
        else
        {
            if(FMC->ISPDAT != 0xFFFFFFFFUL)
            {
                ret = 1;   /* Lock work was progrmmed. OTP was locked. */
            }
        }
    }
    return ret;
}

/**
  * @brief  Check the XOM is actived or not.
  *
  * @param[in] u32XomNum    The xom number(0~3).
  *
  * @retval   1   XOM is actived.
  * @retval   0   XOM is not actived.
  * @retval   -2  Invalid XOM number.
  *
  * @details To get specify XOMRn(n=0~3) active status
  */
int32_t FMC_GetXOMState(uint32_t u32XomNum)
{
    uint32_t u32act;
    int32_t  ret = 0;

    if(u32XomNum >= 4UL)
    {
        ret = -2;
    }

    if(ret >= 0)
    {
        u32act = (((FMC->XOMSTS) & 0xful) & (1ul << u32XomNum)) >> u32XomNum;
        ret = (int32_t)u32act;
    }
    return ret;
}

/**
  * @brief  Lock the specified OTP.
  *
  * @param[in] u32OtpNum    The OTP number.
  *
  * @retval    0   Success
  * @retval   -1  Failed to write OTP lock bits.
  * @retval   -2  Invalid OTP number.
  *
  * @details  To lock specified OTP number
  */
int32_t FMC_Lock_OTP(uint32_t u32OtpNum)
{
    int32_t  ret = 0;

    if(u32OtpNum > 255UL)
    {
        ret = -2;
    }

    if(ret == 0)
    {
        FMC->ISPCMD = FMC_ISPCMD_PROGRAM;
        FMC->ISPADDR = FMC_OTP_BASE + 0x800UL + u32OtpNum * 4UL;
        FMC->ISPDAT = 0UL;
        FMC->ISPTRG = FMC_ISPTRG_ISPGO_Msk;

        while(FMC->ISPTRG & FMC_ISPTRG_ISPGO_Msk) { }

        if(FMC->ISPSTS & FMC_ISPSTS_ISPFF_Msk)
        {
            FMC->ISPSTS |= FMC_ISPSTS_ISPFF_Msk;
            ret = -1;
        }
    }
    return ret;
}

/**
  * @brief    Enable FMC ISP function
  *
  * @param    None
  *
  * @return   None
  *
  * @details  ISPEN bit of ISPCON must be set before we can use ISP commands.
  *           Therefore, To use all FMC function APIs, user needs to call FMC_Open() first to enable ISP functions.
  *
  * @note     ISP functions are write-protected. user also needs to unlock it by calling SYS_UnlockReg() before using all ISP functions.
  *
  */
void FMC_Open(void)
{
    FMC->ISPCTL |=  FMC_ISPCTL_ISPEN_Msk;
}


/**
  * @brief      Read a word bytes from flash
  *
  * @param[in]  u32Addr Address of the flash location to be read.
  *             It must be a word aligned address.
  *
  * @return     The word data read from specified flash address.
  *
  * @details    Execute FMC_ISPCMD_READ command to read a word from flash.
  */
uint32_t FMC_Read(uint32_t u32Addr)
{
    FMC->ISPCMD = FMC_ISPCMD_READ;
    FMC->ISPADDR = u32Addr;
    FMC->ISPTRG = FMC_ISPTRG_ISPGO_Msk;
    while(FMC->ISPTRG & FMC_ISPTRG_ISPGO_Msk) { }

    return FMC->ISPDAT;
}

/**
  * @brief      Read a double-word bytes from flash
  *
  * @param[in]  u32addr   Address of the flash location to be read.
  *             It must be a double-word aligned address.
  *
  * @param[out] u32data0  Place holder of word 0 read from flash address u32addr.
  * @param[out] u32data1  Place holder of word 0 read from flash address u32addr+4.
  *
  * @return     0   Success
  * @return     -1  Failed
  *
  * @details    Execute FMC_ISPCMD_READ_64 command to read a double-word from flash.
  */
int32_t FMC_Read_64(uint32_t u32addr, uint32_t * u32data0, uint32_t * u32data1)
{
    int32_t  ret = 0;

    FMC->ISPCMD = FMC_ISPCMD_READ_64;
    FMC->ISPADDR    = u32addr;
    FMC->ISPDAT = 0x0UL;
    FMC->ISPTRG = FMC_ISPTRG_ISPGO_Msk;

    while(FMC->ISPSTS & FMC_ISPSTS_ISPBUSY_Msk) { }

    if(FMC->ISPSTS & FMC_ISPSTS_ISPFF_Msk)
    {
        FMC->ISPSTS |= FMC_ISPSTS_ISPFF_Msk;
        ret = -1;
    }
    else
    {
        *u32data0 = FMC->MPDAT0;
        *u32data1 = FMC->MPDAT1;
    }
    return ret;
}

/**
  * @brief  Read data from OTP
  *
  * @param[in] u32OtpNum    The OTP number(0~255).
  * @param[in] u32LowWord   Low word of the 64-bits data.
  * @param[in] u32HighWord   High word of the 64-bits data.
  *
  * @retval    0   Success
  * @retval   -1  Read failed.
  * @retval   -2  Invalid OTP number.
  *
  * @details  Read the 64-bits data from the specified OTP.
  */
int32_t FMC_Read_OTP(uint32_t u32OtpNum, uint32_t *u32LowWord, uint32_t *u32HighWord)
{
    int32_t  ret = 0;

    if(u32OtpNum > 255UL)
    {
        ret = -2;
    }

    if(ret == 0)
    {
        FMC->ISPCMD = FMC_ISPCMD_READ_64;
        FMC->ISPADDR    = FMC_OTP_BASE + u32OtpNum * 8UL ;
        FMC->ISPDAT = 0x0UL;
        FMC->ISPTRG = FMC_ISPTRG_ISPGO_Msk;

        while(FMC->ISPSTS & FMC_ISPSTS_ISPBUSY_Msk) {}

        if(FMC->ISPSTS & FMC_ISPSTS_ISPFF_Msk)
        {
            FMC->ISPSTS |= FMC_ISPSTS_ISPFF_Msk;
            ret = -1;
        }
        else
        {
            *u32LowWord = FMC->MPDAT0;
            *u32HighWord = FMC->MPDAT1;
        }
    }
    return ret;
}

/**
  * @brief       Read the User Configuration words.
  *
  * @param[out]  u32Config[]  The word buffer to store the User Configuration data.
  * @param[in]   u32Count   The word count to be read.
  *
  * @return      Success or not.
  * @retval       0 Success
  * @retval      -1 Failed
  *
  * @details     This function is used to read the settings of user configuration.
  *              if u32Count = 1, Only CONFIG0 will be returned to the buffer specified by u32Config.
  *              if u32Count = 2, Both CONFIG0 and CONFIG1 will be returned.
  */
int32_t FMC_ReadConfig(uint32_t u32Config[], uint32_t u32Count)
{
    uint32_t i;

    for(i = 0u; i < u32Count; i++)
    {
        u32Config[i] = FMC_Read(FMC_CONFIG_BASE + i * 4u);
    }
    return 0;
}

/**
  * @brief      Set boot source from LDROM or APROM after next software reset
  *
  * @param[in]  i32BootSrc
  *                1: Boot from LDROM
  *                0: Boot from APROM
  *
  * @return    None
  *
  * @details   This function is used to switch APROM boot or LDROM boot. User need to call
  *            FMC_SetBootSource to select boot source first, then use CPU reset or
  *            System Reset Request to reset system.
  *
  */
void FMC_SetBootSource(int32_t i32BootSrc)
{
    if(i32BootSrc)
    {
        FMC->ISPCTL |= FMC_ISPCTL_BS_Msk; /* Boot from LDROM */
    }
    else
    {
        FMC->ISPCTL &= ~FMC_ISPCTL_BS_Msk;/* Boot from APROM */
    }
}

/**
  * @brief    Execute Security Key Comparison.
  *
  * @param[in] key  Key 0~2 to be compared.
  *
  * @retval   0     Key matched.
  * @retval   -1    Forbidden. Times of key comparison mismatch reach the maximum count.
  * @retval   -2    Key mismatched.
  * @retval   -3    No KPROM key lock. Key comparison is not required.
  *
  * @ details   Input a keys to compare with security key
  */
int32_t  FMC_CompareSPKey(uint32_t key[3])
{
    uint32_t  u32KeySts;
    int32_t   ret = 0;

    if(FMC->KPKEYSTS & FMC_KPKEYSTS_FORBID_Msk)
    {
        /* FMC_SKey_Compare - FORBID!  */
        ret = -1;
    }

    if(!(FMC->KPKEYSTS & FMC_KPKEYSTS_KEYLOCK_Msk))
    {
        /* FMC_SKey_Compare - key is not locked!  */
        ret = -3;
    }

    if(ret == 0)
    {
        FMC->KPKEY0 = key[0];
        FMC->KPKEY1 = key[1];
        FMC->KPKEY2 = key[2];
        FMC->KPKEYTRG = FMC_KPKEYTRG_KPKEYGO_Msk | FMC_KPKEYTRG_TCEN_Msk;

        while(FMC->KPKEYSTS & FMC_KPKEYSTS_KEYBUSY_Msk) { }

        u32KeySts = FMC->KPKEYSTS;

        if(!(u32KeySts & FMC_KPKEYSTS_KEYMATCH_Msk))
        {
            /* Key mismatched! */
            ret = -2;
        }
        else if(u32KeySts & FMC_KPKEYSTS_KEYLOCK_Msk)
        {
            /* Key matched, but still be locked! */
            ret = -2;
        }
    }
    return ret;
}

/**
  * @brief    Setup Security Key.
  *
  * @param[in] au32Key      Key 0~2 to be setup.
  * @param[in] u32Kpmax    Maximum unmatched power-on counting number.
  * @param[in] u32Kemax    Maximum unmatched counting number.
  * @param[in] i32LockCONFIG   1: Security key lock CONFIG to write-protect. 0: Don't lock CONFIG.
  * @param[in] i32LockSPROM    1: Security key lock SPROM to write-protect. 0: Don't lock SPROM. (This param is not supported on M2351)
  *
  * @retval    0    Success.
  * @retval   -1    Key is locked. Cannot overwrite the current key.
  * @retval   -2    Failed to erase flash.
  * @retval   -3    Failed to program key.
  * @retval   -4    Key lock function failed.
  * @retval   -5    CONFIG lock function failed.
  * @retval   -6    SPROM lock function failed. (This status is not supported on M2351)
  * @retval   -7    KPMAX function failed.
  * @retval   -8    KEMAX function failed.
  *
  * @details  Set secure keys and setup key compare count. The secure key also can protect user config.
  */
int32_t  FMC_SetSPKey(uint32_t au32Key[3], uint32_t u32Kpmax, uint32_t u32Kemax,
                      const int32_t i32LockCONFIG, const int32_t i32LockSPROM)
{
    uint32_t  lock_ctrl = 0UL;
    uint32_t  u32KeySts;
    int32_t   ret = 0;

    if(FMC->KPKEYSTS != 0x200UL)
    {
        ret = -1;
    }

    if(FMC_Erase(FMC_KPROM_BASE))
    {
        ret = -2;
    }

    if(FMC_Erase(FMC_KPROM_BASE + 0x200UL))
    {
        ret = -3;
    }

    if(!i32LockCONFIG)
    {
        lock_ctrl |= 0x1UL;
    }

    if(!i32LockSPROM)
    {
        lock_ctrl |= 0x2UL;
    }

    if(ret == 0)
    {
        FMC_Write(FMC_KPROM_BASE, au32Key[0]);
        FMC_Write(FMC_KPROM_BASE + 0x4UL, au32Key[1]);
        FMC_Write(FMC_KPROM_BASE + 0x8UL, au32Key[2]);
        FMC_Write(FMC_KPROM_BASE + 0xCUL, u32Kpmax);
        FMC_Write(FMC_KPROM_BASE + 0x10UL, u32Kemax);
        FMC_Write(FMC_KPROM_BASE + 0x14UL, lock_ctrl);

        while(FMC->KPKEYSTS & FMC_KPKEYSTS_KEYBUSY_Msk) { }

        u32KeySts = FMC->KPKEYSTS;

        if(!(u32KeySts & FMC_KPKEYSTS_KEYLOCK_Msk))
        {
            /* Security key lock failed! */
            ret = -4;
        }
        else if((i32LockCONFIG && (!(u32KeySts & FMC_KPKEYSTS_CFGFLAG_Msk))) ||
                ((!i32LockCONFIG) && (u32KeySts & FMC_KPKEYSTS_CFGFLAG_Msk)))
        {
            /* CONFIG lock failed! */
            ret = -5;
        }
        else if(((FMC->KPCNT & FMC_KPCNT_KPMAX_Msk) >> FMC_KPCNT_KPMAX_Pos) != u32Kpmax)
        {
            /* KPMAX failed! */
            ret = -7;
        }
        else if(((FMC->KPKEYCNT & FMC_KPKEYCNT_KPKEMAX_Msk) >> FMC_KPKEYCNT_KPKEMAX_Pos) != u32Kemax)
        {
            /* KEMAX failed! */
            ret = -8;
        }
    }
    return ret;
}

/**
  * @brief      Write a word bytes to flash.
  *
  * @param[in]  u32Addr Address of the flash location to be programmed.
  *             It must be a word aligned address.
  * @param[in]  u32Data The word data to be programmed.
  *
  * @return     None
  *
  * @ details   Execute ISP FMC_ISPCMD_PROGRAM to program a word to flash.
  */
void FMC_Write(uint32_t u32Addr, uint32_t u32Data)
{
    FMC->ISPCMD = FMC_ISPCMD_PROGRAM;
    FMC->ISPADDR = u32Addr;
    FMC->ISPDAT = u32Data;
    FMC->ISPTRG = FMC_ISPTRG_ISPGO_Msk;
    while(FMC->ISPTRG & FMC_ISPTRG_ISPGO_Msk) { }
}

/**
  * @brief      Write a double-word bytes to flash
  *
  * @param[in]  u32addr Address of the flash location to be programmed.
  *             It must be a double-word aligned address.
  * @param[in]  u32data0   The word data to be programmed to flash address u32addr.
  * @param[in]  u32data1   The word data to be programmed to flash address u32addr+4.
  *
  * @return     0   Success
  * @return     -1  Failed
  *
  * @ details   Execute ISP FMC_ISPCMD_PROGRAM_64 to program a double-word to flash.
  */
int32_t FMC_Write8Bytes(uint32_t u32addr, uint32_t u32data0, uint32_t u32data1)
{
    int32_t  ret = 0;

    FMC->ISPCMD  = FMC_ISPCMD_PROGRAM_64;
    FMC->ISPADDR = u32addr;
    FMC->MPDAT0  = u32data0;
    FMC->MPDAT1  = u32data1;
    FMC->ISPTRG  = FMC_ISPTRG_ISPGO_Msk;

    while(FMC->ISPSTS & FMC_ISPSTS_ISPBUSY_Msk) { }

    if(FMC->ISPSTS & FMC_ISPSTS_ISPFF_Msk)
    {
        FMC->ISPSTS |= FMC_ISPSTS_ISPFF_Msk;
        ret = -1;
    }
    return ret;
}

/**
  * @brief    Write User Configuration
  *
  * @param[in]  au32Config[] The word buffer to store the User Configuration data.
  * @param[in]  u32Count The word count to program to User Configuration.
  *
  * @retval     0 Success
  * @retval    -1 Failed
  *
  * @details  User must enable User Configuration update before writing it.
  *           User must erase User Configuration before writing it.
  *           User Configuration is also be page erase. User needs to backup necessary data
  *           before erase User Configuration.
  */
int32_t FMC_WriteConfig(uint32_t au32Config[], uint32_t u32Count)
{
    int32_t  ret = 0;
    uint32_t i;

    FMC_ENABLE_CFG_UPDATE();
    for(i = 0u; i < u32Count; i++)
    {
        FMC_Write(FMC_CONFIG_BASE + i * 4u, au32Config[i]);
        if(FMC_Read(FMC_CONFIG_BASE + i * 4u) != au32Config[i])
        {
            ret = -1;
        }
    }
    FMC_DISABLE_CFG_UPDATE();
    return ret;
}

/**
  * @brief      Write Multi-Word bytes to flash
  *
  * @param[in]  u32Addr    Start flash address in APROM where the data chunk to be programmed into.
  *                        This address must be 8-bytes aligned to flash address.
  * @param[in]  pu32Buf    Buffer that carry the data chunk.
  * @param[in]  u32Len     Length of the data chunk in bytes.
  *
  * @retval     >=0  Number of data bytes were programmed.
  * @return     -1   Invalid address.
  *
  * @details     Program Multi-Word data into specified address of flash.
  */

int32_t FMC_WriteMultiple(uint32_t u32Addr, uint32_t pu32Buf[], uint32_t u32Len)
{

    uint32_t i, idx, u32OnProg, retval = 0;
    int32_t err;

    if((u32Addr >= FMC_APROM_END) || ((u32Addr % 8) != 0))
    {
        return -1;
    }

    idx = 0u;
    FMC->ISPCMD = FMC_ISPCMD_PROGRAM_MUL;
    FMC->ISPADDR = u32Addr;
    retval += 16;
    do
    {
        err = 0;
        u32OnProg = 1u;
        FMC->MPDAT0 = pu32Buf[idx + 0u];
        FMC->MPDAT1 = pu32Buf[idx + 1u];
        FMC->MPDAT2 = pu32Buf[idx + 2u];
        FMC->MPDAT3 = pu32Buf[idx + 3u];
        FMC->ISPTRG = 0x1u;
        idx += 4u;

        for(i = idx; i < (FMC_MULTI_WORD_PROG_LEN / 4u); i += 4u) /* Max data length is 256 bytes (512/4 words)*/
        {
            __set_PRIMASK(1u); /* Mask interrupt to avoid status check coherence error*/
            do
            {
                if((FMC->MPSTS & FMC_MPSTS_MPBUSY_Msk) == 0u)
                {
                    __set_PRIMASK(0u);

                    FMC->ISPADDR = FMC->MPADDR & (~0xful);
                    idx = (FMC->ISPADDR - u32Addr) / 4u;
                    err = -1;
                }
            }
            while((FMC->MPSTS & (3u << FMC_MPSTS_D0_Pos)) && (err == 0));

            if(err == 0)
            {
                retval += 8;

                /* Update new data for D0 */
                FMC->MPDAT0 = pu32Buf[i];
                FMC->MPDAT1 = pu32Buf[i + 1u];
                do
                {
                    if((FMC->MPSTS & FMC_MPSTS_MPBUSY_Msk) == 0u)
                    {
                        __set_PRIMASK(0u);
                        FMC->ISPADDR = FMC->MPADDR & (~0xful);
                        idx = (FMC->ISPADDR - u32Addr) / 4u;
                        err = -1;
                    }
                }
                while((FMC->MPSTS & (3u << FMC_MPSTS_D2_Pos)) && (err == 0));

                if(err == 0)
                {
                    retval += 8;

                    /* Update new data for D2*/
                    FMC->MPDAT2 = pu32Buf[i + 2u];
                    FMC->MPDAT3 = pu32Buf[i + 3u];
                    __set_PRIMASK(0u);
                }
            }

            if(err < 0)
            {
                break;
            }
        }
        if(err == 0)
        {
            u32OnProg = 0u;
            while(FMC->ISPSTS & FMC_ISPSTS_ISPBUSY_Msk) {}
        }
    }
    while(u32OnProg);

    return retval;
}

/**
  * @brief     Write data to OTP
  *
  * @param[in] u32OtpNum    The OTP number(0~255).
  * @param[in] u32LowWord   Low word of the 64-bits data.
  * @param[in] u32HighWord   High word of the 64-bits data.
  *
  * @retval    0   Success
  * @retval    -1  Program failed.
  * @retval    -2  Invalid OTP number.
  *
  * @details  Program a 64-bits data to the specified OTP.
  */
int32_t FMC_Write_OTP(uint32_t u32OtpNum, uint32_t u32LowWord, uint32_t u32HighWord)
{
    int32_t  ret = 0;

    if(u32OtpNum > 255UL)
    {
        ret = -2;
    }

    if(ret == 0)
    {
        FMC->ISPCMD = FMC_ISPCMD_PROGRAM;
        FMC->ISPADDR = FMC_OTP_BASE + u32OtpNum * 8UL;
        FMC->ISPDAT = u32LowWord;
        FMC->ISPTRG = FMC_ISPTRG_ISPGO_Msk;

        while(FMC->ISPTRG & FMC_ISPTRG_ISPGO_Msk) { }

        if(FMC->ISPSTS & FMC_ISPSTS_ISPFF_Msk)
        {
            FMC->ISPSTS |= FMC_ISPSTS_ISPFF_Msk;
            ret = -1;
        }
    }

    if(ret == 0)
    {
        FMC->ISPCMD = FMC_ISPCMD_PROGRAM;
        FMC->ISPADDR = FMC_OTP_BASE + u32OtpNum * 8UL + 4UL;
        FMC->ISPDAT = u32HighWord;
        FMC->ISPTRG = FMC_ISPTRG_ISPGO_Msk;

        while(FMC->ISPTRG & FMC_ISPTRG_ISPGO_Msk) { }

        if(FMC->ISPSTS & FMC_ISPSTS_ISPFF_Msk)
        {
            FMC->ISPSTS |= FMC_ISPSTS_ISPFF_Msk;
            ret = -1;
        }
    }

    return ret;
}

/*@}*/ /* end of group FMC_EXPORTED_FUNCTIONS */

/*@}*/ /* end of group FMC_Driver */

/*@}*/ /* end of group Standard_Driver */

/*** (C) COPYRIGHT 2016 Nuvoton Technology Corp. ***/


