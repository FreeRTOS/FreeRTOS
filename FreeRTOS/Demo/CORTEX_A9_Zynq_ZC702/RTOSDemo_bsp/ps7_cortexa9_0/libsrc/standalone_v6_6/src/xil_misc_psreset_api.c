/******************************************************************************
*
* Copyright (C) 2013 - 2015 Xilinx, Inc.  All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
* XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/
/*****************************************************************************/
/**
*
* @file xil_misc_reset.c
*
* This file contains the implementation of the reset sequence for various
* zynq ps devices like DDR,OCM,Slcr,Ethernet,Usb.. controllers. The reset
* sequence provided to the interfaces is based on the provision in
* slcr reset functional blcok.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date   Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00b kpc   03/07/13 First release
* 5.4	pkp	  09/11/15 Change the description for XOcm_Remap function
* </pre>
*
******************************************************************************/


/***************************** Include Files *********************************/
#include "xil_misc_psreset_api.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/


/*****************************************************************************/
/**
* This function contains the implementation for ddr reset.
*
* @param   N/A.
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XDdr_ResetHw(void)
{
	u32 RegVal;

	/* Unlock the slcr register access lock */
	 Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Assert and deassert the ddr softreset bit */
     RegVal = 	Xil_In32(XDDRC_CTRL_BASEADDR);
	 RegVal &= (u32)(~XDDRPS_CTRL_RESET_MASK);
	 Xil_Out32(XDDRC_CTRL_BASEADDR,RegVal);
	 RegVal |= ((u32)XDDRPS_CTRL_RESET_MASK);
	 Xil_Out32(XDDRC_CTRL_BASEADDR,RegVal);

}

/*****************************************************************************/
/**
* This function contains the implementation for remapping the ocm memory region
* to postbootrom state.
*
* @param   N/A.
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XOcm_Remap(void)
{
	u32 RegVal;

	/* Unlock the slcr register access lock */
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Map the ocm region to postbootrom state */
	RegVal = Xil_In32(XSLCR_OCM_CFG_ADDR);
	RegVal = (RegVal & (u32)(~XSLCR_OCM_CFG_HIADDR_MASK)) | (u32)XSLCR_OCM_CFG_RESETVAL;
	Xil_Out32(XSLCR_OCM_CFG_ADDR, RegVal);
}

/*****************************************************************************/
/**
* This function contains the implementation for SMC reset sequence
*
* @param   BaseAddress of the interface
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XSmc_ResetHw(u32 BaseAddress)
{
	u32 RegVal;

	/* Clear the interuupts */
	RegVal = Xil_In32(BaseAddress + XSMC_MEMC_CLR_CONFIG_OFFSET);
	RegVal = RegVal | (u32)XSMC_MEMC_CLR_CONFIG_MASK;
	Xil_Out32(BaseAddress + XSMC_MEMC_CLR_CONFIG_OFFSET, RegVal);
	/* Clear the idle counter registers */
	Xil_Out32(BaseAddress + XSMC_REFRESH_PERIOD_0_OFFSET, 0x0U);
	Xil_Out32(BaseAddress + XSMC_REFRESH_PERIOD_1_OFFSET, 0x0U);
	/* Update the ecc registers with reset values */
	Xil_Out32(BaseAddress + XSMC_ECC_MEMCFG1_OFFSET,
							XSMC_ECC_MEMCFG1_RESET_VAL);
	Xil_Out32(BaseAddress + XSMC_ECC_MEMCMD1_OFFSET,
							XSMC_ECC_MEMCMD1_RESET_VAL);
	Xil_Out32(BaseAddress + XSMC_ECC_MEMCMD2_OFFSET,
							XSMC_ECC_MEMCMD2_RESET_VAL);

}

/*****************************************************************************/
/**
* This function contains the implementation for updating the slcr mio registers
* with reset values
* @param   N/A.
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XSlcr_MioWriteResetValues(void)
{
	u32 i;

	/* Unlock the slcr register access lock */
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Update all the MIO registers with reset values */
    for (i=0U; i<=1U;i++)
	{
		Xil_Out32((XSLCR_MIO_PIN_00_ADDR + (i * 4U)),
								XSLCR_MIO_PIN_00_RESET_VAL);
	}
	for (; i<=8U;i++)
	{
		Xil_Out32((XSLCR_MIO_PIN_00_ADDR + (i * 4U)),
								XSLCR_MIO_PIN_02_RESET_VAL);
	}
	for (; i<=53U ;i++)
	{
		Xil_Out32((XSLCR_MIO_PIN_00_ADDR + (i * 4U)),
								XSLCR_MIO_PIN_00_RESET_VAL);
	}


}

/*****************************************************************************/
/**
* This function contains the implementation for updating the slcr pll registers
* with reset values
* @param   N/A.
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XSlcr_PllWriteResetValues(void)
{

	/* Unlock the slcr register access lock */
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);

	/* update the pll control registers with reset values */
	Xil_Out32(XSLCR_IO_PLL_CTRL_ADDR, XSLCR_IO_PLL_CTRL_RESET_VAL);
	Xil_Out32(XSLCR_ARM_PLL_CTRL_ADDR, XSLCR_ARM_PLL_CTRL_RESET_VAL);
	Xil_Out32(XSLCR_DDR_PLL_CTRL_ADDR, XSLCR_DDR_PLL_CTRL_RESET_VAL);
	/* update the pll config registers with reset values */
	Xil_Out32(XSLCR_IO_PLL_CFG_ADDR, XSLCR_IO_PLL_CFG_RESET_VAL);
	Xil_Out32(XSLCR_ARM_PLL_CFG_ADDR, XSLCR_ARM_PLL_CFG_RESET_VAL);
	Xil_Out32(XSLCR_DDR_PLL_CFG_ADDR, XSLCR_DDR_PLL_CFG_RESET_VAL);
	/* update the clock control registers with reset values */
	Xil_Out32(XSLCR_ARM_CLK_CTRL_ADDR, XSLCR_ARM_CLK_CTRL_RESET_VAL);
	Xil_Out32(XSLCR_DDR_CLK_CTRL_ADDR, XSLCR_DDR_CLK_CTRL_RESET_VAL);
}

/*****************************************************************************/
/**
* This function contains the implementation for disabling the level shifters
*
* @param   N/A.
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XSlcr_DisableLevelShifters(void)
{
	u32 RegVal;
	/* Unlock the slcr register access lock */
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Disable the level shifters */
	RegVal = Xil_In32(XSLCR_LVL_SHFTR_EN_ADDR);
	RegVal = RegVal & (u32)(~XSLCR_LVL_SHFTR_EN_MASK);
	Xil_Out32(XSLCR_LVL_SHFTR_EN_ADDR, RegVal);

}
/*****************************************************************************/
/**
* This function contains the implementation for OCM software reset from the
* slcr
*
* @param   N/A.
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XSlcr_OcmReset(void)
{
	u32 RegVal;
	/* Unlock the slcr register access lock */
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Assert the reset */
	RegVal = Xil_In32(XSLCR_OCM_RST_CTRL_ADDR);
	RegVal = RegVal | ((u32)XSLCR_OCM_RST_CTRL_VAL);
	Xil_Out32(XSLCR_OCM_RST_CTRL_ADDR, RegVal);
	/* Release the reset */
	RegVal = Xil_In32(XSLCR_OCM_RST_CTRL_ADDR);
	RegVal = RegVal & (u32)(~XSLCR_OCM_RST_CTRL_VAL);
	Xil_Out32(XSLCR_OCM_RST_CTRL_ADDR, RegVal);
}

/*****************************************************************************/
/**
* This function contains the implementation for Ethernet software reset from
* the slcr
* @param   N/A.
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XSlcr_EmacPsReset(void)
{
	u32 RegVal;
	/* Unlock the slcr register access lock */
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Assert the reset */
	RegVal = Xil_In32(XSLCR_GEM_RST_CTRL_ADDR);
	RegVal = RegVal | ((u32)XSLCR_GEM_RST_CTRL_VAL);
	Xil_Out32(XSLCR_GEM_RST_CTRL_ADDR, RegVal);
	/* Release the reset */
	RegVal = Xil_In32(XSLCR_GEM_RST_CTRL_ADDR);
	RegVal = RegVal & (u32)(~XSLCR_GEM_RST_CTRL_VAL);
	Xil_Out32(XSLCR_GEM_RST_CTRL_ADDR, RegVal);
}

/*****************************************************************************/
/**
* This function contains the implementation for USB software reset from the
* slcr
*
* @param   N/A.
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XSlcr_UsbPsReset(void)
{
	u32 RegVal;
	/* Unlock the slcr register access lock */
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Assert the reset */
	RegVal = Xil_In32(XSLCR_USB_RST_CTRL_ADDR);
	RegVal = RegVal | ((u32)XSLCR_USB_RST_CTRL_VAL);
	Xil_Out32(XSLCR_USB_RST_CTRL_ADDR, RegVal);
	/* Release the reset */
	RegVal = Xil_In32(XSLCR_USB_RST_CTRL_ADDR);
	RegVal = RegVal & (u32)(~XSLCR_USB_RST_CTRL_VAL);
	Xil_Out32(XSLCR_USB_RST_CTRL_ADDR, RegVal);
}
/*****************************************************************************/
/**
* This function contains the implementation for QSPI software reset from the
* slcr
*
* @param   N/A.
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XSlcr_QspiPsReset(void)
{
	u32 RegVal;
	/* Unlock the slcr register access lock */
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Assert the reset */
	RegVal = Xil_In32(XSLCR_LQSPI_RST_CTRL_ADDR);
	RegVal = RegVal | ((u32)XSLCR_QSPI_RST_CTRL_VAL);
	Xil_Out32(XSLCR_LQSPI_RST_CTRL_ADDR, RegVal);
	/* Release the reset */
	RegVal = Xil_In32(XSLCR_LQSPI_RST_CTRL_ADDR);
	RegVal = RegVal & (u32)(~XSLCR_QSPI_RST_CTRL_VAL);
	Xil_Out32(XSLCR_LQSPI_RST_CTRL_ADDR, RegVal);
}
/*****************************************************************************/
/**
* This function contains the implementation for SPI software reset from the
* slcr
*
* @param   N/A.
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XSlcr_SpiPsReset(void)
{
	u32 RegVal;
	/* Unlock the slcr register access lock */
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Assert the reset */
	RegVal = Xil_In32(XSLCR_SPI_RST_CTRL_ADDR);
	RegVal = RegVal | ((u32)XSLCR_SPI_RST_CTRL_VAL);
	Xil_Out32(XSLCR_SPI_RST_CTRL_ADDR, RegVal);
	/* Release the reset */
	RegVal = Xil_In32(XSLCR_SPI_RST_CTRL_ADDR);
	RegVal = RegVal & (u32)(~XSLCR_SPI_RST_CTRL_VAL);
	Xil_Out32(XSLCR_SPI_RST_CTRL_ADDR, RegVal);
}
/*****************************************************************************/
/**
* This function contains the implementation for i2c software reset from the slcr
*
* @param   N/A.
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XSlcr_I2cPsReset(void)
{
	u32 RegVal;
	/* Unlock the slcr register access lock */
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Assert the reset */
	RegVal = Xil_In32(XSLCR_I2C_RST_CTRL_ADDR);
	RegVal = RegVal | ((u32)XSLCR_I2C_RST_CTRL_VAL);
	Xil_Out32(XSLCR_I2C_RST_CTRL_ADDR, RegVal);
	/* Release the reset */
	RegVal = Xil_In32(XSLCR_I2C_RST_CTRL_ADDR);
	RegVal = RegVal & (u32)(~XSLCR_I2C_RST_CTRL_VAL);
	Xil_Out32(XSLCR_I2C_RST_CTRL_ADDR, RegVal);
}
/*****************************************************************************/
/**
* This function contains the implementation for UART software reset from the
* slcr
*
* @param   N/A.
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XSlcr_UartPsReset(void)
{
	u32 RegVal;
	/* Unlock the slcr register access lock */
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Assert the reset */
	RegVal = Xil_In32(XSLCR_UART_RST_CTRL_ADDR);
	RegVal = RegVal | ((u32)XSLCR_UART_RST_CTRL_VAL);
	Xil_Out32(XSLCR_UART_RST_CTRL_ADDR, RegVal);
	/* Release the reset */
	RegVal = Xil_In32(XSLCR_UART_RST_CTRL_ADDR);
	RegVal = RegVal & (u32)(~XSLCR_UART_RST_CTRL_VAL);
	Xil_Out32(XSLCR_UART_RST_CTRL_ADDR, RegVal);
}
/*****************************************************************************/
/**
* This function contains the implementation for CAN software reset from slcr
* registers
*
* @param   N/A.
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XSlcr_CanPsReset(void)
{
	u32 RegVal;
	/* Unlock the slcr register access lock */
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Assert the reset */
	RegVal = Xil_In32(XSLCR_CAN_RST_CTRL_ADDR);
	RegVal = RegVal | ((u32)XSLCR_CAN_RST_CTRL_VAL);
	Xil_Out32(XSLCR_CAN_RST_CTRL_ADDR, RegVal);
	/* Release the reset */
	RegVal = Xil_In32(XSLCR_CAN_RST_CTRL_ADDR);
	RegVal = RegVal & (u32)(~XSLCR_CAN_RST_CTRL_VAL);
	Xil_Out32(XSLCR_CAN_RST_CTRL_ADDR, RegVal);
}
/*****************************************************************************/
/**
* This function contains the implementation for SMC software reset from the slcr
*
* @param   N/A.
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XSlcr_SmcPsReset(void)
{
	u32 RegVal;
	/* Unlock the slcr register access lock */
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Assert the reset */
	RegVal = Xil_In32(XSLCR_SMC_RST_CTRL_ADDR);
	RegVal = RegVal | ((u32)XSLCR_SMC_RST_CTRL_VAL);
	Xil_Out32(XSLCR_SMC_RST_CTRL_ADDR, RegVal);
	/* Release the reset */
	RegVal = Xil_In32(XSLCR_SMC_RST_CTRL_ADDR);
	RegVal = RegVal & (u32)(~XSLCR_SMC_RST_CTRL_VAL);
	Xil_Out32(XSLCR_SMC_RST_CTRL_ADDR, RegVal);
}
/*****************************************************************************/
/**
* This function contains the implementation for DMA controller software reset
* from the slcr
*
* @param   N/A.
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XSlcr_DmaPsReset(void)
{
	u32 RegVal;
	/* Unlock the slcr register access lock */
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Assert the reset */
	RegVal = Xil_In32(XSLCR_DMAC_RST_CTRL_ADDR);
	RegVal = RegVal | ((u32)XSLCR_DMAC_RST_CTRL_VAL);
	Xil_Out32(XSLCR_DMAC_RST_CTRL_ADDR, RegVal);
	/* Release the reset */
	RegVal = Xil_In32(XSLCR_DMAC_RST_CTRL_ADDR);
	RegVal = RegVal & (u32)(~XSLCR_DMAC_RST_CTRL_VAL);
	Xil_Out32(XSLCR_DMAC_RST_CTRL_ADDR, RegVal);
}
/*****************************************************************************/
/**
* This function contains the implementation for Gpio AMBA software reset from
* the slcr
*
* @param   N/A.
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XSlcr_GpioPsReset(void)
{
	u32 RegVal;
	/* Unlock the slcr register access lock */
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Assert the reset */
	RegVal = Xil_In32(XSLCR_GPIO_RST_CTRL_ADDR);
	RegVal = RegVal | ((u32)XSLCR_GPIO_RST_CTRL_VAL);
	Xil_Out32(XSLCR_GPIO_RST_CTRL_ADDR, RegVal);
	/* Release the reset */
	RegVal = Xil_In32(XSLCR_GPIO_RST_CTRL_ADDR);
	RegVal = RegVal & (u32)(~XSLCR_GPIO_RST_CTRL_VAL);
	Xil_Out32(XSLCR_GPIO_RST_CTRL_ADDR, RegVal);
}
