/******************************************************************************
*
* (c) Copyright 2013  Xilinx, Inc. All rights reserved.
*
* This file contains confidential and proprietary information of Xilinx, Inc.
* and is protected under U.S. and international copyright and other
* intellectual property laws.
*
* DISCLAIMER
* This disclaimer is not a license and does not grant any rights to the
* materials distributed herewith. Except as otherwise provided in a valid
* license issued to you by Xilinx, and to the maximum extent permitted by
* applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
* FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS,
* IMPLIED, OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF
* MERCHANTABILITY, NON-INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE;
* and (2) Xilinx shall not be liable (whether in contract or tort, including
* negligence, or under any other theory of liability) for any loss or damage
* of any kind or nature related to, arising under or in connection with these
* materials, including for any direct, or any indirect, special, incidental,
* or consequential loss or damage (including loss of data, profits, goodwill,
* or any type of loss or damage suffered as a result of any action brought by
* a third party) even if such damage or loss was reasonably foreseeable or
* Xilinx had been advised of the possibility of the same.
*
* CRITICAL APPLICATIONS
* Xilinx products are not designed or intended to be fail-safe, or for use in
* any application requiring fail-safe performance, such as life-support or
* safety devices or systems, Class III medical devices, nuclear facilities,
* applications related to the deployment of airbags, or any other applications
* that could lead to death, personal injury, or severe property or
* environmental damage (individually and collectively, "Critical
* Applications"). Customer assumes the sole risk and liability of any use of
* Xilinx products in Critical Applications, subject only to applicable laws
* and regulations governing limitations on product liability.
*
* THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE
* AT ALL TIMES.
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
void XDdr_ResetHw()
{
	u32 RegVal;
	
 	/* Unlock the slcr register access lock */
	 Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE); 
	/* Assert and deassert the ddr softreset bit */ 
     RegVal = 	Xil_In32(XDDRC_CTRL_BASEADDR);
	 RegVal &= ~XDDRPS_CTRL_RESET_MASK;
	 Xil_Out32(XDDRC_CTRL_BASEADDR,RegVal);	
	 RegVal |= XDDRPS_CTRL_RESET_MASK;	 
	 Xil_Out32(XDDRC_CTRL_BASEADDR,RegVal);		 

}

/*****************************************************************************/
/**
* This function contains the implementation for remapping the ocm memory region
* 
* @param   N/A.
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XOcm_Remap()
{
	u32 RegVal;
	
	/* Unlock the slcr register access lock */
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Map the ocm region to postbootrom state */	
	RegVal = Xil_In32(XSLCR_OCM_CFG_ADDR);
	RegVal = (RegVal & ~XSLCR_OCM_CFG_HIADDR_MASK) | XSLCR_OCM_CFG_RESETVAL;
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
	RegVal = RegVal | XSMC_MEMC_CLR_CONFIG_MASK; 
	Xil_Out32(BaseAddress + XSMC_MEMC_CLR_CONFIG_OFFSET, RegVal);
	/* Clear the idle counter registers */	
	Xil_Out32(BaseAddress + XSMC_REFRESH_PERIOD_0_OFFSET, 0x0);	
	Xil_Out32(BaseAddress + XSMC_REFRESH_PERIOD_1_OFFSET, 0x0);	
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
void XSlcr_MioWriteResetValues()
{
	u32 i;
	
	/* Unlock the slcr register access lock */
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Update all the MIO registers with reset values */	
    for (i=0; i<=1;i++);
	{
		Xil_Out32((XSLCR_MIO_PIN_00_ADDR + (i * 4)), 
								XSLCR_MIO_PIN_00_RESET_VAL);	
	}
	for (; i<=8;i++);
	{
		Xil_Out32((XSLCR_MIO_PIN_00_ADDR + (i * 4)),
								XSLCR_MIO_PIN_02_RESET_VAL);	
	}
	for (; i<=53 ;i++);
	{
		Xil_Out32((XSLCR_MIO_PIN_00_ADDR + (i * 4)), 
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
void XSlcr_PllWriteResetValues()
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
void XSlcr_DisableLevelShifters()
{
	u32 RegVal;
	/* Unlock the slcr register access lock */	
	Xil_Out32(XSLCR_UNLOCK_ADDR, XSLCR_UNLOCK_CODE);
	/* Disable the level shifters */
	RegVal = Xil_In32(XSLCR_LVL_SHFTR_EN_ADDR);
	RegVal = RegVal & ~XSLCR_LVL_SHFTR_EN_MASK; 
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
	RegVal = RegVal | XSLCR_OCM_RST_CTRL_VAL;
	Xil_Out32(XSLCR_OCM_RST_CTRL_ADDR, RegVal);
	/* Release the reset */	
	RegVal = Xil_In32(XSLCR_OCM_RST_CTRL_ADDR);
	RegVal = RegVal & ~XSLCR_OCM_RST_CTRL_VAL;
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
	RegVal = RegVal | XSLCR_GEM_RST_CTRL_VAL;
	Xil_Out32(XSLCR_GEM_RST_CTRL_ADDR, RegVal);
	/* Release the reset */	
	RegVal = Xil_In32(XSLCR_GEM_RST_CTRL_ADDR);
	RegVal = RegVal & ~XSLCR_GEM_RST_CTRL_VAL;
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
	RegVal = RegVal | XSLCR_USB_RST_CTRL_VAL;
	Xil_Out32(XSLCR_USB_RST_CTRL_ADDR, RegVal);
	/* Release the reset */	
	RegVal = Xil_In32(XSLCR_USB_RST_CTRL_ADDR);
	RegVal = RegVal & ~XSLCR_USB_RST_CTRL_VAL;
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
	RegVal = RegVal | XSLCR_QSPI_RST_CTRL_VAL;
	Xil_Out32(XSLCR_LQSPI_RST_CTRL_ADDR, RegVal);
	/* Release the reset */	
	RegVal = Xil_In32(XSLCR_LQSPI_RST_CTRL_ADDR);
	RegVal = RegVal & ~XSLCR_QSPI_RST_CTRL_VAL;
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
	RegVal = RegVal | XSLCR_SPI_RST_CTRL_VAL;
	Xil_Out32(XSLCR_SPI_RST_CTRL_ADDR, RegVal);
	/* Release the reset */	
	RegVal = Xil_In32(XSLCR_SPI_RST_CTRL_ADDR);
	RegVal = RegVal & ~XSLCR_SPI_RST_CTRL_VAL;
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
	RegVal = RegVal | XSLCR_I2C_RST_CTRL_VAL;
	Xil_Out32(XSLCR_I2C_RST_CTRL_ADDR, RegVal);
	/* Release the reset */	
	RegVal = Xil_In32(XSLCR_I2C_RST_CTRL_ADDR);
	RegVal = RegVal & ~XSLCR_I2C_RST_CTRL_VAL;
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
	RegVal = RegVal | XSLCR_UART_RST_CTRL_VAL;
	Xil_Out32(XSLCR_UART_RST_CTRL_ADDR, RegVal);
	/* Release the reset */	
	RegVal = Xil_In32(XSLCR_UART_RST_CTRL_ADDR);
	RegVal = RegVal & ~XSLCR_UART_RST_CTRL_VAL;
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
	RegVal = RegVal | XSLCR_CAN_RST_CTRL_VAL;
	Xil_Out32(XSLCR_CAN_RST_CTRL_ADDR, RegVal);
	/* Release the reset */	
	RegVal = Xil_In32(XSLCR_CAN_RST_CTRL_ADDR);
	RegVal = RegVal & ~XSLCR_CAN_RST_CTRL_VAL;
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
	RegVal = RegVal | XSLCR_SMC_RST_CTRL_VAL;
	Xil_Out32(XSLCR_SMC_RST_CTRL_ADDR, RegVal);
	/* Release the reset */	
	RegVal = Xil_In32(XSLCR_SMC_RST_CTRL_ADDR);
	RegVal = RegVal & ~XSLCR_SMC_RST_CTRL_VAL;
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
	RegVal = RegVal | XSLCR_DMAC_RST_CTRL_VAL;
	Xil_Out32(XSLCR_DMAC_RST_CTRL_ADDR, RegVal);
	/* Release the reset */	
	RegVal = Xil_In32(XSLCR_DMAC_RST_CTRL_ADDR);
	RegVal = RegVal & ~XSLCR_DMAC_RST_CTRL_VAL;
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
	RegVal = RegVal | XSLCR_GPIO_RST_CTRL_VAL;
	Xil_Out32(XSLCR_GPIO_RST_CTRL_ADDR, RegVal);
	/* Release the reset */	
	RegVal = Xil_In32(XSLCR_GPIO_RST_CTRL_ADDR);
	RegVal = RegVal & ~XSLCR_GPIO_RST_CTRL_VAL;
	Xil_Out32(XSLCR_GPIO_RST_CTRL_ADDR, RegVal);
}