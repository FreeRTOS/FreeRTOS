/**
  ******************************************************************************
  * @file    			ft32f0xx_opa.c
  * @author  			FMD AE
  * @brief   			This file provides firmware functions to manage the following 
  *          			functionalities of the comparators (OPA1 and OPA2) peripheral
  *          			applicable only on FT32F030 devices: 
  *           		+ Comparators configuration
  *           		+ Window mode control
  * @version 			V1.0.0           
  * @data		 			2021-07-01
	******************************************************************************
  */

/* Includes ------------------------------------------------------------------*/
#include "ft32f0xx_comp.h"
#include "ft32f0xx_opa.h"
/* CSR register Mask */
#define OPA_CR_CLEAR_MASK              ((uint32_t)0x0001FFFF)


   
/**
  * @brief  Deinitializes OPA peripheral registers to their default reset values.
  * @note   Deinitialization can't be performed if the OPA configuration is locked.
  *         To unlock the configuration, perform a system reset.
  * @param  None
  * @retval None
  */
void OPA_DeInit(void)
{
  OPA->CR = ((uint32_t)0x00000000);    /*!< Set OPA_CSR register to reset value */
}

/**
  * @brief  Initializes the OPA peripheral according to the specified parameters
  *         in OPA_InitStruct
  * @note   If the selected comparator is locked, initialization can't be performed.
  *         To unlock the configuration, perform a system reset.
  * @note   By default, PA1 is selected as OPA1 non inverting input.
  *         
  * @param  OPA_Selection: the selected comparator. 
  *          This parameter can be one of the following values:
  *            @arg OPA_Selection_OPA1: OPA1 selected
  *            @arg OPA_Selection_OPA2: OPA2 selected
  * @param  OPA_InitStruct: pointer to an OPA_InitTypeDef structure that contains 
  *         the configuration information for the specified OPA peripheral.
  * @retval None
  */
void OPA_Init(OPA_InitTypeDef* OPA_InitStruct)
{
  uint32_t tmpreg = 0;

  /* Check the parameters */
  assert_param(IS_OPA_VIP_SEL(OPA_InitStruct->OPA_OP0PSel));
  assert_param(IS_OPA_VIN_SEL(OPA_InitStruct->OPA_OP0NSel));
  assert_param(IS_OPA_FR_SEL(OPA_InitStruct->OPA_OP0FR));
  assert_param(IS_OPA_FCAP_SEL(OPA_InitStruct->OPA_OP0FCAPE));
  assert_param(IS_OPA_ODIG_SEL(OPA_InitStruct->OPA_OPTODIG));
  assert_param(IS_OPA_OIO_SEL(OPA_InitStruct->OPA_OPTOIO));
  

  /*!< Get the OPA_CSR register value */
  tmpreg = OPA->CR;

  /*!< Clear the bits */ 
  tmpreg &= (uint32_t) ~(OPA_CR_CLEAR_MASK);

  /*!< Configure OPA: OPA_VipSel, OPA_VinSel, OPA_OutputSel value and OPA_Pol */
  tmpreg |= (uint32_t)((OPA_InitStruct->OPA_OP0PSel | OPA_InitStruct->OPA_OP0NSel|
                       OPA_InitStruct->OPA_OP0FR | OPA_InitStruct->OPA_OP0FCAPE | OPA_InitStruct->OPA_OPTODIG |OPA_InitStruct->OPA_OPTOIO));

  /*!< Write to OPA_CR register */
  OPA->CR = tmpreg;  
}

/**
  * @brief  Fills each OPA_InitStruct member with its default value.
  * @param  OPA_InitStruct: pointer to an OPA_InitTypeDef structure which will 
  *         be initialized.
  * @retval None
  */
void OPA_StructInit(OPA_InitTypeDef* OPA_InitStruct)
{
  OPA_InitStruct->OPA_OP0PSel = OPA_VIP_SEL_PA1;
  OPA_InitStruct->OPA_OP0NSel = OPA_VIN_SEL_PA2;
  OPA_InitStruct->OPA_OP0FR = OPA_FR_SEL_NORES;
  OPA_InitStruct->OPA_OP0FCAPE = OPA_FCAP_SEL_EN;
  OPA_InitStruct->OPA_OPTODIG = OPA_ODIG_SEL_EN;
  OPA_InitStruct->OPA_OPTOIO = OPA_OIO_SEL_EN;
}

/**
  * @brief  Enable or disable the OPA peripheral.
  * @note   If the selected comparator is locked, enable/disable can't be performed.
  *         To unlock the configuration, perform a system reset.
  * @param  OPA_Selection: the selected comparator.
  *          This parameter can be one of the following values:
  *            @arg NOPA_Selection_OPA: OPA1 selected
  *            @arg POPA_Selection_OPA: OPA2 selected
  * @param  NewState: new state of the OPA peripheral.
  *          This parameter can be: ENABLE or DISABLE.
  * @note   When enabled, the comparator compares the non inverting input with 
  *         the inverting input and the comparison result is available on comparator output.
  * @note   When disabled, the comparator doesn't perform comparison and the 
  *         output level is low.
  * @retval None
  */
void OPA_Cmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the selected OPA peripheral */
    OPA->CR |= (uint32_t) (1<<0);
  }
  else
  {
    /* Disable the selected OPA peripheral  */
    OPA->CR &= (uint32_t)(~((uint32_t)1<<0));
  }
}

/**
  * @brief  Return the output level (high or low) of the selected comparator. 
  * @note   The output level depends on the selected polarity.
  * @note   If the polarity is not inverted:
  *          - Comparator output is low when the non-inverting input is at a lower
  *            voltage than the inverting input
  *          - Comparator output is high when the non-inverting input is at a higher
  *            voltage than the inverting input
  * @note   If the polarity is inverted:
  *          - Comparator output is high when the non-inverting input is at a lower
  *            voltage than the inverting input
  *          - Comparator output is low when the non-inverting input is at a higher
  *            voltage than the inverting input
  * @param  OPA_Selection: the selected comparator. 
  *          This parameter can be one of the following values:
  *            @arg OPA_CSR_OPA1OUT: OPA1 selected
  *            @arg OPA_CSR_OPA2OUT: OPA2 selected  
  * @retval Returns the selected comparator output level: low or high.
  *       
  */
uint32_t OPA_GetOutputLevel(uint32_t OPA_OutLevel)
{
  uint32_t compout = 0x0;

  /* Check the parameters */
  assert_param(IS_OPA_OUTPUT_LEVEL(OPA_OutLevel));

  /* Check if selected comparator output is high */
  if ((OPA->CR & OPA_OutLevel) != 0)
  {
    compout = OPA_OutLevel;
  }
  else
  {
    compout = OPA_OutputLevel_Low;
  }

  /* Return the comparator output level */
  return (uint32_t)(compout);
}



/**


*/
uint8_t OPA_Cali(void)
{
  uint32_t  opadelay;
  uint32_t   outstate;
  uint8_t  CalDA, CalDB;
  uint32_t opatmp32;

  /* Enable the selected OPA peripheral */
    OPA->CR |= (uint32_t) (1<<0);

  /* Enable OP0TM */
    OPA->CR |= (uint32_t) (1<<8);

  /* OP0NSEL = 00   ,  SET TO GND */
    OPA->CR &= (uint32_t) (~(3<<13));

  /* OP0PSEL = 1   ,  SET TO GND */
    OPA->CR |= (uint32_t) ((1<<15));

  /* OP0FCAPE = 0 */
    OPA->CR &= (uint32_t) (~(1<<9));

  /* OPTODIG = 1 */
    OPA->CR |= (uint32_t) ((1<<7));

  /* OP0FR = 000 */
    OPA->CR &= (uint32_t) (~(7<<10));
  
  /* PA2 TO FLOAT */
  GPIOA ->PUPDR &= ~(GPIO_PUPDR_PUPDR0 << ((uint16_t)2 * 2));	

  //
  /* OP0COF = 00000 */
   OPA->CR &= (uint32_t) (~(0x1F<<1));
  CalDA=0;
  opadelay=0X0FFF;
  while(opadelay--);
  outstate=OPA->CR;		// save
  while(1){
  	CalDA++;
	if(CalDA>=0x1F) break;
	opatmp32=OPA->CR&(~(0x1f<<1));
	OPA->CR=opatmp32|(CalDA<<1);
  	opadelay=0X0FFF;
	while(opadelay--);
	if((outstate^OPA->CR)&(1<<16)) break;
  }

  outstate=OPA->CR;		// save
  CalDB=CalDA;
   while(1){
   	if(0==CalDB) break;
  	CalDB--;
	opatmp32=OPA->CR&(~(0x1f<<1));
	OPA->CR=opatmp32|(CalDB<<1);
  	opadelay=0X0FFF;
	while(opadelay--);
	if((outstate^OPA->CR)&(1<<16)) break;
  }

  //
  CalDA+=CalDB;
  CalDA/=2;
  opatmp32=OPA->CR&(~(0x1f<<1));
  OPA->CR=opatmp32|(CalDA<<1);

  //
  return CalDA;

}







/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */

/************************ (C) COPYRIGHT FMD *****END OF FILE****/
