 /**
 ******************************************************************************
 * @file    discover_functions.c
 * @author  Microcontroller Division
  * @version V1.0.3
  * @date    May-2013
 * @brief   Discover demo functions
 ******************************************************************************
 * @copy
 *
 * THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
 * WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE
 * TIME. AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY
 * DIRECT, INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING
 * FROM THE CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE
 * CODING INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
 *
 * <h2><center>&copy; COPYRIGHT 2011 STMicroelectronics</center></h2>
 */

/* Includes ------------------------------------------------------------------*/

/* stm32l1xxx std peripheral drivers headers*/ 
#include "stm32l1xx_exti.h"
#include "misc.h"

/* touch sensing library headers*/ 
//#include "stm32_tsl_api.h" -- superseded
//#include "stm32l15x_tsl_ct_acquisition.h" -- superseded
#include "tsl.h"
#include "tsl_user.h"
/* discover application headers*/ 
#include "discover_board.h"
#include "discover_functions.h"
#include "stm32l_discovery_lcd.h"
#include "icc_measure.h"
  
/*Variables placed in DataFlash */

/* ADC converter value for Bias current value*/
#if   (defined ( __CC_ARM ))
uint8_t Bias_Current __attribute__((at(0x08080000)));     
#elif (defined (__ICCARM__))
uint8_t Bias_Current @ ".DataFlash" ;  
#elif (defined (__GNUC__))
/* ADC converter value for Bias current value*/
uint8_t Bias_Current __attribute__((section(".DataFlash")));
#endif

/* Flag for autotest placed in Data Flash for return from RESET after STANDBY */
#if   (defined ( __CC_ARM ))
bool self_test      __attribute__((at(0x08080004)));        
#elif (defined (__ICCARM__))
bool self_test @ ".DataFlash" ;
#elif (defined (__GNUC__))
/* Flag for autotest placed in Data Flash for return from RESET after STANDBY */
bool self_test      __attribute__((section(".DataFlash")));
#endif

extern float Current_STBY;
extern uint8_t t_bar[2];
extern uint16_t Int_CurrentSTBY;

/* Used for indicate that the automatic test is ON (set in interrupt handler).*/

/* To indicate if user button function is actived*/
bool UserButton ;
/* Used for detect keypressed*/
extern volatile bool KeyPressed;


/**
  * @brief  automatic test for VDD 
  * @caller auto_test
  * @param None
  * @retval None
  */
void test_vdd(void)
{
  uint16_t vdd_test;
  uint16_t Message[6];
  
  /* Display test name*/
  LCD_GLASS_DisplayString(" VDD ");
  DELAY;
  /* get VDD voltage value */ 
  vdd_test = (int)Vref_measure();
  DELAY;
  /* Check if value is correct */	
  if ((vdd_test>VCC_MAX) || (vdd_test<VCC_MIN))
  {
    /* if not correct stay in following infinit loop -- Press reset for exit */
    while(1)
    {
      /* Display VDD ERROR message*/
      LCD_GLASS_ScrollSentence("VDD ERROR ",1,SCROLL_SPEED); 
      DELAY;
      /*convert vdd_test value in char and stor it into Message */
      convert_into_char (vdd_test, Message);
      /* Add unit and decimal point to Message  */
      Message[5] = 'V';
      Message[4] = ' ';
      Message[1] |= DOT; 
      Message[0] = ' ';
      /*Display Message*/   
      LCD_GLASS_DisplayStrDeci(Message);      
      DELAY;
      DELAY;      
    }
  }
  /* Display VDD OK message*/
  LCD_GLASS_DisplayString("VDD OK");
  DELAY ;
}

/**
  * @brief  Automatic test current in Run Mode 
  * @caller auto_test
  * @param None
  * @retval None
  */ 
void test_icc_Run(void)
{
  uint16_t icc_test;
  uint16_t Message[6];
  
  /* Display test name*/
  LCD_GLASS_DisplayString("RUN   ");
  DELAY;
  
  /* get ICC current value in RUN mode*/ 
  icc_test = (int)Icc_RUN();
  DELAY;
  /* Check if value is correct */	
  if ((icc_test>ICC_RUN_MAX) || (icc_test<ICC_RUN_MIN))
  {
     /* if not correct stay in following infinit loop -- Press reset for exit */
    while (1)
    {
      KeyPressed = FALSE;
      /* Display RUN ERROR message*/
      LCD_GLASS_ScrollSentence("RUN ERROR ",1,SCROLL_SPEED); 
      DELAY;
      /*convert icc_test value in char and stor it into tab */
      convert_into_char((uint32_t)(icc_test), Message);
      /* Add unit and decimal point to Message  */
      Message[5] = 'A';
      Message[4] = 'm';
      Message[3] = ' ';
      Message[0] |= DOT;
       /*Display Message*/   
      LCD_GLASS_DisplayStrDeci(Message);
      DELAY;
      DELAY;
    }
  }
  /* Display RUN OK message*/
  LCD_GLASS_DisplayString("RUN OK");
  DELAY;
}

/**
  * @brief  Automatic test bias value
  * @caller auto_test
  * @param None
  * @retval None
  */ 
void test_Bias(void)
{
  float Current = 0;
  /* Display test name*/
  LCD_GLASS_DisplayString("BIAS   ");
  DELAY;
  /* Get operational amplifier BIAS current value*/ 
  Current = Bias_Current * Vdd_appli()/ADC_CONV; 
  Current *= 20L;
  display_MuAmp((uint32_t)Current);
  DELAY;
   /* Check if value is correct */	
  if ((Bias_Current > ICC_BIAS_MAX) || (Bias_Current == 0 ))
  {
     /* if not correct stay in following infinit loop */
    while (1)
    {
      KeyPressed = FALSE;
      /* Display BIAS ERROR message and BIAS current*/
      LCD_GLASS_ScrollSentence("BIAS ERROR ",1,SCROLL_SPEED);
      DELAY;
      display_MuAmp((uint32_t)Current);
      DELAY;
      DELAY;
    }
  }
  /* Display BIAS OK message*/
  LCD_GLASS_DisplayString("BIASOK");
  DELAY;
}

/**
  * @brief  Automatic test current in STOP Mode
  * @caller auto_test
  * @param None
  * @retval None
  */
void test_icc_STOP(void)
{
  uint16_t icc_test;
  /* Display test name*/
  LCD_GLASS_DisplayString("STOP  ");
  DELAY;
  
  /* Get operational Icc current value in Stop mode no RTC*/	
  icc_test = (int)Icc_Stop_NoRTC();
    DELAY;
  /* Test if value is correct */
    if ((icc_test>ICC_STOP_MAX) || (icc_test<ICC_STOP_MIN))
    {
       /* if not correct stay in following infinite loop */
      while (1)
      {
        KeyPressed = FALSE;
        /* Display ICC STOP ERROR message*/
        LCD_GLASS_ScrollSentence("ICC STOP ERROR ",1,SCROLL_SPEED);
        DELAY;
        /* Display ICC STOPvalue*/
        display_MuAmp((uint32_t)icc_test);
        DELAY;
        DELAY;
      }
    }
  /* Display STOP OK message*/
  LCD_GLASS_DisplayString("STOPOK");
  DELAY;
}


/**
  * @brief  Automatic test current in STBY Mode
  * @caller auto_test
  * @param None
  * @retval None
  */
void test_icc_STBY(void)
{
  /* Display test name*/
  LCD_GLASS_DisplayString("STBY  ");
  DELAY;
  /* Current value measured in Standby mode*/	
  ADC_Icc_Test(MCU_STBY);
  /* No Return software reset performed in ADC_Icc_Test function */
}

/**
  * @brief  Run auto test
  * @caller main 
  * @param None
  * @retval None
  */ 
void auto_test(void)
{
  uint16_t tab[6]={0x20,0x20,0x20,0x20,0x20,0x20};
  
  AUTOTEST(TRUE) ;
	
  /* Switch off leds*/
  GPIO_LOW(LD_GPIO_PORT,LD_GREEN_GPIO_PIN);	
  GPIO_LOW(LD_GPIO_PORT,LD_BLUE_GPIO_PIN);
  
  /* reset LCD bar indicator*/
  BAR0_OFF;
  BAR1_OFF;
  BAR2_OFF;
  BAR3_OFF;
  
  /* To display version */
  LCD_GLASS_DisplayString(" TEST ");
  DELAY;
  STR_VERSION;
  LCD_GLASS_DisplayStrDeci(tab);
  DELAY;
  DELAY;
  
  /* And launch the tests*/
  test_vdd();
  test_icc_Run();
  test_Bias();
  test_icc_STOP();
  test_icc_STBY();
  
  /* Infinite loop: Press reset button at the end of test for exit*/
  while (1)
  {
    LCD_GLASS_ScrollSentence("TEST OK ",1,SCROLL_SPEED);
    KeyPressed = FALSE;
  }
}

/**
  * @brief Second part of  Run auto test (run after sw reset)
  * @caller main after RESET 
  * @param None
  * @retval None
  */ 
void auto_test_part2(void)
{
  float Current_STBY;
  
  /* Substract operational amplifier bias current from mesured standby current*/
  if ( Int_CurrentSTBY > Bias_Current )
    Int_CurrentSTBY -= Bias_Current;
  /* convert value in uA */ 
  Current_STBY = Int_CurrentSTBY * Vdd_appli()/ADC_CONV;  
  Current_STBY *= 20L;
  /*Display Standby Icc current value*/
  display_MuAmp((uint32_t)Current_STBY);
  DELAY;
 /* Test if value is correct */
    if ((Current_STBY > ICC_STBY_MAX) || (Current_STBY < ICC_STBY_MIN))
    {
       /* if not correct stay in following infinite loop */
      while (1)
      {
        KeyPressed = FALSE;
        /* Display ICC STBY error message */ 
        LCD_GLASS_ScrollSentence("ICC STBY ERROR ",1,SCROLL_SPEED); 
        DELAY;
        /* Display ICC STBY current */
        display_MuAmp((uint32_t)Current_STBY);
        DELAY;
        DELAY;
      }
    }
  /* Display ICC STBY test OK*/  
  LCD_GLASS_DisplayString("STBYOK");
  DELAY;    
  
   /* Infinite loop: Press reset button at the end of autotest to restart application*/
  while (1)
  {
    LCD_GLASS_ScrollSentence("TEST OK ",1,SCROLL_SPEED);
    KeyPressed = FALSE;
  }
}
/**
  * @brief Measures the BIAS current PJ1 Must be on OFF position
  * @caller main 
  * @param None
  * @retval None
  */  
void Bias_measurement(void)
{
  float Current;
  uint16_t MeasurINT;
  /* indicate that applicartion run in ** BIAS CURRENT ** mode */
  LCD_GLASS_ScrollSentence("      ** BIAS CURRENT ** JP1 OFF **",1,SCROLL_SPEED);	
  
  /* Get operational amplifier Bias current value */
  MeasurINT = ADC_Icc_Test(MCU_STOP_NoRTC);
  
  /* convert mesured value in uA*/
  Current = MeasurINT * Vdd_appli()/ADC_CONV; 
  Current *= 20L;
  
  /*display bias current value */
  display_MuAmp((uint32_t)Current);

  /* unlock E²Prom write access*/
  DATA_EEPROM_Unlock();
  
  /* Store the value in E²Prom for application needs*/
  DATA_EEPROM_FastProgramByte((uint32_t)&Bias_Current, MeasurINT) ;
  
  /* Lock back E²PROM write access */
  DATA_EEPROM_Lock();	
  
  /* Infinite loop: BIAS current display -- Press reset button in order to restart application*/
  while (1)  
  { 
    /* Get operational amplifier Bias current value */
    MeasurINT = ADC_Icc_Test(MCU_STOP_NoRTC);
    /* convert mesured value in uA*/
    Current = MeasurINT * Vdd_appli()/ADC_CONV; 
    Current *= 20L;
    /*display bias current value */
    display_MuAmp((uint32_t)Current);
    Delay(800) ;
  }
}

/**
  * @brief converts a 32bit unsined int into ASCII 
  * @caller several callers for display values
  * @param Number digit to displays
  *  p_tab values in array in ASCII   
  * @retval None
  */ 
void convert_into_char(uint32_t number, uint16_t *p_tab)
{
  uint16_t units=0, tens=0, hundreds=0, thousands=0, misc=0;
  
  units = (((number%10000)%1000)%100)%10;
  tens = ((((number-units)/10)%1000)%100)%10;
  hundreds = (((number-tens-units)/100))%100%10;
  thousands = ((number-hundreds-tens-units)/1000)%10;
  misc = ((number-thousands-hundreds-tens-units)/10000);
  
  *(p_tab+4) = units + 0x30;
  *(p_tab+3) = tens + 0x30;
  *(p_tab+2) = hundreds + 0x30;
  *(p_tab+1) = thousands + 0x30;
  *(p_tab) = misc + 0x30;

}

/**
  * @brief Function to return the VDD measurement
  * @caller All measurements: VDD display or Current
  *
  * Method for VDD measurement:
  * The VREFINT is not stored in memory.
  *   In this case:
  *   Vdd_appli = (Theorical_Vref/Vref mesure) * ADC_Converter
  *   Theorical_Vref = 1.224V
  *   ADC_Converter 4096
  *   ---> LSBIdeal = VREF/4096 or VDA/4096
  * @param None   
  * @retval VDD measurements
  */
float Vdd_appli(void)
{
  uint16_t MeasurINT ;

  float f_Vdd_appli ;
  
  /*Read the BandGap value on ADC converter*/
  MeasurINT = ADC_Supply();	
  
  /* We use the theorical value */
  f_Vdd_appli = (VREF/MeasurINT) * ADC_CONV;

  /* convert Vdd_appli into mV */  
  f_Vdd_appli *= 1000L;
	
  return f_Vdd_appli;
}

/**
  * @brief Function to measure VDD
  * @caller main
  * @param None   
  * @retval Vdd value in mV
  */
uint16_t Vref_measure(void)
{
  uint16_t tab[6];	
  uint16_t Vdd_mV ;
  
  Vdd_mV = (uint16_t)Vdd_appli();

  convert_into_char (Vdd_mV, tab);
	
  /* To add unit and decimal point  */
  tab[5] = 'V';
  tab[4] = ' ';
  tab[1] |= DOT; /* To add decimal point for display in volt */
  tab[0] = ' ';
	
  LCD_GLASS_DisplayStrDeci(tab);

  return Vdd_mV;
}

/**
  * @brief funtion to display the current in µA
  * @caller several funcions
  * @param Current value.
  * @retval none
  */ 
void display_MuAmp (uint32_t Current)
{
  uint16_t tab[6];
          
  convert_into_char(Current, tab);
  tab[5] = 'A';
  tab[4] = 'µ';
		
/* Test the significant digit for displays 3 or 4 digits*/
  if ( tab[0] != '0')
  {
    tab[1] |= DOT; /* To add decimal point */
  }  else  {
    /* To shift for suppress '0' before decimal */
    tab[0] = tab[1] ;	
    tab[0] |= DOT ;
    tab[1] = tab[2] ;
    tab[2] = tab[3] ;		
    tab[3] = ' ';
  }
	
  LCD_GLASS_DisplayStrDeci(tab);
}

/**
  * @brief funtion Current measurement in RUN mode
  * @caller main and test_icc_RUN
  * @param none
  * @retval Current (mA)
  */ 
float Icc_RUN(void)
{
  float Current;
  uint16_t MeasurINT;
  uint16_t tab[6];	
  /* Get Icc current value in Run mode*/	
  MeasurINT = ADC_Icc_Test(MCU_RUN);
  /* Convert value in mA*/	
  Current = MeasurINT * Vdd_appli()/ADC_CONV;
  Current *= 100L; 
  /* Convert value in ASCII and store it into tab*/
  convert_into_char((uint32_t)(Current), tab);
  /* Add unit and decimal point  */
  tab[5] = 'A';
  tab[4] = 'm';
  tab[3] = ' ';
  tab[0] |= DOT; 
  /* Display mesured value */
  LCD_GLASS_DisplayStrDeci(tab);
	
  return (Current);
}

/**
  * @brief funtion Current measurement in SLEEP mode
  * @caller main
  * @param none
  * @retval Current (mA)
  */ 
float Icc_SLEEP(void)
{
  float Current;
  uint16_t MeasurINT;
  uint16_t tab[6];	
  
  /* Get Icc current value in Sleep mode*/	
  MeasurINT = ADC_Icc_Test(MCU_SLEEP);
  /* Substract operational amplifier bias current from value*/
  Current = MeasurINT * Vdd_appli()/ADC_CONV;  
  /* Convert value in mA*/	
  Current *= 100L;
  /* Convert value in ASCII and store it into tab*/
  convert_into_char((uint32_t)(Current), tab);
  /* Add unit and decimal point  */
  tab[5] = 'A';
  tab[4] = 'm';
  tab[3] = ' ';
  tab[0] |= DOT; 
  /*Display mesured value */
  LCD_GLASS_DisplayStrDeci(tab);
  /* Return value in mA*/
  return(Current);
}

/**
  * @brief funtion Current measurement in Low power
  * @caller main
  * @param none
  * @retval Current (uA)
  */ 
float Icc_LPRUN(void)
{
  float Current;
  uint16_t MeasurINT;

  /* Get Icc current value in Low power mode*/
  MeasurINT = ADC_Icc_Test(MCU_LP_RUN);
  /* Substract operational amplifier bias current from value*/
  if ( MeasurINT > Bias_Current )
    MeasurINT -= Bias_Current;
  /* Convert value in uA*/	
  Current = MeasurINT * Vdd_appli()/ADC_CONV;  
  Current *= 20L;
  /* Display mesured value */
  display_MuAmp((uint32_t)Current);
  /* Return value in uA*/	
  return(Current);
}

/**
  * @brief funtion Current measurement in Low power
  * @caller main
  * @param none
  * @retval Current (µA)
  */ 
float Icc_LPSLEEP(void)
{
  float Current;
  uint16_t MeasurINT;
  /* Get Icc current value in Low power sleep mode*/
  MeasurINT = ADC_Icc_Test(MCU_LP_SLEEP);
  /* Substract operational amplifier bias current from value*/
  if ( MeasurINT > Bias_Current )
    MeasurINT -= Bias_Current;
  /* Convert value in uA*/
  Current = MeasurINT * Vdd_appli()/ADC_CONV;  
  Current *= 20L;
  /* Test if value is correct */
  if ((int) Current<MAX_CURRENT)
  {
    /* if correct : Display mesured value */
    display_MuAmp((uint32_t)Current);
  } else{
    /* if not correct : Display ERROR */
    LCD_GLASS_Clear();
    LCD_GLASS_DisplayString("Error");
  }
  /* Return value in uA*/
  return(Current);
}

/**
  * @brief funtion Current measurement in Stop mode with LCD ON
  * @caller main and test_icc_LCD
  * @param none
  * @retval Current (µA)
  */
float Icc_STOP(void)
{
  float Current;
  uint16_t MeasurINT;
  
   /* Get Icc current value in STOP mode*/	
  MeasurINT = ADC_Icc_Test(MCU_STOP_RTC); 
  /* Substract operational amplifier bias current from value*/
  if ( MeasurINT > Bias_Current )
      MeasurINT -= Bias_Current;
  /* Convert value in uA*/
  Current = MeasurINT * Vdd_appli()/ADC_CONV; 
  Current *= 20L; 
  /* test if value is correct */
  if ((int) Current<MAX_CURRENT)
  {
    /* if correct : Display mesured value */
    display_MuAmp((uint32_t)Current);
  }
  else
  {
    /* if not correct : Display error if not in autotest */
    if (!self_test)
    {
      LCD_GLASS_Clear();
      LCD_GLASS_DisplayString("Error");
    }
  }
  /* Return value in uA*/
  return (Current);
}

/**
  * @brief funtion Current measurement in Stop mode with LCD OFF
  * @caller main
  * @param none
  * @retval none
  */
float Icc_Stop_NoRTC(void)
{
  float Current;
  uint16_t MeasurINT;
	
  /* Get Icc current value in STOP mode with no RTC */	
  MeasurINT = ADC_Icc_Test(MCU_STOP_NoRTC);
  /* Substract operational amplifier bias current from value*/
  if ( MeasurINT > Bias_Current )
    MeasurINT -=	Bias_Current;
  /* Convert value in uA*/
  Current = MeasurINT * Vdd_appli()/ADC_CONV; 
  Current *= 20L;
  /* Display mesured value */  
  display_MuAmp((uint32_t)Current);
  /* Return value in uA*/
  return (Current);
}	

/******************* (C) COPYRIGHT 2011 STMicroelectronics *****END OF FILE****/
