//*----------------------------------------------------------------------------
//*         ATMEL Microcontroller Software Support  -  ROUSSET  -
//*----------------------------------------------------------------------------
//* The software is delivered "AS IS" without warranty or condition of any
//* kind, either express, implied or statutory. This includes without
//* limitation any warranty or condition with respect to merchantability or
//* fitness for any particular purpose, or against the infringements of
//* intellectual property rights of others.
//*----------------------------------------------------------------------------
//* File Name           : dbgu.c
//* Object              : DBGU routines written in C
//* Creation            : JG   16/Aug/2004
//*----------------------------------------------------------------------------

// Include Standard files
#include "Board.h"

//*--------------------------1--------------------------------------------------
//* \fn    AT91F_DBGU_Printk
//* \brief This function is used to send a string through the DBGU channel (Very low level debugging)
//*----------------------------------------------------------------------------
void AT91F_DBGU_Printk(	char *buffer)
{
    AT91PS_DBGU pDbgu = AT91C_BASE_DBGU ; 
    unsigned int temp;
    
    while(*buffer != '\0') 
    {
        temp=0;
        
	while (temp==0)
	{
	  if ( (pDbgu->DBGU_CSR & 0x0200) == 0)
	    temp=0;
	  else
	    temp=1;
	}

        pDbgu->DBGU_THR = *buffer;
        buffer++;
    }
}


void Init_DBGU_CLK(void)
{
  AT91F_PMC_EnablePeriphClock(AT91C_BASE_PMC, ((unsigned int) 1 << AT91C_ID_SYS));
}

void Init_DBGU_BGR(unsigned short baud)
{
  AT91PS_DBGU pDbgu = AT91C_BASE_DBGU ; 
  
  pDbgu->DBGU_BRGR = (unsigned short)baud;
}

void DBGU_TX_Enable(void)
{
  AT91PS_DBGU pDbgu = AT91C_BASE_DBGU ; 
  
  pDbgu->DBGU_CR = 0x00000040;
}

void DBGU_RX_Enable(void)
{
  AT91PS_DBGU pDbgu = AT91C_BASE_DBGU ; 
  
  pDbgu->DBGU_CR = 0x00000010;
}

void DBGU_RX_TX_RST_DIS(void)
{
  AT91PS_DBGU pDbgu = AT91C_BASE_DBGU ; 
  pDbgu->DBGU_CR = 0x000000AC;
}

void DBGU_Parity_Cfg(unsigned int par)
{
  AT91PS_DBGU pDbgu = AT91C_BASE_DBGU ; 
  
  pDbgu->DBGU_MR = par << 9;
}


void Init_DBGU(void)
{ 
  AT91F_DBGU_CfgPIO();
  DBGU_RX_TX_RST_DIS();
  Init_DBGU_BGR(26);  //26 <=> 115kBd
  DBGU_Parity_Cfg(4);
  DBGU_TX_Enable();   
  DBGU_RX_Enable();
}


