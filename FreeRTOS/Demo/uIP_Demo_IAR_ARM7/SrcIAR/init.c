//*----------------------------------------------------------------------------
//*         ATMEL Microcontroller Software Support  -  ROUSSET  -
//*----------------------------------------------------------------------------
//* The software is delivered "AS IS" without warranty or condition of any
//* kind, either express, implied or statutory. This includes without
//* limitation any warranty or condition with respect to merchantability or
//* fitness for any particular purpose, or against the infringements of
//* intellectual property rights of others.
//*----------------------------------------------------------------------------
//* File Name           : init.c
//* Object              : Low level initialisations written in C
//* Creation            : ODi   06/26/2002
//*
//*----------------------------------------------------------------------------
#include "board.h"
//#include "init.h"
#include <string.h>

//*----------------------------------------------------------------------------
//* \fn    AT91F_DBGU_Printk
//* \brief This function is used to send a string through the DBGU channel (Very low level debugging)
//*----------------------------------------------------------------------------
void AT91F_DBGU_Printk(
	char *buffer) // \arg pointer to a string ending by \0
{
	while(*buffer != '\0') {
		while (!AT91F_US_TxReady((AT91PS_USART)AT91C_BASE_DBGU));
		AT91F_US_PutChar((AT91PS_USART)AT91C_BASE_DBGU, *buffer++);
	}
}

