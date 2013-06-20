/*******************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only
* intended for use with Renesas products. No other uses are authorized. This
* software is owned by Renesas Electronics Corporation and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT
* LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE
* AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
* ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR
* ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE
* BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software
* and to discontinue the availability of this software. By using this software,
* you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.
*******************************************************************************/
/*******************************************************************************
* File Name    : retarget.c
* $Rev: $
* $Date::                           $
* Device(s)    : Aragon
* Tool-Chain   : DS-5 Ver 5.13
*              : ARM Complier
* OS           : 
* H/W Platform : Aragon CPU Board
* Description  : Aragon Sample Program - Retarget standard I/O
* Operation    : 
* Limitations  : 
*******************************************************************************/

        #ifdef        __STANDALONE__

/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include <stdio.h>
#include "r_typedefs.h"
#include "sio_char.h"

#pragma import(__use_no_semihosting)

/******************************************************************************
Typedef definitions
******************************************************************************/
struct __FILE
{
  int_t handle;

  /* Whatever you require here. If the only file you are using is   */
  /* standard output using printf() for debugging, no file handling */
  /* is required.                                                   */
};

/******************************************************************************
Macro definitions
******************************************************************************/
/* File descriptor */
#define STDIN       (0)
#define STDOUT      (1)
#define STDERR      (2)

#define IOSTREAM    (1)
#define BUFF_SIZE   (256)

#if 0
#define DEFAULT_HANDLE  (0x100)
#endif

/******************************************************************************
Imported global variables and functions (from other files)
******************************************************************************/

/******************************************************************************
Exported global variables and functions (to be accessed by other files)
******************************************************************************/
FILE __stdout;
FILE __stdin;
#if 0
FILE __stderr;
#endif

/******************************************************************************
Private global variables and functions
******************************************************************************/

/******************************************************************************
* Function Name: fgetc
* Description  :
* Arguments    :
* Return Value :
******************************************************************************/
int_t fgetc(FILE * file_p)
{
    /* no character to read */
    return EOF;
}

/******************************************************************************
* Function Name: fputc
* Description  :
* Arguments    :
* Return Value :
******************************************************************************/
int_t fputc(int_t channel, FILE * file_p)
{
     return channel;
}

/******************************************************************************
* Function Name: ferror
* Description  : 
* Arguments    : 
* Return Value : 
******************************************************************************/
int_t ferror(FILE * file_p)
{
    return 0;
}

int_t __backspace(FILE * file_p)
{
    return 0;
}


void _sys_exit(int_t returncode)
{
    while (1)
    {
        /* Do Nothing */
    }
}

char_t * _sys_command_string(char_t * cmd, int_t len)
{
    return cmd;
}

    #endif        /* __STANDALONE__    セミホスティング無効    */

/* End of File */

