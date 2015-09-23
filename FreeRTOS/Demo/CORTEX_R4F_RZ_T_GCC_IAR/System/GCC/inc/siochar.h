/***********************************************************************************************************************
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
* Copyright (C) 2014 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name     : siochar.h
* Device(s)     : RZ/A1H (R7S910018)
* Tool-Chain    : GNUARM-NONEv14.02-EABI
* H/W Platform  : RSK+T1 CPU Board
* Description   : Sample Program - Terminal I/O header file
***********************************************************************************************************************/
/***********************************************************************************************************************
* History       : DD.MM.YYYY Version Description
*               : 21.10.2014 1.00
***********************************************************************************************************************/

/* Multiple inclusion prevention macro */
#ifndef SIO_CHAR_H
#define SIO_CHAR_H

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/

/***********************************************************************************************************************
Functions Prototypes
***********************************************************************************************************************/
int32_t sio_write (int32_t file_no, const char * buffer, uint32_t writing_b);
int32_t sio_read (int32_t file_no, char * buffer, uint32_t reading_b);

void    io_init_scifa2 (void);
char    io_get_char (void);
void    io_put_char (char buffer);

/* SIO_CHAR_H */
#endif  

/* End of File */
