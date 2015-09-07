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
* Copyright (C) 2014 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* System Name  : RZ/T1 SCIF program
* File Name    : siorw.c
* Version      : 0.1
* Device       : R7S910018
* Abstract     : Serial I/O settings controlling the read and write command
* Tool-Chain   : GNUARM-NONEv14.02-EABI
* OS           : not use
* H/W Platform : Renesas Starter Kit for RZ/T1(Preliminary)
* Description  : Control the read/write command with serial I/O  
* Limitation   : none
***********************************************************************************************************************/
/***********************************************************************************************************************
* History      : DD.MM.YYYY Version  Description
*              : 21.05.2015 1.00     First Release
***********************************************************************************************************************/


/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include <stdio.h>
#include "r_cg_macrodriver.h"
#include "r_cg_userdefine.h" 
#include "r_cg_scifa.h"
#include "siochar.h"


/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/


/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
/* File descriptor */
#define STDIN           (0)
#define STDOUT          (1)
#define STDERR          (2)

#define SIORW_SUCCESS   (0)
#define SIORW_ERROR     (-1)
#define SIORW_FLAG_OFF  (0)
#define SIORW_FLAG_ON   (1)


/***********************************************************************************************************************
Imported global variables and functions (from other files)
***********************************************************************************************************************/


/***********************************************************************************************************************
Exported global variables and functions (to be accessed by other files)
***********************************************************************************************************************/


/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/


/***********************************************************************************************************************
* Function Name: sio_write
* Description  : The character strings specified with buffer is output for n
*              : bytes from serial port. The output is determined by file number fileno.
*              : The effective outputs in this version are STDOUT and STDERR, and
*              : it is output to the same serial port.
*              : The line-feed code '\n'(LF) is converted in '\r'(CR)+'\n'(LF) to output.
* Arguments    : int32_t  file_no  ; I : File number to be the target of writing
*              : int_t  * buffer   ; O : Pointer to the area in which writing data is stored
*              : uint32_t writing_b; I : Writing bytes
* Return Value : >=0 : Number of transmitting characters
*              : -1  : File number error
***********************************************************************************************************************/
int32_t sio_write (int32_t file_no, const char * buffer, uint32_t writing_b)
{
    uint32_t offset;

    if ((STDOUT == file_no) || (STDERR == file_no))
    {
        for (offset = 0; offset < writing_b; offset++)

        {
            /* Writing in buffer converting line-feed code */
            if ('\n' == (*(buffer + offset)))
            {
                if (0 == offset)
                {
                    io_put_char('\r');
                }
                else
                {
                    if ('\r' != (*((buffer + offset) - 1)))
                    {
                        io_put_char('\r');
                    }
                }
                io_put_char('\n');
            }
            else
            {
                io_put_char(*(buffer + offset));
            }
        }
        return ((int32_t)offset);
    }

    /* File number error */
    return SIORW_ERROR;
}

/***********************************************************************************************************************
 * End of function sio_write
***********************************************************************************************************************/

/***********************************************************************************************************************
* Function Name: sio_read
* Description  : The character strings specified with buffer is input for
*              : n bytes from serial port.The input is determined by file number fileno.
*              : The effective input in this version is STDIN.
* Arguments    : int32_t  file_no  ; I : File number to be the target of reading
*              : int_t  * buffer   ; O : Pointer to the area in which reading data is stored
*              : uint32_t reading_b; I : Reading bytes
* Return Value : >0 : Number of receiving characters
*              : -1 : File number, receiving data error
***********************************************************************************************************************/
int32_t sio_read (int32_t file_no, char * buffer, uint32_t reading_b)
{
    int32_t        char_mem;
    int32_t        sp_char;
    uint32_t       offset;
    static int32_t sjis_flg = SIORW_FLAG_OFF;

    if (STDIN == file_no)
    {
        for (offset = 0; offset < reading_b; )
        {
            /* Reading receiving data */
            char_mem = io_get_char();

            /* -1 is returned when it is receiving data error */
            if ((-1) == char_mem)
            {
                return SIORW_ERROR;
            }

            if (SIORW_FLAG_ON == sjis_flg)
            {
                sjis_flg = SIORW_FLAG_OFF;
                sio_write(STDOUT, (char *)&char_mem, 1);

                (*(buffer + offset)) = (char)char_mem;
                offset++;
            }
            if ((0x20 <= char_mem) && (char_mem <= 0x7E))
            {
                /* Data possible to display */
                sio_write(STDOUT, (char *)&char_mem, 1);
                (*(buffer + offset)) = (char)char_mem;
                offset++;
            }

            /* BS process */
            if (('\b' == char_mem) && (offset > 0))
            {  sp_char = 0x20;
                sio_write(STDOUT, (char *)&char_mem, 1);
                sio_write(STDOUT, (char *)&sp_char, 1);
                sio_write(STDOUT, (char *)&char_mem, 1);
                offset--;
            }

            /* CR process */
            if ('\r' == char_mem)
            {
                (*(buffer + offset)) = '\n';
                sio_write(STDOUT, buffer + offset, 1);
                offset++;
            }

            /* Japanese SJIS ? */
            if (((char_mem >= 0x80) && (char_mem < 0xA0)) || ((char_mem >= 0xE0) && (char_mem < 0xFE)))
            {
                /* Data possible to display */
                sio_write(STDOUT, (char *)&char_mem, 1);
                (*(buffer + offset)) = (char)char_mem;
                offset++;
                sjis_flg = SIORW_FLAG_ON;
            }
        }
        return ((int32_t)offset);
    }

    /* File number error */
    return SIORW_ERROR;
}

/***********************************************************************************************************************
 End of function sio_read
***********************************************************************************************************************/


/* End of File */

