/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products. No
* other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED. TO THE MAXIMUM
* EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES
* SHALL BE LIABLE FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS
* SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability of
* this software. By using this software, you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2013 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : lowsrc.c
* Description  : Functions to support stream I/O
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 28.02.2019 3.00     Merged processing of all devices.
*                               Added support for GNUC and ICCRX.
*                               Fixed coding style.
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#if defined(__CCRX__)
#include <string.h>
#include <stdio.h>
#endif /* defined(__CCRX__) */
#include "r_bsp_common.h"
#include "r_bsp_config.h"
#include "lowlvl.h"
#include "lowsrc.h"


/* When using the user startup program, disable the following code. */
#if BSP_CFG_STARTUP_DISABLE == 0

/* Do not include this file if stdio is disabled in r_bsp_config. */
#if BSP_CFG_IO_LIB_ENABLE == 1

#if defined(__CCRX__)

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
/*Number of I/O Stream*/
#define BSP_PRV_IOSTREAM (20)

/* file number */
#define BSP_PRV_STDIN    (0)    /* Standard input (console) */
#define BSP_PRV_STDOUT   (1)    /* Standard output (console) */
#define BSP_PRV_STDERR   (2)    /* Standard error output (console) */

#define BSP_PRV_FLMIN    (0)    /* Minimum file number */
#define BSP_PRV_MOPENR   (0x1)
#define BSP_PRV_MOPENW   (0x2)
#define BSP_PRV_MOPENA   (0x4)
#define BSP_PRV_MTRUNC   (0x8)
#define BSP_PRV_MCREAT   (0x10)
#define BSP_PRV_MBIN     (0x20)
#define BSP_PRV_MEXCL    (0x40)
#define BSP_PRV_MALBUF   (0x40)
#define BSP_PRV_MALFIL   (0x80)
#define BSP_PRV_MEOF     (0x100)
#define BSP_PRV_MERR     (0x200)
#define BSP_PRV_MLBF     (0x400)
#define BSP_PRV_MNBF     (0x800)
#define BSP_PRV_MREAD    (0x1000)
#define BSP_PRV_MWRITE   (0x2000)
#define BSP_PRV_MBYTE    (0x4000)
#define BSP_PRV_MWIDE    (0x8000)
/* File Flags */
#define BSP_PRV_O_RDONLY (0x0001)  /* Read only */
#define BSP_PRV_O_WRONLY (0x0002)  /* Write only */
#define BSP_PRV_O_RDWR   (0x0004)  /* Both read and Write */
#define BSP_PRV_O_CREAT  (0x0008)  /* A file is created if it is not existed */
#define BSP_PRV_O_TRUNC  (0x0010)  /* The file size is changed to 0 if it is existed. */
#define BSP_PRV_O_APPEND (0x0020)  /* The position is set for next reading/writing
                                      0: Top of the file 1: End of file */

/* Special character code */
#define BSP_PRV_CR (0x0d) /* Carriage return */
#define BSP_PRV_LF (0x0a) /* Line feed */

#define BSP_PRV_FPATH_STDIN     "C:\\stdin"
#define BSP_PRV_FPATH_STDOUT    "C:\\stdout"
#define BSP_PRV_FPATH_STDERR    "C:\\stderr"

#ifdef _REENTRANT
// For Reentrant Library (generated lbgrx with -reent option)
#define BSP_PRV_MALLOC_SEM   (1)  /* Semaphore No. for malloc */
#define BSP_PRV_STRTOK_SEM   (2)  /* Semaphore No. for strtok */
#define BSP_PRV_FILE_TBL_SEM (3)  /* Semaphore No. for fopen  */
#define BSP_PRV_MBRLEN_SEM   (4)  /* Semaphore No. for mbrlen */
#define BSP_PRV_FPSWREG_SEM  (5)  /* Semaphore No. for FPSW register */
#define BSP_PRV_FILES_SEM    (6)  /* Semaphore No. for _Files */
#define BSP_PRV_SEMSIZE      (26) /* BSP_PRV_FILES_SEM + _nfiles (assumed _nfiles=20) */

#define BSP_PRV_TRUE  (1)
#define BSP_PRV_FALSE (0)
#define BSP_PRV_OK    (1)
#define BSP_PRV_NG    (0)
#endif /* _REENTRANT */

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Exported global variables (to be accessed by other files)
***********************************************************************************************************************/
extern const long _nfiles;     /* The number of files for input/output files */
char flmod[BSP_PRV_IOSTREAM];          /* The location for the mode of opened file. */

unsigned char sml_buf[BSP_PRV_IOSTREAM];

FILE *_Files[BSP_PRV_IOSTREAM]; /* structure for FILE */
char *env_list[] = {            /* Array for environment variables(**environ) */
    "ENV1=temp01",
    "ENV2=temp02",
    "ENV9=end",
    '\0'                        /* Terminal for environment variables */
};

char **environ = env_list;

/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/
#ifdef _REENTRANT
static long sem_errno;
static int force_fail_signal_sem = BSP_PRV_FALSE;
static int semaphore[BSP_PRV_SEMSIZE];
#endif /* _REENTRANT */

/***********************************************************************************************************************
* Function Name: init_iolib
* Description  : Initialize C library Functions, if necessary. Define USES_SIMIO on Assembler Option.
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
void init_iolib(void)
{
    /* A file for standard input/output is opened or created. Each FILE
     * structure members are initialized by the library. Each _Buf member
     * in it is re-set the end of buffer pointer.
     */

    /* Initializations of File Stream Table */
    _Files[0] = stdin;
    _Files[1] = stdout;
    _Files[2] = stderr;

    /* Standard Input File */
    if( freopen( BSP_PRV_FPATH_STDIN, "r", stdin ) == NULL )
    {
        stdin->_Mode = 0xffff;  /* Not allow the access if it fails to open */
    }
    stdin->_Mode  = BSP_PRV_MOPENR;         /* Read only attribute */
    stdin->_Mode |= BSP_PRV_MNBF;           /* Non-buffering for data */
    stdin->_Bend = stdin->_Buf + 1;  /* Re-set pointer to the end of buffer */

    /* Standard Output File */
    if( freopen( BSP_PRV_FPATH_STDOUT, "w", stdout ) == NULL ) 
    {
        stdout->_Mode = 0xffff; /* Not allow the access if it fails to open */
    }
    stdout->_Mode |= BSP_PRV_MNBF;            /* Non-buffering for data */
    stdout->_Bend = stdout->_Buf + 1;  /* Re-set pointer to the end of buffer */
    
    /* Standard Error File */
    if( freopen( BSP_PRV_FPATH_STDERR, "w", stderr ) == NULL )
    {
        stderr->_Mode = 0xffff;  /* Not allow the access if it fails to open */
    }
    stderr->_Mode |= BSP_PRV_MNBF;             /* Non-buffering for data */
    stderr->_Bend = stderr->_Buf + 1;/* Re-set pointer to the end of buffer */
} /* End of function init_iolib() */

/***********************************************************************************************************************
* Function Name: close_all
* Description  : Colses the file
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
void close_all(void)
{
    long i;

    /* WAIT_LOOP */
    for( i=0; i < _nfiles; i++ )
    {
        /* Checks if the file is opened or not */
        if( _Files[i]->_Mode & (BSP_PRV_MOPENR | BSP_PRV_MOPENW | BSP_PRV_MOPENA ) )
        {
            fclose( _Files[i] );    /* Closes the file */
        }
    }
} /* End of function close_all() */

/***********************************************************************************************************************
* Function Name: open
* Description  : file open
* Arguments    : name - File name
*                mode - Open mode
*                flg - Open flag
* Return Value : File number (Pass)
*                -1          (Failure)
***********************************************************************************************************************/
long open(const char *name, long  mode, long  flg)
{
    /* This code is only used to remove compiler info messages about these parameters not being used. */
    INTERNAL_NOT_USED(flg);

    if( 0 == strcmp( name, BSP_PRV_FPATH_STDIN ) )       /* Standard Input file? */
    {
        if( 0 == ( mode & BSP_PRV_O_RDONLY ) )
        {
            return -1;
        }
        flmod[BSP_PRV_STDIN] = mode;
        return BSP_PRV_STDIN;
    }
    else if( 0 == strcmp( name, BSP_PRV_FPATH_STDOUT ) ) /* Standard Output file? */
    {
        if( 0 == ( mode & BSP_PRV_O_WRONLY ) )
        {
            return -1;
        }
        flmod[BSP_PRV_STDOUT] = mode;
        return BSP_PRV_STDOUT;
    }
    else if( 0 == strcmp(name, BSP_PRV_FPATH_STDERR ) )   /* Standard Error file? */
    {
        if( 0 == ( mode & BSP_PRV_O_WRONLY ) )
        {
            return -1;
        }
        flmod[BSP_PRV_STDERR] = mode;
        return BSP_PRV_STDERR;
    }
    else
    {
        return -1;                              /*Others */
    }
} /* End of function open() */

/***********************************************************************************************************************
* Function Name: close
* Description  : dummy
* Arguments    : fileno - File number
* Return Value : 1
***********************************************************************************************************************/
long close(long fileno)
{
    /* This code is only used to remove compiler info messages about these parameters not being used. */
    INTERNAL_NOT_USED(fileno);

    return 1;
} /* End of function close() */

/***********************************************************************************************************************
* Function Name: write
* Description  : Data write
* Arguments    : fileno - File number
*                buf - The address of destination buffer
*                count - The number of chacter to write
* Return Value : Number of write characters (Pass)
*                -1                         (Failure)
***********************************************************************************************************************/
long write(long  fileno, const unsigned char *buf, long  count)
{
    long    i;                          /* A variable for counter */
    unsigned char    c;                 /* An output character */

    /* Checking the mode of file , output each character
     * Checking the attribute for Write-Only, Read-Only or Read-Write
     */
    if((flmod[fileno]&BSP_PRV_O_WRONLY) || (flmod[fileno]&BSP_PRV_O_RDWR))
    {
        if( BSP_PRV_STDIN == fileno )
        {
            return -1;            /* Standard Input */
        }
        else if( (BSP_PRV_STDOUT == fileno) || (BSP_PRV_STDERR == fileno) ) /* Standard Error/output */
        {
            /* WAIT_LOOP */
            for( i = count; i > 0; --i )
            {
                c = *buf++;
                charput(c);
            }
            return count;        /*Return the number of written characters */
        }
        else
        {
            return -1;                  /* Incorrect file number */
        }
    }
    else
    {
        return -1;                      /* An error */
    }
} /* End of function write() */

/***********************************************************************************************************************
* Function Name: read
* Description  : Data read
* Arguments    : fileno - File number
*                buf - The address of destination buffer
*                count - The number of chacter to read
* Return Value : Number of read characters (Pass)
*                -1                        (Failure)
***********************************************************************************************************************/
long read(long fileno, unsigned char *buf, long count)
{
       long i;

       /* Checking the file mode with the file number, each character is input and stored the buffer */

       if((flmod[fileno]&BSP_PRV_MOPENR) || (flmod[fileno]&BSP_PRV_O_RDWR))
       {
             /* WAIT_LOOP */
             for(i = count; i > 0; i--)
             {
                   *buf = charget();
                   if(BSP_PRV_CR == (*buf))
                   {
                         *buf = BSP_PRV_LF; /* Replace the new line character */
                   }
                   buf++;
             }
             return count;
       }
       else 
       {
             return -1;
       }
} /* End of function read() */

/***********************************************************************************************************************
* Function Name: lseek
* Description  : dummy
* Arguments    : fileno - File number
*                offset - Offset indicating reading / writing position
*                base - Offset starting point
* Return Value : -1L
***********************************************************************************************************************/
long lseek(long fileno, long offset, long base)
{
    /* This code is only used to remove compiler info messages about these parameters not being used. */
    INTERNAL_NOT_USED(fileno);

    /* This code is only used to remove compiler info messages about these parameters not being used. */
    INTERNAL_NOT_USED(offset);

    /* This code is only used to remove compiler info messages about these parameters not being used. */
    INTERNAL_NOT_USED(base);

    return -1L;
} /* End of function lseek() */

#ifdef _REENTRANT
/***********************************************************************************************************************
* Function Name: errno_addr
* Description  : Acquisition of errno address
* Arguments    : none
* Return Value : errno address
***********************************************************************************************************************/
long *errno_addr(void)
{
    /* Return the errno address of the current task */
    return (&sem_errno);
}

/***********************************************************************************************************************
* Function Name: wait_sem
* Description  : Defines the specified numbers of semaphores
* Arguments    : semnum - Semaphore ID
* Return Value : BSP_PRV_OK(=1) (Normal)
*                BSP_PRV_NG(=0) (Error)
***********************************************************************************************************************/
long wait_sem(long semnum) /* Semaphore ID */
{
    if((0 < semnum) && (semnum < BSP_PRV_SEMSIZE)) {
        if(semaphore[semnum] == BSP_PRV_FALSE) {
            semaphore[semnum] = BSP_PRV_TRUE;
            return(BSP_PRV_OK);
        }
    }
    return(BSP_PRV_NG);
}

/***********************************************************************************************************************
* Function Name: signal_sem
* Description  : Releases the specified numbers of semaphores
* Arguments    : semnum - Semaphore ID
* Return Value : BSP_PRV_OK(=1) (Normal)
*                BSP_PRV_NG(=0) (Error)
***********************************************************************************************************************/
long signal_sem(long semnum) /* Semaphore ID */
{
    if(!force_fail_signal_sem) {
        if((0 <= semnum) && (semnum < BSP_PRV_SEMSIZE)) {
            if( semaphore[semnum] == BSP_PRV_TRUE ) {
                semaphore[semnum] = BSP_PRV_FALSE;
                return(BSP_PRV_OK);
            }
        }
    }
    return(BSP_PRV_NG);
}
#endif /* _REENTRANT */

#endif /* defined(__CCRX__) */

#endif /* BSP_CFG_IO_LIB_ENABLE */

#if defined(__GNUC__)
/***********************************************************************************************************************
* Function Name: write
* Description  : Data write (for GNURX+NEWLIB)
* Arguments    : fileno - File number
*                buf - The address of destination buffer
*                count - The number of chacter to write
* Return Value : Number of write characters (Pass)
***********************************************************************************************************************/
int write(int fileno, char *buf, int count)
{
    int i;
    char c;

    /* This code is only used to remove compiler info messages about these parameters not being used. */
    INTERNAL_NOT_USED(fileno);

    /* WAIT_LOOP */
    for(i = count; i > 0; --i)
    {
       c = *buf++;
       charput(c);
    }

    return count;
}

/***********************************************************************************************************************
* Function Name: read
* Description  : Data read (for GNURX+NEWLIB)
* Arguments    : fileno - File number
*                buf - The address of destination buffer
*                count - The number of chacter to read
* Return Value : 1 (Pass)
***********************************************************************************************************************/
int read(int fileno, char *buf, int count)
{
    /* This code is only used to remove compiler info messages about these parameters not being used. */
    INTERNAL_NOT_USED(fileno);
    INTERNAL_NOT_USED(count);

    *buf = charget();
    return 1;
}

/***********************************************************************************************************************
* Function Name: _write
* Description  : Data write (for GNURX+OPTLIB)
* Arguments    : fileno - File number
*                buf - The address of destination buffer
*                count - The number of chacter to write
* Return Value : Number of write characters (Pass)
***********************************************************************************************************************/
int _write(int fileno, char *buf, int count)
{
    int i;
    char c;

    /* This code is only used to remove compiler info messages about these parameters not being used. */
    INTERNAL_NOT_USED(fileno);

    /* WAIT_LOOP */
    for(i = count; i > 0; --i)
    {
       c = *buf++;
       charput(c);
    }

    return count;
}

/***********************************************************************************************************************
* Function Name: read
* Description  : Data read (for GNURX+OPTLIB)
* Arguments    : fileno - File number
*                buf - The address of destination buffer
*                count - The number of chacter to read
* Return Value : 1 (Pass)
***********************************************************************************************************************/
int _read(int fileno, char *buf, int count)
{
    /* This code is only used to remove compiler info messages about these parameters not being used. */
    INTERNAL_NOT_USED(fileno);
    INTERNAL_NOT_USED(count);

    *buf = charget();
    return 1;
}

/***********************************************************************************************************************
* Function Name: close
* Description  : dummy
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
void close (void)
{
    /* This is dummy function.
       This function is used to suppress the warning messages of GNU compiler.
       Plese edit the function as required. */
}

/***********************************************************************************************************************
* Function Name: fstat
* Description  : dummy
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
void fstat (void)
{
    /* This is dummy function.
       This function is used to suppress the warning messages of GNU compiler.
       Plese edit the function as required. */
}

/***********************************************************************************************************************
* Function Name: isatty
* Description  : dummy
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
void isatty (void)
{
    /* This is dummy function.
       This function is used to suppress the warning messages of GNU compiler.
       Plese edit the function as required. */
}

/***********************************************************************************************************************
* Function Name: lseek
* Description  : dummy
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
void lseek (void)
{
    /* This is dummy function.
       This function is used to suppress the warning messages of GNU compiler.
       Plese edit the function as required. */
}

#endif /* defined(__GNUC__) */

#endif /* BSP_CFG_STARTUP_DISABLE == 0 */

