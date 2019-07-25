/**************************************************************************//**
 * @file     retarget.c
 * @version  V3.00
 * @brief    Debug Port and Semihost Setting Source File
 *
 * @note
 * Copyright (C) 2016 Nuvoton Technology Corp. All rights reserved.
 *
 ******************************************************************************/


#include <stdio.h>
#include "NuMicro.h"

#if defined (__ICCARM__)
# pragma diag_suppress=Pm150
#endif


#if defined ( __CC_ARM   )
#if (__ARMCC_VERSION < 400000)
#else
/* Insist on keeping widthprec, to avoid X propagation by benign code in C-lib */
#pragma import _printf_widthprec
#endif
#endif

/*---------------------------------------------------------------------------------------------------------*/
/* Global variables                                                                                        */
/*---------------------------------------------------------------------------------------------------------*/
#if !(defined(__ICCARM__) && (__VER__ >= 6010000))
# if (__ARMCC_VERSION < 6040000)
struct __FILE
{
    int handle; /* Add whatever you need here */
};
# endif
#elif(__VER__ >= 8000000)
struct __FILE
{
    int handle; /* Add whatever you need here */
};
#endif
FILE __stdout;
FILE __stdin;


#if (defined(__ARMCC_VERSION) || defined(__ICCARM__))
extern int32_t SH_DoCommand(int32_t n32In_R0, int32_t n32In_R1, int32_t *pn32Out_R0);

#if defined( __ICCARM__ )
__WEAK
#else
__attribute__((weak))
#endif
uint32_t ProcessHardFault(uint32_t lr, uint32_t msp, uint32_t psp);

#endif 

int kbhit(void);
int IsDebugFifoEmpty(void);
void _ttywrch(int ch);
int fputc(int ch, FILE *stream);

#if (defined(__ARMCC_VERSION) || defined(__ICCARM__))
int fgetc(FILE *stream);
int ferror(FILE *stream);
#endif

char GetChar(void);
void SendChar_ToUART(int ch);
void SendChar(int ch);

#if defined(DEBUG_ENABLE_SEMIHOST)
#if (defined(__ARMCC_VERSION) || defined(__ICCARM__))
/* The static buffer is used to speed up the semihost */
static char g_buf[16];
static char g_buf_len = 0;
static volatile int32_t g_ICE_Conneced = 1;

/**
 * @brief    This function is called by Hardfault handler.
 * @param    None
 * @returns  None
 * @details  This function is called by Hardfault handler and check if it is caused by __BKPT or not.
 *
 */

uint32_t ProcessHardFault(uint32_t lr, uint32_t msp, uint32_t psp)
{
    uint32_t *sp;
    uint32_t inst;

    /* Check the used stack */
    if(lr & 0x40)
    {
        /* Secure stack used */
        if(lr & 4)
            sp = (uint32_t *)psp;
        else
            sp = (uint32_t *)msp;
    
    }
#if defined (__ARM_FEATURE_CMSE) &&  (__ARM_FEATURE_CMSE == 3U)    
    else
    {
        /* Non-secure stack used */
        if(lr & 4)
            sp = (uint32_t *)__TZ_get_PSP_NS();
        else
            sp = (uint32_t *)__TZ_get_MSP_NS();
    
    }
#endif    
        
    /* Get the instruction caused the hardfault */
    inst = M16(sp[6]);
    
    
    if(inst == 0xBEAB)
    {
        /* 
            If the instruction is 0xBEAB, it means it is caused by BKPT without ICE connected.
            We still return for output/input message to UART.
        */
        g_ICE_Conneced = 0; // Set a flag for ICE offline
        sp[6] += 2; // return to next instruction
        return lr;  // Keep lr in R0
    }
    
    /* It is casued by hardfault (Not semihost). Just process the hard fault here. */
    /* TODO: Implement your hardfault handle code here */
    
    /*
    printf("  HardFault!\n\n");
    printf("r0  = 0x%x\n", sp[0]);
    printf("r1  = 0x%x\n", sp[1]);
    printf("r2  = 0x%x\n", sp[2]);
    printf("r3  = 0x%x\n", sp[3]);
    printf("r12 = 0x%x\n", sp[4]);
    printf("lr  = 0x%x\n", sp[5]);
    printf("pc  = 0x%x\n", sp[6]);
    printf("psr = 0x%x\n", sp[7]);
    */
    
    while(1){}
    
}



/**
 *
 * @brief      The function to process semihosted command
 * @param[in]  n32In_R0  : semihost register 0
 * @param[in]  n32In_R1  : semihost register 1
 * @param[out] pn32Out_R0: semihost register 0
 * @retval     0: No ICE debug
 * @retval     1: ICE debug
 *
 */

int32_t SH_Return(int32_t n32In_R0, int32_t n32In_R1, int32_t *pn32Out_R0)
{
    if(g_ICE_Conneced)
    {
        if(pn32Out_R0)
            *pn32Out_R0 = n32In_R0;
        
        return 1;
    }
    return 0;
}



#endif
#else // defined(DEBUG_ENABLE_SEMIHOST)

int32_t SH_Return(int32_t n32In_R0, int32_t n32In_R1, int32_t *pn32Out_R0);

#if defined( __ICCARM__ )
__WEAK
#else
__attribute__((weak)) 
#endif
uint32_t ProcessHardFault(uint32_t lr, uint32_t msp, uint32_t psp)
{
    uint32_t *sp;
    /* It is casued by hardfault. Just process the hard fault */
    /* TODO: Implement your hardfault handle code here */
    
    /* Check the used stack */
    if(lr & 0x40UL)
    {
        /* Secure stack used */
        if(lr & 4UL)
        {
            sp = (uint32_t *)psp;
        }
        else
        {
            sp = (uint32_t *)msp;
        }
    
    }
#if defined (__ARM_FEATURE_CMSE) &&  (__ARM_FEATURE_CMSE == 3)    
    else
    {
        /* Non-secure stack used */
        if(lr & 4)
            sp = (uint32_t *)__TZ_get_PSP_NS();
        else
            sp = (uint32_t *)__TZ_get_MSP_NS();
    
    }
#endif    
    
    /*
    printf("  HardFault!\n\n");
    printf("r0  = 0x%x\n", sp[0]);
    printf("r1  = 0x%x\n", sp[1]);
    printf("r2  = 0x%x\n", sp[2]);
    printf("r3  = 0x%x\n", sp[3]);
    printf("r12 = 0x%x\n", sp[4]);
    printf("lr  = 0x%x\n", sp[5]);
    printf("pc  = 0x%x\n", sp[6]);
    printf("psr = 0x%x\n", sp[7]);
    */
    
    /* Or *sp to remove compiler warning */
    while(1U|*sp){}
    
    return lr;
}


int32_t SH_Return(int32_t n32In_R0, int32_t n32In_R1, int32_t *pn32Out_R0)
{
    return 0;
}

#endif /* defined(DEBUG_ENABLE_SEMIHOST) */


/**
 * @brief    Routine to send a char
 *
 * @param[in] ch  A character data writes to debug port
 *
 * @returns  Send value from UART debug port
 *
 * @details  Send a target char to UART debug port .
 */
#ifndef NONBLOCK_PRINTF
void SendChar_ToUART(int ch)
{

    while(DEBUG_PORT->FIFOSTS & UART_FIFOSTS_TXFULL_Msk){}
    DEBUG_PORT->DAT = (uint32_t)ch;
    if((char)ch == '\n')
    {
        while(DEBUG_PORT->FIFOSTS & UART_FIFOSTS_TXFULL_Msk){}
        DEBUG_PORT->DAT = '\r';
    }
}

#else
/* Non-block implement of send char */
# define BUF_SIZE    512
void SendChar_ToUART(int ch)
{
    static uint8_t u8Buf[BUF_SIZE] = {0};
    static int32_t i32Head = 0;
    static int32_t i32Tail = 0;
    int32_t i32Tmp;
    
    /* Only flush the data in buffer to UART when ch == 0 */
    if(ch)
    {
        // Push char
        i32Tmp = i32Head+1;
        if(i32Tmp > BUF_SIZE) i32Tmp = 0;
        if(i32Tmp != i32Tail)
        {
            u8Buf[i32Head] = ch;
            i32Head = i32Tmp;
        }
        
        if(ch == '\n')
        {
            i32Tmp = i32Head+1;
            if(i32Tmp > BUF_SIZE) i32Tmp = 0;
            if(i32Tmp != i32Tail)
            {
                u8Buf[i32Head] = '\r';
                i32Head = i32Tmp;
            }
        }
    }
    else
    {
        if(i32Tail == i32Head)
            return;
    }
    
    // pop char
    do
    {
        i32Tmp = i32Tail + 1;
        if(i32Tmp > BUF_SIZE) i32Tmp = 0;
        
        if((DEBUG_PORT->FSR & UART_FSR_TX_FULL_Msk) == 0)
        {
            DEBUG_PORT->DATA = u8Buf[i32Tail];
            i32Tail = i32Tmp;
        }
        else
            break; // FIFO full
    }while(i32Tail != i32Head);
}
#endif

/**
 * @brief    Routine to send a char
 *
 * @param[in] ch A character data writes to debug port
 *
 * @returns  Send value from UART debug port or semihost
 *
 * @details  Send a target char to UART debug port or semihost.
 */
void SendChar(int ch)
{
#if defined(DEBUG_ENABLE_SEMIHOST)
    
    g_buf[g_buf_len++] = ch;
    g_buf[g_buf_len] = '\0';
    if(g_buf_len + 1 >= sizeof(g_buf) || ch == '\n' || ch == '\0')
    {
        /* Send the char */
        if(g_ICE_Conneced)
        {
            
            if(SH_DoCommand(0x04, (int)g_buf, NULL) != 0)
            {
                g_buf_len = 0;
                
                return;
            }
        }
        else
        {
# if (DEBUG_ENABLE_SEMIHOST == 2) // Re-direct to UART Debug Port only when DEBUG_ENABLE_SEMIHOST=2           
            int i;

            for(i = 0; i < g_buf_len; i++)
                SendChar_ToUART(g_buf[i]);
            g_buf_len = 0;
# endif            
        }
    }
#else
    SendChar_ToUART(ch);
#endif
}

/**
 * @brief    Routine to get a char
 *
 * @param    None
 *
 * @returns  Get value from UART debug port or semihost
 *
 * @details  Wait UART debug port or semihost to input a char.
 */
char GetChar(void)
{
#ifdef DEBUG_ENABLE_SEMIHOST
# if defined (__ICCARM__)
    int nRet;
    while(SH_DoCommand(0x7, 0, &nRet) != 0)
    {
        if(nRet != 0)
            return (char)nRet;
    }
# else
    int nRet;
    while(SH_DoCommand(0x101, 0, &nRet) != 0)
    {
        if(nRet != 0)
        {
            SH_DoCommand(0x07, 0, &nRet);
            return (char)nRet;
        }
    }

    
# if (DEBUG_ENABLE_SEMIHOST == 2) // Re-direct to UART Debug Port only when DEBUG_ENABLE_SEMIHOST=2
    
    /* Use debug port when ICE is not connected at semihost mode */
    while(!g_ICE_Conneced)
    {
        if((DEBUG_PORT->FIFOSTS & UART_FIFOSTS_RXEMPTY_Msk) == 0)
        {
            return (DEBUG_PORT->DAT);
        }
    }
# endif    
    
# endif
    return (0);
#else

    while(1)
    {
        if((DEBUG_PORT->FIFOSTS & UART_FIFOSTS_RXEMPTY_Msk) == 0U)
        {
            return ((char)DEBUG_PORT->DAT);
        }
    }

#endif
}

/**
 * @brief    Check any char input from UART
 *
 * @param    None
 *
 * @retval   1: No any char input
 * @retval   0: Have some char input
 *
 * @details  Check UART RSR RX EMPTY or not to determine if any char input from UART
 */

int kbhit(void)
{
    return !((DEBUG_PORT->FIFOSTS & UART_FIFOSTS_RXEMPTY_Msk) == 0U);
}
/**
 * @brief    Check if debug message finished
 *
 * @param    None
 *
 * @retval   1: Message is finished
 * @retval   0: Message is transmitting.
 *
 * @details  Check if message finished (FIFO empty of debug port)
 */

int IsDebugFifoEmpty(void)
{
    return ((DEBUG_PORT->FIFOSTS & UART_FIFOSTS_TXEMPTYF_Msk) != 0U);
}

/**
 * @brief    C library retargetting
 *
 * @param[in]  ch  Write a character data
 *
 * @returns  None
 *
 * @details  Check if message finished (FIFO empty of debug port)
 */

void _ttywrch(int ch)
{
    SendChar(ch);
    return;
}


/**
 * @brief      Write character to stream
 *
 * @param[in]  ch       Character to be written. The character is passed as its int promotion.
 * @param[in]  stream   Pointer to a FILE object that identifies the stream where the character is to be written.
 *
 * @returns    If there are no errors, the same character that has been written is returned.
 *             If an error occurs, EOF is returned and the error indicator is set (see ferror).
 *
 * @details    Writes a character to the stream and advances the position indicator.\n
 *             The character is written at the current position of the stream as indicated \n
 *             by the internal position indicator, which is then advanced one character.
 *
 * @note       The above descriptions are copied from http://www.cplusplus.com/reference/clibrary/cstdio/fputc/.
 *
 *
 */

int fputc(int ch, FILE *stream)
{
    SendChar(ch);
    return ch;
}


#if defined ( __GNUC__ )

#if !defined(OS_USE_SEMIHOSTING)
int _write (int fd, char *ptr, int len)
{
    int i = len;

    while(i--) {
        while(DEBUG_PORT->FIFOSTS & UART_FIFOSTS_TXFULL_Msk);

        DEBUG_PORT->DAT = *ptr++;

        if(*ptr == '\n') {
            while(DEBUG_PORT->FIFOSTS & UART_FIFOSTS_TXFULL_Msk);
            DEBUG_PORT->DAT = '\r';
        }
    }
    return len;
}

int _read (int fd, char *ptr, int len)
{

    while((DEBUG_PORT->FIFOSTS & UART_FIFOSTS_RXEMPTY_Msk) != 0);
    *ptr = DEBUG_PORT->DAT;
    return 1;


}
#endif

#else
/**
 * @brief      Get character from UART debug port or semihosting input
 *
 * @param[in]  stream   Pointer to a FILE object that identifies the stream on which the operation is to be performed.
 *
 * @returns    The character read from UART debug port or semihosting
 *
 * @details    For get message from debug port or semihosting.
 *
 */

int fgetc(FILE *stream)
{
    return ((int)GetChar());
}

/**
 * @brief      Check error indicator
 *
 * @param[in]  stream   Pointer to a FILE object that identifies the stream.
 *
 * @returns    If the error indicator associated with the stream was set, the function returns a nonzero value.
 *             Otherwise, it returns a zero value.
 *
 * @details    Checks if the error indicator associated with stream is set, returning a value different
 *             from zero if it is. This indicator is generally set by a previous operation on the stream that failed.
 *
 * @note       The above descriptions are copied from http://www.cplusplus.com/reference/clibrary/cstdio/ferror/.
 *
 */

int ferror(FILE *stream)
{
    return EOF;
}
#endif

#ifdef DEBUG_ENABLE_SEMIHOST
# ifdef __ICCARM__
void __exit(int return_code)
{

    /* Check if link with ICE */
    if(SH_DoCommand(0x18, 0x20026, NULL) == 0)
    {
        /* Make sure all message is print out */
        while(IsDebugFifoEmpty() == 0);
    }
label:
    goto label;  /* endless loop */
}
# else
void _sys_exit(int return_code)
{

    /* Check if link with ICE */
    if(SH_DoCommand(0x18, 0x20026, NULL) == 0)
    {
        /* Make sure all message is print out */
        while(IsDebugFifoEmpty() == 0);
    }
label:
    goto label;  /* endless loop */
}
# endif
#endif



/*** (C) COPYRIGHT 2016 Nuvoton Technology Corp. ***/


