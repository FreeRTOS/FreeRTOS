/* main.c
 *
 * Copyright (C) 2006-2014 wolfSSL Inc.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */
 
#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <cyassl/ctaocrypt/visibility.h>
#include <cyassl/ctaocrypt/logging.h>

#include <RTL.h>
#include <stdio.h>
#include "cyassl_MDK_ARM.h"

/*-----------------------------------------------------------------------------
 *        Initialize a Flash Memory Card
 *----------------------------------------------------------------------------*/
#if !defined(NO_FILESYSTEM)
static void init_card (void) 
{
    U32 retv;

    while ((retv = finit (NULL)) != 0) {     /* Wait until the Card is ready */
        if (retv == 1) {
            printf ("\nSD/MMC Init Failed");
            printf ("\nInsert Memory card and press key...\n");
        } else {
            printf ("\nSD/MMC Card is Unformatted");
        }
     }
}
#endif


/*-----------------------------------------------------------------------------
 *        TCP/IP tasks
 *----------------------------------------------------------------------------*/
#ifdef CYASSL_KEIL_TCP_NET
__task void tcp_tick (void) 
{
    
    CYASSL_MSG("Time tick started.") ;
    #if defined (HAVE_KEIL_RTX)
    os_itv_set (10);
    #endif
  
    while (1) {
        #if defined (HAVE_KEIL_RTX)
        os_itv_wait ();
        #endif
        /* Timer tick every 100 ms */
        timer_tick ();
    }
}

__task void tcp_poll (void)
{
    CYASSL_MSG("TCP polling started.\n") ;
    while (1) {
        main_TcpNet ();
        #if defined (HAVE_KEIL_RTX)
        os_tsk_pass ();
        #endif
    }
}
#endif

#if defined(HAVE_KEIL_RTX) && defined(CYASSL_MDK_SHELL)
#define SHELL_STACKSIZE 1000
static unsigned char Shell_stack[SHELL_STACKSIZE] ;
#endif


#if  defined(CYASSL_MDK_SHELL)
extern void shell_main(void) ;
#endif

extern void time_main(int) ;
extern void benchmark_test(void) ;
extern void SER_Init(void) ;

/*-----------------------------------------------------------------------------
 *       mian entry 
 *----------------------------------------------------------------------------*/

/*** This is the parent task entry ***/
void main_task (void) 
{
    #ifdef CYASSL_KEIL_TCP_NET
    init_TcpNet ();

    os_tsk_create (tcp_tick, 2);
    os_tsk_create (tcp_poll, 1);
    #endif
    
    #ifdef CYASSL_MDK_SHELL 
        #ifdef  HAVE_KEIL_RTX
           os_tsk_create_user(shell_main, 1, Shell_stack, SHELL_STACKSIZE) ;
       #else
           shell_main() ;
       #endif
    #else

    /************************************/
    /*** USER APPLICATION HERE        ***/
    /************************************/
    printf("USER LOGIC STARTED\n") ;
	
    #endif 

    #ifdef   HAVE_KEIL_RTX
    CYASSL_MSG("Terminating tcp_main\n") ;
    os_tsk_delete_self ();
    #endif

}


    int myoptind = 0;
    char* myoptarg = NULL;

#if defined(DEBUG_CYASSL)
    extern void CyaSSL_Debugging_ON(void) ;
#endif


/*** main entry ***/
extern void init_time(void) ;
extern void 	SystemInit(void);

int main() {

    SystemInit();  
    SER_Init() ;
    #if !defined(NO_FILESYSTEM)
    init_card () ;     /* initializing SD card */
    #endif

    init_time() ;

    #if defined(DEBUG_CYASSL)
         printf("Turning ON Debug message\n") ;
         CyaSSL_Debugging_ON() ;
    #endif
    
    #ifdef   HAVE_KEIL_RTX
        os_sys_init (main_task) ;
    #else
        main_task() ;
    #endif

    return 0 ; /* There should be no return here */

}
