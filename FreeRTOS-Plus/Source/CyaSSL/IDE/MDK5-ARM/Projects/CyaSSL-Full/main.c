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

#include "cmsis_os.h"
#if !defined(NO_FILESYSTEM)
#include "rl_fs.h" 
#endif
#include "rl_net.h" 
#include <stdio.h>
#include "cyassl_MDK_ARM.h"
#include <cyassl/ssl.h>

/*-----------------------------------------------------------------------------
 *        Initialize a Flash Memory Card
 *----------------------------------------------------------------------------*/
#if !defined(NO_FILESYSTEM)
static void init_filesystem (void) {
  int32_t retv;

  retv = finit ("M0:");
  if (retv == 0) {
    retv = fmount ("M0:");
    if (retv == 0) {
      printf ("Drive M0 ready!\n");
    }
    else {
      printf ("Drive M0 mount failed!\n");
    }
  }
  else {
    printf ("Drive M0 initialization failed!\n");
  }
}
#endif

/*-----------------------------------------------------------------------------
 *        TCP/IP tasks
 *----------------------------------------------------------------------------*/
void tcp_poll (void const *arg)
{
    CYASSL_MSG("TCP polling started.\n") ;
    while (1) {
        net_main ();
        osDelay(1) ;
    }
}

extern void shell_main(void * args) ;
extern void init_time(void) ;

osThreadDef (tcp_poll, osPriorityHigh, 1, 0) ;
/*-----------------------------------------------------------------------------
 *       mian entry 
 *----------------------------------------------------------------------------*/
int myoptind = 0;
char* myoptarg = NULL;

int main() 
{
    void *arg = NULL ;
	
	#if !defined(NO_FILESYSTEM)
    init_filesystem ();
	#endif
	
    net_initialize() ;
    
    osThreadCreate (osThread (tcp_poll), NULL); 
    osDelay(10000) ;  /* wait for DHCP */
    #if defined(DEBUG_CYASSL)
         printf("Turning ON Debug message\n") ;
         CyaSSL_Debugging_ON() ;
    #endif

    shell_main(arg) ;   

}
