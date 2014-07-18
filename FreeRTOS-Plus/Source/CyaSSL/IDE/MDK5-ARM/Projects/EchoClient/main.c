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
#include "rl_fs.h" 
#include "rl_net.h" 
#include <stdio.h>
#include "cyassl_MDK_ARM.h"
#include <cyassl/ssl.h>

/*-----------------------------------------------------------------------------
 *        Initialize a Flash Memory Card
 *----------------------------------------------------------------------------*/
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

typedef struct func_args {
    int    argc;
    char** argv;
} func_args;

extern void echoclient_test(func_args * args) ;
extern void init_time(void) ;

    osThreadDef (tcp_poll, osPriorityHigh , 1, 0) ;
/*-----------------------------------------------------------------------------
 *       mian entry 
 *----------------------------------------------------------------------------*/
int myoptind = 0;
char* myoptarg = NULL;

#include "config-EchoClient.h"

int main() 
{
    void *args = NULL ;
    init_filesystem ();
    net_initialize() ;
    osThreadCreate (osThread (tcp_poll), NULL); 
    osDelay(30000) ;  /* wait for DHCP */
    #if defined(DEBUG_CYASSL)
         printf("Turning ON Debug message\n") ;
         CyaSSL_Debugging_ON() ;
    #endif

    echoclient_test(args) ;

}
