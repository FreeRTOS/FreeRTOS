/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief Basic SMTP Client for AVR32 UC3.
 *
 * - Compiler:           GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support and FAQ: http://support.atmel.no/
 *
 *****************************************************************************/

/* Copyright (c) 2007, Atmel Corporation All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of ATMEL may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE EXPRESSLY AND
 * SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/*
  Implements a simplistic SMTP client. First time the task is started, connection is made and
  email is sent. Mail flag is then reset. Each time you press the Push Button 0, a new mail will be sent.
*/

#if (SMTP_USED == 1)

#include <string.h>

// Scheduler includes.
#include "FreeRTOS.h"
#include "task.h"
#include "BasicSMTP.h"


// Demo includes.
#include "portmacro.h"
#include "partest.h"
#include "intc.h"
#include "gpio.h"

// lwIP includes.
#include "lwip/api.h"
#include "lwip/tcpip.h"
#include "lwip/memp.h"
#include "lwip/stats.h"
#include "lwip/opt.h"
#include "lwip/api.h"
#include "lwip/arch.h"
#include "lwip/sys.h"
#include "lwip/sockets.h"
#include "netif/loopif.h"

//! SMTP default port
#define SMTP_PORT     25
//! SMTP EHLO code answer
#define SMTP_EHLO_STRING                  "220"
//! SMTP end of transmission code answer
#define SMTP_END_OF_TRANSMISSION_STRING   "221"
//! SMTP OK code answer
#define SMTP_OK_STRING                    "250"
//! SMTP start of transmission code answer
#define SMTP_START_OF_TRANSMISSION_STRING "354"
//! SMTP DATA<CRLF>
#define SMTP_DATA_STRING                  "DATA\r\n"
//! SMTP <CRLF>.<CRLF>
#define SMTP_MAIL_END_STRING              "\r\n.\r\n"
//! SMTP QUIT<CRLFCRLF>
#define SMTP_QUIT_STRING                  "QUIT\r\n"


//! Server address
#error configure SMTP server address
char cServer[] = "192.168.0.1";

//! Fill here the mailfrom with your mail address
#error configure SMTP mail sender
char cMailfrom[] = "MAIL FROM: <sender@domain.com>\r\n";

//! Fill here the mailto with your contact mail address
#error configure SMTP mail recipient
char cMailto[] = "RCPT TO: <recipient@domain.com>\r\n";

//! Fill here the mailcontent with the mail you want to send
#error configure SMTP mail content
char cMailcontent[] ="Subject: *** SPAM ***\r\nFROM: \"Your Name here\" <sender@domain.com>\r\nTO: \"Your Contact here\" <recipient@domain.com>\r\n\r\nSay what you want here.";

//! flag to send mail
Bool bSendMail = pdFALSE;

//! buffer for SMTP response
char cTempBuffer[200];


//_____ D E C L A R A T I O N S ____________________________________________
//! interrupt handler.
#if __GNUC__
__attribute__((naked))
#elif __ICCAVR32__
#pragma shadow_registers = full   // Naked.
#endif
void vpushb_ISR( void );

//! soft interrupt handler. where treatment should be done
#if __GNUC__
__attribute__((__noinline__))
#endif
static portBASE_TYPE prvpushb_ISR_NonNakedBehaviour( void );



//! Basic SMTP client task definition
portTASK_FUNCTION( vBasicSMTPClient, pvParameters )
{
  struct sockaddr_in stServeurSockAddr; 
  long lRetval;
  long lSocket = -1;
  
  // configure push button 0 to produce IT on falling edge
  gpio_enable_pin_interrupt(GPIO_PUSH_BUTTON_0 , GPIO_FALLING_EDGE);
  // Disable all interrupts
  vPortEnterCritical();
  // register push button 0 handler on level 3
  INTC_register_interrupt( (__int_handler)&vpushb_ISR, AVR32_GPIO_IRQ_0 + (GPIO_PUSH_BUTTON_0/8), INT3);
  // Enable all interrupts
  vPortExitCritical();  
  
  for (;;)
  {
    // wait for a signal to send a mail
    while (bSendMail != pdTRUE)   vTaskDelay(200);

    // Disable all interrupts
    vPortEnterCritical();
    // clear the flag    
    bSendMail = pdFALSE;
    // Enable all interrupts
    vPortExitCritical();    
    // clear the LED
    vParTestSetLED( 3 , pdFALSE );
    // Set up port
    memset(&stServeurSockAddr, 0, sizeof(stServeurSockAddr));
    stServeurSockAddr.sin_len = sizeof(stServeurSockAddr);
    stServeurSockAddr.sin_addr.s_addr = inet_addr(cServer);
    stServeurSockAddr.sin_port = htons(SMTP_PORT);
    stServeurSockAddr.sin_family = AF_INET;
 
    // socket as a stream
    if ( (lSocket = socket(AF_INET, SOCK_STREAM, 0)) < 0)
    {
      // socket failed, blink a LED and stay here
      for (;;) {
        vParTestToggleLED( 4 );
        vTaskDelay( 200 );
      }
    }
    // connect to the server
    if(connect(lSocket,(struct sockaddr *)&stServeurSockAddr, sizeof(stServeurSockAddr)) < 0)
    {
      // connect failed, blink a LED and stay here
      for (;;) {
        vParTestToggleLED( 6 );
        vTaskDelay( 200 );
      }
    }
    else
    {
//Server: 220 SMTP Ready        
      // wait for SMTP Server answer 
      do
      {
        lRetval = recv(lSocket, cTempBuffer, sizeof(cTempBuffer), 0);
      }while (lRetval <= 0);        
      if (strncmp(cTempBuffer, SMTP_EHLO_STRING, sizeof(cTempBuffer)) >= 0)
      {
//Client: EHLO smtp.domain.com
        // send ehlo
        send(lSocket, "HELO ", 5, 0);
        send(lSocket, cServer, strlen(cServer), 0);
        send(lSocket, "\r\n", 2, 0);
//Server: 250 
        // wait for SMTP Server answer
        do
        {
          lRetval = recv(lSocket, cTempBuffer, sizeof(cTempBuffer), 0);
        }while (lRetval <= 0);          
        if (strncmp(cTempBuffer, SMTP_OK_STRING, sizeof(cTempBuffer)) >= 0)
        {
//Client: MAIL FROM:<sender@domain.com>
          // send MAIL FROM
          send(lSocket, cMailfrom, strlen(cMailfrom), 0);            
//Server: 250 OK
          // wait for SMTP Server answer
          do
          {
            lRetval = recv(lSocket, cTempBuffer, sizeof(cTempBuffer), 0);
          }while (lRetval <= 0);       
          if (strncmp(cTempBuffer, SMTP_OK_STRING, sizeof(cTempBuffer)) >= 0)
          {
//Client: RCPT TO:<receiver@domain.com>
            // send RCPT TO
            send(lSocket, cMailto, strlen(cMailto), 0);  
//Server: 250 OK
            // wait for SMTP Server answer
            do
            {
              lRetval = recv(lSocket, cTempBuffer, sizeof(cTempBuffer), 0);
            }while (lRetval <= 0);
            if (strncmp(cTempBuffer, SMTP_OK_STRING, sizeof(cTempBuffer)) >= 0)
            {
//Client: DATA<CRLF>
              // send DATA
              send(lSocket, SMTP_DATA_STRING, 6, 0);  
//Server: 354 Start mail input; end with <CRLF>.<CRLF>              
              // wait for SMTP Server answer
              do
              {
                lRetval = recv(lSocket, cTempBuffer, sizeof(cTempBuffer), 0);
              }while (lRetval <= 0);
              if (strncmp(cTempBuffer, SMTP_START_OF_TRANSMISSION_STRING, sizeof(cTempBuffer)) >= 0)
              {
                // send content
                send(lSocket, cMailcontent, strlen(cMailcontent), 0);                 
//Client: <CRLF>.<CRLF>
                // send "<CRLF>.<CRLF>"
                send(lSocket, SMTP_MAIL_END_STRING, 5, 0);
//Server: 250 OK
                // wait for SMTP Server answer
                do
                {
                  lRetval = recv(lSocket, cTempBuffer, sizeof(cTempBuffer), 0);
                }while (lRetval <= 0);
                if (strncmp(cTempBuffer, SMTP_OK_STRING, sizeof(cTempBuffer)) >= 0)
                {
//Client: QUIT<CRLFCRLF>
                  // send QUIT 
                  send(lSocket, SMTP_QUIT_STRING, 8, 0);  
//Server: 221 smtp.domain.com closing transmission
                  do
                  {
                    lRetval = recv(lSocket, cTempBuffer, sizeof(cTempBuffer), 0);
                  }while (lRetval <= 0);                     
                  if (strncmp(cTempBuffer, SMTP_END_OF_TRANSMISSION_STRING, sizeof(cTempBuffer)) >= 0)
                  {
                    vParTestSetLED( 3 , pdTRUE );
                  }
                }
              }
            }             
          }
        }  
        // close socket
        close(lSocket);
      }
    }
  }
}

/*! \brief push button naked interrupt handler.
 *
 */
#if __GNUC__
__attribute__((naked))
#elif __ICCAVR32__
#pragma shadow_registers = full   // Naked.
#endif
void vpushb_ISR( void )
{
 /* This ISR can cause a context switch, so the first statement must be a
     call to the portENTER_SWITCHING_ISR() macro.  This must be BEFORE any
     variable declarations. */
  portENTER_SWITCHING_ISR();

  prvpushb_ISR_NonNakedBehaviour();

  portEXIT_SWITCHING_ISR();
}

/*! \brief push button interrupt handler. Here, declarations should be done
 *
 */
#if __GNUC__
__attribute__((__noinline__))
#elif __ICCAVR32__
#pragma optimize = no_inline
#endif
static portBASE_TYPE prvpushb_ISR_NonNakedBehaviour( void )
{
  if (gpio_get_pin_interrupt_flag(GPIO_PUSH_BUTTON_0))
  {
    // set the flag    
    bSendMail = pdTRUE;
    // allow new interrupt : clear the IFR flag
    gpio_clear_pin_interrupt_flag(GPIO_PUSH_BUTTON_0);
  }
  // no context switch required, task is polling the flag
  return( pdFALSE );
}




    
#endif
