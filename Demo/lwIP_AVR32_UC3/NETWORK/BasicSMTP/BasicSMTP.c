/* This source file is part of the ATMEL FREERTOS-0.9.0 Release */

/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief Basic SMTP Host for AVR32 UC3.
 *
 * - Compiler:           GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support email: avr32@atmel.com
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
  Implements a simplistic SMTP client.
*/

#if (SMTP_USED == 1)

#include <string.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "BasicSMTP.h"


/* Demo includes. */
#include "AVR32_EMAC.h"
#include "portmacro.h"
#include "partest.h"

/* lwIP includes. */
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

/*! SMTP default port */
#define SMTP_PORT     25
/*! SMTP EHLO code answer */
#define SMTP_EHLO_STRING                  "220"
/*! SMTP end of transmission code answer */
#define SMTP_END_OF_TRANSMISSION_STRING   "221"
/*! SMTP OK code answer */
#define SMTP_OK_STRING                    "250"
/*! SMTP start of transmission code answer */
#define SMTP_START_OF_TRANSMISSION_STRING "354"
/*! SMTP DATA<CRLF> */
#define SMTP_DATA_STRING                  "DATA\r\n"
/*! SMTP <CRLF>.<CRLF> */
#define SMTP_MAIL_END_STRING              "\r\n.\r\n"
/*! SMTP QUIT<CRLFCRLF> */
#define SMTP_QUIT_STRING                  "QUIT\r\n\r\n"


/*! Server address */
portCHAR cServer[] = "192.168.0.1";

/*! Fill here the ehlo with your SMTP server name */
#error configure SMTP server
char ehlo[] = "EHLO smtp.domain.com\r\n";

/*! Fill here the mailfrom with your mail address */
#error configure mail sender
char mailfrom[] = "MAIL FROM: <sender@domain.com>\r\n";

/*! Fill here the mailto with your contact mail address */
#error configure mail receiver
char mailto[] = "RCPT TO: <receiver@domain.com>\r\n";

/*! Fill here the mailcontent with the mail you want to send */
#error configure mail content
char mailcontent[] ="Subject: *** SPAM ***\r\nFROM: \"Your Name here\" <sender@domain.com>\r\nTO: \"Your Contact here\" <receiver@domain.com>\r\n\r\nSay what you want here.";

Bool bSendMail = pdTRUE;
portCHAR cTempBuffer[200];

/*! Basic SMTP Host task definition */
portTASK_FUNCTION( vBasicSMTPHost, pvParameters )
{
  struct sockaddr_in stServeurSockAddr; 
  portLONG lRetval;
  portLONG lSocket = -1;
  
  
  for (;;)
  {
    // wait for a signal to send a mail
    while (bSendMail != pdTRUE)   vTaskDelay(200);

    // Set up port
    memset(&stServeurSockAddr, 0, sizeof(stServeurSockAddr));
    stServeurSockAddr.sin_len = sizeof(stServeurSockAddr);
    stServeurSockAddr.sin_addr.s_addr = inet_addr(cServer);
    stServeurSockAddr.sin_port = htons(SMTP_PORT);
    stServeurSockAddr.sin_family = AF_INET;

    // clear the flag    
    bSendMail = pdFALSE;
    
    // socket as a stream
    if ( (lSocket = socket(AF_INET, SOCK_STREAM, 0)) < 0)
    {
      // socket failed, blink a LED and stay here
      for (;;) {
        vParTestToggleLED( 0 );
        vTaskDelay( 200 );
      }
    }
    // connect to the server
    if(connect(lSocket,(struct sockaddr *)&stServeurSockAddr, sizeof(stServeurSockAddr)) < 0)
    {
      // connect failed, blink a LED and stay here
      for (;;) {
        vParTestToggleLED( 1 );
        vTaskDelay( 200 );
      }
    }
    else
    {
//Server: 220 SMTP Ready        
      /* wait for SMTP Server answer */
      do
      {
        lRetval = recv(lSocket, cTempBuffer, sizeof(cTempBuffer), 0);
      }while (lRetval <= 0);        
      if (strncmp(cTempBuffer, SMTP_EHLO_STRING, sizeof(cTempBuffer)) >= 0)
      {
//Client: EHLO smtp.domain.com
        /* send ehlo */
        send(lSocket, cEhlo, strlen(cEhlo), 0);
//Server: 250 
        /* wait for SMTP Server answer */
        do
        {
          lRetval = recv(lSocket, cTempBuffer, sizeof(cTempBuffer), 0);
        }while (lRetval <= 0);          
        if (strncmp(cTempBuffer, SMTP_OK_STRING, sizeof(cTempBuffer)) >= 0)
        {
//Server: 250 HELP
          do
          {
            lRetval = recv(lSocket, cTempBuffer, sizeof(cTempBuffer), 0);
          }while (lRetval <= 0); 
//Client: MAIL FROM:<sender@domain.com>
          /* send MAIL FROM */
          send(lSocket, cMailfrom, strlen(cMailfrom), 0);            
//Server: 250 OK
          /* wait for SMTP Server answer */
          do
          {
            lRetval = recv(lSocket, cTempBuffer, sizeof(cTempBuffer), 0);
          }while (lRetval <= 0);       
          if (strncmp(cTempBuffer, SMTP_OK_STRING, sizeof(cTempBuffer)) >= 0)
          {
//Client: RCPT TO:<receiver@domain.com>
            /* send RCPT TO */
            send(lSocket, cMailto, strlen(cMailto), 0);  
//Server: 250 OK
            /* wait for SMTP Server answer */
            do
            {
              lRetval = recv(lSocket, cTempBuffer, sizeof(cTempBuffer), 0);
            }while (lRetval <= 0);
            if (strncmp(cTempBuffer, SMTP_OK_STRING, sizeof(cTempBuffer)) >= 0)
            {
//Client: DATA<CRLF>
              /* send DATA */
              send(lSocket, SMTP_DATA_STRING, 6, 0);  
//Server: 354 Start mail input; end with <CRLF>.<CRLF>              
              /* wait for SMTP Server answer */
              do
              {
                lRetval = recv(lSocket, cTempBuffer, sizeof(cTempBuffer), 0);
              }while (lRetval <= 0);
              if (strncmp(cTempBuffer, SMTP_START_OF_TRANSMISSION_STRING, sizeof(cTempBuffer)) >= 0)
              {
                /* send content */
                send(lSocket, cMailcontent, strlen(cMailcontent), 0);                 
//Client: <CRLF>.<CRLF>
                /* send "<CRLF>.<CRLF>" */
                send(lSocket, SMTP_MAIL_END_STRING, 5, 0);
//Server: 250 OK
                /* wait for SMTP Server answer */
                do
                {
                  lRetval = recv(lSocket, cTempBuffer, sizeof(cTempBuffer), 0);
                }while (lRetval <= 0);
                if (strncmp(cTempBuffer, SMTP_OK_STRING, sizeof(cTempBuffer)) >= 0)
                {
//Client: QUIT<CRLFCRLF>
                  /* send QUIT */
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
        /* close socket */
        close(lSocket);
      }
    }
  }
}
#endif
