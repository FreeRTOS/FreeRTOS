/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v3.0.2
 * Percepio AB, www.percepio.com
 *
 * trcTCPIPConfig.h
 *
 * Trace TCP/IP configuration. Modify these includes and functions to perform 
 * the same functionality using your specific TCP/IP stack.
 * Will only be included by trcTCPIP.c.
 *
 * Terms of Use
 * This software (the "Tracealyzer Recorder Library") is the intellectual
 * property of Percepio AB and may not be sold or in other ways commercially
 * redistributed without explicit written permission by Percepio AB.
 *
 * Separate conditions applies for the SEGGER branded source code included.
 *
 * The recorder library is free for use together with Percepio products.
 * You may distribute the recorder library in its original form, but public
 * distribution of modified versions require approval by Percepio AB.
 *
 * Disclaimer
 * The trace tool and recorder library is being delivered to you AS IS and
 * Percepio AB makes no warranty as to its use or performance. Percepio AB does
 * not and cannot warrant the performance or results you may obtain by using the
 * software or documentation. Percepio AB make no warranties, express or
 * implied, as to noninfringement of third party rights, merchantability, or
 * fitness for any particular purpose. In no event will Percepio AB, its
 * technology partners, or distributors be liable to you for any consequential,
 * incidental or special damages, including any lost profits or lost savings,
 * even if a representative of Percepio AB has been advised of the possibility
 * of such damages, or for any claim by any third party. Some jurisdictions do
 * not allow the exclusion or limitation of incidental, consequential or special
 * damages, or the exclusion of implied warranties or limitations on how long an
 * implied warranty may last, so the above limitations may not apply to you.
 *
 * Tabs are used for indent in this file (1 tab = 4 spaces)
 *
 * Copyright Percepio AB, 2015.
 * www.percepio.com
 ******************************************************************************/

#ifndef TRC_TCPIP_CONFIG_H
#define TRC_TCPIP_CONFIG_H

#ifdef __cplusplus
extern “C” {
#endif

/* TCP/IP includes*/
#include "tcpip.h"

#define TRC_TCPIP_PORT 12000

socket* sock = NULL;
socket* listenerSocket = NULL;

int32_t trcSocketSend(void* data, int32_t size, int32_t* bytesWritten)
{
  int32_t error;
  if (sock == NULL)
    return 1;
  
  error = socket_send(sock, data, size, (size_t*)bytesWritten, 0);
  if (error)
  {
    socket_close(sock);
    sock = NULL;
  }
  
  return (int32_t)error;
}

int32_t trcSocketReceive(void* data, int32_t size, int32_t* bytesRead)
{
  int32_t error;
  if (sock == NULL)
    return 1;
  
  error = socket_receive(sock, data, size, (size_t*)bytesRead, SOCKET_WAIT_ALL);
  if (error != ERROR_NONE && error != ERROR_TIMEOUT) /* Timeout may be expected when there is no data */
  {
    socket_close(sock);
    sock = NULL;
    return error;
  }

  return 0;
}

int32_t trcSocketInitializeListener()
{
  int32_t error;
  
  if (listenerSocket)
    return 0;
  
  //Start of exception handling block
  do
  {
    listenerSocket = socket_open(SOCKET_STREAM, SOCKET_TCP);
    if(listenerSocket == NULL)
    {
       error = 1;
       break;
    }

    error = socket_set_timeout(listenerSocket, INFINITE);
    if(error) break;

    error = socket_set_tx_buffer_size(listenerSocket, 1440 * 2);
    if(error) break;

    error = socket_set_rx_buffer_size(listenerSocket, 128);
    if(error) break;

    error = socket_bind_to_interface(listenerSocket, pNetInterface);
    if(error) break;

    error = socket_bind(listenerSocket, ADDR_ANY, TRC_TCPIP_PORT);
    if(error) break;

    error = socket_listen(listenerSocket);
    if(error) break;
    } while(0);

    if(error)
    {
        socket_close(listenerSocket);
        listenerSocket = NULL;
    }
   
    return error;
}

int32_t trcSocketAccept()
{
  ip_addr clientIpAddr;
  uint16_t clientPort;
  
  if (sock != NULL)
    return 0;

  if (listenerSocket == NULL)
    return 1;
  
  /* Wait for connection */
  sock = socket_accept(listenerSocket, &clientIpAddr, &clientPort);
  if(sock != NULL)
  {
    socket_set_timeout(sock, 20);
  }
  else
    return 1;
  
  return 0;
}

#ifdef __cplusplus
}
#endif

#endif /*TRC_TCPIP_CONFIG_H*/