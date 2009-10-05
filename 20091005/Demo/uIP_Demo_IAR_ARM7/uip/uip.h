/**
 * \addtogroup uip
 * @{
 */

/**
 * \file
 * Header file for the uIP TCP/IP stack.
 * \author Adam Dunkels <adam@dunkels.com>
 *
 * The uIP TCP/IP stack header file contains definitions for a number
 * of C macros that are used by uIP programs as well as internal uIP
 * structures, TCP/IP header structures and function declarations.
 *
 */


/*
 * Copyright (c) 2001-2003, Adam Dunkels.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote
 *    products derived from this software without specific prior
 *    written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS
 * OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
 * GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * This file is part of the uIP TCP/IP stack.
 *
 * $Id: uip.h,v 1.36.2.7 2003/10/07 13:47:51 adam Exp $
 *
 */

#ifndef __UIP_H__
#define __UIP_H__

#include "uipopt.h"

/*-----------------------------------------------------------------------------------*/
/* First, the functions that should be called from the
 * system. Initialization, the periodic timer and incoming packets are
 * handled by the following three functions.
 */

/**
 * \defgroup uipconffunc uIP configuration functions
 * @{
 *
 * The uIP configuration functions are used for setting run-time
 * parameters in uIP such as IP addresses.
 */

/**
 * Set the IP address of this host.
 *
 * The IP address is represented as a 4-byte array where the first
 * octet of the IP address is put in the first member of the 4-byte
 * array.
 *
 * \param addr A pointer to a 4-byte representation of the IP address.
 *
 * \hideinitializer
 */
#define uip_sethostaddr(addr) do { uip_hostaddr[0] = addr[0]; \
                              uip_hostaddr[1] = addr[1]; } while(0)

/**
 * Get the IP address of this host.
 *
 * The IP address is represented as a 4-byte array where the first
 * octet of the IP address is put in the first member of the 4-byte
 * array.
 *
 * \param addr A pointer to a 4-byte array that will be filled in with
 * the currently configured IP address.
 *
 * \hideinitializer
 */
#define uip_gethostaddr(addr) do { addr[0] = uip_hostaddr[0]; \
                              addr[1] = uip_hostaddr[1]; } while(0)

/** @} */

/**
 * \defgroup uipinit uIP initialization functions
 * @{
 *
 * The uIP initialization functions are used for booting uIP.
 */

/**
 * uIP initialization function.
 *
 * This function should be called at boot up to initilize the uIP
 * TCP/IP stack.
 */
void uip_init(void);

/** @} */

/**
 * \defgroup uipdevfunc uIP device driver functions
 * @{
 *
 * These functions are used by a network device driver for interacting
 * with uIP.
 */

/**
 * Process an incoming packet.
 *
 * This function should be called when the device driver has received
 * a packet from the network. The packet from the device driver must
 * be present in the uip_buf buffer, and the length of the packet
 * should be placed in the uip_len variable.
 *
 * When the function returns, there may be an outbound packet placed
 * in the uip_buf packet buffer. If so, the uip_len variable is set to
 * the length of the packet. If no packet is to be sent out, the
 * uip_len variable is set to 0.
 *
 * The usual way of calling the function is presented by the source
 * code below.
 \code
  uip_len = devicedriver_poll();
  if(uip_len > 0) {
    uip_input();
    if(uip_len > 0) {
      devicedriver_send();
    }
  }
 \endcode
 *
 * \note If you are writing a uIP device driver that needs ARP
 * (Address Resolution Protocol), e.g., when running uIP over
 * Ethernet, you will need to call the uIP ARP code before calling
 * this function:
 \code
  #define BUF ((struct uip_eth_hdr *)&uip_buf[0])
  uip_len = ethernet_devicedrver_poll();
  if(uip_len > 0) {
    if(BUF->type == HTONS(UIP_ETHTYPE_IP)) {
      uip_arp_ipin();
      uip_input();
      if(uip_len > 0) {
        uip_arp_out();
	ethernet_devicedriver_send();
      }
    } else if(BUF->type == HTONS(UIP_ETHTYPE_ARP)) {
      uip_arp_arpin();
      if(uip_len > 0) {
	ethernet_devicedriver_send();
      }
    }
 \endcode
 *
 * \hideinitializer
 */
#define uip_input()        uip_process(UIP_DATA)

/**
 * Periodic processing for a connection identified by its number.
 *
 * This function does the necessary periodic processing (timers,
 * polling) for a uIP TCP conneciton, and should be called when the
 * periodic uIP timer goes off. It should be called for every
 * connection, regardless of whether they are open of closed.
 *
 * When the function returns, it may have an outbound packet waiting
 * for service in the uIP packet buffer, and if so the uip_len
 * variable is set to a value larger than zero. The device driver
 * should be called to send out the packet.
 *
 * The ususal way of calling the function is through a for() loop like
 * this:
 \code
  for(i = 0; i < UIP_CONNS; ++i) {
    uip_periodic(i);
    if(uip_len > 0) {
      devicedriver_send();
    }
  }
 \endcode
 *
 * \note If you are writing a uIP device driver that needs ARP
 * (Address Resolution Protocol), e.g., when running uIP over
 * Ethernet, you will need to call the uip_arp_out() function before
 * calling the device driver:
 \code
  for(i = 0; i < UIP_CONNS; ++i) {
    uip_periodic(i);
    if(uip_len > 0) {
      uip_arp_out();
      ethernet_devicedriver_send();
    }
  }
 \endcode
 *
 * \param conn The number of the connection which is to be periodically polled.
 *
 * \hideinitializer
 */
#define uip_periodic(conn) do { uip_conn = &uip_conns[conn]; \
                                uip_process(UIP_TIMER); } while (0)

/**
 * Periodic processing for a connection identified by a pointer to its structure.
 *
 * Same as uip_periodic() but takes a pointer to the actual uip_conn
 * struct instead of an integer as its argument. This function can be
 * used to force periodic processing of a specific connection.
 *
 * \param conn A pointer to the uip_conn struct for the connection to
 * be processed.
 *
 * \hideinitializer
 */
#define uip_periodic_conn(conn) do { uip_conn = conn; \
                                     uip_process(UIP_TIMER); } while (0)

#if UIP_UDP
/**
 * Periodic processing for a UDP connection identified by its number.
 *
 * This function is essentially the same as uip_prerioic(), but for
 * UDP connections. It is called in a similar fashion as the
 * uip_periodic() function:
 \code
  for(i = 0; i < UIP_UDP_CONNS; i++) {
    uip_udp_periodic(i);
    if(uip_len > 0) {
      devicedriver_send();
    }
  }
 \endcode
 *
 * \note As for the uip_periodic() function, special care has to be
 * taken when using uIP together with ARP and Ethernet:
 \code
  for(i = 0; i < UIP_UDP_CONNS; i++) {
    uip_udp_periodic(i);
    if(uip_len > 0) {
      uip_arp_out();
      ethernet_devicedriver_send();
    }
  }
 \endcode
 *
 * \param conn The number of the UDP connection to be processed.
 *
 * \hideinitializer
 */
#define uip_udp_periodic(conn) do { uip_udp_conn = &uip_udp_conns[conn]; \
                                uip_process(UIP_UDP_TIMER); } while (0)

/**
 * Periodic processing for a UDP connection identified by a pointer to
 * its structure.
 *
 * Same as uip_udp_periodic() but takes a pointer to the actual
 * uip_conn struct instead of an integer as its argument. This
 * function can be used to force periodic processing of a specific
 * connection.
 *
 * \param conn A pointer to the uip_udp_conn struct for the connection
 * to be processed.
 *
 * \hideinitializer
 */
#define uip_udp_periodic_conn(conn) do { uip_udp_conn = conn; \
                                         uip_process(UIP_UDP_TIMER); } while (0)


#endif /* UIP_UDP */

/**
 * The uIP packet buffer.
 *
 * The uip_buf array is used to hold incoming and outgoing
 * packets. The device driver should place incoming data into this
 * buffer. When sending data, the device driver should read the link
 * level headers and the TCP/IP headers from this buffer. The size of
 * the link level headers is configured by the UIP_LLH_LEN define.
 *
 * \note The application data need not be placed in this buffer, so
 * the device driver must read it from the place pointed to by the
 * uip_appdata pointer as illustrated by the following example:
 \code
 void
 devicedriver_send(void)
 {
    hwsend(&uip_buf[0], UIP_LLH_LEN);
    hwsend(&uip_buf[UIP_LLH_LEN], 40);
    hwsend(uip_appdata, uip_len - 40 - UIP_LLH_LEN);
 }
 \endcode
 */
extern u8_t uip_buf[UIP_BUFSIZE+2]; /*_RB_ __attribute__ ((aligned (4)));*/

/** @} */

/*-----------------------------------------------------------------------------------*/
/* Functions that are used by the uIP application program. Opening and
 * closing connections, sending and receiving data, etc. is all
 * handled by the functions below.
*/
/**
 * \defgroup uipappfunc uIP application functions
 * @{
 *
 * Functions used by an application running of top of uIP.
 */

/**
 * Start listening to the specified port.
 *
 * \note Since this function expects the port number in network byte
 * order, a conversion using HTONS() or htons() is necessary.
 *
 \code
 uip_listen(HTONS(80));
 \endcode
 *
 * \param port A 16-bit port number in network byte order.
 */
void uip_listen(u16_t port);

/**
 * Stop listening to the specified port.
 *
 * \note Since this function expects the port number in network byte
 * order, a conversion using HTONS() or htons() is necessary.
 *
 \code
 uip_unlisten(HTONS(80));
 \endcode
 *
 * \param port A 16-bit port number in network byte order.
 */
void uip_unlisten(u16_t port);

/**
 * Connect to a remote host using TCP.
 *
 * This function is used to start a new connection to the specified
 * port on the specied host. It allocates a new connection identifier,
 * sets the connection to the SYN_SENT state and sets the
 * retransmission timer to 0. This will cause a TCP SYN segment to be
 * sent out the next time this connection is periodically processed,
 * which usually is done within 0.5 seconds after the call to
 * uip_connect().
 *
 * \note This function is avaliable only if support for active open
 * has been configured by defining UIP_ACTIVE_OPEN to 1 in uipopt.h.
 *
 * \note Since this function requires the port number to be in network
 * byte order, a convertion using HTONS() or htons() is necessary.
 *
 \code
 u16_t ipaddr[2];

 uip_ipaddr(ipaddr, 192,168,1,2);
 uip_connect(ipaddr, HTONS(80));
 \endcode
 *
 * \param ripaddr A pointer to a 4-byte array representing the IP
 * address of the remote hot.
 *
 * \param port A 16-bit port number in network byte order.
 *
 * \return A pointer to the uIP connection identifier for the new connection,
 * or NULL if no connection could be allocated.
 *
 */
struct uip_conn *uip_connect(u16_t *ripaddr, u16_t port);



/**
 * \internal
 *
 * Check if a connection has outstanding (i.e., unacknowledged) data.
 *
 * \param conn A pointer to the uip_conn structure for the connection.
 *
 * \hideinitializer
 */
#define uip_outstanding(conn) ((conn)->len)

/**
 * Send data on the current connection.
 *
 * This function is used to send out a single segment of TCP
 * data. Only applications that have been invoked by uIP for event
 * processing can send data.
 *
 * The amount of data that actually is sent out after a call to this
 * funcion is determined by the maximum amount of data TCP allows. uIP
 * will automatically crop the data so that only the appropriate
 * amount of data is sent. The function uip_mss() can be used to query
 * uIP for the amount of data that actually will be sent.
 *
 * \note This function does not guarantee that the sent data will
 * arrive at the destination. If the data is lost in the network, the
 * application will be invoked with the uip_rexmit() event being
 * set. The application will then have to resend the data using this
 * function.
 *
 * \param data A pointer to the data which is to be sent.
 *
 * \param len The maximum amount of data bytes to be sent.
 *
 * \hideinitializer
 */
#define uip_send(data, len) do { uip_sappdata = (data); uip_slen = (len);} while(0)

/**
 * The length of any incoming data that is currently avaliable (if avaliable)
 * in the uip_appdata buffer.
 *
 * The test function uip_data() must first be used to check if there
 * is any data available at all.
 *
 * \hideinitializer
 */
#define uip_datalen()       uip_len

/**
 * The length of any out-of-band data (urgent data) that has arrived
 * on the connection.
 *
 * \note The configuration parameter UIP_URGDATA must be set for this
 * function to be enabled.
 *
 * \hideinitializer
 */
#define uip_urgdatalen()    uip_urglen

/**
 * Close the current connection.
 *
 * This function will close the current connection in a nice way.
 *
 * \hideinitializer
 */
#define uip_close()         (uip_flags = UIP_CLOSE)

/**
 * Abort the current connection.
 *
 * This function will abort (reset) the current connection, and is
 * usually used when an error has occured that prevents using the
 * uip_close() function.
 *
 * \hideinitializer
 */
#define uip_abort()         (uip_flags = UIP_ABORT)

/**
 * Tell the sending host to stop sending data.
 *
 * This function will close our receiver's window so that we stop
 * receiving data for the current connection.
 *
 * \hideinitializer
 */
#define uip_stop()          (uip_conn->tcpstateflags |= UIP_STOPPED)

/**
 * Find out if the current connection has been previously stopped with
 * uip_stop().
 *
 * \hideinitializer
 */
#define uip_stopped(conn)   ((conn)->tcpstateflags & UIP_STOPPED)

/**
 * Restart the current connection, if is has previously been stopped
 * with uip_stop().
 *
 * This function will open the receiver's window again so that we
 * start receiving data for the current connection.
 *
 * \hideinitializer
 */
#define uip_restart()         do { uip_flags |= UIP_NEWDATA; \
                                   uip_conn->tcpstateflags &= ~UIP_STOPPED; \
                              } while(0)


/* uIP tests that can be made to determine in what state the current
   connection is, and what the application function should do. */

/**
 * Is new incoming data available?
 *
 * Will reduce to non-zero if there is new data for the application
 * present at the uip_appdata pointer. The size of the data is
 * avaliable through the uip_len variable.
 *
 * \hideinitializer
 */
#define uip_newdata()   (uip_flags & UIP_NEWDATA)

/**
 * Has previously sent data been acknowledged?
 *
 * Will reduce to non-zero if the previously sent data has been
 * acknowledged by the remote host. This means that the application
 * can send new data.
 *
 * \hideinitializer
 */
#define uip_acked()   (uip_flags & UIP_ACKDATA)

/**
 * Has the connection just been connected?
 *
 * Reduces to non-zero if the current connection has been connected to
 * a remote host. This will happen both if the connection has been
 * actively opened (with uip_connect()) or passively opened (with
 * uip_listen()).
 *
 * \hideinitializer
 */
#define uip_connected() (uip_flags & UIP_CONNECTED)

/**
 * Has the connection been closed by the other end?
 *
 * Is non-zero if the connection has been closed by the remote
 * host. The application may then do the necessary clean-ups.
 *
 * \hideinitializer
 */
#define uip_closed()    (uip_flags & UIP_CLOSE)

/**
 * Has the connection been aborted by the other end?
 *
 * Non-zero if the current connection has been aborted (reset) by the
 * remote host.
 *
 * \hideinitializer
 */
#define uip_aborted()    (uip_flags & UIP_ABORT)

/**
 * Has the connection timed out?
 *
 * Non-zero if the current connection has been aborted due to too many
 * retransmissions.
 *
 * \hideinitializer
 */
#define uip_timedout()    (uip_flags & UIP_TIMEDOUT)

/**
 * Do we need to retransmit previously data?
 *
 * Reduces to non-zero if the previously sent data has been lost in
 * the network, and the application should retransmit it. The
 * application should send the exact same data as it did the last
 * time, using the uip_send() function.
 *
 * \hideinitializer
 */
#define uip_rexmit()     (uip_flags & UIP_REXMIT)

/**
 * Is the connection being polled by uIP?
 *
 * Is non-zero if the reason the application is invoked is that the
 * current connection has been idle for a while and should be
 * polled.
 *
 * The polling event can be used for sending data without having to
 * wait for the remote host to send data.
 *
 * \hideinitializer
 */
#define uip_poll()       (uip_flags & UIP_POLL)

/**
 * Get the initial maxium segment size (MSS) of the current
 * connection.
 *
 * \hideinitializer
 */
#define uip_initialmss()             (uip_conn->initialmss)

/**
 * Get the current maxium segment size that can be sent on the current
 * connection.
 *
 * The current maxiumum segment size that can be sent on the
 * connection is computed from the receiver's window and the MSS of
 * the connection (which also is available by calling
 * uip_initialmss()).
 *
 * \hideinitializer
 */
#define uip_mss()             (uip_conn->mss)

/**
 * Set up a new UDP connection.
 *
 * \param ripaddr A pointer to a 4-byte structure representing the IP
 * address of the remote host.
 *
 * \param rport The remote port number in network byte order.
 *
 * \return The uip_udp_conn structure for the new connection or NULL
 * if no connection could be allocated.
 */
struct uip_udp_conn *uip_udp_new(u16_t *ripaddr, u16_t rport);

/**
 * Removed a UDP connection.
 *
 * \param conn A pointer to the uip_udp_conn structure for the connection.
 *
 * \hideinitializer
 */
#define uip_udp_remove(conn) (conn)->lport = 0

/**
 * Send a UDP datagram of length len on the current connection.
 *
 * This function can only be called in response to a UDP event (poll
 * or newdata). The data must be present in the uip_buf buffer, at the
 * place pointed to by the uip_appdata pointer.
 *
 * \param len The length of the data in the uip_buf buffer.
 *
 * \hideinitializer
 */
#define uip_udp_send(len) uip_slen = (len)

/** @} */

/* uIP convenience and converting functions. */

/**
 * \defgroup uipconvfunc uIP conversion functions
 * @{
 *
 * These functions can be used for converting between different data
 * formats used by uIP.
 */

/**
 * Pack an IP address into a 4-byte array which is used by uIP to
 * represent IP addresses.
 *
 * Example:
 \code
 u16_t ipaddr[2];

 uip_ipaddr(&ipaddr, 192,168,1,2);
 \endcode
 *
 * \param addr A pointer to a 4-byte array that will be filled in with
 * the IP addres.
 * \param addr0 The first octet of the IP address.
 * \param addr1 The second octet of the IP address.
 * \param addr2 The third octet of the IP address.
 * \param addr3 The forth octet of the IP address.
 *
 * \hideinitializer
 */
#define uip_ipaddr(addr, addr0,addr1,addr2,addr3) do { \
                     (addr)[0] = HTONS(((addr0) << 8) | (addr1)); \
                     (addr)[1] = HTONS(((addr2) << 8) | (addr3)); \
                  } while(0)

/**
 * Convert 16-bit quantity from host byte order to network byte order.
 *
 * This macro is primarily used for converting constants from host
 * byte order to network byte order. For converting variables to
 * network byte order, use the htons() function instead.
 *
 * \hideinitializer
 */
#ifndef HTONS
#   if BYTE_ORDER == BIG_ENDIAN
#      define HTONS(n) (n)
#   else /* BYTE_ORDER == BIG_ENDIAN */
#      define HTONS(n) ((((u16_t)((n) & 0xff)) << 8) | (((n) & 0xff00) >> 8))
#   endif /* BYTE_ORDER == BIG_ENDIAN */
#endif /* HTONS */

/**
 * Convert 16-bit quantity from host byte order to network byte order.
 *
 * This function is primarily used for converting variables from host
 * byte order to network byte order. For converting constants to
 * network byte order, use the HTONS() macro instead.
 */
#ifndef htons
u16_t htons(u16_t val);
#endif /* htons */

/** @} */

/**
 * Pointer to the application data in the packet buffer.
 *
 * This pointer points to the application data when the application is
 * called. If the application wishes to send data, the application may
 * use this space to write the data into before calling uip_send().
 */
extern volatile u8_t *uip_appdata;
extern volatile u8_t *uip_sappdata;

#if UIP_URGDATA > 0
/* u8_t *uip_urgdata:
 *
 * This pointer points to any urgent data that has been received. Only
 * present if compiled with support for urgent data (UIP_URGDATA).
 */
extern volatile u8_t *uip_urgdata;
#endif /* UIP_URGDATA > 0 */


/* u[8|16]_t uip_len:
 *
 * When the application is called, uip_len contains the length of any
 * new data that has been received from the remote host. The
 * application should set this variable to the size of any data that
 * the application wishes to send. When the network device driver
 * output function is called, uip_len should contain the length of the
 * outgoing packet.
 */
extern volatile u16_t uip_len, uip_slen;

#if UIP_URGDATA > 0
extern volatile u8_t uip_urglen, uip_surglen;
#endif /* UIP_URGDATA > 0 */


/**
 * Representation of a uIP TCP connection.
 *
 * The uip_conn structure is used for identifying a connection. All
 * but one field in the structure are to be considered read-only by an
 * application. The only exception is the appstate field whos purpose
 * is to let the application store application-specific state (e.g.,
 * file pointers) for the connection. The size of this field is
 * configured in the "uipopt.h" header file.
 */
struct uip_conn {
  u16_t ripaddr[2];   /**< The IP address of the remote host. */

  u16_t lport;        /**< The local TCP port, in network byte order. */
  u16_t rport;        /**< The local remote TCP port, in network byte
			 order. */

  u8_t rcv_nxt[4];    /**< The sequence number that we expect to
			 receive next. */
  u8_t snd_nxt[4];    /**< The sequence number that was last sent by
                         us. */
  u16_t len;          /**< Length of the data that was previously sent. */
  u16_t mss;          /**< Current maximum segment size for the
			 connection. */
  u16_t initialmss;   /**< Initial maximum segment size for the
			 connection. */
  u8_t sa;            /**< Retransmission time-out calculation state
			 variable. */
  u8_t sv;            /**< Retransmission time-out calculation state
			 variable. */
  u8_t rto;           /**< Retransmission time-out. */
  u8_t tcpstateflags; /**< TCP state and flags. */
  u8_t timer;         /**< The retransmission timer. */
  u8_t nrtx;          /**< The number of retransmissions for the last
			 segment sent. */

  /** The application state. */
  u8_t appstate[UIP_APPSTATE_SIZE];
};


/* Pointer to the current connection. */
extern struct uip_conn *uip_conn;
/* The array containing all uIP connections. */
extern struct uip_conn uip_conns[UIP_CONNS];
/**
 * \addtogroup uiparch
 * @{
 */

/**
 * 4-byte array used for the 32-bit sequence number calculations.
 */
extern volatile u8_t uip_acc32[4];

/** @} */


#if UIP_UDP
/**
 * Representation of a uIP UDP connection.
 */
struct uip_udp_conn {
  u16_t ripaddr[2];   /**< The IP address of the remote peer. */
  u16_t lport;        /**< The local port number in network byte order. */
  u16_t rport;        /**< The remote port number in network byte order. */
};

extern struct uip_udp_conn *uip_udp_conn;
extern struct uip_udp_conn uip_udp_conns[UIP_UDP_CONNS];
#endif /* UIP_UDP */

/**
 * The structure holding the TCP/IP statistics that are gathered if
 * UIP_STATISTICS is set to 1.
 *
 */
struct uip_stats {
  struct {
    uip_stats_t drop;     /**< Number of dropped packets at the IP
			     layer. */
    uip_stats_t recv;     /**< Number of received packets at the IP
			     layer. */
    uip_stats_t sent;     /**< Number of sent packets at the IP
			     layer. */
    uip_stats_t vhlerr;   /**< Number of packets dropped due to wrong
			     IP version or header length. */
    uip_stats_t hblenerr; /**< Number of packets dropped due to wrong
			     IP length, high byte. */
    uip_stats_t lblenerr; /**< Number of packets dropped due to wrong
			     IP length, low byte. */
    uip_stats_t fragerr;  /**< Number of packets dropped since they
			     were IP fragments. */
    uip_stats_t chkerr;   /**< Number of packets dropped due to IP
			     checksum errors. */
    uip_stats_t protoerr; /**< Number of packets dropped since they
			     were neither ICMP, UDP nor TCP. */
  } ip;                   /**< IP statistics. */
  struct {
    uip_stats_t drop;     /**< Number of dropped ICMP packets. */
    uip_stats_t recv;     /**< Number of received ICMP packets. */
    uip_stats_t sent;     /**< Number of sent ICMP packets. */
    uip_stats_t typeerr;  /**< Number of ICMP packets with a wrong
			     type. */
  } icmp;                 /**< ICMP statistics. */
  struct {
    uip_stats_t drop;     /**< Number of dropped TCP segments. */
    uip_stats_t recv;     /**< Number of recived TCP segments. */
    uip_stats_t sent;     /**< Number of sent TCP segments. */
    uip_stats_t chkerr;   /**< Number of TCP segments with a bad
			     checksum. */
    uip_stats_t ackerr;   /**< Number of TCP segments with a bad ACK
			     number. */
    uip_stats_t rst;      /**< Number of recevied TCP RST (reset) segments. */
    uip_stats_t rexmit;   /**< Number of retransmitted TCP segments. */
    uip_stats_t syndrop;  /**< Number of dropped SYNs due to too few
			     connections was avaliable. */
    uip_stats_t synrst;   /**< Number of SYNs for closed ports,
			     triggering a RST. */
  } tcp;                  /**< TCP statistics. */
};

/**
 * The uIP TCP/IP statistics.
 *
 * This is the variable in which the uIP TCP/IP statistics are gathered.
 */
extern struct uip_stats uip_stat;


/*-----------------------------------------------------------------------------------*/
/* All the stuff below this point is internal to uIP and should not be
 * used directly by an application or by a device driver.
 */
/*-----------------------------------------------------------------------------------*/
/* u8_t uip_flags:
 *
 * When the application is called, uip_flags will contain the flags
 * that are defined in this file. Please read below for more
 * infomation.
 */
extern volatile u8_t uip_flags;

/* The following flags may be set in the global variable uip_flags
   before calling the application callback. The UIP_ACKDATA and
   UIP_NEWDATA flags may both be set at the same time, whereas the
   others are mutualy exclusive. Note that these flags should *NOT* be
   accessed directly, but through the uIP functions/macros. */

#define UIP_ACKDATA   1     /* Signifies that the outstanding data was
			       acked and the application should send
			       out new data instead of retransmitting
			       the last data. */
#define UIP_NEWDATA   2     /* Flags the fact that the peer has sent
			       us new data. */
#define UIP_REXMIT    4     /* Tells the application to retransmit the
			       data that was last sent. */
#define UIP_POLL      8     /* Used for polling the application, to
			       check if the application has data that
			       it wants to send. */
#define UIP_CLOSE     16    /* The remote host has closed the
			       connection, thus the connection has
			       gone away. Or the application signals
			       that it wants to close the
			       connection. */
#define UIP_ABORT     32    /* The remote host has aborted the
			       connection, thus the connection has
			       gone away. Or the application signals
			       that it wants to abort the
			       connection. */
#define UIP_CONNECTED 64    /* We have got a connection from a remote
                               host and have set up a new connection
                               for it, or an active connection has
                               been successfully established. */

#define UIP_TIMEDOUT  128   /* The connection has been aborted due to
			       too many retransmissions. */


/* uip_process(flag):
 *
 * The actual uIP function which does all the work.
 */
void uip_process(u8_t flag);

/* The following flags are passed as an argument to the uip_process()
   function. They are used to distinguish between the two cases where
   uip_process() is called. It can be called either because we have
   incoming data that should be processed, or because the periodic
   timer has fired. */

#define UIP_DATA    1     /* Tells uIP that there is incoming data in
                             the uip_buf buffer. The length of the
                             data is stored in the global variable
                             uip_len. */
#define UIP_TIMER   2     /* Tells uIP that the periodic timer has
                             fired. */
#if UIP_UDP
#define UIP_UDP_TIMER 3
#endif /* UIP_UDP */

/* The TCP states used in the uip_conn->tcpstateflags. */
#define CLOSED      0
#define SYN_RCVD    1
#define SYN_SENT    2
#define ESTABLISHED 3
#define FIN_WAIT_1  4
#define FIN_WAIT_2  5
#define CLOSING     6
#define TIME_WAIT   7
#define LAST_ACK    8
#define TS_MASK     15

#define UIP_STOPPED      16

#define UIP_TCPIP_HLEN 40

/* The TCP and IP headers. */
typedef struct {
  /* IP header. */
  u8_t vhl,
    tos,
    len[2],
    ipid[2],
    ipoffset[2],
    ttl,
    proto;
  u16_t ipchksum;
  u16_t srcipaddr[2],
    destipaddr[2];

  /* TCP header. */
  u16_t srcport,
    destport;
  u8_t seqno[4],
    ackno[4],
    tcpoffset,
    flags,
    wnd[2];
  u16_t tcpchksum;
  u8_t urgp[2];
  u8_t optdata[4];
} uip_tcpip_hdr;

/* The ICMP and IP headers. */
typedef struct {
  /* IP header. */
  u8_t vhl,
    tos,
    len[2],
    ipid[2],
    ipoffset[2],
    ttl,
    proto;
  u16_t ipchksum;
  u16_t srcipaddr[2],
    destipaddr[2];
  /* ICMP (echo) header. */
  u8_t type, icode;
  u16_t icmpchksum;
  u16_t id, seqno;
} uip_icmpip_hdr;


/* The UDP and IP headers. */
typedef struct {
  /* IP header. */
  u8_t vhl,
    tos,
    len[2],
    ipid[2],
    ipoffset[2],
    ttl,
    proto;
  u16_t ipchksum;
  u16_t srcipaddr[2],
    destipaddr[2];

  /* UDP header. */
  u16_t srcport,
    destport;
  u16_t udplen;
  u16_t udpchksum;
} uip_udpip_hdr;

#define UIP_PROTO_ICMP  1
#define UIP_PROTO_TCP   6
#define UIP_PROTO_UDP   17

#if UIP_FIXEDADDR
extern const u16_t uip_hostaddr[2];
#else /* UIP_FIXEDADDR */
extern u16_t uip_hostaddr[2];
#endif /* UIP_FIXEDADDR */

#endif /* __UIP_H__ */


/** @} */

