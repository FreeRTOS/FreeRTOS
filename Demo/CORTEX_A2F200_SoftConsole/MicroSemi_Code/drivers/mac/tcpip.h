/*******************************************************************************
 * (c) Copyright 2009 SLS Corporation,All Rights Reserved.  
 * 
 *  tcpip.h:header file of TCP/IP implementation.
 * 
 *  Version       Author         Comment
 *  1.0.0         SLS corp.		 First release,16 Jan 2009
 */
#ifndef TCPIP_H_
#define TCPIP_H_

#define FLASH_CONTEXT_INDICATOR      0x20000000
#define FLASH_SELFWAKEUP_INDICATOR	 0x20000001
#define FLASH_CONTEXT_LOCATION       0x20000002

/***************************************************************************//**
 * Replies to ARP requests.
 * 
 * @param  buf      Pointer to the recieved buffer from Ethernet MAC.
 * 
 */
unsigned char send_arp_reply(unsigned char *buf);
/***************************************************************************//**
 * Sends gratuitous arp brodcast message to the LAN.
 * 
 * @param  buf      Pointer to the recieved buffer from Ethernet MAC.
 *  
 */
void send_gratuitous_arp(unsigned char *buf);
/***************************************************************************//**
 * Calculates the checksum for Ethernet data in the header.
 * 
 *  @param  buf      Pointer to the recieved buffer from Ethernet MAC.
 *  @param  len		 Number of bytes.
 *  @param  pos      position for the check sum.   
 * 
 *  @return          value of the checksum
 */
unsigned short int get_checksum(unsigned char *buf, unsigned short int len, unsigned short int pos);
/***************************************************************************//**
 * Calls internally to get_checksum and fixes the value of the checksum to
 * position.
 * 
 *  @param  buf      Pointer to the recieved buffer from Ethernet MAC.
 *  @param  len		 Number of bytes.
 *  @param  pos      position for the check sum.
 * 
 *   @return         OK
 */
unsigned char fix_checksum(unsigned char *buf, unsigned short int len, unsigned short int pos);
/***************************************************************************//**
 * Checks the calculated checksum for the errors.
 * 
 * @param  buf      Pointer to the recieved buffer from Ethernet MAC.
 * @param  len		Number of bytes.
 * @param  pos      position for the check sum.
 * 
 * @return OK       If there is no error
 *	       ERR		If there is error in the data  		  	
 */
unsigned char check_checksum(unsigned char *buf, unsigned short int len, unsigned short int pos, char type);
/***************************************************************************//**
 * Sends the reply to ICMP request like PING.
 * 
 * @param  buf      Pointer to the recieved buffer from Ethernet MAC.
 */
unsigned char send_icmp_echo_reply(unsigned char *buf);
/***************************************************************************//**
 * Converts the input integer to the ascii char and fills in the buffer. 
 * 
 *  @param  buf      To filled in by the ascii value.
 *  @param  n		 integer number
 */
void dtoa_reverse(unsigned short int n, unsigned char *buf);
/***************************************************************************//**
 * Sends DHCP request to the server available in LAN.
 * 
 * @param  buf       Pointer to the recieved data in case of DHCP reply.Zero for request. 
 */
void send_bootp_packet (unsigned char *buf);
/***************************************************************************//**
 * Processes the UDP datagram.
 * 
 * @param  buf      Pointer to the recieved buffer from Ethernet MAC.
 */
unsigned char process_udp_packet (unsigned char *buf);
/***************************************************************************//**
 * Sends TCP packet to the network.
 * 
 * @param  buf      Pointer to the transmitt buffer to Ethernet MAC.
 */
void send_tcp_packet (unsigned char control_bits,unsigned short int buflen);
/***************************************************************************//**
 * Initialize TCP for the software TCP/IP stack.
 * 
 * @return OK
 */
unsigned char tcp_init(void);
/***************************************************************************//**
 * Converts two hex decimal ascii digits into a sigle integer digit.
 * 
 * @param 	u  ascii hex digit 
 * 		  	l  ascii hex digit
 * @returm	converted integer byte
 * 
 */
unsigned char hex_digits_to_byte(unsigned char u, unsigned char l);
/***************************************************************************//**
 * Processes ICMP packets
 * 
 * @param  buf  Pointer to the recieved buffer from Ethernet MAC.
 * 
 * @return ERR  if there is an error in the data
 * 				or calls further necessary functions.
 */
unsigned char process_icmp_packet(unsigned char *buf);
/***************************************************************************//**
 * Sends logo of ACTEL on the network over HTTP protocol.
 * @return OK
 */
unsigned char http_send_logo ();
/***************************************************************************//**
 * Sends appropriate answer to the different HTTP requests.
 * 
 * @param  buf  Pointer to the recieved buffer from Ethernet MAC.
 * @return OK
 */
unsigned char send_http_response(unsigned char *buf);
/***************************************************************************//**
 * Process incoming TCP requests and handles the TCP state machine.
 * 
 * @param  buf  Pointer to the recieved buffer from Ethernet MAC.
 * @return OK
 */
unsigned char process_tcp_packet(unsigned char *buf);
/***************************************************************************//**
 * Process incoming IP datagrams and handles the TCP state machine.
 *  
 * @param  buf  Pointer to the recieved buffer from Ethernet MAC.
 * @return OK
 */
unsigned char process_ip_packet(unsigned char *buf);
/***************************************************************************//**
 * Processes the ARP packets. 
 * @param  buf  Pointer to the recieved buffer from Ethernet MAC.
 * @return OK 
 */
unsigned char process_arp_packet(unsigned char *buf);
/***************************************************************************//**
 * Processes incoming packets and identifies its type.
 * 
 * @param  buf  Pointer to the recieved buffer from Ethernet MAC.
 * @return 		call the function for further process
 * 		   ERR   if any error
 */
unsigned char process_packet( unsigned char * buf );
/***************************************************************************//**
 * copies source string to destination address.
 * 
 * @param d	 Pointer to the destination
 * @param s  Pointer to the source
 * @return   The last location after copy
 * 
 */
unsigned char *xstrcpy(unsigned char *d, const unsigned char *s);
/***************************************************************************//**
 * Sends the home page of the demonstration webserver.
 * 
 */
void http_send_packet();
/***************************************************************************//**
 * Sends the packet for waveform mode.
 * 
 */
void http_send_packet_waveform();
/***************************************************************************//**
 *  Sends the packet for multimeter mode.
 * 
 */
void http_send_packet_multimeter();
/***************************************************************************//**
 *  Sends the packet for DAC mode.
 * 
 */
void http_send_packet_DAC();
/***************************************************************************//**
 *  Sends the packet for sleeping stopwatch.
 * 
 */
void http_send_packet_SLEEPING_STOPWATCH();
/***************************************************************************//**
 *  Sends the packet for text terminal.
 * 
 */
void http_send_packet_textterminal();
/***************************************************************************//**
 *  Sends the packet for VIT auxiliary mode.
 * 
 */
void http_send_packet_VIT();
/***************************************************************************//**
 *  Sends the packet for Real Time Data Display.
 * 
 */
void http_send_packet_RTDD();
/***************************************************************************//**
 *  Sends the packet for Stock Ticker.
 * 
 */
void http_send_packet_Stockticker();
/***************************************************************************//**
 *  Sends the packet for Gadgets mode.
 * 
 */
void http_send_packet_weatherblog();
/***************************************************************************//**
 *  Sends the packet for Selfwakeup.
 * 
 */
void http_send_packet_SELFWAKEUP();
/***************************************************************************//**
 * Same as above mentioned functions but following functions are applicable
 * to Internet Explorer.
 * 
 */
void http_send_packet_IE();
void http_send_packet_SELFWAKEUP_IE();
void http_send_packet_VIT_IE();
void http_send_packet_waveform_IE();
void http_send_packet_SLEEPING_STOPWATCH_IE();
void http_send_packet_DAC_IE();
void http_send_packet_multimeter_IE();
void http_send_packet_RTDD_IE();
#endif /*TCPIP_H_*/
