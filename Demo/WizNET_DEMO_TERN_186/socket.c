/*
********************************************************************************
* TERN, Inc.
* (c) Copyright 2005, http://www.tern.com
*
* MODIFIED BY RICHARD BARRY TO ADD SEMAPHORE FOR COMMUNICATION BETWEEN THE 
* WIZnet ISR AND THE HTTP TASK.
*
* - Derived based on development version provided by Wiznet.
*
* Filename : socket.h
* Programmer(s):
* Created : 2002/06/20
* Modified :
*  2002/09/27 : - Renaming
*			       INT_STATUS --> INT_REG
*			       STATUS(i) --> INT_STATUS(i)
*			       C_STATUS(i) --> SOCK_STATUS(i)
*  2003/11/06 : Ported for use with TERN controller.  Note all byte access is at even addresses
*  2005/10/8  : Modified constants for easier initialization.
*
* Description : Header file of W3100A for TERN embedded controller
********************************************************************************
*/
/*
###############################################################################
File Include Section
###############################################################################
*/
#include "i2chip_hw.h" 
#include "socket.h"
#include "types.h"
#include <string.h>
#include <stdio.h>

#include <FreeRTOS.h>
#include <semphr.h>
#include <portasm.h>


/*
###############################################################################
Local Variable Declaration Section
###############################################################################
*/
u_char I_STATUS[4];				// Store Interrupt Status according to channels
u_int Local_Port;				   // Designate Local Port
union un_l2cval	SEQ_NUM;		// Set initial sequence number

u_long SMASK[MAX_SOCK_NUM];   // Variable to store MASK of Tx in each channel,
                              // on setting dynamic memory size.
u_long RMASK[MAX_SOCK_NUM];   // Variable to store MASK of Rx in each channel,
                              // on setting dynamic memory size.
int SSIZE[MAX_SOCK_NUM];      // Maximun Tx memory size by each channel
int RSIZE[MAX_SOCK_NUM];      // Maximun Rx memory size by each channel

u_int SBUFBASEADDRESS[MAX_SOCK_NUM];   // Maximun Tx memory base address by each channel
u_int RBUFBASEADDRESS[MAX_SOCK_NUM];   // Maximun Rx memory base address by each channel

/*
###############################################################################
Function Implementation Section
###############################################################################
*/

/*
********************************************************************************
*               Interrupt handling function of the W3100A
*
* Description :
*   Stores the status information that each function waits for in the global variable I_STATUS
*   for transfer. I_STATUS stores the interrupt status value for each channel.
* Arguments   : None
* Returns     : None
* Note        : Internal Function
********************************************************************************
*/

portBASE_TYPE prvProcessISR( void )
{
unsigned char status;
extern xSemaphoreHandle xTCPSemaphore;
portBASE_TYPE xSwitchRequired = pdFALSE;

#ifdef I2CHIP_WINDOW
u_int current_window = i2chip_get_window();
#endif

status = READ_VALUE(INT_REG);


if (status)
  {
  xSwitchRequired = pdTRUE;
  // channel 0 interrupt(sysinit, sockinit, established, closed, timeout, send_ok, recv_ok)
  if (status & 0x01)
    {
	 I_STATUS[0] = READ_VALUE(INT_STATUS(0));

//	 if (I_STATUS[0] & SESTABLISHED)
//    ISR_ESTABLISHED(0);
//	 if (I_STATUS[0] & SCLOSED)
//    ISR_CLOSED(0);

	 WRITE_VALUE(INT_REG, 0x01);
	 }

  // channel 1 interrupt(sysinit, sockinit, established, closed, timeout, send_ok, recv_ok)
  if (status & 0x02)
    {
	 I_STATUS[1] = READ_VALUE(INT_STATUS(1));

//	 if (I_STATUS[1] & SESTABLISHED)
//    ISR_ESTABLISHED(1);
//	 if (I_STATUS[1] & SCLOSED)
//    ISR_CLOSED(1);

	 WRITE_VALUE(INT_REG, 0x02);
	 }

  // channel 2 interrupt(sysinit, sockinit, established, closed, timeout, send_ok, recv_ok)
  if (status & 0x04)
    {
	 I_STATUS[2] = READ_VALUE(INT_STATUS(2));

//	 if (I_STATUS[2] & SESTABLISHED)
//    ISR_ESTABLISHED(2);
//	 if (I_STATUS[2] & SCLOSED)
//    ISR_CLOSED(2);

	 WRITE_VALUE(INT_REG, 0x04);
	 }

  // channel 3 interrupt(sysinit, sockinit, established, closed, timeout, send_ok, recv_ok)
  if (status & 0x08)
    {
	 I_STATUS[3] = READ_VALUE(INT_STATUS(3));

//	 if (I_STATUS[3] & SESTABLISHED) ISR_ESTABLISHED(3);
//	 if (I_STATUS[3] & SCLOSED) ISR_CLOSED(3);

	 WRITE_VALUE(INT_REG, 0x08);
	 }

  // channel 0 receive interrupt
  if (status & 0x10)
    {
//	 ISR_RX(0);
	 WRITE_VALUE(INT_REG, 0x10);
	 }

  // channel 1 receive interrupt
  if (status & 0x20)
    {
//	 ISR_RX(1);
	 WRITE_VALUE(INT_REG, 0x20);
	 }

  // channel 2 receive interrupt
  if (status & 0x40)
    {
//	 ISR_RX(2);
	 WRITE_VALUE(INT_REG, 0x40);
	 }

  // channel 3 receive interrupt
  if (status & 0x80)
    {
//	 ISR_RX(3);
	 WRITE_VALUE(INT_REG, 0x80);
	 }
  status = READ_VALUE(INT_REG);
  }

WRITE_VALUE(INT_REG, 0xFF);

#ifdef I2CHIP_WINDOW
i2chip_set_window(current_window);
#endif

	if( xSwitchRequired == pdTRUE )
    {
		xSwitchRequired = xSemaphoreGiveFromISR( xTCPSemaphore, pdFALSE );
    }

	return xSwitchRequired;
}

void far interrupt in4_isr_i2chip(void)
{
	if( prvProcessISR() == pdTRUE )
    {
		portEND_SWITCHING_ISR();
    }

    INT_EOI;
}

/*
****************************************************************************************************
*               Established connection interrupt handling function.
*
* Description :
*   Called upon connection establishment, and may be inserted in user code if needed by
*   the programmer.
* Arguments   : None
* Returns     : None
* Note        : Internal Function
****************************************************************************************************
*/
/*
void ISR_ESTABLISHED(SOCKET s)
{
// TO ADD YOUR CODE
}
*/

/*
****************************************************************************************************
*               Closed connection interrupt handling function
*
* Description :
*   Called upon connection closure, and may be inserted in user code if needed by the programmer.
* Arguments   : None
* Returns     : None
* Note        : Internal Function
****************************************************************************************************
*/
/*
void ISR_CLOSED(SOCKET s)
{
// TO ADD YOUR CODE
}
*/

/*
****************************************************************************************************
*               Received data interrupt handling function
*
* Description :
*   Called upon receiving data, and may be inserted in user code if needed by the programmer.
* Arguments   : None
* Returns     : None
* Note        : Internal Function
****************************************************************************************************
*/
/*
void ISR_RX(SOCKET s)
{
// TO ADD YOUR CODE
}
*/

/*
****************************************************************************************************
*              W3100A Initialization Function
*
* Description:  Reset of W3100A S/W and Registeration of i386 interrupt
* Arguments  : None.
* Returns    : None.
* Note       :
****************************************************************************************************
*/
void initW3100A(void)
{

// Install interrupt handler for i2Chip
INT_INIT(in4_isr_i2chip);


Local_Port = 1000;         // This default value will be set if you didn't designate it when you
                           // create a socket. If you don't designate port number and create a
                           // socket continuously, the port number will be assigned with
                           // incremented by one to Local_Port
SEQ_NUM.lVal = 4294967293ul;	// Sets the initial SEQ# to be used for TCP communication.
                           // (It should be ramdom value)
WRITE_VALUE(COMMAND(0), CSW_RESET);   // Software RESET
}

/*
****************************************************************************************************
*               W3100A initialization function
*
* Description :
*   Sets the Tx, Rx memory size by each channel, source MAC, source IP, gateway, and subnet mask
*   to be used by the W3100A to the designated values.
*   May be called when reflecting modified network information or Tx, Rx memory size on the W3100A
*   Include Ping Request for ARP update (In case that a device embedding W3100A is directly
*     connected to Router)
* Arguments  : sbufsize - Tx memory size (00 - 1KByte, 01- 2KBtye, 10 - 4KByte, 11 - 8KByte)
*                          bit 1-0 : Tx memory size of channel #0
*                          bit 3-2 : Tx memory size of channel #1
*                          bit 5-4 : Tx memory size of channel #2
*                          bit 7-6 : Tx memory size of channel #3
*              rbufsize - Rx memory size (00 - 1KByte, 01- 2KBtye, 10 - 4KByte, 11 - 8KByte)
*                          bit 1-0 : Rx memory size of channel #0
*                          bit 3-2 : Rx memory size of channel #1
*                          bit 5-4 : Rx memory size of channel #2
*                          bit 7-6 : Rx memory size of channel #3
* Returns    : None
* Note       : API Function
*              Maximum memory size for Tx, Rx in W3100A is 8KBytes,
*              In the range of 8KBytes, the memory size could be allocated dynamically by
*              each channel
*              Be attentive to sum of memory size shouldn't exceed 8Kbytes
*              and to data transmission and receiption from non-allocated channel may cause
*              some problems.
*              If 8KBytes memory already is assigned to centain channel, other 3 channels
*                couldn't be used, for there's no available memory.
*              If two 4KBytes memory are assigned to two each channels, other 2 channels couldn't
*                be used, for there's no available memory.
*              (Example of memory assignment)
*               sbufsize => 00000011, rbufsize => 00000011 :
*                 Assign 8KBytes for Tx and Rx to channel #0, Cannot use channel #1,#2,#3
*               sbufsize => 00001010, rbufsize => 00001010 :
*                 Assign 4KBytes for Tx and Rx to each channel #0,#1 respectively. Cannot use
*                 channel #2,#3
*               sbufsize => 01010101, rbufsize => 01010101 :
*                 Assign 2KBytes for Tx and Rx to each all channels respectively.
*               sbufsize => 00010110, rbufsize => 01010101 :
*                 Assign 4KBytes for Tx, 2KBytes for Rx to channel #0
*       s          2KBytes for Tx, 2KBytes for Rx to channel #1
*                 2KBytes for Tx, 2KBytes for Rx to channel #2
*                 2KBytes is available exclusively for Rx in channel #3. There's no memory for Tx.
****************************************************************************************************
*/
void sysinit(u_char sbufsize, u_char rbufsize)
{
char i;
int ssum,rsum;

ssum = 0;
rsum = 0;

// Set Tx memory size for each channel
WRITE_VALUE(TX_DMEM_SIZE, sbufsize);

// Set Rx memory size for each channel
WRITE_VALUE(RX_DMEM_SIZE, rbufsize);

// Set Base Address of Tx memory for channel #0
SBUFBASEADDRESS[0] = 0;

// Set Base Address of Rx memory for channel #0
RBUFBASEADDRESS[0] = 0;

// Set maximum memory size for Tx and Rx, mask, base address of memory by each channel
for(i = 0 ; i < MAX_SOCK_NUM; i++)
  {
  SSIZE[i] = 0;
  RSIZE[i] = 0;
  if(ssum < 8192)
	 {
	 switch((sbufsize >> i*2) & 0x03) // Set maximum Tx memory size
		{
		case 0:
		  SSIZE[i] = 1024;
		  SMASK[i] = 0x000003FF;
		  break;

		case 1:
		  SSIZE[i] = 2048;
		  SMASK[i] = 0x000007FF;
		  break;

		case 2:
		  SSIZE[i] = 4096;
		  SMASK[i] = 0x00000FFF;
		  break;

		case 3:
		  SSIZE[i] = 8192;
		  SMASK[i] = 0x00001FFF;
		  break;
		}
	 }
  if(rsum < 8192)
	 {
	 switch((rbufsize >> i*2) & 0x03)  // Set maximum Rx memory size
		{
		case 0:
		  RSIZE[i] = 1024;
		  RMASK[i] = 0x000003FF;
		  break;

		case 1:
		  RSIZE[i] = 2048;
		  RMASK[i] = 0x000007FF;
		  break;

		case 2:
		  RSIZE[i] = 4096;
		  RMASK[i] = 0x00000FFF;
		  break;

		case 3:
		  RSIZE[i] = 8192;
		  RMASK[i] = 0x00001FFF;
		  break;
		}
	 }
  ssum += SSIZE[i];
  rsum += RSIZE[i];

  // Set base address of Tx and Rx memory for channel #1,#2,#3
  if(i != 0)
    {
    SBUFBASEADDRESS[i] = ssum - SSIZE[i];
    RBUFBASEADDRESS[i] = rsum - RSIZE[i];
    }
  }

  WRITE_VALUE(COMMAND(0), CSYS_INIT);

while(!(I_STATUS[0] & SSYS_INIT_OK))
  I2CHIP_POLL_ISR(in4_isr_i2chip);

#ifdef __PING__
  {
  u_char xdata pingbuf[8];
  setIPprotocol(0, IPPROTO_ICMP);
  socket(0, SOCK_IPL_RAW, 3000,0);     // Create a socket for ARP update

  pingbuf[0] = 8;                      // ICMP TYPE
  pingbuf[1] = 0;                      // ICMP CODE
  pingbuf[2] = 0xf7;                   // CHECKSUM (already calculated)
  pingbuf[3] = 0xfd;
  pingbuf[4] = 0;                      // ID
  pingbuf[5] = 1;
  pingbuf[6] = 0;                      // SEQ #
  pingbuf[7] = 1;
  pingbuf[8] = 0;                      // Data 1 Byte

  sendto(0, pingbuf, 9, GATEWAY_PTR,3000);  // Ping Request
  close(0);
  printf("Route MAC Update Success");
  }
#endif
}

/*
****************************************************************************************************
*              Function to set subnet mask
*
* Description:
* Arguments  : addr--> Pointer that has the value to be set
* Returns    : None.
* Note       :
****************************************************************************************************
*/
void setsubmask(u_char * addr)
{
u_char i;
u_char far* sm_ptr = SUBNET_MASK_PTR;   // We can only convert to 'regular'
                                   // pointer if we're confident arithmetic
                                   // won't take us out of current window.

for (i = 0; i < 4; i++)
  {
  WRITE_VALUE(sm_ptr + SA_OFFSET(i), addr[i]);
  }
}

/*
****************************************************************************************************
*               Function to set gateway IP
*
* Description:
* Arguments  : addr--> Pointer that has Gateway IP to be set
* Returns    : None.
* Note       :
****************************************************************************************************
*/
void setgateway(u_char * addr)
{
u_char i;
u_char far* gw_ptr = GATEWAY_PTR;   // We can only convert to 'regular'
                                   // pointer if we're confident arithmetic
                                   // won't take us out of current window.
for (i = 0; i < 4; i++)
  {
  WRITE_VALUE(gw_ptr + SA_OFFSET(i), addr[i]);
  }
}

/*
****************************************************************************************************
*                 Function to set W3100A IP
*
* Description:
* Arguments  : addr--> Pointer that has Source IP to be set
* Returns    : None.
* Note       :
****************************************************************************************************
*/
void setIP(u_char * addr)
{
u_char i;
u_char far* src_ptr = SRC_IP_PTR;   // We can only convert to 'regular'
                                   // pointer if we're confident arithmetic
                                   // won't take us out of current window.

for (i = 0; i < 4; i++)
  {
  WRITE_VALUE(src_ptr + SA_OFFSET(i), addr[i]);
  }
}

// DEBUG
void getIP(u_char* addr)
{
u_char i;
u_char far* src_ptr = SRC_IP_PTR;   // We can only convert to 'regular'
                                   // pointer if we're confident arithmetic
                                   // won't take us out of current window.

for (i = 0; i < 4; i++)
	addr[i] = READ_VALUE(src_ptr + SA_OFFSET(i));
}


/*
****************************************************************************************************
*                Function to set MAC
*
* Description:
* Arguments  : addr--> Pointer that has MAC to be set
* Returns    : None.
* Note       :
****************************************************************************************************
*/
void setMACAddr(u_char * addr)
{
u_char i;
u_char far* ha_ptr = SRC_HA_PTR;   // We can only convert to 'regular'
                                   // pointer if we're confident arithmetic
                                   // won't take us out of current window.

for (i = 0; i < 6; i++)
  {
  WRITE_VALUE(ha_ptr + SA_OFFSET(i), addr[i]);
  }
}

/*
****************************************************************************************************
*                  Function to set TCP timeout
*
* Description: The function that used to adjust time to resend TCP
* Arguments  : val	--> Pointer that has the value to be set
*					Upper 2 byte:Initial timeout value
*					Last 1 byte:The count to retry till timeout
* Returns    : None.
* Note       :
****************************************************************************************************
*/
void settimeout(u_char * val)
{
u_char i;
u_char far* tout_ptr = TIMEOUT_PTR;   // We can only convert to 'regular'
                                   // pointer if we're confident arithmetic
                                   // won't take us out of current window.

for (i = 0; i < 3; i++)
  {
  WRITE_VALUE(tout_ptr + SA_OFFSET(i), val[i]);
  }
}

/*
****************************************************************************************************
*                 Function to set interrupt mask.
*
* Description:
* Arguments  : mask--> Mask value to be set ('1'-> interrupt )
* Returns    : None.
* Note       :
****************************************************************************************************
*/
void setINTMask(u_char mask)
{
WRITE_VALUE(INTMASK, mask);
}

/*
****************************************************************************************************
*                  Function to set enable in sending and receiving of broadcast data
*
* Description:  Enable to process of broadcating data in UDP or IP RAW mode.
* Arguments  : s	--> Channel No. to be set
* Returns    : None.
* Note       :
****************************************************************************************************
*/
void setbroadcast(SOCKET s)
{
u_char val = READ_VALUE(OPT_PROTOCOL(s));
WRITE_VALUE(OPT_PROTOCOL(s), val | SOCKOPT_BROADCAST);
}

/*
****************************************************************************************************
*                Function to set process protocol  in IP RAW mode.
*
* Description:
* Arguments  : s--> Channel No. to be set
*	        tos-->Protocol Value to be set
* Returns    : None.
* Note       :
****************************************************************************************************
*/
void setTOS(SOCKET s, u_char tos)
{
WRITE_VALUE(TOS(s), tos);
}

/*
****************************************************************************************************
*               Upper layer protocol setup function in IP RAW Mode
*
* Description : Upper layer protocol setup function in protocol field of IP header when
*                    developing upper layer protocol like ICMP, IGMP, EGP etc. by using IP Protocol
* Arguments   : s          - Channel number
*               ipprotocol - Upper layer protocol setting value of IP Protocol
*                            (Possible to use designated IPPROTO_ in header file)
* Returns     : None
* Note        : API Function
*                  This function should be called before calling socket() that is, before
*                  socket initialization.
****************************************************************************************************
*/
void setIPprotocol(SOCKET s, u_char ipprotocol)
{
WRITE_VALUE(IP_PROTOCOL(s), ipprotocol);
}

/*
****************************************************************************************************
*              Initialization function to appropriate channel
*
* Description : Initialize designated channel and wait until W3100 has done.
* Arguments   : s - channel number
*               protocol - designate protocol for channel
*                          SOCK_STREAM(0x01) -> TCP.
*                          SOCK_DGRAM(0x02)  -> UDP.
*                          SOCK_IPL_RAW(0x03) -> IP LAYER RAW.
*                          SOCK_MACL_RAW(0x04) -> MAC LAYER RAW.
*               port     - designate source port for appropriate channel
*               flag     - designate option to be used in appropriate.
*                          SOCKOPT_BROADCAST(0x80) -> Send/receive broadcast message in UDP
*                          SOCKOPT_NDTIMEOUT(0x40) -> Use register value which designated TIMEOUT
*                            value
*                          SOCKOPT_NDACK(0x20)     -> When not using no delayed ack
*                          SOCKOPT_SWS(0x10)       -> When not using silly window syndrome
* Returns     : When succeeded : Channel number, failed :-1
* Note        : API Function
****************************************************************************************************
*/
char socket(SOCKET s, u_char protocol, u_int port, u_char flag)
{
u_char k;

//Designate socket protocol and option
WRITE_VALUE(OPT_PROTOCOL(s), protocol | flag);

// setup designated port number
if (port != 0)
  {
  k = (u_char)((port & 0xff00) >> 8);
  WRITE_VALUE(SRC_PORT_PTR(s), k);
  k = (u_char)(port & 0x00ff);
  WRITE_VALUE(SRC_PORT_PTR(s) + SA_OFFSET(1), k);
  }
else
  {
  // Designate random port number which is managed by local when you didn't designate source port
  Local_Port++;

  WRITE_VALUE(SRC_PORT_PTR(s), (u_char)((Local_Port & 0xff00) >> 8));
  WRITE_VALUE(SRC_PORT_PTR(s) + SA_OFFSET(1), (u_char)(Local_Port & 0x00ff));
  }

// SOCK_INIT
I_STATUS[s] = 0;
WRITE_VALUE(COMMAND(s), CSOCK_INIT);

// Waiting Interrupt to CSOCK_INIT
while (I_STATUS[s] == 0)
	I2CHIP_POLL_ISR(in4_isr_i2chip);

if (!(I_STATUS[s] & SSOCK_INIT_OK))
  return(-1);

initseqnum(s);							//  Use initial seq# with random number

return(s);
}

/*
****************************************************************************************************
*               Connection establishing function to designated peer.
*
* Description : This function establish a connection to the peer by designated channel,
*     and wait until the connection is established successfully. (TCP client mode)
* Arguments   : s    - channel number
*               addr - destination IP Address
*               port - destination Port Number
* Returns     : when succeeded : 1, failed : -1
* Note        : API Function
****************************************************************************************************
*/
char connect(SOCKET s, u_char far * addr, u_int port)
{

if (port != 0)
  {						//designate destination port
  WRITE_VALUE(DST_PORT_PTR(s), (u_char)((port & 0xff00) >> 8));
  WRITE_VALUE(DST_PORT_PTR(s) + SA_OFFSET(1), (u_char)(port & 0x00ff));
  }
else
  return(-1);

  WRITE_VALUE(DST_IP_PTR(s), addr[0]);				//designate destination IP address
  WRITE_VALUE(DST_IP_PTR(s) + SA_OFFSET(1), addr[1]);
  WRITE_VALUE(DST_IP_PTR(s) + SA_OFFSET(2), addr[2]);
  WRITE_VALUE(DST_IP_PTR(s) + SA_OFFSET(3), addr[3]);

I_STATUS[s] = 0;

  WRITE_VALUE(COMMAND(s), CCONNECT);					// CONNECT
  I2CHIP_POLL_ISR(in4_isr_i2chip);

// Wait until connection is established successfully
while (I_STATUS[s] == 0)
  {
  // When failed, appropriate channel will be closed and return an error
  if (select(s, SEL_CONTROL) == SOCK_CLOSED)
    return -1;
  }

if (!(I_STATUS[s] & SESTABLISHED))
  return(-1);

return(1);
}

/*
****************************************************************************************************
*               Connection establishing function to designated peer. (Non-blocking Mode)
*
* Description : This function establish a connection to the peer by designated channel.
*
* Arguments   : s    - channel number
*               addr - destination IP Address
*               port - destination Port Number
* Returns     : when succeeded : 1, failed : -1
* Note        : API Function
****************************************************************************************************
*/
char NBconnect(SOCKET s, u_char far * addr, u_int port)
{

if (port != 0)
  {						//designate destination port
	WRITE_VALUE(DST_PORT_PTR(s), (u_char) ((port & 0xff00) >> 8) );
   WRITE_VALUE(DST_PORT_PTR(s) + SA_OFFSET(1), (u_char)(port & 0x00ff));
  }
else
  return(-1);

  WRITE_VALUE(DST_IP_PTR(s), addr[0]);				//designate destination IP address
  WRITE_VALUE(DST_IP_PTR(s) + SA_OFFSET(1), addr[1]);
  WRITE_VALUE(DST_IP_PTR(s) + SA_OFFSET(2), addr[2]);
  WRITE_VALUE(DST_IP_PTR(s) + SA_OFFSET(3), addr[3]);

I_STATUS[s] = 0;

WRITE_VALUE(COMMAND(s), CCONNECT);					// CONNECT
return(1);
}

/*
****************************************************************************************************
*            Waits for connection request from a peer (Blocking Mode)
*
* Description : Wait for connection request from a peer through designated channel (TCP Server mode)
* Arguments   : s    - channel number
*               addr - IP Address of the peer when a connection is established
*               port - Port number of the peer when a connection is established
* Returns     : When succeeded : 1, failed : -1
* Note        : API Function
****************************************************************************************************
*/
/*
char listen(SOCKET s, u_char far * addr, u_int far * port)
{
u_int i;

I_STATUS[s] = 0;

// LISTEN
COMMAND(s) = CLISTEN;

// Wait until connection is established
while (I_STATUS[s] == 0)
  {
  // When failed to connect, the designated channel will be closed and return an error.
  if (select(s, SEL_CONTROL) == SOCK_CLOSED)
    return -1;
  }

// Receive IP address and port number of the peer connected
if (I_STATUS[s] & SESTABLISHED)
  {
  i = *DST_PORT_PTR(s);
  *port = (u_int)((i & 0xff00) >> 8);
  i = *(DST_PORT_PTR(s) + 2);
  i = (u_int)(i & 0x00ff);
  *port += (i << 8);

  addr[0] = *DST_IP_PTR(s);
  addr[1] = *(DST_IP_PTR(s) + 2);
  addr[2] = *(DST_IP_PTR(s) + 4);
  addr[3] = *(DST_IP_PTR(s) + 6);
  }
else
  return(-1);

return(1);
}
*/

/*
****************************************************************************************************
*                Waits for connection request from a peer (Non-blocking Mode)
*
* Description : Wait for connection request from a peer through designated channel (TCP Server mode)
* Arguments   : s - channel number
* Returns     : None
* Note        : API Function
****************************************************************************************************
*/
char NBlisten(SOCKET s)
{
I_STATUS[s] = 0;

// LISTEN
WRITE_VALUE(COMMAND(s), CLISTEN);

return(1);
}

/*
****************************************************************************************************
*               Create random value for initial Seq# when establishing TCP connection
*
* Description : In this function, you can add some source codes to create random number for
*     initial Seq#. In real, TCP initial SEQ# should be random value.
*               (Currently, we're using static value in EVB/DK.)
* Arguments   : s - channel number
* Returns     : None
* Note        : API Function
****************************************************************************************************
*/
void initseqnum(SOCKET s)
{
// Designate initial seq#
// If you have random number generation function, assign random number instead of SEQ_NUM.lVal++.
SEQ_NUM.lVal++;

//randomize();
//SEQ_NUM.lVal = rand();

WRITE_VALUE(TX_WR_PTR(s), SEQ_NUM.cVal[0]);
WRITE_VALUE(TX_WR_PTR(s) + SA_OFFSET(1), SEQ_NUM.cVal[1]);
WRITE_VALUE(TX_WR_PTR(s) + SA_OFFSET(2), SEQ_NUM.cVal[2]);
WRITE_VALUE(TX_WR_PTR(s) + SA_OFFSET(3), SEQ_NUM.cVal[3]);
delay0(2);

WRITE_VALUE(TX_RD_PTR(s), SEQ_NUM.cVal[0]);
WRITE_VALUE(TX_RD_PTR(s) + SA_OFFSET(1), SEQ_NUM.cVal[1]);
WRITE_VALUE(TX_RD_PTR(s) + SA_OFFSET(2), SEQ_NUM.cVal[2]);
WRITE_VALUE(TX_RD_PTR(s) + SA_OFFSET(3), SEQ_NUM.cVal[3]);
delay0(2);

WRITE_VALUE(TX_ACK_PTR(s), SEQ_NUM.cVal[0]);
WRITE_VALUE(TX_ACK_PTR(s) + SA_OFFSET(1), SEQ_NUM.cVal[1]);
WRITE_VALUE(TX_ACK_PTR(s) + SA_OFFSET(2), SEQ_NUM.cVal[2]);
WRITE_VALUE(TX_ACK_PTR(s) + SA_OFFSET(3), SEQ_NUM.cVal[3]);
delay0(2);
}

/*
****************************************************************************************************
*              Function for sending TCP data.
*
* Description : Function for sending TCP data and Composed of the send() and send_in() functions.
*     The send() function is an application I/F function.
*     It continues to call the send_in() function to complete the sending of the data up to the
*     size of the data to be sent when the application is called.
*     The send_in() function receives the return value (the size of the data sent), calculates
*     the size of the data to be sent, and calls the send_in() function again if there is any
*     data left to be sent.
* Arguments   : s   - channel number
*               buf - Pointer pointing data to send
*               len - data size to send
* Returns     : Succeed: sent data size, Failed:  -1;
* Note        : API Function
****************************************************************************************************
*/
int send(SOCKET s, u_char far * buf, u_int len)
{
int ptr, size;
u_char huge* huge_buf = (u_char huge*)buf;
u_char far*  local_buf = (u_char far*)huge_buf;    

if (len <= 0)
  return (0);
else
  {
  ptr = 0;
  do
    {
	 size = send_in(s, local_buf + ptr, len);
	 if (size == -1)
      return -1;
	 len = len - size;
	 ptr += size;
	 } while ( len > 0);
  }
return ptr;
}

/*
****************************************************************************************************
*              Internal function for sending TCP data.
*
* Description : Called by the send() function for TCP transmission.
*    It first calculates the free transmit buffer size
*    and compares it with the size of the data to be transmitted to determine the transmission size.
*    After calculating the data size, it copies data from TX_WR_PTR.
*    It waits if there is a previous send command in process.
*    When the send command is cleared, it updates the TX_WR_PTR up to the size to be transmitted
     and performs the send command.
* Arguments   : s   - channel number
*               buf - Pointer pointing data to send
*               len - data size to send
* Returns     : Succeeded: sent data size, Failed: -1
* Note        : Internal Function
****************************************************************************************************
*/
int send_in(SOCKET s, u_char far * buf, u_int len)
{
u_char k;
u_int size;
union un_l2cval wr_ptr, ack_ptr;
unsigned int offset;

S_START:
disable();            // CT: Shadow register access should not conflict with ISR.
k = READ_VALUE(SHADOW_TXWR_PTR(s));
WINDOW_RESTORE_BASE;  // Needed whenever we touch a shadow ptr; different window.
delay0(2);
wr_ptr.cVal[3] = READ_VALUE(TX_WR_PTR(s));
wr_ptr.cVal[2] = READ_VALUE(TX_WR_PTR(s) + SA_OFFSET(1));
wr_ptr.cVal[1] = READ_VALUE(TX_WR_PTR(s) + SA_OFFSET(2));
wr_ptr.cVal[0] = READ_VALUE(TX_WR_PTR(s) + SA_OFFSET(3));

k = READ_VALUE(SHADOW_TXACK_PTR(s));
WINDOW_RESTORE_BASE;  // Needed whenever we touch a shadow ptr; different window.
delay0(2);
ack_ptr.cVal[3] = READ_VALUE(TX_ACK_PTR(s));
ack_ptr.cVal[2] = READ_VALUE(TX_ACK_PTR(s) + SA_OFFSET(1));
ack_ptr.cVal[1] = READ_VALUE(TX_ACK_PTR(s) + SA_OFFSET(2));
ack_ptr.cVal[0] = READ_VALUE(TX_ACK_PTR(s) + SA_OFFSET(3));
enable();

// Suppress compiler errors that k is not used
k = k;

//  Calculate send free buffer size
if (wr_ptr.lVal >= ack_ptr.lVal)
  size = (u_int)(SSIZE[s] - (wr_ptr.lVal - ack_ptr.lVal));
else
  size = (u_int)(SSIZE[s] - (0 - ack_ptr.lVal + wr_ptr.lVal));

// Recalulate after some delay because of error in pointer calculation
if (size > SSIZE[s])
  {
  if (select(s, SEL_CONTROL) != SOCK_ESTABLISHED)
    return -1;
  delay_ms(1);
	 goto S_START;
  }

// Wait when previous sending has not finished yet and there's no free buffer
if (size == 0)
  {
  if (select(s, SEL_CONTROL) != SOCK_ESTABLISHED)
    return -1;

  delay_ms(1);
  goto S_START;
  }
else if (size < len)
  {
  len = size;
  }

//  Calculate pointer to data copy
offset = (UINT)(wr_ptr.lVal & SMASK[s]);

// copy data
write_data(s, buf, offset, len);

while (READ_VALUE(COMMAND(s)) & CSEND)
  {
  // Confirm previous send command
  if (select(s, SEL_CONTROL) != SOCK_ESTABLISHED)
    return -1;
  }

//  update tx_wr_ptr
wr_ptr.lVal = wr_ptr.lVal + len;
WRITE_VALUE(TX_WR_PTR(s), wr_ptr.cVal[3]);
WRITE_VALUE(TX_WR_PTR(s) + SA_OFFSET(1), wr_ptr.cVal[2]);
WRITE_VALUE(TX_WR_PTR(s) + SA_OFFSET(2), wr_ptr.cVal[1]);
WRITE_VALUE(TX_WR_PTR(s) + SA_OFFSET(3), wr_ptr.cVal[0]);

delay0(1);

// SEND
WRITE_VALUE(COMMAND(s), CSEND);

return(len);
}

/*
****************************************************************************************************
*              TCP data receiving function.
*
* Description : This function is to clear out any received TCP data.
* Arguments   : s   - channel number
* Returns     : None
* Note        : API Fcuntion
****************************************************************************************************
*/
void recv_clear(SOCKET s)
{
u_char k;
u_int size;
union un_l2cval wr_ptr, rd_ptr;

disable();
k = READ_VALUE(SHADOW_RXWR_PTR(s));
WINDOW_RESTORE_BASE;  // Needed whenever we touch a shadow ptr; different window.
delay0(2);
wr_ptr.cVal[3] = READ_VALUE(RX_WR_PTR(s));
wr_ptr.cVal[2] = READ_VALUE(RX_WR_PTR(s) + SA_OFFSET(1));
wr_ptr.cVal[1] = READ_VALUE(RX_WR_PTR(s) + SA_OFFSET(2));
wr_ptr.cVal[0] = READ_VALUE(RX_WR_PTR(s) + SA_OFFSET(3));

k = READ_VALUE(SHADOW_RXRD_PTR(s));
WINDOW_RESTORE_BASE;  // Needed whenever we touch a shadow ptr; different window.
delay0(2);
rd_ptr.cVal[3] = READ_VALUE(RX_RD_PTR(s));
rd_ptr.cVal[2] = READ_VALUE(RX_RD_PTR(s) + SA_OFFSET(1));
rd_ptr.cVal[1] = READ_VALUE(RX_RD_PTR(s) + SA_OFFSET(2));
rd_ptr.cVal[0] = READ_VALUE(RX_RD_PTR(s) + SA_OFFSET(3));
enable();

// Suppress compiler errors that k is not used
k = k;

//  calculate received data size
if (wr_ptr.lVal >= rd_ptr.lVal)
  size = (u_int)(wr_ptr.lVal - rd_ptr.lVal);
else
  size = (u_int)(0 - rd_ptr.lVal + wr_ptr.lVal);

// Update rx_rd_ptr
rd_ptr.lVal += size;
WRITE_VALUE(RX_RD_PTR(s), rd_ptr.cVal[3]);
WRITE_VALUE(RX_RD_PTR(s) + SA_OFFSET(1), rd_ptr.cVal[2]);
WRITE_VALUE(RX_RD_PTR(s) + SA_OFFSET(2), rd_ptr.cVal[1]);
WRITE_VALUE(RX_RD_PTR(s) + SA_OFFSET(3), rd_ptr.cVal[0]);

// RECV
 WRITE_VALUE(COMMAND(s), CRECV);
}

/*
****************************************************************************************************
*              TCP data receiving function.
*
* Description : This function is for receiving TCP data.
*     The recv() function is an application I/F function. It will read up to len chars if there are
      enough characters in the buffer, otherwise will onl read the number of characters availiable
* Arguments   : s   - channel number
*               buf - Pointer where the data to be received is copied
*               len - Size of the data to be received
* Returns     : Succeeded: received data size, Failed: -1
* Note        : API Fcuntion
****************************************************************************************************
*/
int recv(SOCKET s, u_char far * buf, u_int len)
{
u_char k;
u_int size;
union un_l2cval wr_ptr, rd_ptr;
unsigned int offset;

// If out length is 0, then we do not need to do anything
if (len <= 0)
  return (0);

disable();
k = READ_VALUE(SHADOW_RXWR_PTR(s));
WINDOW_RESTORE_BASE;  // Needed whenever we touch a shadow ptr; different window.
delay0(2);
wr_ptr.cVal[3] = READ_VALUE(RX_WR_PTR(s));
wr_ptr.cVal[2] = READ_VALUE(RX_WR_PTR(s) + SA_OFFSET(1));
wr_ptr.cVal[1] = READ_VALUE(RX_WR_PTR(s) + SA_OFFSET(2));
wr_ptr.cVal[0] = READ_VALUE(RX_WR_PTR(s) + SA_OFFSET(3));

k = READ_VALUE(SHADOW_RXRD_PTR(s));
WINDOW_RESTORE_BASE;  // Needed whenever we touch a shadow ptr; different window.
delay0(2);
rd_ptr.cVal[3] = READ_VALUE(RX_RD_PTR(s));
rd_ptr.cVal[2] = READ_VALUE(RX_RD_PTR(s) + SA_OFFSET(1));
rd_ptr.cVal[1] = READ_VALUE(RX_RD_PTR(s) + SA_OFFSET(2));
rd_ptr.cVal[0] = READ_VALUE(RX_RD_PTR(s) + SA_OFFSET(3));
enable();

// Suppress compiler errors that k is not used
k = k;

//  calculate IIM7010A received data size
if (wr_ptr.lVal == rd_ptr.lVal)
  return(0);
else if (wr_ptr.lVal >= rd_ptr.lVal)
  size = (u_int)(wr_ptr.lVal - rd_ptr.lVal);
else
  size = (u_int)(0 - rd_ptr.lVal + wr_ptr.lVal);

// Make sure we do not try to read more characters than what is availiable in the IIM7010 buffer
if (size < len)
  len = size;

// Calculate pointer to be copied received data
offset = ((UINT)(rd_ptr.lVal & RMASK[s]));

// Copy received data
size = read_data(s, offset, buf, len);

// Update rx_rd_ptr
rd_ptr.lVal += size;
WRITE_VALUE(RX_RD_PTR(s), rd_ptr.cVal[3]);
WRITE_VALUE(RX_RD_PTR(s) + SA_OFFSET(1), rd_ptr.cVal[2]);
WRITE_VALUE(RX_RD_PTR(s) + SA_OFFSET(2), rd_ptr.cVal[1]);
WRITE_VALUE(RX_RD_PTR(s) + SA_OFFSET(3), rd_ptr.cVal[0]);

// RECV
 WRITE_VALUE(COMMAND(s), CRECV);
return(size);
}


/*
****************************************************************************************************
*               UDP data sending function.
*
* Description : Composed of the sendto()and sendto_in() functions.
*    The send() function is an application I/F function.
*    It continues to call the send_in() function to complete the sending of the data up to the
*    size of the data to be sent
*    when the application is called.Unlike TCP transmission, it designates the destination address
*    and the port.
* Arguments   : s    - channel port
*               buf  - Pointer pointing data to send
*               len  - data size to send
*               addr - destination IP address to send data
*               port - destination port number to send data
* Returns     : Sent data size
* Note        : API Function
****************************************************************************************************
*/
u_int sendto(SOCKET s, u_char far * buf, u_int len, u_char * addr, u_int port)
{
//char val;
u_int ptr, size;

// Wait until previous send commnad has completed.
while(READ_VALUE(COMMAND(s)) & CSEND)
  {
  if(select(s, SEL_CONTROL) == SOCK_CLOSED)
    return -1;	// Error.
  }

// Designate destination port number.
if (port != 0)
  {
  WRITE_VALUE(DST_PORT_PTR(s), (u_char)((port & 0xff00) >> 8));
  WRITE_VALUE(DST_PORT_PTR(s) + SA_OFFSET(1), (u_char)(port & 0x00ff));
  }

//  Designate destination IP address
WRITE_VALUE(DST_IP_PTR(s), addr[0]);
WRITE_VALUE(DST_IP_PTR(s) + SA_OFFSET(1), addr[1]);
WRITE_VALUE(DST_IP_PTR(s) + SA_OFFSET(2), addr[2]);
WRITE_VALUE(DST_IP_PTR(s) + SA_OFFSET(3), addr[3]);

if (len <= 0)
  return (0);
else
  {
  ptr = 0;
  do
    {
	 size = sendto_in(s, buf + ptr, len);
	 len = len - size;
	 ptr += size;
	 } while ( len > 0);
  }
return ptr;
}

/*
****************************************************************************************************
*            UDP data sending function.
*
* Description : An internal function that is the same as the send_in() function of the TCP.
* Arguments   : s   - Channel number
*               buf - Pointer indicating the data to send
*               len - data size to send
* Returns     : Sent data size
* Note        : Internal Function
****************************************************************************************************
*/
u_int sendto_in(SOCKET s, u_char far * buf, u_int len)
{
u_char k;
u_int size;
union un_l2cval wr_ptr, rd_ptr;
unsigned int offset;

S2_START:
disable();
k = READ_VALUE(SHADOW_TXWR_PTR(s));
WINDOW_RESTORE_BASE;  // Needed whenever we touch a shadow ptr; different window.
delay0(2);
wr_ptr.cVal[3] = READ_VALUE(TX_WR_PTR(s));
wr_ptr.cVal[2] = READ_VALUE(TX_WR_PTR(s) + SA_OFFSET(1));
wr_ptr.cVal[1] = READ_VALUE(TX_WR_PTR(s) + SA_OFFSET(2));
wr_ptr.cVal[0] = READ_VALUE(TX_WR_PTR(s) + SA_OFFSET(3));

k = READ_VALUE(SHADOW_TXRD_PTR(s));
WINDOW_RESTORE_BASE;  // Needed whenever we touch a shadow ptr; different window.
delay0(2);
rd_ptr.cVal[3] = READ_VALUE(TX_RD_PTR(s));
rd_ptr.cVal[2] = READ_VALUE(TX_RD_PTR(s) + SA_OFFSET(1));
rd_ptr.cVal[1] = READ_VALUE(TX_RD_PTR(s) + SA_OFFSET(2));
rd_ptr.cVal[0] = READ_VALUE(TX_RD_PTR(s) + SA_OFFSET(3));
enable();

// Suppress compiler errors that k is not used
k = k;

//  Calculate free buffer size to send
if (wr_ptr.lVal >= rd_ptr.lVal)
  size = (u_int)(SSIZE[s] - (wr_ptr.lVal - rd_ptr.lVal));
else
  size = (u_int)(SSIZE[s] - (0 - rd_ptr.lVal + wr_ptr.lVal));

//  Recalulate after some delay because of error in pointer caluation
if (size > SSIZE[s])
  {
  delay_ms(1);
  goto S2_START;
  }

// Wait when previous sending has not finished yet and there's no free buffer
if (size == 0)
  {
  delay_ms(1);
  goto S2_START;

  }
else if (size < len)
  {
  len = size;
  }

// Calculate pointer to copy data pointer
offset =(UINT)(wr_ptr.lVal & SMASK[s]);

// copy data
write_data(s, buf, offset, len);

// Confirm previous send command
while (READ_VALUE(COMMAND(s)) & CSEND)
  {
  if(select(s, SEL_CONTROL)==SOCK_CLOSED)
    return -1;                  // Error
  }

// update tx_wr_ptr
wr_ptr.lVal = wr_ptr.lVal + len;
WRITE_VALUE(TX_WR_PTR(s), wr_ptr.cVal[3]);
WRITE_VALUE(TX_WR_PTR(s) + SA_OFFSET(1), wr_ptr.cVal[2]);
WRITE_VALUE(TX_WR_PTR(s) + SA_OFFSET(2), wr_ptr.cVal[1]);
WRITE_VALUE(TX_WR_PTR(s) + SA_OFFSET(3), wr_ptr.cVal[0]);

delay0(1);

// SEND
WRITE_VALUE(COMMAND(s), CSEND);

return(len);
}

/*
****************************************************************************************************
*             UDP data receiving function.
*
* Description : Function for receiving UDP and IP layer RAW mode data, and handling the data header.
* Arguments   : s    - channel number
*               buf  - Pointer where the data to be received is copied
*               len  - Size of the data to be received
*               addr - Peer IP address for receiving
*               port - Peer port number for receiving
* Returns     : Received data size
* Note        : API Function
****************************************************************************************************
*/
u_int recvfrom(SOCKET s, u_char far *buf, u_int len, u_char *addr, u_int *port)
{
struct _UDPHeader									// When receiving UDP data, header added by W3100A
  {
  union
	 {
	 struct
		{
		u_int size;
		u_char addr[4];
		u_int port;
		} header;
	 u_char stream[8];
    } u;
  } UDPHeader;

u_int ret;
union un_l2cval wr_ptr, rd_ptr;
u_long size;
u_char k;
unsigned int offset;

if(select(s,SEL_CONTROL)==SOCK_CLOSED)
  return -1;

disable();
k = READ_VALUE(SHADOW_RXWR_PTR(s));
WINDOW_RESTORE_BASE;  // Needed whenever we touch a shadow ptr; different window.
delay0(2);
wr_ptr.cVal[3] = READ_VALUE(RX_WR_PTR(s));
wr_ptr.cVal[2] = READ_VALUE(RX_WR_PTR(s) + SA_OFFSET(1));
wr_ptr.cVal[1] = READ_VALUE(RX_WR_PTR(s) + SA_OFFSET(2));
wr_ptr.cVal[0] = READ_VALUE(RX_WR_PTR(s) + SA_OFFSET(3));

k = READ_VALUE(SHADOW_RXRD_PTR(s));
WINDOW_RESTORE_BASE;  // Needed whenever we touch a shadow ptr; different window.
delay0(2);
rd_ptr.cVal[3] = READ_VALUE(RX_RD_PTR(s));
rd_ptr.cVal[2] = READ_VALUE(RX_RD_PTR(s) + SA_OFFSET(1));
rd_ptr.cVal[1] = READ_VALUE(RX_RD_PTR(s) + SA_OFFSET(2));
rd_ptr.cVal[0] = READ_VALUE(RX_RD_PTR(s) + SA_OFFSET(3));
enable();

// Suppress compiler errors that k is not used
k = k;

// Calculate received data size
if (len <= 0)
  return (0);
else if (wr_ptr.lVal >= rd_ptr.lVal)
  size = wr_ptr.lVal - rd_ptr.lVal;
else
  size = 0 - rd_ptr.lVal + wr_ptr.lVal;

if (size == 0)
  return 0;

  // Calulate received data pointer
offset = ((UINT)(rd_ptr.lVal & RMASK[s]));

// When UDP data
if (( READ_VALUE(OPT_PROTOCOL(s)) & 0x07) == SOCK_DGRAM)
  {
  // Copy W3100A UDP header
  read_data(s, offset, UDPHeader.u.stream, 8);

  // Read UDP Packet size
  size = UDPHeader.u.stream[0];
  size = (size << 8) + UDPHeader.u.stream[1];

  // Read IP address of the peer
  addr[0] = UDPHeader.u.header.addr[0];
  addr[1] = UDPHeader.u.header.addr[1];
  addr[2] = UDPHeader.u.header.addr[2];
  addr[3] = UDPHeader.u.header.addr[3];

  // Read Port number of the peer
  *port = UDPHeader.u.stream[6];
  *port = (*port << 8) + UDPHeader.u.stream[7];

  // Increase read pointer by 8, because already read as UDP header size
  rd_ptr.lVal += 8;

  // Calculate UDP data copy pointer
  offset = ((UINT)(rd_ptr.lVal & RMASK[s]));

  // Calculate data size of current UDP Packet from UDP header
  size = size - 8;

  // Copy one UDP data packet to user-specific buffer
  ret = read_data(s, offset, buf, (u_int)size);

  // Increase read pointer by UDP packet data size
  rd_ptr.lVal += ret;
  }
else if ((READ_VALUE(OPT_PROTOCOL(s)) & 0x07) == SOCK_IPL_RAW)	 // When IP layer RAW mode data
  {
  // Copy W3100A IP Raw header
  read_data(s, offset, UDPHeader.u.stream, 6);

  // Read IP layer RAW Packet size
  size = UDPHeader.u.stream[0];
  size = (size << 8) + UDPHeader.u.stream[1];

  // Read IP address of the peer
  addr[0] = UDPHeader.u.header.addr[0];
  addr[1] = UDPHeader.u.header.addr[1];
  addr[2] = UDPHeader.u.header.addr[2];
  addr[3] = UDPHeader.u.header.addr[3];

  // Increase read pointer by 6, because already read as IP RAW header size
  rd_ptr.lVal += 6;

  // Calculate IP layer raw mode data pointer
  offset = ((UINT)(rd_ptr.lVal & RMASK[s]));

  // Copy one IP Raw data packet to user-specific buffer
  ret = read_data(s, offset, buf, (u_int)size);
  rd_ptr.lVal = rd_ptr.lVal + (ret - 4);
  }

  // Update rx_rd_ptr
  WRITE_VALUE(RX_RD_PTR(s), rd_ptr.cVal[3]);
  WRITE_VALUE(RX_RD_PTR(s) + SA_OFFSET(1), rd_ptr.cVal[2]);
  WRITE_VALUE(RX_RD_PTR(s) + SA_OFFSET(2), rd_ptr.cVal[1]);
  WRITE_VALUE(RX_RD_PTR(s) + SA_OFFSET(3), rd_ptr.cVal[0]);

  // RECV
  WRITE_VALUE(COMMAND(s), CRECV);

// Real received size return
return(ret);
}

/*
****************************************************************************************************
*              Channel closing function.
*
* Description : Function for closing the connection of the designated channel.
* Arguments   : s - channel number
* Returns     : None
* Note        : API Function
****************************************************************************************************
*/
void close(SOCKET s)
{
u_int len;

I_STATUS[s] = 0;

if (select(s, SEL_CONTROL) == SOCK_CLOSED)
  return;	   // Already closed

// When closing, if there's data which have not processed, Insert some source codes to handle this
// Or before application call close(), handle those data first and call close() later.

len = select(s, SEL_SEND);
if (len == SSIZE[s])
  {
  // CLOSE
  WRITE_VALUE(COMMAND(s), CCLOSE);
  // TODO: The 'SCLOSED' status value is only set briefly as part of the close,
  // and will otherwise quickly return to normal.  That means your code might
  // become 'stuck' at this point even if the packet has closed normally.
  // Rather than a while() call, it might be preferred to time out on this
  // close check and return to the application after some time.
  while(!(I_STATUS[s] & SCLOSED))
  	  I2CHIP_POLL_ISR(in4_isr_i2chip);
  }
}

u_char tx_empty(SOCKET s)
{
	return (select(s, SEL_SEND) == SSIZE[s]);
}

/*
****************************************************************************************************
*              Channel closing function.
*
* Description : Function for closing the connection of the designated channel.
* Arguments   : s - channel number
* Returns     : None
* Note        : API Function
****************************************************************************************************
*/
char reset_sock(SOCKET s)
{
u_char c;

c = 1 << s;

// RESET
WRITE_VALUE(RESETSOCK, c);
return	(1);
}

/*
****************************************************************************************************
*             Function handling the channel socket information.
*
* Description : Return socket information of designated channel
* Arguments   : s    - channel number
*               func - SEL_CONTROL(0x00) -> return socket status
*                      SEL_SEND(0x01)    -> return free transmit buffer size
*                      SEL_RECV(0x02)    -> return received data size
* Returns     : socket status or free transmit buffer size or received data size
* Note        : API Function
****************************************************************************************************
*/
u_int select(SOCKET s, u_char func)
{
u_int val;
union un_l2cval rd_ptr, wr_ptr, ack_ptr;
u_char k;

switch (func)
  {
  // socket status information
  case SEL_CONTROL :
	 val = READ_VALUE(SOCK_STATUS(s));
	 break;

  // Calculate send free buffer size
  case SEL_SEND :
	 disable();
	 k = READ_VALUE(SHADOW_TXWR_PTR(s));
	 WINDOW_RESTORE_BASE;  // Needed whenever we touch a shadow ptr; different window.
	 delay0(2);
	 wr_ptr.cVal[3] = READ_VALUE(TX_WR_PTR(s));
	 wr_ptr.cVal[2] = READ_VALUE(TX_WR_PTR(s) + SA_OFFSET(1));
	 wr_ptr.cVal[1] = READ_VALUE(TX_WR_PTR(s) + SA_OFFSET(2));
	 wr_ptr.cVal[0] = READ_VALUE(TX_WR_PTR(s) + SA_OFFSET(3));

	 if (( READ_VALUE(OPT_PROTOCOL(s)) & 0x07) == SOCK_STREAM)	// TCP
		{
		k = READ_VALUE(SHADOW_TXACK_PTR(s));
		WINDOW_RESTORE_BASE;  // Needed whenever we touch a shadow ptr; different window.
		delay0(2);
		ack_ptr.cVal[3] = READ_VALUE(TX_ACK_PTR(s));
		ack_ptr.cVal[2] = READ_VALUE(TX_ACK_PTR(s) + SA_OFFSET(1));
		ack_ptr.cVal[1] = READ_VALUE(TX_ACK_PTR(s) + SA_OFFSET(2));
		ack_ptr.cVal[0] = READ_VALUE(TX_ACK_PTR(s) + SA_OFFSET(3));
		enable();

		if (wr_ptr.lVal >= ack_ptr.lVal)
        val = (u_int)(SSIZE[s] - (wr_ptr.lVal - ack_ptr.lVal));
		else
        val = (u_int)(SSIZE[s] - (0 - ack_ptr.lVal + wr_ptr.lVal));
		}
	 else											// UDP, IP RAW ... (except TCP)
		{
		k = READ_VALUE(SHADOW_TXRD_PTR(s));
		WINDOW_RESTORE_BASE;  // Needed whenever we touch a shadow ptr; different window.
		delay0(2);
		rd_ptr.cVal[3] = READ_VALUE(TX_RD_PTR(s));
		rd_ptr.cVal[2] = READ_VALUE(TX_RD_PTR(s) + SA_OFFSET(1));
		rd_ptr.cVal[1] = READ_VALUE(TX_RD_PTR(s) + SA_OFFSET(2));
		rd_ptr.cVal[0] = READ_VALUE(TX_RD_PTR(s) + SA_OFFSET(3));
		enable();

		if (wr_ptr.lVal >= rd_ptr.lVal)
        val = (u_int)(SSIZE[s] - (wr_ptr.lVal - rd_ptr.lVal));
		else
        val = (u_int)(SSIZE[s] - (0 - rd_ptr.lVal + wr_ptr.lVal));
		}
	 break;

  //  Calculate received data size
  case SEL_RECV :
	 disable();
	 k = READ_VALUE(SHADOW_RXWR_PTR(s));
	 WINDOW_RESTORE_BASE;  // Needed whenever we touch a shadow ptr; different window.
	 delay0(2);
	 wr_ptr.cVal[3] = READ_VALUE(RX_WR_PTR(s));
	 wr_ptr.cVal[2] = READ_VALUE(RX_WR_PTR(s) + SA_OFFSET(1));
	 wr_ptr.cVal[1] = READ_VALUE(RX_WR_PTR(s) + SA_OFFSET(2));
	 wr_ptr.cVal[0] = READ_VALUE(RX_WR_PTR(s) + SA_OFFSET(3));

	 k = READ_VALUE(SHADOW_RXRD_PTR(s));
    WINDOW_RESTORE_BASE;  // Needed whenever we touch a shadow ptr; different window.
	 delay0(2);
	 rd_ptr.cVal[3] = READ_VALUE(RX_RD_PTR(s));
	 rd_ptr.cVal[2] = READ_VALUE(RX_RD_PTR(s) + SA_OFFSET(1));
	 rd_ptr.cVal[1] = READ_VALUE(RX_RD_PTR(s) + SA_OFFSET(2));
	 rd_ptr.cVal[0] = READ_VALUE(RX_RD_PTR(s) + SA_OFFSET(3));
	 enable();

	 if (wr_ptr.lVal == rd_ptr.lVal)
      val = 0;
	 else if (wr_ptr.lVal > rd_ptr.lVal)
      val = (u_int)(wr_ptr.lVal - rd_ptr.lVal);
	 else
      val = (u_int)(0 - rd_ptr.lVal + wr_ptr.lVal);
	 break;

  default :
	 val = -1;
	 break;
  }
// Suppress compiler errors that k is not used
k = k;
return(val);
}

//
//	unsigned char dma_read_i2chip (unsigned int i2_segm, unsigned int i2_offs,
//	unsigned int cnt, unsigned int des_segm, unsigned int des_offs);
//	Using DMA0 to read data from i2chip buffer into destination SRAM.
//	where:
//		unsigned int cnt = number of sectors, 512-byte per sector
//		unsigned int des_segm = segment of destination SRAM data memory
//		unsigned int des_offs = offset of destination SRAM data memory
//		unsigned int i2_segm = segment of i2chip buffer mapped in memory
//		unsigned int i2_offs = offset of i2chip buffer mapped in memory
//	 return DMA counter value
//
unsigned int dma_read_i2chip(u_char far* i2_src, u_char far* des, u_int cnt)
{
	u_int des_segm, des_offs;
   u_int i2_segm, i2_offs;
   u_long temp;

   temp = ((long)FP_SEG(des) << 4) + ((long)FP_OFF(des));
   des_segm = (u_int)(temp >> 16);
   des_offs = (u_int)(temp & 0xffff);

   temp = ((long)FP_SEG(i2_src) << 4) + ((long)FP_OFF(i2_src));
   i2_segm = (u_int)(temp >> 16);
   i2_offs = (u_int)(temp & 0xffff);

	outport(0xffc6, des_segm);   /* D0DSTH destination SRAM segment */
	outport(0xffc4, des_offs);   /* D0DSTL destination SRAM offset */
	outport(0xffc2, i2_segm);   /* D0SRCH=SP0RD */
	outport(0xffc0, i2_offs);   /* D0SRCL=SP0RD */
	outport(0xffc8, cnt);   // D0TC counter
	outport(0xfff8,0x0504);	// PLLCON, 0203=10M,050f=40M, 051f=80MHz
// DMA0 mem-mem, 16-bit, unsync, Start moving data line below
	outport(0xffca, 0xb60e);   /* D0CON 1011 0110 0000 1111 */
//	outport(0xffca, 0xb42e);         // 1011 0100 0010 1110
	while( inport(0xffc8) ); /* D0TC counter=0, DMA complete */
	outport(0xfff8,0x051f);	// PLLCON, 0203=10M,050f=40M, 051f=80MHz
return( inport(0xffc8) ); // counter
}

//
//	unsigned int dma_write_i2chip (unsigned int src_segm, unsigned int src_offs,
//	unsigned int cnt, unsigned int i2_segm, unsigned int i2_offs);
//	Using DMA0 to write data from memory into i2chip.
//	where:
//		unsigned int cnt = number of 16-bit DMA transfers
//		unsigned int src_segm = segment of the source SRAM data memory
//		unsigned int src_offs = offset of the source SRAM data memory
//		unsigned int i2_segm = segment of i2chip buffer mapped in memory
//		unsigned int i2_offs = offset of i2chip buffer mapped in memory
//	 return DMA counter value
//
unsigned int dma_write_i2chip(u_char far* src, u_char far* i2_dest, u_int cnt)
{
	u_int src_segm, src_offs;
   u_int i2_segm, i2_offs;
   u_long temp;

   temp = (FP_SEG(src) << 4) + (FP_OFF(src));
   src_segm = (u_int)(temp >> 4);
   src_offs = (u_int)(temp & 0xffff);

   temp = (FP_SEG(i2_dest) << 4) + (FP_OFF(i2_dest));
   i2_segm = (u_int)(temp >> 4);
   i2_offs = (u_int)(temp & 0xffff);

	outport(0xffc8, cnt);   // D0TC counter
	outport(0xffc6, i2_segm); // D0DSTH=i2chip buffer segment
	outport(0xffc4, i2_offs); // D0DSTL=i2chip buffer offset
	outport(0xffc2, src_segm);   /* D0SRCH=SP0RD */
	outport(0xffc0, src_offs);   /* D0SRCL=SP0RD */
//	outport(0xfff8,0x050f);	// PLLCON, 0203=10M,050f=40M, 051f=80MHz
// DMA0 mem-mem, 16-bit, unsync, Start moving data line below
	outport(0xffca, 0xb60f);   /* D0CON 1011 0110 0000 1111 */
	while( inport(0xffc8) ); /* D0TC counter=0, DMA complete */
//	outport(0xfff8,0x051f);	// PLLCON, 0203=10M,050f=40M, 051f=80MHz

return( inport(0xffc8) ); // counter
}

/*
****************************************************************************************************
*              Copies the receive buffer data of the W3100A to the system buffer.
*
* Description : Copies the receive buffer data of the W3100A to the system buffer.
*    It is called from the recv()or recvfrom() function.
* Arguments   : s   - channel number
*               src - receive buffer pointer of W3100A
*               dst - system buffer pointer
*               len - data size to copy
* Returns     : copied data size
* Note        : Internal Function
****************************************************************************************************
*/
u_int read_data(SOCKET s, u_int offset, u_char far * dst, u_int len)
{
	u_int i, size, size1;
   u_char far* src = (u_char far*)(MK_FP_WINDOW(RECV_DATA_BUF,
                                        RBUFBASEADDRESS[s] + offset));
//   src = (u_char far*)(MK_FP_WINDOW(RECV_DATA_BUF,
//                                        0));

	if (len == 0)
   {
   	WINDOW_RESTORE_BASE;    // Needed whenever we do a call to MK_FP_WINDOW.
  		return 0;
   }

   if ((offset + len) > RSIZE[s])
   {
		size = (u_int)(RSIZE[s] - offset);

  		if (size > TERN_RDMA_THRES)
  		{
  			dma_read_i2chip(src, dst, size);
  		}
  		else
      {
  	 		for (i = 0; i < size; i++)
    		{
 	 			*dst++ = READ_VALUE(src);
            WINDOW_PTR_INC(src);

	 		}
  		}

	  size1 = len - size;
     src = (u_char far *)(MK_FP_WINDOW(RECV_DATA_BUF, (RBUFBASEADDRESS[s])));

     if (size1 > TERN_RDMA_THRES)
     {
     		dma_read_i2chip(src, dst, size);
  	  }
     else
  	  {
  			for (i = 0; i < size1; i++)
   		{
	 			*dst++ = READ_VALUE(src);
            WINDOW_PTR_INC(src);
   		}
  		}
	}
   else
   {
	 if (len > TERN_RDMA_THRES)
    {
  		dma_read_i2chip(src, dst, size);
    }
    else
    {
  		for (i = 0; i < len; i++)
    	{
  	 		*dst++ = READ_VALUE(src);
         WINDOW_PTR_INC(src);
	 	}
    }
   }
   WINDOW_RESTORE_BASE;    // Needed whenever we do a call to MK_FP_WINDOW.
	return len;
}


/*
****************************************************************************************************
*              Copies the system buffer data to the transmit buffer of the W3100A.
*
* Description : Copies the system buffer data to the transmit buffer of the W3100A.
*               It is called from the send_in()or sendto_in() function.
* Arguments   : s   - channel number
*               src - system buffer pointer
*               dst - send buffer pointer of W3100A
*               len - data size to copy
* Returns     : copied data size
* Note        : Internal Function
****************************************************************************************************
*/
u_int write_data(SOCKET s, u_char far * src, u_int offset, u_int len)
{
	u_int i, size, size1;
	u_char far* dst = (u_char far*)MK_FP_WINDOW(SEND_DATA_BUF,
                                  SBUFBASEADDRESS[s] + offset);

	if (len == 0)
   {
   	WINDOW_RESTORE_BASE;    // Needed whenever we do a call to MK_FP_WINDOW.
  		return 0;
   }

	if ((offset + len) > SSIZE[s])
   {
		size = (u_int)(SSIZE[s] - offset);

  		for (i = 0; i < size; i++)
    	{
	 		WRITE_VALUE(dst, *src++);
         WINDOW_PTR_INC(dst);
	 	}

  		size1 = len - size;
  		dst = (u_char far *)(MK_FP_WINDOW(SEND_DATA_BUF, (SBUFBASEADDRESS[s])));

  		for (i = 0; i < size1; i++)
    	{
	 		WRITE_VALUE(dst, *src++);
         WINDOW_PTR_INC(dst);
	 	}
  }
  else
  {
  	for (i = 0; i < len; i++)
    	{
	 		WRITE_VALUE(dst, *src++);
         WINDOW_PTR_INC(dst);
	 	}
  	}
   WINDOW_RESTORE_BASE;    // Needed whenever we do a call to MK_FP_WINDOW.
	return len;
}



