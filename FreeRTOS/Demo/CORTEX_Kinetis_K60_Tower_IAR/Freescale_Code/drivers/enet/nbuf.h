// ----------------------------------------------------------------------
// File:		nbuf.h
// Purpose:		Definitions for Network Buffer Allocation.
// 
// Notes:		
// 
// ----------------------------------------------------------------------

#ifndef _NBUF_H_
#define _NBUF_H_

// Define number of MACs
#define NUM_CHANNELS 1/*b06862*/

// Choose Enhanced Buffer Descriptor or Legacy
#define ENHANCED_BD

//b06862: define Endianess for Little Endian architectures like ARM.
//Motorola/Freescale uses Big Endian or Register-Endianess
#define NBUF_LITTLE_ENDIAN

// Transmit packet directly or copy to dedicated buffers. If packets
// are not alligned dedicated Tx buffers can be used
//#define USE_DEDICATED_TX_BUFFERS

// Buffer sizes in bytes (must be divisible by 16)
#define RX_BUFFER_SIZE                                         256
#define TX_BUFFER_SIZE                                         256

// Number of Receive and Transmit Buffers and Buffer Descriptors
#define NUM_RXBDS 20//10
#define NUM_TXBDS 20//10

// Buffer Descriptor Format
#ifdef ENHANCED_BD
  typedef struct
  {
  	uint16_t status;	            /* control and status */
  	uint16_t length;	            /* transfer length */
  	uint8_t  *data;	                /* buffer address */
  	uint32_t ebd_status;
  	uint16_t length_proto_type;
  	uint16_t payload_checksum;
  	uint32_t bdu;
  	uint32_t timestamp;
  	uint32_t reserverd_word1;
  	uint32_t reserverd_word2;
  } NBUF;
#else
  typedef struct
  {
  	uint16_t status;	/* control and status */
  	uint16_t length;	/* transfer length */
  	uint8_t  *data;	    /* buffer address */
  } NBUF;
#endif /* ENHANCED_BD */

// ----------------------------------------------------------------------
// Function Declarations 
// ----------------------------------------------------------------------
void 
nbuf_alloc(int ch);
  
void 
nbuf_init(int);

void 
nbuf_start_rx(int);

void 
nbuf_flush(int);

//NM -  return value
void 
enet_get_received_packet(int, NBUF *);

//NM - return value
void 
enet_fill_txbds(int, NBUF *);

void 
enet_transmit_packet(int,NBUF *);

#ifdef NBUF_LITTLE_ENDIAN

//For Freescale ARM Architecture

// ----------------------------------------------------------------------
// TX Buffer Descriptor Bit Definitions
// ----------------------------------------------------------------------
#define TX_BD_R			0x0080
#define TX_BD_TO1		0x0040
#define TX_BD_W			0x0020
#define TX_BD_TO2		0x0010
#define TX_BD_L			0x0008
#define TX_BD_TC		0x0004
#define TX_BD_ABC		0x0002

// ----------------------------------------------------------------------
// TX Enhanced BD Bit Definitions
// ----------------------------------------------------------------------
#define TX_BD_INT       0x00000040 
#define TX_BD_TS        0x00000020 
#define TX_BD_PINS      0x00000010 
#define TX_BD_IINS      0x00000008 
#define TX_BD_TXE       0x00800000 
#define TX_BD_UE        0x00200000 
#define TX_BD_EE        0x00100000
#define TX_BD_FE        0x00080000 
#define TX_BD_LCE       0x00040000 
#define TX_BD_OE        0x00020000 
#define TX_BD_TSE       0x00010000 

#define TX_BD_BDU       0x00000080    

// ----------------------------------------------------------------------
// RX Buffer Descriptor Bit Definitions
// ----------------------------------------------------------------------

// Offset 0 flags - status: Big Endian
#define RX_BD_E			0x0080
#define RX_BD_R01		0x0040
#define RX_BD_W			0x0020
#define RX_BD_R02		0x0010
#define RX_BD_L			0x0008
#define RX_BD_M			0x0001
#define RX_BD_BC		0x8000
#define RX_BD_MC		0x4000
#define RX_BD_LG		0x2000
#define RX_BD_NO		0x1000
#define RX_BD_CR		0x0400
#define RX_BD_OV		0x0200
#define RX_BD_TR		0x0100

// ----------------------------------------------------------------------
// RX Enhanced BD Bit Definitions
// ----------------------------------------------------------------------
#define RX_BD_ME               0x00000080    
#define RX_BD_PE               0x00000004    
#define RX_BD_CE               0x00000002    
#define RX_BD_UC               0x00000001
    
#define RX_BD_INT              0x00008000    

#define RX_BD_ICE              0x20000000    
#define RX_BD_PCR              0x10000000    
#define RX_BD_VLAN             0x04000000    
#define RX_BD_IPV6             0x02000000    
#define RX_BD_FRAG             0x01000000    

#define RX_BD_BDU              0x00000080    

#else

//For Freescale ColdFire Architecture
// ----------------------------------------------------------------------
// TX Buffer Descriptor Bit Definitions
// ----------------------------------------------------------------------
#define TX_BD_R			0x8000
#define TX_BD_TO1		0x4000
#define TX_BD_W			0x2000
#define TX_BD_TO2		0x1000
#define TX_BD_L			0x0800
#define TX_BD_TC		0x0400
#define TX_BD_ABC		0x0200

// ----------------------------------------------------------------------
// TX Enhanced BD Bit Definitions
// ----------------------------------------------------------------------
#define TX_BD_INT       0x40000000 
#define TX_BD_TS        0x20000000 
#define TX_BD_PINS      0x10000000 
#define TX_BD_IINS      0x08000000 
#define TX_BD_TXE       0x00008000 
#define TX_BD_UE        0x00002000 
#define TX_BD_EE        0x00001000 
#define TX_BD_FE        0x00000800 
#define TX_BD_LCE       0x00000400 
#define TX_BD_OE        0x00000200 
#define TX_BD_TSE       0x00000100 

#define TX_BD_BDU       0x80000000    

// ----------------------------------------------------------------------
// RX Buffer Descriptor Bit Definitions
// ----------------------------------------------------------------------

// Offset 0 flags - status
#define RX_BD_E			0x8000
#define RX_BD_R01		0x4000
#define RX_BD_W			0x2000
#define RX_BD_R02		0x1000
#define RX_BD_L			0x0800
#define RX_BD_M			0x0100
#define RX_BD_BC		0x0080
#define RX_BD_MC		0x0040
#define RX_BD_LG		0x0020
#define RX_BD_NO		0x0010
#define RX_BD_CR		0x0004
#define RX_BD_OV		0x0002
#define RX_BD_TR		0x0001

// ----------------------------------------------------------------------
// RX Enhanced BD Bit Definitions
// ----------------------------------------------------------------------
#define RX_BD_ME               0x80000000    
#define RX_BD_PE               0x04000000    
#define RX_BD_CE               0x02000000    
#define RX_BD_UC               0x01000000    
#define RX_BD_INT              0x00800000    
#define RX_BD_ICE              0x00000020    
#define RX_BD_PCR              0x00000010    
#define RX_BD_VLAN             0x00000004    
#define RX_BD_IPV6             0x00000002    
#define RX_BD_FRAG             0x00000001    

#define RX_BD_BDU              0x80000000    


#endif

// ----------------------------------------------------------------------
// Defines for word offsets of various fields of RX Enhanced BDs
// ----------------------------------------------------------------------
//#define RX_EBD_HEADER_LENGTH_OFFSET    12
//#define RX_EBD_PROTOCOL_TYPE_OFFSET    12
//#define RX_EBD_PAYLOAD_CHKSM_OFFSET    14
//#define RX_EBD_BDU_OFFSET              16
//#define RX_EBD_TIMESTAMP_MSB_OFFSET    20
//#define RX_EBD_TIMESTAMP_LSB_OFFSET    22


#endif 	/* _NBUF_H_ */
