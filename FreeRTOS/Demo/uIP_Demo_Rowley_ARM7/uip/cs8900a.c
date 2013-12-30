// cs8900a.c: device driver for the CS8900a chip in 8-bit mode.

#include <LPC210x.h>

#include "cs8900a.h"
#include "uip.h"
#include "uip_arp.h"

#define IOR                  (1<<12)          // CS8900's ISA-bus interface pins
#define IOW                  (1<<13)

// definitions for Crystal CS8900 ethernet-controller
// based on linux-header by Russel Nelson

#define PP_ChipID            0x0000          // offset 0h -> Corp-ID

											 // offset 2h -> Model/Product Number
#define LED_RED (1<<8)
#define LED_GREEN (1<<10)
#define LED_YELLOW (1<<11)

#define PP_ISAIOB            0x0020          // IO base address
#define PP_CS8900_ISAINT     0x0022          // ISA interrupt select
#define PP_CS8900_ISADMA     0x0024          // ISA Rec DMA channel
#define PP_ISASOF            0x0026          // ISA DMA offset
#define PP_DmaFrameCnt       0x0028          // ISA DMA Frame count
#define PP_DmaByteCnt        0x002A          // ISA DMA Byte count
#define PP_CS8900_ISAMemB    0x002C          // Memory base
#define PP_ISABootBase       0x0030          // Boot Prom base
#define PP_ISABootMask       0x0034          // Boot Prom Mask

// EEPROM data and command registers
#define PP_EECMD             0x0040          // NVR Interface Command register
#define PP_EEData            0x0042          // NVR Interface Data Register

// Configuration and control registers
#define PP_RxCFG             0x0102          // Rx Bus config
#define PP_RxCTL             0x0104          // Receive Control Register
#define PP_TxCFG             0x0106          // Transmit Config Register
#define PP_TxCMD             0x0108          // Transmit Command Register
#define PP_BufCFG            0x010A          // Bus configuration Register
#define PP_LineCTL           0x0112          // Line Config Register
#define PP_SelfCTL           0x0114          // Self Command Register
#define PP_BusCTL            0x0116          // ISA bus control Register
#define PP_TestCTL           0x0118          // Test Register

// Status and Event Registers
#define PP_ISQ               0x0120          // Interrupt Status
#define PP_RxEvent           0x0124          // Rx Event Register
#define PP_TxEvent           0x0128          // Tx Event Register
#define PP_BufEvent          0x012C          // Bus Event Register
#define PP_RxMiss            0x0130          // Receive Miss Count
#define PP_TxCol             0x0132          // Transmit Collision Count
#define PP_LineST            0x0134          // Line State Register
#define PP_SelfST            0x0136          // Self State register
#define PP_BusST             0x0138          // Bus Status
#define PP_TDR               0x013C          // Time Domain Reflectometry

// Initiate Transmit Registers
#define PP_TxCommand         0x0144          // Tx Command
#define PP_TxLength          0x0146          // Tx Length

// Adress Filter Registers
#define PP_LAF               0x0150          // Hash Table
#define PP_IA                0x0158          // Physical Address Register

// Frame Location
#define PP_RxStatus          0x0400          // Receive start of frame
#define PP_RxLength          0x0402          // Receive Length of frame
#define PP_RxFrame           0x0404          // Receive frame pointer
#define PP_TxFrame           0x0A00          // Transmit frame pointer

// Primary I/O Base Address. If no I/O base is supplied by the user, then this
// can be used as the default I/O base to access the PacketPage Area.
#define DEFAULTIOBASE        0x0300

// PP_RxCFG - Receive  Configuration and Interrupt Mask bit definition - Read/write
#define SKIP_1               0x0040
#define RX_STREAM_ENBL       0x0080
#define RX_OK_ENBL           0x0100
#define RX_DMA_ONLY          0x0200
#define AUTO_RX_DMA          0x0400
#define BUFFER_CRC           0x0800
#define RX_CRC_ERROR_ENBL    0x1000
#define RX_RUNT_ENBL         0x2000
#define RX_EXTRA_DATA_ENBL   0x4000

// PP_RxCTL - Receive Control bit definition - Read/write
#define RX_IA_HASH_ACCEPT    0x0040
#define RX_PROM_ACCEPT       0x0080
#define RX_OK_ACCEPT         0x0100
#define RX_MULTCAST_ACCEPT   0x0200
#define RX_IA_ACCEPT         0x0400
#define RX_BROADCAST_ACCEPT  0x0800
#define RX_BAD_CRC_ACCEPT    0x1000
#define RX_RUNT_ACCEPT       0x2000
#define RX_EXTRA_DATA_ACCEPT 0x4000

// PP_TxCFG - Transmit Configuration Interrupt Mask bit definition - Read/write
#define TX_LOST_CRS_ENBL     0x0040
#define TX_SQE_ERROR_ENBL    0x0080
#define TX_OK_ENBL           0x0100
#define TX_LATE_COL_ENBL     0x0200
#define TX_JBR_ENBL          0x0400
#define TX_ANY_COL_ENBL      0x0800
#define TX_16_COL_ENBL       0x8000

// PP_TxCMD - Transmit Command bit definition - Read-only and
// PP_TxCommand - Write-only
#define TX_START_5_BYTES     0x0000
#define TX_START_381_BYTES   0x0040
#define TX_START_1021_BYTES  0x0080
#define TX_START_ALL_BYTES   0x00C0
#define TX_FORCE             0x0100
#define TX_ONE_COL           0x0200
#define TX_NO_CRC            0x1000
#define TX_RUNT              0x2000

// PP_BufCFG - Buffer Configuration Interrupt Mask bit definition - Read/write
#define GENERATE_SW_INTERRUPT      0x0040
#define RX_DMA_ENBL                0x0080
#define READY_FOR_TX_ENBL          0x0100
#define TX_UNDERRUN_ENBL           0x0200
#define RX_MISS_ENBL               0x0400
#define RX_128_BYTE_ENBL           0x0800
#define TX_COL_COUNT_OVRFLOW_ENBL  0x1000
#define RX_MISS_COUNT_OVRFLOW_ENBL 0x2000
#define RX_DEST_MATCH_ENBL         0x8000

// PP_LineCTL - Line Control bit definition - Read/write
#define SERIAL_RX_ON         0x0040
#define SERIAL_TX_ON         0x0080
#define AUI_ONLY             0x0100
#define AUTO_AUI_10BASET     0x0200
#define MODIFIED_BACKOFF     0x0800
#define NO_AUTO_POLARITY     0x1000
#define TWO_PART_DEFDIS      0x2000
#define LOW_RX_SQUELCH       0x4000

// PP_SelfCTL - Software Self Control bit definition - Read/write
#define POWER_ON_RESET       0x0040
#define SW_STOP              0x0100
#define SLEEP_ON             0x0200
#define AUTO_WAKEUP          0x0400
#define HCB0_ENBL            0x1000
#define HCB1_ENBL            0x2000
#define HCB0                 0x4000
#define HCB1                 0x8000

// PP_BusCTL - ISA Bus Control bit definition - Read/write
#define RESET_RX_DMA         0x0040
#define MEMORY_ON            0x0400
#define DMA_BURST_MODE       0x0800
#define IO_CHANNEL_READY_ON  0x1000
#define RX_DMA_SIZE_64K      0x2000
#define ENABLE_IRQ           0x8000

// PP_TestCTL - Test Control bit definition - Read/write
#define LINK_OFF             0x0080
#define ENDEC_LOOPBACK       0x0200
#define AUI_LOOPBACK         0x0400
#define BACKOFF_OFF          0x0800
#define FDX_8900             0x4000

// PP_RxEvent - Receive Event Bit definition - Read-only
#define RX_IA_HASHED         0x0040
#define RX_DRIBBLE           0x0080
#define RX_OK                0x0100
#define RX_HASHED            0x0200
#define RX_IA                0x0400
#define RX_BROADCAST         0x0800
#define RX_CRC_ERROR         0x1000
#define RX_RUNT              0x2000
#define RX_EXTRA_DATA        0x4000
#define HASH_INDEX_MASK      0xFC00          // Hash-Table Index Mask (6 Bit)

// PP_TxEvent - Transmit Event Bit definition - Read-only
#define TX_LOST_CRS          0x0040
#define TX_SQE_ERROR         0x0080
#define TX_OK                0x0100
#define TX_LATE_COL          0x0200
#define TX_JBR               0x0400
#define TX_16_COL            0x8000
#define TX_COL_COUNT_MASK    0x7800

// PP_BufEvent - Buffer Event Bit definition - Read-only
#define SW_INTERRUPT         0x0040
#define RX_DMA               0x0080
#define READY_FOR_TX         0x0100
#define TX_UNDERRUN          0x0200
#define RX_MISS              0x0400
#define RX_128_BYTE          0x0800
#define TX_COL_OVRFLW        0x1000
#define RX_MISS_OVRFLW       0x2000
#define RX_DEST_MATCH        0x8000

// PP_LineST - Ethernet Line Status bit definition - Read-only
#define LINK_OK              0x0080
#define AUI_ON               0x0100
#define TENBASET_ON          0x0200
#define POLARITY_OK          0x1000
#define CRS_OK               0x4000

// PP_SelfST - Chip Software Status bit definition
#define ACTIVE_33V           0x0040
#define INIT_DONE            0x0080
#define SI_BUSY              0x0100
#define EEPROM_PRESENT       0x0200
#define EEPROM_OK            0x0400
#define EL_PRESENT           0x0800
#define EE_SIZE_64           0x1000

// PP_BusST - ISA Bus Status bit definition
#define TX_BID_ERROR         0x0080
#define READY_FOR_TX_NOW     0x0100

// The following block defines the ISQ event types
#define ISQ_RX_EVENT         0x0004
#define ISQ_TX_EVENT         0x0008
#define ISQ_BUFFER_EVENT     0x000C
#define ISQ_RX_MISS_EVENT    0x0010
#define ISQ_TX_COL_EVENT     0x0012

#define ISQ_EVENT_MASK       0x003F          // ISQ mask to find out type of event

// Ports for I/O-Mode
#define RX_FRAME_PORT        0x0000
#define TX_FRAME_PORT        0x0000
#define TX_CMD_PORT          0x0004
#define TX_LEN_PORT          0x0006
#define ISQ_PORT             0x0008
#define ADD_PORT             0x000A
#define DATA_PORT            0x000C

#define AUTOINCREMENT        0x8000          // Bit mask to set Bit-15 for autoincrement

// EEProm Commands
#define EEPROM_WRITE_EN      0x00F0
#define EEPROM_WRITE_DIS     0x0000
#define EEPROM_WRITE_CMD     0x0100
#define EEPROM_READ_CMD      0x0200

// Receive Header of each packet in receive area of memory for DMA-Mode
#define RBUF_EVENT_LOW       0x0000          // Low byte of RxEvent
#define RBUF_EVENT_HIGH      0x0001          // High byte of RxEvent
#define RBUF_LEN_LOW         0x0002          // Length of received data - low byte
#define RBUF_LEN_HI          0x0003          // Length of received data - high byte
#define RBUF_HEAD_LEN        0x0004          // Length of this header

// typedefs
typedef struct {                             // struct to store CS8900's
  unsigned int Addr;                         // init-sequence
  unsigned int Data;
} TInitSeq;

unsigned short ticks;

static void skip_frame(void);

const TInitSeq InitSeq[] =
{
  PP_IA,       UIP_ETHADDR0 + (UIP_ETHADDR1 << 8),     // set our MAC as Individual Address
  PP_IA + 2,   UIP_ETHADDR2 + (UIP_ETHADDR3 << 8),
  PP_IA + 4,   UIP_ETHADDR4 + (UIP_ETHADDR5 << 8),
  PP_LineCTL,  SERIAL_RX_ON | SERIAL_TX_ON,           // configure the Physical Interface
  PP_RxCTL,    RX_OK_ACCEPT | RX_IA_ACCEPT | RX_BROADCAST_ACCEPT
};

// Writes a word in little-endian byte order to a specified port-address
void
cs8900a_write(unsigned addr, unsigned int data)
{
  GPIO_IODIR |= 0xff << 16;                           // Data port to output

  GPIO_IOCLR = 0xf << 4;                              // Put address on bus
  GPIO_IOSET = addr << 4;

  GPIO_IOCLR = 0xff << 16;                            // Write low order byte to data bus
  GPIO_IOSET = data << 16;

  __asm volatile ( "NOP" );
  GPIO_IOCLR = IOW;                                   // Toggle IOW-signal
  __asm volatile ( "NOP" );
  GPIO_IOSET = IOW;
  __asm volatile ( "NOP" );

  GPIO_IOCLR = 0xf << 4;
  GPIO_IOSET = ((addr | 1) << 4);                     // And put next address on bus

  GPIO_IOCLR = 0xff << 16;                            // Write high order byte to data bus
  GPIO_IOSET = data >> 8 << 16;

  __asm volatile ( "NOP" );
  GPIO_IOCLR = IOW;                                   // Toggle IOW-signal
  __asm volatile ( "NOP" );
  GPIO_IOSET = IOW;
  __asm volatile ( "NOP" );
}

// Reads a word in little-endian byte order from a specified port-address
unsigned
cs8900a_read(unsigned addr)
{
  unsigned int value;

  GPIO_IODIR &= ~(0xff << 16);                        // Data port to input

  GPIO_IOCLR = 0xf << 4;                              // Put address on bus
  GPIO_IOSET = addr << 4;

  __asm volatile ( "NOP" );
  GPIO_IOCLR = IOR;                                   // IOR-signal low
  __asm volatile ( "NOP" );
  value = (GPIO_IOPIN >> 16) & 0xff;                  // get low order byte from data bus
  GPIO_IOSET = IOR;

  GPIO_IOSET = 1 << 4;                                // IOR high and put next address on bus

  __asm volatile ( "NOP" );
  GPIO_IOCLR = IOR;                                   // IOR-signal low
  __asm volatile ( "NOP" );
  value |= ((GPIO_IOPIN >> 8) & 0xff00);              // get high order byte from data bus
  GPIO_IOSET = IOR;                                   // IOR-signal low

  return value;
}

// Reads a word in little-endian byte order from a specified port-address
unsigned
cs8900a_read_addr_high_first(unsigned addr)
{
  unsigned int value;

  GPIO_IODIR &= ~(0xff << 16);                        // Data port to input

  GPIO_IOCLR = 0xf << 4;                              // Put address on bus
  GPIO_IOSET = (addr+1) << 4;

  __asm volatile ( "NOP" );
  GPIO_IOCLR = IOR;                                   // IOR-signal low
  __asm volatile ( "NOP" );
  value = ((GPIO_IOPIN >> 8) & 0xff00);               // get high order byte from data bus
  GPIO_IOSET = IOR;                                   // IOR-signal high

  GPIO_IOCLR = 1 << 4;                                // Put low address on bus

  __asm volatile ( "NOP" );
  GPIO_IOCLR = IOR;                                   // IOR-signal low
  __asm volatile ( "NOP" );
  value |= (GPIO_IOPIN >> 16) & 0xff;                 // get low order byte from data bus
  GPIO_IOSET = IOR;

  return value;
}

void
cs8900a_init(void)
{
  int i;

  // Reset outputs, control lines high
  GPIO_IOSET = IOR | IOW;

  // No LEDs on.
  GPIO_IOSET = LED_RED | LED_YELLOW | LED_GREEN;

  // Port 3 as output (all pins but RS232)
  GPIO_IODIR = ~0U; // everything to output.

  // Reset outputs
  GPIO_IOCLR = 0xff << 16;  // clear data outputs

  // Reset the CS8900A
  cs8900a_write(ADD_PORT, PP_SelfCTL);
  cs8900a_write(DATA_PORT, POWER_ON_RESET);

  // Wait until chip-reset is done
  cs8900a_write(ADD_PORT, PP_SelfST);
  while ((cs8900a_read(DATA_PORT) & INIT_DONE) == 0)
    ;

  // Configure the CS8900A
  for (i = 0; i < sizeof InitSeq / sizeof (TInitSeq); ++i)
    {
      cs8900a_write(ADD_PORT, InitSeq[i].Addr);
      cs8900a_write(DATA_PORT, InitSeq[i].Data);
    }
}

void
cs8900a_send(void)
{
  unsigned u;

  GPIO_IOCLR = LED_RED;  // Light RED LED when frame starting

  // Transmit command
  cs8900a_write(TX_CMD_PORT, TX_START_ALL_BYTES);
  cs8900a_write(TX_LEN_PORT, uip_len);

  // Maximum number of retries
  u = 8;
  for (;;)
    {
      // Check for avaliable buffer space
      cs8900a_write(ADD_PORT, PP_BusST);
      if (cs8900a_read(DATA_PORT) & READY_FOR_TX_NOW)
        break;
      if (u -- == 0)
        {
          GPIO_IOSET = LED_RED;  // Extinguish RED LED on end of frame
          return;
        }

      // No space avaliable, skip a received frame and try again
      skip_frame();
    }

  GPIO_IODIR |= 0xff << 16;                           // Data port to output

  // Send 40+14=54 bytes of header
  for (u = 0; u < 54; u += 2)
    {
      GPIO_IOCLR = 0xf << 4;                              // Put address on bus
      GPIO_IOSET = TX_FRAME_PORT << 4;

      GPIO_IOCLR = 0xff << 16;                            // Write low order byte to data bus
      GPIO_IOSET = uip_buf[u] << 16;                      // write low order byte to data bus

      __asm volatile ( "NOP" );
      GPIO_IOCLR = IOW;                                   // Toggle IOW-signal
      __asm volatile ( "NOP" );
      GPIO_IOSET = IOW;

      GPIO_IOCLR = 0xf << 4;                              // Put address on bus
      GPIO_IOSET = (TX_FRAME_PORT | 1) << 4;              // and put next address on bus

      GPIO_IOCLR = 0xff << 16;                            // Write low order byte to data bus
      GPIO_IOSET = uip_buf[u+1] << 16;                    // write low order byte to data bus

      __asm volatile ( "NOP" );
	  GPIO_IOCLR = IOW;                                   // Toggle IOW-signal
      __asm volatile ( "NOP" );
      GPIO_IOSET = IOW;
    }

  if (uip_len <= 54)
    {
      GPIO_IOSET = LED_RED;  // Extinguish RED LED on end of frame
      return;
    }

  // Send remainder of packet, the application data
  uip_len -= 54;
  for (u = 0; u < uip_len; u += 2)
    {

      GPIO_IOCLR = 0xf << 4;                          // Put address on bus
      GPIO_IOSET = TX_FRAME_PORT << 4;

      GPIO_IOCLR = 0xff << 16;                        // Write low order byte to data bus
      GPIO_IOSET = uip_appdata[u] << 16;              // write low order byte to data bus

      __asm volatile ( "NOP" );
	  GPIO_IOCLR = IOW;                               // Toggle IOW-signal
      __asm volatile ( "NOP" );
      GPIO_IOSET = IOW;

      GPIO_IOCLR = 0xf << 4;                          // Put address on bus
      GPIO_IOSET = (TX_FRAME_PORT | 1) << 4;          // and put next address on bus

      GPIO_IOCLR = 0xff << 16;                        // Write low order byte to data bus
      GPIO_IOSET = uip_appdata[u+1] << 16;            // write low order byte to data bus

      __asm volatile ( "NOP" );
	  GPIO_IOCLR = IOW;                               // Toggle IOW-signal
      __asm volatile ( "NOP" );
      GPIO_IOSET = IOW;
    }

  GPIO_IOSET = LED_RED;  // Extinguish RED LED on end of frame
}

static void
skip_frame(void)
{
  // No space avaliable, skip a received frame and try again
  cs8900a_write(ADD_PORT, PP_RxCFG);
  cs8900a_write(DATA_PORT, cs8900a_read(DATA_PORT) | SKIP_1);
}

u8_t
cs8900a_poll(void)
{
  u16_t len, u;

  // Check receiver event register to see if there are any valid frames avaliable
  cs8900a_write(ADD_PORT, PP_RxEvent);
  if ((cs8900a_read(DATA_PORT) & 0xd00) == 0)
    return 0;

  GPIO_IOCLR = LED_GREEN;  // Light GREED LED when frame coming in.

  // Read receiver status and discard it.
  cs8900a_read_addr_high_first(RX_FRAME_PORT);

  // Read frame length
  len = cs8900a_read_addr_high_first(RX_FRAME_PORT);

  // If the frame is too big to handle, throw it away
  if (len > UIP_BUFSIZE)
    {
      skip_frame();
      return 0;
    }

  // Data port to input
  GPIO_IODIR &= ~(0xff << 16);

  GPIO_IOCLR = 0xf << 4;                          // put address on bus
  GPIO_IOSET = RX_FRAME_PORT << 4;

  // Read bytes into uip_buf
  u = 0;
  while (u < len)
    {
      GPIO_IOCLR = 1 << 4;                            // put address on bus

      GPIO_IOCLR = IOR;                               // IOR-signal low
      uip_buf[u] = GPIO_IOPIN >> 16;                // get high order byte from data bus
      __asm volatile ( "NOP" );
      GPIO_IOSET = IOR;                               // IOR-signal high

      GPIO_IOSET = 1 << 4;                            // put address on bus

      GPIO_IOCLR = IOR;                               // IOR-signal low
      __asm volatile ( "NOP" );
      uip_buf[u+1] = GPIO_IOPIN >> 16;                  // get high order byte from data bus
      GPIO_IOSET = IOR;                               // IOR-signal high
      u += 2;
    }

  GPIO_IOSET = LED_GREEN;  // Extinguish GREED LED when frame finished.
  return len;
}

