tcp_dump_packets.c dumps network packets in a C source file.

It is written to be added to the "pc" project ( Windows simulator ). It uses the file system to write 2 C source files:

    PacketList.c
    PacketList.h

How to include 'tcp_dump_packets' into a project:

● Make sure that tools/tcp_dump_packets.c is added to the source files
● See if Network Interface has been adapted to call:
    `iptraceDUMP_PACKET( ucBuffer, xLength, pdTRUE );     /* Incoming packet. */`
    `iptraceDUMP_PACKET( ucBuffer, xLength, pdFALSE );    /* Outgoing packet. */`
● Once the network is up, call `dump_packet_init()` with a file name and a pointer to
  `DumpEntries_t`, which contains the requirements. For instance like this:
   static DumpEntries_t xExampleEntries = {
       .uxEntryCount = 4,	/* No more than 'dumpMAX_DUMP_ENTRIES' elements. */
       .xEntries = {
           { .ulMask = flag_IN | flag_UDP,   .uxMax = 2u },
           { .ulMask = flag_IN | flag_ARP,   .uxMax = 2u },
           { .ulMask = flag_IN | flag_TCP,   .uxMax = 5u },
           { .ulMask = flag_IN | flag_SYN,   .uxMax = 1u },
       }
   };
● Add the following lines to FreeRTOSIPConfig.h :
    #define ipconfigUSE_DUMP_PACKETS                    ( 1 )
    #include "../tools/tcp_dump_packets.h"

Later on, the module can disabled by simply setting `ipconfigUSE_DUMP_PACKETS` to `0`.

Here is some contents of the output file:

    /* Packet_0001 */
    uint8_t ucPacket_0001[ 60 ] =
    {
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x74, 0xb5, 0x7e, 0xf0, 0x47, 0xee, 0x08, 0x06, 0x00, 0x01,
        0x08, 0x00, 0x06, 0x04, 0x00, 0x01, 0x74, 0xb5, 0x7e, 0xf0, 0x47, 0xee, 0xc0, 0xa8, 0x02, 0x01,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc0, 0xa8, 0x02, 0x0e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
    };

    DumpPacket_t xPacket_0001 =
    {
        .pucData = ucPacket_0001,
        .uxLength = 60,
        .ulType = 0x6840, /* IN | FRAME_ARP | ARP | REQUEST */
    };
    /*-----------------------------------------------------------*/

tcp_dump_packets has an enum of all possible properties of network packets:
    ICMP4, ICMP6, UDP, TCP, DNS, REPLY, REQUEST, SYN, 
    FIN, RST, ACK, IN, OUT, ARP, FRAME_ARP, FRAME_4, and FRAME_6

Each property is defined as a bit so they can be combined as in:
    .ulType = 0x6840, /* IN | FRAME_ARP | ARP | REQUEST */

Finishing: when there are enough packets of all required types, an array is added to the C-source output:

    DumpPacket_t *xPacketList[ dumpPACKET_COUNT ] =
    {
        &xPacket_0000,
        &xPacket_0001,
        &xPacket_0002,
        &xPacket_0003,
        &xPacket_0004,
        &xPacket_0005,
        &xPacket_0006,
        &xPacket_0007,
        &xPacket_0008,
    };

The new source file PacketList.{c, h} can be used in testing software as sample packets.
