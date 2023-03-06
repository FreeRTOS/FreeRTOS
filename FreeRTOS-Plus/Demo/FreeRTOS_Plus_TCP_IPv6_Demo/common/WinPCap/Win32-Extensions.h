 /*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */


#ifndef __WIN32_EXTENSIONS_H__
    #define __WIN32_EXTENSIONS_H__

    #ifdef __cplusplus
        extern "C" {
    #endif

/* Definitions */

/*!
 * \brief A queue of raw packets that will be sent to the network with pcap_sendqueue_transmit().
 */
    struct pcap_send_queue
    {
        u_int maxlen;  /*/< Maximum size of the the queue, in bytes. This variable contains the size of the buffer field. */
        u_int len;     /*/< Current size of the queue, in bytes. */
        char * buffer; /*/< Buffer containing the packets to be sent. */
    };

    typedef struct pcap_send_queue      pcap_send_queue;

/*!
 * \brief This typedef is a support for the pcap_get_airpcap_handle() function
 */
    #if !defined( AIRPCAP_HANDLE__EAE405F5_0171_9592_B3C2_C19EC426AD34__DEFINED_ )
        #define AIRPCAP_HANDLE__EAE405F5_0171_9592_B3C2_C19EC426AD34__DEFINED_
        typedef struct _AirpcapHandle   * PAirpcapHandle;
    #endif

    #define     BPF_MEM_EX_IMM            0xc0
    #define     BPF_MEM_EX_IND            0xe0

/*used for ST*/
    #define     BPF_MEM_EX                0xc0
    #define     BPF_TME                   0x08

    #define     BPF_LOOKUP                0x90
    #define     BPF_EXECUTE               0xa0
    #define     BPF_INIT                  0xb0
    #define     BPF_VALIDATE              0xc0
    #define     BPF_SET_ACTIVE            0xd0
    #define     BPF_RESET                 0xe0
    #define     BPF_SET_MEMORY            0x80
    #define     BPF_GET_REGISTER_VALUE    0x70
    #define     BPF_SET_REGISTER_VALUE    0x60
    #define     BPF_SET_WORKING           0x50
    #define     BPF_SET_ACTIVE_READ       0x40
    #define     BPF_SET_AUTODELETION      0x30
    #define     BPF_SEPARATION            0xff

/* Prototypes */
    pcap_send_queue * pcap_sendqueue_alloc( u_int memsize );

    void pcap_sendqueue_destroy( pcap_send_queue * queue );

    int pcap_sendqueue_queue( pcap_send_queue * queue,
                              const struct pcap_pkthdr * pkt_header,
                              const u_char * pkt_data );

    u_int pcap_sendqueue_transmit( pcap_t * p,
                                   pcap_send_queue * queue,
                                   int sync );

    HANDLE pcap_getevent( pcap_t * p );

    struct pcap_stat * pcap_stats_ex( pcap_t * p,
                                      int * pcap_stat_size );

    int pcap_setuserbuffer( pcap_t * p,
                            int size );

    int pcap_live_dump( pcap_t * p,
                        char * filename,
                        int maxsize,
                        int maxpacks );

    int pcap_live_dump_ended( pcap_t * p,
                              int sync );

    int pcap_offline_filter( struct bpf_program * prog,
                             const struct pcap_pkthdr * header,
                             const u_char * pkt_data );

    int pcap_start_oem( char * err_str,
                        int flags );

    PAirpcapHandle pcap_get_airpcap_handle( pcap_t * p );

    #ifdef __cplusplus
        }
    #endif

#endif /*__WIN32_EXTENSIONS_H__ */
