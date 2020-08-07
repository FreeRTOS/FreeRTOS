/**************************************************************************//**
 * @copyright (C) 2019 Nuvoton Technology Corp. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *   1. Redistributions of source code must retain the above copyright notice,
 *      this list of conditions and the following disclaimer.
 *   2. Redistributions in binary form must reproduce the above copyright notice,
 *      this list of conditions and the following disclaimer in the documentation
 *      and/or other materials provided with the distribution.
 *   3. Neither the name of Nuvoton Technology Corp. nor the names of its contributors
 *      may be used to endorse or promote products derived from this software
 *      without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*****************************************************************************/
#include "M480.h"
#ifndef  _M480_ETH_
#define  _M480_ETH_

/* Generic MII registers. */

#define MII_BMCR            0x00        /* Basic mode control register */
#define MII_BMSR            0x01        /* Basic mode status register  */
#define MII_PHYSID1         0x02        /* PHYS ID 1                   */
#define MII_PHYSID2         0x03        /* PHYS ID 2                   */
#define MII_ADVERTISE       0x04        /* Advertisement control reg   */
#define MII_LPA             0x05        /* Link partner ability reg    */
#define MII_EXPANSION       0x06        /* Expansion register          */
#define MII_DCOUNTER        0x12        /* Disconnect counter          */
#define MII_FCSCOUNTER      0x13        /* False carrier counter       */
#define MII_NWAYTEST        0x14        /* N-way auto-neg test reg     */
#define MII_RERRCOUNTER     0x15        /* Receive error counter       */
#define MII_SREVISION       0x16        /* Silicon revision            */
#define MII_RESV1           0x17        /* Reserved...                 */
#define MII_LBRERROR        0x18        /* Lpback, rx, bypass error    */
#define MII_PHYADDR         0x19        /* PHY address                 */
#define MII_RESV2           0x1a        /* Reserved...                 */
#define MII_TPISTATUS       0x1b        /* TPI status for 10mbps       */
#define MII_NCONFIG         0x1c        /* Network interface config    */

/* Basic mode control register. */
#define BMCR_RESV               0x007f  /* Unused...                   */
#define BMCR_CTST               0x0080  /* Collision test              */
#define BMCR_FULLDPLX           0x0100  /* Full duplex                 */
#define BMCR_ANRESTART          0x0200  /* Auto negotiation restart    */
#define BMCR_ISOLATE            0x0400  /* Disconnect DP83840 from MII */
#define BMCR_PDOWN              0x0800  /* Powerdown the DP83840       */
#define BMCR_ANENABLE           0x1000  /* Enable auto negotiation     */
#define BMCR_SPEED100           0x2000  /* Select 100Mbps              */
#define BMCR_LOOPBACK           0x4000  /* TXD loopback bits           */
#define BMCR_RESET              0x8000  /* Reset the DP83840           */

/* Basic mode status register. */
#define BMSR_ERCAP              0x0001  /* Ext-reg capability          */
#define BMSR_JCD                0x0002  /* Jabber detected             */
#define BMSR_LSTATUS            0x0004  /* Link status                 */
#define BMSR_ANEGCAPABLE        0x0008  /* Able to do auto-negotiation */
#define BMSR_RFAULT             0x0010  /* Remote fault detected       */
#define BMSR_ANEGCOMPLETE       0x0020  /* Auto-negotiation complete   */
#define BMSR_RESV               0x07c0  /* Unused...                   */
#define BMSR_10HALF             0x0800  /* Can do 10mbps, half-duplex  */
#define BMSR_10FULL             0x1000  /* Can do 10mbps, full-duplex  */
#define BMSR_100HALF            0x2000  /* Can do 100mbps, half-duplex */
#define BMSR_100FULL            0x4000  /* Can do 100mbps, full-duplex */
#define BMSR_100BASE4           0x8000  /* Can do 100mbps, 4k packets  */

/* Advertisement control register. */
#define ADVERTISE_SLCT          0x001f  /* Selector bits               */
#define ADVERTISE_CSMA          0x0001  /* Only selector supported     */
#define ADVERTISE_10HALF        0x0020  /* Try for 10mbps half-duplex  */
#define ADVERTISE_10FULL        0x0040  /* Try for 10mbps full-duplex  */
#define ADVERTISE_100HALF       0x0080  /* Try for 100mbps half-duplex */
#define ADVERTISE_100FULL       0x0100  /* Try for 100mbps full-duplex */
#define ADVERTISE_100BASE4      0x0200  /* Try for 100mbps 4k packets  */
#define ADVERTISE_RESV          0x1c00  /* Unused...                   */
#define ADVERTISE_RFAULT        0x2000  /* Say we can detect faults    */
#define ADVERTISE_LPACK         0x4000  /* Ack link partners response  */
#define ADVERTISE_NPAGE         0x8000  /* Next page bit               */

#define RX_DESCRIPTOR_NUM       4 //8    // Max Number of Rx Frame Descriptors
#define TX_DESCRIPTOR_NUM       2 //4    // Max number of Tx Frame Descriptors

#define PACKET_BUFFER_SIZE      1520

#define CONFIG_PHY_ADDR     1


// Frame Descriptor's Owner bit
#define OWNERSHIP_EMAC 0x80000000  // 1 = EMAC
//#define OWNERSHIP_CPU 0x7fffffff  // 0 = CPU



// Rx Frame Descriptor Status
#define RXFD_RXGD    0x00100000  // Receiving Good Packet Received
#define RXFD_RTSAS   0x00800000  // RX Time Stamp Available 


// Tx Frame Descriptor's Control bits
#define TXFD_TTSEN    0x08    // Tx Time Stamp Enable
#define TXFD_INTEN    0x04    // Interrupt Enable
#define TXFD_CRCAPP   0x02    // Append CRC
#define TXFD_PADEN    0x01    // Padding Enable

// Tx Frame Descriptor Status
#define TXFD_TXCP    0x00080000  // Transmission Completion
#define TXFD_TTSAS   0x08000000  // TX Time Stamp Available

// Tx/Rx buffer descriptor structure
struct eth_descriptor;
struct eth_descriptor {
    uint32_t  status1;
    uint8_t *buf;
    uint32_t  status2;
    struct eth_descriptor *next;
#ifdef TIME_STAMPING
    uint32_t backup1;
    uint32_t backup2;
    uint32_t reserved1;
    uint32_t reserved2;
#endif
};

#ifdef TIME_STAMPING

#define ETH_TS_ENABLE() do{EMAC->TSCTL = EMAC_TSCTL_TSEN_Msk;}while(0)
#define ETH_TS_START() do{EMAC->TSCTL |= (EMAC_TSCTL_TSMODE_Msk | EMAC_TSCTL_TSIEN_Msk);}while(0)
s32_t ETH_settime(u32_t sec, u32_t nsec);
s32_t ETH_gettime(u32_t *sec, u32_t *nsec);
s32_t ETH_updatetime(u32_t neg, u32_t sec, u32_t nsec);
s32_t ETH_adjtimex(int ppm);
void ETH_setinc(void);

#endif

#ifdef NU_TRACE
#define NU_DEBUGF(x) { printf x; }
#else
#define NU_DEBUGF(x)
#endif

void numaker_set_mac_addr(uint8_t *addr);
int numaker_eth_init(uint8_t *mac_addr);
uint8_t *numaker_eth_get_tx_buf(void);
void numaker_eth_trigger_tx(uint16_t length, void *p);
int numaker_eth_get_rx_buf(uint16_t *len, uint8_t **buf);
void numaker_eth_rx_next(void);
void numaker_eth_trigger_rx(void);
int numaker_eth_link_ok(void);
void numaker_mac_address(uint8_t *mac);
void numaker_eth_enable_interrupts(void);
void numaker_eth_disable_interrupts(void);

#endif  /* _M480_ETH_ */
