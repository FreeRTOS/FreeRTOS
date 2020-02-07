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
#include "FreeRTOS.h"
#include "list.h"
#include "FreeRTOS_IP.h"

#include "m480_eth.h"

#define ETH_TRIGGER_RX()    do{EMAC->RXST = 0;}while(0)
#define ETH_TRIGGER_TX()    do{EMAC->TXST = 0;}while(0)
#define ETH_ENABLE_TX()     do{EMAC->CTL |= EMAC_CTL_TXON;}while(0)
#define ETH_ENABLE_RX()     do{EMAC->CTL |= EMAC_CTL_RXON;}while(0)
#define ETH_DISABLE_TX()    do{EMAC->CTL &= ~EMAC_CTL_TXON;}while(0)
#define ETH_DISABLE_RX()    do{EMAC->CTL &= ~EMAC_CTL_RXON;}while(0)
    

struct eth_descriptor rx_desc[RX_DESCRIPTOR_NUM] __attribute__ ((aligned(4)));
struct eth_descriptor tx_desc[TX_DESCRIPTOR_NUM] __attribute__ ((aligned(4)));
#ifdef __ICCARM__
#pragma data_alignment=4
struct eth_descriptor rx_desc[RX_DESCRIPTOR_NUM];
struct eth_descriptor tx_desc[TX_DESCRIPTOR_NUM];
uint8_t rx_buf[RX_DESCRIPTOR_NUM][PACKET_BUFFER_SIZE];
uint8_t tx_buf[TX_DESCRIPTOR_NUM][PACKET_BUFFER_SIZE];
#else
struct eth_descriptor rx_desc[RX_DESCRIPTOR_NUM] __attribute__ ((aligned(4)));
struct eth_descriptor tx_desc[TX_DESCRIPTOR_NUM] __attribute__ ((aligned(4)));
uint8_t rx_buf[RX_DESCRIPTOR_NUM][PACKET_BUFFER_SIZE]  __attribute__ ((aligned(4)));
uint8_t tx_buf[TX_DESCRIPTOR_NUM][PACKET_BUFFER_SIZE]  __attribute__ ((aligned(4)));
#endif
struct eth_descriptor volatile *cur_tx_desc_ptr, *cur_rx_desc_ptr, *fin_tx_desc_ptr;


// PTP source clock is 84MHz (Real chip using PLL). Each tick is 11.90ns
// Assume we want to set each tick to 100ns.
// Increase register = (100 * 2^31) / (10^9) = 214.71 =~ 215 = 0xD7
// Addend register = 2^32 * tick_freq / (84MHz), where tick_freq = (2^31 / 215) MHz
// From above equation, addend register = 2^63 / (84M * 215) ~= 510707200 = 0x1E70C600



static void mdio_write(uint8_t addr, uint8_t reg, uint16_t val)
{

    EMAC->MIIMDAT = val;
    EMAC->MIIMCTL = (addr << EMAC_MIIMCTL_PHYADDR_Pos) | reg | EMAC_MIIMCTL_BUSY_Msk | EMAC_MIIMCTL_WRITE_Msk | EMAC_MIIMCTL_MDCON_Msk;

    while (EMAC->MIIMCTL & EMAC_MIIMCTL_BUSY_Msk);

}


static uint16_t mdio_read(uint8_t addr, uint8_t reg)
{
    EMAC->MIIMCTL = (addr << EMAC_MIIMCTL_PHYADDR_Pos) | reg | EMAC_MIIMCTL_BUSY_Msk | EMAC_MIIMCTL_MDCON_Msk;
    while (EMAC->MIIMCTL & EMAC_MIIMCTL_BUSY_Msk);

    return(EMAC->MIIMDAT);
}

static int reset_phy(void)
{

    uint16_t reg;
    uint32_t delayCnt;


    mdio_write(CONFIG_PHY_ADDR, MII_BMCR, BMCR_RESET);

    delayCnt = 2000;
    while(delayCnt-- > 0) {
        if((mdio_read(CONFIG_PHY_ADDR, MII_BMCR) & BMCR_RESET) == 0)
            break;

    }

    if(delayCnt == 0) {
        NU_DEBUGF(("Reset phy failed\n"));
        return(-1);
    }

    mdio_write(CONFIG_PHY_ADDR, MII_ADVERTISE, ADVERTISE_CSMA |
               ADVERTISE_10HALF |
               ADVERTISE_10FULL |
               ADVERTISE_100HALF |
               ADVERTISE_100FULL);

    reg = mdio_read(CONFIG_PHY_ADDR, MII_BMCR);
    mdio_write(CONFIG_PHY_ADDR, MII_BMCR, reg | BMCR_ANRESTART);

    delayCnt = 200000;
    while(delayCnt-- > 0) {
        if((mdio_read(CONFIG_PHY_ADDR, MII_BMSR) & (BMSR_ANEGCOMPLETE | BMSR_LSTATUS))
                == (BMSR_ANEGCOMPLETE | BMSR_LSTATUS))
            break;
    }

    if(delayCnt == 0) {
        NU_DEBUGF(("AN failed. Set to 100 FULL\n"));
        EMAC->CTL |= (EMAC_CTL_OPMODE_Msk | EMAC_CTL_FUDUP_Msk);
        return(-1);
    } else {
        reg = mdio_read(CONFIG_PHY_ADDR, MII_LPA);

        if(reg & ADVERTISE_100FULL) {
            NU_DEBUGF(("100 full\n"));
            EMAC->CTL |= (EMAC_CTL_OPMODE_Msk | EMAC_CTL_FUDUP_Msk);
        } else if(reg & ADVERTISE_100HALF) {
            NU_DEBUGF(("100 half\n"));
            EMAC->CTL = (EMAC->CTL & ~EMAC_CTL_FUDUP_Msk) | EMAC_CTL_OPMODE_Msk;
        } else if(reg & ADVERTISE_10FULL) {
            NU_DEBUGF(("10 full\n"));
            EMAC->CTL = (EMAC->CTL & ~EMAC_CTL_OPMODE_Msk) | EMAC_CTL_FUDUP_Msk;
        } else {
            NU_DEBUGF(("10 half\n"));
            EMAC->CTL &= ~(EMAC_CTL_OPMODE_Msk | EMAC_CTL_FUDUP_Msk);
        }
    }
	FreeRTOS_printf(("PHY ID 1:0x%x\r\n", mdio_read(CONFIG_PHY_ADDR, MII_PHYSID1)));
	FreeRTOS_printf(("PHY ID 2:0x%x\r\n", mdio_read(CONFIG_PHY_ADDR, MII_PHYSID2)));

    return(0);
}


static void init_tx_desc(void)
{
    uint32_t i;


    cur_tx_desc_ptr = fin_tx_desc_ptr = &tx_desc[0];

    for(i = 0; i < TX_DESCRIPTOR_NUM; i++) {
        tx_desc[i].status1 = TXFD_PADEN | TXFD_CRCAPP | TXFD_INTEN;
        tx_desc[i].buf = &tx_buf[i][0];
        tx_desc[i].status2 = 0;
        tx_desc[i].next = &tx_desc[(i + 1) % TX_DESCRIPTOR_NUM];

    }
    EMAC->TXDSA = (unsigned int)&tx_desc[0];
    return;
}

static void init_rx_desc(void)
{
    uint32_t i;


    cur_rx_desc_ptr = &rx_desc[0];

    for(i = 0; i < RX_DESCRIPTOR_NUM; i++) {
        rx_desc[i].status1 = OWNERSHIP_EMAC;
        rx_desc[i].buf = &rx_buf[i][0];
        rx_desc[i].status2 = 0;
        rx_desc[i].next = &rx_desc[(i + 1) % TX_DESCRIPTOR_NUM];
    }
    EMAC->RXDSA = (unsigned int)&rx_desc[0];
    return;
}

void numaker_set_mac_addr(uint8_t *addr)
{

    EMAC->CAM0M = (addr[0] << 24) |
                  (addr[1] << 16) |
                  (addr[2] << 8) |
                  addr[3];

    EMAC->CAM0L = (addr[4] << 24) |
                  (addr[5] << 16);


}

static void __eth_clk_pin_init()
{
    /* Unlock protected registers */
    SYS_UnlockReg();

    /* Enable IP clock */
    CLK_EnableModuleClock(EMAC_MODULE);
    
    // Configure MDC clock rate to HCLK / (127 + 1) = 1.25 MHz if system is running at 160 MH
    CLK_SetModuleClock(EMAC_MODULE, 0, CLK_CLKDIV3_EMAC(127));
    
    /* Update System Core Clock */
    SystemCoreClockUpdate();
    
    /*---------------------------------------------------------------------------------------------------------*/
    /* Init I/O Multi-function                                                                                 */
    /*---------------------------------------------------------------------------------------------------------*/
    // Configure RMII pins
    SYS->GPA_MFPL &= ~(SYS_GPA_MFPL_PA6MFP_Msk | SYS_GPA_MFPL_PA7MFP_Msk);
    SYS->GPA_MFPL |= SYS_GPA_MFPL_PA6MFP_EMAC_RMII_RXERR | SYS_GPA_MFPL_PA7MFP_EMAC_RMII_CRSDV;
    SYS->GPC_MFPL &= ~(SYS_GPC_MFPL_PC6MFP_Msk | SYS_GPC_MFPL_PC7MFP_Msk);
    SYS->GPC_MFPL |= SYS_GPC_MFPL_PC6MFP_EMAC_RMII_RXD1 | SYS_GPC_MFPL_PC7MFP_EMAC_RMII_RXD0;
    SYS->GPC_MFPH &= ~SYS_GPC_MFPH_PC8MFP_Msk;
    SYS->GPC_MFPH |= SYS_GPC_MFPH_PC8MFP_EMAC_RMII_REFCLK;
    SYS->GPE_MFPH &= ~(SYS_GPE_MFPH_PE8MFP_Msk | SYS_GPE_MFPH_PE9MFP_Msk | SYS_GPE_MFPH_PE10MFP_Msk |
                       SYS_GPE_MFPH_PE11MFP_Msk | SYS_GPE_MFPH_PE12MFP_Msk);
    SYS->GPE_MFPH |= SYS_GPE_MFPH_PE8MFP_EMAC_RMII_MDC |
                    SYS_GPE_MFPH_PE9MFP_EMAC_RMII_MDIO |
                    SYS_GPE_MFPH_PE10MFP_EMAC_RMII_TXD0 |
                    SYS_GPE_MFPH_PE11MFP_EMAC_RMII_TXD1 |
                    SYS_GPE_MFPH_PE12MFP_EMAC_RMII_TXEN;

    // Enable high slew rate on all RMII TX output pins
    PE->SLEWCTL = (GPIO_SLEWCTL_HIGH << GPIO_SLEWCTL_HSREN10_Pos) |
                  (GPIO_SLEWCTL_HIGH << GPIO_SLEWCTL_HSREN11_Pos) |
                  (GPIO_SLEWCTL_HIGH << GPIO_SLEWCTL_HSREN12_Pos);


    /* Lock protected registers */
    SYS_LockReg();


}

int numaker_eth_init(uint8_t *mac_addr)
{
    int ret = 0;
    // init CLK & pins
    __eth_clk_pin_init();
  
    // Reset MAC
    EMAC->CTL = EMAC_CTL_RST_Msk;
    while(EMAC->CTL & EMAC_CTL_RST_Msk) {}

    init_tx_desc();
    init_rx_desc();

    numaker_set_mac_addr(mac_addr);  // need to reconfigure hardware address 'cos we just RESET emc...


    /* Configure the MAC interrupt enable register. */
    EMAC->INTEN = EMAC_INTEN_RXIEN_Msk |
                  EMAC_INTEN_TXIEN_Msk |
                  EMAC_INTEN_RXGDIEN_Msk |
                  EMAC_INTEN_TXCPIEN_Msk |
                  EMAC_INTEN_RXBEIEN_Msk |
                  EMAC_INTEN_TXBEIEN_Msk |
                  EMAC_INTEN_RDUIEN_Msk |
                  EMAC_INTEN_TSALMIEN_Msk |
                  EMAC_INTEN_WOLIEN_Msk;

    /* Configure the MAC control register. */
    EMAC->CTL = EMAC_CTL_STRIPCRC_Msk | EMAC_CTL_RMIIEN_Msk;

    /* Accept packets for us and all broadcast and multicast packets */
    EMAC->CAMCTL =  EMAC_CAMCTL_CMPEN_Msk |
                    EMAC_CAMCTL_AMP_Msk |
                    EMAC_CAMCTL_ABP_Msk;
    EMAC->CAMEN = 1;    // Enable CAM entry 0    

    ret= reset_phy();                    
                    
    EMAC_ENABLE_RX();
    EMAC_ENABLE_TX();
    return ret;
}



void  ETH_halt(void)
{

    EMAC->CTL &= ~(EMAC_CTL_RXON_Msk | EMAC_CTL_TXON_Msk);
}

unsigned int m_status;

void EMAC_RX_IRQHandler(void)
{
//    NU_DEBUGF(("%s ... \r\n", __FUNCTION__));
    m_status = EMAC->INTSTS & 0xFFFF;
    EMAC->INTSTS = m_status;
    if (m_status & EMAC_INTSTS_RXBEIF_Msk) {
        // Shouldn't goes here, unless descriptor corrupted
		NU_DEBUGF(("RX descriptor corrupted \r\n"));
		//return;
    }
    // FIX ME: for rx-event, to ack rx_isr into event queue
        xNetworkCallback('R');
}


void numaker_eth_trigger_rx(void)
{
    ETH_TRIGGER_RX();
}

int numaker_eth_get_rx_buf(uint16_t *len, uint8_t **buf)
{
    unsigned int cur_entry, status;

    cur_entry = EMAC->CRXDSA;
    if ((cur_entry == (uint32_t)cur_rx_desc_ptr) && (!(m_status & EMAC_INTSTS_RDUIF_Msk)))  // cur_entry may equal to cur_rx_desc_ptr if RDU occures
            return -1;
    status = cur_rx_desc_ptr->status1;

    if(status & OWNERSHIP_EMAC)
            return -1;

    if (status & RXFD_RXGD) {
        *buf = cur_rx_desc_ptr->buf;
        *len = status & 0xFFFF;
    }
    return 0;
}    

void numaker_eth_rx_next(void)
{
    cur_rx_desc_ptr->status1 = OWNERSHIP_EMAC;
    cur_rx_desc_ptr = cur_rx_desc_ptr->next;    
}    

void EMAC_TX_IRQHandler(void)
{
    unsigned int cur_entry, status;

    status = EMAC->INTSTS & 0xFFFF0000;
    EMAC->INTSTS = status;
    if(status & EMAC_INTSTS_TXBEIF_Msk) {
        // Shouldn't goes here, unless descriptor corrupted
        return;
    }

    cur_entry = EMAC->CTXDSA;

    while (cur_entry != (uint32_t)fin_tx_desc_ptr) {

        fin_tx_desc_ptr = fin_tx_desc_ptr->next;
    }
    // FIX ME: for tx-event, no-op at this stage
    xNetworkCallback('T');
}

uint8_t *numaker_eth_get_tx_buf(void)
{
    if(cur_tx_desc_ptr->status1 & OWNERSHIP_EMAC)
        return(NULL);
    else
        return(cur_tx_desc_ptr->buf);
}

void numaker_eth_trigger_tx(uint16_t length, void *p)
{
    struct eth_descriptor volatile *desc;
    cur_tx_desc_ptr->status2 = (unsigned int)length;
    desc = cur_tx_desc_ptr->next;    // in case TX is transmitting and overwrite next pointer before we can update cur_tx_desc_ptr
    cur_tx_desc_ptr->status1 |= OWNERSHIP_EMAC;
    cur_tx_desc_ptr = desc;

    ETH_TRIGGER_TX();

}

int numaker_eth_link_ok(void)
{
    /* first, a dummy read to latch */
    mdio_read(CONFIG_PHY_ADDR, MII_BMSR);
    if(mdio_read(CONFIG_PHY_ADDR, MII_BMSR) & BMSR_LSTATUS)
      return 1;
    return 0;	
}

//void numaker_eth_set_cb(eth_callback_t eth_cb, void *userData)
//{
//    nu_eth_txrx_cb =  eth_cb;
//    nu_userData = userData;
//}

// Provide ethernet devices with a semi-unique MAC address
void numaker_mac_address(uint8_t *mac)
{
    uint32_t uID1;
    // Fetch word 0
    uint32_t word0 = *(uint32_t *)0x7F804; // 2KB Data Flash at 0x7F800
    // Fetch word 1
    // we only want bottom 16 bits of word1 (MAC bits 32-47)
    // and bit 9 forced to 1, bit 8 forced to 0
    // Locally administered MAC, reduced conflicts
    // http://en.wikipedia.org/wiki/MAC_address
    uint32_t word1 = *(uint32_t *)0x7F800; // 2KB Data Flash at 0x7F800

    if( word0 == 0xFFFFFFFF )		// Not burn any mac address at 1st 2 words of Data Flash
    {
        // with a semi-unique MAC address from the UUID
        /* Enable FMC ISP function */
        SYS_UnlockReg();
        FMC_Open();
        // = FMC_ReadUID(0);
        uID1 = FMC_ReadUID(1);
        word1 = (uID1 & 0x003FFFFF) | ((uID1 & 0x030000) << 6) >> 8;
        word0 = ((FMC_ReadUID(0) >> 4) << 20) | ((uID1 & 0xFF)<<12) | (FMC_ReadUID(2) & 0xFFF);
        /* Disable FMC ISP function */
        FMC_Close();
        /* Lock protected registers */
        SYS_LockReg();
    }

    word1 |= 0x00000200;
    word1 &= 0x0000FEFF;

    mac[0] = (word1 & 0x0000ff00) >> 8;    
    mac[1] = (word1 & 0x000000ff);
    mac[2] = (word0 & 0xff000000) >> 24;
    mac[3] = (word0 & 0x00ff0000) >> 16;
    mac[4] = (word0 & 0x0000ff00) >> 8;
    mac[5] = (word0 & 0x000000ff);
    
    NU_DEBUGF(("mac address %02x-%02x-%02x-%02x-%02x-%02x \r\n", mac[0], mac[1],mac[2],mac[3],mac[4],mac[5]));
}

void numaker_eth_enable_interrupts(void) {
  EMAC->INTEN |= EMAC_INTEN_RXIEN_Msk |
                   EMAC_INTEN_TXIEN_Msk ;
  NVIC_EnableIRQ(EMAC_RX_IRQn);
  NVIC_EnableIRQ(EMAC_TX_IRQn);
}

void numaker_eth_disable_interrupts(void) {
  NVIC_DisableIRQ(EMAC_RX_IRQn);
  NVIC_DisableIRQ(EMAC_TX_IRQn);
}
