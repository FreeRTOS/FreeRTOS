
FreeRTOS+TCP driver for STM32H7xx.

Some STM32 network settings are stored in 'stm32h7xx_hal_conf.h'.

Number of DMA descriptors, for transmission and for reception.

The descriptors for transmission are protected with a counting semaphore.
By the time that a packet has been sent, the other TX descriptor becomes
available already.
The more descriptors, the higher the performance.  But htat also depends on the size
of the TCP buffers and TCP window sizes.

Here are settings give a high performance for iperf3:

~~~
/* ########################### Ethernet Configuration ######################### */
#define ETH_TX_DESC_CNT         14U /* number of Ethernet Tx DMA descriptors */
#define ETH_RX_DESC_CNT         6U  /* number of Ethernet Rx DMA descriptors */
~~~

Two more defines that are needed:

~~~
#define HAL_ETH_MODULE_ENABLED
#define USE_HAL_ETH_REGISTER_CALLBACKS     0U /* ETH register callback disabled     */
~~~

The following macro's are **not** used by the FreeRTOS driver:

    #define ETH_MAC_ADDR0    ((uint8_t)0x02)
    #define ETH_MAC_ADDR1    ((uint8_t)0x00)
    ...

All memory that is shared between the CPU and the DMA ETH peripheral, should be
located in special RAM area:

    RAM3 (xrw)      : ORIGIN = 0x24000000, LENGTH = 512K

Please make sure that the address and length are correct for your model of STM32H7xx.
If you use a memory that is not supported, it will result in a DMA errors.

In FreeRTOSIPConfig.h :

Define the total number of network buffer descriptors, e.g. 64:

~~~
    #define ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS    ( 64 )
~~~

It is recommended to use the zero-copy method for both reception and transmission:

~~~
    #define ipconfigZERO_COPY_RX_DRIVER            ( 1 )
    #define ipconfigZERO_COPY_TX_DRIVER            ( 1 )
~~~

The copy-method also works well, may just a little slower.


The most important DMAC registers, along with their names which are used in the reference manual:

    __IO uint32_t DMAMR;           // ETH_DMAMR         DMA mode register
    __IO uint32_t DMAISR;          // ETH_DMAISR        DMA Interrupt status register
    __IO uint32_t DMADSR;          // ETH_DMADSR        DMA Debug status register
    __IO uint32_t DMACCR;          // ETH_DMACCR        DMA Channel control register
    __IO uint32_t DMACTCR;         // ETH_DMACTXCR      Channel Tx transmit control register
    __IO uint32_t DMACRCR;         // ETH_DMACRXCR      Channel Rx receive control register
    __IO uint32_t DMACTDLAR;       // ETH_DMACTXDLAR    Channel Tx descriptor list address register 
    __IO uint32_t DMACRDLAR;       // ETH_DMACRXDLAR    Channel Rx descriptor list address register
    __IO uint32_t DMACTDTPR;       // ETH_DMACTXDTPR    Channel TX tail pointer
    __IO uint32_t DMACRDTPR;       // ETH_DMACRXDTPR    Channel RX tail pointer
    __IO uint32_t DMACTDRLR;       // ETH_DMACTXRLR     Channel Tx descriptor ring length register
    __IO uint32_t DMACRDRLR;       // ETH_DMACRXRLR     Channel Rx descriptor ring length register
    __IO uint32_t DMACIER;         // ETH_DMACIER       Channel interrupt enable register 
    __IO uint32_t DMACRIWTR;       // ETH_DMACRXIWTR    Channel Rx interrupt watchdog timer register
    __IO uint32_t DMACCATDR;       // ETH_DMACCATXDR    Channel Tx current application transmit descriptor register
    __IO uint32_t DMACCARDR;       // ETH_DMACCARXDR    Channel Rx current application receive descriptor register
    __IO uint32_t DMACCATBR;       // ETH_DMACCATXBR    Channel Tx current application transmit buffer register
    __IO uint32_t DMACCARBR;       // ETH_DMACCARXBR    Channel Rx current application receive buffer register
    __IO uint32_t DMACSR;          // ETH_DMACSR        Channel status register


As most EMAC's the STM32H7 EMAC is able to put packets in multiple linked DMA segments.
FreeRTOS+TCP never uses this feature. Each packet is stored in a single buffer called
`NetworkBufferDescriptor_t`.

