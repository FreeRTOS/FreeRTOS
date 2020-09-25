
FreeRTOS+TCP driver for STM32H7xx.

Some STM32 network settings are stored in 'stm32h7xx_hal_conf.h'.

Number of DMA descriptors, for transmission and for reception.

The descriptors for transmission are protected with a counting semaphore.
By the time that a packet has been sent, the other TX descriptor becomes
available already.
The number of descriptors has an incluence on the performance.  But that also depends on the size
of the TCP buffers and TCP window sizes.

When ETH_RX_DESC_CNT is too low, the adapter may miss incoming packets, they will be dropped.
When ETH_RX_DESC_CNT is low, sending packets becomes slower.

Here are settings give a high performance for iperf3:

~~~
/* ########################### Ethernet Configuration ######################### */
#define ETH_TX_DESC_CNT         14U /* number of Ethernet Tx DMA descriptors */
#define ETH_RX_DESC_CNT         8U  /* number of Ethernet Rx DMA descriptors */
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
located in special RAM area called ".ethernet_data". This shall be declared in
the linker file.

It is possible to use the AXI SRAM for this, but RAM{1,2,3} are also connected
to the Ethernet MAC.

Here is an example of the changes to the linker file:

	AXI_RAM (xrw)   : ORIGIN = 0x24000000, LENGTH = 512K	/* .ethernet_data declared here. */
	.ethernet_data :
	{
		PROVIDE_HIDDEN (__ethernet_data_start = .);
		KEEP (*(SORT(.ethernet_data.*)))
		KEEP (*(.ethernet_data*))
		PROVIDE_HIDDEN (__ethernet_data_end = .);
	} >AXI_RAM

Here is a table of 3 types of STH32H7 :
/**
 * RAM area	H747	H743	H742	Location
 * ------------------------------------------------
 * DTCM		128k	128k	128k	0x20000000
 * AXI-SRAM	511k	511k	384k	0x24000000
 *
 * SRAM1	128k	128k	32k		0x30000000
 * SRAM2	128k	128k	16k		0x30020000
 * SRAM3	32k		32k	 	-		0x30040000
 * SRAM4	64k		64k		64k		0x38000000
 * Backup   SRAM	4k		4k	4k	0x38800000
 */


Please make sure that the addresses and lengths are correct for your model of STM32H7xx.
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

Checksum cal be calculated in the Ethernet MAC, which is faster than doing manual calculations:

~~~
	/* The checksums will be checked and calculated by the STM32F4x ETH peripheral. */
	#define ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM		( 1 )
	#define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM		( 1 )
~~~

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


As most EMAC's, the STM32H7 EMAC is able to put packets in multiple linked DMA segments.
FreeRTOS+TCP never uses this feature. Each packet is stored in a single buffer called
`NetworkBufferDescriptor_t`.
