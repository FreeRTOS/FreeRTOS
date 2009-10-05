/********************
* Original work (C) COPYRIGHT 2006 STMicroelectronics **************************
* Modifications (C) CopyRight 2006 Richard barry
* File Name          : 91x_enet.c
* Author             : MCD Application Team
* Date First Issued  : May 2006
* Description        : ENET library functions
********************************************************************************
* History:
* May 2006: v1.0
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/


/* Includes ------------------------------------------------------------------*/
#include "FreeRTOS.h"
#include "task.h"
#include "91x_lib.h"
#include "string.h"  //include when using memcpy function

/* Include of other module interface headers ---------------------------------*/
/* Local includes ------------------------------------------------------------*/
/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
#ifndef NULL
#define NULL    (0)
#endif
/* Function return values */
#define ENET_OK  (1)
#define ENET_NOK (0)

/* PHY interface constants. */
#define STE100P_STATUS_REG				0x01
#define STE100P_CONTROL_REG				0x00
#define STE100P_LINK_ABILITY			0x05
#define STE100P_STATUS_LINKED			0x0004
#define STE100P_AUTO_NEGOTIATE_ABILITY	0x1000
#define STE100P_AUTO_NEGOTIATE_COMPLETE 0x20
#define STE100P_10HALF              	0x0020
#define STE100P_10FULL              	0x0040
#define STE100P_100HALF             	0x0080
#define STE100P_100FULL             	0x0100
#define STE100P_CTRL_FULL           	0x0100


/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
#define ENET_NUM_RX_BUFFERS 8

static ENET_DMADSCRBase  dmaTxDscrBase, dmaRxDscrBase[ ENET_NUM_RX_BUFFERS ];
static u8 RxBuff[ ENET_NUM_RX_BUFFERS ][ENET_BUFFER_SIZE];
u8 TxBuff[ENET_BUFFER_SIZE];

/* Private function prototypes -----------------------------------------------*/
extern MEMCOPY_L2S_BY4();

/* Interface functions -------------------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : ENET_SetMACConfig(ENET_MACConfig * MAC_Config)
* Description    : MAC Control Register Configuration
* Input          : MAC_Config structure
* Output         : None
* Return         : None
*******************************************************************************/
void ENET_MACControlConfig(ENET_MACConfig *MAC_Config)
{
  /* ReceiveALL bit */
  if (MAC_Config->ReceiveALL==ENABLE) ENET_MAC->MCR |= MAC_MCR_RA;
  else ENET_MAC->MCR &=~MAC_MCR_RA;

  /* MIIPrescaler */
  ENET_MAC->MCR &=~(0x3<<24);
  if ((MAC_Config->MIIPrescaler) == MIIPrescaler_2)
  ENET_MAC->MCR |=0x1<<24;

  /* Loopback mode */
  if (MAC_Config->LoopbackMode==ENABLE)
  {
    ENET_MAC->MCR &=~MAC_MCR_LM;
    ENET_MAC->MCR |=0x1<<21;
    ENET_MAC->MCR &=~MAC_MCR_DRO;  /*enable frame reception during transmission*/
  }

  /* Address filtering mode */
  ENET_MAC->MCR &=~MAC_MCR_AFM;
  ENET_MAC->MCR |= MAC_Config->AddressFilteringMode;

  /* VLAN Filtering Mode */
 	ENET_MAC->MCR |= (MAC_Config->VLANFilteringMode)<<15;

  /*Wrong Frame Pass */
  if (MAC_Config->PassWrongFrame == ENABLE) ENET_MAC->MCR |=MAC_MCR_PWF;
  else ENET_MAC->MCR &=~MAC_MCR_PWF;

  /* Late Collision Retransmission*/
  if (MAC_Config->LateCollision == ENABLE) ENET_MAC->MCR |=MAC_MCR_ELC;
  else ENET_MAC->MCR &=~MAC_MCR_ELC;

  /* Broadcast Frame Reception */
  if (MAC_Config->BroadcastFrameReception == ENABLE) ENET_MAC->MCR &=~MAC_MCR_DBF;
  else ENET_MAC->MCR |=MAC_MCR_DBF;

  /* PacketRetry */
  if (MAC_Config->PacketRetry == ENABLE) ENET_MAC->MCR &=~MAC_MCR_DPR;
  else ENET_MAC->MCR |=MAC_MCR_DPR;

  /* RxFrameFiltering */
  if (MAC_Config->RxFrameFiltering == ENABLE) ENET_MAC->MCR |=MAC_MCR_RVFF;
  else ENET_MAC->MCR &=~MAC_MCR_RVFF;

  /* AutomaticPadRemoval */
  if (MAC_Config->AutomaticPadRemoval == ENABLE) ENET_MAC->MCR |=MAC_MCR_APR;
  else ENET_MAC->MCR &=~MAC_MCR_APR;

  /* DefferalCheck */
  if (MAC_Config->DeferralCheck == ENABLE) ENET_MAC->MCR |=MAC_MCR_DCE;
  else ENET_MAC->MCR &=~MAC_MCR_DCE;

}



/*******************************************************************************
* Function Name  : ENET_SetOperatingMode
* Description    : Sets the Operating mode
* Input          : ENET_OperatingMode:(see ENET_OperatingMode in 91x_enet.h)
* Output         : None
* Return         : None
*******************************************************************************/
portBASE_TYPE ENET_SetOperatingMode( void )
{
unsigned long ulStatusReg, ulControlReg, ulLinkAbilityReg;

	/* Link status is latched, so read twice to get current value */
	ulStatusReg = ENET_MIIReadReg(0, STE100P_STATUS_REG);
	ulStatusReg = ENET_MIIReadReg(0, STE100P_STATUS_REG);

	if( !( ulStatusReg & STE100P_STATUS_LINKED ) )
	{	
		/* No Link. */
		return pdFAIL;
	}

	ulControlReg = ENET_MIIReadReg(0, STE100P_CONTROL_REG);
	if (ulControlReg & STE100P_AUTO_NEGOTIATE_ABILITY)
	{				
		/* AutoNegotiation is enabled. */
		if (!(ulStatusReg & STE100P_AUTO_NEGOTIATE_COMPLETE))
		{
			/* Auto-negotiation in progress. */
			return pdFAIL;				
		}		

		ulLinkAbilityReg = ENET_MIIReadReg(0, STE100P_LINK_ABILITY);
		if( ( ulLinkAbilityReg & STE100P_100FULL ) || ( ulLinkAbilityReg & STE100P_10FULL ) )
		{
			ENET_MAC->MCR |=MAC_MCR_FDM;   /* full duplex mode */
			ENET_MAC->MCR &=~MAC_MCR_DRO;  /* enable frame reception during transmission */
		}
		else
		{
			ENET_MAC->MCR &=~MAC_MCR_FDM; /* half duplex mode */
			ENET_MAC->MCR |=MAC_MCR_DRO;  /* disable frame reception during transmission */
		}
	}
	else
	{
		if( ulStatusReg & STE100P_CTRL_FULL )
		{
			ENET_MAC->MCR |=MAC_MCR_FDM;   /* full duplex mode */
			ENET_MAC->MCR &=~MAC_MCR_DRO;  /* enable frame reception during transmission */		
		}
		else
		{
			ENET_MAC->MCR &=~MAC_MCR_FDM; /* half duplex mode */
			ENET_MAC->MCR |=MAC_MCR_DRO;  /* disable frame reception during transmission */
		}
	}	
	
	return pdPASS;
}

/*******************************************************************************
* Function Name  : ENET_MIIWriteReg
* Description    : Writes a value on the PHY registers
* Input          : phyDev PHY device address
                 : phyReg PHY register to be written
*                : phyVal PHY register value
* Output         : None
* Return         : None
*******************************************************************************/
void ENET_MIIWriteReg (u8 phyDev, u8 phyReg, u32  phyVal)
{

  volatile u32 addr;
  volatile u32 res;     /* temporary result for address register status */
  volatile u32 timeout;

  /* Prepare the MII register address */
  addr = 0;
  addr |= ((phyDev<<11) & MAC_MII_ADDR_PHY_ADDR); /* set the PHY address */
  addr |= ((phyReg<<6) & MAC_MII_ADDR_MII_REG); /* select the corresponding register */
  addr |= MAC_MII_ADDR_MII_WRITE;  /* in write mode */
  addr |= MAC_MII_ADDR_MII_BUSY;

  /* Check for the Busy flag */
  timeout=0;
  do
  {
    timeout++;
    res = ENET_MAC->MIIA;
  } while ((res & MAC_MII_ADDR_MII_BUSY) && (timeout < (u32 )MII_WRITE_TO));

  /* Give the value to the MII data register */
  ENET_MAC->MIID = (phyVal & 0xFFFF);

  /* write the result value into the MII Address register */
  ENET_MAC->MIIA =addr;

  /* Check for the Busy flag */
  timeout=0;
  do
  {
    timeout++;
    res = ENET_MAC->MIIA;
  } while ((res & MAC_MII_ADDR_MII_BUSY) && (timeout < (u32 )MII_WRITE_TO));

}

/*******************************************************************************
* Function Name  : ENET_MIIReadReg
* Description    : Writes a value on the PHY
* Input          : phyDev PHY device address
*                : phyReg PHY register to be read
* Output         : None
* Return         : The read value (16 bits)
*******************************************************************************/
u32 ENET_MIIReadReg (u8 phyDev, u32 phyReg )
{

  u32 rValue;
  u32 addr;
  u32 res;     /* temporary result for address register status */
  u32 timeout; /* timeout value for read process */

  /* prepare the MII register address */
  addr = 0;
  addr |= ((phyDev<<11) & MAC_MII_ADDR_PHY_ADDR); /* set the PHY address */
  addr |= ((phyReg<<6) & MAC_MII_ADDR_MII_REG); /* select the corresponding register */
  addr &= ~(MAC_MII_ADDR_MII_WRITE);  /* ... in read mode */
  addr |= MAC_MII_ADDR_MII_BUSY;

  /* Check for the Busy flag */
  timeout = 0;

  do
  {
    timeout++;
    res = ENET_MAC->MIIA;
  } while ((res & MAC_MII_ADDR_MII_BUSY) && (timeout < (u32 )MII_READ_TO));

  /* write the result value into the MII Address register */
  ENET_MAC->MIIA = addr;

  /* Check for the Busy flag */
  timeout = 0;

  do
  {
    timeout++;
    res = ENET_MAC->MIIA;
  } while ((res & MAC_MII_ADDR_MII_BUSY) && (timeout < (u32 )MII_READ_TO));

  /* read the result value from data register*/
  rValue = ENET_MAC->MIID;

  return (rValue & 0x0000FFFF);
}

/*******************************************************************************
* Function Name  : ENET_RxDscrInit
* Description    : Initializes the Rx ENET descriptor chain. Single Descriptor
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/

void ENET_RxDscrInit(void)
{
int i;

	for( i = 0; i < ENET_NUM_RX_BUFFERS; i++ )
	{
		/* Assign temp Rx array to the ENET buffer */
		dmaRxDscrBase[ i ].dmaAddr = (u32)&(RxBuff[ i ][ 0 ]);

		/* Initialize RX ENET Status and control */
		dmaRxDscrBase[ i ].dmaStatCntl = 0x4000;

		/* Initialize the next descriptor- In our case its single descriptor */
		dmaRxDscrBase[ i ].dmaNext = (u32)&(dmaRxDscrBase[i+1]) | 0x01;

		/* Set the max packet size  */
		dmaRxDscrBase[ i ].dmaStatCntl = ENET_MAX_PACKET_SIZE | ENET_NEXT_ENABLE;

		/* Setting the VALID bit */
		dmaRxDscrBase[ i ].dmaPackStatus = DMA_DSCR_RX_STATUS_VALID_MSK;
	}

	dmaRxDscrBase[ ENET_NUM_RX_BUFFERS - 1 ].dmaNext = (u32)&(dmaRxDscrBase[ 0 ]);

	/* Setting the RX NEXT Descriptor Register inside the ENET */
	ENET_DMA->RXNDAR = (u32)&(dmaRxDscrBase) | 0x01;
}

/*******************************************************************************
* Function Name  : ENET_TxDscrInit
* Description    : Initializes the Tx ENET descriptor chain with single descriptor
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/

void ENET_TxDscrInit(void)
{

  /* ENET Start Address */
  dmaTxDscrBase.dmaAddr = (u32)TxBuff;

  /* Next Descriptor Address */
  dmaTxDscrBase.dmaNext = (u32)&(dmaTxDscrBase);

  /* Initialize ENET status and control */
  dmaTxDscrBase.dmaStatCntl = 0;

  /* Tx next set to Tx decriptor base */
  ENET_DMA->TXNDAR = (u32)&(dmaTxDscrBase);

  /* Enable next enable */
  ENET_DMA->TXNDAR |= DMA_DSCR_NXT_NPOL_EN;

}

/*******************************************************************************
* Function Name  : ENET_Init
* Description    : ENET MAC, PHY and DMA initializations
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void ENET_Init ()
{

  vu32 regValue;
  ENET_MACConfig *MAC_Config;
  ENET_MACConfig config;

  /* De-assert the SRESET bit of ENET + MAC devices */
  ENET_DMA->SCR &=~DMA_SCR_SRESET;
  MAC_Config =&config;
  /* Initialize MAC control register with common values */
  MAC_Config->ReceiveALL = DISABLE;
  if (SCU_GetHCLKFreqValue() > 50000)
  MAC_Config->MIIPrescaler = MIIPrescaler_2;
  MAC_Config->LoopbackMode = DISABLE;
  MAC_Config->AddressFilteringMode = MAC_Perfect_Multicast_Perfect;
	MAC_Config->VLANFilteringMode = VLANfilter_VLTAG;
  MAC_Config->PassWrongFrame = DISABLE;
  MAC_Config->LateCollision = DISABLE;
  MAC_Config->BroadcastFrameReception = ENABLE;
  MAC_Config->PacketRetry = ENABLE;
  MAC_Config->RxFrameFiltering = ENABLE;
  MAC_Config->AutomaticPadRemoval = ENABLE;
  MAC_Config->DeferralCheck = ENABLE;

    /* Configure MAC control register */
  ENET_MACControlConfig(MAC_Config);

  /* DMA initialization */
  /* Read the ENET DMA Status and Control Register */
  regValue = ENET_DMA->SCR;

  /* Setup Tx Max burst size */
  regValue &= ~(u32)DMA_SCR_TX_MAX_BURST_SZ;
  regValue |= (u32)DMA_SCR_TX_MAX_BURST_SZ_VAL;

  /* Setup Rx Max Burst size */
  regValue &= ~(u32)DMA_SCR_RX_MAX_BURST_SZ;
  regValue |= (u32)DMA_SCR_RX_MAX_BURST_SZ_VAL;

  /* Write Tx & Rx burst size to the ENET status and control register */
  ENET_DMA->SCR = regValue;

  /* Put the PHY in reset mode */
  ENET_MIIWriteReg(0x0,MAC_MII_REG_XCR, 0x8000);

  /* Delay to assure PHY reset */
  vTaskDelay( 3000 / portTICK_RATE_MS );

  /* initialize the opearting mode */
  while( ENET_SetOperatingMode() == pdFAIL )
  {
  		vTaskDelay( 3000 / portTICK_RATE_MS );
  }
	
  /*set MAC physical*/
	//ENET_MAC->MAH = (MAC_ADDR5<<8) + MAC_ADDR4;
	//ENET_MAC->MAL = (MAC_ADDR3<<24) + (MAC_ADDR2<<16) + (MAC_ADDR1<<8) + MAC_ADDR0;
	
  /* Initialize Rx and Tx descriptors in memory */
  ENET_TxDscrInit();
  ENET_RxDscrInit();

	// What's happening ???
#ifdef DEBUG
	//int pippo = 1; // Do NOT remove!!!
#endif
}

/********************************************************************************
* Function Name  : ENET_HandleRxPkt
* Description    : receive a packet and copy it to memory pointed by ppkt.
* Input          : ppkt: pointer on application receive buffer.
* Output         : None
* Return         : ENET_NOK - If there is no packet
*                : ENET_OK  - If there is a packet
*******************************************************************************/
u32 ENET_HandleRxPkt ( void *ppkt)
{
ENET_DMADSCRBase *pDescr;
u16 size;
static int iNextRx = 0;

	if( dmaRxDscrBase[ iNextRx ].dmaPackStatus & DMA_DSCR_RX_STATUS_VALID_MSK )
	{
		return 0;
	}

	pDescr = &dmaRxDscrBase[ iNextRx ];

	/*Get the size of the packet*/
	size = ((pDescr->dmaPackStatus & 0x7ff) - 4);

	//MEMCOPY_L2S_BY4((u8*)ppkt, RxBuff, size); /*optimized memcopy function*/
	memcpy(ppkt, RxBuff[iNextRx], size);   //string.h library*/

	/* Give the buffer back to ENET */
	pDescr->dmaPackStatus = DMA_DSCR_RX_STATUS_VALID_MSK;

	iNextRx++;

	if( iNextRx >= ENET_NUM_RX_BUFFERS )
	{
		iNextRx = 0;
	}

	/* Return no error */
	return size;
}

/*******************************************************************************
* Function Name  : ENET_TxPkt
* Description    : Transmit a packet
* Input          : ppkt: pointer to application packet Buffer
*                : size: Tx Packet size
* Output         : None
* Return         : None
*******************************************************************************/

u8 *pcGetNextBuffer( void )
{
	if( dmaTxDscrBase.dmaPackStatus & DMA_DSCR_TX_STATUS_VALID_MSK )
	{
		return NULL;
	}
	else
	{
		return ( unsigned char * ) TxBuff;
	}
}

void ENET_TxPkt(void *ppkt, u16 size)
{
	/* Setting the Frame Length*/
	dmaTxDscrBase.dmaStatCntl = (size&0xFFF);

	/* Start the ENET by setting the VALID bit in dmaPackStatus of current descr*/
	dmaTxDscrBase.dmaPackStatus = DMA_DSCR_TX_STATUS_VALID_MSK;

	/* Start the transmit operation */
	ENET_DMA->TXSTR|= DMA_TX_START_FETCH;
}

/*******************************************************************************
* Function Name  : ENET_Start
* Description    : Enables ENET MAC reception / transmission & starts DMA fetch
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/

void  ENET_Start ( void)
{
  u32 value;

  /* Force a ENET abort by software for the receive block */
   ENET_DMA->RXSTR &=~ DMA_RX_START_DMA_EN;

  /* Force a ENET abort by software for the transmit block */
   ENET_DMA->TXSTR &=~DMA_TX_START_DMA_EN;

  /* Reset all interrupts */
  ENET_DMA->ISR = 0xFFFFFFFF;

  /* Setup Descriptor Fetch ENET_PhyDelay for Receive Block */
  value = ENET_DMA->RXSTR;
  value &= ~( DMA_RX_START_DFETCH_DLY );
  value |= DMA_RX_START_DFETCH_DEFAULT;
  ENET_DMA->RXSTR=  value;

  /* Setup Descriptor Fetch ENET_PhyDelay for Transmit Block */
  value = ENET_DMA->TXSTR;
  value &= ~( DMA_TX_START_DFETCH_DLY );
  value |= DMA_TX_START_DFETCH_DEFAULT;
  ENET_DMA->TXSTR= value;

  /* Set Tx underrun bit */
  value &= ~( DMA_TX_START_URUN );
  value |= DMA_TX_START_URUN;
  ENET_DMA->TXSTR = value;

  /* Clear the interrupts */
  ENET_DMA->IER = 0x0;

  /* MAC TX enable */
  ENET_MAC->MCR|= MAC_MCR_TE;

  /* MAC RX enable */
  ENET_MAC->MCR|= MAC_MCR_RE;

  /* Start the DMA Fetch */
  ENET_DMA->RXSTR|= DMA_RX_START_FETCH;
}


/*******************************************************************************
* Function Name  : ENET_InitClocksGPIO
* Description    : Reset, clocks & GPIO Ethernet Pin initializations
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void ENET_InitClocksGPIO(void)
{

  GPIO_InitTypeDef GPIO_Struct;

  SCU_AHBPeriphClockConfig(__ENET, ENABLE);
  SCU_AHBPeriphReset(__ENET,DISABLE);
  SCU_PHYCLKConfig(ENABLE);

  GPIO_DeInit(GPIO1);
  GPIO_Struct.GPIO_Pin = GPIO_Pin_1 | GPIO_Pin_2 |GPIO_Pin_3 |GPIO_Pin_4 |GPIO_Pin_7 ;
  GPIO_Struct.GPIO_Type = GPIO_Type_PushPull;
  GPIO_Struct.GPIO_Direction = GPIO_PinOutput;
  GPIO_Struct.GPIO_IPConnected = GPIO_IPConnected_Disable;
  GPIO_Struct.GPIO_Alternate=GPIO_OutputAlt2;
  GPIO_Init(GPIO1, &GPIO_Struct);


  GPIO_DeInit(GPIO5);
  GPIO_Struct.GPIO_Pin = GPIO_Pin_2 | GPIO_Pin_3;
  GPIO_Struct.GPIO_Type = GPIO_Type_PushPull;
  GPIO_Struct.GPIO_Direction = GPIO_PinOutput;
  GPIO_Struct.GPIO_IPConnected = GPIO_IPConnected_Disable;
  GPIO_Struct.GPIO_Alternate=GPIO_OutputAlt2;
  GPIO_Init(GPIO5, &GPIO_Struct);

}

/******************** (C) COPYRIGHT 2006 STMicroelectronics *******************/


