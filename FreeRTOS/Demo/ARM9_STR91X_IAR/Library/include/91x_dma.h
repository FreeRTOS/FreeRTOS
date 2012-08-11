/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : template.h
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : provide a short description of the source file indicating
*                      its purpose.
********************************************************************************
* History:
* 05/24/2006 : Version 1.1
* 05/18/2006 : Version 1.0
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __91x_DMA_H
#define __91x_DMA_H

/* Includes ------------------------------------------------------------------*/
#include"91x_map.h"


/* Exported types ------------------------------------------------------------*/

typedef struct
{
 u32 DMA_Channel_SrcAdd;    /* The current source address (byte-aligned) of the data to be transferred.*/

 u32 DMA_Channel_DesAdd;    /* The current destination address (byte-aligned) of the data to be transferred.*/

 u32 DMA_Channel_LLstItm;   /* The word- aligned address for the next Linked List Item. */

 u32 DMA_Channel_DesWidth;   /* Destination transfer width. */

 u32 DMA_Channel_SrcWidth;   /* Source transfer width. */

 u32 DMA_Channel_DesBstSize; /* The destination burst size which indicates the number of transfers that make up a destination burst transfer request.*/

 u32 DMA_Channel_SrcBstSize; /* The source burst size.Indicates the number of transfers that make up a source burst */

 u32 DMA_Channel_TrsfSize;   /* Transfer size which indicates the size of the transfer when the DMA controller is the flow controller*/

 u32 DMA_Channel_FlowCntrl;  /* Flow control and transfer type. */

 u32 DMA_Channel_Src;        /* Source peripheral: selects the DMA source request peripheral. */

 u32 DMA_Channel_Des;        /* Destination peripheral:selects the DMA destination request peripheral. */

} DMA_InitTypeDef;

/* Exported constants --------------------------------------------------------*/

    /* Interrupts masks */

#define    DMA_ITMask_IE	        0x4000	/* Interrupt error mask. */
#define    DMA_ITMask_ITC	        0x8000	/* Terminal count interrupt mask.*/
#define    DMA_ITMask_ALL	        0xC000	/* All DMA_Channelx interrupts enable/disable mask*/

  /* Sources Request (used as masks) */

#define   DMA_USB_RX_Mask	            0x0001
#define   DMA_USB_TX_Mask	            0x0002
#define   DMA_TIM0_Mask	                0x0004
#define   DMA_TIM1_Mask	                0x0008
#define   DMA_UART0_RX_Mask             0x0010
#define   DMA_UART0_TX_Mask             0x0020
#define   DMA_UART1_RX_Mask             0x0040
#define   DMA_UART1_TX_Mask             0x0080
#define   DMA_External_Req0_Mask        0x0100
#define   DMA_External_Req1_Mask	    0x0200
#define   DMA_I2C0_Mask	                0x0400
#define   DMA_I2C1_Mask	                0x0800
#define   DMA_SSP0_RX_Mask	            0x1000
#define   DMA_SSP0_TX_Mask	            0x2000
#define   DMA_SSP1_RX_Mask	            0x4000
#define   DMA_SSP1_TX_Mask	            0x8000


/* Previleged Mode and user mode */

#define   DMA_PrevilegedMode	        0x10000000
#define   DMA_UserMode	                0xEFFFFFFF


/* Error and Terminal Count interrupts Status, after and before"raw" masking */
#define   DMA_IS	                0x01
#define   DMA_TCS	                0x02
#define   DMA_ES	                0x03
#define   DMA_TCRS	                0x04
#define   DMA_ERS	                0x05


/* interrupt clear: Terminal Count flag Clear and Error flag clear*/

#define   DMA_TCC	                0x01
#define   DMA_EC	                0x02

/* channel index "0...7"*/

#define   Channel0                      0
#define   Channel1                      1
#define   Channel2                      2
#define   Channel3                      3
#define   Channel4                      4
#define   Channel5                      5
#define   Channel6                      6
#define   Channel7                      7



/* Destination request selection: selects the DMA Destination request peripheral */

#define   DMA_DES_USB_RX	        0x00
#define   DMA_DES_USB_TX	        0x40
#define   DMA_DES_TIM1	            0x80
#define   DMA_DES_TIM2	            0xC0
#define   DMA_DES_UART0_RX	 	    0x100
#define   DMA_DES_UART0_TX		    0x140
#define   DMA_DES_UART1_RX	        0x180
#define   DMA_DES_UART1_TX	        0x1C0
#define   DMA_DES_External_Req0	    0x200
#define   DMA_DES_External_Req1	    0x240
#define   DMA_DES_I2C0	            0x280
#define   DMA_DES_I2C1	            0x2C0
#define   DMA_DES_SSP0_RX	        0x300
#define   DMA_DES_SSP0_TX	        0x340
#define   DMA_DES_SSP1_RX	        0x380
#define   DMA_DES_SSP1_TX	        0x3C0




/* Source request selection: selects the DMA Source request peripheral */

#define   DMA_SRC_USB_RX	        0x00
#define   DMA_SRC_USB_TX	        0x02
#define   DMA_SRC_TIM1	            0x04
#define   DMA_SRC_TIM2	            0x06
#define   DMA_SRC_UART0_RX	 	    0x08
#define   DMA_SRC_UART0_TX		    0x0A
#define   DMA_SRC_UART1_RX	        0x0C
#define   DMA_SRC_UART1_TX	        0x0E
#define   DMA_SRC_External_Req0	    0x10
#define   DMA_SRC_External_Req1	    0x12
#define   DMA_SRC_I2C0	            0x14
#define   DMA_SRC_I2C1	            0x16
#define   DMA_SRC_SSP0_RX	        0x18
#define   DMA_SRC_SSP0_TX	        0x1A
#define   DMA_SRC_SSP1_RX	        0x1C
#define   DMA_SRC_SSP1_TX	        0x1E





#define   DMA_FlowCntrlt0_DMA	       0x00000000	   /* transfer type :Memory-to-memory, flow controller:DMA */
#define   DMA_FlowCntrl1_DMA	       0x00000800	   /* transfer type :Memory-to-peripheral, flow controller:DMA */
#define   DMA_FlowCntrl2_DMA	       0x00001000	   /* transfer type :Peripheral-to-memory, flow controller:DMA */
#define   DMA_FlowCntrl3_DMA	       0x00001800	   /* transfer type :Source peripheral-to-destination peripheral, flow controller:DMA */	
#define   DMA_FlowCntrl_DestPerip	   0x00002000      /* transfer type :Source peripheral-to-destination peripheral, flow controller:Destination peripheral */	
#define   DMA_FlowCntrl_Perip1	       0x00002800      /* transfer type :Memory-to-peripheral, flow controller:peripheral */		
#define   DMA_FlowCntrl_Perip2	       0x00003000      /* transfer  type : Peripheral-to-memory, flow controller:peripheral */	
#define   DMA_FlowCntrl_SrcPerip	   0x00003800      /* transfer  type :Source peripheral-to-destination peripheral, flow controller:Source peripheral */	




#define   DMA_SrcBst_1Data	          0x00000000	/* Source Burst transfer request IS 1 Data ( DATA = Source transfer width ) */
#define   DMA_SrcBst_4Data	          0x00001000	/* Source Burst transfer request IS 4 Data  */
#define   DMA_SrcBst_8Data	          0x00002000	/* Source Burst transfer request IS 8 Data   */
#define   DMA_SrcBst_16Data	          0x00003000    /* Source Burst transfer request IS 16 Data  */
#define   DMA_SrcBst_32Data	          0x00004000	/* Source Burst transfer request IS 32 Data  */
#define   DMA_SrcBst_64Data	          0x00005000	/* Source Burst transfer request IS 64Data   */
#define   DMA_SrcBst_128Data	      0x00006000	/* Source Burst transfer request IS 128 Data */
#define   DMA_SrcBst_256Data 	      0x00007000	/* Source Burst transfer request IS 256 Data */




#define   DMA_DesBst_1Data	          0x00000000	/*Destination Burst transfer request IS 1Data ( DATA = destination transfer width ) */
#define   DMA_DesBst_4Data	          0x00008000	/*Destination Burst transfer request IS 1 Data   */
#define   DMA_DesBst_8Data	          0x00010000	/*Destination Burst transfer request IS 4 Data   */
#define   DMA_DesBst_16Data	          0x00018000	/*Destination Burst transfer request IS 8 Data   */
#define   DMA_DesBst_32Data	          0x00020000	/*Destination Burst transfer request IS 16 Data  */
#define   DMA_DesBst_64Data	          0x00028000	/*Destination Burst transfer request IS 32 Data  */
#define   DMA_DesBst_128Data	      0x00030000	/*Destination Burst transfer request IS 128 Data */
#define   DMA_DesBst_256Data	      0x00038000	/*Destination Burst transfer request IS 256 Data */





#define   DMA_SrcWidth_Byte	          0x00000000  /* source Width is one Byte */
#define   DMA_SrcWidth_HalfWord	      0x00040000  /* source Width is one HalfWord */
#define   DMA_SrcWidth_Word	          0x00080000  /*  source Width is one Word  */




#define   DMA_DesWidth_Byte	          0x00000000  /* Destination Width is one Byte */
#define   DMA_DesWidth_HalfWord	      0x00200000  /* Destination Width is one HalfWord */
#define   DMA_DesWidth_Word	          0x00400000	/* Destination Width is one Word */






/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */

void DMA_DeInit(void);
void DMA_Init(DMA_Channel_TypeDef * DMA_Channelx, DMA_InitTypeDef * DMA_InitStruct);
void DMA_StructInit(DMA_InitTypeDef *DMA_InitStruct);
void DMA_Cmd(FunctionalState NewState);
void DMA_ITMaskConfig(DMA_Channel_TypeDef * DMA_Channelx, u16 DMA_ITMask, FunctionalState NewState);
void DMA_ITConfig(DMA_Channel_TypeDef * DMA_Channelx, FunctionalState NewState);
FlagStatus DMA_GetChannelStatus(u8 ChannelIndx );
ITStatus DMA_GetITStatus(u8 ChannelIndx,u8 DMA_ITReq);
void DMA_ClearIT(u8 ChannelIndx,u8 DMA_ITClr);
void DMA_SyncConfig(u16 DMA_SrcReq, FunctionalState NewState);
FlagStatus DMA_GetSReq(u16 DMA_SrcReq);
FlagStatus DMA_GetLSReq(u16 DMA_SrcReq);
FlagStatus DMA_GetBReq(u16 DMA_SrcReq);
FlagStatus DMA_GetLBReq(u16 DMA_SrcReq);
FlagStatus DMA_GetChannelActiveStatus( DMA_Channel_TypeDef * DMA_Channelx);
void DMA_SetSReq(u16 DMA_SrcReq);
void DMA_SetLSReq(u16 DMA_SrcReq);
void DMA_SetBReq(u16 DMA_SrcReq);
void DMA_SetLBReq(u16 DMA_SrcReq);
void DMA_ChannelCmd (DMA_Channel_TypeDef * DMA_Channelx,FunctionalState NewState);
void DMA_ChannelHalt (DMA_Channel_TypeDef * DMA_Channelx,FunctionalState NewState);
void DMA_ChannelBuffering (DMA_Channel_TypeDef * DMA_Channelx,FunctionalState NewState);
void DMA_ChannelLockTrsf(DMA_Channel_TypeDef * DMA_Channelx,FunctionalState NewState);
void DMA_ChannelCache(DMA_Channel_TypeDef * DMA_Channelx,FunctionalState NewState);
void DMA_ChannelProt0Mode(DMA_Channel_TypeDef * DMA_Channelx,u32 Prot0Mode);
void DMA_ChannelSRCIncConfig (DMA_Channel_TypeDef * DMA_Channelx, FunctionalState NewState);
void DMA_ChannelDESIncConfig (DMA_Channel_TypeDef * DMA_Channelx, FunctionalState NewState);

#endif /* __91x_DMA_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
