/*********************************************************************** 
 * $Id: dma.h 8242 2011-10-11 15:15:25Z nxp28536 $
 * 
 * Project: LPC43xx Validation
 * 
 * Description: DMA Test
 * 
 * Copyright(C) 2010, NXP Semiconductor
 * All rights reserved.
 * 
 ***********************************************************************
 * Software that is described herein is for illustrative purposes only  
 * which provides customers with programming information regarding the  
 * products. This software is supplied "AS IS" without any warranties.  
 * NXP Semiconductors assumes no responsibility or liability for the 
 * use of the software, conveys no license or title under any patent, 
 * copyright, or mask work right to the product. NXP Semiconductors 
 * reserves the right to make changes in the software without 
 * notification. NXP Semiconductors also make no representation or 
 * warranty that such application will be suitable for the specified 
 * use without further testing or modification. 
 **********************************************************************/
#ifndef __DMA_H 
#define __DMA_H

#define DMA_SIZE		0x1000

#define M2M				0x00
#define M2P				0x01
#define P2M				0x02
#define P2P				0x03

extern void DMA_IRQHandler (void);
extern uint32_t DMA_Init_Matrix( uint32_t u32SrcAddr );

typedef struct _LinkedList {
    DWORD   SRC;
    DWORD   DST;  		
    DWORD   LLI;
    DWORD   CTRL;
}LinkedList;

#endif /* end __DMA_H */
/****************************************************************************
**                            End Of File
****************************************************************************/
