/*----------------------------------------------------------------------------
 *      U S B  -  K e r n e l
 *----------------------------------------------------------------------------
 *      Name:    cdcuser.h
 *      Purpose: USB Communication Device Class User module Definitions
 *      Version: V1.10
 *----------------------------------------------------------------------------
 *      This software is supplied "AS IS" without any warranties, express,
 *      implied or statutory, including but not limited to the implied
 *      warranties of fitness for purpose, satisfactory quality and
 *      noninfringement. Keil extends you a royalty-free right to reproduce
 *      and distribute executable files created using this software for use
 *      on NXP Semiconductors LPC microcontroller devices only. Nothing else
 *      gives you the right to use this software.
 *
 * Copyright (c) 2009 Keil - An ARM Company. All rights reserved.
 *---------------------------------------------------------------------------*/

#ifndef __CDCUSER_H__
#define __CDCUSER_H__

/* CDC buffer handling */
extern int CDC_RdOutBuf        (char *buffer, const int *length);
extern int CDC_WrOutBuf        (const char *buffer, int length);
extern int CDC_OutBufAvailChar (int *availChar);
extern void CDC_WaitNewData    ( void );


/* CDC Data In/Out Endpoint Address */
#define CDC_DEP_IN       0x82
#define CDC_DEP_OUT      0x02

/* CDC Communication In Endpoint Address */
#define CDC_CEP_IN       0x81

/* CDC Requests Callback Functions */
extern uint32_t CDC_SendEncapsulatedCommand  (void);
extern uint32_t CDC_GetEncapsulatedResponse  (void);
extern uint32_t CDC_SetCommFeature           (unsigned short wFeatureSelector);
extern uint32_t CDC_GetCommFeature           (unsigned short wFeatureSelector);
extern uint32_t CDC_ClearCommFeature         (unsigned short wFeatureSelector);
extern uint32_t CDC_GetLineCoding            (void);
extern uint32_t CDC_SetLineCoding            (void);
extern uint32_t CDC_SetControlLineState      (unsigned short wControlSignalBitmap);
extern uint32_t CDC_SendBreak                (unsigned short wDurationOfBreak);

/* CDC Bulk Callback Functions */
extern void CDC_BulkIn                   (void);
extern void CDC_BulkOut                  (void);
extern void CDC_BulkOutNak				 (void);

/* CDC Notification Callback Function */
extern void CDC_NotificationIn           (void);

/* CDC Initializtion Function */
extern void CDC_Init (char portNum);

/* CDC prepare the SERAIAL_STATE */
extern unsigned short CDC_GetSerialState (void);

/* CDC New data Notification Function */
extern void vCDCNewDataNotify();

/* flow control */
extern unsigned short CDC_DepInEmpty;         // DataEndPoint IN empty

#endif  /* __CDCUSER_H__ */

