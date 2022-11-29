/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2008/04/17 Revision: 0.2
 *
 * (c) Copyright UNIS, spol. s r.o. 1997-2008
 * UNIS, spol. s r.o.
 * Jundrovska 33
 * 624 00 Brno
 * Czech Republic
 * http      : www.processorexpert.com
 * mail      : info@processorexpert.com
 */

#ifndef __MCF52259_CANMB_H__
#define __MCF52259_CANMB_H__


/*********************************************************************
*
* Flex Controller Area Network Module (FlexCAN) message buffers
*
*********************************************************************/

/* Register read/write macros */
#define MCF_CANMB_CODE0                      (*(vuint8 *)(&__IPSBAR[0x170080]))
#define MCF_CANMB_CTRL0                      (*(vuint8 *)(&__IPSBAR[0x170081]))
#define MCF_CANMB_TIME0                      (*(vuint16*)(&__IPSBAR[0x170082]))
#define MCF_CANMB_ID0                        (*(vuint32*)(&__IPSBAR[0x170084]))
#define MCF_CANMB_DATA_WORD_1_0              (*(vuint16*)(&__IPSBAR[0x170088]))
#define MCF_CANMB_DATA_WORD_2_0              (*(vuint16*)(&__IPSBAR[0x17008A]))
#define MCF_CANMB_DATA_WORD_3_0              (*(vuint16*)(&__IPSBAR[0x17008C]))
#define MCF_CANMB_DATA_WORD_4_0              (*(vuint16*)(&__IPSBAR[0x17008E]))
#define MCF_CANMB_CODE1                      (*(vuint8 *)(&__IPSBAR[0x170090]))
#define MCF_CANMB_CTRL1                      (*(vuint8 *)(&__IPSBAR[0x170091]))
#define MCF_CANMB_TIME1                      (*(vuint16*)(&__IPSBAR[0x170092]))
#define MCF_CANMB_ID1                        (*(vuint32*)(&__IPSBAR[0x170094]))
#define MCF_CANMB_DATA_WORD_1_1              (*(vuint16*)(&__IPSBAR[0x170098]))
#define MCF_CANMB_DATA_WORD_2_1              (*(vuint16*)(&__IPSBAR[0x17009A]))
#define MCF_CANMB_DATA_WORD_3_1              (*(vuint16*)(&__IPSBAR[0x17009C]))
#define MCF_CANMB_DATA_WORD_4_1              (*(vuint16*)(&__IPSBAR[0x17009E]))
#define MCF_CANMB_CODE2                      (*(vuint8 *)(&__IPSBAR[0x1700A0]))
#define MCF_CANMB_CTRL2                      (*(vuint8 *)(&__IPSBAR[0x1700A1]))
#define MCF_CANMB_TIME2                      (*(vuint16*)(&__IPSBAR[0x1700A2]))
#define MCF_CANMB_ID2                        (*(vuint32*)(&__IPSBAR[0x1700A4]))
#define MCF_CANMB_DATA_WORD_1_2              (*(vuint16*)(&__IPSBAR[0x1700A8]))
#define MCF_CANMB_DATA_WORD_2_2              (*(vuint16*)(&__IPSBAR[0x1700AA]))
#define MCF_CANMB_DATA_WORD_3_2              (*(vuint16*)(&__IPSBAR[0x1700AC]))
#define MCF_CANMB_DATA_WORD_4_2              (*(vuint16*)(&__IPSBAR[0x1700AE]))
#define MCF_CANMB_CODE3                      (*(vuint8 *)(&__IPSBAR[0x1700B0]))
#define MCF_CANMB_CTRL3                      (*(vuint8 *)(&__IPSBAR[0x1700B1]))
#define MCF_CANMB_TIME3                      (*(vuint16*)(&__IPSBAR[0x1700B2]))
#define MCF_CANMB_ID3                        (*(vuint32*)(&__IPSBAR[0x1700B4]))
#define MCF_CANMB_DATA_WORD_1_3              (*(vuint16*)(&__IPSBAR[0x1700B8]))
#define MCF_CANMB_DATA_WORD_2_3              (*(vuint16*)(&__IPSBAR[0x1700BA]))
#define MCF_CANMB_DATA_WORD_3_3              (*(vuint16*)(&__IPSBAR[0x1700BC]))
#define MCF_CANMB_DATA_WORD_4_3              (*(vuint16*)(&__IPSBAR[0x1700BE]))
#define MCF_CANMB_CODE4                      (*(vuint8 *)(&__IPSBAR[0x1700C0]))
#define MCF_CANMB_CTRL4                      (*(vuint8 *)(&__IPSBAR[0x1700C1]))
#define MCF_CANMB_TIME4                      (*(vuint16*)(&__IPSBAR[0x1700C2]))
#define MCF_CANMB_ID4                        (*(vuint32*)(&__IPSBAR[0x1700C4]))
#define MCF_CANMB_DATA_WORD_1_4              (*(vuint16*)(&__IPSBAR[0x1700C8]))
#define MCF_CANMB_DATA_WORD_2_4              (*(vuint16*)(&__IPSBAR[0x1700CA]))
#define MCF_CANMB_DATA_WORD_3_4              (*(vuint16*)(&__IPSBAR[0x1700CC]))
#define MCF_CANMB_DATA_WORD_4_4              (*(vuint16*)(&__IPSBAR[0x1700CE]))
#define MCF_CANMB_CODE5                      (*(vuint8 *)(&__IPSBAR[0x1700D0]))
#define MCF_CANMB_CTRL5                      (*(vuint8 *)(&__IPSBAR[0x1700D1]))
#define MCF_CANMB_TIME5                      (*(vuint16*)(&__IPSBAR[0x1700D2]))
#define MCF_CANMB_ID5                        (*(vuint32*)(&__IPSBAR[0x1700D4]))
#define MCF_CANMB_DATA_WORD_1_5              (*(vuint16*)(&__IPSBAR[0x1700D8]))
#define MCF_CANMB_DATA_WORD_2_5              (*(vuint16*)(&__IPSBAR[0x1700DA]))
#define MCF_CANMB_DATA_WORD_3_5              (*(vuint16*)(&__IPSBAR[0x1700DC]))
#define MCF_CANMB_DATA_WORD_4_5              (*(vuint16*)(&__IPSBAR[0x1700DE]))
#define MCF_CANMB_CODE6                      (*(vuint8 *)(&__IPSBAR[0x1700E0]))
#define MCF_CANMB_CTRL6                      (*(vuint8 *)(&__IPSBAR[0x1700E1]))
#define MCF_CANMB_TIME6                      (*(vuint16*)(&__IPSBAR[0x1700E2]))
#define MCF_CANMB_ID6                        (*(vuint32*)(&__IPSBAR[0x1700E4]))
#define MCF_CANMB_DATA_WORD_1_6              (*(vuint16*)(&__IPSBAR[0x1700E8]))
#define MCF_CANMB_DATA_WORD_2_6              (*(vuint16*)(&__IPSBAR[0x1700EA]))
#define MCF_CANMB_DATA_WORD_3_6              (*(vuint16*)(&__IPSBAR[0x1700EC]))
#define MCF_CANMB_DATA_WORD_4_6              (*(vuint16*)(&__IPSBAR[0x1700EE]))
#define MCF_CANMB_CODE7                      (*(vuint8 *)(&__IPSBAR[0x1700F0]))
#define MCF_CANMB_CTRL7                      (*(vuint8 *)(&__IPSBAR[0x1700F1]))
#define MCF_CANMB_TIME7                      (*(vuint16*)(&__IPSBAR[0x1700F2]))
#define MCF_CANMB_ID7                        (*(vuint32*)(&__IPSBAR[0x1700F4]))
#define MCF_CANMB_DATA_WORD_1_7              (*(vuint16*)(&__IPSBAR[0x1700F8]))
#define MCF_CANMB_DATA_WORD_2_7              (*(vuint16*)(&__IPSBAR[0x1700FA]))
#define MCF_CANMB_DATA_WORD_3_7              (*(vuint16*)(&__IPSBAR[0x1700FC]))
#define MCF_CANMB_DATA_WORD_4_7              (*(vuint16*)(&__IPSBAR[0x1700FE]))
#define MCF_CANMB_CODE8                      (*(vuint8 *)(&__IPSBAR[0x170100]))
#define MCF_CANMB_CTRL8                      (*(vuint8 *)(&__IPSBAR[0x170101]))
#define MCF_CANMB_TIME8                      (*(vuint16*)(&__IPSBAR[0x170102]))
#define MCF_CANMB_ID8                        (*(vuint32*)(&__IPSBAR[0x170104]))
#define MCF_CANMB_DATA_WORD_1_8              (*(vuint16*)(&__IPSBAR[0x170108]))
#define MCF_CANMB_DATA_WORD_2_8              (*(vuint16*)(&__IPSBAR[0x17010A]))
#define MCF_CANMB_DATA_WORD_3_8              (*(vuint16*)(&__IPSBAR[0x17010C]))
#define MCF_CANMB_DATA_WORD_4_8              (*(vuint16*)(&__IPSBAR[0x17010E]))
#define MCF_CANMB_CODE9                      (*(vuint8 *)(&__IPSBAR[0x170110]))
#define MCF_CANMB_CTRL9                      (*(vuint8 *)(&__IPSBAR[0x170111]))
#define MCF_CANMB_TIME9                      (*(vuint16*)(&__IPSBAR[0x170112]))
#define MCF_CANMB_ID9                        (*(vuint32*)(&__IPSBAR[0x170114]))
#define MCF_CANMB_DATA_WORD_1_9              (*(vuint16*)(&__IPSBAR[0x170118]))
#define MCF_CANMB_DATA_WORD_2_9              (*(vuint16*)(&__IPSBAR[0x17011A]))
#define MCF_CANMB_DATA_WORD_3_9              (*(vuint16*)(&__IPSBAR[0x17011C]))
#define MCF_CANMB_DATA_WORD_4_9              (*(vuint16*)(&__IPSBAR[0x17011E]))
#define MCF_CANMB_CODE10                     (*(vuint8 *)(&__IPSBAR[0x170120]))
#define MCF_CANMB_CTRL10                     (*(vuint8 *)(&__IPSBAR[0x170121]))
#define MCF_CANMB_TIME10                     (*(vuint16*)(&__IPSBAR[0x170122]))
#define MCF_CANMB_ID10                       (*(vuint32*)(&__IPSBAR[0x170124]))
#define MCF_CANMB_DATA_WORD_1_10             (*(vuint16*)(&__IPSBAR[0x170128]))
#define MCF_CANMB_DATA_WORD_2_10             (*(vuint16*)(&__IPSBAR[0x17012A]))
#define MCF_CANMB_DATA_WORD_3_10             (*(vuint16*)(&__IPSBAR[0x17012C]))
#define MCF_CANMB_DATA_WORD_4_10             (*(vuint16*)(&__IPSBAR[0x17012E]))
#define MCF_CANMB_CODE11                     (*(vuint8 *)(&__IPSBAR[0x170130]))
#define MCF_CANMB_CTRL11                     (*(vuint8 *)(&__IPSBAR[0x170131]))
#define MCF_CANMB_TIME11                     (*(vuint16*)(&__IPSBAR[0x170132]))
#define MCF_CANMB_ID11                       (*(vuint32*)(&__IPSBAR[0x170134]))
#define MCF_CANMB_DATA_WORD_1_11             (*(vuint16*)(&__IPSBAR[0x170138]))
#define MCF_CANMB_DATA_WORD_2_11             (*(vuint16*)(&__IPSBAR[0x17013A]))
#define MCF_CANMB_DATA_WORD_3_11             (*(vuint16*)(&__IPSBAR[0x17013C]))
#define MCF_CANMB_DATA_WORD_4_11             (*(vuint16*)(&__IPSBAR[0x17013E]))
#define MCF_CANMB_CODE12                     (*(vuint8 *)(&__IPSBAR[0x170140]))
#define MCF_CANMB_CTRL12                     (*(vuint8 *)(&__IPSBAR[0x170141]))
#define MCF_CANMB_TIME12                     (*(vuint16*)(&__IPSBAR[0x170142]))
#define MCF_CANMB_ID12                       (*(vuint32*)(&__IPSBAR[0x170144]))
#define MCF_CANMB_DATA_WORD_1_               (*(vuint16*)(&__IPSBAR[0x170148]))
#define MCF_CANMB_DATA_WORD_2_12             (*(vuint16*)(&__IPSBAR[0x17014A]))
#define MCF_CANMB_DATA_WORD_3_12             (*(vuint16*)(&__IPSBAR[0x17014C]))
#define MCF_CANMB_DATA_WORD_4_12             (*(vuint16*)(&__IPSBAR[0x17014E]))
#define MCF_CANMB_CODE13                     (*(vuint8 *)(&__IPSBAR[0x170150]))
#define MCF_CANMB_CTRL13                     (*(vuint8 *)(&__IPSBAR[0x170151]))
#define MCF_CANMB_TIME13                     (*(vuint16*)(&__IPSBAR[0x170152]))
#define MCF_CANMB_ID13                       (*(vuint32*)(&__IPSBAR[0x170154]))
#define MCF_CANMB_DATA_WORD_1_13             (*(vuint16*)(&__IPSBAR[0x170158]))
#define MCF_CANMB_DATA_WORD_2_13             (*(vuint16*)(&__IPSBAR[0x17015A]))
#define MCF_CANMB_DATA_WORD_3_13             (*(vuint16*)(&__IPSBAR[0x17015C]))
#define MCF_CANMB_DATA_WORD_4_13             (*(vuint16*)(&__IPSBAR[0x17015E]))
#define MCF_CANMB_CODE14                     (*(vuint8 *)(&__IPSBAR[0x170160]))
#define MCF_CANMB_CTRL14                     (*(vuint8 *)(&__IPSBAR[0x170161]))
#define MCF_CANMB_TIME14                     (*(vuint16*)(&__IPSBAR[0x170162]))
#define MCF_CANMB_ID14                       (*(vuint32*)(&__IPSBAR[0x170164]))
#define MCF_CANMB_DATA_WORD_1_14             (*(vuint16*)(&__IPSBAR[0x170168]))
#define MCF_CANMB_DATA_WORD_2_14             (*(vuint16*)(&__IPSBAR[0x17016A]))
#define MCF_CANMB_DATA_WORD_3_14             (*(vuint16*)(&__IPSBAR[0x17016C]))
#define MCF_CANMB_DATA_WORD_4_14             (*(vuint16*)(&__IPSBAR[0x17016E]))
#define MCF_CANMB_CODE15                     (*(vuint8 *)(&__IPSBAR[0x170170]))
#define MCF_CANMB_CTRL15                     (*(vuint8 *)(&__IPSBAR[0x170171]))
#define MCF_CANMB_TIME15                     (*(vuint16*)(&__IPSBAR[0x170172]))
#define MCF_CANMB_ID15                       (*(vuint32*)(&__IPSBAR[0x170174]))
#define MCF_CANMB_DATA_WORD_1_15             (*(vuint16*)(&__IPSBAR[0x170178]))
#define MCF_CANMB_DATA_WORD_2_15             (*(vuint16*)(&__IPSBAR[0x17017A]))
#define MCF_CANMB_DATA_WORD_3_15             (*(vuint16*)(&__IPSBAR[0x17017C]))
#define MCF_CANMB_DATA_WORD_4_15             (*(vuint16*)(&__IPSBAR[0x17017E]))
#define MCF_CANMB_CODE(x)                    (*(vuint8 *)(&__IPSBAR[0x170080 + ((x)*0x10)]))
#define MCF_CANMB_CTRL(x)                    (*(vuint8 *)(&__IPSBAR[0x170081 + ((x)*0x10)]))
#define MCF_CANMB_TIME(x)                    (*(vuint16*)(&__IPSBAR[0x170082 + ((x)*0x10)]))
#define MCF_CANMB_ID(x)                      (*(vuint32*)(&__IPSBAR[0x170084 + ((x)*0x10)]))
#define MCF_CANMB_DATA_WORD_1(x)             (*(vuint16*)(&__IPSBAR[0x170088 + ((x)*0x10)]))
#define MCF_CANMB_DATA_WORD_2(x)             (*(vuint16*)(&__IPSBAR[0x17008A + ((x)*0x10)]))
#define MCF_CANMB_DATA_WORD_3(x)             (*(vuint16*)(&__IPSBAR[0x17008C + ((x)*0x10)]))
#define MCF_CANMB_DATA_WORD_4(x)             (*(vuint16*)(&__IPSBAR[0x17008E + ((x)*0x10)]))


/* Other macros */
#define MCF_CANMB_BYTE(x,y)                  (*(vuint8 *)(&__IPSBAR[((0x170088 + ((x)*0x10)+y))]))


/* Bit definitions and macros for MCF_CANMB_CODE */
#define MCF_CANMB_CODE_CODE(x)               (((x)&0xF)<<0)

/* Bit definitions and macros for MCF_CANMB_CTRL */
#define MCF_CANMB_CTRL_LENGTH(x)             (((x)&0xF)<<0)
#define MCF_CANMB_CTRL_RTR                   (0x10)
#define MCF_CANMB_CTRL_IDE                   (0x20)
#define MCF_CANMB_CTRL_SRR                   (0x40)

/* Bit definitions and macros for MCF_CANMB_TIME */
#define MCF_CANMB_TIME_TIME_STAMP(x)         (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_CANMB_ID */
#define MCF_CANMB_ID_EXT(x)                  (((x)&0x3FFFF)<<0)
#define MCF_CANMB_ID_STD(x)                  (((x)&0x7FF)<<0x12)

/* Bit definitions and macros for MCF_CANMB_DATA_WORD_1 */
#define MCF_CANMB_DATA_WORD_1_DATA_BYTE_1(x) (((x)&0xFF)<<0)
#define MCF_CANMB_DATA_WORD_1_DATA_BYTE_0(x) (((x)&0xFF)<<0x8)

/* Bit definitions and macros for MCF_CANMB_DATA_WORD_2 */
#define MCF_CANMB_DATA_WORD_2_DATA_BYTE_3(x) (((x)&0xFF)<<0)
#define MCF_CANMB_DATA_WORD_2_DATA_BYTE_2(x) (((x)&0xFF)<<0x8)

/* Bit definitions and macros for MCF_CANMB_DATA_WORD_3 */
#define MCF_CANMB_DATA_WORD_3_DATA_BYTE_5(x) (((x)&0xFF)<<0)
#define MCF_CANMB_DATA_WORD_3_DATA_BYTE_4(x) (((x)&0xFF)<<0x8)

/* Bit definitions and macros for MCF_CANMB_DATA_WORD_4 */
#define MCF_CANMB_DATA_WORD_4_DATA_BYTE_7(x) (((x)&0xFF)<<0)
#define MCF_CANMB_DATA_WORD_4_DATA_BYTE_6(x) (((x)&0xFF)<<0x8)


#endif /* __MCF52259_CANMB_H__ */
