/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.9
 */

#ifndef __MCF5282_PAD_H__
#define __MCF5282_PAD_H__


/*********************************************************************
*
* Common GPIO Registers
*
*********************************************************************/

/* Register read/write macros */
#define MCF_PAD_PBCDPAR                      (*(vuint8 *)(&__IPSBAR[0x100050]))
#define MCF_PAD_PFPAR                        (*(vuint8 *)(&__IPSBAR[0x100051]))
#define MCF_PAD_PEPAR                        (*(vuint16*)(&__IPSBAR[0x100052]))
#define MCF_PAD_PJPAR                        (*(vuint8 *)(&__IPSBAR[0x100054]))
#define MCF_PAD_PSDPAR                       (*(vuint8 *)(&__IPSBAR[0x100055]))
#define MCF_PAD_PASPAR                       (*(vuint16*)(&__IPSBAR[0x100056]))
#define MCF_PAD_PEHLPAR                      (*(vuint8 *)(&__IPSBAR[0x100058]))
#define MCF_PAD_PQSPAR                       (*(vuint8 *)(&__IPSBAR[0x100059]))
#define MCF_PAD_PTCPAR                       (*(vuint8 *)(&__IPSBAR[0x10005A]))
#define MCF_PAD_PTDPAR                       (*(vuint8 *)(&__IPSBAR[0x10005B]))
#define MCF_PAD_PUAPAR                       (*(vuint8 *)(&__IPSBAR[0x10005C]))


/* Bit definitions and macros for MCF_PAD_PBCDPAR */
#define MCF_PAD_PBCDPAR_PCDPA                (0x40)
#define MCF_PAD_PBCDPAR_PBPA                 (0x80)

/* Bit definitions and macros for MCF_PAD_PFPAR */
#define MCF_PAD_PFPAR_PFPA5                  (0x20)
#define MCF_PAD_PFPAR_PFPA6                  (0x40)
#define MCF_PAD_PFPAR_PFPA7                  (0x80)

/* Bit definitions and macros for MCF_PAD_PEPAR */
#define MCF_PAD_PEPAR_PEPA0(x)               (((x)&0x3)<<0)
#define MCF_PAD_PEPAR_PEPA0_GPIO             (0)
#define MCF_PAD_PEPAR_PEPA0_SYNCB            (0x2)
#define MCF_PAD_PEPAR_PEPA0_TIP              (0x3)
#define MCF_PAD_PEPAR_PEPA1(x)               (((x)&0x3)<<0x2)
#define MCF_PAD_PEPAR_PEPA1_GPIO             (0)
#define MCF_PAD_PEPAR_PEPA1_SYNCA            (0x8)
#define MCF_PAD_PEPAR_PEPA1_TS               (0xC)
#define MCF_PAD_PEPAR_PEPA2                  (0x10)
#define MCF_PAD_PEPAR_PEPA3                  (0x40)
#define MCF_PAD_PEPAR_PEPA4                  (0x100)
#define MCF_PAD_PEPAR_PEPA5                  (0x400)
#define MCF_PAD_PEPAR_PEPA6                  (0x1000)
#define MCF_PAD_PEPAR_PEPA7                  (0x4000)

/* Bit definitions and macros for MCF_PAD_PJPAR */
#define MCF_PAD_PJPAR_PJPA0                  (0x1)
#define MCF_PAD_PJPAR_PJPA1                  (0x2)
#define MCF_PAD_PJPAR_PJPA2                  (0x4)
#define MCF_PAD_PJPAR_PJPA3                  (0x8)
#define MCF_PAD_PJPAR_PJPA4                  (0x10)
#define MCF_PAD_PJPAR_PJPA5                  (0x20)
#define MCF_PAD_PJPAR_PJPA6                  (0x40)
#define MCF_PAD_PJPAR_PJPA7                  (0x80)

/* Bit definitions and macros for MCF_PAD_PSDPAR */
#define MCF_PAD_PSDPAR_PSDPA                 (0x80)

/* Bit definitions and macros for MCF_PAD_PASPAR */
#define MCF_PAD_PASPAR_PASPA0(x)             (((x)&0x3)<<0)
#define MCF_PAD_PASPAR_PASPA0_GPIO           (0)
#define MCF_PAD_PASPAR_PASPA0_UTXD2          (0x2)
#define MCF_PAD_PASPAR_PASPA0_SCL            (0x3)
#define MCF_PAD_PASPAR_PASPA1(x)             (((x)&0x3)<<0x2)
#define MCF_PAD_PASPAR_PASPA1_GPIO           (0)
#define MCF_PAD_PASPAR_PASPA1_URXD2          (0x8)
#define MCF_PAD_PASPAR_PASPA1_SDA            (0xC)
#define MCF_PAD_PASPAR_PASPA2(x)             (((x)&0x3)<<0x4)
#define MCF_PAD_PASPAR_PASPA2_GPIO           (0)
#define MCF_PAD_PASPAR_PASPA2_UTXD2          (0x20)
#define MCF_PAD_PASPAR_PASPA2_CANTX          (0x30)
#define MCF_PAD_PASPAR_PASPA3(x)             (((x)&0x3)<<0x6)
#define MCF_PAD_PASPAR_PASPA3_GPIO           (0)
#define MCF_PAD_PASPAR_PASPA3_URXD2          (0x80)
#define MCF_PAD_PASPAR_PASPA3_CANRX          (0xC0)
#define MCF_PAD_PASPAR_PASPA4(x)             (((x)&0x3)<<0x8)
#define MCF_PAD_PASPAR_PASPA4_GPIO           (0)
#define MCF_PAD_PASPAR_PASPA4_UTXD2          (0x200)
#define MCF_PAD_PASPAR_PASPA4_EMDC           (0x300)
#define MCF_PAD_PASPAR_PASPA5(x)             (((x)&0x3)<<0xA)
#define MCF_PAD_PASPAR_PASPA5_GPIO           (0)
#define MCF_PAD_PASPAR_PASPA5_URXD2          (0x800)
#define MCF_PAD_PASPAR_PASPA5_EMDIO          (0xC00)

/* Bit definitions and macros for MCF_PAD_PEHLPAR */
#define MCF_PAD_PEHLPAR_PELPA                (0x40)
#define MCF_PAD_PEHLPAR_PEHPA                (0x80)

/* Bit definitions and macros for MCF_PAD_PQSPAR */
#define MCF_PAD_PQSPAR_PQSPA0                (0x1)
#define MCF_PAD_PQSPAR_PQSPA1                (0x2)
#define MCF_PAD_PQSPAR_PQSPA2                (0x4)
#define MCF_PAD_PQSPAR_PQSPA3                (0x8)
#define MCF_PAD_PQSPAR_PQSPA4                (0x10)
#define MCF_PAD_PQSPAR_PQSPA5                (0x20)
#define MCF_PAD_PQSPAR_PQSPA6                (0x40)

/* Bit definitions and macros for MCF_PAD_PTCPAR */
#define MCF_PAD_PTCPAR_PTCPA0(x)             (((x)&0x3)<<0)
#define MCF_PAD_PTCPAR_PTCPA0_GPIO           (0)
#define MCF_PAD_PTCPAR_PTCPA0_UCTS0          (0x1)
#define MCF_PAD_PTCPAR_PTCPA0_UCTS1          (0x2)
#define MCF_PAD_PTCPAR_PTCPA0_TOUT2          (0x3)
#define MCF_PAD_PTCPAR_PTCPA1(x)             (((x)&0x3)<<0x2)
#define MCF_PAD_PTCPAR_PTCPA1_GPIO           (0)
#define MCF_PAD_PTCPAR_PTCPA1_UCTS0          (0x4)
#define MCF_PAD_PTCPAR_PTCPA1_UCTS1          (0x8)
#define MCF_PAD_PTCPAR_PTCPA1_TIN2           (0xC)
#define MCF_PAD_PTCPAR_PTCPA2(x)             (((x)&0x3)<<0x4)
#define MCF_PAD_PTCPAR_PTCPA2_GPIO           (0)
#define MCF_PAD_PTCPAR_PTCPA2_URTS0          (0x10)
#define MCF_PAD_PTCPAR_PTCPA2_URTS1          (0x20)
#define MCF_PAD_PTCPAR_PTCPA2_TOUT3          (0x30)
#define MCF_PAD_PTCPAR_PTCPA3(x)             (((x)&0x3)<<0x6)
#define MCF_PAD_PTCPAR_PTCPA3_GPIO           (0)
#define MCF_PAD_PTCPAR_PTCPA3_URTS0          (0x40)
#define MCF_PAD_PTCPAR_PTCPA3_URTS1          (0x80)
#define MCF_PAD_PTCPAR_PTCPA3_TIN3           (0xC0)

/* Bit definitions and macros for MCF_PAD_PTDPAR */
#define MCF_PAD_PTDPAR_PTDPA0(x)             (((x)&0x3)<<0)
#define MCF_PAD_PTDPAR_PTDPA0_GPIO           (0)
#define MCF_PAD_PTDPAR_PTDPA0_UCTS0          (0x1)
#define MCF_PAD_PTDPAR_PTDPA0_UCTS1          (0x2)
#define MCF_PAD_PTDPAR_PTDPA0_TOUT0          (0x3)
#define MCF_PAD_PTDPAR_PTDPA1(x)             (((x)&0x3)<<0x2)
#define MCF_PAD_PTDPAR_PTDPA2_GPIO           (0)
#define MCF_PAD_PTDPAR_PTDPA2_UCTS0          (0x4)
#define MCF_PAD_PTDPAR_PTDPA2_UCTS1          (0x8)
#define MCF_PAD_PTDPAR_PTDPA2_TIN0           (0xC)
#define MCF_PAD_PTDPAR_PTDPA2(x)             (((x)&0x3)<<0x4)
#define MCF_PAD_PTDPAR_PTDPA2_URTS0          (0x10)
#define MCF_PAD_PTDPAR_PTDPA2_URTS1          (0x20)
#define MCF_PAD_PTDPAR_PTDPA2_TOUT1          (0x30)
#define MCF_PAD_PTDPAR_PTDPA3(x)             (((x)&0x3)<<0x6)
#define MCF_PAD_PTDPAR_PTDPA3_GPIO           (0)
#define MCF_PAD_PTDPAR_PTDPA3_URTS0          (0x40)
#define MCF_PAD_PTDPAR_PTDPA3_URTS1          (0x80)
#define MCF_PAD_PTDPAR_PTDPA3_TIN1           (0xC0)

/* Bit definitions and macros for MCF_PAD_PUAPAR */
#define MCF_PAD_PUAPAR_PUAPA0                (0x1)
#define MCF_PAD_PUAPAR_PUAPA1                (0x2)
#define MCF_PAD_PUAPAR_PUAPA2                (0x4)
#define MCF_PAD_PUAPAR_PUAPA3                (0x8)


#endif /* __MCF5282_PAD_H__ */
