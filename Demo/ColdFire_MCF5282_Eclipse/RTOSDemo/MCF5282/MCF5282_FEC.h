/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.9
 */

#ifndef __MCF5282_FEC_H__
#define __MCF5282_FEC_H__


/*********************************************************************
*
* Fast Ethernet Controller(FEC)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_FEC_EIR                          (*(vuint32*)(&__IPSBAR[0x1004]))
#define MCF_FEC_EIMR                         (*(vuint32*)(&__IPSBAR[0x1008]))
#define MCF_FEC_RDAR                         (*(vuint32*)(&__IPSBAR[0x1010]))
#define MCF_FEC_TDAR                         (*(vuint32*)(&__IPSBAR[0x1014]))
#define MCF_FEC_ECR                          (*(vuint32*)(&__IPSBAR[0x1024]))
#define MCF_FEC_MMFR                         (*(vuint32*)(&__IPSBAR[0x1040]))
#define MCF_FEC_MSCR                         (*(vuint32*)(&__IPSBAR[0x1044]))
#define MCF_FEC_MIBC                         (*(vuint32*)(&__IPSBAR[0x1064]))
#define MCF_FEC_RCR                          (*(vuint32*)(&__IPSBAR[0x1084]))
#define MCF_FEC_TCR                          (*(vuint32*)(&__IPSBAR[0x10C4]))
#define MCF_FEC_PALR                         (*(vuint32*)(&__IPSBAR[0x10E4]))
#define MCF_FEC_PAUR                         (*(vuint32*)(&__IPSBAR[0x10E8]))
#define MCF_FEC_OPD                          (*(vuint32*)(&__IPSBAR[0x10EC]))
#define MCF_FEC_IAUR                         (*(vuint32*)(&__IPSBAR[0x1118]))
#define MCF_FEC_IALR                         (*(vuint32*)(&__IPSBAR[0x111C]))
#define MCF_FEC_GAUR                         (*(vuint32*)(&__IPSBAR[0x1120]))
#define MCF_FEC_GALR                         (*(vuint32*)(&__IPSBAR[0x1124]))
#define MCF_FEC_TFWR                         (*(vuint32*)(&__IPSBAR[0x1144]))
#define MCF_FEC_FRBR                         (*(vuint32*)(&__IPSBAR[0x114C]))
#define MCF_FEC_FRSR                         (*(vuint32*)(&__IPSBAR[0x1150]))
#define MCF_FEC_ERDSR                        (*(vuint32*)(&__IPSBAR[0x1180]))
#define MCF_FEC_ETSDR                        (*(vuint32*)(&__IPSBAR[0x1184]))
#define MCF_FEC_EMRBR                        (*(vuint32*)(&__IPSBAR[0x1188]))
#define MCF_FEC_RMON_T_DROP                  (*(vuint32*)(&__IPSBAR[0x1200]))
#define MCF_FEC_RMON_T_PACKETS               (*(vuint32*)(&__IPSBAR[0x1204]))
#define MCF_FEC_RMON_T_BC_PKT                (*(vuint32*)(&__IPSBAR[0x1208]))
#define MCF_FEC_RMON_T_MC_PKT                (*(vuint32*)(&__IPSBAR[0x120C]))
#define MCF_FEC_RMON_T_CRC_ALIGN             (*(vuint32*)(&__IPSBAR[0x1210]))
#define MCF_FEC_RMON_T_UNDERSIZE             (*(vuint32*)(&__IPSBAR[0x1214]))
#define MCF_FEC_RMON_T_OVERSIZE              (*(vuint32*)(&__IPSBAR[0x1218]))
#define MCF_FEC_RMON_T_FRAG                  (*(vuint32*)(&__IPSBAR[0x121C]))
#define MCF_FEC_RMON_T_JAB                   (*(vuint32*)(&__IPSBAR[0x1220]))
#define MCF_FEC_RMON_T_COL                   (*(vuint32*)(&__IPSBAR[0x1224]))
#define MCF_FEC_RMON_T_P64                   (*(vuint32*)(&__IPSBAR[0x1228]))
#define MCF_FEC_RMON_T_P65TO127              (*(vuint32*)(&__IPSBAR[0x122C]))
#define MCF_FEC_RMON_T_P128TO255             (*(vuint32*)(&__IPSBAR[0x1230]))
#define MCF_FEC_RMON_T_P256TO511             (*(vuint32*)(&__IPSBAR[0x1234]))
#define MCF_FEC_RMON_T_P512TO1023            (*(vuint32*)(&__IPSBAR[0x1238]))
#define MCF_FEC_RMON_T_P1024TO2047           (*(vuint32*)(&__IPSBAR[0x123C]))
#define MCF_FEC_RMON_T_P_GTE2048             (*(vuint32*)(&__IPSBAR[0x1240]))
#define MCF_FEC_RMON_T_OCTETS                (*(vuint32*)(&__IPSBAR[0x1244]))
#define MCF_FEC_IEEE_T_DROP                  (*(vuint32*)(&__IPSBAR[0x1248]))
#define MCF_FEC_IEEE_T_FRAME_OK              (*(vuint32*)(&__IPSBAR[0x124C]))
#define MCF_FEC_IEEE_T_1COL                  (*(vuint32*)(&__IPSBAR[0x1250]))
#define MCF_FEC_IEEE_T_MCOL                  (*(vuint32*)(&__IPSBAR[0x1254]))
#define MCF_FEC_IEEE_T_DEF                   (*(vuint32*)(&__IPSBAR[0x1258]))
#define MCF_FEC_IEEE_T_LCOL                  (*(vuint32*)(&__IPSBAR[0x125C]))
#define MCF_FEC_IEEE_T_EXCOL                 (*(vuint32*)(&__IPSBAR[0x1260]))
#define MCF_FEC_IEEE_T_MACERR                (*(vuint32*)(&__IPSBAR[0x1264]))
#define MCF_FEC_IEEE_T_CSERR                 (*(vuint32*)(&__IPSBAR[0x1268]))
#define MCF_FEC_IEEE_T_SQE                   (*(vuint32*)(&__IPSBAR[0x126C]))
#define MCF_FEC_IEEE_T_FDXFC                 (*(vuint32*)(&__IPSBAR[0x1270]))
#define MCF_FEC_IEEE_T_OCTETS_OK             (*(vuint32*)(&__IPSBAR[0x1274]))
#define MCF_FEC_RMON_R_PACKETS               (*(vuint32*)(&__IPSBAR[0x1284]))
#define MCF_FEC_RMON_R_BC_PKT                (*(vuint32*)(&__IPSBAR[0x1288]))
#define MCF_FEC_RMON_R_MC_PKT                (*(vuint32*)(&__IPSBAR[0x128C]))
#define MCF_FEC_RMON_R_CRC_ALIGN             (*(vuint32*)(&__IPSBAR[0x1290]))
#define MCF_FEC_RMON_R_UNDERSIZE             (*(vuint32*)(&__IPSBAR[0x1294]))
#define MCF_FEC_RMON_R_OVERSIZE              (*(vuint32*)(&__IPSBAR[0x1298]))
#define MCF_FEC_RMON_R_FRAG                  (*(vuint32*)(&__IPSBAR[0x129C]))
#define MCF_FEC_RMON_R_JAB                   (*(vuint32*)(&__IPSBAR[0x12A0]))
#define MCF_FEC_RMON_R_RESVD_0               (*(vuint32*)(&__IPSBAR[0x12A4]))
#define MCF_FEC_RMON_R_P64                   (*(vuint32*)(&__IPSBAR[0x12A8]))
#define MCF_FEC_RMON_R_P65TO127              (*(vuint32*)(&__IPSBAR[0x12AC]))
#define MCF_FEC_RMON_R_P128TO255             (*(vuint32*)(&__IPSBAR[0x12B0]))
#define MCF_FEC_RMON_R_P256TO511             (*(vuint32*)(&__IPSBAR[0x12B4]))
#define MCF_FEC_RMON_R_P512TO1023            (*(vuint32*)(&__IPSBAR[0x12B8]))
#define MCF_FEC_RMON_R_P1024TO2047           (*(vuint32*)(&__IPSBAR[0x12BC]))
#define MCF_FEC_RMON_R_P_GTE2048             (*(vuint32*)(&__IPSBAR[0x12C0]))
#define MCF_FEC_RMON_R_OCTETS                (*(vuint32*)(&__IPSBAR[0x12C4]))
#define MCF_FEC_IEEE_R_DROP                  (*(vuint32*)(&__IPSBAR[0x12C8]))
#define MCF_FEC_IEEE_R_FRAME_OK              (*(vuint32*)(&__IPSBAR[0x12CC]))
#define MCF_FEC_IEEE_R_CRC                   (*(vuint32*)(&__IPSBAR[0x12D0]))
#define MCF_FEC_IEEE_R_ALIGN                 (*(vuint32*)(&__IPSBAR[0x12D4]))
#define MCF_FEC_IEEE_R_MACERR                (*(vuint32*)(&__IPSBAR[0x12D8]))
#define MCF_FEC_IEEE_R_FDXFC                 (*(vuint32*)(&__IPSBAR[0x12DC]))
#define MCF_FEC_IEEE_R_OCTETS_OK             (*(vuint32*)(&__IPSBAR[0x12E0]))



/* Bit definitions and macros for MCF_FEC_EIR */
#define MCF_FEC_EIR_UN                       (0x80000)
#define MCF_FEC_EIR_RL                       (0x100000)
#define MCF_FEC_EIR_LC                       (0x200000)
#define MCF_FEC_EIR_EBERR                    (0x400000)
#define MCF_FEC_EIR_MII                      (0x800000)
#define MCF_FEC_EIR_RXB                      (0x1000000)
#define MCF_FEC_EIR_RXF                      (0x2000000)
#define MCF_FEC_EIR_TXB                      (0x4000000)
#define MCF_FEC_EIR_TXF                      (0x8000000)
#define MCF_FEC_EIR_GRA                      (0x10000000)
#define MCF_FEC_EIR_BABT                     (0x20000000)
#define MCF_FEC_EIR_BABR                     (0x40000000)
#define MCF_FEC_EIR_HBERR                    (0x80000000)
#define MCF_FEC_EIR_CLEAR_ALL                (0xFFFFFFFF)

/* Bit definitions and macros for MCF_FEC_EIMR */
#define MCF_FEC_EIMR_UN                      (0x80000)
#define MCF_FEC_EIMR_RL                      (0x100000)
#define MCF_FEC_EIMR_LC                      (0x200000)
#define MCF_FEC_EIMR_EBERR                   (0x400000)
#define MCF_FEC_EIMR_MII                     (0x800000)
#define MCF_FEC_EIMR_RXB                     (0x1000000)
#define MCF_FEC_EIMR_RXF                     (0x2000000)
#define MCF_FEC_EIMR_TXB                     (0x4000000)
#define MCF_FEC_EIMR_TXF                     (0x8000000)
#define MCF_FEC_EIMR_GRA                     (0x10000000)
#define MCF_FEC_EIMR_BABT                    (0x20000000)
#define MCF_FEC_EIMR_BABR                    (0x40000000)
#define MCF_FEC_EIMR_HBERR                   (0x80000000)
#define MCF_FEC_EIMR_MASK_ALL                (0)
#define MCF_FEC_EIMR_UNMASK_ALL              (0xFFFFFFFF)

/* Bit definitions and macros for MCF_FEC_RDAR */
#define MCF_FEC_RDAR_R_DES_ACTIVE            (0x1000000)

/* Bit definitions and macros for MCF_FEC_TDAR */
#define MCF_FEC_TDAR_X_DES_ACTIVE            (0x1000000)

/* Bit definitions and macros for MCF_FEC_ECR */
#define MCF_FEC_ECR_RESET                    (0x1)
#define MCF_FEC_ECR_ETHER_EN                 (0x2)

/* Bit definitions and macros for MCF_FEC_MMFR */
#define MCF_FEC_MMFR_DATA(x)                 (((x)&0xFFFF)<<0)
#define MCF_FEC_MMFR_TA(x)                   (((x)&0x3)<<0x10)
#define MCF_FEC_MMFR_TA_10                   (0x20000)
#define MCF_FEC_MMFR_RA(x)                   (((x)&0x1F)<<0x12)
#define MCF_FEC_MMFR_PA(x)                   (((x)&0x1F)<<0x17)
#define MCF_FEC_MMFR_OP(x)                   (((x)&0x3)<<0x1C)
#define MCF_FEC_MMFR_OP_READ                 (0x20000000)
#define MCF_FEC_MMFR_OP_WRITE                (0x10000000)
#define MCF_FEC_MMFR_ST(x)                   (((x)&0x3)<<0x1E)
#define MCF_FEC_MMFR_ST_01                   (0x40000000)

/* Bit definitions and macros for MCF_FEC_MSCR */
#define MCF_FEC_MSCR_MII_SPEED(x)            (((x)&0x3F)<<0x1)
#define MCF_FEC_MSCR_DIS_PREAMBLE            (0x80)

/* Bit definitions and macros for MCF_FEC_MIBC */
#define MCF_FEC_MIBC_MIB_IDLE                (0x40000000)
#define MCF_FEC_MIBC_MIB_DISABLE             (0x80000000)

/* Bit definitions and macros for MCF_FEC_RCR */
#define MCF_FEC_RCR_LOOP                     (0x1)
#define MCF_FEC_RCR_DRT                      (0x2)
#define MCF_FEC_RCR_MII_MODE                 (0x4)
#define MCF_FEC_RCR_PROM                     (0x8)
#define MCF_FEC_RCR_BC_REJ                   (0x10)
#define MCF_FEC_RCR_FCE                      (0x20)
#define MCF_FEC_RCR_MAX_FL(x)                (((x)&0x7FF)<<0x10)

/* Bit definitions and macros for MCF_FEC_TCR */
#define MCF_FEC_TCR_GTS                      (0x1)
#define MCF_FEC_TCR_HBC                      (0x2)
#define MCF_FEC_TCR_FDEN                     (0x4)
#define MCF_FEC_TCR_TFC_PAUSE                (0x8)
#define MCF_FEC_TCR_RFC_PAUSE                (0x10)

/* Bit definitions and macros for MCF_FEC_PALR */
#define MCF_FEC_PALR_PADDR1(x)               (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_PAUR */
#define MCF_FEC_PAUR_TYPE(x)                 (((x)&0xFFFF)<<0)
#define MCF_FEC_PAUR_PADDR2(x)               (((x)&0xFFFF)<<0x10)

/* Bit definitions and macros for MCF_FEC_OPD */
#define MCF_FEC_OPD_PAUSE_DUR(x)             (((x)&0xFFFF)<<0)
#define MCF_FEC_OPD_OPCODE(x)                (((x)&0xFFFF)<<0x10)

/* Bit definitions and macros for MCF_FEC_IAUR */
#define MCF_FEC_IAUR_IADDR1(x)               (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IALR */
#define MCF_FEC_IALR_IADDR2(x)               (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_GAUR */
#define MCF_FEC_GAUR_GADDR1(x)               (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_GALR */
#define MCF_FEC_GALR_GADDR2(x)               (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_TFWR */
#define MCF_FEC_TFWR_X_WMRK(x)               (((x)&0x3)<<0)
#define MCF_FEC_TFWR_X_WMRK_64               (0)
#define MCF_FEC_TFWR_X_WMRK_128              (0x2)
#define MCF_FEC_TFWR_X_WMRK_192              (0x3)

/* Bit definitions and macros for MCF_FEC_FRBR */
#define MCF_FEC_FRBR_R_BOUND(x)              (((x)&0xFF)<<0x2)

/* Bit definitions and macros for MCF_FEC_FRSR */
#define MCF_FEC_FRSR_R_FSTART(x)             (((x)&0xFF)<<0x2)

/* Bit definitions and macros for MCF_FEC_ERDSR */
#define MCF_FEC_ERDSR_R_DES_START(x)         (((x)&0x3FFFFFFF)<<0x2)

/* Bit definitions and macros for MCF_FEC_ETSDR */
#define MCF_FEC_ETSDR_X_DES_START(x)         (((x)&0x3FFFFFFF)<<0x2)

/* Bit definitions and macros for MCF_FEC_EMRBR */
#define MCF_FEC_EMRBR_R_BUF_SIZE(x)          (((x)&0x7F)<<0x4)

/* Bit definitions and macros for MCF_FEC_RMON_T_DROP */
#define MCF_FEC_RMON_T_DROP_Value(x)         (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_T_PACKETS */
#define MCF_FEC_RMON_T_PACKETS_Value(x)      (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_T_BC_PKT */
#define MCF_FEC_RMON_T_BC_PKT_Value(x)       (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_T_MC_PKT */
#define MCF_FEC_RMON_T_MC_PKT_Value(x)       (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_T_CRC_ALIGN */
#define MCF_FEC_RMON_T_CRC_ALIGN_Value(x)    (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_T_UNDERSIZE */
#define MCF_FEC_RMON_T_UNDERSIZE_Value(x)    (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_T_OVERSIZE */
#define MCF_FEC_RMON_T_OVERSIZE_Value(x)     (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_T_FRAG */
#define MCF_FEC_RMON_T_FRAG_Value(x)         (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_T_JAB */
#define MCF_FEC_RMON_T_JAB_Value(x)          (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_T_COL */
#define MCF_FEC_RMON_T_COL_Value(x)          (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_T_P64 */
#define MCF_FEC_RMON_T_P64_Value(x)          (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_T_P65TO127 */
#define MCF_FEC_RMON_T_P65TO127_Value(x)     (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_T_P128TO255 */
#define MCF_FEC_RMON_T_P128TO255_Value(x)    (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_T_P256TO511 */
#define MCF_FEC_RMON_T_P256TO511_Value(x)    (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_T_P512TO1023 */
#define MCF_FEC_RMON_T_P512TO1023_Value(x)   (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_T_P1024TO2047 */
#define MCF_FEC_RMON_T_P1024TO2047_Value(x)  (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_T_P_GTE2048 */
#define MCF_FEC_RMON_T_P_GTE2048_Value(x)    (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_T_OCTETS */
#define MCF_FEC_RMON_T_OCTETS_Value(x)       (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_T_DROP */
#define MCF_FEC_IEEE_T_DROP_Value(x)         (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_T_FRAME_OK */
#define MCF_FEC_IEEE_T_FRAME_OK_Value(x)     (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_T_1COL */
#define MCF_FEC_IEEE_T_1COL_Value(x)         (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_T_MCOL */
#define MCF_FEC_IEEE_T_MCOL_Value(x)         (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_T_DEF */
#define MCF_FEC_IEEE_T_DEF_Value(x)          (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_T_LCOL */
#define MCF_FEC_IEEE_T_LCOL_Value(x)         (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_T_EXCOL */
#define MCF_FEC_IEEE_T_EXCOL_Value(x)        (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_T_MACERR */
#define MCF_FEC_IEEE_T_MACERR_Value(x)       (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_T_CSERR */
#define MCF_FEC_IEEE_T_CSERR_Value(x)        (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_T_SQE */
#define MCF_FEC_IEEE_T_SQE_Value(x)          (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_T_FDXFC */
#define MCF_FEC_IEEE_T_FDXFC_Value(x)        (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_T_OCTETS_OK */
#define MCF_FEC_IEEE_T_OCTETS_OK_Value(x)    (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_R_PACKETS */
#define MCF_FEC_RMON_R_PACKETS_Value(x)      (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_R_BC_PKT */
#define MCF_FEC_RMON_R_BC_PKT_Value(x)       (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_R_MC_PKT */
#define MCF_FEC_RMON_R_MC_PKT_Value(x)       (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_R_CRC_ALIGN */
#define MCF_FEC_RMON_R_CRC_ALIGN_Value(x)    (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_R_UNDERSIZE */
#define MCF_FEC_RMON_R_UNDERSIZE_Value(x)    (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_R_OVERSIZE */
#define MCF_FEC_RMON_R_OVERSIZE_Value(x)     (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_R_FRAG */
#define MCF_FEC_RMON_R_FRAG_Value(x)         (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_R_JAB */
#define MCF_FEC_RMON_R_JAB_Value(x)          (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_R_RESVD_0 */
#define MCF_FEC_RMON_R_RESVD_0_Value(x)      (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_R_P64 */
#define MCF_FEC_RMON_R_P64_Value(x)          (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_R_P65TO127 */
#define MCF_FEC_RMON_R_P65TO127_Value(x)     (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_R_P128TO255 */
#define MCF_FEC_RMON_R_P128TO255_Value(x)    (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_R_P256TO511 */
#define MCF_FEC_RMON_R_P256TO511_Value(x)    (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_R_P512TO1023 */
#define MCF_FEC_RMON_R_P512TO1023_Value(x)   (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_R_P1024TO2047 */
#define MCF_FEC_RMON_R_P1024TO2047_Value(x)  (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_R_P_GTE2048 */
#define MCF_FEC_RMON_R_P_GTE2048_Value(x)    (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_RMON_R_OCTETS */
#define MCF_FEC_RMON_R_OCTETS_Value(x)       (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_R_DROP */
#define MCF_FEC_IEEE_R_DROP_Value(x)         (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_R_FRAME_OK */
#define MCF_FEC_IEEE_R_FRAME_OK_Value(x)     (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_R_CRC */
#define MCF_FEC_IEEE_R_CRC_Value(x)          (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_R_ALIGN */
#define MCF_FEC_IEEE_R_ALIGN_Value(x)        (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_R_MACERR */
#define MCF_FEC_IEEE_R_MACERR_Value(x)       (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_R_FDXFC */
#define MCF_FEC_IEEE_R_FDXFC_Value(x)        (((x)&0xFFFFFFFF)<<0)

/* Bit definitions and macros for MCF_FEC_IEEE_R_OCTETS_OK */
#define MCF_FEC_IEEE_R_OCTETS_OK_Value(x)    (((x)&0xFFFFFFFF)<<0)


#endif /* __MCF5282_FEC_H__ */
