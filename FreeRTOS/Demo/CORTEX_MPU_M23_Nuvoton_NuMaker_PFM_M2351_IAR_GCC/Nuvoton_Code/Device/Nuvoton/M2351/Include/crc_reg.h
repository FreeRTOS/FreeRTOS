/**************************************************************************//**
 * @file     crc_reg.h
 * @version  V1.00
 * @brief    CRC register definition header file
 *
 * @copyright (C) 2017 Nuvoton Technology Corp. All rights reserved.
 *****************************************************************************/
#ifndef __CRC_REG_H__
#define __CRC_REG_H__

/** @addtogroup REGISTER Control Register

  @{

*/


/*---------------------- Cyclic Redundancy Check Controller -------------------------*/
/**
    @addtogroup CRC Cyclic Redundancy Check Controller(CRC)
    Memory Mapped Structure for CRC Controller
@{ */

typedef struct
{


    /**
     * @var CRC_T::CTL
     * Offset: 0x00  CRC Control Register
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[0]     |CRCEN     |CRC Channel Generator Enable Bit
     * |        |          |Set this bit 1 to enable CRC generator for CRC operation.
     * |        |          |0 = No effect.
     * |        |          |1 = CRC operation generator is active.
     * |[1]     |CHKSINIT  |Checksum Initialization
     * |        |          |Set this bit will auto reload SEED (CRC_SEED [31:0]) to CHECKSUM (CRC_CHECKSUM[31:0]) as CRC operation initial value.
     * |        |          |0 = No effect.
     * |        |          |1 = Reload SEED value to CHECKSUM register as CRC operation initial checksum value.
     * |        |          |The others contents of CRC_CTL register will not be cleared.
     * |        |          |Note1: This bit will be cleared automatically
     * |        |          |Note2: Setting this bit will reload the seed value from CRC_SEED register as checksum initial value.
     * |[24]    |DATREV    |Write Data Bit Order Reverse Enable Bit
     * |        |          |This bit is used to enable the bit order reverse function per byte for write data value DATA (CRC_DATA[31:0]) in CRC_DAT register.
     * |        |          |0 = Bit order reversed for CRC_DATA write data in Disabled.
     * |        |          |1 = Bit order reversed for CRC_DATA write data in Enabled (per byte).
     * |        |          |Note: If the write data is 0xAABBCCDD, the bit order reverse for CRC write data in is 0x55DD33BB.
     * |[25]    |CHKSREV   |Checksum Bit Order Reverse Enable Bit
     * |        |          |This bit is used to enable the bit order reverse function for checksum result CHECKSUM (CRC_CHECKSUM[31:0]).
     * |        |          |0 = Bit order reverse for CRC CHECKSUMCRC checksum Disabled.
     * |        |          |1 = Bit order reverse for CRC CHECKSUMCRC checksum Enabled.
     * |        |          |Note: If the checksum result is 0xDD7B0F2E, the bit order reverse result for CRC checksum is 0x74F0DEBB.
     * |[26]    |DATFMT    |Write Data 1's Complement Enable Bit
     * |        |          |This bit is used to enable the 1's complement function for write data value DATA (CRC_DATA[31:0]).
     * |        |          |0 = 1's complement for CRC_DATA writes data in Disabled.
     * |        |          |1 = 1's complement for CRC_DATA writes data in Enabled.
     * |[27]    |CHKSFMT   |Checksum 1's Complement Enable Bit
     * |        |          |This bit is used to enable the 1's complement function for checksum result in CHECKSUM (CRC_CHECKSUM[31:0]) register.
     * |        |          |0 = 1's complement for CRC CHECKSUM Disabled.
     * |        |          |1 = 1's complement for CRC CHECKSUMCRC Enabled.
     * |[29:28] |DATLEN    |CPU Write Data Length
     * |        |          |This field indicates the valid write data length of DATA (CRC_DAT[31:0]).
     * |        |          |00 = Data length is 8-bit mode.
     * |        |          |01 = Data length is 16-bit mode.
     * |        |          |1x = Data length is 32-bit mode.
     * |        |          |Note: When the write data length is 8-bit mode, the valid data in CRC_DAT register is only DATA[7:0] bits; if the write data length is 16-bit mode, the valid data in CRC_DAT register is only DATA[15:0]
     * |[31:30] |CRCMODE   |CRC Polynomial Mode
     * |        |          |This field indicates the CRC operation polynomial mode.
     * |        |          |00 = CRC-CCITT Polynomial mode.
     * |        |          |01 = CRC-8 Polynomial mode.
     * |        |          |10 = CRC-16 Polynomial mode.
     * |        |          |11 = CRC-32 Polynomial mode.
     * @var CRC_T::DAT
     * Offset: 0x04  CRC Write Data Register
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |DATA      |CRC Write Data Bits
     * |        |          |User can write data directly by CPU mode or use PDMA function to write data to this field to perform CRC operation.
     * |        |          |Note: When the write data length is 8-bit mode, the valid data in CRC_DAT register is only DATA[7:0] bits; if the write data length is 16-bit mode, the valid data in CRC_DAT register is only DATA[15:0].
     * @var CRC_T::SEED
     * Offset: 0x08  CRC Seed Register
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |SEED      |CRC Seed Value
     * |        |          |This field indicates the CRC seed value.
     * |        |          |Note1: This field SEED value will be reloaded to as checksum initial value CHECKSUM (CRC_CHECKSUM[31:0]) register) after perform CRC engine reset, CHKSINIT (CRC_CTL[1]) to 1.
     * |        |          |Note2: The valid bits of CRC_SEED[31:0] is correlated to CRCMODE (CRC_CTL[31:30]).
     * @var CRC_T::CHECKSUM
     * Offset: 0x0C  CRC Checksum Register
     * ---------------------------------------------------------------------------------------------------
     * |Bits    |Field     |Descriptions
     * | :----: | :----:   | :---- |
     * |[31:0]  |CHECKSUM  |CRC Checksum Results
     * |        |          |This field indicates the CRC checksum result.
     * |        |          |Note: The valid bits of CRC_CHECKSUM[31:0] is correlated to CRCMODE (CRC_CTL[31:30]).
     */
    __IO uint32_t CTL;                   /*!< [0x0000] CRC Control Register                                             */
    __IO uint32_t DAT;                   /*!< [0x0004] CRC Write Data Register                                          */
    __IO uint32_t SEED;                  /*!< [0x0008] CRC Seed Register                                                */
    __I  uint32_t CHECKSUM;              /*!< [0x000c] CRC Checksum Register                                            */

} CRC_T;

/**
    @addtogroup CRC_CONST CRC Bit Field Definition
    Constant Definitions for CRC Controller
@{ */

#define CRC_CTL_CRCEN_Pos                (0)                                               /*!< CRC_T::CTL: CRCEN Position             */
#define CRC_CTL_CRCEN_Msk                (0x1ul << CRC_CTL_CRCEN_Pos)                      /*!< CRC_T::CTL: CRCEN Mask                 */

#define CRC_CTL_CHKSINIT_Pos             (1)                                               /*!< CRC_T::CTL: CHKSINIT Position          */
#define CRC_CTL_CHKSINIT_Msk             (0x1ul << CRC_CTL_CHKSINIT_Pos)                   /*!< CRC_T::CTL: CHKSINIT Mask              */

#define CRC_CTL_DATREV_Pos               (24)                                              /*!< CRC_T::CTL: DATREV Position            */
#define CRC_CTL_DATREV_Msk               (0x1ul << CRC_CTL_DATREV_Pos)                     /*!< CRC_T::CTL: DATREV Mask                */

#define CRC_CTL_CHKSREV_Pos              (25)                                              /*!< CRC_T::CTL: CHKSREV Position           */
#define CRC_CTL_CHKSREV_Msk              (0x1ul << CRC_CTL_CHKSREV_Pos)                    /*!< CRC_T::CTL: CHKSREV Mask               */

#define CRC_CTL_DATFMT_Pos               (26)                                              /*!< CRC_T::CTL: DATFMT Position            */
#define CRC_CTL_DATFMT_Msk               (0x1ul << CRC_CTL_DATFMT_Pos)                     /*!< CRC_T::CTL: DATFMT Mask                */

#define CRC_CTL_CHKSFMT_Pos              (27)                                              /*!< CRC_T::CTL: CHKSFMT Position           */
#define CRC_CTL_CHKSFMT_Msk              (0x1ul << CRC_CTL_CHKSFMT_Pos)                    /*!< CRC_T::CTL: CHKSFMT Mask               */

#define CRC_CTL_DATLEN_Pos               (28)                                              /*!< CRC_T::CTL: DATLEN Position            */
#define CRC_CTL_DATLEN_Msk               (0x3ul << CRC_CTL_DATLEN_Pos)                     /*!< CRC_T::CTL: DATLEN Mask                */

#define CRC_CTL_CRCMODE_Pos              (30)                                              /*!< CRC_T::CTL: CRCMODE Position           */
#define CRC_CTL_CRCMODE_Msk              (0x3ul << CRC_CTL_CRCMODE_Pos)                    /*!< CRC_T::CTL: CRCMODE Mask               */

#define CRC_DAT_DATA_Pos                 (0)                                               /*!< CRC_T::DAT: DATA Position              */
#define CRC_DAT_DATA_Msk                 (0xfffffffful << CRC_DAT_DATA_Pos)                /*!< CRC_T::DAT: DATA Mask                  */

#define CRC_SEED_SEED_Pos                (0)                                               /*!< CRC_T::SEED: SEED Position             */
#define CRC_SEED_SEED_Msk                (0xfffffffful << CRC_SEED_SEED_Pos)               /*!< CRC_T::SEED: SEED Mask                 */

#define CRC_CHECKSUM_CHECKSUM_Pos        (0)                                               /*!< CRC_T::CHECKSUM: CHECKSUM Position     */
#define CRC_CHECKSUM_CHECKSUM_Msk        (0xfffffffful << CRC_CHECKSUM_CHECKSUM_Pos)       /*!< CRC_T::CHECKSUM: CHECKSUM Mask         */

/**@}*/ /* CRC_CONST */
/**@}*/ /* end of CRC register group */
/**@}*/ /* end of REGISTER group */

#endif /* __CLK_REG_H__ */
