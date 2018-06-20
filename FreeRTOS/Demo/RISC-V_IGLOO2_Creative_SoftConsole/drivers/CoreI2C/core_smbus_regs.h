/*******************************************************************************
 * (c) Copyright 2009-2015 Microsemi SoC Products Group.  All rights reserved.
 * 
 * SVN $Revision: 7984 $
 * SVN $Date: 2015-10-12 12:07:40 +0530 (Mon, 12 Oct 2015) $
 */

#ifndef __CORE_SMBUS_REGISTERS
#define __CORE_SMBUS_REGISTERS    1

/*------------------------------------------------------------------------------
 * CONTROL register details
 */
#define CONTROL_REG_OFFSET    0x00u

/*
 * CR0 bits.
 */
#define CR0_OFFSET   0x00u
#define CR0_MASK     0x01u
#define CR0_SHIFT    0u

/*
 * CR1 bits.
 */
#define CR1_OFFSET   0x00u
#define CR1_MASK     0x02u
#define CR1_SHIFT    1u

/*
 * AA bits.
 */
#define AA_OFFSET   0x00u
#define AA_MASK     0x04u
#define AA_SHIFT    2u

/*
 * SI bits.
 */
#define SI_OFFSET   0x00u
#define SI_MASK     0x08u
#define SI_SHIFT    3u

/*
 * STO bits.
 */
#define STO_OFFSET   0x00u
#define STO_MASK     0x10u
#define STO_SHIFT    4u

/*
 * STA bits.
 */
#define STA_OFFSET   0x00u
#define STA_MASK     0x20u
#define STA_SHIFT    5u

/*
 * ENS1 bits.
 */
#define ENS1_OFFSET   0x00u
#define ENS1_MASK     0x40u
#define ENS1_SHIFT    6u

/*
 * CR2 bits.
 */
#define CR2_OFFSET   0x00u
#define CR2_MASK     0x80u
#define CR2_SHIFT    7u

/*------------------------------------------------------------------------------
 * STATUS register details
 */
#define STATUS_REG_OFFSET    0x04u

/*------------------------------------------------------------------------------
 * DATA register details
 */
#define DATA_REG_OFFSET    0x08u

/*
 * TARGET_ADDR bits.
 */
#define TARGET_ADDR_OFFSET    0x08u
#define TARGET_ADDR_MASK      0xFEu
#define TARGET_ADDR_SHIFT     1u
 
/*
 * DIR bit.
 */
#define DIR_OFFSET   0x08u
#define DIR_MASK     0x01u
#define DIR_SHIFT    0u


/*------------------------------------------------------------------------------
 * ADDRESS register details
 */
#define ADDRESS_REG_OFFSET    0x0Cu

/*
 * GC bits.
 */
#define GC_OFFSET   0x0Cu
#define GC_MASK     0x01u
#define GC_SHIFT    0u

/*
 * ADR bits.
 */
#define OWN_SLAVE_ADDR_OFFSET   0x0Cu
#define OWN_SLAVE_ADDR_MASK     0xFEu
#define OWN_SLAVE_ADDR_SHIFT    1u

/*------------------------------------------------------------------------------
 * SMBUS register details
 */
#define SMBUS_REG_OFFSET    0x10u

/*
 * SMBALERT_IE bits.
 */
#define SMBALERT_IE_OFFSET   0x10u
#define SMBALERT_IE_MASK     0x01u
#define SMBALERT_IE_SHIFT    0u

/*
 * SMBSUS_IE bits.
 */
#define SMBSUS_IE_OFFSET   0x10u
#define SMBSUS_IE_MASK     0x02u
#define SMBSUS_IE_SHIFT    1u

/*
 * SMB_IPMI_EN bits.
 */
#define SMB_IPMI_EN_OFFSET   0x10u
#define SMB_IPMI_EN_MASK     0x04u
#define SMB_IPMI_EN_SHIFT    2u

/*
 * SMBALERT_NI_STATUS bits.
 */
#define SMBALERT_NI_STATUS_OFFSET   0x10u
#define SMBALERT_NI_STATUS_MASK     0x08u
#define SMBALERT_NI_STATUS_SHIFT    3u

/*
 * SMBALERT_NO_CONTROL bits.
 */
#define SMBALERT_NO_CONTROL_OFFSET   0x10u
#define SMBALERT_NO_CONTROL_MASK     0x10u
#define SMBALERT_NO_CONTROL_SHIFT    4u

/*
 * SMBSUS_NI_STATUS bits.
 */
#define SMBSUS_NI_STATUS_OFFSET   0x10u
#define SMBSUS_NI_STATUS_MASK     0x20u
#define SMBSUS_NI_STATUS_SHIFT    5u

/*
 * SMBSUS_NO_CONTROL bits.
 */
#define SMBSUS_NO_CONTROL_OFFSET   0x10u
#define SMBSUS_NO_CONTROL_MASK     0x40u
#define SMBSUS_NO_CONTROL_SHIFT    6u

/*
 * SMBUS_MST_RESET bits.
 */
#define SMBUS_MST_RESET_OFFSET   0x10u
#define SMBUS_MST_RESET_MASK     0x80u
#define SMBUS_MST_RESET_SHIFT    7u

/*------------------------------------------------------------------------------
 * SLAVE ADDRESS 1 register details
 */

#define ADDRESS1_REG_OFFSET    0x1Cu

/*
 * SLAVE1_EN bit of Slave Address 1 .
 */
#define SLAVE1_EN_OFFSET      0x1Cu
#define SLAVE1_EN_MASK        0x01u
#define SLAVE1_EN_SHIFT          0u

#endif    /* __CORE_SMBUS_REGISTERS */
