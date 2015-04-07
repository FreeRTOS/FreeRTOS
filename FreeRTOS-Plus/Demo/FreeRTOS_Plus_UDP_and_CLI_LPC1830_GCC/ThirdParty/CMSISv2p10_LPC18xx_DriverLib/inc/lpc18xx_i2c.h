/**********************************************************************
* $Id$		lpc18xx_i2c.h		2011-06-02
*//**
* @file		lpc18xx_i2c.h
* @brief	Contains all macro definitions and function prototypes
* 			support for I2C firmware library on LPC18xx
* @version	1.0
* @date		02. June. 2011
* @author	NXP MCU SW Application Team
*
* Copyright(C) 2011, NXP Semiconductor
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

/* Peripheral group ----------------------------------------------------------- */
/** @defgroup I2C I2C (Inter-Integrated Circuit)
 * @ingroup LPC1800CMSIS_FwLib_Drivers
 * @{
 */

#ifndef LPC18XX_I2C_H_
#define LPC18XX_I2C_H_

/* Includes ------------------------------------------------------------------- */
#include "LPC18xx.h"
#include "lpc_types.h"


#ifdef __cplusplus
extern "C"
{
#endif


/* Private Macros ------------------------------------------------------------- */
/** @defgroup I2C_Private_Macros I2C Private Macros
 * @{
 */

/* --------------------- BIT DEFINITIONS -------------------------------------- */
/*******************************************************************//**
 * I2C Control Set register description
 *********************************************************************/
#define I2C_I2CONSET_AA				((0x04)) /*!< Assert acknowledge flag */
#define I2C_I2CONSET_SI				((0x08)) /*!< I2C interrupt flag */
#define I2C_I2CONSET_STO			((0x10)) /*!< STOP flag */
#define I2C_I2CONSET_STA			((0x20)) /*!< START flag */
#define I2C_I2CONSET_I2EN			((0x40)) /*!< I2C interface enable */

/*******************************************************************//**
 * I2C Control Clear register description
 *********************************************************************/
/** Assert acknowledge Clear bit */
#define I2C_I2CONCLR_AAC			((1<<2))
/** I2C interrupt Clear bit */
#define I2C_I2CONCLR_SIC			((1<<3))
/** START flag Clear bit */
#define I2C_I2CONCLR_STAC			((1<<5))
/** I2C interface Disable bit */
#define I2C_I2CONCLR_I2ENC			((1<<6))

/********************************************************************//**
 * I2C Status Code definition (I2C Status register)
 *********************************************************************/
/* Return Code in I2C status register */
#define I2C_STAT_CODE_BITMASK		((0xF8))

/* I2C return status code definitions ----------------------------- */

/** No relevant information */
#define I2C_I2STAT_NO_INF						((0xF8))

/* Master transmit mode -------------------------------------------- */
/** A start condition has been transmitted */
#define I2C_I2STAT_M_TX_START					((0x08))
/** A repeat start condition has been transmitted */
#define I2C_I2STAT_M_TX_RESTART					((0x10))
/** SLA+W has been transmitted, ACK has been received */
#define I2C_I2STAT_M_TX_SLAW_ACK				((0x18))
/** SLA+W has been transmitted, NACK has been received */
#define I2C_I2STAT_M_TX_SLAW_NACK				((0x20))
/** Data has been transmitted, ACK has been received */
#define I2C_I2STAT_M_TX_DAT_ACK					((0x28))
/** Data has been transmitted, NACK has been received */
#define I2C_I2STAT_M_TX_DAT_NACK				((0x30))
/** Arbitration lost in SLA+R/W or Data bytes */
#define I2C_I2STAT_M_TX_ARB_LOST				((0x38))

/* Master receive mode -------------------------------------------- */
/** A start condition has been transmitted */
#define I2C_I2STAT_M_RX_START					((0x08))
/** A repeat start condition has been transmitted */
#define I2C_I2STAT_M_RX_RESTART					((0x10))
/** Arbitration lost */
#define I2C_I2STAT_M_RX_ARB_LOST				((0x38))
/** SLA+R has been transmitted, ACK has been received */
#define I2C_I2STAT_M_RX_SLAR_ACK				((0x40))
/** SLA+R has been transmitted, NACK has been received */
#define I2C_I2STAT_M_RX_SLAR_NACK				((0x48))
/** Data has been received, ACK has been returned */
#define I2C_I2STAT_M_RX_DAT_ACK					((0x50))
/** Data has been received, NACK has been return */
#define I2C_I2STAT_M_RX_DAT_NACK				((0x58))

/* Slave receive mode -------------------------------------------- */
/** Own slave address has been received, ACK has been returned */
#define I2C_I2STAT_S_RX_SLAW_ACK				((0x60))

/** Arbitration lost in SLA+R/W as master */
#define I2C_I2STAT_S_RX_ARB_LOST_M_SLA			((0x68))
/** Own SLA+W has been received, ACK returned */
//#define I2C_I2STAT_S_RX_SLAW_ACK				((0x68))

/** General call address has been received, ACK has been returned */
#define I2C_I2STAT_S_RX_GENCALL_ACK				((0x70))

/** Arbitration lost in SLA+R/W (GENERAL CALL) as master */
#define I2C_I2STAT_S_RX_ARB_LOST_M_GENCALL		((0x78))
/** General call address has been received, ACK has been returned */
//#define I2C_I2STAT_S_RX_GENCALL_ACK				((0x78))

/** Previously addressed with own SLV address;
 * Data has been received, ACK has been return */
#define I2C_I2STAT_S_RX_PRE_SLA_DAT_ACK			((0x80))
/** Previously addressed with own SLA;
 * Data has been received and NOT ACK has been return */
#define I2C_I2STAT_S_RX_PRE_SLA_DAT_NACK		((0x88))
/** Previously addressed with General Call;
 * Data has been received and ACK has been return */
#define I2C_I2STAT_S_RX_PRE_GENCALL_DAT_ACK		((0x90))
/** Previously addressed with General Call;
 * Data has been received and NOT ACK has been return */
#define I2C_I2STAT_S_RX_PRE_GENCALL_DAT_NACK	((0x98))
/** A STOP condition or repeated START condition has
 * been received while still addressed as SLV/REC
 * (Slave Receive) or SLV/TRX (Slave Transmit) */
#define I2C_I2STAT_S_RX_STA_STO_SLVREC_SLVTRX	((0xA0))

/** Slave transmit mode */
/** Own SLA+R has been received, ACK has been returned */
#define I2C_I2STAT_S_TX_SLAR_ACK				((0xA8))

/** Arbitration lost in SLA+R/W as master */
#define I2C_I2STAT_S_TX_ARB_LOST_M_SLA			((0xB0))
/** Own SLA+R has been received, ACK has been returned */
//#define I2C_I2STAT_S_TX_SLAR_ACK				((0xB0))

/** Data has been transmitted, ACK has been received */
#define I2C_I2STAT_S_TX_DAT_ACK					((0xB8))
/** Data has been transmitted, NACK has been received */
#define I2C_I2STAT_S_TX_DAT_NACK				((0xC0))
/** Last data byte in I2DAT has been transmitted (AA = 0);
 ACK has been received */
#define I2C_I2STAT_S_TX_LAST_DAT_ACK			((0xC8))

/** Time out in case of using I2C slave mode */
#define I2C_SLAVE_TIME_OUT						0x10000UL

/********************************************************************//**
 * I2C Data register definition
 *********************************************************************/
/** Mask for I2DAT register*/
#define I2C_I2DAT_BITMASK			((0xFF))

/** Idle data value will be send out in slave mode in case of the actual
 * expecting data requested from the master is greater than its sending data
 * length that can be supported */
#define I2C_I2DAT_IDLE_CHAR			(0xFF)

/********************************************************************//**
 * I2C Monitor mode control register description
 *********************************************************************/
#define I2C_I2MMCTRL_MM_ENA			((1<<0))		/**< Monitor mode enable */
#define I2C_I2MMCTRL_ENA_SCL		((1<<1))		/**< SCL output enable */
#define I2C_I2MMCTRL_MATCH_ALL		((1<<2))		/**< Select interrupt register match */
#define I2C_I2MMCTRL_BITMASK		((0x07))		/**< Mask for I2MMCTRL register */

/********************************************************************//**
 * I2C Data buffer register description
 *********************************************************************/
/** I2C Data buffer register bit mask */
#define I2DATA_BUFFER_BITMASK		((0xFF))

/********************************************************************//**
 * I2C Slave Address registers definition
 *********************************************************************/
/** General Call enable bit */
#define I2C_I2ADR_GC				((1<<0))
/** I2C Slave Address registers bit mask */
#define I2C_I2ADR_BITMASK			((0xFF))

/********************************************************************//**
 * I2C Mask Register definition
 *********************************************************************/
/** I2C Mask Register mask field */
#define I2C_I2MASK_MASK(n)			((n&0xFE))

/********************************************************************//**
 * I2C SCL HIGH duty cycle Register definition
 *********************************************************************/
/** I2C SCL HIGH duty cycle Register bit mask */
#define I2C_I2SCLH_BITMASK			((0xFFFF))

/********************************************************************//**
 * I2C SCL LOW duty cycle Register definition
 *********************************************************************/
/** I2C SCL LOW duty cycle Register bit mask */
#define I2C_I2SCLL_BITMASK			((0xFFFF))

/* I2C status values */
#define I2C_SETUP_STATUS_ARBF   (1<<8)	/**< Arbitration false */
#define I2C_SETUP_STATUS_NOACKF (1<<9)	/**< No ACK returned */
#define I2C_SETUP_STATUS_DONE   (1<<10)	/**< Status DONE */

/*********************************************************************//**
 * I2C monitor control configuration defines
 **********************************************************************/
#define I2C_MONITOR_CFG_SCL_OUTPUT	I2C_I2MMCTRL_ENA_SCL		/**< SCL output enable */
#define I2C_MONITOR_CFG_MATCHALL	I2C_I2MMCTRL_MATCH_ALL		/**< Select interrupt register match */

/* ---------------- CHECK PARAMETER DEFINITIONS ---------------------------- */
/* Macros check I2C slave address */
#define PARAM_I2C_SLAVEADDR_CH(n)	(n<=3)

/** Macro to determine if it is valid SSP port number */
#define PARAM_I2Cx(n)	((((uint32_t *)n)==((uint32_t *)LPC_I2C0)) \
|| (((uint32_t *)n)==((uint32_t *)LPC_I2C1)))

/* Macros check I2C monitor configuration type */
#define PARAM_I2C_MONITOR_CFG(n) ((n==I2C_MONITOR_CFG_SCL_OUTPUT) || (I2C_MONITOR_CFG_MATCHALL))

/**
 * @}
 */



/* Public Types --------------------------------------------------------------- */
/** @defgroup I2C_Public_Types I2C Public Types
 * @{
 */

/**
 * @brief I2C Own slave address setting structure
 */
typedef struct {
	uint8_t SlaveAddrChannel;	/**< Slave Address channel in I2C control,
								should be in range from 0..3
								*/
	uint8_t SlaveAddr_7bit;		/**< Value of 7-bit slave address */
	uint8_t GeneralCallState;	/**< Enable/Disable General Call Functionality
								when I2C control being in Slave mode, should be:
								- ENABLE: Enable General Call function.
								- DISABLE: Disable General Call function.
								*/
	uint8_t SlaveAddrMaskValue;	/**< Any bit in this 8-bit value (bit 7:1)
								which is set to '1' will cause an automatic compare on
								the corresponding bit of the received address when it
								is compared to the SlaveAddr_7bit value associated with this
								mask register. In other words, bits in SlaveAddr_7bit value
								which are masked are not taken into account in determining
								an address match
								*/
} I2C_OWNSLAVEADDR_CFG_Type;


/**
 * @brief Master transfer setup data structure definitions
 */
typedef struct
{
  uint32_t          sl_addr7bit;				/**< Slave address in 7bit mode */
  uint8_t*          tx_data;					/**< Pointer to Transmit data - NULL if data transmit
													  is not used */
  uint32_t          tx_length;					/**< Transmit data length - 0 if data transmit
													  is not used*/
  uint32_t          tx_count;					/**< Current Transmit data counter */
  uint8_t*          rx_data;					/**< Pointer to Receive data - NULL if data receive
													  is not used */
  uint32_t          rx_length;					/**< Receive data length - 0 if data receive is
													   not used */
  uint32_t          rx_count;					/**< Current Receive data counter */
  uint32_t          retransmissions_max;		/**< Max Re-Transmission value */
  uint32_t          retransmissions_count;		/**< Current Re-Transmission counter */
  uint32_t          status;						/**< Current status of I2C activity */
  void 				(*callback)(void);			/**< Pointer to Call back function when transmission complete
													used in interrupt transfer mode */
} I2C_M_SETUP_Type;


/**
 * @brief Slave transfer setup data structure definitions
 */
typedef struct
{
  uint8_t*          tx_data;					/**< Pointer to transmit data - NULL if data transmit is not used */
  uint32_t          tx_length;					/**< Transmit data length - 0 if data transmit is not used */
  uint32_t          tx_count;					/**< Current transmit data counter	*/
  uint8_t*          rx_data;					/**< Pointer to receive data - NULL if data received is not used */
  uint32_t          rx_length;					/**< Receive data length - 0 if data receive is not used */
  uint32_t          rx_count;					/**< Current receive data counter */
  uint32_t          status;						/**< Current status of I2C activity */
  void 				(*callback)(void);			/**< Pointer to call-back function when transmission complete
  													used by interrupt transfer mode */
} I2C_S_SETUP_Type;

/**
 * @brief Transfer option type definitions
 */
typedef enum {
	I2C_TRANSFER_POLLING = 0,		/**< Transfer in polling mode */
	I2C_TRANSFER_INTERRUPT			/**< Transfer in interrupt mode */
} I2C_TRANSFER_OPT_Type;


/**
 * @}
 */


/* Public Functions ----------------------------------------------------------- */
/** @defgroup I2C_Public_Functions I2C Public Functions
 * @{
 */

/* I2C Init/DeInit functions ---------- */
void I2C_Init(LPC_I2Cn_Type *I2Cx, uint32_t clockrate);
void I2C_DeInit(LPC_I2Cn_Type* I2Cx);
//void I2C_SetClock (LPC_I2Cn_Type *I2Cx, uint32_t target_clock);
void I2C_Cmd(LPC_I2Cn_Type* I2Cx, FunctionalState NewState);

/* I2C transfer data functions -------- */
Status I2C_MasterTransferData(LPC_I2Cn_Type *I2Cx, \
		I2C_M_SETUP_Type *TransferCfg, I2C_TRANSFER_OPT_Type Opt);
Status I2C_SlaveTransferData(LPC_I2Cn_Type *I2Cx, \
		I2C_S_SETUP_Type *TransferCfg, I2C_TRANSFER_OPT_Type Opt);
uint32_t I2C_MasterTransferComplete(LPC_I2Cn_Type *I2Cx);
uint32_t I2C_SlaveTransferComplete(LPC_I2Cn_Type *I2Cx);


void I2C_SetOwnSlaveAddr(LPC_I2Cn_Type *I2Cx, I2C_OWNSLAVEADDR_CFG_Type *OwnSlaveAddrConfigStruct);
uint8_t I2C_GetLastStatusCode(LPC_I2Cn_Type* I2Cx);

/* I2C Monitor functions ---------------*/
void I2C_MonitorModeConfig(LPC_I2Cn_Type *I2Cx, uint32_t MonitorCfgType, FunctionalState NewState);
void I2C_MonitorModeCmd(LPC_I2Cn_Type *I2Cx, FunctionalState NewState);
uint8_t I2C_MonitorGetDatabuffer(LPC_I2Cn_Type *I2Cx);
BOOL_8 I2C_MonitorHandler(LPC_I2Cn_Type *I2Cx, uint8_t *buffer, uint32_t size);

/* I2C Interrupt handler functions ------*/
void I2C_IntCmd (LPC_I2Cn_Type *I2Cx, Bool NewState);
void I2C_MasterHandler (LPC_I2Cn_Type *I2Cx);
void I2C_SlaveHandler (LPC_I2Cn_Type *I2Cx);


/**
 * @}
 */


#ifdef __cplusplus
}
#endif

#endif /* LPC18XX_I2C_H_ */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
