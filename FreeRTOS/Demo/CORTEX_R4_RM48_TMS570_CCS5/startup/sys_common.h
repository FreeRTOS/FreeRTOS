/*----------------------------------------------------------------------------*/
/* sys_common.h                                             10/20/10 15:19:19 */
/*                                                                            */
/* (c) Texas Instruments 2003-2010, All rights reserved.                      */
/*                                                                            */


#ifndef __sys_common_h__
#define __sys_common_h__

/*----------------------------------------------------------------------------*/
/* NULL                                                                       */

#ifndef NULL
#define NULL ((void *) 0)
#endif

/*----------------------------------------------------------------------------*/
/* Error Codes                                                                */

#define IO_E_OK                  0U
#define IO_E_BUSY                1U
#define IO_E_UNKNOWN_MODE        2U
#define IO_E_OVR                 3U
#define IO_E_FCN_SUSPENDED      16U
#define IO_E_PARAM_IGNORED      17U
#define IO_E_INVALID_CHANNEL_ID 18U
#define IO_E_INVALID_VALUE      19U
#define IO_E_INVALID_SIZE       20U
#define IO_E_INVALID_POSITION   21U
#define IO_E_INVALID_NOTIF_TYPE 22U
#define IO_E_MISSING_INIT       64U
#define IO_E_INVALID_GROUP_ID   66U
#define IO_E_INVALID_POINTER    67U
#define IO_E_INVALID_NODE       68U
#define IO_E_INVALID_CAN_ID     69U
#define IO_E_INVALID_OVR        70U
#define IO_E_INVALID_CONFIG     72U
#define IO_E_MISSING_CONNECT    73U
#define IO_E_MISSING_DISCONNECT 74U
#define IO_E_ALREADY_CONNECTED  75U
#define IO_E_GRP_NOTACTIVATED   80U
#define IO_E_INVALID_RESULT     81U
#define IO_E_TIMEOUT            82U
#define IO_E_INVALID_PARITY     83U
#define IO_E_SINGLE_ERROR       84U
#define IO_E_DOUBLE_ERROR       85U
#define IO_E_SINGLE_ERROR_EVEN  86U
#define IO_E_SINGLE_ERROR_ODD   87U
#define IO_E_DOUBLE_ERROR_EVEN  88U
#define IO_E_DOUBLE_ERROR_ODD   89U

/*----------------------------------------------------------------------------*/
/* Device Types                                                               */

#define IO_SPI                  0U
#define IO_DIO                  1U
#define IO_TIM                  2U
#define IO_PWM                  3U
#define IO_CCU                  4U
#define IO_RTI                  5U
#define IO_WDT                  6U
#define IO_ADC                  7U
#define IO_SCI                  8U
#define IO_FLS                  9U
#define IO_CAN                 10U
#define IO_QSPI                11U
#define IO_MSPI                11U
#define IO_LIN                 12U
#define IO_CRC                 13U
#define IO_DMA                 14U
#define IO_HTU                 15U
#define IO_PWD                 16U
#define IO_HET                 17U
#define IO_ESM                 18U
#define IO_I2C                 19U
#define IO_ECC                 20U
#define IO_VIM                 21U
#define IO_STC                 22U

/*----------------------------------------------------------------------------*/
/* Device States                                                              */

#define IO_STATE_IDLE           0U
#define IO_STATE_ACTIVE         1U

/*----------------------------------------------------------------------------*/
/* Notification Types                                                         */

#define IO_N_RISING_EDGE         0U
#define IO_N_FALLING_EDGE        1U
#define IO_N_THRESHOLD_1         2U
#define IO_N_THRESHOLD_2         3U
#define IO_N_CAPTURE             4U
#define IO_N_ALL                 5U
#define IO_N_ROLLOVER            6U
#define IO_N_READY               7U
#define IO_N_FCN_SUSPENDED       8U
#define IO_N_PARITY_ERROR        9U
#define IO_N_FRAMING_ERROR      10U
#define IO_N_BUFFER_OVERRUN     11U
#define IO_N_RECEIVE            12U
#define IO_N_TRANSMIT           13U
#define IO_N_TX_ERROR           15U
#define IO_N_RX_ERROR           16U
#define IO_N_BAUDRATE_ERROR     17U
#define IO_N_PHASE_ERROR        18U
#define IO_N_OCSET              19U
#define IO_N_OCRESET            20U
#define IO_N_RX_LOST            21U
#define IO_N_ACTIVE             22U
#define IO_N_WARNING            23U
#define IO_N_PASSIVE            24U
#define IO_N_BUS_OFF            25U
#define IO_N_WAKE_UP            26U
#define IO_N_LAST_ERROR         27U
#define IO_N_GRP_READY          30U
#define IO_N_ERROR              31U
#define IO_N_HDR_RECEIVE        32U
#define IO_N_HDR_TRANSMIT       33U
#define IO_N_ID_ERROR           34U
#define IO_N_CHECKSUM_ERROR     35U
#define IO_N_BIT_ERROR          36U
#define IO_N_FRAME_TIMEOUT      37U
#define IO_N_BUS_ERROR          38U
#define IO_N_SYNC_FIELD_ERROR   39U
#define IO_N_WAKE_UP_RECEIVE    40U
#define IO_N_WAKE_UP_TRANSMIT   41U
#define IO_N_ADJUST_BAUDRATE    42U
#define IO_N_BUS_IDLE_TIMEOUT   43U
#define IO_N_WAKE_UP_TIMEOUT    44U

/*----------------------------------------------------------------------------*/
/* Programming Interface Constants                                            */

#define IO_LOW                  0U
#define IO_HIGH                 1U
#define IO_INVALID              0xFFFFU

/*----------------------------------------------------------------------------*/
/* Data Types                                                                 */

typedef T_U32 IO_ErrorType;
typedef T_U32 IO_DeviceType;
typedef T_U32 IO_FunctionNrType;
typedef T_U32 IO_DeviceStateType;
typedef T_U32 IO_ChannelType;
typedef T_U32 IO_ModeType;
typedef T_U32 IO_ValueType;
typedef T_U32 IO_U32;

/*----------------------------------------------------------------------------*/
/* Error hook                                                                 */

void IO_ErrorHook(IO_DeviceType device, IO_ErrorType error);

/*----------------------------------------------------------------------------*/
/* ISR Function Prototypes                                                    */

void IO_PHANTOM_INT(void);
void IO_ESM_INT_HIGH(void);
void IO_TIM0_INT(void);
void IO_TIM1_INT(void);
void IO_DIO_INT_HIGH(void);
void IO_HET_INT_HIGH(void);
void IO_HTU_INT_HIGH(void);
void IO_MIBSPI1_INT_HIGH(void);
void IO_LIN_INT_HIGH(void);
void IO_MIBADC_INT_GROUP0(void);
void IO_MIBADC_INT_GROUP1(void);
void IO_CAN1_INT_HIGH(void);
void IO_SPI2_INT_HIGH(void);
void IO_ESM_INT_LOW(void);
void IO_DIO_INT_LOW(void);
void IO_HET_INT_LOW(void);
void IO_HTU_INT_LOW(void);
void IO_MIBSPI1_INT_LOW(void);
void IO_LIN_INT_LOW(void);
void IO_MIBADC_INT_GROUP2(void);
void IO_CAN1_INT_LOW(void);
void IO_SPI2_INT_LOW(void);
void IO_MIBADC_INT_MAG(void);
void IO_DMA_INT_FTCA(void);
void IO_DMA_INT_LFSA(void);
void IO_CAN2_INT_HIGH(void);
void IO_MIBSPI3_INT_HIGH(void);
void IO_MIBSPI3_INT_LOW(void);
void IO_DMA_INT_HBCA(void);
void IO_DMA_INT_BTCA(void);
void IO_CAN2_INT_LOW(void);

/*----------------------------------------------------------------------------*/
/* Notification Function Prototypes                                           */


#endif
/*----------------------------------------------------------------------------*/

