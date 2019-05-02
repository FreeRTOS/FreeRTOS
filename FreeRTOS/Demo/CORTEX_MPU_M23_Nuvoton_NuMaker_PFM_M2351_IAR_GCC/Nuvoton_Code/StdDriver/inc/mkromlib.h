/**************************************************************************//**
 * @file     MKROMLib.h
 * @version  V2.00
 * @brief    MaskROM library header file
 *
 * @copyright (C) 2018 Nuvoton Technology Corp. All rights reserved.
 *****************************************************************************/
#ifndef __MKROM_LIB_H__
#define __MKROM_LIB_H__

#ifdef __cplusplus
extern "C"
{
#endif


/** @addtogroup Standard_Driver Standard Driver
  @{
*/

/** @addtogroup MKROM_Driver MKROM Driver
  @{
*/

/** @addtogroup MKROM_EXPORTED_CONSTANTS MKROM Exported Constants
  @{
*/
/*--------------------------------------------------------------------------------------------------*/
/*  Status and Error Code Constant Definitions                                                      */
/*--------------------------------------------------------------------------------------------------*/
#define BL_ERR_TT_CHECK         0xF0F00000UL    /*!< Not a Non-secure parameter         */
#define BL_ERR_PARAMETER        0xF0F00001UL    /*!< Invalid parameter                  */
#define BL_PARAM_ALIGN          0xF0F00002UL    /*!< Parameter alignment error          */
#define BL_NOT_FLASH_ADDR       0xF0F00003UL    /*!< Invalid flash address              */
#define BL_NOT_SRAM_ADDR        0xF0F00004UL    /*!< Invalid sram address               */
#define BL_XOM_NOT_CONFIG       0xF0F00005UL    /*!< XOM is not configure yet           */
#define BL_XOM_HAS_CONFIG       0xF0F00006UL    /*!< XOM has beeen configured           */
#define BL_XOM_HAS_ACTIVE       0xF0F00007UL    /*!< XOM is actived                     */
#define BL_XOM_BASE_ERROR       0xF0F00008UL    /*!< Invalid XOM base address           */
#define BL_KPROM_NOT_ENABLE     0xF0F00009UL    /*!< KPROM is not enabled yet           */
#define BL_KPROM_KEY_FORBID     0xF0F0000AUL    /*!< KPROM comparison is forbidden      */
#define BL_KPROM_KEY_UNMATCH    0xF0F0000BUL    /*!< KPROM comparison is unmatched      */
#define BL_KPROM_KEY_LOCKED     0xF0F0000CUL    /*!< KPROM write-protect is enabled     */
#define BL_KPROM_SET_FAIL       0xF0F0000EUL    /*!< Set KPROM key fail                 */
#define BL_ISP_CMD_FAIL         (-1)            /*!< FMC command fail                   */
#define BL_FLASH_ALLONE         0xA11FFFFFUL    /*!< Check-all-one result is all one    */
#define BL_FLASH_NOT_ALLONE     0xA1100000UL    /*!< Check-all-one result is not all one*/

/*--------------------------------------------------------------------------------------------------*/
/*  Random Number Generator Constant Definitions                                                    */
/*--------------------------------------------------------------------------------------------------*/
#define BL_RNG_PRNG             (0UL)   /*!<Use H/W random number generator */
#define BL_RNG_SWRNG            (1UL)   /*!<Use S/W random number generator */
#define BL_RNG_LIRC32K          (0UL)   /*!<Use LIRC32 for random number generator */
#define BL_RNG_LXT              (2UL)   /*!<Use LXT for random number generator */
#define XTRNG_PRNG              (0UL)   /*!<Use H/W random number generator */
#define XTRNG_SWRNG             (1UL)   /*!<Use S/W random number generator */
#define XTRNG_LIRC32K           (0UL)   /*!<Use LIRC32 for random number generator */
#define XTRNG_LXT               (2UL)   /*!<Use LXT for random number generator */

/*--------------------------------------------------------------------------------------------------*/
/*  Maximum SecureISP Mode Transmit/Receive Packet Size Constant Definitions                        */
/*--------------------------------------------------------------------------------------------------*/
#define MAX_PKT_SIZE            64

/*@}*/ /* end of group MKROM_EXPORTED_CONSTANTS */


/** @addtogroup MKROM_EXPORTED_STRUCTS MKROM Exported Structs
  @{
*/
/**
  * @details    Random number generator structure
  */
typedef struct
{
    uint32_t opt;       /*!< Operation mode */
    int32_t data_len;   /*!< Internal use for random number generator */
    uint8_t buf[32];    /*!< Internal use for random number generator */
    uint8_t buf2[20];   /*!< Internal use for random number generator */
} BL_RNG_T;

typedef struct
{
    uint32_t opt;       /*!< Operation mode */
    int32_t data_len;   /*!< Internal use for random number generator */
    uint8_t buf[32];    /*!< Internal use for random number generator */
    uint8_t buf2[20];   /*!< Internal use for random number generator */
} XTRNG_T;


/**
  * @details    XCRPT_T is structure for access MKROM Crypto library
  */
typedef struct
{
    CRPT_T      *crpt;       /*!< The pointer of the CRYPTO module */
    ECC_CURVE   *pCurve;     /*!< Internal use for ECC */
    ECC_CURVE   Curve_Copy;  /*!< Internal use for ECC */
    uint32_t    AES_CTL[4];  /*!< AES channel selection */ 
    uint32_t    TDES_CTL[4]; /*!< TDES channel selection */
} XCRPT_T;

/*---------------------------------------------------------------------------------------------------*/
/*  Define a global constant XCRPT as the access address of g_xcrpta for using MKROM Crypto library. */
/*---------------------------------------------------------------------------------------------------*/
extern XCRPT_T g_xcrpt;
#define XCRPT (&g_xcrpt)


/**
  * @details    Command packet structure for transmit/receive data in SecureISP function
  */
typedef struct
{
    /* Word-0 */
    uint16_t        u16CRC16;       /* CRC16 checksum of from u8CmdID to Word-13 */
    uint16_t        u16CmdID;       /* Command ID */

    /* Word-1 */
    uint16_t        u16PacketID;    /* Packet ID */
    uint16_t        u16Len;         /* Valid data length in command data field */

    /* Word-2 ~ 13 */
    uint32_t        au32Data[12];   /* Data fields */

    /* Word-14 */
    uint32_t        u32CRC32;       /* CRC32 from Word-0 to Word-13 for check cmd integrity */

    /* Word-15 */
    uint32_t        RSVD;           /* Reserved */

} CMD_PACKET_T;


/**
  * @details    ECC public key structure
  */
typedef struct
{
    uint32_t        au32Key0[8];    /* 256-bits */
    uint32_t        au32Key1[8];    /* 256-bits */
} __attribute__((packed)) ECC_PUBKEY_T;


/**
  * @details    ECC ECDSA signature structure
  */
typedef struct
{
    uint32_t        au32R[8];   /* 256-bits */
    uint32_t        au32S[8];   /* 256-bits */
} __attribute__((packed)) ECDSA_SIGN_T;


/**
  * @details    SecureISP operation mode enumerate
  */
typedef enum
{
    USB_MODE        = 0x1,
    UART_MODE       = 0x2,
    USB_UART_MODE   = 0x3,
    RESYNC_ISP      = 0x80, /* To set SecureISP in waiting connection state */
} E_ISP_MODE;


/**
  * @details    Global ISP information data for perform SecureISP function
  */
typedef void (*ISPCallback)(uint32_t *pu32Buf, uint32_t u32Data);
typedef void (*USBDEPFunc)(void);
typedef struct
{
    uint32_t        u32CmdMask;         /* Disable the specify command in SecureISP */

    uint32_t        au32AESKey[8];      /* AES-256 keys */
    uint32_t        au32AESIV[4];       /* AES IV, 128-bits */

    ECC_PUBKEY_T    ClientPubKey;       /* Client's ECC public key, 64-bytes (256-bits + 256-bits) */
    ECC_PUBKEY_T    ServerPubKey;       /* Server's ECC public key, 64-bytes (256-bits + 256-bits) */

    ECDSA_SIGN_T    sign;               /* 64-bytes (256-bits R + 256-bits S) */

    uint32_t        IsConnectOK;        /* Internal use in SecureISP */
    uint32_t        timeout;            /* Timeout period for connecting to SecureISP Tool */
    
    __attribute__((aligned(4))) uint8_t rcvbuf[MAX_PKT_SIZE]; /* Internal use in SecureISP */
    __attribute__((aligned(4))) uint8_t rspbuf[MAX_PKT_SIZE]; /* Internal use in SecureISP */       

    USBDEPFunc      pfnUSBDEP[USBD_MAX_EP]; /* Internal use in SecureISP */
    uint32_t        IsUSBDataReady;     /* Internal use in SecureISP */

    uint32_t        UARTClockFreq;      /* UART clock frequency */
    uint32_t        UARTDataIdx;        /* Internal use in SecureISP */
    uint32_t        IsUARTDataReady;    /* Internal use in SecureISP */

    ISPCallback     pfnVendorFunc;      /* Vendor function address */

    uint32_t        tmp0[8];            /* Internal use in SecureISP */
    uint32_t        tmp1[8];            /* Internal use in SecureISP */
  
} ISP_INFO_T;


/**
  * @details    Global USBD data for SecureISP USB
  * @note       This data is internal use in SecureISP operation
  */
typedef struct
{
    uint8_t             g_usbd_SetupPacket[8];  
    volatile uint8_t    g_usbd_RemoteWakeupEn;  
    volatile uint8_t    g_usbd_u8ZeroFlag;

    volatile uint8_t    *g_usbd_CtrlInPointer;
    volatile uint8_t    *g_usbd_CtrlOutPointer;
    volatile uint32_t   g_usbd_CtrlInSize;
    volatile uint32_t   g_usbd_CtrlOutSize;
    volatile uint32_t   g_usbd_CtrlOutSizeLimit;
    volatile uint32_t   g_usbd_UsbAddr;
    volatile uint32_t   g_usbd_UsbConfig;
    volatile uint32_t   g_usbd_CtrlMaxPktSize;
    volatile uint32_t   g_usbd_UsbAltInterface;

    S_USBD_INFO_T       *g_usbd_sInfo;                  

    VENDOR_REQ          g_usbd_pfnVendorRequest;        
    CLASS_REQ           g_usbd_pfnClassRequest;         
    SET_INTERFACE_REQ   g_usbd_pfnSetInterface;         
    SET_CONFIG_CB       g_usbd_pfnSetConfigCallback;
    uint32_t            g_u32EpStallLock;              

} BL_USBD_INFO_T;


/*@}*/ /* end of group MKROM_EXPORTED_STRUCTS */


/** @addtogroup MKROM_EXPORTED_FUNCTIONS Bootloader Exported Functions
  @{
*/
/**
  * @brief      Get MKROM Version Number
  * @param      None
  * @return     Version number of MKROM
  * @details    This API will return the MKROM version number.
  */
uint32_t BL_GetVersion(void);


/**
  * @brief      Enable FMC ISP Function and return maximum APROM size
  * @param      None
  * @return     Maximum APROM size
  * @details    This API will unlock register write-protect, enable relative settings for access FMC ISP commands
  *             and return maximum APROM by chip package.
  */
uint32_t BL_EnableFMC(void);


/**
  * @brief      Disable FMC ISP Function
  * @param      None
  * @return     None
  * @details    This API will disable relative settings for disable FMC ISP function and lock register write-protect
  *             until last ISP operation is finished.
  */
void BL_DisableFMC(void);


/**
  * @brief      Get FMC ISP Busy Status
  * @param      None
  * @retval     0   ISP operation is finished
  * @retval     1   ISP operation is in processing
  * @details    This API indicates ISP operation in in processing or finished.
  */
uint32_t BL_GetISPStatus(void);


/**
  * @brief      Get Non-secure Boundary
  * @param      None
  * @return     Current Non-secure boundary
  * @details    This API can get current Non-secure boundary address.
  */
uint32_t BL_GetNSBoundary(void);


/**
  * @brief      Set All Flash Region Lock
  * @param      None
  * @retval     -1      Set flash all lock failed
  * @retval     0       Set flash all lock operation is success
  * @details    This API will protect all flash region read/write operate by ICE interface.
  */
int32_t BL_SetFlashAllLock(void);


/**
  * @brief      Read Non-secure Flash Address Data (for Non-secure region)
  * @param[in]  u32NSAddr   Non-secure flash address
  * @retval     0xF0F00000  u32NSAddr isn't in Non-secure area
  * @retval     0xF0F00001  u32NSAddr isn't word aligned
  * @retval     0xF0F00003  u32NSAddr isn't valid flash address
  * @retval     -1          Flash read failed
  * @retval     The data of specified Non-secure address
  * @details    To read word data from specified Non-secure flash address.
  */
uint32_t BL_FlashRead(uint32_t u32NSAddr);


/**
  * @brief      Read Multi-Word Data from Non-secure Flash Address (for Non-secure region)
  * @param[in]  u32NSAddr       Starting Non-secure flash address
  * @param[out] pu32NSRamBuf    Non-secure sram address to store reading data
  * @param[in]  u32Size         Total read byte counts, it should be word aligned and maximum size is one page size.
  * @retval     0xF0F00000      u32NSAddr or pu32NSRamBuf region isn't in Non-secure area
  * @retval     0xF0F00001      Wrong u32NSAddr, pu32NSRamBuf or u32Size parameter
  * @retval     0xF0F00003      u32NSAddr isn't valid flash address
  * @retval     0xF0F00004      pu32NSRamBuf isn't valid sram address
  * @retval     -1              Multi-words read failed
  * @retval     0               Read operation is success
  * @details    To read multi-words data start from specified Non-secure flash address.
  *             And maximum read size is one page size, 2048 bytes.
  */
int32_t BL_FlashMultiRead(uint32_t u32NSAddr, uint32_t *pu32NSRamBuf, uint32_t u32Size);


/**
  * @brief      Program Data into Non-secure Flash Address (for Non-secure region)
  * @param[in]  u32NSAddr   Non-secure flash address
  * @param[in]  u32Data     32-bit Data to program
  * @retval     0xF0F00000  u32NSAddr isn't in Non-secure area
  * @retval     0xF0F00001  u32NSAddr isn't word aligned
  * @retval     0xF0F00003  u32NSAddr isn't valid flash address
  * @retval     -1          Flash write failed
  * @retval     0           Program command is finished
  * @details    To program word data into specified Non-secure flash address.
  */
int32_t BL_FlashWrite(uint32_t u32NSAddr, uint32_t u32Data);


/**
  * @brief      Program Multi-Word Data into Non-secure Flash Address (for Non-secure region)
  * @param[in]  u32NSAddr       Starting Non-secure flash address
  * @param[in]  pu32NSRamBuf    Non-secure sram buffer address to store program data
  * @param[in]  u32Size         Total program byte counts, it should be word aligned and maximum size is one page size.
  * @retval     0xF0F00000      u32NSAddr or pu32NSRamBuf region isn't in Non-secure area
  * @retval     0xF0F00001      Wrong u32NSAddr, pu32NSRamBuf or u32Size parameter
  * @retval     0xF0F00003      u32NSAddr isn't valid flash address
  * @retval     0xF0F00004      pu32NSRamBuf isn't valid sram address
  * @retval     -1              Multi-words write failed
  * @retval     0               Program operation is finished
  * @details    To program multi-words data start from specified Non-secure flash address.
  *             And maximum program size is one page size, 2048 bytes.
  */
int32_t BL_FlashMultiWrite(uint32_t u32NSAddr, uint32_t *pu32NSRamBuf, uint32_t u32Size);


/**
  * @brief      Non-secure Flash Page Erase (for Non-secure region)
  * @param[in]  u32NSAddr   Non-secure flash region to be erased and must be a page size aligned address.
  * @retval     0xF0F00000  u32NSAddr region isn't in Non-secure area
  * @retval     0xF0F00001  u32NSAddr isn't page size aligned
  * @retval     0xF0F00003  u32NSAddr isn't valid flash address
  * @retval     -1          Page erase failed
  * @retval     0           Page erase success
  * @details    This API is used to perform page erase command on specified Non-secure flash address.
  *             And this address must be a page size aligned address.
  */
int32_t BL_FlashPageErase(uint32_t u32NSAddr);


/**
  * @brief      Get Non-secure Flash Area CRC32 Checksum (for Non-secure region)
  * @param[in]  u32NSAddr       Non-secure flash region to be calculated. u32NSAddr must be a page size aligned address.
  * @param[in]  u32ByteCount    Byte counts of Non-secure flash area to be calculated. It must be multiple of 2048 bytes.
  * @retval     0xF0F00000      u32NSAddr region isn't in Non-secure area
  * @retval     0xF0F00001      Wrong u32NSAddr or u32ByteCount parameter
  * @retval     0xF0F00003      u32NSAddr isn't valid flash address
  * @retval     -1              Execute CRC32 operation failed
  * @retval     Result of CRC32 checksum
  * @details    This API will calculate the CRC32 checksum result of specified non-secure flash area.
  *             The starting address and calculated size must be all 2048 bytes page size aligned.
  */
uint32_t BL_FlashChecksum(uint32_t u32NSAddr, uint32_t u32ByteCount);


/**
  * @brief      Check Non-secure Flash Area Data are all ONE or not (for Non-secure region)
  * @param[in]  u32NSAddr       Non-secure flash region to be calculated. u32NSAddr must be a page size aligned address.
  * @param[in]  u32ByteCount    Byte counts of Non-secure flash area to be calculated. It must be multiple of 2048 bytes.
  * @retval     0xF0F00000      u32NSAddr region isn't in Non-secure area
  * @retval     0xF0F00001      Wrong u32NSAddr or u32ByteCount parameter
  * @retval     0xF0F00003      u32NSAddr isn't valid flash address
  * @retval     -1              Execute Check Flash All One operation failed
  * @retval     0xA11FFFFF      The contents of verified Non-secure flash area are 0xFFFFFFFF
  * @retval     0xA1100000      Some contents of verified Non-secure flash area are not 0xFFFFFFFF
  * @details    This API is used to check specified Non-secure flash area are all 0xFFFFFFFF or not.
  */
uint32_t BL_CheckFlashAllOne(uint32_t u32NSAddr, uint32_t u32ByteCount);


/**
  * @brief      Read Company ID
  * @param      None
  * @return     The company ID (32-bit)
  * @details    The company ID of Nuvoton is fixed to be 0xDA.
  */
uint32_t BL_ReadCID(void);


/**
  * @brief      Read Device ID
  * @param      None
  * @return     The device ID (32-bit)
  * @details    This function is used to read device ID.
  */
uint32_t BL_ReadDID(void);


/**
  * @brief      Read Product ID
  * @param      None
  * @return     The product ID (32-bit)
  * @details    This function is used to read product ID.
  */
uint32_t BL_ReadPID(void);


/**
  * @brief      Read UCID
  * @param[in]  u32Index    Index of the UCID to read and u32Index must be 0, 1, 2, or 3.
  * @return     The UCID of specified index
  * @details    This function is used to read unique chip ID (UCID).
  */
uint32_t BL_ReadUCID(uint32_t u32Index);


/**
  * @brief      Read UID
  * @param[in]  u32Index    UID index. 0 = UID[31:0], 1 = UID[63:32], 2 = UID[95:64]
  * @return     The 32-bit unique ID data of specified UID index
  * @details    To read out specified 32-bit unique ID.
  */
uint32_t BL_ReadUID(uint32_t u32Index);


/**
  * @brief      Get XOM Active Status
  * @param[in]  u32XOM      Specified XOM region, it must be between 0~3.
  * @retval     0xF0F00001  Invalid u32XOM number
  * @retval     0           Current XOM region isn't active yet
  * @retval     1           Current XOM region is active
  * @details    This API will return specified XOM region active status.
  */
uint32_t BL_GetXOMActiveStatus(uint32_t u32XOM);


/**
  * @brief      Read XOM Setting (for Non-secure region)
  * @param[in]  u32XOM          Specified XOM region, it must be between 0~3
  * @param[out] pu32Base        Return specified XOM base address
  * @param[out] pu32PageCnt     Return specified XOM page count
  * @retval     0xF0F00000      pu32Base, pu32PageCnt or XOM base address isn't in Non-secure area
  * @retval     0xF0F00001      Wrong u32XOM, pu32Base or pu32PageCnt parameter
  * @retval     0xF0F00003      XOM base address isn't valid flash address
  * @retval     0xF0F00004      pu32Base or pu32PageCnt isn't valid sram address
  * @retval     0xF0F00005      XOM region isn't configured
  * @retval     0               Read specified XOM setting success
  * @details    This API will read specified XOM relative settings.
  */
int32_t BL_ReadXOMRegion(uint32_t u32XOM, uint32_t *pu32Base, uint32_t *pu32PageCnt);


/**
  * @brief      Set XOM Region and Active (for Non-secure region)
  * @param[in]  u32XOM          Specified XOM region, it must be between 0~3
  * @param[in]  u32Base         Base address of XOM region
  * @param[in]  u32PageCnt      Page count of XOM region
  * @param[in]  u32IsDebugMode  1: Enable XOM debug mode; others will disable XOM debug mode.
  * @retval     0xF0F00000      XOM region isn't in Non-secure area
  * @retval     0xF0F00001      Wrong u32XOM, u32Base or u32PageCnt parameter
  * @retval     0xF0F00003      u32Base isn't valid flash address
  * @retval     0xF0F00006      XOM region has configured
  * @retval     0xF0F00007      XOM region has active
  * @retval     -1              Set XOM failed
  * @retval     0               Set specified XOM success
  * @details    This API will set specified XOM active.
  */
int32_t BL_SetXOMRegion(uint32_t u32XOM, uint32_t u32Base, uint32_t u32PageCnt, uint32_t u32IsDebugMode);


/**
  * @brief      Erase XOM Setting (for Non-secure region)
  * @param[in]  u32XOMBase  Specified XOM region to be erase
  * @retval     0xF0F00000  u32XOMBase or erase XOM region isn't in Non-secure area
  * @retval     0xF0F00001  u32XOMBase isn't page size aligned
  * @retval     0xF0F00003  u32XOMBase isn't valid flash address
  * @retval     0xF0F00008  Invalid u32XOMBase address
  * @retval     -1          Erase XOM region failed
  * @retval     0           Erase XOM region success
  * @details    This API will erase specified XOM region data and relative XOM setting.
  */
int32_t BL_EraseXOMRegion(uint32_t u32XOMBase);


/**
  * @brief      Get XOM Erased Status
  * @param      None
  * @retval     -1      Erase XOM operation failed
  * @retval     0       Erase XOM operation success
  * @details    This API will return the XOM erase operation is success or not.
  */
int32_t BL_GetXOMEraseStatus(void);


/**
  * @brief      Read KPKEYSTS Status
  * @param      None
  * @return     KPKEYSTS register status
  * @details    This API can read KPROM KPKEYSTS register status.
  */
uint32_t BL_GetKPROMStatus(void);


/**
  * @brief      Read KPKEYCNT Status
  * @param      None
  * @return     KPKEYCNT register status
  * @details    This API can read KPROM KPKEYCNT register status.
  */
uint32_t BL_GetKPROMCounter(void);


/**
  * @brief      Read KPCNT Status
  * @param      None
  * @return     KPCNT register status
  * @details    This API can read KPROM KPCNT register status.
  */
uint32_t BL_GetKPROMPowerOnCounter(void);


/**
  * @brief      Execute KPROM Key Comparison
  * @param[in]  key0        KPROM key0
  * @param[in]  key1        KPROM key1
  * @param[in]  key2        KPROM key2
  * @retval     0xF0F00009  KPROM function isn't enabled
  * @retval     0xF0F0000A  Trigger KPROM key comparison is FORBID
  * @retval     0xF0F0000B  KPROM Key is mismatch
  * @retval     0xF0F0000C  KPROM key still locked
  * @retval     0           KPROM Key are matched
  * @details    With this API, user can unlock KPROM write-protection and then execute FMC program command well.
  */
int32_t BL_TrgKPROMCompare(uint32_t key0, uint32_t key1, uint32_t key2);


/**
  * @brief      Execute CHIP Reset
  * @param      None
  * @return     None
  * @details    This API will perform reset CHIP command to reset chip.
  */
void BL_ResetChip(void);


/*--------------------------------------------------------------------------------------------------*/
/*  The following functions are for Secure code only                                                */
/*--------------------------------------------------------------------------------------------------*/
/**
  * @brief      Check if ECC Private Key Valid
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[in]  ecc_curve   The pre-defined ECC curve.
  * @param[in]  private_k   The input private key.
  * @return     1   Is valid.
  * @return     0   Is not valid.
  * @return     -1  Invalid curve.
  * @details    This API is used to check if the private key is placed in valid range of curve.
  */
int32_t XECC_IsPrivateKeyValid(XCRPT_T *xcrpt, E_ECC_CURVE ecc_curve, char private_k[]);


/**
  * @brief      Generate ECC Public Key
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[in]  ecc_curve   The pre-defined ECC curve.
  * @param[in]  private_k   The input private key.
  * @param[out] public_k1   The output public key 1.
  * @param[out] public_k2   The output public key 2.
  * @return     0   Success.
  * @return     -1  "ecc_curve" value is invalid.
  * @details    This API is used to generate a public key pair by a specified ECC private key and ECC curve.
  */
int32_t XECC_GeneratePublicKey(XCRPT_T *xcrpt, E_ECC_CURVE ecc_curve, char *private_k, char public_k1[], char public_k2[]);


/**
  * @brief      Generate ECDSA Signature
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[in]  ecc_curve   The pre-defined ECC curve.
  * @param[in]  message     The hash value of source context.
  * @param[in]  d           The private key.
  * @param[in]  k           The selected random integer.
  * @param[out] R           R of the (R,S) pair digital signature
  * @param[out] S           S of the (R,S) pair digital signature
  * @return     0   Success.
  * @return     -1  "ecc_curve" value is invalid.
  * @details    This API is used to generate an ECDSA digital signature.
  */
int32_t XECC_GenerateSignature(XCRPT_T *xcrpt, E_ECC_CURVE ecc_curve, char *message, char *d, char *k, char *R, char *S);


/**
  * @brief      Verify ECDSA Signature
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[in]  ecc_curve   The pre-defined ECC curve.
  * @param[in]  message     The hash value of source context.
  * @param[in]  public_k1   The public key 1.
  * @param[in]  public_k2   The public key 2.
  * @param[in]  R           R of the (R,S) pair digital signature
  * @param[in]  S           S of the (R,S) pair digital signature
  * @return     0   Success.
  * @return     -1  "ecc_curve" value is invalid.
  * @return     -2  Verification failed.
  * @details    This API is used to perform the ECDSA digital signature verification.
  */
int32_t XECC_VerifySignature(XCRPT_T *xcrpt, E_ECC_CURVE ecc_curve, char *message, char *public_k1, char *public_k2, char *R, char *S);


/**
  * @brief      Generate ECDH Secret Shared Key
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[in]  ecc_curve   The pre-defined ECC curve.
  * @param[in]  private_k   One's own private key.
  * @param[in]  public_k1   The other party's public key 1.
  * @param[in]  public_k2   The other party's public key 2.
  * @param[out] secret_z    The ECC CDH secret Z.
  * @return     0   Success.
  * @return     -1  "ecc_curve" value is invalid.
  * @details    This API is used to generate an ECDH shared key.
  */
int32_t XECC_GenerateSecretZ(XCRPT_T *xcrpt, E_ECC_CURVE ecc_curve, char *private_k, char public_k1[], char public_k2[], char secret_z[]);


/**
  * @brief      Convert Data to Hex Format
  * @param[in]  count   Byte counts for convert.
  * @param[in]  reg     The input data buffer.
  * @param[out] output  The output data buffer.
  * @return     None
  * @details    This API is used to convert the data to hex format.
  */
void XECC_Reg2Hex(int32_t count, uint32_t volatile reg[], char output[]);


/**
  * @brief      Convert Data to Register Format
  * @param[in]  input   The input data buffer.
  * @param[out] reg     The output data buffer.
  * @return     None
  * @details    This API is used to convert the data in a register data format.
  */
void XECC_Hex2Reg(char input[], uint32_t volatile reg[]);


/**
  * @brief      Get ID ECC R, S digital signature (for Secure code)
  * @param[out] R           R of the (R,S) pair digital signature
  * @param[out] S           S of the (R,S) pair digital signature
  * @retval     -1          Get R, S digital signature fail
  * @retval     0           Success
  * @details    This API will return ECC R, S digital signature of chip ID, include PDID, UID0~2 and UCID0~3.
  */
int32_t XECC_GetIDECCSignature(uint32_t *R, uint32_t *S);


/**
  * @brief      Open TDES Encrypt/Decrypt
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[in]  u32Channel  TDES channel. Must be 0~3.
  * @param[in]  u32EncDec   1: TDES encode; 0: TDES decode
  * @param[in]  Is3DES      1: TDES; 0: DES
  * @param[in]  Is3Key      1: TDES 3 key mode; 0: TDES 2 key mode
  * @param[in]  u32OpMode   TDES operation mode, including:
  *                 - \ref TDES_MODE_ECB
  *                 - \ref TDES_MODE_CBC
  *                 - \ref TDES_MODE_CFB
  *                 - \ref TDES_MODE_OFB
  *                 - \ref TDES_MODE_CTR
  * @param[in]  u32SwapType is TDES input/output data swap control and word swap control, including:
  *                 - \ref TDES_NO_SWAP
  *                 - \ref TDES_WHL_SWAP
  *                 - \ref TDES_OUT_SWAP
  *                 - \ref TDES_OUT_WHL_SWAP
  *                 - \ref TDES_IN_SWAP
  *                 - \ref TDES_IN_WHL_SWAP
  *                 - \ref TDES_IN_OUT_SWAP
  *                 - \ref TDES_IN_OUT_WHL_SWAP
  * @return     None
  * @details    This API is used to enable TDES encrypt/decrypt function.
  */
void XTDES_Open(XCRPT_T *xcrpt, uint32_t u32Channel, uint32_t u32EncDec, int32_t Is3DES, int32_t Is3Key, uint32_t u32OpMode, uint32_t u32SwapType);


/**
  * @brief      Start TDES Encrypt/Decrypt
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[in]  u32Channel  TDES channel. Must be 0~3.
  * @param[in]  u32DMAMode  TDES DMA control, including:
  *                 - \ref CRYPTO_DMA_ONE_SHOT  One shot TDES encrypt/decrypt.
  *                 - \ref CRYPTO_DMA_CONTINUE  Continuous TDES encrypt/decrypt.
  *                 - \ref CRYPTO_DMA_LAST      Last TDES encrypt/decrypt of a series of XTDES_Start.
  * @return     None
  * @details    This API is used to start TDES encrypt/decrypt.
  */
void XTDES_Start(XCRPT_T *xcrpt, int32_t u32Channel, uint32_t u32DMAMode);


/**
  * @brief      Set TDES Keys
  * @param[in]  xcrpt           The pointer of the global XCRPT data
  * @param[in]  u32Channel      TDES channel. Must be 0~3.
  * @param[in]  au32Keys        The TDES keys. au32Keys[0][0] is Key0 high word and au32Keys[0][1] is key0 low word.
  * @return     None
  * @details    This API is used to set TDES keys.
  */
void XTDES_SetKey(XCRPT_T *xcrpt, uint32_t u32Channel, uint32_t au32Keys[3][2]);


/**
  * @brief      Set TDES Initial Vectors
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[in]  u32Channel  TDES channel. Must be 0~3.
  * @param[in]  u32IVH      TDES initial vector high word.
  * @param[in]  u32IVL      TDES initial vector low word.
  * @return     None
  * @details    This API is used to set TDES initial vectors.
  */
void XTDES_SetInitVect(XCRPT_T *xcrpt, uint32_t u32Channel, uint32_t u32IVH, uint32_t u32IVL);


/**
  * @brief      Set TDES DMA Transfer Configuration
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[in]  u32Channel  TDES channel. Must be 0~3.
  * @param[in]  u32SrcAddr  TDES DMA source address
  * @param[in]  u32DstAddr  TDES DMA destination address
  * @param[in]  u32TransCnt TDES DMA transfer byte count
  * @return     None
  * @details    This API is used to configure the TDES DMA transfer.
  */
void XTDES_SetDMATransfer(XCRPT_T *xcrpt, uint32_t u32Channel, uint32_t u32SrcAddr, uint32_t u32DstAddr, uint32_t u32TransCnt);


/**
  * @brief      Open SHA Encrypt
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[in]  u32OpMode   SHA operation mode, including:
  *                 - \ref SHA_MODE_SHA1
  *                 - \ref SHA_MODE_SHA224
  *                 - \ref SHA_MODE_SHA256
  *                 - \ref SHA_MODE_SHA384
  *                 - \ref SHA_MODE_SHA512
  * @param[in]  u32SwapType is the SHA input/output data swap control, including:
  *                 - \ref SHA_NO_SWAP
  *                 - \ref SHA_OUT_SWAP
  *                 - \ref SHA_IN_SWAP
  *                 - \ref SHA_IN_OUT_SWAP
  * @param[in]  hmac_key_len    HMAC key byte count
  * @return     None
  * @details    This API is used to enable SHA encrypt function.
  */
void XSHA_Open(XCRPT_T *xcrpt, uint32_t u32OpMode, uint32_t u32SwapType, uint32_t hmac_key_len);


/**
  * @brief      Start SHA Encrypt
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[in]  u32DMAMode  SHA DMA control, including:
  *                 - \ref CRYPTO_DMA_ONE_SHOT  One shot SHA encrypt.
  *                 - \ref CRYPTO_DMA_CONTINUE  Continuous SHA encrypt.
  *                 - \ref CRYPTO_DMA_LAST      Last SHA encrypt of a series of XSHA_Start.
  * @return     None
  * @details    This API is used to start SHA encrypt.
  */
void XSHA_Start(XCRPT_T *xcrpt, uint32_t u32DMAMode);


/**
  * @brief      Set SHA DMA Transfer Configuration
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[in]  u32SrcAddr  SHA DMA source address
  * @param[in]  u32TransCnt SHA DMA transfer byte count
  * @return     None
  * @details    This API is used to configure the SHA DMA transfer.
  */
void XSHA_SetDMATransfer(XCRPT_T *xcrpt, uint32_t u32SrcAddr, uint32_t u32TransCnt);


/**
  * @brief      Read SHA Digest
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[out] u32Digest   The SHA encrypt output digest.
  * @return     None
  * @details    This API is used to read the SHA digest.
  */
void XSHA_Read(XCRPT_T *xcrpt, uint32_t u32Digest[]);


/**
  * @brief      Open AES Encrypt/Decrypt
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[in]  u32Channel  AES channel. Must be 0~3.
  * @param[in]  u32EncDec   1: AES encode;  0: AES decode
  * @param[in]  u32OpMode   AES operation mode, including:
  *                 - \ref AES_MODE_ECB
  *                 - \ref AES_MODE_CBC
  *                 - \ref AES_MODE_CFB
  *                 - \ref AES_MODE_OFB
  *                 - \ref AES_MODE_CTR
  *                 - \ref AES_MODE_CBC_CS1
  *                 - \ref AES_MODE_CBC_CS2
  *                 - \ref AES_MODE_CBC_CS3
  * @param[in]  u32KeySize is AES key size, including:
  *                 - \ref AES_KEY_SIZE_128
  *                 - \ref AES_KEY_SIZE_192
  *                 - \ref AES_KEY_SIZE_256
  * @param[in]  u32SwapType is AES input/output data swap control, including:
  *                 - \ref AES_NO_SWAP
  *                 - \ref AES_OUT_SWAP
  *                 - \ref AES_IN_SWAP
  *                 - \ref AES_IN_OUT_SWAP
  * @return     None
  * @details    This API is used to enable AES encrypt/decrypt function.
  */
void XAES_Open(XCRPT_T *xcrpt, uint32_t u32Channel, uint32_t u32EncDec, uint32_t u32OpMode, uint32_t u32KeySize, uint32_t u32SwapType);


/**
  * @brief      Start AES Encrypt/Decrypt
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[in]  u32Channel  AES channel. Must be 0~3.
  * @param[in]  u32DMAMode  AES DMA control, including:
  *                     - \ref CRYPTO_DMA_ONE_SHOT  One shot AES encrypt/decrypt.
  *                     - \ref CRYPTO_DMA_CONTINUE  Continuous AES encrypt/decrypt.
  *                     - \ref CRYPTO_DMA_LAST      Last AES encrypt/decrypt of a series of XAES_Start.
  * @return     None
  * @details    This API is used to start AES encrypt/decrypt.
  */
void XAES_Start(XCRPT_T *xcrpt, int32_t u32Channel, uint32_t u32DMAMode);


/**
  * @brief      Set AES Keys
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[in]  u32Channel  AES channel. Must be 0~3.
  * @param[in]  au32Keys    An word array contains AES keys.
  * @param[in]  u32KeySize is AES key size, including:
  *                 - \ref AES_KEY_SIZE_128
  *                 - \ref AES_KEY_SIZE_192
  *                 - \ref AES_KEY_SIZE_256
  * @return     None
  * @details    This API is used to set AES keys.
  */
void XAES_SetKey(XCRPT_T *xcrpt, uint32_t u32Channel, uint32_t au32Keys[], uint32_t u32KeySize);


/**
  * @brief      Set AES Initial Vectors
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[in]  u32Channel  AES channel. Must be 0~3.
  * @param[in]  au32IV      A four entry word array contains AES initial vectors.
  * @return     None
  * @details    This API is used to set AES initial vectors.
  */
void XAES_SetInitVect(XCRPT_T *xcrpt, uint32_t u32Channel, uint32_t au32IV[]);


/**
  * @brief      Set AES DMA Transfer Configuration
  * @param[in]  xcrpt       The pointer of the global XCRPT data
  * @param[in]  u32Channel   AES channel. Must be 0~3.
  * @param[in]  u32SrcAddr   AES DMA source address
  * @param[in]  u32DstAddr   AES DMA destination address
  * @param[in]  u32TransCnt  AES DMA transfer byte count
  * @return     None
  * @details    This API is used to configure the AES DMA transfer.
  */
void XAES_SetDMATransfer(XCRPT_T *xcrpt, uint32_t u32Channel, uint32_t u32SrcAddr, uint32_t u32DstAddr, uint32_t u32TransCnt);


/**
  * @brief      Initial Random Number Generator (for Secure code)
  *
  * @param[in]  rng     The structure of random number generator
  * @param[in]  opt     Operation modes. Possible options are,
  *                         (XTRNG_PRNG | XTRNG_LIRC32K),
  *                         (XTRNG_PRNG | XTRNG_LXT),
  *                         (XTRNG_SWRNG | XTRNG_LIRC32K),
  *                         (XTRNG_SWRNG | XTRNG_LXT)
  * @retval     -1      Fail
  * @retval     0       Success
  *
  * @details    This API is used to initial random number generator.
  *             After initial this API success, user can call XTRNG_Random API to generate the random number.
  */
int32_t XTRNG_RandomInit(XTRNG_T *rng, uint32_t opt);


/**
  * @brief      Generate Random Number (for Secure code)
  *
  * @param[in]  rng     The structure of random number generator
  * @param[out] p       Starting buffer address to store random number
  * @param[in]  size    Total byte counts of random number
  * @retval     -1      Fail
  * @retval     0       Success
  * @details    This API is used to generate random number.
  */
int32_t XTRNG_Random(XTRNG_T *rng, uint8_t *p, uint32_t size);


/**
  * @brief      Get ID ECC R, S Digital Signature (for Secure code)
  * @param[out] R           R of the (R,S) pair digital signature
  * @param[out] S           S of the (R,S) pair digital signature
  * @retval     -1          Get R, S digital signature fail
  * @retval     0           Success
  * @details    This API will return ECC R, S digital signature of chip ID, include PDID, UID0~2 and UCID0~3.
  */
int32_t BL_GetIDECCSignature(uint32_t *R, uint32_t *S);


/**
  * @brief      Initial Random Number Generator (for Secure code)
  *
  * @param[in]  rng     The structure of random number generator
  * @param[in]  opt     Operation modes. Possible options are,
  *                         (BL_RNG_PRNG | BL_RNG_LIRC32K),
  *                         (BL_RNG_PRNG | BL_RNG_LXT),
  *                         (BL_RNG_SWRNG | BL_RNG_LIRC32K),
  *                         (BL_RNG_SWRNG | BL_RNG_LXT)
  * @retval     -1      Fail
  * @retval     0       Success
  *
  * @details    This API is used to initial random number generator.
  *             After initial this API success, user can perform BL_Random API to generate the random number.
  */
int32_t BL_RandomInit(BL_RNG_T *rng, uint32_t opt);


/**
  * @brief      Generate Random Number (for Secure code)
  *
  * @param[in]  rng     The structure of random number generator
  * @param[out] p       Starting buffer address to store random number
  * @param[in]  size    Total byte counts of random number
  * @retval     -1      Fail
  * @retval     0       Success
  * @details    This API is used to generate random number.
  */
int32_t BL_Random(BL_RNG_T *rng, uint8_t *p, uint32_t size);


/**
  * @brief      Initialize SecureISP Function (for Secure code)
  * @param[in]  pISPInfo    The ISP information data buffer address
  * @param[in]  pUSBDInfo   USB data buffer for SecureISP USB
  * @param[in]  mode        Operation mode. Possible options are
  *                             - \ref USB_MODE
  *                             - \ref UART_MODE
  *                             - \ref USB_UART_MODE
  *                             - \ref RESYNC_ISP
  * @return     Return process status and exit SecureISP mode.
  * @details    Executing this API will initialize USB or UART1 SecureISP function.
  *             User can use SecureISP Tool to communicate with target chip.
  * @note       Configure relate USB and UART1 settings are necessary before executing this API.
  */
int32_t BL_SecureISPInit(ISP_INFO_T *pISPInfo, BL_USBD_INFO_T *pUSBDInfo, E_ISP_MODE mode);


/**
  * @brief      Process USBD Interrupt (for Secure code)
  * @param[in]  pfnEPTable      Starting address to store EP callback function
  * @param[in]  pInfo           The ISP information data buffer address
  * @param[in]  pUSBDInfo       USB data buffer for SecureISP USB
  * @retval     -1      Execute API in Non-secure code
  * @retval     0       Process USBD interrupt event success
  * @details    This API is used to process USBD command and should be called in USBD_IRQHandler().
  */
int32_t BL_ProcessUSBDInterrupt(uint32_t *pfnEPTable, uint32_t *pInfo, uint32_t *pUSBDInfo);


/**
  * @brief      Process UART1 Interrupt (for Secure code)
  * @param[in]  pInfo   The ISP information data buffer address
  * @retval     -1      Execute API in Non-secure code
  * @retval     0       Process UART1 interrupt event success
  * @details    This API is used to process UART1 command and should be called in UART1_IRQHandler().
  */
int32_t BL_ProcessUART1Interrupt(uint32_t *pInfo);


/**
  * @brief      Get Vendor Data (for Secure code)
  * @param[in]  pInfo       The ISP information data buffer address
  * @param[out] pu32Data    Data buffer to store vendor data. Maximum buffer size is 44 bytes.
  * @param[in]  pu32Buf     Internal used data buffer address
  * @retval     0           Success
  * @retval     -1          Invalid command packet
  * @retval     -2          Not in vendor function
  * @details    This API is used to get the vendor data and should be called in the vendor function.
  */
int32_t BL_GetVendorData(uint32_t *pInfo, uint32_t *pu32Data, uint32_t *pu32Buf);


/**
  * @brief      Return Vendor Data (for Secure code)
  * @param[in]  pu32Data    Data buffer to store response data
  * @param[in]  u32Len      Data buffer length, maximum size is 40 bytes.
  * @param[in]  pu32Buf     Internal used data buffer address
  * @retval     0           Success
  * @retval     -1          Invalid buffer length
  * @retval     -2          Not in vendor function
  * @details    This API is used to return vendor data to server and should be called in the vendor function.
  */
int32_t BL_ReturnVendorData(uint32_t *pu32Data, uint32_t u32Len, uint32_t *pu32Buf);


/**
  * @brief      Generate Command Response Data (for Secure code)
  * @param[in]  pCMD        Buffer address to store command data
  * @param[in]  pISPInfo    The ISP information data buffer address
  * @retval     0           Command success
  * @retval     Other       Command fail
  * @details    This API is used to generate response data to server.
  */
int32_t Cmd_GenRspPacket(CMD_PACKET_T *pCMD, ISP_INFO_T *pISPInfo);


/**
  * @brief      Parse Command (for Secure code)
  * @param[in]  pCMD        Buffer address to store command
  * @param[in]  pISPInfo    The ISP information data buffer address
  * @retval     0           Command success
  * @retval     Other       Command fail
  * @details    This API is used to parse data from server.
  */
int32_t Cmd_ParseReqPacket(CMD_PACKET_T *pCMD, ISP_INFO_T *pISPInfo);


/**
  * @brief      Parse CONNECT Command (for Secure code)
  * @param[in]  pISPInfo    The ISP information data buffer address
  * @retval     0           Success
  * @retval     Other       Command fail
  * @details    This API is used for parse CONNECT command only.
  */
int32_t ParseCONNECT(ISP_INFO_T *pISPInfo);


/**
  * @brief      Parse related ECDH Commands (for Secure code)
  * @param[in]  pISPInfo    The ISP information data buffer address
  * @retval     0           Success
  * @retval     Other       Command fail
  * @details    This API is used for parse related ECDH commands.
  */
int32_t ParseECDH(ISP_INFO_T *pISPInfo);


/**
  * @brief      Parse Commands (for Secure code)
  * @param[in]  pISPInfo    The ISP information data buffer address
  * @retval     0           Success
  * @retval     Other       Command fail
  * @details    This API is used for parse all commands except CONNECT and related ECDH commands.
  */
int32_t ParseCommands(ISP_INFO_T *pISPInfo);


/**
  * @brief      Initialize USBD Module (for Secure code)
  * @param[in]  param           The structure of USBD information
  * @param[in]  pfnClassReq     USB Class request callback function
  * @param[in]  pfnSetInterface USB Set Interface request callback function
  * @param[in]  pUSBDInfo       USB data buffer for SecureISP USB mode
  * @retval     -1              Execute API in Non-secure code
  * @retval     0               Success
  * @details    This function will enable USB controller, USB PHY transceiver and pull-up resistor of USB_D+ pin. USB PHY will drive SE0 to bus.
  */
int32_t BL_USBDOpen(const S_USBD_INFO_T *param, CLASS_REQ pfnClassReq, SET_INTERFACE_REQ pfnSetInterface, uint32_t *pUSBDInfo);


/**
  * @brief      Install EP Callback Function (for Secure code)
  * @param[in]  ep              EP number
  * @param[in]  pfnEPHandler    EP callback function
  * @param[in]  pfnEPTable      Starting address to store EP callback function
  * @retval     -1      Fail
  * @retval     0       Success
  * @details    This function is used to set specific EP callback function
  */
int32_t BL_USBDInstallEPHandler(uint32_t ep, void *pfnEPHandler, uint32_t *pfnEPTable);


/**
  * @brief      Start USBD Function (for Secure code)
  * @param      None
  * @retval     -1      Execute API in Non-secure code
  * @retval     0       Success
  * @details    Enable WAKEUP, FLDET, USB and BUS interrupts. Disable software-disconnect function after 100ms delay with SysTick timer.
  */
int32_t BL_USBDStart(void);


/*@}*/ /* end of group MKROM_EXPORTED_FUNCTIONS */

/*@}*/ /* end of group MKROM_Driver */

/*@}*/ /* end of group Standard_Driver */


#ifdef __cplusplus
}
#endif

#endif  /* __MKROM_LIB_H__ */

/*** (C) COPYRIGHT 2018 Nuvoton Technology Corp. ***/
