/*
 * @brief Enhanced Host Controller Interface
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * All rights reserved.
 *
 * @par
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licensor disclaim any and
 * all warranties, express or implied, including all implied warranties of
 * merchantability, fitness for a particular purpose and non-infringement of
 * intellectual property rights.  NXP Semiconductors assumes no responsibility
 * or liability for the use of the software, conveys no license or rights under any
 * patent, copyright, mask work right, or any other intellectual property rights in
 * or to any products. NXP Semiconductors reserves the right to make changes
 * in the software without notification. NXP Semiconductors also makes no
 * representation or warranty that such application will be suitable for the
 * specified use without further testing or modification.
 *
 * @par
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
 */
/** @ingroup Group_HCD
 *  @defgroup Host_EHCI Enhanced Host Controller Interface Driver
 *  @{
 */
#ifndef __LPC_EHCI_H__
#define __LPC_EHCI_H__

#ifndef __LPC_EHCI_C__	// TODO INCLUDE FROM EHCI.C
	#error "EHCI.h is private header and can only be included by EHCI.c, try to include HCD.h instead"
#endif

#ifdef __TEST__	// suppress static/inline for Testing purpose
	#define static
	#define inline
#endif

/*=======================================================================*/
/*  EHCI C O N F I G U R A T I O N                        */
/*=======================================================================*/
#define HCD_MAX_QHD					HCD_MAX_ENDPOINT		/* USBD_USB_HC_EHCI */
//#define	HCD_MAX_QTD					(HCD_MAX_ENDPOINT+3)	/* USBD_USB_HC_EHCI */
#define	HCD_MAX_QTD					8						/* USBD_USB_HC_EHCI */
#define	HCD_MAX_HS_ITD				4						/* USBD_USB_HC_EHCI */
#define HCD_MAX_SITD				16						/* USBD_USB_HC_EHCI */

#define FRAMELIST_SIZE_BITS         5			/* (0:1024) - (1:512) - (2:256) - (3:128) - (4:64) - (5:32) - (6:16) - (7:8) */
#define FRAME_LIST_SIZE             (1024 >> FRAMELIST_SIZE_BITS)

/**********************/
/* USBCMD Register */
/**********************/
#define INT_THRESHOLD_CTRL              0x00080000UL/* Max Int Interval = 8 uframes */
#define ASYNC_SCHEDULE_PARK_MODE_ENABLE NO
#define ASYNC_SCHEDULE_PARK_MODE_COUNT  0

/****************************/
/* USBSTS Register */
/****************************/

/**************************************************/
/* USBINTR Register */
/**************************************************/
#define INT_SOF_RECEIVED_ENABLE NO
// #define INT_ASYNC_ADVANCE_ENABLE	Must be YES
// #define	INT_SYSTEM_ERR_ENABLE	Must be	YES
#define INT_FRAME_ROLL_OVER_ENABLE  NO
// #define	INT_PORT_CHANGE_ENABLE	Must be	YES
// #define	INT_USB_ERR_ENABLE		Must be	YES
// #define	INT_USB_ENABLE			Must be	YES (NO for NXP chips in favor of UAI, UPI)
// #define	INT_USB_ASYNC_INT_ENABLE	Must be YES
// #define	INT_USB_PERIOD_INT_ENABLE	Must be YES

/********************************************/
/* PORTSC Register */
/********************************************/
#define PORT_WAKE_OVER_CURRENT                  NO
#define PORT_WAKE_ON_DISCONNECT                 NO
#define PORT_WAKE_ON_CONNECT                    NO
#define PORT_INDICATOR                          NO

/*==========================================================================*/
/* EHCI LOCAL DECLARATIONS                                                                  */
/*==========================================================================*/

/*==========================================================================*/
/* EHCI REGISTERS                                                                   */
/*==========================================================================*/
/* Bit field definition for USBMODE_H */
#define USBMODE_DeviceController                (2)
#define USBMODE_HostController                  (3)
#define USBMODE_VBusPowerSelect_High            (1 << 5)

/* Bit field definition for register UsbCmd */
#define EHC_USBCMD_RunStop                      0x00000001UL		/* Run or Stop */
#define EHC_USBCMD_HostReset                    0x00000002UL		/* Host Controller Reset */
#define EHC_USBCMD_FrameListSize                0x0000000CUL		/* Frame List Size */
#define EHC_USBCMD_PeriodScheduleEnable         0x00000010UL		/* Periodic Schedule Enable */
#define EHC_USBCMD_AsynScheduleEnable           0x00000020UL		/* Asynchronous Schedule Enable */
#define EHC_USBCMD_IntAsyncAdvanceDoorbell      0x00000040UL		/* Interrupt on Async Advance Doorbell */
#define EHC_USBCMD_LightReset                   0x00000080UL		/* Light Host Controller Reset */
#define EHC_USBCMD_AsyncScheduleParkCount       0x00000300UL		/* Asynchronous Schedule Park Mode Count */
#define EHC_USBCMD_AsyncScheduleParkEnable      0x00000800UL		/* Asynchronous Schedule Park Mode Enable */
#define EHC_USBCMD_FrameListSizeBit2            0x00008000UL		/* Frame List Size bit 2 - EHCI derivation */
#define EHC_USBCMD_InterruptThresholdControl    0x00FF0000UL		/* Interrupt Threshold control */

/* Bit field definition for register UsbStatus */
#define EHC_USBSTS_UsbInt                       0x00000001UL		/* USB Interrupt */
#define EHC_USBSTS_UsbErrorInt                  0x00000002UL		/* USB Error Interrupt */
#define EHC_USBSTS_PortChangeDetect             0x00000004UL		/* Port Change Detect */
#define EHC_USBSTS_FrameListRollover            0x00000008UL		/* Frame List Rollover */
#define EHC_USBSTS_HostSystemError              0x00000010UL		/* Host System Error */
#define EHC_USBSTS_IntAsyncAdvance              0x00000020UL		/* Interrupt on Async Advance */
#define EHC_USBSTS_SofRecieveInt                0x00000080UL		/* SOF - EHCI derivation */
#define EHC_USBSTS_HCHalted                     0x00001000UL		/* HCHalted */
#define EHC_USBSTS_Reclamation                  0x00002000UL		/* Reclamation */
#define EHC_USBSTS_PeriodScheduleStatus         0x00004000UL		/* Periodic Schedule Status */
#define EHC_USBSTS_AsyncScheduleStatus          0x00008000UL		/* Asynchronous Schedule Status */
#define EHC_USBSTS_UsbAsyncInt                  0x00040000UL		/* USB Asynchronous Interrupt - EHCI derivation */
#define EHC_USBSTS_UsbPeriodInt                 0x00080000UL		/* USB Period Interrupt - EHCI derivation */

/* Bit field definition for register UsbIntr */
#define EHC_USBINTR_UsbIntEnable                0x00000001UL		/* USB Interrupt Enable */
#define EHC_USBINTR_UsbErroIntEnable            0x00000002UL		/* USB Error Interrupt Enable */
#define EHC_USBINTR_PortChangeIntEnable         0x00000004UL		/* Port Change Interrupt Enable */
#define EHC_USBINTR_FrameListRolloverEnable     0x00000008UL		/* Frame List Rollover Enable */
#define EHC_USBINTR_HostSystemErrorEnable       0x00000010UL		/* Host System Error Enable */
#define EHC_USBINTR_IntAsyncAdvanceEnable       0x00000020UL		/* Interrupt on Async Advance Enable */
#define EHC_USBINTR_SofRecieveEnable            0x00000080UL		/* SOF - EHCI derivation */
#define EHC_USBINTR_UsbAsyncEnable              0x00040000UL		/* USB Asynchronous Interrupt - EHCI derivation */
#define EHC_USBINTR_UsbPeriodEnable             0x00080000UL		/* USB Period Interrupt - EHCI derivation */
#define EHC_USBINTR_ALL                         0x000C00BFUL		/* All Interrupt */

/* Bit field definition for register FrIndex */
#define EHC_FRINDEX_MASK                        0x000003FFUL		/* Frame Index */
#define EHC_UFRAME_MASK                         0x00000007UL		/* u-Frame Index */
#define EHC_MFRAME_MASK                         0x00001FF8UL		/* m-Frame Index */

/* Bit field definition for register PortSC */
#define EHC_PORTSC_CurrentConnectStatus         0x00000001UL		/* Current Connect Status */
#define EHC_PORTSC_ConnectStatusChange          0x00000002UL		/* Connect Status Change */
#define EHC_PORTSC_PortEnable                   0x00000004UL		/* Port Enabled Status */
#define EHC_PORTSC_PortEnableChange             0x00000008UL		/* Port Enabled/Disabled Change */
#define EHC_PORTSC_OvercurrentActive            0x00000010UL		/* Over-current Status */
#define EHC_PORTSC_OvercurrentChange            0x00000020UL		/* Over-current Change */
#define EHC_PORTSC_ForcePortResume              0x00000040UL		/* Force Port Resume */
#define EHC_PORTSC_PortSuspend                  0x00000080UL		/* Port Suspend */
#define EHC_PORTSC_PortReset                    0x00000100UL		/* Port Reset */
#define EHC_PORTSC_LineStatus                   0x00000C00UL		/* Line Status */
#define EHC_PORTSC_PortPowerControl             0x00001000UL		/* Port Power Status */
#define EHC_PORTSC_PortOwner                    0x00002000UL		/* Port Owner Status */
#define EHC_PORTSC_PortIndicatorControl         0x0000C000UL		/* Port Indicator Control */
#define EHC_PORTSC_PortTestControl              0x000F0000UL		/* Port Test Control */
#define EHC_PORTSC_WakeonConnectEnable          0x00100000UL		/* Wake on Connect Enable */
#define EHC_PORTSC_WakeonDisconnectEnable       0x00200000UL		/* Wake on Disconnect Enable */
#define EHC_PORTSC_WakeonOvercurrentEnable      0x00400000UL		/* Wake on Over-Current Enable */
#define EHC_PORTSC_PhyClockDisable              0x00800000UL		/* PHY Clock Disable - EHCI derivation */
#define EHC_PORTSC_PortForceFullspeedConnect    0x01000000UL		/* Force Device on Fullspeed mode (disable chirp sequences) - EHCI derivation */
#define EHC_PORTSC_PortSpeed                    0x0C000000UL		/* Device Speed - EHCI derivation */

/* Definitions for Frame List Element Pointer */
#define QTD_MAX_XFER_LENGTH                     0x5000
#define FRAMELIST_ALIGNMENT                     4096				/* Frame List Alignment */
//#define LINK_TERMINATE                          0x01
#define SPLIT_MAX_LEN_UFRAME                    188

/*=======================================================================*/
/*  E H C I		S T R U C T U R E S				*/
/*=======================================================================*/

/* Memory for EHCI Structures, docs for more information */

typedef union un_EHCD_Link {
	uint32_t Link;
	struct  {
		uint32_t Terminate : 1;
		uint32_t Type  : 2;
	};

} NextLinkPointer;

typedef struct st_EHCD_QTD {
	/*---------- Word 1 ----------*/
	uint32_t NextQtd;

	/*---------- Word 2 ----------*/
	/*-- Take advantage of this to store HCD information --*/
	union {
		uint32_t AlterNextQtd;
		struct  {
			uint32_t Terminate : 1;
			uint32_t : 4;

			// === TODO: used reserved space, need to move to other place ===
			/*-- HCD Area --*/
			uint32_t inUse : 1;
			uint32_t : 0;
		};

	};

	/*---------- Word 3 ----------*/
	/* Status [7:0] */
	__IO uint32_t PingState_Err : 1;
	__IO uint32_t SplitXstate : 1;
	__IO uint32_t MissedUframe : 1;
	__IO uint32_t TransactionError : 1;
	__IO uint32_t Babble : 1;
	__IO uint32_t BufferError : 1;
	__IO uint32_t Halted : 1;
	__IO uint32_t Active : 1;

	uint32_t PIDCode : 2;
	__IO uint32_t ErrorCounter : 2;
	__IO uint32_t CurrentPage : 3;
	uint32_t IntOnComplete : 1;
	__IO uint32_t TotalBytesToTransfer : 15;
	__IO uint32_t DataToggle : 1;
	uint32_t                    : 0;/* Force next member on next storage unit */
	/*---------- End Word 3 ----------*/

	/*---------- Buffer Pointer Word 4-7 ----------*/
	uint32_t BufferPointer[5];
} HCD_QTD, *PHCD_QTD;	// TODO: because QTD is used to declare overlay in HCD_QHD, we cannot put aligned 32 here ATTR_ALIGNED(32)

typedef struct st_EHCD_QHD {
	/*---------- Word 1 ----------*/
	NextLinkPointer Horizontal;

	/*---------- Word 2 ----------*/
	uint32_t DeviceAddress             : 7;
	uint32_t InActiveOnNextTransaction : 1;
	uint32_t EndpointNumber            : 4;
	uint32_t EndpointSpeed             : 2;
	uint32_t DataToggleControl         : 1;
	uint32_t HeadReclamationFlag       : 1;
	uint32_t MaxPackageSize            : 11;
	uint32_t ControlEndpointFlag       : 1;
	uint32_t NakCountReload            : 4;
	uint32_t                            : 0;/* Force next member on next storage unit */
	/*---------- End Word 2 ----------*/

	/*---------- Word 3 ----------*/
	uint32_t uFrameSMask       : 8;
	uint32_t uFrameCMask       : 8;
	uint32_t HubAddress        : 7;
	uint32_t PortNumber        : 7;
	uint32_t Mult               : 2;
	uint32_t                    : 0;/* Force next member on next storage unit */
	/*---------- End Word 3 ----------*/

	/*---------- Word 4 ----------*/
	__IO uint32_t CurrentQtd;

	/*---------- Overlay Area ----------*/
	__IO HCD_QTD Overlay;

	/*---------- HCD Area : 16 Bytes----------*/
	uint32_t inUse : 1;
	uint32_t Direction : 2;
	uint32_t Interval : 5;
	uint32_t ListIndex : 20;/* not support full period list */
	uint32_t            : 0;/* Force next member on next storage unit */

	__IO uint32_t status;	// TODO will remove __IO after remove all HcdQHD function
	uint32_t FirstQtd;	/* used as TD head to clean up TD chain when transfer done */
	uint16_t *pActualTransferCount;	/* total transferred bytes of a usb request */
} ATTR_ALIGNED (32) HCD_QHD, *PHCD_QHD;

typedef struct st_EHCD_ITD {
	/*---------- Word 1 ----------*/
	NextLinkPointer Horizontal;

	/*---------- Word 2-9 ----------*/
	struct  {
		__IO uint32_t Offset : 12;
		__IO uint32_t PageSelect : 3;
		uint32_t IntOnComplete : 1;
		__IO uint32_t Length : 12;
		/*-- status [31:28] --*/
		__IO uint32_t Error : 1;
		__IO uint32_t Babble : 1;
		__IO uint32_t BufferError : 1;
		__IO uint32_t Active : 1;
	} Transaction[8];

	/*---------- Word 10-16 ----------*/
	uint32_t BufferPointer[7];

	// FIXME: refractor to save memory HCD Area
	/*---------- HCD Area ----------*/
	uint32_t inUse;
	uint32_t IhdIdx;
	uint32_t reserved[6];
} ATTR_ALIGNED (32) HCD_HS_ITD, *PHCD_HS_ITD;

typedef struct st_EHCD_SITD {
	NextLinkPointer Horizontal;

	/*---------- Word 2: static endpoint ----------*/
	uint32_t DeviceAddress             : 7;
	uint32_t : 1;
	uint32_t EndpointNumber            : 4;
	uint32_t : 4;
	uint32_t HubAddress        : 7;
	uint32_t : 1;
	uint32_t PortNumber        : 7;
	uint32_t Direction : 1;
	uint32_t                            : 0;/* Force next member on next storage unit */
	/*---------- End Word 2 ----------*/

	/*---------- Word 3: Slipt Mask ----------*/
	uint8_t uFrameSMask;
	uint8_t uFrameCMask;
	uint16_t reserved;	/* Force next member on next storage unit */
	/*---------- End Word 3 ----------*/

	/*---------- Word 4: ----------*/
	/* Status [7:0] */
	__IO uint32_t  : 1;
	__IO uint32_t SplitXstate : 1;
	__IO uint32_t MissedUframe : 1;
	__IO uint32_t TransactionError : 1;
	__IO uint32_t Babble : 1;
	__IO uint32_t BufferError : 1;
	__IO uint32_t ERR : 1;
	__IO uint32_t Active : 1;

	__IO uint32_t uFrameCProgMask : 8;
	__IO uint32_t TotalBytesToTransfer : 10;
	__IO uint32_t : 4;
	__IO uint32_t PageSelect : 1;
	uint32_t IntOnComplete : 1;
	uint32_t : 0;
	/*---------- End Word 4 ----------*/

	/*---------- Word 5-6 ----------*/
	uint32_t BufferPointer[2];		/*-- in BufferPointer[1] TP: Transaction Position - T-Count: Transaction Count --*/

	//  union{
	//      uint32_t BufferPointer1;
	//      struct  {
	//          __IO uint32_t TCount : 3;
	//          __IO uint32_t TPosition : 2;
	//      };
	//  };

	/*---------- Word 7 ----------*/
	uint32_t BackPointer;

	/*-- HCD ARERA 4 bytes --*/
	uint8_t inUse;
	uint8_t IhdIdx;
	uint8_t reserved2[2];
} ATTR_ALIGNED (32) HCD_SITD, *PHCD_SITD;

typedef struct st_EHCI_HOST_DATA {
	HCD_HS_ITD          iTDs[HCD_MAX_HS_ITD];			/* Iso Transfer Descriptor */
	HCD_QHD             AsyncHeadQhd;					/* Serve as H-Queue Head in Async Schedule */
	HCD_QHD             IntHeadQhd;							/* Serve as Static 1ms Interrupt Heads */
	HCD_QHD             qHDs[HCD_MAX_QHD];				/* Queue Head */
	HCD_QTD             qTDs[HCD_MAX_QTD];				/* Queue Transfer Descriptor (Queue Element) */
	HCD_SITD            siTDs[HCD_MAX_SITD];			/* Split Iso Transfer Descriptor */
} EHCI_HOST_DATA_T;

typedef enum {
	ITD_TYPE = 0,
	QHD_TYPE,
	SITD_TYPE,
	FSTN_TYPE
} TD_TYPE;

typedef struct st_PipeHandle {
	uint8_t Idx;
	uint8_t Type;
	uint8_t PortNumber;
	uint8_t HostId;
} Pipe_Handle_T;

typedef struct st_PipeStreamHandle {
	uint32_t BufferAddress;
	uint32_t RemainBytes;
	uint16_t PacketSize;
	uint8_t  DataToggle;
} Pipe_Stream_Handle_T;

/*=======================================================================*/
/*  LOCAL   S Y M B O L   D E C L A R A T I O N S                        */
/*=======================================================================*/
extern EHCI_HOST_DATA_T ehci_data[MAX_USB_CORE];
// extern EHCI_HOST_DATA_T ehci_data;
extern NextLinkPointer      PeriodFrameList0[FRAME_LIST_SIZE];		/* Period Frame List */
extern NextLinkPointer      PeriodFrameList1[FRAME_LIST_SIZE];		/* Period Frame List */
#define EHCI_FRAME_LIST(HostID)     ((HostID) ? PeriodFrameList1 : PeriodFrameList0 )

/*=======================================================================*/
/*  G L O B A L   S Y M B O L   D E C L A R A T I O N S                  */
/*=======================================================================*/
void USB_Host_Enumerate (uint8_t HostID);

void USB_Host_DeEnumerate(uint8_t HostID);

/*=======================================================================*/
/* L O C A L   F U N C T I O N   P R O T O T Y P E S                     */
/*=======================================================================*/
/********************************* HOST API *********************************/
static INLINE HCD_STATUS EHciHostInit(uint8_t HostID);

static INLINE HCD_STATUS EHciHostRun(uint8_t HostID);

static INLINE HCD_STATUS EHciHostStop(uint8_t HostID);

static INLINE HCD_STATUS EHciHostReset(uint8_t HostID);

static void DisableAsyncSchedule(uint8_t HostID);

static void EnableAsyncSchedule(uint8_t HostID);

#if !defined(__ICCARM__)
static void DisablePeriodSchedule(uint8_t HostID) __attribute__ ((unused));	// TODO temporarily suppress unused warnnings for DisablePeriodSchedule & EnablePeriodSchedule

static void EnablePeriodSchedule(uint8_t HostID) __attribute__ ((unused));	// TODO temporarily suppress unused warnnings for DisablePeriodSchedule & EnablePeriodSchedule

#else
static void DisablePeriodSchedule(uint8_t HostID);	// TODO temporarily suppress unused warnnings for DisablePeriodSchedule & EnablePeriodSchedule

static void EnablePeriodSchedule(uint8_t HostID);	// TODO temporarily suppress unused warnnings for DisablePeriodSchedule & EnablePeriodSchedule

#endif
static INLINE void DisableSchedule(uint8_t HostID, uint8_t isPeriod);

static INLINE void EnableSchedule(uint8_t HostID, uint8_t isPeriod);

/********************************* HELPER *********************************/
static INLINE PHCD_QHD    HcdAsyncHead(uint8_t HostID);

static INLINE PHCD_QHD    HcdIntHead(uint8_t HostID);

static INLINE PHCD_QHD    HcdQHD(uint8_t HostID, uint8_t idx);

static INLINE PHCD_QTD    HcdQTD(uint8_t HostID, uint8_t idx);

static INLINE PHCD_HS_ITD HcdHsITD(uint8_t HostID, uint8_t idx);

static INLINE PHCD_SITD   HcdSITD(uint8_t HostID, uint8_t idx);

static INLINE bool        isValidLink(uint32_t link);

static INLINE bool IsInterruptQhd (uint8_t HostID, uint8_t QhdIdx);

/********************************* Queue Head & Queue TD *********************************/
static void FreeQhd(uint8_t HostID, uint8_t QhdIdx);

static HCD_STATUS AllocQhd(uint8_t HostID,
						   uint8_t DeviceAddr,
						   HCD_USB_SPEED DeviceSpeed,
						   uint8_t EndpointNumber,
						   HCD_TRANSFER_TYPE TransferType,
						   HCD_TRANSFER_DIR TransferDir,
						   uint16_t MaxPacketSize,
						   uint8_t Interval,
						   uint8_t Mult,
						   uint8_t HSHubDevAddr,
						   uint8_t HSHubPortNum,
						   uint32_t *pQhdIdx);

static HCD_STATUS InsertLinkPointer(NextLinkPointer *pList, NextLinkPointer *pNew, uint8_t type);

static HCD_STATUS RemoveQueueHead(uint8_t HostID, uint8_t QhdIdx);

static void FreeQtd(PHCD_QTD pQtd);

static HCD_STATUS AllocQTD (uint8_t HostID,
							uint32_t *pTdIdx,
							uint8_t *const BufferPointer,
							uint32_t xferLen,
							HCD_TRANSFER_DIR PIDCode,
							uint8_t DataToggle,
							uint8_t IOC);

static HCD_STATUS QueueQTDs (uint8_t HostID,
							 uint32_t* pTdIdx,
							 uint8_t* dataBuff,
							 uint32_t xferLen,
							 HCD_TRANSFER_DIR PIDCode,
							 uint8_t DataToggle);

/********************************* ISO Head & ISO TD & Split ISO *********************************/
static void FreeHsItd(PHCD_HS_ITD pItd);

static HCD_STATUS AllocHsItd(uint8_t HostID,
							 uint32_t *pTdIdx,
							 uint8_t IhdIdx,
							 uint8_t *dataBuff,
							 uint32_t TDLen,
							 uint8_t XactPerITD,
							 uint8_t IntOnComplete);

static HCD_STATUS QueueITDs(uint8_t HostID, uint8_t IhdIdx, uint8_t *dataBuff, uint32_t xferLen);

static void FreeSItd(PHCD_SITD pSItd);

static HCD_STATUS AllocSItd(uint8_t HostID,
							uint32_t *TdIdx,
							uint8_t HeadIdx,
							uint8_t *dataBuff,
							uint32_t TDLen,
							uint8_t IntOnComplete);

static HCD_STATUS QueueSITDs(uint8_t HostID, uint8_t HeadIdx, uint8_t *dataBuff, uint32_t xferLen);

/********************************* Transfer Routines *********************************/
static HCD_STATUS WaitForTransferComplete(uint8_t HostID, uint8_t EpIdx);

static HCD_STATUS PipehandleParse(uint32_t Pipehandle, uint8_t *pHostID, HCD_TRANSFER_TYPE *XferType, uint8_t *pIdx);

static void PipehandleCreate(uint32_t *pPipeHandle, uint8_t HostID, HCD_TRANSFER_TYPE XferType, uint8_t idx);

/********************************* Interrupt Service Routines *********************************/
static void AsyncScheduleIsr(uint8_t HostID);

static void PeriodScheduleIsr(uint8_t HostID);

static HCD_STATUS PortStatusChangeIsr(uint8_t HostID, uint32_t deviceConnect);

static void AsyncAdvanceIsr(uint8_t HostID);

static void UsbErrorIsr(uint8_t HostID);

#endif

/** @} */
