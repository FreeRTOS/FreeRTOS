/*
 * @brief Open Host Controller Interface
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
 *  @defgroup Host_OHCI Open Host Controller Interface Driver
 *  @{
 */
 
#ifndef __LPC_OHCI_H__
#define __LPC_OHCI_H__

#ifndef __LPC_OHCI_C__	// TODO INCLUDE FROM OHCI.C
	#error OHCI.h is private header and can only be included by OHCI.c, try to include HCD.h instead
#endif

#ifdef __TEST__	// suppress static/inline for Testing purpose
	#define static
	#define inline
#endif

#define MAX_ED                              HCD_MAX_ENDPOINT
#define MAX_GTD                             (MAX_ED + 3)
#define MAX_STATIC_ED                       3	/* Serve as list head, fixed, not configurable */

#if ISO_LIST_ENABLE
	#define MAX_ITD                             4
#else
	#define MAX_ITD                             0
#endif

#define CONTROL_BULK_SERVICE_RATIO          3			/* Control Bulk transfer ratio 0 = 1:1 - 1 = 2:1 - 2 = 3:1 - 3 = 4:1 */
#define INTERRUPT_ROUTING                   0			/* Host interrupt routing 0 = IRQ - 1 = SMI */
#define REMOTE_WAKEUP_CONNECTED             NO		/* Remote wakeup connected */
#define REMOTE_WAKEUP_ENABLE                NO		/* Remote wakeup enable    */

#define SCHEDULING_OVRERRUN_INTERRUPT       NO

#define SOF_INTERRUPT                       NO
#define RESUME_DETECT_INTERRUPT             NO
#define UNRECOVERABLE_ERROR_INTERRUPT       NO
#define FRAMENUMBER_OVERFLOW_INTERRUPT      NO

#define OWNERSHIP_CHANGE_INTERRUPT          NO

#define FRAME_INTERVAL                      0x2EDF		/* Reset default value */
#define HC_FMINTERVAL_DEFAULT               ((((6 * (FRAME_INTERVAL - 210)) / 7) << 16) | FRAME_INTERVAL)

#define PERIODIC_START                      0x00002A27UL		/* 10% off from FRAME_INTERVAL */

#define PORT_POWER_SWITCHING                NO
#define PER_PORT_POWER_SWITCHING            NO
#define PER_PORT_OVER_CURRENT_REPORT        NO
#define OVER_CURRENT_PROTECTION             NO

#define INTERRUPT_1ms_LIST_HEAD     0
#define INTERRUPT_2ms_LIST_HEAD     1
#define INTERRUPT_4ms_LIST_HEAD     3
#define INTERRUPT_8ms_LIST_HEAD     7
#define INTERRUPT_16ms_LIST_HEAD    15
#define INTERRUPT_32ms_LIST_HEAD    31
#define ISO_LIST_HEAD               (MAX_STATIC_ED - 3)
#define CONTROL_LIST_HEAD           (MAX_STATIC_ED - 2)
#define BULK_LIST_HEAD              (MAX_STATIC_ED - 1)
#define TD_MAX_XFER_LENGTH          0x2000

#define TD_NoInterruptOnComplete    (7)

#define HC_REVISION                                     0x000000FFUL

#define HC_FM_REMAIN                                    0x00003FFFUL		/* Frame remaining				*/

#define HC_FM_NUMBER                                    0x0000FFFFUL		/* Frame Number					*/

#define HC_CONTROL_ControlBulkServiceRatio              0x00000003UL		/* Control/Bulk ratio			*/
#define HC_CONTROL_PeriodListEnable                     0x00000004UL		/* Periodic List Enable			*/
#define HC_CONTROL_IsochronousEnable                    0x00000008UL		/* Isochronous Enable			*/
#define HC_CONTROL_ControlListEnable                    0x00000010UL		/* Control List Enable			*/
#define HC_CONTROL_BulkListEnable                       0x00000020UL		/* Bulk List Enable				*/
#define HC_CONTROL_HostControllerFunctionalState        0x000000C0UL		/* Host Controller Functional State */
#define HC_CONTROL_InterruptRouting                     0x00000100UL		/* Interrupt Routing			*/
#define HC_CONTROL_RemoteWakeupConnected                0x00000200UL		/* Remote Wakeup Connected		*/
#define HC_CONTROL_RemoteWakeupEnable                   0x00000400UL		/* Remote Wakeup Enable			*/

#define HC_HOST_RESET                                   0x00000000UL		/* Reset state					*/
#define HC_HOST_RESUME                                  0X00000001UL		/* Resume state					*/
#define HC_HOST_OPERATIONAL                             0x00000002UL		/* Operational state			*/
#define HC_HOST_SUSPEND                                 0x00000003UL		/* Suspend state				*/

#define HC_COMMAND_STATUS_HostControllerReset           0x00000001UL		/* Host Controller Reset		*/
#define HC_COMMAND_STATUS_ControlListFilled             0x00000002UL		/* Control List Filled			*/
#define HC_COMMAND_STATUS_BulkListFilled                0x00000004UL		/* Bulk List Filled				*/

#define HC_INTERRUPT_SchedulingOverrun                  0x00000001UL		/* Scheduling Overrun			*/
#define HC_INTERRUPT_WritebackDoneHead                  0x00000002UL		/* Writeback DoneHead			*/
#define HC_INTERRUPT_StartofFrame                       0x00000004UL		/* Start of Frame				*/
#define HC_INTERRUPT_ResumeDetected                     0x00000008UL		/* Resume Detect				*/
#define HC_INTERRUPT_UnrecoverableError                 0x00000010UL		/* Unrecoverable error			*/
#define HC_INTERRUPT_FrameNumberOverflow                0x00000020UL		/* Frame Number Overflow		*/
#define HC_INTERRUPT_RootHubStatusChange                0x00000040UL		/* Root Hub Status Change		*/
#define HC_INTERRUPT_OwnershipChange                    0x40000000UL		/* Ownership Change				*/
#define HC_INTERRUPT_MasterInterruptEnable              0x80000000UL		/* Master Interrupt Enable		*/
#define HC_INTERRUPT_ALL                                0xC000007FUL		/* All interrupts				*/

#define HC_RH_DESCRIPTORA_NumberDownstreamPorts         0x000000FFUL		/* Number of downstream ports  */
#define HC_RH_DESCRIPTORA_PowerSwitchingMode            0x00000100UL		/* Power Switching Mode        */
#define HC_RH_DESCRIPTORA_NoPowerSwitching              0x00000200UL		/* No Power Switching          */
#define HC_RH_DESCRIPTORA_OverCurrentProtectionMode     0x00000800UL		/* OverCurrent Protection Mode */
#define HC_RH_DESCRIPTORA_NoOverCurrentProtection       0x00001000UL		/* No OverCurrent Protection   */
#define HC_RH_DESCRIPTORA_PowerOnToPowerGoodTime        0xFF000000UL		/* Power On To Power Good Time */

#define HC_RH_DESCRIPTORB_PortPowerControlMask          0xFFFF0000UL		/* Port Power Control Mask     */
#define HC_RH_DESCRIPTORB_DeviceRemovable               0x0000FFFFUL		/* Device Removable            */

#define HC_RH_STATUS_LocalPowerStatus                   0x00000001UL		/* R: Local Power Status		- W: Clear Global Power		*/
#define HC_RH_STATUS_LocalPowerStatusChange             0x00010000UL		/* R: Local Power Status Change - W: Set Global Power		*/
#define HC_RH_STATUS_DeviceRemoteWakeupEnable           0x00008000UL		/* W: Set Remote Wakeup Enable */

#define HC_RH_PORT_STATUS_CurrentConnectStatus          0x00000001UL		/* R: Current Connect Status	- W: Clear Port Enable      */
#define HC_RH_PORT_STATUS_PowerEnableStatus             0x00000002UL		/* R: Port Enable Status		- W: Set Port Enable        */
#define HC_RH_PORT_STATUS_PortSuspendStatus             0x00000004UL		/* R: Port Suspend Status		- W: Set Port Suspend       */
#define HC_RH_PORT_STATUS_PortOverCurrentIndicator      0x00000008UL		/* R: Port OverCurrent Indicator- W: Clear Suspend Status	*/
#define HC_RH_PORT_STATUS_PortResetStatus               0x00000010UL		/* R: Port Reset  Status		- W: Set Port Reset         */
#define HC_RH_PORT_STATUS_PortPowerStatus               0x00000100UL		/* R: Port Power Status			- W: Set Port Power         */
#define HC_RH_PORT_STATUS_LowSpeedDeviceAttached        0x00000200UL		/* R: Low Speed Device Attached	- W: Clear Port Power       */

#define HC_RH_PORT_STATUS_ConnectStatusChange           0x00010000UL		/* Connect Status Change        */
#define HC_RH_PORT_STATUS_PortEnableStatusChange        0x00020000UL		/* Port Enable Status Change    */
#define HC_RH_PORT_STATUS_PortSuspendStatusChange       0x00040000UL		/* Port Suspend Status Change   */
#define HC_RH_PORT_STATUS_OverCurrentIndicatorChange    0x00080000UL		/* OverCurrent Indicator Change */
#define HC_RH_PORT_STATUS_PortResetStatusChange         0x00100000UL		/* Port Reset Status Change     */
#define HC_RH_PORT_STATUS_StatusChangeMask							(HC_RH_PORT_STATUS_ConnectStatusChange | \
																													HC_RH_PORT_STATUS_PortEnableStatusChange | \
																													HC_RH_PORT_STATUS_PortSuspendStatusChange | \
																													HC_RH_PORT_STATUS_OverCurrentIndicatorChange | \
																													HC_RH_PORT_STATUS_PortResetStatusChange)

typedef struct st_HC_HCCA {
	__O  uint32_t HccaIntTable[32];
	__I  uint16_t HccaFrameNumber;
	__I  uint16_t HccaPad1;
	__I  uint32_t HccaDoneHead;
	__I  uint8_t  HccaReserved[116];
} ATTR_ALIGNED (256) HC_HCCA;

typedef struct st_HC_ED {	// 16 byte align
	/*---------- Word 1 ----------*/
	uint32_t FunctionAddr   : 7;
	uint32_t EndpointNumber : 4;
	uint32_t Direction      : 2;
	uint32_t Speed          : 1;
	uint32_t Skip           : 1;
	uint32_t Format         : 1;
	uint32_t MaxPackageSize : 11;
	uint32_t                : 0;/* Force next member on next storage unit */
	/*---------- End Word 1 ----------*/

	/*---------- Word 2 ----------*/
	uint32_t TailP;	// only 28 bits - 16B align

	/*---------- Word 3 ----------*/
	union {
		 uint32_t HeadTD;
		 struct {
			uint32_t Halted         : 1;
			uint32_t ToggleCarry    : 1;
			uint32_t                : 30;
		};

	} HeadP;/* TODO remove this name */

	/*---------- Word 4 ----------*/
	uint32_t NextED;// only 28 bits - 16B align
} ATTR_ALIGNED (16) HC_ED, *PHC_ED;

typedef struct st_HCD_EndpointDescriptor {	// 32 byte align
	HC_ED hcED;

	/*---------- Word 1 ----------*/
	uint32_t inUse          : 1;
	uint32_t ListIndex      : 7;	// 0: Interrupt/ISO, 1: Control, 2: bulk
	uint32_t Interval       : 8;	/* Used by ISO, High speed Bulk/Control maximum NAK */
	uint32_t                : 0;	/* Force next member on next storage unit */
	/*---------- End Word 1 ----------*/

	__IO uint32_t status;			// TODO status is updated by ISR --> is non-caching
	uint16_t *pActualTransferCount;	/* total transferred bytes of a usb request */

	uint32_t reserved;
} HCD_EndpointDescriptor, *PHCD_EndpointDescriptor;

typedef struct st_HC_GTD {	// 16 byte align
	/*---------- Word 1 ----------*/
	uint32_t               : 18;
	uint32_t BufferRounding : 1;
	uint32_t DirectionPID  : 2;
	uint32_t DelayInterrupt : 3;
	__IO uint32_t DataToggle    : 2;
	__IO uint32_t ErrorCount    : 2;
	__IO uint32_t ConditionCode : 4;
	uint32_t               : 0;			/* Force next member on next storage unit */
	/*---------- End Word 1 ----------*/

	/*---------- Word 2 ----------*/
	__IO uint8_t *CurrentBufferPointer;

	/*---------- Word 3 ----------*/
	__IO uint32_t NextTD;	// only 28 bits - 16B align

	/*---------- Word 4 ----------*/
	uint8_t *BufferEnd;
} ATTR_ALIGNED (16) HC_GTD, *PHC_GTD;	/* TODO merge into HCD_GeneralTransferDescriptor */

typedef struct st_HCD_GeneralTransferDescriptor {	// 32 byte align
	HC_GTD hcGTD;

	/*---------- Word 1 ----------*/
	uint32_t inUse      : 1;
	uint32_t            : 0;	/* Force next member on next storage unit */
	/*---------- End Word 1 ----------*/

	uint16_t EdIdx;
	uint16_t TransferCount;

	uint32_t reserved2;
	uint32_t reserved3;
} HCD_GeneralTransferDescriptor, *PHCD_GeneralTransferDescriptor;

typedef struct st_HCD_IsoTransferDescriptor {	// 64 byte align
	/*---------- Word 1 ----------*/
	uint32_t StartingFrame : 16;
	uint32_t               : 5;
	uint32_t DelayInterrupt : 3;
	uint32_t FrameCount    : 3;
	uint32_t               : 1;
	__IO uint32_t ConditionCode : 4;
	uint32_t               : 0;			/* Force next member on next storage unit */
	/*---------- End Word 1 ----------*/

	/*---------- Word 2 ----------*/
	uint32_t BufferPage0;	// only 20 bits - 4KB align

	/*---------- Word 3 ----------*/
	__IO uint32_t NextTD;	// only 27 bits - 32B align

	/*---------- Word 4 ----------*/
	uint32_t BufferEnd;

	/*---------- Word 5-8 ----------*/
	__IO uint16_t OffsetPSW[8];

	/*---------- HCD AREA ----------*/
	/*---------- Word 9 ----------*/
	uint32_t inUse      : 1;
	uint32_t            : 0;	/* Force next member on next storage unit */
	/*---------- End Word 9 ----------*/

	/*---------- Word 10 ----------*/
	uint16_t EdIdx;
	uint16_t reserved3;
	/*---------- End Word 10 ----------*/

	uint32_t reserved2[6];
} ATTR_ALIGNED (32)  HCD_IsoTransferDescriptor, *PHCD_IsoTransferDescriptor;

typedef struct st_OHCI_HOST {
	HC_HCCA hcca;
        uint32_t host_reserved1;
#if ISO_LIST_ENABLE
	HCD_IsoTransferDescriptor       iTDs[MAX_ITD];
#endif
	HCD_GeneralTransferDescriptor   gTDs[MAX_GTD];
	HCD_EndpointDescriptor          EDs[MAX_ED];
	HC_ED                           staticEDs[MAX_STATIC_ED];
} OHCI_HOST_DATA_T;

// #define OHCI_DATA(HostID)	((OHCI_HOST_DATA_T*) HCD_RAM_ADDR_BASE)
extern OHCI_HOST_DATA_T ohci_data[MAX_USB_CORE];

static INLINE HCD_STATUS OHciHostInit(uint8_t HostID);

static INLINE HCD_STATUS OHciHostReset(uint8_t HostID);

static INLINE HCD_STATUS OHciHostOperational(uint8_t HostID);

#if 0	// just to clear warning
static INLINE HCD_STATUS OHciHostSuspend(uint8_t HostID);

static INLINE HCD_STATUS OHciRhPortPowerOn(uint8_t HostID, uint8_t uPortNumber);

static INLINE HCD_STATUS OHciRhPortPowerOff(uint8_t HostID, uint8_t uPortNumber);

static INLINE HCD_STATUS OHciRhPortSuspend(uint8_t HostID, uint8_t uPortNumber);

static INLINE HCD_STATUS OHciRhPortResume(uint8_t HostID, uint8_t uPortNumber);

static INLINE Bool IsInterruptEndpoint (uint8_t EdIdx);

#endif

static INLINE uint32_t Align16 (uint32_t Value);

static INLINE PHCD_EndpointDescriptor HcdED(uint8_t idx);

static INLINE PHCD_GeneralTransferDescriptor HcdGTD(uint8_t idx);

static INLINE PHCD_IsoTransferDescriptor HcdITD(uint8_t idx);

static INLINE Bool IsIsoEndpoint(uint8_t EdIdx);

static void PipehandleCreate(uint32_t *pPipeHandle, uint8_t HostID, uint8_t idx);

static HCD_STATUS PipehandleParse(uint32_t Pipehandle, uint8_t *HostID, uint8_t *EdIdx);

static INLINE void BuildPeriodicStaticEdTree(uint8_t HostID);

static INLINE HCD_STATUS AllocEd(uint8_t DeviceAddr,
								   HCD_USB_SPEED DeviceSpeed,
								   uint8_t EndpointNumber,
								   HCD_TRANSFER_TYPE TransferType,
								   HCD_TRANSFER_DIR TransferDir,
								   uint16_t MaxPacketSize,
								   uint8_t Interval,
								   uint32_t *pEdIdx);

static INLINE HCD_STATUS AllocGtdForEd(uint8_t EdIdx);

static INLINE HCD_STATUS AllocItdForEd(uint8_t EdIdx);

static INLINE HCD_STATUS FreeED(uint8_t EdIdx);

static INLINE HCD_STATUS FreeGtd(PHCD_GeneralTransferDescriptor pGtd);

static INLINE HCD_STATUS FreeItd(PHCD_IsoTransferDescriptor pItd);

static INLINE HCD_STATUS InsertEndpoint(uint8_t HostID, uint32_t EdIdx, uint8_t ListIndex);

static INLINE HCD_STATUS RemoveEndpoint(uint8_t HostID, uint32_t EdIdx);

/*static INLINE uint8_t FindInterruptTransferListIndex(uint8_t HostID, uint8_t Interval);*/
static HCD_STATUS QueueOneGTD (uint32_t EdIdx,
							   uint8_t *const CurrentBufferPointer,
							   uint32_t xferLen,
							   uint8_t DirectionPID,
							   uint8_t DataToggle,
							   uint8_t IOC);

static HCD_STATUS QueueGTDs (uint32_t EdIdx, uint8_t *dataBuff, uint32_t xferLen, uint8_t Direction);

static HCD_STATUS WaitForTransferComplete(uint8_t EdIdx);

#endif /*defined(__LPC_OHCI__)*/

/** @} */
