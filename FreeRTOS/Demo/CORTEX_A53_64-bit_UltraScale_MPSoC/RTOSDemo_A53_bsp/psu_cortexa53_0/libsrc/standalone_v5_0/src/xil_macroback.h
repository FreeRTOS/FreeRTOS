/******************************************************************************
*
* Copyright (C) 2010 - 2014 Xilinx, Inc. All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
* XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/

/*********************************************************************/
/**
 * @file xil_macroback.h
 *
 * This header file is meant to bring back the removed _m macros.
 * This header file must be included last.
 * The following macros are not defined here due to the driver change:
 *   XGpio_mSetDataDirection
 *   XGpio_mGetDataReg
 *   XGpio_mSetDataReg
 *   XIIC_RESET
 *   XIIC_CLEAR_STATS
 *   XSpi_mReset
 *   XSysAce_mSetCfgAddr
 *   XSysAce_mIsCfgDone
 *   XTft_mSetPixel
 *   XTft_mGetPixel
 *   XWdtTb_mEnableWdt
 *   XWdtTb_mDisbleWdt
 *   XWdtTb_mRestartWdt
 *   XWdtTb_mGetTimebaseReg
 *   XWdtTb_mHasReset
 *
 * Please refer the corresonding driver document for replacement.
 *
 *********************************************************************/

#ifndef XIL_MACROBACK_H
#define XIL_MACROBACK_H

/*********************************************************************/
/**
 * Macros for Driver XCan
 *
 *********************************************************************/
#ifndef XCan_mReadReg
#define XCan_mReadReg XCan_ReadReg
#endif

#ifndef XCan_mWriteReg
#define XCan_mWriteReg XCan_WriteReg
#endif

#ifndef XCan_mIsTxDone
#define XCan_mIsTxDone XCan_IsTxDone
#endif

#ifndef XCan_mIsTxFifoFull
#define XCan_mIsTxFifoFull XCan_IsTxFifoFull
#endif

#ifndef XCan_mIsHighPriorityBufFull
#define XCan_mIsHighPriorityBufFull XCan_IsHighPriorityBufFull
#endif

#ifndef XCan_mIsRxEmpty
#define XCan_mIsRxEmpty XCan_IsRxEmpty
#endif

#ifndef XCan_mIsAcceptFilterBusy
#define XCan_mIsAcceptFilterBusy XCan_IsAcceptFilterBusy
#endif

#ifndef XCan_mCreateIdValue
#define XCan_mCreateIdValue XCan_CreateIdValue
#endif

#ifndef XCan_mCreateDlcValue
#define XCan_mCreateDlcValue XCan_CreateDlcValue
#endif

/*********************************************************************/
/**
 * Macros for Driver XDmaCentral
 *
 *********************************************************************/
#ifndef XDmaCentral_mWriteReg
#define XDmaCentral_mWriteReg XDmaCentral_WriteReg
#endif

#ifndef XDmaCentral_mReadReg
#define XDmaCentral_mReadReg XDmaCentral_ReadReg
#endif

/*********************************************************************/
/**
 * Macros for Driver XDsAdc
 *
 *********************************************************************/
#ifndef XDsAdc_mWriteReg
#define XDsAdc_mWriteReg XDsAdc_WriteReg
#endif

#ifndef XDsAdc_mReadReg
#define XDsAdc_mReadReg XDsAdc_ReadReg
#endif

#ifndef XDsAdc_mIsEmpty
#define XDsAdc_mIsEmpty XDsAdc_IsEmpty
#endif

#ifndef XDsAdc_mSetFstmReg
#define XDsAdc_mSetFstmReg XDsAdc_SetFstmReg
#endif

#ifndef XDsAdc_mGetFstmReg
#define XDsAdc_mGetFstmReg XDsAdc_GetFstmReg
#endif

#ifndef XDsAdc_mEnableConversion
#define XDsAdc_mEnableConversion XDsAdc_EnableConversion
#endif

#ifndef XDsAdc_mDisableConversion
#define XDsAdc_mDisableConversion XDsAdc_DisableConversion
#endif

#ifndef XDsAdc_mGetFifoOccyReg
#define XDsAdc_mGetFifoOccyReg XDsAdc_GetFifoOccyReg
#endif

/*********************************************************************/
/**
 * Macros for Driver XDsDac
 *
 *********************************************************************/
#ifndef XDsDac_mWriteReg
#define XDsDac_mWriteReg XDsDac_WriteReg
#endif

#ifndef XDsDac_mReadReg
#define XDsDac_mReadReg XDsDac_ReadReg
#endif

#ifndef XDsDac_mIsEmpty
#define XDsDac_mIsEmpty XDsDac_IsEmpty
#endif

#ifndef XDsDac_mFifoIsFull
#define XDsDac_mFifoIsFull XDsDac_FifoIsFull
#endif

#ifndef XDsDac_mGetVacancy
#define XDsDac_mGetVacancy XDsDac_GetVacancy
#endif

/*********************************************************************/
/**
 * Macros for Driver XEmacLite
 *
 *********************************************************************/
#ifndef XEmacLite_mReadReg
#define XEmacLite_mReadReg XEmacLite_ReadReg
#endif

#ifndef XEmacLite_mWriteReg
#define XEmacLite_mWriteReg XEmacLite_WriteReg
#endif

#ifndef XEmacLite_mGetTxStatus
#define XEmacLite_mGetTxStatus XEmacLite_GetTxStatus
#endif

#ifndef XEmacLite_mSetTxStatus
#define XEmacLite_mSetTxStatus XEmacLite_SetTxStatus
#endif

#ifndef XEmacLite_mGetRxStatus
#define XEmacLite_mGetRxStatus XEmacLite_GetRxStatus
#endif

#ifndef XEmacLite_mSetRxStatus
#define XEmacLite_mSetRxStatus XEmacLite_SetRxStatus
#endif

#ifndef XEmacLite_mIsTxDone
#define XEmacLite_mIsTxDone XEmacLite_IsTxDone
#endif

#ifndef XEmacLite_mIsRxEmpty
#define XEmacLite_mIsRxEmpty XEmacLite_IsRxEmpty
#endif

#ifndef XEmacLite_mNextTransmitAddr
#define XEmacLite_mNextTransmitAddr XEmacLite_NextTransmitAddr
#endif

#ifndef XEmacLite_mNextReceiveAddr
#define XEmacLite_mNextReceiveAddr XEmacLite_NextReceiveAddr
#endif

#ifndef XEmacLite_mIsMdioConfigured
#define XEmacLite_mIsMdioConfigured XEmacLite_IsMdioConfigured
#endif

#ifndef XEmacLite_mIsLoopbackConfigured
#define XEmacLite_mIsLoopbackConfigured XEmacLite_IsLoopbackConfigured
#endif

#ifndef XEmacLite_mGetReceiveDataLength
#define XEmacLite_mGetReceiveDataLength XEmacLite_GetReceiveDataLength
#endif

#ifndef XEmacLite_mGetTxActive
#define XEmacLite_mGetTxActive XEmacLite_GetTxActive
#endif

#ifndef XEmacLite_mSetTxActive
#define XEmacLite_mSetTxActive XEmacLite_SetTxActive
#endif

/*********************************************************************/
/**
 * Macros for Driver XGpio
 *
 *********************************************************************/
#ifndef XGpio_mWriteReg
#define XGpio_mWriteReg XGpio_WriteReg
#endif

#ifndef XGpio_mReadReg
#define XGpio_mReadReg XGpio_ReadReg
#endif

/*********************************************************************/
/**
 * Macros for Driver XHwIcap
 *
 *********************************************************************/
#ifndef XHwIcap_mFifoWrite
#define XHwIcap_mFifoWrite XHwIcap_FifoWrite
#endif

#ifndef XHwIcap_mFifoRead
#define XHwIcap_mFifoRead XHwIcap_FifoRead
#endif

#ifndef XHwIcap_mSetSizeReg
#define XHwIcap_mSetSizeReg XHwIcap_SetSizeReg
#endif

#ifndef XHwIcap_mGetControlReg
#define XHwIcap_mGetControlReg XHwIcap_GetControlReg
#endif

#ifndef XHwIcap_mStartConfig
#define XHwIcap_mStartConfig XHwIcap_StartConfig
#endif

#ifndef XHwIcap_mStartReadBack
#define XHwIcap_mStartReadBack XHwIcap_StartReadBack
#endif

#ifndef XHwIcap_mGetStatusReg
#define XHwIcap_mGetStatusReg XHwIcap_GetStatusReg
#endif

#ifndef XHwIcap_mIsTransferDone
#define XHwIcap_mIsTransferDone XHwIcap_IsTransferDone
#endif

#ifndef XHwIcap_mIsDeviceBusy
#define XHwIcap_mIsDeviceBusy XHwIcap_IsDeviceBusy
#endif

#ifndef XHwIcap_mIntrGlobalEnable
#define XHwIcap_mIntrGlobalEnable XHwIcap_IntrGlobalEnable
#endif

#ifndef XHwIcap_mIntrGlobalDisable
#define XHwIcap_mIntrGlobalDisable XHwIcap_IntrGlobalDisable
#endif

#ifndef XHwIcap_mIntrGetStatus
#define XHwIcap_mIntrGetStatus XHwIcap_IntrGetStatus
#endif

#ifndef XHwIcap_mIntrDisable
#define XHwIcap_mIntrDisable XHwIcap_IntrDisable
#endif

#ifndef XHwIcap_mIntrEnable
#define XHwIcap_mIntrEnable XHwIcap_IntrEnable
#endif

#ifndef XHwIcap_mIntrGetEnabled
#define XHwIcap_mIntrGetEnabled XHwIcap_IntrGetEnabled
#endif

#ifndef XHwIcap_mIntrClear
#define XHwIcap_mIntrClear XHwIcap_IntrClear
#endif

#ifndef XHwIcap_mGetWrFifoVacancy
#define XHwIcap_mGetWrFifoVacancy XHwIcap_GetWrFifoVacancy
#endif

#ifndef XHwIcap_mGetRdFifoOccupancy
#define XHwIcap_mGetRdFifoOccupancy XHwIcap_GetRdFifoOccupancy
#endif

#ifndef XHwIcap_mSliceX2Col
#define XHwIcap_mSliceX2Col XHwIcap_SliceX2Col
#endif

#ifndef XHwIcap_mSliceY2Row
#define XHwIcap_mSliceY2Row XHwIcap_SliceY2Row
#endif

#ifndef XHwIcap_mSliceXY2Slice
#define XHwIcap_mSliceXY2Slice XHwIcap_SliceXY2Slice
#endif

#ifndef XHwIcap_mReadReg
#define XHwIcap_mReadReg XHwIcap_ReadReg
#endif

#ifndef XHwIcap_mWriteReg
#define XHwIcap_mWriteReg XHwIcap_WriteReg
#endif

/*********************************************************************/
/**
 * Macros for Driver XIic
 *
 *********************************************************************/
#ifndef XIic_mReadReg
#define XIic_mReadReg XIic_ReadReg
#endif

#ifndef XIic_mWriteReg
#define XIic_mWriteReg XIic_WriteReg
#endif

#ifndef XIic_mEnterCriticalRegion
#define XIic_mEnterCriticalRegion XIic_IntrGlobalDisable
#endif

#ifndef XIic_mExitCriticalRegion
#define XIic_mExitCriticalRegion XIic_IntrGlobalEnable
#endif

#ifndef XIIC_GINTR_DISABLE
#define XIIC_GINTR_DISABLE XIic_IntrGlobalDisable
#endif

#ifndef XIIC_GINTR_ENABLE
#define XIIC_GINTR_ENABLE XIic_IntrGlobalEnable
#endif

#ifndef XIIC_IS_GINTR_ENABLED
#define XIIC_IS_GINTR_ENABLED XIic_IsIntrGlobalEnabled
#endif

#ifndef XIIC_WRITE_IISR
#define XIIC_WRITE_IISR XIic_WriteIisr
#endif

#ifndef XIIC_READ_IISR
#define XIIC_READ_IISR XIic_ReadIisr
#endif

#ifndef XIIC_WRITE_IIER
#define XIIC_WRITE_IIER XIic_WriteIier
#endif

#ifndef XIic_mClearIisr
#define XIic_mClearIisr XIic_ClearIisr
#endif

#ifndef XIic_mSend7BitAddress
#define XIic_mSend7BitAddress XIic_Send7BitAddress
#endif

#ifndef XIic_mDynSend7BitAddress
#define XIic_mDynSend7BitAddress XIic_DynSend7BitAddress
#endif

#ifndef XIic_mDynSendStartStopAddress
#define XIic_mDynSendStartStopAddress XIic_DynSendStartStopAddress
#endif

#ifndef XIic_mDynSendStop
#define XIic_mDynSendStop XIic_DynSendStop
#endif

#ifndef XIic_mSend10BitAddrByte1
#define XIic_mSend10BitAddrByte1 XIic_Send10BitAddrByte1
#endif

#ifndef XIic_mSend10BitAddrByte2
#define XIic_mSend10BitAddrByte2 XIic_Send10BitAddrByte2
#endif

#ifndef XIic_mSend7BitAddr
#define XIic_mSend7BitAddr XIic_Send7BitAddr
#endif

#ifndef XIic_mDisableIntr
#define XIic_mDisableIntr XIic_DisableIntr
#endif

#ifndef XIic_mEnableIntr
#define XIic_mEnableIntr XIic_EnableIntr
#endif

#ifndef XIic_mClearIntr
#define XIic_mClearIntr XIic_ClearIntr
#endif

#ifndef XIic_mClearEnableIntr
#define XIic_mClearEnableIntr XIic_ClearEnableIntr
#endif

#ifndef XIic_mFlushRxFifo
#define XIic_mFlushRxFifo XIic_FlushRxFifo
#endif

#ifndef XIic_mFlushTxFifo
#define XIic_mFlushTxFifo XIic_FlushTxFifo
#endif

#ifndef XIic_mReadRecvByte
#define XIic_mReadRecvByte XIic_ReadRecvByte
#endif

#ifndef XIic_mWriteSendByte
#define XIic_mWriteSendByte XIic_WriteSendByte
#endif

#ifndef XIic_mSetControlRegister
#define XIic_mSetControlRegister XIic_SetControlRegister
#endif

/*********************************************************************/
/**
 * Macros for Driver XIntc
 *
 *********************************************************************/
#ifndef XIntc_mMasterEnable
#define XIntc_mMasterEnable XIntc_MasterEnable
#endif

#ifndef XIntc_mMasterDisable
#define XIntc_mMasterDisable XIntc_MasterDisable
#endif

#ifndef XIntc_mEnableIntr
#define XIntc_mEnableIntr XIntc_EnableIntr
#endif

#ifndef XIntc_mDisableIntr
#define XIntc_mDisableIntr XIntc_DisableIntr
#endif

#ifndef XIntc_mAckIntr
#define XIntc_mAckIntr XIntc_AckIntr
#endif

#ifndef XIntc_mGetIntrStatus
#define XIntc_mGetIntrStatus XIntc_GetIntrStatus
#endif

/*********************************************************************/
/**
 * Macros for Driver XLlDma
 *
 *********************************************************************/
#ifndef XLlDma_mBdRead
#define XLlDma_mBdRead XLlDma_BdRead
#endif

#ifndef XLlDma_mBdWrite
#define XLlDma_mBdWrite XLlDma_BdWrite
#endif

#ifndef XLlDma_mWriteReg
#define XLlDma_mWriteReg XLlDma_WriteReg
#endif

#ifndef XLlDma_mReadReg
#define XLlDma_mReadReg XLlDma_ReadReg
#endif

#ifndef XLlDma_mBdClear
#define XLlDma_mBdClear XLlDma_BdClear
#endif

#ifndef XLlDma_mBdSetStsCtrl
#define XLlDma_mBdSetStsCtrl XLlDma_BdSetStsCtrl
#endif

#ifndef XLlDma_mBdGetStsCtrl
#define XLlDma_mBdGetStsCtrl XLlDma_BdGetStsCtrl
#endif

#ifndef XLlDma_mBdSetLength
#define XLlDma_mBdSetLength XLlDma_BdSetLength
#endif

#ifndef XLlDma_mBdGetLength
#define XLlDma_mBdGetLength XLlDma_BdGetLength
#endif

#ifndef XLlDma_mBdSetId
#define XLlDma_mBdSetId XLlDma_BdSetId
#endif

#ifndef XLlDma_mBdGetId
#define XLlDma_mBdGetId XLlDma_BdGetId
#endif

#ifndef XLlDma_mBdSetBufAddr
#define XLlDma_mBdSetBufAddr XLlDma_BdSetBufAddr
#endif

#ifndef XLlDma_mBdGetBufAddr
#define XLlDma_mBdGetBufAddr XLlDma_BdGetBufAddr
#endif

#ifndef XLlDma_mBdGetLength
#define XLlDma_mBdGetLength XLlDma_BdGetLength
#endif

#ifndef XLlDma_mGetTxRing
#define XLlDma_mGetTxRing XLlDma_GetTxRing
#endif

#ifndef XLlDma_mGetRxRing
#define XLlDma_mGetRxRing XLlDma_GetRxRing
#endif

#ifndef XLlDma_mGetCr
#define XLlDma_mGetCr XLlDma_GetCr
#endif

#ifndef XLlDma_mSetCr
#define XLlDma_mSetCr XLlDma_SetCr
#endif

#ifndef XLlDma_mBdRingCntCalc
#define XLlDma_mBdRingCntCalc XLlDma_BdRingCntCalc
#endif

#ifndef XLlDma_mBdRingMemCalc
#define XLlDma_mBdRingMemCalc XLlDma_BdRingMemCalc
#endif

#ifndef XLlDma_mBdRingGetCnt
#define XLlDma_mBdRingGetCnt XLlDma_BdRingGetCnt
#endif

#ifndef XLlDma_mBdRingGetFreeCnt
#define XLlDma_mBdRingGetFreeCnt XLlDma_BdRingGetFreeCnt
#endif

#ifndef XLlDma_mBdRingSnapShotCurrBd
#define XLlDma_mBdRingSnapShotCurrBd XLlDma_BdRingSnapShotCurrBd
#endif

#ifndef XLlDma_mBdRingNext
#define XLlDma_mBdRingNext XLlDma_BdRingNext
#endif

#ifndef XLlDma_mBdRingPrev
#define XLlDma_mBdRingPrev XLlDma_BdRingPrev
#endif

#ifndef XLlDma_mBdRingGetSr
#define XLlDma_mBdRingGetSr XLlDma_BdRingGetSr
#endif

#ifndef XLlDma_mBdRingSetSr
#define XLlDma_mBdRingSetSr XLlDma_BdRingSetSr
#endif

#ifndef XLlDma_mBdRingGetCr
#define XLlDma_mBdRingGetCr XLlDma_BdRingGetCr
#endif

#ifndef XLlDma_mBdRingSetCr
#define XLlDma_mBdRingSetCr XLlDma_BdRingSetCr
#endif

#ifndef XLlDma_mBdRingBusy
#define XLlDma_mBdRingBusy XLlDma_BdRingBusy
#endif

#ifndef XLlDma_mBdRingIntEnable
#define XLlDma_mBdRingIntEnable XLlDma_BdRingIntEnable
#endif

#ifndef XLlDma_mBdRingIntDisable
#define XLlDma_mBdRingIntDisable XLlDma_BdRingIntDisable
#endif

#ifndef XLlDma_mBdRingIntGetEnabled
#define XLlDma_mBdRingIntGetEnabled XLlDma_BdRingIntGetEnabled
#endif

#ifndef XLlDma_mBdRingGetIrq
#define XLlDma_mBdRingGetIrq XLlDma_BdRingGetIrq
#endif

#ifndef XLlDma_mBdRingAckIrq
#define XLlDma_mBdRingAckIrq XLlDma_BdRingAckIrq
#endif

/*********************************************************************/
/**
 * Macros for Driver XMbox
 *
 *********************************************************************/
#ifndef XMbox_mWriteReg
#define XMbox_mWriteReg XMbox_WriteReg
#endif

#ifndef XMbox_mReadReg
#define XMbox_mReadReg XMbox_ReadReg
#endif

#ifndef XMbox_mWriteMBox
#define XMbox_mWriteMBox XMbox_WriteMBox
#endif

#ifndef XMbox_mReadMBox
#define XMbox_mReadMBox XMbox_ReadMBox
#endif

#ifndef XMbox_mFSLReadMBox
#define XMbox_mFSLReadMBox XMbox_FSLReadMBox
#endif

#ifndef XMbox_mFSLWriteMBox
#define XMbox_mFSLWriteMBox XMbox_FSLWriteMBox
#endif

#ifndef XMbox_mFSLIsEmpty
#define XMbox_mFSLIsEmpty XMbox_FSLIsEmpty
#endif

#ifndef XMbox_mFSLIsFull
#define XMbox_mFSLIsFull XMbox_FSLIsFull
#endif

#ifndef XMbox_mIsEmpty
#define XMbox_mIsEmpty XMbox_IsEmptyHw
#endif

#ifndef XMbox_mIsFull
#define XMbox_mIsFull XMbox_IsFullHw
#endif

/*********************************************************************/
/**
 * Macros for Driver XMpmc
 *
 *********************************************************************/
#ifndef XMpmc_mReadReg
#define XMpmc_mReadReg XMpmc_ReadReg
#endif

#ifndef XMpmc_mWriteReg
#define XMpmc_mWriteReg XMpmc_WriteReg
#endif

/*********************************************************************/
/**
 * Macros for Driver XMutex
 *
 *********************************************************************/
#ifndef XMutex_mWriteReg
#define XMutex_mWriteReg XMutex_WriteReg
#endif

#ifndef XMutex_mReadReg
#define XMutex_mReadReg XMutex_ReadReg
#endif

/*********************************************************************/
/**
 * Macros for Driver XPcie
 *
 *********************************************************************/
#ifndef XPcie_mReadReg
#define XPcie_mReadReg XPcie_ReadReg
#endif

#ifndef XPcie_mWriteReg
#define XPcie_mWriteReg XPcie_WriteReg
#endif

/*********************************************************************/
/**
 * Macros for Driver XSpi
 *
 *********************************************************************/
#ifndef XSpi_mIntrGlobalEnable
#define XSpi_mIntrGlobalEnable XSpi_IntrGlobalEnable
#endif

#ifndef XSpi_mIntrGlobalDisable
#define XSpi_mIntrGlobalDisable XSpi_IntrGlobalDisable
#endif

#ifndef XSpi_mIsIntrGlobalEnabled
#define XSpi_mIsIntrGlobalEnabled XSpi_IsIntrGlobalEnabled
#endif

#ifndef XSpi_mIntrGetStatus
#define XSpi_mIntrGetStatus XSpi_IntrGetStatus
#endif

#ifndef XSpi_mIntrClear
#define XSpi_mIntrClear XSpi_IntrClear
#endif

#ifndef XSpi_mIntrEnable
#define XSpi_mIntrEnable XSpi_IntrEnable
#endif

#ifndef XSpi_mIntrDisable
#define XSpi_mIntrDisable XSpi_IntrDisable
#endif

#ifndef XSpi_mIntrGetEnabled
#define XSpi_mIntrGetEnabled XSpi_IntrGetEnabled
#endif

#ifndef XSpi_mSetControlReg
#define XSpi_mSetControlReg XSpi_SetControlReg
#endif

#ifndef XSpi_mGetControlReg
#define XSpi_mGetControlReg XSpi_GetControlReg
#endif

#ifndef XSpi_mGetStatusReg
#define XSpi_mGetStatusReg XSpi_GetStatusReg
#endif

#ifndef XSpi_mSetSlaveSelectReg
#define XSpi_mSetSlaveSelectReg XSpi_SetSlaveSelectReg
#endif

#ifndef XSpi_mGetSlaveSelectReg
#define XSpi_mGetSlaveSelectReg XSpi_GetSlaveSelectReg
#endif

#ifndef XSpi_mEnable
#define XSpi_mEnable XSpi_Enable
#endif

#ifndef XSpi_mDisable
#define XSpi_mDisable XSpi_Disable
#endif

/*********************************************************************/
/**
 * Macros for Driver XSysAce
 *
 *********************************************************************/
#ifndef XSysAce_mGetControlReg
#define XSysAce_mGetControlReg XSysAce_GetControlReg
#endif

#ifndef XSysAce_mSetControlReg
#define XSysAce_mSetControlReg XSysAce_SetControlReg
#endif

#ifndef XSysAce_mOrControlReg
#define XSysAce_mOrControlReg XSysAce_OrControlReg
#endif

#ifndef XSysAce_mAndControlReg
#define XSysAce_mAndControlReg XSysAce_AndControlReg
#endif

#ifndef XSysAce_mGetErrorReg
#define XSysAce_mGetErrorReg XSysAce_GetErrorReg
#endif

#ifndef XSysAce_mGetStatusReg
#define XSysAce_mGetStatusReg XSysAce_GetStatusReg
#endif

#ifndef XSysAce_mWaitForLock
#define XSysAce_mWaitForLock XSysAce_WaitForLock
#endif

#ifndef XSysAce_mEnableIntr
#define XSysAce_mEnableIntr XSysAce_EnableIntr
#endif

#ifndef XSysAce_mDisableIntr
#define XSysAce_mDisableIntr XSysAce_DisableIntr
#endif

#ifndef XSysAce_mIsReadyForCmd
#define XSysAce_mIsReadyForCmd XSysAce_IsReadyForCmd
#endif

#ifndef XSysAce_mIsMpuLocked
#define XSysAce_mIsMpuLocked XSysAce_IsMpuLocked
#endif

#ifndef XSysAce_mIsIntrEnabled
#define XSysAce_mIsIntrEnabled XSysAce_IsIntrEnabled
#endif

/*********************************************************************/
/**
 * Macros for Driver XSysMon
 *
 *********************************************************************/
#ifndef XSysMon_mIsEventSamplingModeSet
#define XSysMon_mIsEventSamplingModeSet XSysMon_IsEventSamplingModeSet
#endif

#ifndef XSysMon_mIsDrpBusy
#define XSysMon_mIsDrpBusy XSysMon_IsDrpBusy
#endif

#ifndef XSysMon_mIsDrpLocked
#define XSysMon_mIsDrpLocked XSysMon_IsDrpLocked
#endif

#ifndef XSysMon_mRawToTemperature
#define XSysMon_mRawToTemperature XSysMon_RawToTemperature
#endif

#ifndef XSysMon_mRawToVoltage
#define XSysMon_mRawToVoltage XSysMon_RawToVoltage
#endif

#ifndef XSysMon_mTemperatureToRaw
#define XSysMon_mTemperatureToRaw XSysMon_TemperatureToRaw
#endif

#ifndef XSysMon_mVoltageToRaw
#define XSysMon_mVoltageToRaw XSysMon_VoltageToRaw
#endif

#ifndef XSysMon_mReadReg
#define XSysMon_mReadReg XSysMon_ReadReg
#endif

#ifndef XSysMon_mWriteReg
#define XSysMon_mWriteReg XSysMon_WriteReg
#endif

/*********************************************************************/
/**
 * Macros for Driver XTmrCtr
 *
 *********************************************************************/
#ifndef XTimerCtr_mReadReg
#define XTimerCtr_mReadReg XTimerCtr_ReadReg
#endif

#ifndef XTmrCtr_mWriteReg
#define XTmrCtr_mWriteReg XTmrCtr_WriteReg
#endif

#ifndef XTmrCtr_mSetControlStatusReg
#define XTmrCtr_mSetControlStatusReg XTmrCtr_SetControlStatusReg
#endif

#ifndef XTmrCtr_mGetControlStatusReg
#define XTmrCtr_mGetControlStatusReg XTmrCtr_GetControlStatusReg
#endif

#ifndef XTmrCtr_mGetTimerCounterReg
#define XTmrCtr_mGetTimerCounterReg XTmrCtr_GetTimerCounterReg
#endif

#ifndef XTmrCtr_mSetLoadReg
#define XTmrCtr_mSetLoadReg XTmrCtr_SetLoadReg
#endif

#ifndef XTmrCtr_mGetLoadReg
#define XTmrCtr_mGetLoadReg XTmrCtr_GetLoadReg
#endif

#ifndef XTmrCtr_mEnable
#define XTmrCtr_mEnable XTmrCtr_Enable
#endif

#ifndef XTmrCtr_mDisable
#define XTmrCtr_mDisable XTmrCtr_Disable
#endif

#ifndef XTmrCtr_mEnableIntr
#define XTmrCtr_mEnableIntr XTmrCtr_EnableIntr
#endif

#ifndef XTmrCtr_mDisableIntr
#define XTmrCtr_mDisableIntr XTmrCtr_DisableIntr
#endif

#ifndef XTmrCtr_mLoadTimerCounterReg
#define XTmrCtr_mLoadTimerCounterReg XTmrCtr_LoadTimerCounterReg
#endif

#ifndef XTmrCtr_mHasEventOccurred
#define XTmrCtr_mHasEventOccurred XTmrCtr_HasEventOccurred
#endif

/*********************************************************************/
/**
 * Macros for Driver XUartLite
 *
 *********************************************************************/
#ifndef XUartLite_mUpdateStats
#define XUartLite_mUpdateStats XUartLite_UpdateStats
#endif

#ifndef XUartLite_mWriteReg
#define XUartLite_mWriteReg XUartLite_WriteReg
#endif

#ifndef XUartLite_mReadReg
#define XUartLite_mReadReg XUartLite_ReadReg
#endif

#ifndef XUartLite_mClearStats
#define XUartLite_mClearStats XUartLite_ClearStats
#endif

#ifndef XUartLite_mSetControlReg
#define XUartLite_mSetControlReg XUartLite_SetControlReg
#endif

#ifndef XUartLite_mGetStatusReg
#define XUartLite_mGetStatusReg XUartLite_GetStatusReg
#endif

#ifndef XUartLite_mIsReceiveEmpty
#define XUartLite_mIsReceiveEmpty XUartLite_IsReceiveEmpty
#endif

#ifndef XUartLite_mIsTransmitFull
#define XUartLite_mIsTransmitFull XUartLite_IsTransmitFull
#endif

#ifndef XUartLite_mIsIntrEnabled
#define XUartLite_mIsIntrEnabled XUartLite_IsIntrEnabled
#endif

#ifndef XUartLite_mEnableIntr
#define XUartLite_mEnableIntr XUartLite_EnableIntr
#endif

#ifndef XUartLite_mDisableIntr
#define XUartLite_mDisableIntr XUartLite_DisableIntr
#endif

/*********************************************************************/
/**
 * Macros for Driver XUartNs550
 *
 *********************************************************************/
#ifndef XUartNs550_mUpdateStats
#define XUartNs550_mUpdateStats XUartNs550_UpdateStats
#endif

#ifndef XUartNs550_mReadReg
#define XUartNs550_mReadReg XUartNs550_ReadReg
#endif

#ifndef XUartNs550_mWriteReg
#define XUartNs550_mWriteReg XUartNs550_WriteReg
#endif

#ifndef XUartNs550_mClearStats
#define XUartNs550_mClearStats XUartNs550_ClearStats
#endif

#ifndef XUartNs550_mGetLineStatusReg
#define XUartNs550_mGetLineStatusReg XUartNs550_GetLineStatusReg
#endif

#ifndef XUartNs550_mGetLineControlReg
#define XUartNs550_mGetLineControlReg XUartNs550_GetLineControlReg
#endif

#ifndef XUartNs550_mSetLineControlReg
#define XUartNs550_mSetLineControlReg XUartNs550_SetLineControlReg
#endif

#ifndef XUartNs550_mEnableIntr
#define XUartNs550_mEnableIntr XUartNs550_EnableIntr
#endif

#ifndef XUartNs550_mDisableIntr
#define XUartNs550_mDisableIntr XUartNs550_DisableIntr
#endif

#ifndef XUartNs550_mIsReceiveData
#define XUartNs550_mIsReceiveData XUartNs550_IsReceiveData
#endif

#ifndef XUartNs550_mIsTransmitEmpty
#define XUartNs550_mIsTransmitEmpty XUartNs550_IsTransmitEmpty
#endif

/*********************************************************************/
/**
 * Macros for Driver XUsb
 *
 *********************************************************************/
#ifndef XUsb_mReadReg
#define XUsb_mReadReg XUsb_ReadReg
#endif

#ifndef XUsb_mWriteReg
#define XUsb_mWriteReg XUsb_WriteReg
#endif

#endif
