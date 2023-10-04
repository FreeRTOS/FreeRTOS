/******************************************************************************
 *
 * Copyright (C) 2016 Xilinx, Inc.  All rights reserved.
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
 *****************************************************************************/
/****************************************************************************/

/**
 *
 * @file xusbpsu_endpoint.c
 * @addtogroup usbpsu_v1_3
 * @{
 *
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- -------------------------------------------------------
 * 1.0   sg  06/06/16 First release
 * 1.3   vak 04/03/17 Added CCI support for USB
 * 1.4	bk  12/01/18 Modify USBPSU driver code to fit USB common example code
 *		       for all USB IPs
 *	myk 12/01/18 Added hibernation support for device mode
 * </pre>
 *
 *****************************************************************************/

/***************************** Include Files *********************************/
#include "xusbpsu_endpoint.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

/****************************************************************************/

/**
 * Returns zeroed parameters to be used by Endpoint commands
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 *
 * @return	Zeroed Params structure pointer.
 *
 * @note		None.
 *
 *****************************************************************************/
struct XUsbPsu_EpParams * XUsbPsu_GetEpParams( struct XUsbPsu * InstancePtr )
{
    if( InstancePtr == NULL )
    {
        return NULL;
    }

    InstancePtr->EpParams.Param0 = 0x00U;
    InstancePtr->EpParams.Param1 = 0x00U;
    InstancePtr->EpParams.Param2 = 0x00U;

    return &InstancePtr->EpParams;
}

/****************************************************************************/

/**
 * Returns Transfer Index assigned by Core for an Endpoint transfer.
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	UsbEpNum is USB endpoint number.
 * @param	Dir is direction of endpoint - XUSBPSU_EP_DIR_IN/XUSBPSU_EP_DIR_OUT
 *
 * @return	Transfer Resource Index.
 *
 * @note		None.
 *
 *****************************************************************************/
u32 XUsbPsu_EpGetTransferIndex( struct XUsbPsu * InstancePtr,
                                u8 UsbEpNum,
                                u8 Dir )
{
    u8 PhyEpNum;
    u32 ResourceIndex;

    Xil_AssertNonvoid( InstancePtr != NULL );
    Xil_AssertNonvoid( UsbEpNum <= ( u8 ) 16U );
    Xil_AssertNonvoid( ( Dir == XUSBPSU_EP_DIR_IN ) ||
                       ( Dir == XUSBPSU_EP_DIR_OUT ) );

    PhyEpNum = ( u8 ) PhysicalEp( UsbEpNum, Dir );
    ResourceIndex = XUsbPsu_ReadReg( InstancePtr, XUSBPSU_DEPCMD( PhyEpNum ) );

    return ( u32 ) XUSBPSU_DEPCMD_GET_RSC_IDX( ResourceIndex );
}

/****************************************************************************/

/**
 * Sends Endpoint command to Endpoint.
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	UsbEpNum is USB endpoint number.
 * @param	Dir is direction of endpoint
 *			- XUSBPSU_EP_DIR_IN/ XUSBPSU_EP_DIR_OUT.
 * @param	Cmd is Endpoint command.
 * @param	Params is Endpoint command parameters.
 *
 * @return	XST_SUCCESS else XST_FAILURE.
 *
 * @note		None.
 *
 *****************************************************************************/
s32 XUsbPsu_SendEpCmd( struct XUsbPsu * InstancePtr,
                       u8 UsbEpNum,
                       u8 Dir,
                       u32 Cmd,
                       struct XUsbPsu_EpParams * Params )
{
    u32 PhyEpNum;

    Xil_AssertNonvoid( InstancePtr != NULL );
    Xil_AssertNonvoid( UsbEpNum <= ( u8 ) 16U );
    Xil_AssertNonvoid( ( Dir == XUSBPSU_EP_DIR_IN ) ||
                       ( Dir == XUSBPSU_EP_DIR_OUT ) );

    PhyEpNum = PhysicalEp( UsbEpNum, Dir );

    XUsbPsu_WriteReg( InstancePtr, XUSBPSU_DEPCMDPAR0( PhyEpNum ),
                      Params->Param0 );
    XUsbPsu_WriteReg( InstancePtr, XUSBPSU_DEPCMDPAR1( PhyEpNum ),
                      Params->Param1 );
    XUsbPsu_WriteReg( InstancePtr, XUSBPSU_DEPCMDPAR2( PhyEpNum ),
                      Params->Param2 );

    XUsbPsu_WriteReg( InstancePtr, XUSBPSU_DEPCMD( PhyEpNum ),
                      Cmd | XUSBPSU_DEPCMD_CMDACT );

    if( XUsbPsu_Wait_Clear_Timeout( InstancePtr, XUSBPSU_DEPCMD( PhyEpNum ),
                                    XUSBPSU_DEPCMD_CMDACT, 500U ) == ( s32 ) XST_FAILURE )
    {
        return XST_FAILURE;
    }

    return XST_SUCCESS;
}

/****************************************************************************/

/**
 * Sends Start New Configuration command to Endpoint.
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	UsbEpNum is USB endpoint number.
 * @param	Dir is direction of endpoint
 *			- XUSBPSU_EP_DIR_IN/ XUSBPSU_EP_DIR_OUT.
 *
 * @return	XST_SUCCESS else XST_FAILURE.
 *
 * @note
 *          As per data book this command should be issued by software
 *			under these conditions:
 *				1. After power-on-reset with XferRscIdx=0 before starting
 *				   to configure Physical Endpoints 0 and 1.
 *				2. With XferRscIdx=2 before starting to configure
 *				   Physical Endpoints > 1
 *				3. This command should always be issued to
 *				   Endpoint 0 (DEPCMD0).
 *
 *****************************************************************************/
s32 XUsbPsu_StartEpConfig( struct XUsbPsu * InstancePtr,
                           u32 UsbEpNum,
                           u8 Dir )
{
    struct XUsbPsu_EpParams * Params;
    u32 Cmd;
    u8 PhyEpNum;

    Xil_AssertNonvoid( InstancePtr != NULL );
    Xil_AssertNonvoid( UsbEpNum <= ( u32 ) 16U );
    Xil_AssertNonvoid( ( Dir == XUSBPSU_EP_DIR_IN ) ||
                       ( Dir == XUSBPSU_EP_DIR_OUT ) );

    PhyEpNum = ( u8 ) PhysicalEp( UsbEpNum, ( u32 ) Dir );
    Params = XUsbPsu_GetEpParams( InstancePtr );
    Xil_AssertNonvoid( Params != NULL );

    if( PhyEpNum != 1U )
    {
        Cmd = XUSBPSU_DEPCMD_DEPSTARTCFG;

        /* XferRscIdx == 0 for EP0 and 2 for the remaining */
        if( PhyEpNum > 1U )
        {
            if( InstancePtr->IsConfigDone != 0U )
            {
                return XST_SUCCESS;
            }

            InstancePtr->IsConfigDone = 1U;
            Cmd |= XUSBPSU_DEPCMD_PARAM( 2 );
        }

        return XUsbPsu_SendEpCmd( InstancePtr, 0U, XUSBPSU_EP_DIR_OUT,
                                  Cmd, Params );
    }

    return XST_SUCCESS;
}

/****************************************************************************/

/**
 * Sends Set Endpoint Configuration command to Endpoint.
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	UsbEpNum is USB endpoint number.
 * @param	Dir is direction of endpoint - XUSBPSU_EP_DIR_IN/XUSBPSU_EP_DIR_OUT.
 * @param	Size is size of Endpoint size.
 * @param	Type is Endpoint type Control/Bulk/Interrupt/Isoc.
 * @param	Restore should be true if saved state should be restored;
 *			typically this would be false
 *
 * @return	XST_SUCCESS else XST_FAILURE.
 *
 * @note		None.
 *
 *****************************************************************************/
s32 XUsbPsu_SetEpConfig( struct XUsbPsu * InstancePtr,
                         u8 UsbEpNum,
                         u8 Dir,
                         u16 Size,
                         u8 Type,
                         u8 Restore )
{
    struct XUsbPsu_Ep * Ept;
    struct XUsbPsu_EpParams * Params;
    u8 PhyEpNum;

    Xil_AssertNonvoid( InstancePtr != NULL );
    Xil_AssertNonvoid( UsbEpNum <= ( u8 ) 16U );
    Xil_AssertNonvoid( ( Dir == XUSBPSU_EP_DIR_IN ) ||
                       ( Dir == XUSBPSU_EP_DIR_OUT ) );
    Xil_AssertNonvoid( ( Size >= 64U ) && ( Size <= 1024U ) );

    Params = XUsbPsu_GetEpParams( InstancePtr );
    Xil_AssertNonvoid( Params != NULL );

    PhyEpNum = PhysicalEp( UsbEpNum, Dir );
    Ept = &InstancePtr->eps[ PhyEpNum ];

    Params->Param0 = XUSBPSU_DEPCFG_EP_TYPE( Type )
                     | XUSBPSU_DEPCFG_MAX_PACKET_SIZE( Size );

    /*
     * Set burst size to 1 as recommended
     */
    if( InstancePtr->AppData->Speed == XUSBPSU_SPEED_SUPER )
    {
        Params->Param0 |= XUSBPSU_DEPCFG_BURST_SIZE( 1 );
    }

    Params->Param1 = XUSBPSU_DEPCFG_XFER_COMPLETE_EN
                     | XUSBPSU_DEPCFG_XFER_NOT_READY_EN;

    if( Restore )
    {
        Params->Param0 |= XUSBPSU_DEPCFG_ACTION_RESTORE;
        Params->Param2 = Ept->EpSavedState;
    }

    /*
     * We are doing 1:1 mapping for endpoints, meaning
     * Physical Endpoints 2 maps to Logical Endpoint 2 and
     * so on. We consider the direction bit as part of the physical
     * endpoint number. So USB endpoint 0x81 is 0x03.
     */
    Params->Param1 |= XUSBPSU_DEPCFG_EP_NUMBER( PhyEpNum );

    if( Dir != XUSBPSU_EP_DIR_OUT )
    {
        Params->Param0 |= XUSBPSU_DEPCFG_FIFO_NUMBER( ( u32 ) PhyEpNum >> 1 );
    }

    if( Ept->Type == XUSBPSU_ENDPOINT_XFER_ISOC )
    {
        Params->Param1 |= XUSBPSU_DEPCFG_BINTERVAL_M1( Ept->Interval - 1 );
        Params->Param1 |= XUSBPSU_DEPCFG_XFER_IN_PROGRESS_EN;
    }

    return XUsbPsu_SendEpCmd( InstancePtr, UsbEpNum, Dir,
                              XUSBPSU_DEPCMD_SETEPCONFIG, Params );
}

/****************************************************************************/

/**
 * Sends Set Transfer Resource command to Endpoint.
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	UsbEpNum is USB endpoint number.
 * @param	Dir is direction of endpoint - XUSBPSU_EP_DIR_IN/
 *											XUSBPSU_EP_DIR_OUT.
 *
 * @return	XST_SUCCESS else XST_FAILURE.
 *
 * @note		None.
 *
 *****************************************************************************/
s32 XUsbPsu_SetXferResource( struct XUsbPsu * InstancePtr,
                             u8 UsbEpNum,
                             u8 Dir )
{
    struct XUsbPsu_EpParams * Params;


    Xil_AssertNonvoid( InstancePtr != NULL );
    Xil_AssertNonvoid( UsbEpNum <= ( u8 ) 16U );
    Xil_AssertNonvoid( ( Dir == XUSBPSU_EP_DIR_IN ) ||
                       ( Dir == XUSBPSU_EP_DIR_OUT ) );

    Params = XUsbPsu_GetEpParams( InstancePtr );
    Xil_AssertNonvoid( Params != NULL );

    Params->Param0 = XUSBPSU_DEPXFERCFG_NUM_XFER_RES( 1 );

    return XUsbPsu_SendEpCmd( InstancePtr, UsbEpNum, Dir,
                              XUSBPSU_DEPCMD_SETTRANSFRESOURCE, Params );
}

/****************************************************************************/

/**
 * Enables Endpoint for sending/receiving data.
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	UsbEpNum is USB endpoint number.
 * @param	Dir is direction of endpoint - XUSBPSU_EP_DIR_IN/XUSBPSU_EP_DIR_OUT.
 * @param	Maxsize is size of Endpoint size.
 * @param	Type is Endpoint type Control/Bulk/Interrupt/Isoc.
 * @param	Restore should be true if saved state should be restored;
 *			typically this would be false
 *
 * @return	XST_SUCCESS else XST_FAILURE.
 *
 * @note		None.
 *
 ****************************************************************************/
s32 XUsbPsu_EpEnable( struct XUsbPsu * InstancePtr,
                      u8 UsbEpNum,
                      u8 Dir,
                      u16 Maxsize,
                      u8 Type,
                      u8 Restore )
{
    struct XUsbPsu_Ep * Ept;
    struct XUsbPsu_Trb * TrbStHw, * TrbLink;
    u32 RegVal;
    s32 Ret = ( s32 ) XST_FAILURE;
    u32 PhyEpNum;

    Xil_AssertNonvoid( InstancePtr != NULL );
    Xil_AssertNonvoid( UsbEpNum <= ( u8 ) 16U );
    Xil_AssertNonvoid( ( Dir == XUSBPSU_EP_DIR_IN ) ||
                       ( Dir == XUSBPSU_EP_DIR_OUT ) );
    Xil_AssertNonvoid( ( Maxsize >= 64U ) && ( Maxsize <= 1024U ) );

    PhyEpNum = PhysicalEp( UsbEpNum, Dir );
    Ept = &InstancePtr->eps[ PhyEpNum ];

    Ept->UsbEpNum = UsbEpNum;
    Ept->Direction = Dir;
    Ept->Type = Type;
    Ept->MaxSize = Maxsize;
    Ept->PhyEpNum = ( u8 ) PhyEpNum;
    Ept->CurUf = 0;

    if( !InstancePtr->IsHibernated )
    {
        Ept->TrbEnqueue = 0;
        Ept->TrbDequeue = 0;
    }

    if( ( ( Ept->EpStatus & XUSBPSU_EP_ENABLED ) == 0U ) ||
        ( InstancePtr->IsHibernated ) )
    {
        Ret = XUsbPsu_StartEpConfig( InstancePtr, UsbEpNum, Dir );

        if( Ret != 0 )
        {
            return Ret;
        }
    }

    Ret = XUsbPsu_SetEpConfig( InstancePtr, UsbEpNum, Dir, Maxsize,
                               Type, Restore );

    if( Ret != 0 )
    {
        return Ret;
    }

    if( ( ( Ept->EpStatus & XUSBPSU_EP_ENABLED ) == 0U ) ||
        ( InstancePtr->IsHibernated ) )
    {
        Ret = XUsbPsu_SetXferResource( InstancePtr, UsbEpNum, Dir );

        if( Ret != 0 )
        {
            return Ret;
        }

        Ept->EpStatus |= XUSBPSU_EP_ENABLED;

        RegVal = XUsbPsu_ReadReg( InstancePtr, XUSBPSU_DALEPENA );
        RegVal |= XUSBPSU_DALEPENA_EP( Ept->PhyEpNum );
        XUsbPsu_WriteReg( InstancePtr, XUSBPSU_DALEPENA, RegVal );

        /* Following code is only applicable for ISO XFER */
        TrbStHw = &Ept->EpTrb[ 0 ];

        /* Link TRB. The HWO bit is never reset */
        TrbLink = &Ept->EpTrb[ NO_OF_TRB_PER_EP ];
        memset( TrbLink, 0x00, sizeof( struct XUsbPsu_Trb ) );

        TrbLink->BufferPtrLow = ( UINTPTR ) TrbStHw;
        TrbLink->BufferPtrHigh = ( ( UINTPTR ) TrbStHw >> 16 ) >> 16;
        TrbLink->Ctrl |= XUSBPSU_TRBCTL_LINK_TRB;
        TrbLink->Ctrl |= XUSBPSU_TRB_CTRL_HWO;
    }

    return XST_SUCCESS;
}

/****************************************************************************/

/**
 * Disables Endpoint.
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	UsbEpNum is USB endpoint number.
 * @param	Dir is direction of endpoint
 *			- XUSBPSU_EP_DIR_IN/XUSBPSU_EP_DIR_OUT.
 *
 * @return	XST_SUCCESS else XST_FAILURE.
 *
 * @note		None.
 *
 ****************************************************************************/
s32 XUsbPsu_EpDisable( struct XUsbPsu * InstancePtr,
                       u8 UsbEpNum,
                       u8 Dir )
{
    u32 RegVal;
    u8 PhyEpNum;
    struct XUsbPsu_Ep * Ept;

    Xil_AssertNonvoid( InstancePtr != NULL );
    Xil_AssertNonvoid( UsbEpNum <= ( u8 ) 16U );
    Xil_AssertNonvoid( ( Dir == XUSBPSU_EP_DIR_IN ) ||
                       ( Dir == XUSBPSU_EP_DIR_OUT ) );

    PhyEpNum = PhysicalEp( UsbEpNum, Dir );
    Ept = &InstancePtr->eps[ PhyEpNum ];

    /* make sure HW endpoint isn't stalled */
    if( Ept->EpStatus & XUSBPSU_EP_STALL )
    {
        XUsbPsu_EpClearStall( InstancePtr, Ept->UsbEpNum, Ept->Direction );
    }

    RegVal = XUsbPsu_ReadReg( InstancePtr, XUSBPSU_DALEPENA );
    RegVal &= ~XUSBPSU_DALEPENA_EP( PhyEpNum );
    XUsbPsu_WriteReg( InstancePtr, XUSBPSU_DALEPENA, RegVal );

    Ept->Type = 0U;
    Ept->EpStatus = 0U;
    Ept->MaxSize = 0U;
    Ept->TrbEnqueue = 0U;
    Ept->TrbDequeue = 0U;

    return XST_SUCCESS;
}

/****************************************************************************/

/**
 * Enables USB Control Endpoint i.e., EP0OUT and EP0IN of Core.
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	Size is control endpoint size.
 *
 * @return	XST_SUCCESS else XST_FAILURE.
 *
 * @note		None.
 *
 ****************************************************************************/
s32 XUsbPsu_EnableControlEp( struct XUsbPsu * InstancePtr,
                             u16 Size )
{
    s32 RetVal;

    Xil_AssertNonvoid( InstancePtr != NULL );
    Xil_AssertNonvoid( ( Size >= 64U ) && ( Size <= 512U ) );

    RetVal = XUsbPsu_EpEnable( InstancePtr, 0U, XUSBPSU_EP_DIR_OUT, Size,
                               XUSBPSU_ENDPOINT_XFER_CONTROL, FALSE );

    if( RetVal != 0 )
    {
        return XST_FAILURE;
    }

    RetVal = XUsbPsu_EpEnable( InstancePtr, 0U, XUSBPSU_EP_DIR_IN, Size,
                               XUSBPSU_ENDPOINT_XFER_CONTROL, FALSE );

    if( RetVal != 0 )
    {
        return XST_FAILURE;
    }

    return XST_SUCCESS;
}

/****************************************************************************/

/**
 * Initializes Endpoints. All OUT endpoints are even numbered and all IN
 * endpoints are odd numbered. EP0 is for Control OUT and EP1 is for
 * Control IN.
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 *
 * @return	None.
 *
 * @note		None.
 *
 ****************************************************************************/
void XUsbPsu_InitializeEps( struct XUsbPsu * InstancePtr )
{
    u8 i;
    u8 Epnum;

    Xil_AssertVoid( InstancePtr != NULL );

    for( i = 0U; i < InstancePtr->NumOutEps; i++ )
    {
        Epnum = ( i << 1U ) | XUSBPSU_EP_DIR_OUT;
        InstancePtr->eps[ Epnum ].PhyEpNum = Epnum;
        InstancePtr->eps[ Epnum ].Direction = XUSBPSU_EP_DIR_OUT;
        InstancePtr->eps[ Epnum ].ResourceIndex = 0;
    }

    for( i = 0U; i < InstancePtr->NumInEps; i++ )
    {
        Epnum = ( i << 1U ) | XUSBPSU_EP_DIR_IN;
        InstancePtr->eps[ Epnum ].PhyEpNum = Epnum;
        InstancePtr->eps[ Epnum ].Direction = XUSBPSU_EP_DIR_IN;
        InstancePtr->eps[ Epnum ].ResourceIndex = 0;
    }
}

/****************************************************************************/

/**
 * Stops transfer on Endpoint.
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	UsbEpNum is USB endpoint number.
 * @param	Dir is direction of endpoint - XUSBPSU_EP_DIR_IN/XUSBPSU_EP_DIR_OUT.
 * @Force	Force flag to stop/pause transfer.
 *
 * @return	None.
 *
 * @note		None.
 *
 ****************************************************************************/
void XUsbPsu_StopTransfer( struct XUsbPsu * InstancePtr,
                           u8 UsbEpNum,
                           u8 Dir,
                           u8 Force )
{
    struct XUsbPsu_Ep * Ept;
    struct XUsbPsu_EpParams * Params;
    u8 PhyEpNum;
    u32 Cmd;

    Xil_AssertVoid( InstancePtr != NULL );
    Xil_AssertVoid( UsbEpNum <= ( u8 ) 16U );
    Xil_AssertVoid( ( Dir == XUSBPSU_EP_DIR_IN ) || ( Dir == XUSBPSU_EP_DIR_OUT ) );

    PhyEpNum = PhysicalEp( UsbEpNum, Dir );
    Params = XUsbPsu_GetEpParams( InstancePtr );
    Xil_AssertVoid( Params != NULL );

    Ept = &InstancePtr->eps[ PhyEpNum ];

    if( Ept->ResourceIndex == 0U )
    {
        return;
    }

    /*
     * - Issue EndTransfer WITH CMDIOC bit set
     * - Wait 100us
     */
    Cmd = XUSBPSU_DEPCMD_ENDTRANSFER;
    Cmd |= Force ? XUSBPSU_DEPCMD_HIPRI_FORCERM : 0;
    Cmd |= XUSBPSU_DEPCMD_CMDIOC;
    Cmd |= XUSBPSU_DEPCMD_PARAM( Ept->ResourceIndex );
    ( void ) XUsbPsu_SendEpCmd( InstancePtr, Ept->UsbEpNum, Ept->Direction,
                                Cmd, Params );

    if( Force )
    {
        Ept->ResourceIndex = 0U;
    }

    Ept->EpStatus &= ~XUSBPSU_EP_BUSY;
    XUsbSleep( 100U );
}

/****************************************************************************/

/**
 * Query endpoint state and save it in EpSavedState
 *
 * @param   InstancePtr is a pointer to the XUsbPsu instance.
 * @param   Ept is a pointer to the XUsbPsu pointer structure.
 *
 * @return	None.
 *
 * @note		None.
 *
 ****************************************************************************/
void XUsbPsu_SaveEndpointState( struct XUsbPsu * InstancePtr,
                                struct XUsbPsu_Ep * Ept )
{
    struct XUsbPsu_EpParams * Params = XUsbPsu_GetEpParams( InstancePtr );

    XUsbPsu_SendEpCmd( InstancePtr, Ept->UsbEpNum, Ept->Direction,
                       XUSBPSU_DEPCMD_GETEPSTATE, Params );
    Ept->EpSavedState = XUsbPsu_ReadReg( InstancePtr, XUSBPSU_DEPCMDPAR2( Ept->PhyEpNum ) );
}

/****************************************************************************/

/**
 * Clears Stall on all endpoints.
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 *
 * @return	None.
 *
 * @note		None.
 *
 ****************************************************************************/
void XUsbPsu_ClearStalls( struct XUsbPsu * InstancePtr )
{
    struct XUsbPsu_EpParams * Params;
    u32 Epnum;
    struct XUsbPsu_Ep * Ept;

    Xil_AssertVoid( InstancePtr != NULL );

    Params = XUsbPsu_GetEpParams( InstancePtr );
    Xil_AssertVoid( Params != NULL );

    for( Epnum = 1U; Epnum < XUSBPSU_ENDPOINTS_NUM; Epnum++ )
    {
        Ept = &InstancePtr->eps[ Epnum ];

        if( Ept == NULL )
        {
            continue;
        }

        if( ( Ept->EpStatus & XUSBPSU_EP_STALL ) == 0U )
        {
            continue;
        }

        Ept->EpStatus &= ~XUSBPSU_EP_STALL;

        ( void ) XUsbPsu_SendEpCmd( InstancePtr, Ept->UsbEpNum,
                                    Ept->Direction, XUSBPSU_DEPCMD_CLEARSTALL,
                                    Params );
    }
}

/****************************************************************************/

/**
 * Initiates DMA to send data on endpoint to Host.
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	UsbEp is USB endpoint number.
 * @param	BufferPtr is pointer to data.
 * @param	BufferLen is length of data buffer.
 *
 * @return	XST_SUCCESS else XST_FAILURE
 *
 * @note		None.
 *
 *****************************************************************************/
s32 XUsbPsu_EpBufferSend( struct XUsbPsu * InstancePtr,
                          u8 UsbEp,
                          u8 * BufferPtr,
                          u32 BufferLen )
{
    u8 PhyEpNum;
    u32 cmd;
    s32 RetVal;
    struct XUsbPsu_Trb * TrbPtr;
    struct XUsbPsu_Ep * Ept;
    struct XUsbPsu_EpParams * Params;

    Xil_AssertNonvoid( InstancePtr != NULL );
    Xil_AssertNonvoid( UsbEp <= ( u8 ) 16U );
    Xil_AssertNonvoid( BufferPtr != NULL );

    PhyEpNum = PhysicalEp( UsbEp, XUSBPSU_EP_DIR_IN );

    if( PhyEpNum == 1U )
    {
        RetVal = XUsbPsu_Ep0Send( InstancePtr, BufferPtr, BufferLen );
        return RetVal;
    }

    Ept = &InstancePtr->eps[ PhyEpNum ];

    if( Ept->Direction != XUSBPSU_EP_DIR_IN )
    {
        return XST_FAILURE;
    }

    Ept->RequestedBytes = BufferLen;
    Ept->BytesTxed = 0U;
    Ept->BufferPtr = BufferPtr;

    TrbPtr = &Ept->EpTrb[ Ept->TrbEnqueue ];
    Xil_AssertNonvoid( TrbPtr != NULL );

    Ept->TrbEnqueue++;

    if( Ept->TrbEnqueue == NO_OF_TRB_PER_EP )
    {
        Ept->TrbEnqueue = 0;
    }

    TrbPtr->BufferPtrLow = ( UINTPTR ) BufferPtr;
    TrbPtr->BufferPtrHigh = ( ( UINTPTR ) BufferPtr >> 16 ) >> 16;
    TrbPtr->Size = BufferLen & XUSBPSU_TRB_SIZE_MASK;

    switch( Ept->Type )
    {
        case XUSBPSU_ENDPOINT_XFER_ISOC:

            /*
             *  According to DWC3 datasheet, XUSBPSU_TRBCTL_ISOCHRONOUS and
             *  XUSBPSU_TRBCTL_CHN fields are only set when request has
             *  scattered list so these fields are not set over here.
             */
            TrbPtr->Ctrl = ( XUSBPSU_TRBCTL_ISOCHRONOUS_FIRST
                             | XUSBPSU_TRB_CTRL_CSP );

            break;

        case XUSBPSU_ENDPOINT_XFER_INT:
        case XUSBPSU_ENDPOINT_XFER_BULK:
            TrbPtr->Ctrl = ( XUSBPSU_TRBCTL_NORMAL
                             | XUSBPSU_TRB_CTRL_LST );

            break;
    }

    TrbPtr->Ctrl |= ( XUSBPSU_TRB_CTRL_HWO
                      | XUSBPSU_TRB_CTRL_IOC
                      | XUSBPSU_TRB_CTRL_ISP_IMI );

    if( InstancePtr->ConfigPtr->IsCacheCoherent == 0 )
    {
        Xil_DCacheFlushRange( ( INTPTR ) TrbPtr, sizeof( struct XUsbPsu_Trb ) );
        Xil_DCacheFlushRange( ( INTPTR ) BufferPtr, BufferLen );
    }

    Params = XUsbPsu_GetEpParams( InstancePtr );
    Xil_AssertNonvoid( Params != NULL );
    Params->Param0 = 0U;
    Params->Param1 = ( UINTPTR ) TrbPtr;

    if( Ept->EpStatus & XUSBPSU_EP_BUSY )
    {
        cmd = XUSBPSU_DEPCMD_UPDATETRANSFER;
        cmd |= XUSBPSU_DEPCMD_PARAM( Ept->ResourceIndex );
    }
    else
    {
        if( Ept->Type == XUSBPSU_ENDPOINT_XFER_ISOC )
        {
            BufferPtr += BufferLen;
            struct XUsbPsu_Trb * TrbTempNext;
            TrbTempNext = &Ept->EpTrb[ Ept->TrbEnqueue ];
            Xil_AssertNonvoid( TrbTempNext != NULL );

            Ept->TrbEnqueue++;

            if( Ept->TrbEnqueue == NO_OF_TRB_PER_EP )
            {
                Ept->TrbEnqueue = 0;
            }

            TrbTempNext->BufferPtrLow = ( UINTPTR ) BufferPtr;
            TrbTempNext->BufferPtrHigh = ( ( UINTPTR ) BufferPtr >> 16 ) >> 16;
            TrbTempNext->Size = BufferLen & XUSBPSU_TRB_SIZE_MASK;

            TrbTempNext->Ctrl = ( XUSBPSU_TRBCTL_ISOCHRONOUS_FIRST
                                  | XUSBPSU_TRB_CTRL_CSP
                                  | XUSBPSU_TRB_CTRL_HWO
                                  | XUSBPSU_TRB_CTRL_IOC
                                  | XUSBPSU_TRB_CTRL_ISP_IMI );

            if( InstancePtr->ConfigPtr->IsCacheCoherent == 0 )
            {
                Xil_DCacheFlushRange( ( INTPTR ) TrbTempNext,
                                      sizeof( struct XUsbPsu_Trb ) );
                Xil_DCacheFlushRange( ( INTPTR ) BufferPtr, BufferLen );
            }
        }

        cmd = XUSBPSU_DEPCMD_STARTTRANSFER;
        cmd |= XUSBPSU_DEPCMD_PARAM( Ept->CurUf );
    }

    RetVal = XUsbPsu_SendEpCmd( InstancePtr, UsbEp, Ept->Direction,
                                cmd, Params );

    if( RetVal != XST_SUCCESS )
    {
        return XST_FAILURE;
    }

    if( !( Ept->EpStatus & XUSBPSU_EP_BUSY ) )
    {
        Ept->ResourceIndex = ( u8 ) XUsbPsu_EpGetTransferIndex( InstancePtr,
                                                                Ept->UsbEpNum,
                                                                Ept->Direction );

        Ept->EpStatus |= XUSBPSU_EP_BUSY;
    }

    return XST_SUCCESS;
}

/****************************************************************************/

/**
 * Initiates DMA to receive data on Endpoint from Host.
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	UsbEp is USB endpoint number.
 * @param	BufferPtr is pointer to data.
 * @param	Length is length of data to be received.
 *
 * @return	XST_SUCCESS else XST_FAILURE
 *
 * @note		None.
 *
 *****************************************************************************/
s32 XUsbPsu_EpBufferRecv( struct XUsbPsu * InstancePtr,
                          u8 UsbEp,
                          u8 * BufferPtr,
                          u32 Length )
{
    u8 PhyEpNum;
    u32 cmd;
    u32 Size;
    s32 RetVal;
    struct XUsbPsu_Trb * TrbPtr;
    struct XUsbPsu_Ep * Ept;
    struct XUsbPsu_EpParams * Params;

    Xil_AssertNonvoid( InstancePtr != NULL );
    Xil_AssertNonvoid( UsbEp <= ( u8 ) 16U );
    Xil_AssertNonvoid( BufferPtr != NULL );

    PhyEpNum = PhysicalEp( UsbEp, XUSBPSU_EP_DIR_OUT );

    if( PhyEpNum == 0U )
    {
        RetVal = XUsbPsu_Ep0Recv( InstancePtr, BufferPtr, Length );
        return RetVal;
    }

    Ept = &InstancePtr->eps[ PhyEpNum ];

    if( Ept->Direction != XUSBPSU_EP_DIR_OUT )
    {
        return XST_FAILURE;
    }

    Ept->RequestedBytes = Length;
    Size = Length;
    Ept->BytesTxed = 0U;
    Ept->BufferPtr = BufferPtr;

    /*
     * 8.2.5 - An OUT transfer size (Total TRB buffer allocation)
     * must be a multiple of MaxPacketSize even if software is expecting a
     * fixed non-multiple of MaxPacketSize transfer from the Host.
     */
    if( !IS_ALIGNED( Length, Ept->MaxSize ) )
    {
        Size = ( u32 ) roundup( Length, Ept->MaxSize );
        Ept->UnalignedTx = 1U;
    }

    TrbPtr = &Ept->EpTrb[ Ept->TrbEnqueue ];
    Xil_AssertNonvoid( TrbPtr != NULL );

    Ept->TrbEnqueue++;

    if( Ept->TrbEnqueue == NO_OF_TRB_PER_EP )
    {
        Ept->TrbEnqueue = 0;
    }

    TrbPtr->BufferPtrLow = ( UINTPTR ) BufferPtr;
    TrbPtr->BufferPtrHigh = ( ( UINTPTR ) BufferPtr >> 16 ) >> 16;
    TrbPtr->Size = Size;

    switch( Ept->Type )
    {
        case XUSBPSU_ENDPOINT_XFER_ISOC:

            /*
             *  According to Linux driver, XUSBPSU_TRBCTL_ISOCHRONOUS and
             *  XUSBPSU_TRBCTL_CHN fields are only set when request has
             *  scattered list so these fields are not set over here.
             */
            TrbPtr->Ctrl = ( XUSBPSU_TRBCTL_ISOCHRONOUS_FIRST
                             | XUSBPSU_TRB_CTRL_CSP );

            break;

        case XUSBPSU_ENDPOINT_XFER_INT:
        case XUSBPSU_ENDPOINT_XFER_BULK:
            TrbPtr->Ctrl = ( XUSBPSU_TRBCTL_NORMAL
                             | XUSBPSU_TRB_CTRL_LST );

            break;
    }

    TrbPtr->Ctrl |= ( XUSBPSU_TRB_CTRL_HWO
                      | XUSBPSU_TRB_CTRL_IOC
                      | XUSBPSU_TRB_CTRL_ISP_IMI );

    if( InstancePtr->ConfigPtr->IsCacheCoherent == 0 )
    {
        Xil_DCacheFlushRange( ( INTPTR ) TrbPtr, sizeof( struct XUsbPsu_Trb ) );
        Xil_DCacheInvalidateRange( ( INTPTR ) BufferPtr, Length );
    }

    Params = XUsbPsu_GetEpParams( InstancePtr );
    Xil_AssertNonvoid( Params != NULL );
    Params->Param0 = 0U;
    Params->Param1 = ( UINTPTR ) TrbPtr;

    if( Ept->EpStatus & XUSBPSU_EP_BUSY )
    {
        cmd = XUSBPSU_DEPCMD_UPDATETRANSFER;
        cmd |= XUSBPSU_DEPCMD_PARAM( Ept->ResourceIndex );
    }
    else
    {
        if( Ept->Type == XUSBPSU_ENDPOINT_XFER_ISOC )
        {
            BufferPtr += Length;
            struct XUsbPsu_Trb * TrbTempNext;
            TrbTempNext = &Ept->EpTrb[ Ept->TrbEnqueue ];
            Xil_AssertNonvoid( TrbTempNext != NULL );

            Ept->TrbEnqueue++;

            if( Ept->TrbEnqueue == NO_OF_TRB_PER_EP )
            {
                Ept->TrbEnqueue = 0;
            }

            TrbTempNext->BufferPtrLow = ( UINTPTR ) BufferPtr;
            TrbTempNext->BufferPtrHigh = ( ( UINTPTR ) BufferPtr >> 16 ) >> 16;
            TrbTempNext->Size = Length & XUSBPSU_TRB_SIZE_MASK;

            TrbTempNext->Ctrl = ( XUSBPSU_TRBCTL_ISOCHRONOUS_FIRST
                                  | XUSBPSU_TRB_CTRL_CSP
                                  | XUSBPSU_TRB_CTRL_HWO
                                  | XUSBPSU_TRB_CTRL_IOC
                                  | XUSBPSU_TRB_CTRL_ISP_IMI );

            if( InstancePtr->ConfigPtr->IsCacheCoherent == 0 )
            {
                Xil_DCacheFlushRange( ( INTPTR ) TrbTempNext,
                                      sizeof( struct XUsbPsu_Trb ) );
                Xil_DCacheFlushRange( ( INTPTR ) BufferPtr, Length );
            }
        }

        cmd = XUSBPSU_DEPCMD_STARTTRANSFER;
        cmd |= XUSBPSU_DEPCMD_PARAM( Ept->CurUf );
    }

    RetVal = XUsbPsu_SendEpCmd( InstancePtr, UsbEp, Ept->Direction,
                                cmd, Params );

    if( RetVal != XST_SUCCESS )
    {
        return XST_FAILURE;
    }

    if( !( Ept->EpStatus & XUSBPSU_EP_BUSY ) )
    {
        Ept->ResourceIndex = ( u8 ) XUsbPsu_EpGetTransferIndex( InstancePtr,
                                                                Ept->UsbEpNum,
                                                                Ept->Direction );

        Ept->EpStatus |= XUSBPSU_EP_BUSY;
    }

    return XST_SUCCESS;
}

/****************************************************************************/

/**
 * Stalls an Endpoint.
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	Epnum is USB endpoint number.
 * @param	Dir	is direction.
 *
 * @return	None.
 *
 * @note		None.
 *
 *****************************************************************************/
void XUsbPsu_EpSetStall( struct XUsbPsu * InstancePtr,
                         u8 Epnum,
                         u8 Dir )
{
    u8 PhyEpNum;
    struct XUsbPsu_Ep * Ept = NULL;
    struct XUsbPsu_EpParams * Params;

    Xil_AssertVoid( InstancePtr != NULL );
    Xil_AssertVoid( Epnum <= ( u8 ) 16U );
    Xil_AssertVoid( ( Dir == XUSBPSU_EP_DIR_IN ) || ( Dir == XUSBPSU_EP_DIR_OUT ) );

    PhyEpNum = PhysicalEp( Epnum, Dir );
    Ept = &InstancePtr->eps[ PhyEpNum ];

    Params = XUsbPsu_GetEpParams( InstancePtr );
    Xil_AssertVoid( Params != NULL );

    ( void ) XUsbPsu_SendEpCmd( InstancePtr, Ept->UsbEpNum, Ept->Direction,
                                XUSBPSU_DEPCMD_SETSTALL, Params );

    Ept->EpStatus |= XUSBPSU_EP_STALL;
}

/****************************************************************************/

/**
 * Clears Stall on an Endpoint.
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	EpNum is USB endpoint number.
 * @param	Dir	is direction.
 *
 * @return	None.
 *
 * @note		None.
 *
 *****************************************************************************/
void XUsbPsu_EpClearStall( struct XUsbPsu * InstancePtr,
                           u8 Epnum,
                           u8 Dir )
{
    u8 PhyEpNum;
    struct XUsbPsu_Ep * Ept = NULL;
    struct XUsbPsu_EpParams * Params;

    Xil_AssertVoid( InstancePtr != NULL );
    Xil_AssertVoid( Epnum <= ( u8 ) 16U );
    Xil_AssertVoid( ( Dir == XUSBPSU_EP_DIR_IN ) || ( Dir == XUSBPSU_EP_DIR_OUT ) );

    PhyEpNum = PhysicalEp( Epnum, Dir );
    Ept = &InstancePtr->eps[ PhyEpNum ];

    Params = XUsbPsu_GetEpParams( InstancePtr );
    Xil_AssertVoid( Params != NULL );

    ( void ) XUsbPsu_SendEpCmd( InstancePtr, Ept->UsbEpNum, Ept->Direction,
                                XUSBPSU_DEPCMD_CLEARSTALL, Params );

    Ept->EpStatus &= ~XUSBPSU_EP_STALL;
}

/****************************************************************************/

/**
 * Sets an user handler to be called after data is sent/received by an Endpoint
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	EpNum is USB endpoint number.
 * @param	Dir is direction of endpoint - XUSBPSU_EP_DIR_IN/XUSBPSU_EP_DIR_OUT.
 * @param	Handler is user handler to be called.
 *
 * @return	None.
 *
 * @note		None.
 *
 *****************************************************************************/
void XUsbPsu_SetEpHandler( struct XUsbPsu * InstancePtr,
                           u8 Epnum,
                           u8 Dir,
                           void ( * Handler )( void *, u32, u32 ) )
{
    u8 PhyEpNum;
    struct XUsbPsu_Ep * Ept;

    Xil_AssertVoid( InstancePtr != NULL );
    Xil_AssertVoid( Epnum <= ( u8 ) 16U );
    Xil_AssertVoid( ( Dir == XUSBPSU_EP_DIR_IN ) || ( Dir == XUSBPSU_EP_DIR_OUT ) );

    PhyEpNum = PhysicalEp( Epnum, Dir );
    Ept = &InstancePtr->eps[ PhyEpNum ];
    Ept->Handler = Handler;
}

/****************************************************************************/

/**
 * Returns status of endpoint - Stalled or not
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	EpNum is USB endpoint number.
 * @param	Dir is direction of endpoint - XUSBPSU_EP_DIR_IN/XUSBPSU_EP_DIR_OUT.
 *
 * @return
 *			1 - if stalled
 *			0 - if not stalled
 *
 * @note		None.
 *
 *****************************************************************************/
s32 XUsbPsu_IsEpStalled( struct XUsbPsu * InstancePtr,
                         u8 Epnum,
                         u8 Dir )
{
    u8 PhyEpNum;
    struct XUsbPsu_Ep * Ept;

    Xil_AssertNonvoid( InstancePtr != NULL );
    Xil_AssertNonvoid( Epnum <= ( u8 ) 16U );
    Xil_AssertNonvoid( ( Dir == XUSBPSU_EP_DIR_IN ) || ( Dir == XUSBPSU_EP_DIR_OUT ) );

    PhyEpNum = PhysicalEp( Epnum, Dir );
    Ept = &InstancePtr->eps[ PhyEpNum ];

    return ( s32 ) ( !!( Ept->EpStatus & XUSBPSU_EP_STALL ) );
}

/****************************************************************************/

/**
 * Checks the Data Phase and calls user Endpoint handler.
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	Event is a pointer to the Endpoint event occured in core.
 *
 * @return	None.
 *
 * @note		None.
 *
 *****************************************************************************/
void XUsbPsu_EpXferComplete( struct XUsbPsu * InstancePtr,
                             const struct XUsbPsu_Event_Epevt * Event )
{
    struct XUsbPsu_Ep * Ept;
    struct XUsbPsu_Trb * TrbPtr;
    u32 Length;
    u32 Epnum;
    u8 Dir;

    Xil_AssertVoid( InstancePtr != NULL );
    Xil_AssertVoid( Event != NULL );

    Epnum = Event->Epnumber;
    Ept = &InstancePtr->eps[ Epnum ];
    Dir = Ept->Direction;
    TrbPtr = &Ept->EpTrb[ Ept->TrbDequeue ];
    Xil_AssertVoid( TrbPtr != NULL );

    Ept->TrbDequeue++;

    if( Ept->TrbDequeue == NO_OF_TRB_PER_EP )
    {
        Ept->TrbDequeue = 0;
    }

    if( InstancePtr->ConfigPtr->IsCacheCoherent == 0 )
    {
        Xil_DCacheInvalidateRange( ( INTPTR ) TrbPtr, sizeof( struct XUsbPsu_Trb ) );
    }

    if( Event->Endpoint_Event == XUSBPSU_DEPEVT_XFERCOMPLETE )
    {
        Ept->EpStatus &= ~( XUSBPSU_EP_BUSY );
        Ept->ResourceIndex = 0;
    }

    Length = TrbPtr->Size & XUSBPSU_TRB_SIZE_MASK;

    if( Length == 0U )
    {
        Ept->BytesTxed = Ept->RequestedBytes;
    }
    else
    {
        if( Dir == XUSBPSU_EP_DIR_IN )
        {
            Ept->BytesTxed = Ept->RequestedBytes - Length;
        }
        else if( Dir == XUSBPSU_EP_DIR_OUT )
        {
            if( Ept->UnalignedTx == 1U )
            {
                Ept->BytesTxed = ( u32 ) roundup( Ept->RequestedBytes,
                                                  Ept->MaxSize );
                Ept->BytesTxed -= Length;
                Ept->UnalignedTx = 0U;
            }
            else
            {
                /*
                 * Get the actual number of bytes transmitted
                 * by host
                 */
                Ept->BytesTxed = Ept->RequestedBytes - Length;
            }
        }
    }

    if( Dir == XUSBPSU_EP_DIR_OUT )
    {
        /* Invalidate Cache */
        if( InstancePtr->ConfigPtr->IsCacheCoherent == 0 )
        {
            Xil_DCacheInvalidateRange( ( INTPTR ) Ept->BufferPtr, Ept->BytesTxed );
        }
    }

    if( Ept->Handler != NULL )
    {
        Ept->Handler( InstancePtr->AppData, Ept->RequestedBytes, Ept->BytesTxed );
    }
}

/****************************************************************************/

/**
 * For Isochronous transfer, get the microframe time and calls respective Endpoint
 * handler.
 *
 * @param	InstancePtr is a pointer to the XUsbPsu instance.
 * @param	Event is a pointer to the Endpoint event occurred in core.
 *
 * @return	None.
 *
 * @note		None.
 *
 *****************************************************************************/
void XUsbPsu_EpXferNotReady( struct XUsbPsu * InstancePtr,
                             const struct XUsbPsu_Event_Epevt * Event )
{
    struct XUsbPsu_Ep * Ept;
    u32 Epnum;
    u32 CurUf, Mask;

    Xil_AssertVoid( InstancePtr != NULL );
    Xil_AssertVoid( Event != NULL );

    Epnum = Event->Epnumber;
    Ept = &InstancePtr->eps[ Epnum ];

    if( Ept->Type == XUSBPSU_ENDPOINT_XFER_ISOC )
    {
        Mask = ~( 1 << ( Ept->Interval - 1 ) );
        CurUf = Event->Parameters & Mask;
        Ept->CurUf = CurUf + ( Ept->Interval * 4 );

        if( Ept->Handler != NULL )
        {
            Ept->Handler( InstancePtr->AppData, 0, 0 );
        }
    }
}
/** @} */
