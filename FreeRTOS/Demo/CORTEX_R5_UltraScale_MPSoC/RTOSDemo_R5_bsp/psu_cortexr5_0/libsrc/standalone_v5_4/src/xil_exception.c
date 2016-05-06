/******************************************************************************
*
* Copyright (C) 2014 - 2015 Xilinx, Inc. All rights reserved.
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
/****************************************************************************/
/**
*
* @file xil_exception.c
*
* This file contains low-level driver functions for the Cortex R5 exception
* Handler.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who      Date     Changes
* ----- -------- -------- -----------------------------------------------
* 5.00 	pkp  	 02/20/14 First release
*
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_exception.h"
#include "xpseudo_asm.h"
#include "xdebug.h"
/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

typedef struct {
	Xil_ExceptionHandler Handler;
	void *Data;
} XExc_VectorTableEntry;

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Function Prototypes *****************************/
static void Xil_ExceptionNullHandler(void *Data);
/************************** Variable Definitions *****************************/
/*
 * Exception vector table to store handlers for each exception vector.
 */
XExc_VectorTableEntry XExc_VectorTable[XIL_EXCEPTION_ID_LAST + 1] =
{
	{Xil_ExceptionNullHandler, NULL},
	{Xil_ExceptionNullHandler, NULL},
	{Xil_ExceptionNullHandler, NULL},
	{Xil_PrefetchAbortHandler, NULL},
	{Xil_DataAbortHandler, NULL},
	{Xil_ExceptionNullHandler, NULL},
	{Xil_ExceptionNullHandler, NULL},
};

/*****************************************************************************/

/****************************************************************************/
/**
*
* This function is a stub Handler that is the default Handler that gets called
* if the application has not setup a Handler for a specific  exception. The
* function interface has to match the interface specified for a Handler even
* though none of the arguments are used.
*
* @param	Data is unused by this function.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
static void Xil_ExceptionNullHandler(void *Data)
{
	(void *)Data;
DieLoop: goto DieLoop;
}

/****************************************************************************/
/**
* The function is a common API used to initialize exception handlers across all
* processors supported. For ARM CortexR5, the exception handlers are being
* initialized statically and hence this function does not do anything.
*
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void Xil_ExceptionInit(void)
{
	return;
}

/*****************************************************************************/
/**
*
* Makes the connection between the Id of the exception source and the
* associated Handler that is to run when the exception is recognized. The
* argument provided in this call as the Data is used as the argument
* for the Handler when it is called.
*
* @param	exception_id contains the ID of the exception source and should
*		be in the range of 0 to XIL_EXCEPTION_ID_LAST.
		See xil_exception_l.h for further information.
* @param	Handler to the Handler for that exception.
* @param	Data is a reference to Data that will be passed to the
*		Handler when it gets called.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void Xil_ExceptionRegisterHandler(u32 Exception_id,
				    Xil_ExceptionHandler Handler,
				    void *Data)
{
	XExc_VectorTable[Exception_id].Handler = Handler;
	XExc_VectorTable[Exception_id].Data = Data;
}

/*****************************************************************************/
/**
*
* Removes the Handler for a specific exception Id. The stub Handler is then
* registered for this exception Id.
*
* @param	exception_id contains the ID of the exception source and should
*		be in the range of 0 to XIL_EXCEPTION_ID_LAST.
*		See xil_exception_l.h for further information.

* @return	None.
*
* @note		None.
*
****************************************************************************/
void Xil_ExceptionRemoveHandler(u32 Exception_id)
{
	Xil_ExceptionRegisterHandler(Exception_id,
				       Xil_ExceptionNullHandler,
				       NULL);
}
/*****************************************************************************/
/**
*
* Default Data abort handler which prints a debug message on console if
* Debug flag is enabled
*
* @param	None
*
* @return	None.
*
* @note		None.
*
****************************************************************************/

void Xil_DataAbortHandler(void *CallBackRef){

	xdbg_printf(XDBG_DEBUG_ERROR, "Data abort \n");
	while(1) {
		;
	}
}

/*****************************************************************************/
/**
*
* Default Prefetch abort handler which printsa debug message on console if
* Debug flag is enabled
*
* @param	None
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void Xil_PrefetchAbortHandler(void *CallBackRef){

	xdbg_printf(XDBG_DEBUG_ERROR, "Prefetch abort \n");
	while(1) {
		;
	}
}
