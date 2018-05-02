/******************************************************************************
*
* Copyright (C) 2009 - 2016 Xilinx, Inc. All rights reserved.
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
/*****************************************************************************/
/**
*
* @file xil_assert.h
*
* @addtogroup common_assert_apis Assert APIs and Macros
*
* The xil_assert.h file contains assert related functions and macros.
* Assert APIs/Macros specifies that a application program satisfies certain
* conditions at particular points in its execution. These function can be
* used by application programs to ensure that, application code is satisfying
* certain conditions.
*
* @{
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date   Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00a hbm  07/14/09 First release
* 6.0   kvn  05/31/16 Make Xil_AsserWait a global variable
* </pre>
*
******************************************************************************/

#ifndef XIL_ASSERT_H	/* prevent circular inclusions */
#define XIL_ASSERT_H	/* by using protection macros */

#include "xil_types.h"

#ifdef __cplusplus
extern "C" {
#endif


/***************************** Include Files *********************************/


/************************** Constant Definitions *****************************/

#define XIL_ASSERT_NONE     0U
#define XIL_ASSERT_OCCURRED 1U
#define XNULL NULL

extern u32 Xil_AssertStatus;
extern s32 Xil_AssertWait;
extern void Xil_Assert(const char8 *File, s32 Line);
void XNullHandler(void *NullParameter);

/**
 * This data type defines a callback to be invoked when an
 * assert occurs. The callback is invoked only when asserts are enabled
 */
typedef void (*Xil_AssertCallback) (const char8 *File, s32 Line);

/***************** Macros (Inline Functions) Definitions *********************/

#ifndef NDEBUG

/*****************************************************************************/
/**
* @brief    This assert macro is to be used for void functions. This in
*           conjunction with the Xil_AssertWait boolean can be used to
*           accomodate tests so that asserts which fail allow execution to
*           continue.
*
* @param    Expression: expression to be evaluated. If it evaluates to
*           false, the assert occurs.
*
* @return   Returns void unless the Xil_AssertWait variable is true, in which
*           case no return is made and an infinite loop is entered.
*
******************************************************************************/
#define Xil_AssertVoid(Expression)                \
{                                                  \
    if (Expression) {                              \
        Xil_AssertStatus = XIL_ASSERT_NONE;       \
    } else {                                       \
        Xil_Assert(__FILE__, __LINE__);            \
        Xil_AssertStatus = XIL_ASSERT_OCCURRED;   \
        return;                                    \
    }                                              \
}

/*****************************************************************************/
/**
* @brief    This assert macro is to be used for functions that do return a
*           value. This in conjunction with the Xil_AssertWait boolean can be
*           used to accomodate tests so that asserts which fail allow execution
*           to continue.
*
* @param    Expression: expression to be evaluated. If it evaluates to false,
*           the assert occurs.
*
* @return   Returns 0 unless the Xil_AssertWait variable is true, in which
* 	        case no return is made and an infinite loop is entered.
*
******************************************************************************/
#define Xil_AssertNonvoid(Expression)             \
{                                                  \
    if (Expression) {                              \
        Xil_AssertStatus = XIL_ASSERT_NONE;       \
    } else {                                       \
        Xil_Assert(__FILE__, __LINE__);            \
        Xil_AssertStatus = XIL_ASSERT_OCCURRED;   \
        return 0;                                  \
    }                                              \
}

/*****************************************************************************/
/**
* @brief     Always assert. This assert macro is to be used for void functions.
*            Use for instances where an assert should always occur.
*
* @return    Returns void unless the Xil_AssertWait variable is true, in which
*	         case no return is made and an infinite loop is entered.
*
******************************************************************************/
#define Xil_AssertVoidAlways()                   \
{                                                  \
   Xil_Assert(__FILE__, __LINE__);                 \
   Xil_AssertStatus = XIL_ASSERT_OCCURRED;        \
   return;                                         \
}

/*****************************************************************************/
/**
* @brief   Always assert. This assert macro is to be used for functions that
*          do return a value. Use for instances where an assert should always
*          occur.
*
* @return Returns void unless the Xil_AssertWait variable is true, in which
*	      case no return is made and an infinite loop is entered.
*
******************************************************************************/
#define Xil_AssertNonvoidAlways()                \
{                                                  \
   Xil_Assert(__FILE__, __LINE__);                 \
   Xil_AssertStatus = XIL_ASSERT_OCCURRED;        \
   return 0;                                       \
}


#else

#define Xil_AssertVoid(Expression)
#define Xil_AssertVoidAlways()
#define Xil_AssertNonvoid(Expression)
#define Xil_AssertNonvoidAlways()

#endif

/************************** Function Prototypes ******************************/

void Xil_AssertSetCallback(Xil_AssertCallback Routine);

#ifdef __cplusplus
}
#endif

#endif	/* end of protection macro */
/**
* @} End of "addtogroup common_assert_apis".
*/