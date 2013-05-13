/*******************************************************************************
 * (c) Copyright 2008-2013 Microsemi SoC Products Group. All rights reserved.
 * 
 * SVN $Revision: 5274 $
 * SVN $Date: 2013-03-22 13:18:44 +0000 (Fri, 22 Mar 2013) $
 */
#ifndef HAL_ASSERT_HEADER
#define HAL_ASSERT_HEADER

#include "../CMSIS/mss_assert.h"

#if defined(NDEBUG)
/***************************************************************************//**
 * HAL_ASSERT() is defined out when the NDEBUG symbol is used.
 ******************************************************************************/
#define HAL_ASSERT(CHECK)

#else
/***************************************************************************//**
 * Default behaviour for HAL_ASSERT() macro:
 *------------------------------------------------------------------------------
 * Using the HAL_ASSERT() macro is the same as directly using the SmartFusion2
 * CMSIS ASSERT() macro. The behaviour is toolchain specific and project
 * setting specific.
 ******************************************************************************/
#define HAL_ASSERT(CHECK)     ASSERT(CHECK);

#endif  /* NDEBUG */

#endif  /* HAL_ASSERT_HEADER */
