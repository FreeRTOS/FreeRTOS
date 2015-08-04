/******************************************************************************
*
* Copyright (C) 2009 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xil_testmem.c
*
* Contains the memory test utility functions.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver    Who    Date    Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a hbm  08/25/09 First release
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/
#include "xil_testmem.h"
#include "xil_io.h"
#include "xil_assert.h"

/************************** Constant Definitions ****************************/
/************************** Function Prototypes *****************************/

static u32 RotateLeft(u32 Input, u8 Width);

/* define ROTATE_RIGHT to give access to this functionality */
/* #define ROTATE_RIGHT */
#ifdef ROTATE_RIGHT
static u32 RotateRight(u32 Input, u8 Width);
#endif /* ROTATE_RIGHT */


/*****************************************************************************/
/**
*
* Perform a destructive 32-bit wide memory test.
*
* @param    Addr is a pointer to the region of memory to be tested.
* @param    Words is the length of the block.
* @param    Pattern is the constant used for the constant pattern test, if 0,
*           0xDEADBEEF is used.
* @param    Subtest is the test selected. See xil_testmem.h for possible
*	    values.
*
* @return
*
* - 0 is returned for a pass
* - -1 is returned for a failure
*
* @note
*
* Used for spaces where the address range of the region is smaller than
* the data width. If the memory range is greater than 2 ** Width,
* the patterns used in XIL_TESTMEM_WALKONES and XIL_TESTMEM_WALKZEROS will
* repeat on a boundry of a power of two making it more difficult to detect
* addressing errors. The XIL_TESTMEM_INCREMENT and XIL_TESTMEM_INVERSEADDR
* tests suffer the same problem. Ideally, if large blocks of memory are to be
* tested, break them up into smaller regions of memory to allow the test
* patterns used not to repeat over the region tested.
*
*****************************************************************************/
int Xil_TestMem32(u32 *Addr, u32 Words, u32 Pattern, u8 Subtest)
{
	u32 I;
	u32 J;
	u32 Val;
	u32 FirtVal;
	u32 Word;

	Xil_AssertNonvoid(Words != 0);
	Xil_AssertNonvoid(Subtest <= XIL_TESTMEM_MAXTEST);

	/*
	 * variable initialization
	 */
	Val = XIL_TESTMEM_INIT_VALUE;
	FirtVal = XIL_TESTMEM_INIT_VALUE;

	/*
	 * Select the proper Subtest
	 */
	switch (Subtest) {

	case XIL_TESTMEM_ALLMEMTESTS:

		/* this case executes all of the Subtests */

		/* fall through case statement */

	case XIL_TESTMEM_INCREMENT:

		/*
		 * Fill the memory with incrementing
		 * values starting from 'FirtVal'
		 */
		for (I = 0L; I < Words; I++) {
			Addr[I] = Val;
			Val++;
		}

		/*
		 * Restore the reference 'Val' to the
		 * initial value
		 */
		Val = FirtVal;

		/*
		 * Check every word within the words
		 * of tested memory and compare it
		 * with the incrementing reference
		 * Val
		 */

		for (I = 0L; I < Words; I++) {
			Word = Addr[I];

			if (Word != Val) {
				return -1;
			}

			Val++;
		}


		if (Subtest != XIL_TESTMEM_ALLMEMTESTS) {
			return 0;
		}


		/* end of case 1 */

		/* fall through case statement */

	case XIL_TESTMEM_WALKONES:
		/*
		 * set up to cycle through all possible initial
		 * test Patterns for walking ones test
		 */

		for (J = 0L; J < 32; J++) {
			/*
			 * Generate an initial value for walking ones test
			 * to test for bad data bits
			 */

			Val = 1 << J;

			/*
			 * START walking ones test
			 * Write a one to each data bit indifferent locations
			 */

			for (I = 0L; I < 32; I++) {
				/* write memory location */
				Addr[I] = Val;
				Val = (u32) RotateLeft(Val, 32);
			}

			/*
			 * Restore the reference 'val' to the
			 * initial value
			 */
			Val = 1 << J;

			/* Read the values from each location that was
			 * written */
			for (I = 0L; I < 32; I++) {
				/* read memory location */

				Word = Addr[I];

				if (Word != Val) {
					return -1;
				}

				Val = (u32)RotateLeft(Val, 32);
			}

		}

		if (Subtest != XIL_TESTMEM_ALLMEMTESTS) {
			return 0;
		}

		/* end of case 2 */
		/* fall through case statement */

	case XIL_TESTMEM_WALKZEROS:
		/*
		 * set up to cycle through all possible
		 * initial test Patterns for walking zeros test
		 */

		for (J = 0L; J < 32; J++) {

			/*
			 * Generate an initial value for walking ones test
			 * to test for bad data bits
			 */

			Val = ~(1 << J);

			/*
			 * START walking zeros test
			 * Write a one to each data bit indifferent locations
			 */

			for (I = 0L; I < 32; I++) {
				/* write memory location */
				Addr[I] = Val;
				Val = ~((u32)RotateLeft(~Val, 32));
			}

			/*
			 * Restore the reference 'Val' to the
			 * initial value
			 */

			Val = ~(1 << J);

			/* Read the values from each location that was
			 * written */
			for (I = 0L; I < 32; I++) {
				/* read memory location */
				Word = Addr[I];
				if (Word != Val) {
					return -1;
				}
				Val = ~((u32)RotateLeft(~Val, 32));
			}

		}

		if (Subtest != XIL_TESTMEM_ALLMEMTESTS) {
			return 0;
		}

		/* end of case 3 */

		/* fall through case statement */

	case XIL_TESTMEM_INVERSEADDR:
		/* Fill the memory with inverse of address */
		for (I = 0L; I < Words; I++) {
			/* write memory location */
			Val = (u32) (~((u32) (&Addr[I])));
			Addr[I] = Val;
		}

		/*
		 * Check every word within the words
		 * of tested memory
		 */

		for (I = 0L; I < Words; I++) {
			/* Read the location */
			Word = Addr[I];
			Val = (u32) (~((u32) (&Addr[I])));

			if ((Word ^ Val) != 0x00000000) {
				return -1;
			}
		}

		if (Subtest != XIL_TESTMEM_ALLMEMTESTS) {
			return 0;
		}
		/* end of case 4 */

		/* fall through case statement */

	case XIL_TESTMEM_FIXEDPATTERN:
		/*
		 * Generate an initial value for
		 * memory testing
		 */

		if (Pattern == 0) {
			Val = 0xDEADBEEF;
		}
		else {
			Val = Pattern;
		}

		/*
		 * Fill the memory with fixed Pattern
		 */

		for (I = 0L; I < Words; I++) {
			/* write memory location */
			Addr[I] = Val;
		}

		/*
		 * Check every word within the words
		 * of tested memory and compare it
		 * with the fixed Pattern
		 */

		for (I = 0L; I < Words; I++) {

			/* read memory location */

			Word = Addr[I];
			if (Word != Val) {
				return -1;
			}
		}

		if (Subtest != XIL_TESTMEM_ALLMEMTESTS) {
			return 0;
		}
		/* end of case 5 */

		/* this break is for the prior fall through case statements */

		break;

	default:
		return -1;

	}			/* end of switch */

	/* Successfully passed memory test ! */

	return 0;
}

/*****************************************************************************/
/**
*
* Perform a destructive 16-bit wide memory test.
*
* @param    Addr is a pointer to the region of memory to be tested.
* @param    Words is the length of the block.
* @param    Pattern is the constant used for the constant Pattern test, if 0,
*           0xDEADBEEF is used.
* @param    Subtest is the test selected. See xil_testmem.h for possible
*	    values.
*
* @return
*
* - -1 is returned for a failure
* - 0 is returned for a pass
*
* @note
*
* Used for spaces where the address range of the region is smaller than
* the data width. If the memory range is greater than 2 ** Width,
* the patterns used in XIL_TESTMEM_WALKONES and XIL_TESTMEM_WALKZEROS will
* repeat on a boundry of a power of two making it more difficult to detect
* addressing errors. The XIL_TESTMEM_INCREMENT and XIL_TESTMEM_INVERSEADDR
* tests suffer the same problem. Ideally, if large blocks of memory are to be
* tested, break them up into smaller regions of memory to allow the test
* patterns used not to repeat over the region tested.
*
*****************************************************************************/
int Xil_TestMem16(u16 *Addr, u32 Words, u16 Pattern, u8 Subtest)
{
	u32 I;
	u32 J;
	u16 Val;
	u16 FirtVal;
	u16 Word;

	Xil_AssertNonvoid(Words != 0);
	Xil_AssertNonvoid(Subtest <= XIL_TESTMEM_MAXTEST);

	/*
	 * variable initialization
	 */
	Val = XIL_TESTMEM_INIT_VALUE;
	FirtVal = XIL_TESTMEM_INIT_VALUE;

	/*
	 * selectthe proper Subtest(s)
	 */

	switch (Subtest) {

	case XIL_TESTMEM_ALLMEMTESTS:

		/* this case executes all of the Subtests */

		/* fall through case statement */

	case XIL_TESTMEM_INCREMENT:
		/*
		 * Fill the memory with incrementing
		 * values starting from 'FirtVal'
		 */
		for (I = 0L; I < Words; I++) {
			/* write memory location */
			Addr[I] = Val;
			Val++;
		}
		/*
		 * Restore the reference 'Val' to the
		 * initial value
		 */
		Val = FirtVal;

		/*
		 * Check every word within the words
		 * of tested memory and compare it
		 * with the incrementing reference val
		 */

		for (I = 0L; I < Words; I++) {
			/* read memory location */
			Word = Addr[I];
			if (Word != Val) {
				return -1;
			}
			Val++;
		}
		if (Subtest != XIL_TESTMEM_ALLMEMTESTS) {
			return 0;
		}

		/* end of case 1 */
		/* fall through case statement */

	case XIL_TESTMEM_WALKONES:
		/*
		 * set up to cycle through all possible initial test
		 * Patterns for walking ones test
		 */

		for (J = 0L; J < 16; J++) {
			/*
			 * Generate an initial value for walking ones test
			 * to test for bad data bits
			 */

			Val = 1 << J;
			/*
			 * START walking ones test
			 * Write a one to each data bit indifferent locations
			 */

			for (I = 0L; I < 16; I++) {
				/* write memory location */
				Addr[I] = Val;
				Val = (u16)RotateLeft(Val, 16);
			}
			/*
			 * Restore the reference 'Val' to the
			 * initial value
			 */
			Val = 1 << J;
			/* Read the values from each location that was written */
			for (I = 0L; I < 16; I++) {
				/* read memory location */
				Word = Addr[I];
				if (Word != Val) {
					return -1;
				}
				Val = (u16)RotateLeft(Val, 16);
			}

		}
		if (Subtest != XIL_TESTMEM_ALLMEMTESTS) {
			return 0;
		}
		/* end of case 2 */
		/* fall through case statement */

	case XIL_TESTMEM_WALKZEROS:
		/*
		 * set up to cycle through all possible initial
		 * test Patterns for walking zeros test
		 */

		for (J = 0L; J < 16; J++) {
			/*
			 * Generate an initial value for walking ones
			 * test to test for bad
			 * data bits
			 */

			Val = ~(1 << J);
			/*
			 * START walking zeros test
			 * Write a one to each data bit indifferent locations
			 */

			for (I = 0L; I < 16; I++) {
				/* write memory location */
				Addr[I] = Val;
				Val = ~((u16)RotateLeft(~Val, 16));
			}
			/*
			 * Restore the reference 'Val' to the
			 * initial value
			 */
			Val = ~(1 << J);
			/* Read the values from each location that was written */
			for (I = 0L; I < 16; I++) {
				/* read memory location */
				Word = Addr[I];
				if (Word != Val) {
					return -1;
				}
				Val = ~((u16)RotateLeft(~Val, 16));
			}

		}
		if (Subtest != XIL_TESTMEM_ALLMEMTESTS) {
			return 0;
		}
		/* end of case 3 */
		/* fall through case statement */

	case XIL_TESTMEM_INVERSEADDR:
		/* Fill the memory with inverse of address */
		for (I = 0L; I < Words; I++) {
			/* write memory location */
			Val = (u16) (~((u32) (&Addr[I])));
			Addr[I] = Val;
		}
		/*
		 * Check every word within the words
		 * of tested memory
		 */

		for (I = 0L; I < Words; I++) {
			/* read memory location */
			Word = Addr[I];
			Val = (u16) (~((u32) (&Addr[I])));
			if ((Word ^ Val) != 0x0000) {
				return -1;
			}
		}
		if (Subtest != XIL_TESTMEM_ALLMEMTESTS) {
			return 0;
		}
		/* end of case 4 */
		/* fall through case statement */

	case XIL_TESTMEM_FIXEDPATTERN:
		/*
		 * Generate an initial value for
		 * memory testing
		 */
		if (Pattern == 0) {
			Val = 0xDEAD;
		}
		else {
			Val = Pattern;
		}

		/*
		 * Fill the memory with fixed pattern
		 */

		for (I = 0L; I < Words; I++) {
			/* write memory location */
			Addr[I] = Val;
		}

		/*
		 * Check every word within the words
		 * of tested memory and compare it
		 * with the fixed pattern
		 */

		for (I = 0L; I < Words; I++) {
			/* read memory location */
			Word = Addr[I];
			if (Word != Val) {
				return -1;
			}
		}
		if (Subtest != XIL_TESTMEM_ALLMEMTESTS) {
			return 0;
		}
		/* end of case 5 */
		/* this break is for the prior fall through case statements */

		break;

	default:
		return -1;

	}			/* end of switch */

	/* Successfully passed memory test ! */

	return 0;
}


/*****************************************************************************/
/**
*
* Perform a destructive 8-bit wide memory test.
*
* @param    Addr is a pointer to the region of memory to be tested.
* @param    Words is the length of the block.
* @param    Pattern is the constant used for the constant pattern test, if 0,
*           0xDEADBEEF is used.
* @param    Subtest is the test selected. See xil_testmem.h for possible
*	    values.
*
* @return
*
* - -1 is returned for a failure
* - 0 is returned for a pass
*
* @note
*
* Used for spaces where the address range of the region is smaller than
* the data width. If the memory range is greater than 2 ** Width,
* the patterns used in XIL_TESTMEM_WALKONES and XIL_TESTMEM_WALKZEROS will
* repeat on a boundry of a power of two making it more difficult to detect
* addressing errors. The XIL_TESTMEM_INCREMENT and XIL_TESTMEM_INVERSEADDR
* tests suffer the same problem. Ideally, if large blocks of memory are to be
* tested, break them up into smaller regions of memory to allow the test
* patterns used not to repeat over the region tested.
*
*****************************************************************************/
int Xil_TestMem8(u8 *Addr, u32 Words, u8 Pattern, u8 Subtest)
{
	u32 I;
	u32 J;
	u8 Val;
	u8 FirtVal;
	u8 Word;

	Xil_AssertNonvoid(Words != 0);
	Xil_AssertNonvoid(Subtest <= XIL_TESTMEM_MAXTEST);

	/*
	 * variable initialization
	 */
	Val = XIL_TESTMEM_INIT_VALUE;
	FirtVal = XIL_TESTMEM_INIT_VALUE;

	/*
	 * select the proper Subtest(s)
	 */

	switch (Subtest) {

	case XIL_TESTMEM_ALLMEMTESTS:
		/* this case executes all of the Subtests */
		/* fall through case statement */

	case XIL_TESTMEM_INCREMENT:
		/*
		 * Fill the memory with incrementing
		 * values starting from 'FirtVal'
		 */
		for (I = 0L; I < Words; I++) {
			/* write memory location */
			Addr[I] = Val;
			Val++;
		}
		/*
		 * Restore the reference 'Val' to the
		 * initial value
		 */
		Val = FirtVal;
		/*
		 * Check every word within the words
		 * of tested memory and compare it
		 * with the incrementing reference
		 * Val
		 */

		for (I = 0L; I < Words; I++) {
			/* read memory location */
			Word = Addr[I];
			if (Word != Val) {
				return -1;
			}
			Val++;
		}

		if (Subtest != XIL_TESTMEM_ALLMEMTESTS) {
			return 0;
		}
		/* end of case 1 */

		/* fall through case statement */

	case XIL_TESTMEM_WALKONES:
		/*
		 * set up to cycle through all possible initial
		 * test Patterns for walking ones test
		 */

		for (J = 0L; J < 8; J++) {
			/*
			 * Generate an initial value for walking ones test
			 * to test for bad data bits
			 */
			Val = 1 << J;
			/*
			 * START walking ones test
			 * Write a one to each data bit indifferent locations
			 */
			for (I = 0L; I < 8; I++) {
				/* write memory location */
				Addr[I] = Val;
				Val = (u8)RotateLeft(Val, 8);
			}
			/*
			 * Restore the reference 'Val' to the
			 * initial value
			 */
			Val = 1 << J;
			/* Read the values from each location that was written */
			for (I = 0L; I < 8; I++) {
				/* read memory location */
				Word = Addr[I];
				if (Word != Val) {
					return -1;
				}
				Val = (u8)RotateLeft(Val, 8);
			}
		}

		if (Subtest != XIL_TESTMEM_ALLMEMTESTS) {
			return 0;
		}
		/* end of case 2 */
		/* fall through case statement */

	case XIL_TESTMEM_WALKZEROS:
		/*
		 * set up to cycle through all possible initial test
		 * Patterns for walking zeros test
		 */

		for (J = 0L; J < 8; J++) {
			/*
			 * Generate an initial value for walking ones test to test
			 * for bad data bits
			 */
			Val = ~(1 << J);
			/*
			 * START walking zeros test
			 * Write a one to each data bit indifferent locations
			 */
			for (I = 0L; I < 8; I++) {
				/* write memory location */
				Addr[I] = Val;
				Val = ~((u8)RotateLeft(~Val, 8));
			}
			/*
			 * Restore the reference 'Val' to the
			 * initial value
			 */
			Val = ~(1 << J);
			/* Read the values from each location that was written */
			for (I = 0L; I < 8; I++) {
				/* read memory location */
				Word = Addr[I];
				if (Word != Val) {
					return -1;
				}

				Val = ~((u8)RotateLeft(~Val, 8));
			}
		}

		if (Subtest != XIL_TESTMEM_ALLMEMTESTS) {
			return 0;
		}
		/* end of case 3 */
		/* fall through case statement */

	case XIL_TESTMEM_INVERSEADDR:
		/* Fill the memory with inverse of address */
		for (I = 0L; I < Words; I++) {
			/* write memory location */
			Val = (u8) (~((u32) (&Addr[I])));
			Addr[I] = Val;
		}

		/*
		 * Check every word within the words
		 * of tested memory
		 */

		for (I = 0L; I < Words; I++) {
			/* read memory location */
			Word = Addr[I];
			Val = (u8) (~((u32) (&Addr[I])));
			if ((Word ^ Val) != 0x00) {
				return -1;
			}
		}
		if (Subtest != XIL_TESTMEM_ALLMEMTESTS) {
			return 0;
		}
		/* end of case 4 */
		/* fall through case statement */

	case XIL_TESTMEM_FIXEDPATTERN:
		/*
		 * Generate an initial value for
		 * memory testing
		 */

		if (Pattern == 0) {
			Val = 0xA5;
		}
		else {
			Val = Pattern;
		}
		/*
		 * Fill the memory with fixed Pattern
		 */
		for (I = 0L; I < Words; I++) {
			/* write memory location */
			Addr[I] = Val;
		}
		/*
		 * Check every word within the words
		 * of tested memory and compare it
		 * with the fixed Pattern
		 */

		for (I = 0L; I < Words; I++) {
			/* read memory location */
			Word = Addr[I];
			if (Word != Val) {
				return -1;
			}
		}

		if (Subtest != XIL_TESTMEM_ALLMEMTESTS) {
			return 0;
		}

		/* end of case 5 */

		/* this break is for the prior fall through case statements */

		break;

	default:
		return -1;

	}	/* end of switch */

	/* Successfully passed memory test ! */

	return 0;
}


/*****************************************************************************/
/**
*
* Rotates the provided value to the left one bit position
*
* @param    Input is value to be rotated to the left
* @param    Width is the number of bits in the input data
*
* @return
*
* The resulting unsigned long value of the rotate left
*
* @note
*
* None.
*
*****************************************************************************/
static u32 RotateLeft(u32 Input, u8 Width)
{
	u32 Msb;
	u32 ReturnVal;
	u32 WidthMask;
	u32 MsbMask;

	/*
	 * set up the WidthMask and the MsbMask
	 */

	MsbMask = 1 << (Width - 1);

	WidthMask = (MsbMask << 1) - 1;

	/*
	 * set the Width of the Input to the correct width
	 */

	Input = Input & WidthMask;

	Msb = Input & MsbMask;

	ReturnVal = Input << 1;

	if (Msb != 0x00000000) {
		ReturnVal = ReturnVal | 0x00000001;
	}

	ReturnVal = ReturnVal & WidthMask;

	return ReturnVal;

}

#ifdef ROTATE_RIGHT
/*****************************************************************************/
/**
*
* Rotates the provided value to the right one bit position
*
* @param    Input is value to be rotated to the right
* @param    Width is the number of bits in the input data
*
* @return
*
* The resulting u32 value of the rotate right
*
* @note
*
* None.
*
*****************************************************************************/
static u32 RotateRight(u32 Input, u8 Width)
{
	u32 Lsb;
	u32 ReturnVal;
	u32 WidthMask;
	u32 MsbMask;

	/*
	 * set up the WidthMask and the MsbMask
	 */

	MsbMask = 1 << (Width - 1);

	WidthMask = (MsbMask << 1) - 1;

	/*
	 * set the width of the input to the correct width
	 */

	Input = Input & WidthMask;

	ReturnVal = Input >> 1;

	Lsb = Input & 0x00000001;

	if (Lsb != 0x00000000) {
		ReturnVal = ReturnVal | MsbMask;
	}

	ReturnVal = ReturnVal & WidthMask;

	return ReturnVal;

}
#endif /* ROTATE_RIGHT */

