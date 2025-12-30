/*
 * Some or all of this work - Copyright (c) 2006 - 2021, Intel Corp.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 * Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 * Neither the name of Intel Corporation nor the names of its contributors
 * may be used to endorse or promote products derived from this software
 * without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * Test of Impllicit Return
 *
 * The last operation of Methods is a standalone Return.
 */

Name(z137, 137)

Method(mf6f,, Serialized)
{
	Name(fl00, 0)
	Name(i000, 0xabcd0000)
	Name(i001, 0xabcd0001)

	Method(m000)
	{
		Store(0xabcd0002, i001)
		if (fl00) {
			Store(0xdddd0000, i001)
			Return (0)
		}
		Return
	}

	Method(m001)
	{
		if (fl00) {
			Store(0xdddd0001, i001)
			Return (0)
		}
		Store(0xabcd0003, i001)
		Return
	}

	Method(m002, 1)
	{
		if (fl00) {
			Store(0xdddd0002, i001)
			Return (0)
		}
		if (fl00) {
			Return (0)
		}
		if (arg0) {
			Store(0xabcd0004, i001)
			Return
		}
	}

	Method(m003, 1)
	{
		if (fl00) {
			Store(0xdddd0003, i001)
			Return (0)
		}
		if (fl00) {
			Return (0)
		}
		if (arg0) {
			Store(0xabcd0005, i001)
		} else {
			Store(0xabcd0006, i001)
		}
		Return
	}

	Method(m004, 1)
	{
		if (fl00) {
			Return (0)
		}

		switch (arg0) {
			case (0) {
				Store(0xabcd0007, i001)
			}
			case (0x12345678) {
				Store(0xabcd0008, i001)
			}
			default {
				Store(0xabcd0009, i001)
			}
		}
		Return
	}

	Method(m005)
	{
		if (fl00) {
			Return (0)
		}

		While (1) {
			Store(0xabcd000a, i001)
			Break
		}
		Return
	}

	Method(m006)
	{
		if (fl00) {
			Return (0)
		}

		Store(0xabcd000b, i001)
		While (1) {
			Break
		}
		Return
	}

	Method(m007,, Serialized)
	{
		Name(i000, 0)
		Name(num, 0)
		Name(lpN0, 0)
		Name(lpC0, 0)

		Store(10, num)

		Store(num, lpN0)
		Store(0, lpC0)

		if (fl00) {
			Return (0)
		}

		While (lpN0) {
			if (i000) {
				Break
			}
			Decrement(lpN0)
			Increment(lpC0)
			Store(1, i000)
			Store(0xabcd000c, i001)
			Continue
		}
		Return
	}

	Method(m008)
	{
		Method(m000)
		{
			Store(0xabcd000d, i001)
		}

		if (fl00) {
			Return (0)
		}

		m000()

		Return
	}


	// m000

	Store(0xabcd9000, i000)

	CH03("", z137, 0x200, __LINE__, 0)

	Store(m000(), i000)

	if (SLCK) {
		CH03("", z137, 0x201, __LINE__, 0)
		if (LNotEqual(i000, 0)) {
			err("", z137, __LINE__, 0, 0, i000, 0)
		}
	} else {
		CH03("", z137, 0x203, __LINE__, 0)
	}

	// m001

	Store(0xabcd9001, i000)

	CH03("", z137, 0x204, __LINE__, 0)

	Store(m001(), i000)

	if (SLCK) {
		CH03("", z137, 0x205, __LINE__, 0)
		if (LNotEqual(i000, 0)) {
			err("", z137, __LINE__, 0, 0, i000, 0)
		}
	} else {
		CH03("", z137, 0x207, __LINE__, 0)
	}

	// m002

	Store(0xabcd9002, i000)

	CH03("", z137, 0x208, __LINE__, 0)

	Store(m002(1), i000)

	if (SLCK) {
		CH03("", z137, 0x209, __LINE__, 0)
		if (LNotEqual(i000, 0)) {
			err("", z137, __LINE__, 0, 0, i000, 0)
		}
	} else {
		CH03("", z137, 0x20b, __LINE__, 0)
	}

	// m003

	Store(0xabcd9003, i000)

	CH03("", z137, 0x20c, __LINE__, 0)

	Store(m003(0), i000)

	if (SLCK) {
		CH03("", z137, 0x20d, __LINE__, 0)
		if (LNotEqual(i000, 0)) {
			err("", z137, __LINE__, 0, 0, i000, 0)
		}
	} else {
		CH03("", z137, 0x20f, __LINE__, 0)
	}

	// m004(0)

	Store(0xabcd9004, i000)

	CH03("", z137, 0x210, __LINE__, 0)

	Store(m004(0), i000)

	if (SLCK) {
		CH03("", z137, 0x211, __LINE__, 0)
		if (LNotEqual(i000, 0)) {
			err("", z137, __LINE__, 0, 0, i000, 0)
		}
	} else {
		CH03("", z137, 0x213, __LINE__, 0)
	}

	// m004(0x12345678)

	Store(0xabcd9005, i000)

	CH03("", z137, 0x214, __LINE__, 0)

	Store(m004(0x12345678), i000)

	if (SLCK) {
		CH03("", z137, 0x215, __LINE__, 0)
		if (LNotEqual(i000, 0)) {
			err("", z137, __LINE__, 0, 0, i000, 0)
		}
	} else {
		CH03("", z137, 0x217, __LINE__, 0)
	}

	// m004(Default)

	Store(0xabcd9006, i000)

	CH03("", z137, 0x218, __LINE__, 0)

	Store(m004(1111), i000)

	if (SLCK) {
		CH03("", z137, 0x219, __LINE__, 0)
		if (LNotEqual(i000, 0)) {
			err("", z137, __LINE__, 0, 0, i000, 0)
		}
	} else {
		CH03("", z137, 0x21b, __LINE__, 0)
	}

	// m005

	Store(0xabcd9007, i000)

	CH03("", z137, 0x21c, __LINE__, 0)

	Store(m005(), i000)

	if (SLCK) {
		CH03("", z137, 0x21d, __LINE__, 0)
		if (LNotEqual(i000, 0)) {
			err("", z137, __LINE__, 0, 0, i000, 0)
		}
	} else {
		CH03("", z137, 0x21f, __LINE__, 0)
	}

	// m006

	Store(0xabcd9008, i000)

	CH03("", z137, 0x220, __LINE__, 0)

	Store(m006(), i000)

	if (SLCK) {
		CH03("", z137, 0x221, __LINE__, 0)
		if (LNotEqual(i000, 0)) {
			err("", z137, __LINE__, 0, 0, i000, 0)
		}
	} else {
		CH03("", z137, 0x223, __LINE__, 0)
	}

	// m007

	Store(0xabcd9009, i000)

	CH03("", z137, 0x224, __LINE__, 0)

	Store(m007(), i000)

	if (SLCK) {
		CH03("", z137, 0x225, __LINE__, 0)
		if (LNotEqual(i000, 0)) {
			err("", z137, __LINE__, 0, 0, i000, 0)
		}
	} else {
		CH03("", z137, 0x227, __LINE__, 0)
	}

	// m008

	Store(0xabcd900a, i000)

	CH03("", z137, 0x228, __LINE__, 0)

	Store(m008(), i000)

	if (SLCK) {
		CH03("", z137, 0x229, __LINE__, 0)
		if (LNotEqual(i000, 0)) {
			err("", z137, __LINE__, 0, 0, i000, 0)
		}
	} else {
		CH03("", z137, 0x22b, __LINE__, 0)
	}
}
