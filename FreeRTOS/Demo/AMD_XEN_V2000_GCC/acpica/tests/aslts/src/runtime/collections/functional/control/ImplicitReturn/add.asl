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
 * The last operation of Methods is Add.
 */

Name(z136, 136)

Method(mf71,, Serialized)
{
	Name(fl00, 0)
	Name(i000, 0xabcd0000)
	Name(i001, 0)

	Method(m000)
	{
		Store(Add(0xabcd0002, i001), Local1)
		if (fl00) {
			Store(0xdddd0000, i001)
			Return (0)
		}
	}

	Method(m001)
	{
		if (fl00) {
			Store(0xdddd0001, i001)
			Return (0)
		}
		Store(Add(0xabcd0003, i001), Local1)
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
			Store(Add(0xabcd0004, i001), Local1)
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
			Store(Add(0xabcd0005, i001), Local1)
		} else {
			Store(Add(0xabcd0006, i001), Local1)
		}
	}

	Method(m004, 1)
	{
		if (fl00) {
			Return (0)
		}

		switch (arg0) {
			case (0) {
				Store(Add(0xabcd0007, i001), Local1)
			}
			case (0x12345678) {
				Store(Add(0xabcd0008, i001), Local1)
			}
			default {
				Store(Add(0xabcd0009, i001), Local1)
			}
		}
	}

	Method(m005)
	{
		if (fl00) {
			Return (0)
		}

		While (1) {
			Store(Add(0xabcd000a, i001), Local1)
			Break
		}
	}

	Method(m006)
	{
		if (fl00) {
			Return (0)
		}

		Store(Add(0xabcd000b, i001), Local1)
		While (0xabcd0003) {
			Break
		}
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
			Store(0xabcd0001, i000)
			Store(Add(0xabcd000c, i001), Local1)
			Continue
		}
	}

	Method(m008)
	{
		Method(m000)
		{
			Store(Add(0xabcd000d, i001), Local1)
		}

		if (fl00) {
			Return (0)
		}

		m000()
	}


	// m000

	Store(0xabcd9000, i000)

	CH03("", z136, 0x100, __LINE__, 0)

	Store(m000(), i000)

	if (SLCK) {
		CH03("", z136, 0x101, __LINE__, 0)
		if (y901) {
			Store(0, Local0)
		} else {
			Store(0xabcd0002, Local0)
		}
		if (LNotEqual(i000, Local0)) {
			err("", z136, __LINE__, 0, 0, i000, Local0)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m001

	Store(0xabcd9001, i000)

	CH03("", z136, 0x104, __LINE__, 0)

	Store(m001(), i000)

	if (SLCK) {
		CH03("", z136, 0x105, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0003)) {
			err("", z136, __LINE__, 0, 0, i000, 0xabcd0003)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m002

	Store(0xabcd9002, i000)

	CH03("", z136, 0x108, __LINE__, 0)

	Store(m002(1), i000)

	if (SLCK) {
		CH03("", z136, 0x109, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0004)) {
			err("", z136, __LINE__, 0, 0, i000, 0xabcd0004)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m003

	Store(0xabcd9003, i000)

	CH03("", z136, 0x10c, __LINE__, 0)

	Store(m003(0), i000)

	if (SLCK) {
		CH03("", z136, 0x10d, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0006)) {
			err("", z136, __LINE__, 0, 0, i000, 0xabcd0006)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m004(0)

	Store(0xabcd9004, i000)

	CH03("", z136, 0x110, __LINE__, 0)

	Store(m004(0), i000)

	if (SLCK) {
		CH03("", z136, 0x111, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0007)) {
			err("", z136, __LINE__, 0, 0, i000, 0xabcd0007)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m004(0x12345678)

	Store(0xabcd9005, i000)

	CH03("", z136, 0x114, __LINE__, 0)

	Store(m004(0x12345678), i000)

	if (SLCK) {
		CH03("", z136, 0x115, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0008)) {
			err("", z136, __LINE__, 0, 0, i000, 0xabcd0008)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m004(Default)

	Store(0xabcd9006, i000)

	CH03("", z136, 0x118, __LINE__, 0)

	Store(m004(1111), i000)

	if (SLCK) {
		CH03("", z136, 0x119, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0009)) {
			err("", z136, __LINE__, 0, 0, i000, 0xabcd0009)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m005

	Store(0xabcd9007, i000)

	CH03("", z136, 0x11c, __LINE__, 0)

	Store(m005(), i000)

	if (SLCK) {
		CH03("", z136, 0x11d, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd000a)) {
			err("", z136, __LINE__, 0, 0, i000, 0xabcd000a)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m006

	Store(0xabcd9008, i000)

	CH03("", z136, 0x120, __LINE__, 0)

	Store(m006(), i000)

	if (SLCK) {
		CH03("", z136, 0x121, __LINE__, 0)
		if (y901) {
			Store(0xabcd0003, Local0)
		} else {
			Store(0xabcd000b, Local0)
		}
		if (LNotEqual(i000, Local0)) {
			err("", z136, __LINE__, 0, 0, i000, Local0)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m007

	Store(0xabcd9009, i000)

	CH03("", z136, 0x124, __LINE__, 0)

	Store(m007(), i000)

	if (SLCK) {
		CH03("", z136, 0x125, __LINE__, 0)
		if (y901) {
			Store(0xabcd0001, Local0)
		} else {
			Store(0xabcd000c, Local0)
		}
		if (LNotEqual(i000, Local0)) {
			err("", z136, __LINE__, 0, 0, i000, Local0)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m008

	Store(0xabcd900a, i000)

	CH03("", z136, 0x128, __LINE__, 0)

	Store(m008(), i000)

	if (SLCK) {
		CH03("", z136, 0x129, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd000d)) {
			err("", z136, __LINE__, 0, 0, i000, 0xabcd000d)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}
}

// Implements mf71 where i001 relocated with Local0
// to extend implicit return conditions checked
Method(mff0,, Serialized)
{
	Name(fl00, 0)
	Name(i000, 0xabcd0000)

	Method(m000)
	{
		Store(0, Local0)

		Store(Add(0xabcd0002, Local0), Local1)
		if (fl00) {
			Store(0xdddd0000, Local0)
			Return (0)
		}
	}

	Method(m001)
	{
		Store(0, Local0)

		if (fl00) {
			Store(0xdddd0001, Local0)
			Return (0)
		}
		Store(Add(0xabcd0003, Local0), Local1)
	}

	Method(m002, 1)
	{
		Store(0, Local0)

		if (fl00) {
			Store(0xdddd0002, Local0)
			Return (0)
		}
		if (fl00) {
			Return (0)
		}
		if (arg0) {
			Store(Add(0xabcd0004, Local0), Local1)
		}
	}

	Method(m003, 1)
	{
		Store(0, Local0)

		if (fl00) {
			Store(0xdddd0003, Local0)
			Return (0)
		}
		if (fl00) {
			Return (0)
		}
		if (arg0) {
			Store(Add(0xabcd0005, Local0), Local1)
		} else {
			Store(Add(0xabcd0006, Local0), Local1)
		}
	}

	Method(m004, 1)
	{
		Store(0, Local0)

		if (fl00) {
			Return (0)
		}

		switch (arg0) {
			case (0) {
				Store(Add(0xabcd0007, Local0), Local1)
			}
			case (0x12345678) {
				Store(Add(0xabcd0008, Local0), Local1)
			}
			default {
				Store(Add(0xabcd0009, Local0), Local1)
			}
		}
	}

	Method(m005)
	{
		Store(0, Local0)

		if (fl00) {
			Return (0)
		}

		While (1) {
			Store(Add(0xabcd000a, Local0), Local1)
			Break
		}
	}

	Method(m006)
	{
		Store(0, Local0)

		if (fl00) {
			Return (0)
		}

		Store(Add(0xabcd000b, Local0), Local1)
		While (0xabcd0002) {
			Break
		}
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

		Store(0, Local0)

		While (lpN0) {
			if (i000) {
				Break
			}
			Decrement(lpN0)
			Increment(lpC0)
			Store(0xabcd0005, i000)
			Store(Add(0xabcd000c, Local0), Local1)
			Continue
		}
	}

	Method(m008)
	{
		Method(m000)
		{
			Store(0, Local0)

			Store(Add(0xabcd000d, Local0), Local1)
		}

		if (fl00) {
			Return (0)
		}

		m000()
	}

	Method(m009)
	{
		Method(m000)
		{
			Store(0, Local0)

			Store(Add(Local0, 0xabcd000e, Local0), Local1)
			m001(Local0)
		}

		Method(m001, 1)
		{
			Store(arg0, Local0)
		}

		if (fl00) {
			Return (0)
		}

		m000()
	}

	// m000

	Store(0xabcd9000, i000)

	CH03("", z136, 0x12c, __LINE__, 0)

	Store(m000(), i000)

	if (SLCK) {
		CH03("", z136, 0x12d, __LINE__, 0)
		if (y901) {
			Store(0, Local0)
		} else {
			Store(0xabcd0002, Local0)
		}
		if (LNotEqual(i000, Local0)) {
			err("", z136, __LINE__, 0, 0, i000, Local0)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m001

	Store(0xabcd9001, i000)

	CH03("", z136, 0x130, __LINE__, 0)

	Store(m001(), i000)

	if (SLCK) {
		CH03("", z136, 0x131, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0003)) {
			err("", z136, __LINE__, 0, 0, i000, 0xabcd0003)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m002

	Store(0xabcd9002, i000)

	CH03("", z136, 0x134, __LINE__, 0)

	Store(m002(1), i000)

	if (SLCK) {
		CH03("", z136, 0x135, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0004)) {
			err("", z136, __LINE__, 0, 0, i000, 0xabcd0004)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m003

	Store(0xabcd9003, i000)

	CH03("", z136, 0x138, __LINE__, 0)

	Store(m003(0), i000)

	if (SLCK) {
		CH03("", z136, 0x139, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0006)) {
			err("", z136, __LINE__, 0, 0, i000, 0xabcd0006)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m004(0)

	Store(0xabcd9004, i000)

	CH03("", z136, 0x13b, __LINE__, 0)

	Store(m004(0), i000)

	if (SLCK) {
		CH03("", z136, 0x13c, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0007)) {
			err("", z136, __LINE__, 0, 0, i000, 0xabcd0007)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m004(0x12345678)

	Store(0xabcd9005, i000)

	CH03("", z136, 0x13f, __LINE__, 0)

	Store(m004(0x12345678), i000)

	if (SLCK) {
		CH03("", z136, 0x140, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0008)) {
			err("", z136, __LINE__, 0, 0, i000, 0xabcd0008)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m004(Default)

	Store(0xabcd9006, i000)

	CH03("", z136, 0x143, __LINE__, 0)

	Store(m004(1111), i000)

	if (SLCK) {
		CH03("", z136, 0x144, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0009)) {
			err("", z136, __LINE__, 0, 0, i000, 0xabcd0009)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m005

	Store(0xabcd9007, i000)

	CH03("", z136, 0x147, __LINE__, 0)

	Store(m005(), i000)

	if (SLCK) {
		CH03("", z136, 0x148, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd000a)) {
			err("", z136, __LINE__, 0, 0, i000, 0xabcd000a)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m006

	Store(0xabcd9008, i000)

	CH03("", z136, 0x14b, __LINE__, 0)

	Store(m006(), i000)

	if (SLCK) {
		CH03("", z136, 0x14c, __LINE__, 0)
		if (y901) {
			Store(0xabcd0002, Local0)
		} else {
			Store(0xabcd000b, Local0)
		}
		if (LNotEqual(i000, Local0)) {
			err("", z136, __LINE__, 0, 0, i000, Local0)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m007

	Store(0xabcd9009, i000)

	CH03("", z136, 0x14f, __LINE__, 0)

	Store(m007(), i000)

	if (SLCK) {
		CH03("", z136, 0x150, __LINE__, 0)
		if (y901) {
			Store(0xabcd0005, Local0)
		} else {
			Store(0xabcd000c, Local0)
		}
		if (LNotEqual(i000, Local0)) {
			err("", z136, __LINE__, 0, 0, i000, Local0)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m008

	Store(0xabcd900a, i000)

	CH03("", z136, 0x153, __LINE__, 0)

	Store(m008(), i000)

	if (SLCK) {
		CH03("", z136, 0x154, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd000d)) {
			err("", z136, __LINE__, 0, 0, i000, 0xabcd000d)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

	// m009

	Store(0xabcd900b, i000)

	CH03("", z136, 0x157, __LINE__, 0)

	Store(m009(), i000)

	if (SLCK) {
		CH03("", z136, 0x158, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd000e)) {
			err("", z136, __LINE__, 0, 0, i000, 0xabcd000e)
		}
	} else {
		CH04("", 0, 0xff, z136, __LINE__, 0, 0)
	}

}
