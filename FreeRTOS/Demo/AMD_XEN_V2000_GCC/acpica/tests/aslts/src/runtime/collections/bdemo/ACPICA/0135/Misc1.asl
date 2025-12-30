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
 * Check self-references
 *
 * 0xE Outstanding allocations because of
 * AcpiExec doesn't run the unload of the table have been processed.
 * All they are caused by call to SRMT Method.
 *
 * Outstanding: 0xE allocations after execution.
 */

Method(mfcb,, Serialized)
{
	Name(p000, Package(16) {})

	Name(num, 8)		// half-size of Package
	Name(i000, 0xabcd0000)	// value of the first element of Package

	/* 1 */

	Store(Index(p000, 0), Index(p000, 8))
	Store(Index(p000, 1), Index(p000, 9))
	Store(Index(p000, 2), Index(p000, 10))
	Store(Index(p000, 3), Index(p000, 11))
	Store(Index(p000, 4), Index(p000, 12))
	Store(Index(p000, 5), Index(p000, 13))
	Store(Index(p000, 6), Index(p000, 14))
	Store(Index(p000, 7), Index(p000, 15))
	mfc7(p000, 0, num, i000)
	mfcc(p000, num, num, i000, 0, 0x003)

	/* 2 */

	mfcd(p000, 0, num, 0)
	Store(Index(p000, 0), Index(p000, 8))
	Store(Index(p000, 0), Index(p000, 9))
	Store(Index(p000, 0), Index(p000, 10))
	Store(Index(p000, 0), Index(p000, 11))
	Store(Index(p000, 0), Index(p000, 12))
	Store(Index(p000, 0), Index(p000, 13))
	Store(Index(p000, 0), Index(p000, 14))
	Store(Index(p000, 0), Index(p000, 15))
	Store(0xabcd0100, i000)
	Store(i000, Index(p000, 0))
	mfce(p000, num, num, i000, 0, 0x004)

	/* 3 */

	mfcd(p000, 0, num, 0)
	mfc7(p000, 0, num, 0xabcd0200)
	Store(Index(p000, 0), Index(p000, 8))
	Store(Index(p000, 1), Index(p000, 8))
	Store(Index(p000, 2), Index(p000, 8))
	Store(Index(p000, 3), Index(p000, 8))
	Store(Index(p000, 4), Index(p000, 8))
	Store(Index(p000, 5), Index(p000, 8))
	Store(Index(p000, 6), Index(p000, 8))
	Store(Index(p000, 7), Index(p000, 8))
	mfce(p000, num, 1, 0xabcd0207, 0, 0x005)

	/* 4 */

	mfcd(p000, 0, num, 0)
	mfc7(p000, 0, num, 0xabcd0300)
	Store(Index(p000, 1), Index(p000, 8))
	Store(Index(p000, 1), Index(p000, 8))
	Store(Index(p000, 1), Index(p000, 8))
	Store(Index(p000, 1), Index(p000, 8))
	Store(Index(p000, 1), Index(p000, 8))
	Store(Index(p000, 1), Index(p000, 8))
	Store(Index(p000, 1), Index(p000, 8))
	Store(Index(p000, 1), Index(p000, 8))
	mfce(p000, num, 1, 0xabcd0301, 0, 0x006)
}

/*
 * LocalX involved
 */
Method(mfcf,, Serialized)
{
	Name(p000, Package(16) {})

	Store(Index(p000, 0), Local0)
	Store(Local0, Index(p000, 1))
	Store(0xabcd0000, Index(p000, 0))
	Store(Index(p000, 1), Local0)
	Store(DerefOf(Local0), Local1)
	Store(DerefOf(Local1), Local0)

	if (LNotEqual(Local0, 0xabcd0000)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 0xabcd0000)
	}
}

/*
 * One-directional list of references
 */
Method(mfd0,, Serialized)
{
	Name(sz, 16)	// full size of Package
	Name(num, 0)	// half-size of Package

	Name(p000, Package(sz) {})
	Name(p001, Package(sz) {})
	Name(p002, Package(sz) {})
	Name(p003, Package(sz) {})
	Name(p004, Package(sz) {})
	Name(p005, Package(sz) {})
	Name(p006, Package(sz) {})
	Name(p007, Package(sz) {})

	Name(i000, 0xabcd0000)
	Name(i001, 0xabcd0100)
	Name(i002, 0xabcd0200)
	Name(i003, 0xabcd0300)
	Name(i004, 0xabcd0400)
	Name(i005, 0xabcd0500)
	Name(i006, 0xabcd0600)
	Name(i007, 0xabcd0700)

	Divide(sz, 2, Local0, num)

	/* Initializing Packages with monotone increasing Integers */

	mfc7(p000, 0, sz, i000)
	mfc7(p001, 0, sz, i001)
	mfc7(p002, 0, sz, i002)
	mfc7(p003, 0, sz, i003)
	mfc7(p004, 0, sz, i004)
	mfc7(p005, 0, sz, i005)
	mfc7(p006, 0, sz, i006)
	mfc7(p007, 0, sz, i007)

	/* Initializing the Package with IRefs */

	mfc8(p000, p001, 0, num, num, 0, 0)
	mfc8(p001, p002, 0, num, num, 0, 0)
	mfc8(p002, p003, 0, num, num, 0, 0)
	mfc8(p003, p004, 0, num, num, 0, 0)
	mfc8(p004, p005, 0, num, num, 0, 0)
	mfc8(p005, p006, 0, num, num, 0, 0)
	mfc8(p006, p007, 0, num, num, 0, 0)

	/* Verifying access to the first parts of Packages through the IRefs */

	mfcc(p001, num, num, i000, 0, 0x008)
	mfcc(p002, num, num, i001, 0, 0x009)
	mfcc(p003, num, num, i002, 0, 0x00a)
	mfcc(p004, num, num, i003, 0, 0x00b)
	mfcc(p005, num, num, i004, 0, 0x00c)
	mfcc(p006, num, num, i005, 0, 0x00d)
	mfcc(p007, num, num, i006, 0, 0x00e)
}

/*
 * 0-Ring of references
 */
Method(mfd1,, Serialized)
{
	Name(sz, 16)	// full size of Package
	Name(num, 0)	// half-size of Package

	Name(p000, Package(sz) {})
	Name(p001, Package(sz) {})
	Name(p002, Package(sz) {})
	Name(p003, Package(sz) {})
	Name(p004, Package(sz) {})
	Name(p005, Package(sz) {})
	Name(p006, Package(sz) {})
	Name(p007, Package(sz) {})

	Name(i000, 0xabcd0000)
	Name(i001, 0xabcd0100)
	Name(i002, 0xabcd0200)
	Name(i003, 0xabcd0300)
	Name(i004, 0xabcd0400)
	Name(i005, 0xabcd0500)
	Name(i006, 0xabcd0600)
	Name(i007, 0xabcd0700)

	Divide(sz, 2, Local0, num)

	/* Initializing Packages with monotone increasing Integers */

	mfc7(p000, 0, sz, i000)
	mfc7(p001, 0, sz, i001)
	mfc7(p002, 0, sz, i002)
	mfc7(p003, 0, sz, i003)
	mfc7(p004, 0, sz, i004)
	mfc7(p005, 0, sz, i005)
	mfc7(p006, 0, sz, i006)
	mfc7(p007, 0, sz, i007)

	/* Initializing the Package with IRefs */

	mfc8(p000, p001, 0, num, num, 0, 0)
	mfc8(p001, p002, 0, num, num, 0, 0)
	mfc8(p002, p003, 0, num, num, 0, 0)
	mfc8(p003, p004, 0, num, num, 0, 0)
	mfc8(p004, p005, 0, num, num, 0, 0)
	mfc8(p005, p006, 0, num, num, 0, 0)
	mfc8(p006, p007, 0, num, num, 0, 0)
	mfc8(p007, p000, 0, num, num, 0, 0)

	/* Verifying access to the first parts of Packages through the IRefs */

	mfcc(p001, num, num, i000, 0, 0x00f)
	mfcc(p002, num, num, i001, 0, 0x010)
	mfcc(p003, num, num, i002, 0, 0x011)
	mfcc(p004, num, num, i003, 0, 0x012)
	mfcc(p005, num, num, i004, 0, 0x013)
	mfcc(p006, num, num, i005, 0, 0x014)
	mfcc(p007, num, num, i006, 0, 0x015)
	mfcc(p000, num, num, i007, 0, 0x016)
}

/*
 * 9-Ring of references
 */
Method(mfd2,, Serialized)
{
	Name(sz, 16)	// full size of Package
	Name(num, 0)	// half-size of Package

	Name(p000, Package(sz) {})
	Name(p001, Package(sz) {})
	Name(p002, Package(sz) {})
	Name(p003, Package(sz) {})
	Name(p004, Package(sz) {})
	Name(p005, Package(sz) {})
	Name(p006, Package(sz) {})
	Name(p007, Package(sz) {})

	Name(i000, 0xabcd0000)
	Name(i001, 0xabcd0100)
	Name(i002, 0xabcd0200)
	Name(i003, 0xabcd0300)
	Name(i004, 0xabcd0400)
	Name(i005, 0xabcd0500)
	Name(i006, 0xabcd0600)
	Name(i007, 0xabcd0700)

	Divide(sz, 2, Local0, num)

	/* Initializing Packages with monotone increasing Integers */

	mfc7(p000, 0, sz, i000)
	mfc7(p001, 0, sz, i001)
	mfc7(p002, 0, sz, i002)
	mfc7(p003, 0, sz, i003)
	mfc7(p004, 0, sz, i004)
	mfc7(p005, 0, sz, i005)
	mfc7(p006, 0, sz, i006)
	mfc7(p007, 0, sz, i007)

	/* Initializing the Package with IRefs */

	mfc8(p000, p001, 0, num, num, 0, 0)
	mfc8(p001, p002, 0, num, num, 0, 0)
	mfc8(p002, p003, 0, num, num, 0, 0)
	mfc8(p003, p000, 0, num, num, 0, 0)

	mfc8(p003, p004, 0, num, num, 0, 0)
	mfc8(p004, p005, 0, num, num, 0, 0)
	mfc8(p005, p006, 0, num, num, 0, 0)
	mfc8(p006, p007, 0, num, num, 0, 0)

	/* Verifying access to the first parts of Packages through the IRefs */

	mfcc(p001, num, num, i000, 0, 0x017)
	mfcc(p002, num, num, i001, 0, 0x018)
	mfcc(p003, num, num, i002, 0, 0x019)
	mfcc(p000, num, num, i003, 0, 0x01a)

	mfcc(p004, num, num, i003, 0, 0x01b)
	mfcc(p005, num, num, i004, 0, 0x01c)
	mfcc(p006, num, num, i005, 0, 0x01d)
	mfcc(p007, num, num, i006, 0, 0x01e)
}

/*
 * Bush of references
 */
Method(mfd3,, Serialized)
{
	Name(sz, 16)	// full size of Package
	Name(num, 0)	// half-size of Package

	Name(p000, Package(sz) {})
	Name(p001, Package(sz) {})
	Name(p002, Package(sz) {})
	Name(p003, Package(sz) {})
	Name(p004, Package(sz) {})
	Name(p005, Package(sz) {})
	Name(p006, Package(sz) {})
	Name(p007, Package(sz) {})
	Name(p008, Package(sz) {})

	Name(i000, 0xabcd0000)
	Name(i001, 0xabcd0100)
	Name(i002, 0xabcd0200)
	Name(i003, 0xabcd0300)
	Name(i004, 0xabcd0400)
	Name(i005, 0xabcd0500)
	Name(i006, 0xabcd0600)
	Name(i007, 0xabcd0700)
	Name(i008, 0xabcd0800)

	Divide(sz, 2, Local0, num)

	/* Initializing Packages with monotone increasing Integers */

	mfc7(p000, 0, sz, i000)
	mfc7(p001, 0, sz, i001)
	mfc7(p002, 0, sz, i002)
	mfc7(p003, 0, sz, i003)
	mfc7(p004, 0, sz, i004)
	mfc7(p005, 0, sz, i005)
	mfc7(p006, 0, sz, i006)
	mfc7(p007, 0, sz, i007)
	mfc7(p008, 0, sz, i008)

	/* Initializing the Package with IRefs */

	mfc8(p005, p005, 0, num, num, 0, 0)

	mfc8(p005, p000, 0, num, num, 0, 0)
	mfc8(p000, p001, 0, num, num, 0, 0)

	mfc8(p005, p002, 0, num, num, 0, 0)
	mfc8(p002, p003, 0, num, num, 0, 0)

	mfc8(p005, p004, 0, num, num, 0, 0)
	mfc8(p004, p006, 0, num, num, 0, 0)

	mfc8(p005, p007, 0, num, num, 0, 0)
	mfc8(p007, p008, 0, num, num, 0, 0)

	/* Do self-references repeatedly */

	mfc8(p005, p005, 0, num, num, 0, 0)
	mfc8(p005, p005, 0, num, num, 0, 0)
	mfc8(p005, p005, 0, num, num, 0, 0)
	mfc8(p005, p005, 0, num, num, 0, 0)
	mfc8(p005, p005, 0, num, num, 0, 0)

	/* Verifying access to the first parts of Packages through the IRefs */

	mfcc(p005, num, num, i005, 0, 0x01f)
	mfcc(p000, num, num, i005, 0, 0x020)
	mfcc(p001, num, num, i000, 0, 0x021)
	mfcc(p002, num, num, i005, 0, 0x022)
	mfcc(p003, num, num, i002, 0, 0x023)
	mfcc(p004, num, num, i005, 0, 0x024)
	mfcc(p006, num, num, i004, 0, 0x025)
	mfcc(p007, num, num, i005, 0, 0x026)
	mfcc(p008, num, num, i007, 0, 0x027)
}

/*
 * Two-directional list of references
 */
Method(mfd4,, Serialized)
{
	Name(sz, 16)	// full size of Package
	Name(nm2, 0)	// half-size of Package
	Name(nm4, 0)	// one fourth of size of Package
	Name(nm34, 0)	// three fourth of size of Package

	Name(p000, Package(sz) {})
	Name(p001, Package(sz) {})
	Name(p002, Package(sz) {})
	Name(p003, Package(sz) {})
	Name(p004, Package(sz) {})
	Name(p005, Package(sz) {})
	Name(p006, Package(sz) {})
	Name(p007, Package(sz) {})

	Name(i000, 0xabcd0000)
	Name(i001, 0xabcd0100)
	Name(i002, 0xabcd0200)
	Name(i003, 0xabcd0300)
	Name(i004, 0xabcd0400)
	Name(i005, 0xabcd0500)
	Name(i006, 0xabcd0600)
	Name(i007, 0xabcd0700)

	Divide(sz, 2, Local0, nm2)
	Divide(sz, 4, Local0, nm4)
	Add(nm2, nm4, nm34)

	/* Initializing Packages with monotone increasing Integers */

	mfc7(p000, 0, sz, i000)
	mfc7(p001, 0, sz, i001)
	mfc7(p002, 0, sz, i002)
	mfc7(p003, 0, sz, i003)
	mfc7(p004, 0, sz, i004)
	mfc7(p005, 0, sz, i005)
	mfc7(p006, 0, sz, i006)
	mfc7(p007, 0, sz, i007)

	/* Initializing the Package with IRefs */

	mfc8(p000, p001, 0, nm2, nm4, 0, 0)
	mfc8(p001, p002, 0, nm2, nm4, 0, 0)
	mfc8(p002, p003, 0, nm2, nm4, 0, 0)
	mfc8(p003, p004, 0, nm2, nm4, 0, 0)
	mfc8(p004, p005, 0, nm2, nm4, 0, 0)
	mfc8(p005, p006, 0, nm2, nm4, 0, 0)
	mfc8(p006, p007, 0, nm2, nm4, 0, 0)

	mfc8(p007, p006, nm4, nm34, nm4, 0, 0)
	mfc8(p006, p005, nm4, nm34, nm4, 0, 0)
	mfc8(p005, p004, nm4, nm34, nm4, 0, 0)
	mfc8(p004, p003, nm4, nm34, nm4, 0, 0)
	mfc8(p003, p002, nm4, nm34, nm4, 0, 0)
	mfc8(p002, p001, nm4, nm34, nm4, 0, 0)
	mfc8(p001, p000, nm4, nm34, nm4, 0, 0)

	/* Verifying access to the first parts of Packages through the IRefs */

	mfcc(p001, nm2, nm4, i000, 0, 0x028)
	mfcc(p002, nm2, nm4, i001, 0, 0x029)
	mfcc(p003, nm2, nm4, i002, 0, 0x02a)
	mfcc(p004, nm2, nm4, i003, 0, 0x02b)
	mfcc(p005, nm2, nm4, i004, 0, 0x02c)
	mfcc(p006, nm2, nm4, i005, 0, 0x02d)
	mfcc(p007, nm2, nm4, i006, 0, 0x02e)

	Add(i007, nm4, i007)
	Add(i006, nm4, i006)
	Add(i005, nm4, i005)
	Add(i004, nm4, i004)
	Add(i003, nm4, i003)
	Add(i002, nm4, i002)
	Add(i001, nm4, i001)

	mfcc(p006, nm34, nm4, i007, 0, 0x02f)
	mfcc(p005, nm34, nm4, i006, 0, 0x030)
	mfcc(p004, nm34, nm4, i005, 0, 0x031)
	mfcc(p003, nm34, nm4, i004, 0, 0x032)
	mfcc(p002, nm34, nm4, i003, 0, 0x033)
	mfcc(p001, nm34, nm4, i002, 0, 0x034)
	mfcc(p000, nm34, nm4, i001, 0, 0x035)
}

/*
 * Ring of two-directional references
 */
Method(mfd5,, Serialized)
{
	Name(sz, 16)	// full size of Package
	Name(nm2, 0)	// half-size of Package
	Name(nm4, 0)	// one fourth of size of Package
	Name(nm34, 0)	// three fourth of size of Package

	Name(p000, Package(sz) {})
	Name(p001, Package(sz) {})
	Name(p002, Package(sz) {})
	Name(p003, Package(sz) {})
	Name(p004, Package(sz) {})
	Name(p005, Package(sz) {})
	Name(p006, Package(sz) {})
	Name(p007, Package(sz) {})

	Name(i000, 0xabcd0000)
	Name(i001, 0xabcd0100)
	Name(i002, 0xabcd0200)
	Name(i003, 0xabcd0300)
	Name(i004, 0xabcd0400)
	Name(i005, 0xabcd0500)
	Name(i006, 0xabcd0600)
	Name(i007, 0xabcd0700)

	Divide(sz, 2, Local0, nm2)
	Divide(sz, 4, Local0, nm4)
	Add(nm2, nm4, nm34)

	/* Initializing Packages with monotone increasing Integers */

	mfc7(p000, 0, sz, i000)
	mfc7(p001, 0, sz, i001)
	mfc7(p002, 0, sz, i002)
	mfc7(p003, 0, sz, i003)
	mfc7(p004, 0, sz, i004)
	mfc7(p005, 0, sz, i005)
	mfc7(p006, 0, sz, i006)
	mfc7(p007, 0, sz, i007)

	/* Initializing the Package with IRefs */

	mfc8(p000, p001, 0, nm2, nm4, 0, 0)
	mfc8(p001, p002, 0, nm2, nm4, 0, 0)
	mfc8(p002, p003, 0, nm2, nm4, 0, 0)
	mfc8(p003, p004, 0, nm2, nm4, 0, 0)
	mfc8(p004, p005, 0, nm2, nm4, 0, 0)
	mfc8(p005, p006, 0, nm2, nm4, 0, 0)
	mfc8(p006, p007, 0, nm2, nm4, 0, 0)
	mfc8(p007, p000, 0, nm2, nm4, 0, 0)


	mfc8(p007, p006, nm4, nm34, nm4, 0, 0)
	mfc8(p006, p005, nm4, nm34, nm4, 0, 0)
	mfc8(p005, p004, nm4, nm34, nm4, 0, 0)
	mfc8(p004, p003, nm4, nm34, nm4, 0, 0)
	mfc8(p003, p002, nm4, nm34, nm4, 0, 0)
	mfc8(p002, p001, nm4, nm34, nm4, 0, 0)
	mfc8(p001, p000, nm4, nm34, nm4, 0, 0)
	mfc8(p000, p007, nm4, nm34, nm4, 0, 0)


	/* Verifying access to the first parts of Packages through the IRefs */

	mfcc(p001, nm2, nm4, i000, 0, 0x036)
	mfcc(p002, nm2, nm4, i001, 0, 0x037)
	mfcc(p003, nm2, nm4, i002, 0, 0x038)
	mfcc(p004, nm2, nm4, i003, 0, 0x039)
	mfcc(p005, nm2, nm4, i004, 0, 0x03a)
	mfcc(p006, nm2, nm4, i005, 0, 0x03b)
	mfcc(p007, nm2, nm4, i006, 0, 0x03c)
	mfcc(p000, nm2, nm4, i007, 0, 0x03d)

	Add(i007, nm4, i007)
	Add(i006, nm4, i006)
	Add(i005, nm4, i005)
	Add(i004, nm4, i004)
	Add(i003, nm4, i003)
	Add(i002, nm4, i002)
	Add(i001, nm4, i001)
	Add(i000, nm4, i000)

	mfcc(p006, nm34, nm4, i007, 0, 0x03e)
	mfcc(p005, nm34, nm4, i006, 0, 0x03f)
	mfcc(p004, nm34, nm4, i005, 0, 0x040)
	mfcc(p003, nm34, nm4, i004, 0, 0x041)
	mfcc(p002, nm34, nm4, i003, 0, 0x042)
	mfcc(p001, nm34, nm4, i002, 0, 0x043)
	mfcc(p000, nm34, nm4, i001, 0, 0x044)
	mfcc(p007, nm34, nm4, i000, 0, 0x045)
}

/*
 * Web of references
 */
Method(mfd6,, Serialized)
{
	Name(sz, 32)	// full size of Package
	Name(prt, 16)	// number of different parts
	Name(nm16, 0)	// 1/16 of size
	Name(i1, 0)		// 1/16 of size
	Name(i2, 0)		// 2/16 of size
	Name(i3, 0)
	Name(i4, 0)
	Name(i5, 0)
	Name(i6, 0)
	Name(i8, 0)
	Name(i9, 0)
	Name(i10, 0)
	Name(i11, 0)
	Name(i12, 0)
	Name(i13, 0)
	Name(i14, 0)

	Name(p000, Package(sz) {})
	Name(p001, Package(sz) {})
	Name(p002, Package(sz) {})
	Name(p003, Package(sz) {})
	Name(p004, Package(sz) {})
	Name(p005, Package(sz) {})
	Name(p006, Package(sz) {})
	Name(p007, Package(sz) {})

	Name(i000, 0xabcd0000)
	Name(i001, 0xabcd0100)
	Name(i002, 0xabcd0200)
	Name(i003, 0xabcd0300)
	Name(i004, 0xabcd0400)
	Name(i005, 0xabcd0500)
	Name(i006, 0xabcd0600)
	Name(i007, 0xabcd0700)

	Divide(sz, prt, Local0, nm16)

	Store(nm16, i1)
	Multiply(nm16, 2, i2)
	Multiply(nm16, 3, i3)
	Multiply(nm16, 4, i4)
	Multiply(nm16, 5, i5)
	Multiply(nm16, 6, i6)
	Multiply(nm16, 8, i8)
	Multiply(nm16, 9, i9)
	Multiply(nm16, 10, i10)
	Multiply(nm16, 11, i11)
	Multiply(nm16, 12, i12)
	Multiply(nm16, 13, i13)
	Multiply(nm16, 14, i14)


	/* Initializing full Packages with monotone increasing Integers */

	mfc7(p000, 0, sz, i000)
	mfc7(p001, 0, sz, i001)
	mfc7(p002, 0, sz, i002)
	mfc7(p003, 0, sz, i003)
	mfc7(p004, 0, sz, i004)
	mfc7(p005, 0, sz, i005)
	mfc7(p006, 0, sz, i006)
	mfc7(p007, 0, sz, i007)

	/* Initializing the Package with IRefs */

	/* Generate two-directional ring of references */

	mfc8(p000, p001, 0, i8, nm16, 0, 0)
	mfc8(p001, p002, 0, i8, nm16, 0, 0)
	mfc8(p002, p003, 0, i8, nm16, 0, 0)
	mfc8(p003, p004, 0, i8, nm16, 0, 0)
	mfc8(p004, p005, 0, i8, nm16, 0, 0)
	mfc8(p005, p006, 0, i8, nm16, 0, 0)
	mfc8(p006, p007, 0, i8, nm16, 0, 0)
	mfc8(p007, p000, 0, i8, nm16, 0, 0)

	mfc8(p007, p006, i1, i9, nm16, 0, 0)
	mfc8(p006, p005, i1, i9, nm16, 0, 0)
	mfc8(p005, p004, i1, i9, nm16, 0, 0)
	mfc8(p004, p003, i1, i9, nm16, 0, 0)
	mfc8(p003, p002, i1, i9, nm16, 0, 0)
	mfc8(p002, p001, i1, i9, nm16, 0, 0)
	mfc8(p001, p000, i1, i9, nm16, 0, 0)
	mfc8(p000, p007, i1, i9, nm16, 0, 0)

	/*
	 * Join all other packages
	 * (two directions for each two points)
	 */

	mfc8(p002, p000, i2, i10, nm16, 0, 0)
	mfc8(p003, p000, i3, i11, nm16, 0, 0)
	mfc8(p004, p000, i4, i12, nm16, 0, 0)
	mfc8(p005, p000, i5, i13, nm16, 0, 0)
	mfc8(p006, p000, i6, i14, nm16, 0, 0)

	mfc8(p003, p001, i3, i11, nm16, 0, 0)
	mfc8(p004, p001, i4, i12, nm16, 0, 0)
	mfc8(p005, p001, i5, i13, nm16, 0, 0)
	mfc8(p006, p001, i6, i14, nm16, 0, 0)
	mfc8(p007, p001, i2, i10, nm16, 0, 0)

	mfc8(p004, p002, i4, i12, nm16, 0, 0)
	mfc8(p005, p002, i5, i13, nm16, 0, 0)
	mfc8(p006, p002, i6, i14, nm16, 0, 0)
	mfc8(p007, p002, i2, i10, nm16, 0, 0)
	mfc8(p000, p002, i3, i11, nm16, 0, 0)

	mfc8(p005, p003, i5, i13, nm16, 0, 0)
	mfc8(p006, p003, i6, i14, nm16, 0, 0)
	mfc8(p007, p003, i2, i10, nm16, 0, 0)
	mfc8(p000, p003, i3, i11, nm16, 0, 0)
	mfc8(p001, p003, i4, i12, nm16, 0, 0)

	mfc8(p006, p004, i6, i14, nm16, 0, 0)
	mfc8(p007, p004, i2, i10, nm16, 0, 0)
	mfc8(p000, p004, i3, i11, nm16, 0, 0)
	mfc8(p001, p004, i4, i12, nm16, 0, 0)
	mfc8(p002, p004, i5, i13, nm16, 0, 0)

	mfc8(p007, p005, i2, i10, nm16, 0, 0)
	mfc8(p000, p005, i3, i11, nm16, 0, 0)
	mfc8(p001, p005, i4, i12, nm16, 0, 0)
	mfc8(p002, p005, i5, i13, nm16, 0, 0)
	mfc8(p003, p005, i6, i14, nm16, 0, 0)

	mfc8(p000, p006, i3, i11, nm16, 0, 0)
	mfc8(p001, p006, i4, i12, nm16, 0, 0)
	mfc8(p002, p006, i5, i13, nm16, 0, 0)
	mfc8(p003, p006, i6, i14, nm16, 0, 0)
	mfc8(p004, p006, i2, i10, nm16, 0, 0)

	mfc8(p001, p007, i4, i12, nm16, 0, 0)
	mfc8(p002, p007, i5, i13, nm16, 0, 0)
	mfc8(p003, p007, i6, i14, nm16, 0, 0)
	mfc8(p004, p007, i2, i10, nm16, 0, 0)
	mfc8(p005, p007, i3, i11, nm16, 0, 0)


	/* Verifying access to Packages through the IRefs */

	/* Two-directional ring of references */

	mfcc(p001, i8, nm16, i000, 0, 0x046)
	mfcc(p002, i8, nm16, i001, 0, 0x047)
	mfcc(p003, i8, nm16, i002, 0, 0x048)
	mfcc(p004, i8, nm16, i003, 0, 0x049)
	mfcc(p005, i8, nm16, i004, 0, 0x04a)
	mfcc(p006, i8, nm16, i005, 0, 0x04b)
	mfcc(p007, i8, nm16, i006, 0, 0x04c)
	mfcc(p000, i8, nm16, i007, 0, 0x04d)

	Add(i007, nm16, i007)
	Add(i006, nm16, i006)
	Add(i005, nm16, i005)
	Add(i004, nm16, i004)
	Add(i003, nm16, i003)
	Add(i002, nm16, i002)
	Add(i001, nm16, i001)
	Add(i000, nm16, i000)

	mfcc(p006, i9, nm16, i007, 0, 0x04e)
	mfcc(p005, i9, nm16, i006, 0, 0x04f)
	mfcc(p004, i9, nm16, i005, 0, 0x050)
	mfcc(p003, i9, nm16, i004, 0, 0x051)
	mfcc(p002, i9, nm16, i003, 0, 0x052)
	mfcc(p001, i9, nm16, i002, 0, 0x053)
	mfcc(p000, i9, nm16, i001, 0, 0x054)
	mfcc(p007, i9, nm16, i000, 0, 0x055)

	/* Verify other references */

	Add(i007, nm16, i007)
	Add(i006, nm16, i006)
	Add(i005, nm16, i005)
	Add(i004, nm16, i004)
	Add(i003, nm16, i003)
	Add(i002, nm16, i002)
	Add(i001, nm16, i001)
	Add(i000, nm16, i000)

	mfcc(p000, i10, nm16, i002, 0, 0x056)
	mfcc(p001, i10, nm16, i007, 0, 0x057)
	mfcc(p002, i10, nm16, i007, 0, 0x058)
	mfcc(p003, i10, nm16, i007, 0, 0x059)
	mfcc(p004, i10, nm16, i007, 0, 0x05a)
	mfcc(p005, i10, nm16, i007, 0, 0x05b)
	mfcc(p006, i10, nm16, i004, 0, 0x05c)
	mfcc(p007, i10, nm16, i004, 0, 0x05d)

	Add(i007, nm16, i007)
	Add(i006, nm16, i006)
	Add(i005, nm16, i005)
	Add(i004, nm16, i004)
	Add(i003, nm16, i003)
	Add(i002, nm16, i002)
	Add(i001, nm16, i001)
	Add(i000, nm16, i000)

	mfcc(p000, i11, nm16, i003, 0, 0x05e)
	mfcc(p001, i11, nm16, i003, 0, 0x05f)
	mfcc(p002, i11, nm16, i000, 0, 0x060)
	mfcc(p003, i11, nm16, i000, 0, 0x061)
	mfcc(p004, i11, nm16, i000, 0, 0x062)
	mfcc(p005, i11, nm16, i000, 0, 0x063)
	mfcc(p006, i11, nm16, i000, 0, 0x064)
	mfcc(p007, i11, nm16, i005, 0, 0x065)

	Add(i007, nm16, i007)
	Add(i006, nm16, i006)
	Add(i005, nm16, i005)
	Add(i004, nm16, i004)
	Add(i003, nm16, i003)
	Add(i002, nm16, i002)
	Add(i001, nm16, i001)
	Add(i000, nm16, i000)

	mfcc(p000, i12, nm16, i004, 0, 0x066)
	mfcc(p001, i12, nm16, i004, 0, 0x067)
	mfcc(p002, i12, nm16, i004, 0, 0x068)
	mfcc(p003, i12, nm16, i001, 0, 0x069)
	mfcc(p004, i12, nm16, i001, 0, 0x06a)
	mfcc(p005, i12, nm16, i001, 0, 0x06b)
	mfcc(p006, i12, nm16, i001, 0, 0x06c)
	mfcc(p007, i12, nm16, i001, 0, 0x06d)

	Add(i007, nm16, i007)
	Add(i006, nm16, i006)
	Add(i005, nm16, i005)
	Add(i004, nm16, i004)
	Add(i003, nm16, i003)
	Add(i002, nm16, i002)
	Add(i001, nm16, i001)
	Add(i000, nm16, i000)

	mfcc(p000, i13, nm16, i005, 0, 0x06e)
	mfcc(p001, i13, nm16, i005, 0, 0x06f)
	mfcc(p002, i13, nm16, i005, 0, 0x070)
	mfcc(p003, i13, nm16, i005, 0, 0x071)
	mfcc(p004, i13, nm16, i002, 0, 0x072)
	mfcc(p005, i13, nm16, i002, 0, 0x073)
	mfcc(p006, i13, nm16, i002, 0, 0x074)
	mfcc(p007, i13, nm16, i002, 0, 0x075)

	Add(i007, nm16, i007)
	Add(i006, nm16, i006)
	Add(i005, nm16, i005)
	Add(i004, nm16, i004)
	Add(i003, nm16, i003)
	Add(i002, nm16, i002)
	Add(i001, nm16, i001)
	Add(i000, nm16, i000)

	mfcc(p000, i14, nm16, i006, 0, 0x076)
	mfcc(p001, i14, nm16, i006, 0, 0x077)
	mfcc(p002, i14, nm16, i006, 0, 0x078)
	mfcc(p003, i14, nm16, i006, 0, 0x079)
	mfcc(p004, i14, nm16, i006, 0, 0x07a)
	mfcc(p005, i14, nm16, i003, 0, 0x07b)
	mfcc(p006, i14, nm16, i003, 0, 0x07c)
	mfcc(p007, i14, nm16, i003, 0, 0x07d)
}

/*
 * Extended Web of references
 */
Method(mfd7, 7, Serialized)
{
	Name(lpN0, 0)
	Name(lpC0, 0)

	Name(sz, 32)	// full size of Package
	Name(prt, 16)	// number of different parts
	Name(nm16, 0)	// 1/16 of size
	Name(i1, 0)		// 1/16 of size
	Name(i2, 0)		// 2/16 of size
	Name(i3, 0)
	Name(i4, 0)
	Name(i5, 0)
	Name(i6, 0)
	Name(i8, 0)
	Name(i9, 0)
	Name(i10, 0)
	Name(i11, 0)
	Name(i12, 0)
	Name(i13, 0)
	Name(i14, 0)

	Name(p000, Package(sz) {})
	Name(p001, Package(sz) {})
	Name(p002, Package(sz) {})
	Name(p003, Package(sz) {})
	Name(p004, Package(sz) {})
	Name(p005, Package(sz) {})
	Name(p006, Package(sz) {})
	Name(p007, Package(sz) {})

	Name(i000, 0xabcd0000)
	Name(i001, 0xabcd0100)
	Name(i002, 0xabcd0200)
	Name(i003, 0xabcd0300)
	Name(i004, 0xabcd0400)
	Name(i005, 0xabcd0500)
	Name(i006, 0xabcd0600)
	Name(i007, 0xabcd0700)

	Name(iii0, 0)
	Name(iii1, 0)
	Name(iii2, 0)
	Name(iii3, 0)
	Name(iii4, 0)
	Name(iii5, 0)
	Name(iii6, 0)
	Name(iii7, 0)

	Divide(sz, prt, Local0, nm16)

	Store(nm16, i1)
	Multiply(nm16, 2, i2)
	Multiply(nm16, 3, i3)
	Multiply(nm16, 4, i4)
	Multiply(nm16, 5, i5)
	Multiply(nm16, 6, i6)
	Multiply(nm16, 8, i8)
	Multiply(nm16, 9, i9)
	Multiply(nm16, 10, i10)
	Multiply(nm16, 11, i11)
	Multiply(nm16, 12, i12)
	Multiply(nm16, 13, i13)
	Multiply(nm16, 14, i14)


	/* Initializing full Packages with monotone increasing Integers */

	mfc7(p000, 0, sz, i000)
	mfc7(p001, 0, sz, i001)
	mfc7(p002, 0, sz, i002)
	mfc7(p003, 0, sz, i003)
	mfc7(p004, 0, sz, i004)
	mfc7(p005, 0, sz, i005)
	mfc7(p006, 0, sz, i006)
	mfc7(p007, 0, sz, i007)

	/* Initializing the Package with IRefs */

	/* Generate two-directional ring of references */

	mfc8(p000, p001, 0, i8, nm16, 0, 0)
	mfc8(p001, p002, 0, i8, nm16, 0, 0)
	mfc8(p002, p003, 0, i8, nm16, 0, 0)
	mfc8(p003, p004, 0, i8, nm16, 0, 0)
	mfc8(p004, p005, 0, i8, nm16, 0, 0)
	mfc8(p005, p006, 0, i8, nm16, 0, 0)
	mfc8(p006, p007, 0, i8, nm16, 0, 0)
	mfc8(p007, p000, 0, i8, nm16, 0, 0)

	/* Do some initialization repeatedly so writing upon references */

	Store(2, lpN0)
	Store(0, lpC0)

	While (lpN0) {
		mfc8(p007, p006, i1, i9, nm16, 0, 0)
		mfc8(p006, p005, i1, i9, nm16, 0, 0)
		mfc8(p005, p004, i1, i9, nm16, 0, 0)
		mfc8(p004, p003, i1, i9, nm16, 0, 0)
		mfc8(p003, p002, i1, i9, nm16, 0, 0)
		mfc8(p002, p001, i1, i9, nm16, 0, 0)
		mfc8(p001, p000, i1, i9, nm16, 0, 0)
		mfc8(p000, p007, i1, i9, nm16, 0, 0)

		Decrement(lpN0)
		Increment(lpC0)
	}

	/* Store references additionally to LocalX */

	Store(Index(p000, 0), Local0)
	Store(Index(p000, 0), Local1)
	Store(Index(p000, 0), Local2)
	Store(Index(p000, 0), Local3)
	Store(Index(p000, 0), Local4)
	Store(Index(p000, 0), Local5)
	Store(Index(p000, 0), Local6)
	Store(Index(p000, 0), Local7)

	/* Re-write */

	Store(Index(p000, 0), Local0)
	Store(Index(p000, 0), Local1)
	Store(Index(p000, 0), Local2)
	Store(Index(p000, 0), Local3)
	Store(Index(p001, 0), Local4)
	Store(Index(p002, 0), Local5)
	Store(Index(p003, 0), Local6)
	Store(Index(p004, 0), Local7)

	/* Store references additionally to ArgX */

	Store(Index(p000, 0), arg0)
	Store(Index(p000, 0), arg1)
	Store(Index(p000, 0), arg2)
	Store(Index(p000, 0), arg3)
	Store(Index(p000, 0), arg4)
	Store(Index(p000, 0), arg5)
	Store(Index(p000, 0), arg6)

	/* Re-write */

	Store(Index(p000, 0), arg0)
	Store(Index(p000, 0), arg1)
	Store(Index(p000, 0), arg2)
	Store(Index(p000, 0), arg3)
	Store(Index(p001, 0), arg4)
	Store(Index(p002, 0), arg5)
	Store(Index(p003, 0), arg6)

	/* Store references additionally to NamedX */

	CopyObject(Index(p000, 0), iii0)
	CopyObject(Index(p000, 0), iii1)
	CopyObject(Index(p000, 0), iii2)
	CopyObject(Index(p000, 0), iii3)
	CopyObject(Index(p000, 0), iii4)
	CopyObject(Index(p000, 0), iii5)
	CopyObject(Index(p000, 0), iii6)
	CopyObject(Index(p000, 0), iii7)

	/* Re-write */

	CopyObject(Index(p000, 0), iii0)
	CopyObject(Index(p000, 0), iii1)
	CopyObject(Index(p000, 0), iii2)
	CopyObject(Index(p000, 0), iii3)
	CopyObject(Index(p001, 0), iii4)
	CopyObject(Index(p002, 0), iii5)
	CopyObject(Index(p003, 0), iii6)
	CopyObject(Index(p004, 0), iii7)

	/*
	 * Join all other packages
	 * (two directions for each two points)
	 */

	mfc8(p002, p000, i2, i10, nm16, 0, 0)
	mfc8(p003, p000, i3, i11, nm16, 0, 0)
	mfc8(p004, p000, i4, i12, nm16, 0, 0)
	mfc8(p005, p000, i5, i13, nm16, 0, 0)
	mfc8(p006, p000, i6, i14, nm16, 0, 0)

	mfc8(p003, p001, i3, i11, nm16, 0, 0)
	mfc8(p004, p001, i4, i12, nm16, 0, 0)
	mfc8(p005, p001, i5, i13, nm16, 0, 0)
	mfc8(p006, p001, i6, i14, nm16, 0, 0)
	mfc8(p007, p001, i2, i10, nm16, 0, 0)

	/* Do some initialization repeatedly so writing upon references */

	Store(2, lpN0)
	Store(0, lpC0)

	While (lpN0) {

		mfc8(p004, p002, i4, i12, nm16, 0, 0)
		mfc8(p005, p002, i5, i13, nm16, 0, 0)
		mfc8(p006, p002, i6, i14, nm16, 0, 0)
		mfc8(p007, p002, i2, i10, nm16, 0, 0)
		mfc8(p000, p002, i3, i11, nm16, 0, 0)

		mfc8(p005, p003, i5, i13, nm16, 0, 0)
		mfc8(p006, p003, i6, i14, nm16, 0, 0)
		mfc8(p007, p003, i2, i10, nm16, 0, 0)
		mfc8(p000, p003, i3, i11, nm16, 0, 0)
		mfc8(p001, p003, i4, i12, nm16, 0, 0)

		mfc8(p006, p004, i6, i14, nm16, 0, 0)
		mfc8(p007, p004, i2, i10, nm16, 0, 0)
		mfc8(p000, p004, i3, i11, nm16, 0, 0)
		mfc8(p001, p004, i4, i12, nm16, 0, 0)
		mfc8(p002, p004, i5, i13, nm16, 0, 0)

		mfc8(p007, p005, i2, i10, nm16, 0, 0)
		mfc8(p000, p005, i3, i11, nm16, 0, 0)
		mfc8(p001, p005, i4, i12, nm16, 0, 0)
		mfc8(p002, p005, i5, i13, nm16, 0, 0)
		mfc8(p003, p005, i6, i14, nm16, 0, 0)

		Decrement(lpN0)
		Increment(lpC0)
	}

	mfc8(p000, p006, i3, i11, nm16, 0, 0)
	mfc8(p001, p006, i4, i12, nm16, 0, 0)
	mfc8(p002, p006, i5, i13, nm16, 0, 0)
	mfc8(p003, p006, i6, i14, nm16, 0, 0)
	mfc8(p004, p006, i2, i10, nm16, 0, 0)

	mfc8(p001, p007, i4, i12, nm16, 0, 0)
	mfc8(p002, p007, i5, i13, nm16, 0, 0)
	mfc8(p003, p007, i6, i14, nm16, 0, 0)
	mfc8(p004, p007, i2, i10, nm16, 0, 0)
	mfc8(p005, p007, i3, i11, nm16, 0, 0)


	/* Verifying access to Packages through the IRefs */

	/* Two-directional ring of references */

	mfcc(p001, i8, nm16, i000, 0, 0x07e)
	mfcc(p002, i8, nm16, i001, 0, 0x07f)
	mfcc(p003, i8, nm16, i002, 0, 0x080)
	mfcc(p004, i8, nm16, i003, 0, 0x081)
	mfcc(p005, i8, nm16, i004, 0, 0x082)
	mfcc(p006, i8, nm16, i005, 0, 0x083)
	mfcc(p007, i8, nm16, i006, 0, 0x084)
	mfcc(p000, i8, nm16, i007, 0, 0x085)

	Add(i007, nm16, i007)
	Add(i006, nm16, i006)
	Add(i005, nm16, i005)
	Add(i004, nm16, i004)
	Add(i003, nm16, i003)
	Add(i002, nm16, i002)
	Add(i001, nm16, i001)
	Add(i000, nm16, i000)

	mfcc(p006, i9, nm16, i007, 0, 0x086)
	mfcc(p005, i9, nm16, i006, 0, 0x087)
	mfcc(p004, i9, nm16, i005, 0, 0x088)
	mfcc(p003, i9, nm16, i004, 0, 0x089)
	mfcc(p002, i9, nm16, i003, 0, 0x08a)
	mfcc(p001, i9, nm16, i002, 0, 0x08b)
	mfcc(p000, i9, nm16, i001, 0, 0x08c)
	mfcc(p007, i9, nm16, i000, 0, 0x08d)

	/* Verify other references */

	Add(i007, nm16, i007)
	Add(i006, nm16, i006)
	Add(i005, nm16, i005)
	Add(i004, nm16, i004)
	Add(i003, nm16, i003)
	Add(i002, nm16, i002)
	Add(i001, nm16, i001)
	Add(i000, nm16, i000)

	mfcc(p000, i10, nm16, i002, 0, 0x08e)
	mfcc(p001, i10, nm16, i007, 0, 0x08f)
	mfcc(p002, i10, nm16, i007, 0, 0x090)
	mfcc(p003, i10, nm16, i007, 0, 0x091)
	mfcc(p004, i10, nm16, i007, 0, 0x092)
	mfcc(p005, i10, nm16, i007, 0, 0x093)
	mfcc(p006, i10, nm16, i004, 0, 0x094)
	mfcc(p007, i10, nm16, i004, 0, 0x095)

	Add(i007, nm16, i007)
	Add(i006, nm16, i006)
	Add(i005, nm16, i005)
	Add(i004, nm16, i004)
	Add(i003, nm16, i003)
	Add(i002, nm16, i002)
	Add(i001, nm16, i001)
	Add(i000, nm16, i000)

	mfcc(p000, i11, nm16, i003, 0, 0x096)
	mfcc(p001, i11, nm16, i003, 0, 0x097)
	mfcc(p002, i11, nm16, i000, 0, 0x098)
	mfcc(p003, i11, nm16, i000, 0, 0x099)
	mfcc(p004, i11, nm16, i000, 0, 0x09a)
	mfcc(p005, i11, nm16, i000, 0, 0x09b)
	mfcc(p006, i11, nm16, i000, 0, 0x09c)
	mfcc(p007, i11, nm16, i005, 0, 0x09d)

	Add(i007, nm16, i007)
	Add(i006, nm16, i006)
	Add(i005, nm16, i005)
	Add(i004, nm16, i004)
	Add(i003, nm16, i003)
	Add(i002, nm16, i002)
	Add(i001, nm16, i001)
	Add(i000, nm16, i000)

	mfcc(p000, i12, nm16, i004, 0, 0x09e)
	mfcc(p001, i12, nm16, i004, 0, 0x09f)
	mfcc(p002, i12, nm16, i004, 0, 0x0a0)
	mfcc(p003, i12, nm16, i001, 0, 0x0a1)
	mfcc(p004, i12, nm16, i001, 0, 0x0a2)
	mfcc(p005, i12, nm16, i001, 0, 0x0a3)
	mfcc(p006, i12, nm16, i001, 0, 0x0a4)
	mfcc(p007, i12, nm16, i001, 0, 0x0a5)

	Add(i007, nm16, i007)
	Add(i006, nm16, i006)
	Add(i005, nm16, i005)
	Add(i004, nm16, i004)
	Add(i003, nm16, i003)
	Add(i002, nm16, i002)
	Add(i001, nm16, i001)
	Add(i000, nm16, i000)

	mfcc(p000, i13, nm16, i005, 0, 0x0a6)
	mfcc(p001, i13, nm16, i005, 0, 0x0a7)
	mfcc(p002, i13, nm16, i005, 0, 0x0a8)
	mfcc(p003, i13, nm16, i005, 0, 0x0a9)
	mfcc(p004, i13, nm16, i002, 0, 0x0aa)
	mfcc(p005, i13, nm16, i002, 0, 0x0ab)
	mfcc(p006, i13, nm16, i002, 0, 0x0ac)
	mfcc(p007, i13, nm16, i002, 0, 0x0ad)

	Add(i007, nm16, i007)
	Add(i006, nm16, i006)
	Add(i005, nm16, i005)
	Add(i004, nm16, i004)
	Add(i003, nm16, i003)
	Add(i002, nm16, i002)
	Add(i001, nm16, i001)
	Add(i000, nm16, i000)

	mfcc(p000, i14, nm16, i006, 0, 0x0ae)
	mfcc(p001, i14, nm16, i006, 0, 0x0af)
	mfcc(p002, i14, nm16, i006, 0, 0x0b0)
	mfcc(p003, i14, nm16, i006, 0, 0x0b1)
	mfcc(p004, i14, nm16, i006, 0, 0x0b2)
	mfcc(p005, i14, nm16, i003, 0, 0x0b3)
	mfcc(p006, i14, nm16, i003, 0, 0x0b4)
	mfcc(p007, i14, nm16, i003, 0, 0x0b5)

	mfd8(Local0, 0xabcd0000, 0x0b6)
	mfd8(Local1, 0xabcd0000, 0x0b7)
	mfd8(Local2, 0xabcd0000, 0x0b8)
	mfd8(Local3, 0xabcd0000, 0x0b9)
	mfd8(Local4, 0xabcd0100, 0x0ba)
	mfd8(Local5, 0xabcd0200, 0x0bb)
	mfd8(Local6, 0xabcd0300, 0x0bc)
	mfd8(Local7, 0xabcd0400, 0x0bd)

	mfd8(arg0, 0xabcd0000, 0x0be)
	mfd8(arg1, 0xabcd0000, 0x0bf)
	mfd8(arg2, 0xabcd0000, 0x0c0)
	mfd8(arg3, 0xabcd0000, 0x0c1)
	mfd8(arg4, 0xabcd0100, 0x0c2)
	mfd8(arg5, 0xabcd0200, 0x0c3)
	mfd8(arg6, 0xabcd0300, 0x0c4)

	if (y127) {
		mfd8(iii0, 0xabcd0000, 0x0c5)
		mfd8(iii1, 0xabcd0000, 0x0c6)
		mfd8(iii2, 0xabcd0000, 0x0c7)
		mfd8(iii3, 0xabcd0000, 0x0c8)
		mfd8(iii4, 0xabcd0100, 0x0c9)
		mfd8(iii5, 0xabcd0200, 0x0ca)
		mfd8(iii6, 0xabcd0300, 0x0cb)
		mfd8(iii7, 0xabcd0400, 0x0cc)
	}
}

Method(mfe9,, Serialized)
{
	Name(p000, Package(101) {0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f})
	Name(p002, Package(102) {0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27})

	Method(m000,, Serialized)
	{
		Name(p001, Package(100) {0,1})
		Store(Index(p000, 0), Index(p001, 0))
		Store(Index(p002, 0), Index(p001, 8))
		Store(Index(p001, 0), Index(p000, 0))
		Store(Index(p002, 0), Index(p000, 8))

		Store(Index(p000, 16), Index(p000, 16))
		Store(Index(p000, 16), Index(p000, 17))
		Store(Index(p000, 18), Index(p000, 19))
		Store(Index(p001, 16), Index(p001, 16))
		Store(Index(p001, 16), Index(p001, 17))
		Store(Index(p001, 18), Index(p001, 19))
		Store(Index(p002, 16), Index(p002, 16))
		Store(Index(p002, 16), Index(p002, 17))
		Store(Index(p002, 18), Index(p002, 19))
	}

	Method(m001,, Serialized)
	{
		Name(p001, Package(100) {0,1})
		Store(Index(p000, 1), Index(p001, 1))
		Store(Index(p002, 1), Index(p001, 9))
		Store(Index(p001, 1), Index(p000, 1))
		Store(Index(p002, 1), Index(p000, 9))

		Store(Index(p000, 20), Index(p000, 20))
		Store(Index(p000, 20), Index(p000, 21))
		Store(Index(p000, 22), Index(p000, 23))
		Store(Index(p001, 20), Index(p001, 20))
		Store(Index(p001, 20), Index(p001, 21))
		Store(Index(p001, 22), Index(p001, 23))
		Store(Index(p002, 20), Index(p002, 20))
		Store(Index(p002, 20), Index(p002, 21))
		Store(Index(p002, 22), Index(p002, 23))

		m000()
	}

	Method(m002,, Serialized)
	{
		Name(p001, Package(100) {0,1})
		Store(Index(p000, 2), Index(p001, 2))
		Store(Index(p002, 2), Index(p001, 10))
		Store(Index(p001, 2), Index(p000, 2))
		Store(Index(p002, 2), Index(p000, 10))

		Store(Index(p000, 30), Index(p000, 30))
		Store(Index(p000, 30), Index(p000, 31))
		Store(Index(p000, 32), Index(p000, 33))
		Store(Index(p001, 30), Index(p001, 30))
		Store(Index(p001, 30), Index(p001, 31))
		Store(Index(p001, 32), Index(p001, 33))
		Store(Index(p002, 30), Index(p002, 30))
		Store(Index(p002, 30), Index(p002, 31))
		Store(Index(p002, 32), Index(p002, 33))

		m001()
	}

	Method(m003,, Serialized)
	{
		Name(p001, Package(100) {0,1})
		Store(Index(p000, 3), Index(p001, 3))
		Store(Index(p002, 3), Index(p001, 11))
		Store(Index(p001, 3), Index(p000, 3))
		Store(Index(p002, 3), Index(p000, 11))

		Store(Index(p000, 40), Index(p000, 40))
		Store(Index(p000, 40), Index(p000, 41))
		Store(Index(p000, 42), Index(p000, 43))
		Store(Index(p001, 40), Index(p001, 40))
		Store(Index(p001, 40), Index(p001, 41))
		Store(Index(p001, 42), Index(p001, 43))
		Store(Index(p002, 40), Index(p002, 40))
		Store(Index(p002, 40), Index(p002, 41))
		Store(Index(p002, 42), Index(p002, 43))

		m002()
	}

	Method(m004,, Serialized)
	{
		Name(p001, Package(100) {0,1})
		Store(Index(p000, 4), Index(p001, 4))
		Store(Index(p002, 4), Index(p001, 12))
		Store(Index(p001, 4), Index(p000, 4))
		Store(Index(p002, 4), Index(p000, 12))

		Store(Index(p000, 50), Index(p000, 50))
		Store(Index(p000, 50), Index(p000, 51))
		Store(Index(p000, 52), Index(p000, 53))
		Store(Index(p001, 50), Index(p001, 50))
		Store(Index(p001, 50), Index(p001, 51))
		Store(Index(p001, 52), Index(p001, 53))
		Store(Index(p002, 50), Index(p002, 50))
		Store(Index(p002, 50), Index(p002, 51))
		Store(Index(p002, 52), Index(p002, 53))

		m003()
	}

	Method(m005,, Serialized)
	{
		Name(p001, Package(100) {0,1})
		Store(Index(p000, 5), Index(p001, 5))
		Store(Index(p002, 5), Index(p001, 13))
		Store(Index(p001, 5), Index(p000, 5))
		Store(Index(p002, 5), Index(p000, 13))

		Store(Index(p000, 60), Index(p000, 60))
		Store(Index(p000, 60), Index(p000, 61))
		Store(Index(p000, 62), Index(p000, 63))
		Store(Index(p001, 60), Index(p001, 60))
		Store(Index(p001, 60), Index(p001, 61))
		Store(Index(p001, 62), Index(p001, 63))
		Store(Index(p002, 60), Index(p002, 60))
		Store(Index(p002, 60), Index(p002, 61))
		Store(Index(p002, 62), Index(p002, 63))

		m004()
	}

	Method(m006,, Serialized)
	{
		Name(p001, Package(100) {0,1})
		Store(Index(p000, 6), Index(p001, 6))
		Store(Index(p002, 6), Index(p001, 14))
		Store(Index(p001, 6), Index(p000, 6))
		Store(Index(p002, 6), Index(p000, 14))

		Store(Index(p000, 70), Index(p000, 70))
		Store(Index(p000, 70), Index(p000, 71))
		Store(Index(p000, 72), Index(p000, 73))
		Store(Index(p001, 70), Index(p001, 70))
		Store(Index(p001, 70), Index(p001, 71))
		Store(Index(p001, 72), Index(p001, 73))
		Store(Index(p002, 70), Index(p002, 70))
		Store(Index(p002, 70), Index(p002, 71))
		Store(Index(p002, 72), Index(p002, 73))

		m005()
	}

	Method(m007,, Serialized)
	{
		Name(p001, Package(100) {0,1})
		Store(Index(p000, 7), Index(p001, 7))
		Store(Index(p002, 7), Index(p001, 15))
		Store(Index(p001, 7), Index(p000, 7))
		Store(Index(p002, 7), Index(p000, 15))

		Store(Index(p000, 80), Index(p000, 80))
		Store(Index(p000, 80), Index(p000, 81))
		Store(Index(p000, 82), Index(p000, 83))
		Store(Index(p001, 80), Index(p001, 80))
		Store(Index(p001, 80), Index(p001, 81))
		Store(Index(p001, 82), Index(p001, 83))
		Store(Index(p002, 80), Index(p002, 80))
		Store(Index(p002, 80), Index(p002, 81))
		Store(Index(p002, 82), Index(p002, 83))

		m006()
	}

	m007()
	m007()
}

Method(mfea,, Serialized)
{
	Name(p000, Package(101) {0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f})
	Name(p002, Package(102) {0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27})

	Method(m000, 1, Serialized)
	{
		Name(p001, Package(100) {0,1})
		Store(Index(arg0, 0), Index(p001, 0))
		Store(Index(p002, 0), Index(p001, 8))
		Store(Index(p001, 0), Index(arg0, 0))
		Store(Index(p002, 0), Index(arg0, 8))

		Store(Index(arg0, 16), Index(arg0, 16))
		Store(Index(arg0, 16), Index(arg0, 17))
		Store(Index(arg0, 18), Index(arg0, 19))
		Store(Index(p001, 16), Index(p001, 16))
		Store(Index(p001, 16), Index(p001, 17))
		Store(Index(p001, 18), Index(p001, 19))
		Store(Index(p002, 16), Index(p002, 16))
		Store(Index(p002, 16), Index(p002, 17))
		Store(Index(p002, 18), Index(p002, 19))
	}

	Method(m001, 1, Serialized)
	{
		Name(p001, Package(100) {0,1})
		Store(Index(arg0, 1), Index(p001, 1))
		Store(Index(p002, 1), Index(p001, 9))
		Store(Index(p001, 1), Index(arg0, 1))
		Store(Index(p002, 1), Index(arg0, 9))

		Store(Index(arg0, 20), Index(arg0, 20))
		Store(Index(arg0, 20), Index(arg0, 21))
		Store(Index(arg0, 22), Index(arg0, 23))
		Store(Index(p001, 20), Index(p001, 20))
		Store(Index(p001, 20), Index(p001, 21))
		Store(Index(p001, 22), Index(p001, 23))
		Store(Index(p002, 20), Index(p002, 20))
		Store(Index(p002, 20), Index(p002, 21))
		Store(Index(p002, 22), Index(p002, 23))

		m000(arg0)
	}

	Method(m002, 1, Serialized)
	{
		Name(p001, Package(100) {0,1})
		Store(Index(arg0, 2), Index(p001, 2))
		Store(Index(p002, 2), Index(p001, 10))
		Store(Index(p001, 2), Index(arg0, 2))
		Store(Index(p002, 2), Index(arg0, 10))

		Store(Index(arg0, 30), Index(arg0, 30))
		Store(Index(arg0, 30), Index(arg0, 31))
		Store(Index(arg0, 32), Index(arg0, 33))
		Store(Index(p001, 30), Index(p001, 30))
		Store(Index(p001, 30), Index(p001, 31))
		Store(Index(p001, 32), Index(p001, 33))
		Store(Index(p002, 30), Index(p002, 30))
		Store(Index(p002, 30), Index(p002, 31))
		Store(Index(p002, 32), Index(p002, 33))

		m001(arg0)
	}

	Method(m003, 1, Serialized)
	{
		Name(p001, Package(100) {0,1})
		Store(Index(arg0, 3), Index(p001, 3))
		Store(Index(p002, 3), Index(p001, 11))
		Store(Index(p001, 3), Index(arg0, 3))
		Store(Index(p002, 3), Index(arg0, 11))

		Store(Index(arg0, 40), Index(arg0, 40))
		Store(Index(arg0, 40), Index(arg0, 41))
		Store(Index(arg0, 42), Index(arg0, 43))
		Store(Index(p001, 40), Index(p001, 40))
		Store(Index(p001, 40), Index(p001, 41))
		Store(Index(p001, 42), Index(p001, 43))
		Store(Index(p002, 40), Index(p002, 40))
		Store(Index(p002, 40), Index(p002, 41))
		Store(Index(p002, 42), Index(p002, 43))

		m002(arg0)
	}

	Method(m004, 1, Serialized)
	{
		Name(p001, Package(100) {0,1})
		Store(Index(arg0, 4), Index(p001, 4))
		Store(Index(p002, 4), Index(p001, 12))
		Store(Index(p001, 4), Index(arg0, 4))
		Store(Index(p002, 4), Index(arg0, 12))

		Store(Index(arg0, 50), Index(arg0, 50))
		Store(Index(arg0, 50), Index(arg0, 51))
		Store(Index(arg0, 52), Index(arg0, 53))
		Store(Index(p001, 50), Index(p001, 50))
		Store(Index(p001, 50), Index(p001, 51))
		Store(Index(p001, 52), Index(p001, 53))
		Store(Index(p002, 50), Index(p002, 50))
		Store(Index(p002, 50), Index(p002, 51))
		Store(Index(p002, 52), Index(p002, 53))

		m003(arg0)
	}

	Method(m005, 1, Serialized)
	{
		Name(p001, Package(100) {0,1})
		Store(Index(arg0, 5), Index(p001, 5))
		Store(Index(p002, 5), Index(p001, 13))
		Store(Index(p001, 5), Index(arg0, 5))
		Store(Index(p002, 5), Index(arg0, 13))

		Store(Index(arg0, 60), Index(arg0, 60))
		Store(Index(arg0, 60), Index(arg0, 61))
		Store(Index(arg0, 62), Index(arg0, 63))
		Store(Index(p001, 60), Index(p001, 60))
		Store(Index(p001, 60), Index(p001, 61))
		Store(Index(p001, 62), Index(p001, 63))
		Store(Index(p002, 60), Index(p002, 60))
		Store(Index(p002, 60), Index(p002, 61))
		Store(Index(p002, 62), Index(p002, 63))

		m004(arg0)
	}

	Method(m006, 1, Serialized)
	{
		Name(p001, Package(100) {0,1})
		Store(Index(arg0, 6), Index(p001, 6))
		Store(Index(p002, 6), Index(p001, 14))
		Store(Index(p001, 6), Index(arg0, 6))
		Store(Index(p002, 6), Index(arg0, 14))

		Store(Index(arg0, 70), Index(arg0, 70))
		Store(Index(arg0, 70), Index(arg0, 71))
		Store(Index(arg0, 72), Index(arg0, 73))
		Store(Index(p001, 70), Index(p001, 70))
		Store(Index(p001, 70), Index(p001, 71))
		Store(Index(p001, 72), Index(p001, 73))
		Store(Index(p002, 70), Index(p002, 70))
		Store(Index(p002, 70), Index(p002, 71))
		Store(Index(p002, 72), Index(p002, 73))

		m005(arg0)
	}

	Method(m007, 1, Serialized)
	{
		Name(p001, Package(100) {0,1})
		Store(Index(arg0, 7), Index(p001, 7))
		Store(Index(p002, 7), Index(p001, 15))
		Store(Index(p001, 7), Index(arg0, 7))
		Store(Index(p002, 7), Index(arg0, 15))

		Store(Index(arg0, 80), Index(arg0, 80))
		Store(Index(arg0, 80), Index(arg0, 81))
		Store(Index(arg0, 82), Index(arg0, 83))
		Store(Index(p001, 80), Index(p001, 80))
		Store(Index(p001, 80), Index(p001, 81))
		Store(Index(p001, 82), Index(p001, 83))
		Store(Index(p002, 80), Index(p002, 80))
		Store(Index(p002, 80), Index(p002, 81))
		Store(Index(p002, 82), Index(p002, 83))

		m006(arg0)
	}

	m007(p000)
	m007(p000)
}

Method(mfeb,, Serialized)
{
	Name(cmd0, 0)

	Name(p000, Package(30) {0,1,2,3,4,5,6,7,8,9})
	Name(p001, Package(31) {0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,0x78,0x79})
	Name(p002, Package(32) {0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,0x88,0x89})
	Name(p003, Package(33) {0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,0x98,0x99})
	Name(p004, Package(34) {0xa0,0xa1,0xa2,0xa3,0xa4,0xa5,0xa6,0xa7,0xa8,0xa9})
	Name(p005, Package(35) {0xb0,0xb1,0xb2,0xb3,0xb4,0xb5,0xb6,0xb7,0xb8,0xb9})
	Name(p006, Package(36) {0xc0,0xc1,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7,0xc8,0xc9})
	Name(p007, Package(37) {0xd0,0xd1,0xd2,0xd3,0xd4,0xd5,0xd6,0xd7,0xd8,0xd9})

	Method(m000, 7, Serialized)
	{
		Name(pp00, Package(64) {0xd0,0xd1,0xd2,0xd3,0xd4,0xd5,0xd6,0xd7})
		Name(pp01, Package(64) {0xd0,0xd1,0xd2,0xd3,0xd4,0xd5,0xd6,0xd7})


		Store(Index(arg0, 0), Index(pp01, 8))
		Store(Index(arg1, 1), Index(pp01, 9))
		Store(Index(arg2, 2), Index(pp01, 10))
		Store(Index(arg3, 3), Index(pp01, 11))
		Store(Index(arg4, 4), Index(pp01, 12))
		Store(Index(arg5, 5), Index(pp01, 13))
		Store(Index(arg6, 6), Index(pp01, 14))
		Store(Index(pp00, 0), Index(pp01, 15))
		Store(Index(pp01, 0), Index(pp01, 16))
		Store(Index(pp01, 9), Index(pp01, 17))
		Store(Index(p000, 0), Index(pp01, 18))
		Store(Index(p001, 0), Index(pp01, 19))
		Store(Index(p002, 0), Index(pp01, 20))
		Store(Index(p003, 0), Index(pp01, 21))
		Store(Index(p004, 0), Index(pp01, 22))
		Store(Index(p005, 0), Index(pp01, 23))
		Store(Index(p006, 0), Index(pp01, 24))

		Store(Index(arg0, 0), Index(pp00, 8))
		Store(Index(arg0, 1), Index(pp00, 9))
		Store(Index(arg0, 2), Index(pp00, 10))
		Store(Index(arg0, 3), Index(pp00, 11))
		Store(Index(arg0, 4), Index(pp00, 12))
		Store(Index(arg0, 5), Index(pp00, 13))
		Store(Index(arg0, 6), Index(pp00, 14))
		Store(Index(pp00, 0), Index(pp00, 15))
		Store(Index(pp01, 0), Index(pp00, 16))
		Store(Index(pp01, 9), Index(pp00, 17))
		Store(Index(p000, 0), Index(pp00, 18))
		Store(Index(p001, 0), Index(pp00, 19))
		Store(Index(p002, 0), Index(pp00, 20))
		Store(Index(p003, 0), Index(pp00, 21))
		Store(Index(p004, 0), Index(pp00, 22))
		Store(Index(p005, 0), Index(pp00, 23))
		Store(Index(p006, 0), Index(pp00, 24))

		Store(Index(arg0, 0), Index(p000, 8))
		Store(Index(arg1, 1), Index(p000, 9))
		Store(Index(arg2, 2), Index(p000, 10))
		Store(Index(arg3, 3), Index(p000, 11))
		Store(Index(arg4, 4), Index(p000, 12))
		Store(Index(arg5, 5), Index(p000, 13))
		Store(Index(arg6, 6), Index(p000, 14))
		Store(Index(pp00, 0), Index(p000, 15))
		Store(Index(pp01, 0), Index(p000, 16))
		Store(Index(pp01, 9), Index(p000, 17))
		Store(Index(p000, 0), Index(p000, 18))
		Store(Index(p001, 0), Index(p000, 19))
		Store(Index(p002, 0), Index(p000, 20))
		Store(Index(p003, 0), Index(p000, 21))
		Store(Index(p004, 0), Index(p000, 22))
		Store(Index(p005, 0), Index(p000, 23))
		Store(Index(p006, 0), Index(p000, 24))

		Store(Index(arg0, 0), Index(p001, 8))
		Store(Index(arg0, 1), Index(p001, 9))
		Store(Index(arg0, 2), Index(p001, 10))
		Store(Index(arg0, 3), Index(p001, 11))
		Store(Index(arg0, 4), Index(p001, 12))
		Store(Index(arg0, 5), Index(p001, 13))
		Store(Index(arg0, 6), Index(p001, 14))
		Store(Index(pp00, 0), Index(p001, 15))
		Store(Index(pp01, 0), Index(p001, 16))
		Store(Index(pp01, 9), Index(p001, 17))
		Store(Index(p000, 0), Index(p001, 18))
		Store(Index(p001, 0), Index(p001, 19))
		Store(Index(p002, 0), Index(p001, 20))
		Store(Index(p003, 0), Index(p001, 21))
		Store(Index(p004, 0), Index(p001, 22))
		Store(Index(p005, 0), Index(p001, 23))
		Store(Index(p006, 0), Index(p001, 24))

		Store(DerefOf(Index(arg0, 3)), Local0)
		if (LNotEqual(Local0, 3)) {
			err("", zFFF, __LINE__, 0, 0, Local0, 3)
		}

		Store(DerefOf(Index(arg1, 3)), Local0)
		if (LNotEqual(Local0, 0x13)) {
			err("", zFFF, __LINE__, 0, 0, Local0, 0x13)
		}

		Store(DerefOf(Index(arg2, 3)), Local0)
		if (LNotEqual(Local0, 0x23)) {
			err("", zFFF, __LINE__, 0, 0, Local0, 0x23)
		}

		Store(DerefOf(Index(arg3, 3)), Local0)
		if (LNotEqual(Local0, 0x33)) {
			err("", zFFF, __LINE__, 0, 0, Local0, 0x33)
		}

		Store(DerefOf(Index(arg4, 3)), Local0)
		if (LNotEqual(Local0, 0x43)) {
			err("", zFFF, __LINE__, 0, 0, Local0, 0x43)
		}

		Store(DerefOf(Index(arg5, 3)), Local0)
		if (LNotEqual(Local0, 0x53)) {
			err("", zFFF, __LINE__, 0, 0, Local0, 0x53)
		}

		Store(DerefOf(Index(arg6, 3)), Local0)
		if (LNotEqual(Local0, 0x63)) {
			err("", zFFF, __LINE__, 0, 0, Local0, 0x63)
		}

		Store(DerefOf(Index(p000, 14)), Local0)
		Store(DerefOf(Local0), Local1)
		if (LNotEqual(Local1, 0x66)) {
			err("", zFFF, __LINE__, 0, 0, Local1, 0x66)
		}

		if (LEqual(cmd0, 1)) {

			Store(p007, arg0)
			Store(p001, arg1)
			Store(p002, arg2)
			Store(p003, arg3)
			Store(p004, arg4)
			Store(p005, arg5)
			Store(p006, arg6)

			Store(Index(arg0, 0), Index(pp01, 8))
			Store(Index(arg1, 1), Index(pp01, 9))
			Store(Index(arg2, 2), Index(pp01, 10))
			Store(Index(arg3, 3), Index(pp01, 11))
			Store(Index(arg4, 4), Index(pp01, 12))
			Store(Index(arg5, 5), Index(pp01, 13))
			Store(Index(arg6, 6), Index(pp01, 14))
			Store(Index(pp00, 0), Index(pp01, 15))
			Store(Index(pp01, 0), Index(pp01, 16))
			Store(Index(pp01, 9), Index(pp01, 17))
			Store(Index(p000, 0), Index(pp01, 18))
			Store(Index(p001, 0), Index(pp01, 19))
			Store(Index(p002, 0), Index(pp01, 20))
			Store(Index(p003, 0), Index(pp01, 21))
			Store(Index(p004, 0), Index(pp01, 22))
			Store(Index(p005, 0), Index(pp01, 23))
			Store(Index(p006, 0), Index(pp01, 24))

			Store(Index(arg0, 0), Index(pp00, 8))
			Store(Index(arg0, 1), Index(pp00, 9))
			Store(Index(arg0, 2), Index(pp00, 10))
			Store(Index(arg0, 3), Index(pp00, 11))
			Store(Index(arg0, 4), Index(pp00, 12))
			Store(Index(arg0, 5), Index(pp00, 13))
			Store(Index(arg0, 6), Index(pp00, 14))
			Store(Index(pp00, 0), Index(pp00, 15))
			Store(Index(pp01, 0), Index(pp00, 16))
			Store(Index(pp01, 9), Index(pp00, 17))
			Store(Index(p000, 0), Index(pp00, 18))
			Store(Index(p001, 0), Index(pp00, 19))
			Store(Index(p002, 0), Index(pp00, 20))
			Store(Index(p003, 0), Index(pp00, 21))
			Store(Index(p004, 0), Index(pp00, 22))
			Store(Index(p005, 0), Index(pp00, 23))
			Store(Index(p006, 0), Index(pp00, 24))

			Store(Index(arg0, 0), Index(p000, 8))
			Store(Index(arg1, 1), Index(p000, 9))
			Store(Index(arg2, 2), Index(p000, 10))
			Store(Index(arg3, 3), Index(p000, 11))
			Store(Index(arg4, 4), Index(p000, 12))
			Store(Index(arg5, 5), Index(p000, 13))
			Store(Index(arg6, 6), Index(p000, 14))
			Store(Index(pp00, 0), Index(p000, 15))
			Store(Index(pp01, 0), Index(p000, 16))
			Store(Index(pp01, 9), Index(p000, 17))
			Store(Index(p000, 0), Index(p000, 18))
			Store(Index(p001, 0), Index(p000, 19))
			Store(Index(p002, 0), Index(p000, 20))
			Store(Index(p003, 0), Index(p000, 21))
			Store(Index(p004, 0), Index(p000, 22))
			Store(Index(p005, 0), Index(p000, 23))
			Store(Index(p006, 0), Index(p000, 24))

			Store(Index(arg0, 0), Index(p001, 8))
			Store(Index(arg0, 1), Index(p001, 9))
			Store(Index(arg0, 2), Index(p001, 10))
			Store(Index(arg0, 3), Index(p001, 11))
			Store(Index(arg0, 4), Index(p001, 12))
			Store(Index(arg0, 5), Index(p001, 13))
			Store(Index(arg0, 6), Index(p001, 14))
			Store(Index(pp00, 0), Index(p001, 15))
			Store(Index(pp01, 0), Index(p001, 16))
			Store(Index(pp01, 9), Index(p001, 17))
			Store(Index(p000, 0), Index(p001, 18))
			Store(Index(p001, 0), Index(p001, 19))
			Store(Index(p002, 0), Index(p001, 20))
			Store(Index(p003, 0), Index(p001, 21))
			Store(Index(p004, 0), Index(p001, 22))
			Store(Index(p005, 0), Index(p001, 23))
			Store(Index(p006, 0), Index(p001, 24))

			Store(DerefOf(Index(arg0, 3)), Local0)
			if (LNotEqual(Local0, 0xd3)) {
				err("", zFFF, __LINE__, 0, 0, Local0, 0xd3)
			}
			Store(DerefOf(Index(arg1, 3)), Local0)
			if (LNotEqual(Local0, 0x73)) {
				err("", zFFF, __LINE__, 0, 0, Local0, 0x73)
			}
			Store(DerefOf(Index(arg2, 3)), Local0)
			if (LNotEqual(Local0, 0x83)) {
				err("", zFFF, __LINE__, 0, 0, Local0, 0x83)
			}
			Store(DerefOf(Index(arg3, 3)), Local0)
			if (LNotEqual(Local0, 0x93)) {
				err("", zFFF, __LINE__, 0, 0, Local0, 0x93)
			}
			Store(DerefOf(Index(arg4, 3)), Local0)
			if (LNotEqual(Local0, 0xa3)) {
				err("", zFFF, __LINE__, 0, 0, Local0, 0xa3)
			}
			Store(DerefOf(Index(arg5, 3)), Local0)
			if (LNotEqual(Local0, 0xb3)) {
				err("", zFFF, __LINE__, 0, 0, Local0, 0xb3)
			}
			Store(DerefOf(Index(arg6, 3)), Local0)
			if (LNotEqual(Local0, 0xc3)) {
				err("", zFFF, __LINE__, 0, 0, Local0, 0xc3)
			}

			Store(DerefOf(Index(p000, 14)), Local0)
			Store(DerefOf(Local0), Local1)
			if (LNotEqual(Local1, 0xc6)) {
				err("", zFFF, __LINE__, 0, 0, Local1, 0xc6)
			}
		}
	}

	Method(m001, 7, Serialized)
	{
		Name(pp00, Package(64) {0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17})
		Name(pp01, Package(64) {0xd0,0xd1,0xd2,0xd3,0xd4,0xd5,0xd6,0xd7})

		m000(arg0,pp00,arg2,arg3,arg4,arg5,arg6)

		if (LEqual(cmd0, 0)) {

			Store(p007, arg0)
			Store(p001, arg1)
			Store(p002, arg2)
			Store(p003, arg3)
			Store(p004, arg4)
			Store(p005, arg5)
			Store(p006, arg6)

			Store(Index(arg0, 0), Index(pp01, 8))
			Store(Index(arg1, 1), Index(pp01, 9))
			Store(Index(arg2, 2), Index(pp01, 10))
			Store(Index(arg3, 3), Index(pp01, 11))
			Store(Index(arg4, 4), Index(pp01, 12))
			Store(Index(arg5, 5), Index(pp01, 13))
			Store(Index(arg6, 6), Index(pp01, 14))
			Store(Index(pp00, 0), Index(pp01, 15))
			Store(Index(pp01, 0), Index(pp01, 16))
			Store(Index(pp01, 9), Index(pp01, 17))
			Store(Index(p000, 0), Index(pp01, 18))
			Store(Index(p001, 0), Index(pp01, 19))
			Store(Index(p002, 0), Index(pp01, 20))
			Store(Index(p003, 0), Index(pp01, 21))
			Store(Index(p004, 0), Index(pp01, 22))
			Store(Index(p005, 0), Index(pp01, 23))
			Store(Index(p006, 0), Index(pp01, 24))

			Store(Index(arg0, 0), Index(pp00, 8))
			Store(Index(arg0, 1), Index(pp00, 9))
			Store(Index(arg0, 2), Index(pp00, 10))
			Store(Index(arg0, 3), Index(pp00, 11))
			Store(Index(arg0, 4), Index(pp00, 12))
			Store(Index(arg0, 5), Index(pp00, 13))
			Store(Index(arg0, 6), Index(pp00, 14))
			Store(Index(pp00, 0), Index(pp00, 15))
			Store(Index(pp01, 0), Index(pp00, 16))
			Store(Index(pp01, 9), Index(pp00, 17))
			Store(Index(p000, 0), Index(pp00, 18))
			Store(Index(p001, 0), Index(pp00, 19))
			Store(Index(p002, 0), Index(pp00, 20))
			Store(Index(p003, 0), Index(pp00, 21))
			Store(Index(p004, 0), Index(pp00, 22))
			Store(Index(p005, 0), Index(pp00, 23))
			Store(Index(p006, 0), Index(pp00, 24))

			Store(Index(arg0, 0), Index(p000, 8))
			Store(Index(arg1, 1), Index(p000, 9))
			Store(Index(arg2, 2), Index(p000, 10))
			Store(Index(arg3, 3), Index(p000, 11))
			Store(Index(arg4, 4), Index(p000, 12))
			Store(Index(arg5, 5), Index(p000, 13))
			Store(Index(arg6, 6), Index(p000, 14))
			Store(Index(pp00, 0), Index(p000, 15))
			Store(Index(pp01, 0), Index(p000, 16))
			Store(Index(pp01, 9), Index(p000, 17))
			Store(Index(p000, 0), Index(p000, 18))
			Store(Index(p001, 0), Index(p000, 19))
			Store(Index(p002, 0), Index(p000, 20))
			Store(Index(p003, 0), Index(p000, 21))
			Store(Index(p004, 0), Index(p000, 22))
			Store(Index(p005, 0), Index(p000, 23))
			Store(Index(p006, 0), Index(p000, 24))

			Store(Index(arg0, 0), Index(p001, 8))
			Store(Index(arg0, 1), Index(p001, 9))
			Store(Index(arg0, 2), Index(p001, 10))
			Store(Index(arg0, 3), Index(p001, 11))
			Store(Index(arg0, 4), Index(p001, 12))
			Store(Index(arg0, 5), Index(p001, 13))
			Store(Index(arg0, 6), Index(p001, 14))
			Store(Index(pp00, 0), Index(p001, 15))
			Store(Index(pp01, 0), Index(p001, 16))
			Store(Index(pp01, 9), Index(p001, 17))
			Store(Index(p000, 0), Index(p001, 18))
			Store(Index(p001, 0), Index(p001, 19))
			Store(Index(p002, 0), Index(p001, 20))
			Store(Index(p003, 0), Index(p001, 21))
			Store(Index(p004, 0), Index(p001, 22))
			Store(Index(p005, 0), Index(p001, 23))
			Store(Index(p006, 0), Index(p001, 24))

			Store(DerefOf(Index(arg0, 3)), Local0)
			if (LNotEqual(Local0, 0xd3)) {
				err("", zFFF, __LINE__, 0, 0, Local0, 0xd3)
			}
			Store(DerefOf(Index(arg1, 3)), Local0)
			if (LNotEqual(Local0, 0x73)) {
				err("", zFFF, __LINE__, 0, 0, Local0, 0x73)
			}
			Store(DerefOf(Index(arg2, 3)), Local0)
			if (LNotEqual(Local0, 0x83)) {
				err("", zFFF, __LINE__, 0, 0, Local0, 0x83)
			}
			Store(DerefOf(Index(arg3, 3)), Local0)
			if (LNotEqual(Local0, 0x93)) {
				err("", zFFF, __LINE__, 0, 0, Local0, 0x93)
			}
			Store(DerefOf(Index(arg4, 3)), Local0)
			if (LNotEqual(Local0, 0xa3)) {
				err("", zFFF, __LINE__, 0, 0, Local0, 0xa3)
			}
			Store(DerefOf(Index(arg5, 3)), Local0)
			if (LNotEqual(Local0, 0xb3)) {
				err("", zFFF, __LINE__, 0, 0, Local0, 0xb3)
			}
			Store(DerefOf(Index(arg6, 3)), Local0)
			if (LNotEqual(Local0, 0xc3)) {
				err("", zFFF, __LINE__, 0, 0, Local0, 0xc3)
			}

			Store(DerefOf(Index(p000, 14)), Local0)
			Store(DerefOf(Local0), Local1)
			if (LNotEqual(Local1, 0xc6)) {
				err("", zFFF, __LINE__, 0, 0, Local1, 0xc6)
			}
		}
	}

	Method(m002, 7, Serialized)
	{
		Name(pp00, Package(64) {0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27})

		m001(arg0,arg1,pp00,arg3,arg4,arg5,arg6)
		Store(pp00, arg0)
	}

	Method(m003, 7, Serialized)
	{
		Name(pp00, Package(64) {0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37})

		m002(arg0,arg1,arg2,pp00,arg4,arg5,arg6)
		Store(pp00, arg0)
	}

	Method(m004, 7, Serialized)
	{
		Name(pp00, Package(64) {0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47})

		m003(arg0,arg1,arg2,arg3,pp00,arg5,arg6)
		Store(pp00, arg0)
	}

	Method(m005, 7, Serialized)
	{
		Name(pp00, Package(64) {0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57})

		m004(arg0,arg1,arg2,arg3,arg4,pp00,arg6)
		Store(pp00, arg0)
	}

	Method(m006, 7, Serialized)
	{
		Name(pp00, Package(64) {0x60,0x61,0x62,0x63,0x64,0x65,0x66,0x67})

		m005(arg0,arg1,arg2,arg3,arg4,arg5,pp00)
		Store(pp00, arg0)
	}

	Store(0, cmd0)
	m006(p000,p001,p002,p003,p004,p005,p006)

	Store(1, cmd0)
	m006(p000,p001,p002,p003,p004,p005,p006)
}

Method(mf01,, Serialized)
{
	Name(i000, 0)
	Name(i001, 1)
	Name(i002, 2)
	Name(i003, 3)

		/* 4-level hierarchy model: 0,1,2,3 */

		Name(pp00, Package(8){0x44})
		Name(pp10, Package(8){0x1044})

		Name(p000, Package() {
			Package() {0x00,0x01,0x02,0x03,Package(8){0x04},0x05,0x06,0x07},
			0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,
			Package() {0x10,0x11,0x12,0x13,Package(8){0x14},0x15,0x16,0x17},
			Package() {0x18},0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f,
			Package() {0x10,0x21,0x22,0x23,Package(8){0x24},0x25,0x26,0x27},
			0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,
			Package() {0x20,0x31,0x32,0x33,Package(8){0x34},0x35,0x36,0x37},
			0x38,0x39,0x3a,0x3b,0x3c,0x3d,0x3e,0x3f,
			Package() {0x30,0x41,0x42,0x43,pp00,0x45,0x46,0x47},
			0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f,
			Package() {0x40,0x51,0x52,0x53,Package(8){0x54},0x55,0x56,0x57},
			0x58,0x59,0x5a,0x5b,0x5c,0x5d,0x5e,0x5f,
			Package() {0x50,0x61,0x62,0x63,Package(8){0x64},0x65,0x66,0x67},
			0x68,0x69,0x6a,0x6b,0x6c,0x6d,0x6e,0x6f,
			Package() {0x60,0x71,0x72,0x73,Package(8){0x74},0x75,0x76,0x77},
			0x78,0x79,0x7a,0x7b,0x7c,0x7d,0x7e,0x7f,
			Package() {0x80,0x81,0x82,0x83,Package(8){0x84},0x85,0x86,0x87},
			Package() {0x88},0x89,0x8a,0x8b,0x8c,0x8d,0x8e,0x8f,
			Package() {0x90,0x91,0x92,0x93,Package(8){0x94},0x95,0x96,0x97},
			Package() {0x98},0x99,0x9a,0x9b,0x9c,0x9d,0x9e,0x9f,
			Package() {0xa0,0xa1,0xa2,0xa3,Package(8){0xa4},0xa5,0xa6,0xa7},
			0xa8,0xa9,0xaa,0xab,0xac,0xad,0xae,0xaf,
			Package() {0xb0,0xb1,0xb2,0xb3,Package(8){0xb4},0xb5,0xb6,0xb7},
			0xb8,0xb9,0xba,0xbb,0xbc,0xbd,0xbe,0xbf,
			Package() {0xc0,0xc1,0xc2,0xc3,Package(8){0xc4},0xc5,0xc6,0xc7},
			0xc8,0xc9,0xca,0xcb,0xcc,0xcd,0xce,0xcf,
			Package() {0xd0,0xd1,0xd2,0xd3,Package(8){0xd4},0xd5,0xd6,0xd7},
			0xd8,0xd9,0xda,0xdb,0xdc,0xdd,0xde,0xdf,
			Package() {0xe0,0xe1,0xe2,0xe3,Package(8){0xe4},0xe5,0xe6,0xe7},
			0xe8,0xe9,0xea,0xeb,0xec,0xed,0xee,0xef,
			Package() {0xf0,0xf1,0xf2,0xf3,Package(8){0xf4},0xf5,0xf6,0xf7},
			0xf8,0xf9,0xfa,0xfb,0xfc,0xfd,0xfe,0xff,
		})

		Name(p001, Package() {
			Package() {0x1000,0x1001,0x1002,0x1003,Package(8){0x1004},0x1005,0x1006,0x1007},
			0x1008,0x1009,0x100a,0x100b,0x100c,0x100d,0x100e,0x100f,
			Package() {0x1010,0x1011,0x1012,0x1013,Package(8){0x1014},0x1015,0x1016,0x1017},
			Package() {0x1018},0x1019,0x101a,0x101b,0x101c,0x101d,0x101e,0x101f,
			Package() {0x1010,0x1021,0x1022,0x1023,Package(8){0x1024},0x1025,0x1026,0x1027},
			0x1028,0x1029,0x102a,0x102b,0x102c,0x102d,0x102e,0x102f,
			Package() {0x1020,0x1031,0x1032,0x1033,Package(8){0x1034},0x1035,0x1036,0x1037},
			0x1038,0x1039,0x103a,0x103b,0x103c,0x103d,0x103e,0x103f,
			Package() {0x1030,0x1041,0x1042,0x1043,pp10,0x1045,0x1046,0x1047},
			0x1048,0x1049,0x104a,0x104b,0x104c,0x104d,0x104e,0x104f,
			Package() {0x1040,0x1051,0x1052,0x1053,Package(8){0x1054},0x1055,0x1056,0x1057},
			0x1058,0x1059,0x105a,0x105b,0x105c,0x105d,0x105e,0x105f,
			Package() {0x1050,0x1061,0x1062,0x1063,Package(8){0x1064},0x1065,0x1066,0x1067},
			0x1068,0x1069,0x106a,0x106b,0x106c,0x106d,0x106e,0x106f,
			Package() {0x1060,0x1071,0x1072,0x1073,Package(8){0x1074},0x1075,0x1076,0x1077},
			0x1078,0x1079,0x107a,0x107b,0x107c,0x107d,0x107e,0x107f,
			Package() {0x1080,0x1081,0x1082,0x1083,Package(8){0x1084},0x1085,0x1086,0x1087},
			Package() {0x1088},0x1089,0x108a,0x108b,0x108c,0x108d,0x108e,0x108f,
			Package() {0x1090,0x1091,0x1092,0x1093,Package(8){0x1094},0x1095,0x1096,0x1097},
			Package() {0x1098},0x1099,0x109a,0x109b,0x109c,0x109d,0x109e,0x109f,
			Package() {0x10a0,0x10a1,0x10a2,0x10a3,Package(8){0x10a4},0x10a5,0x10a6,0x10a7},
			0x10a8,0x10a9,0x10aa,0x10ab,0x10ac,0x10ad,0x10ae,0x10af,
			Package() {0x10b0,0x10b1,0x10b2,0x10b3,Package(8){0x10b4},0x10b5,0x10b6,0x10b7},
			0x10b8,0x10b9,0x10ba,0x10bb,0x10bc,0x10bd,0x10be,0x10bf,
			Package() {0x10c0,0x10c1,0x10c2,0x10c3,Package(8){0x10c4},0x10c5,0x10c6,0x10c7},
			0x10c8,0x10c9,0x10ca,0x10cb,0x10cc,0x10cd,0x10ce,0x10cf,
			Package() {0x10d0,0x10d1,0x10d2,0x10d3,Package(8){0x10d4},0x10d5,0x10d6,0x10d7},
			0x10d8,0x10d9,0x10da,0x10db,0x10dc,0x10dd,0x10de,0x10df,
			Package() {0x10e0,0x10e1,0x10e2,0x10e3,Package(8){0x10e4},0x10e5,0x10e6,0x10e7},
			0x10e8,0x10e9,0x10ea,0x10eb,0x10ec,0x10ed,0x10ee,0x10ef,
			Package() {0x10f0,0x10f1,0x10f2,0x10f3,Package(8){0x10f4},0x10f5,0x10f6,0x10f7},
			0x10f8,0x10f9,0x10fa,0x10fb,0x10fc,0x10fd,0x10fe,0x10ff,
		})

		/*
		 * Store additionally IRefs into Named.
		 * Test is not correct and completed.
		 * Develop it after Bug 127 resolving.
		 */
		Method(m004)
		{
			Store(Index(DerefOf(Index(DerefOf(Index(p000, 0)), 4)), 0), Local0)
			CopyObject(Local0, i000)

			CopyObject(Index(DerefOf(Index(DerefOf(Index(p001, 0)), 4)), 0), Local0)
			CopyObject(Local0, i001)

			m005(i000, 0)
			m005(i001, 1)

			/* The same repeatedly */

			Store(Index(DerefOf(Index(DerefOf(Index(p000, 0)), 4)), 0), Local0)
			CopyObject(Local0, i000)

			CopyObject(Index(DerefOf(Index(DerefOf(Index(p001, 0)), 4)), 0), Local0)
			CopyObject(Local0, i001)

			m005(i000, 0)
			m005(i001, 1)

			/* Directly by CopyObject */

			CopyObject(Index(DerefOf(Index(DerefOf(Index(p000, 0)), 4)), 0), i000)
			CopyObject(Index(DerefOf(Index(DerefOf(Index(p000, 1)), 4)), 0), i001)

			m005(i000, 0)
			m005(i001, 1)
		}

		Method(m005, 2)
		{
			Store(DerefOf(arg0), Local0)
			if (LNotEqual(Local0, arg1)) {
				err("", zFFF, __LINE__, 0, 0, Local0, arg1)
			}
		}

		/*
		 * Store additionally IRefs into LocalX
		 * (Identical to m004).
		 */
		Method(m006)
		{
			Store(Index(DerefOf(Index(DerefOf(Index(p000, 0)), 4)), 0), Local0)
			Store(Index(DerefOf(Index(DerefOf(Index(p001, 0)), 4)), 0), Local1)

			m005(Local0, 0x0004)
			m005(Local1, 0x1004)

			/* The same repeatedly */

			Store(Index(DerefOf(Index(DerefOf(Index(p000, 0)), 4)), 0), Local0)
			Store(Index(DerefOf(Index(DerefOf(Index(p001, 0)), 4)), 0), Local1)

			m005(Local0, 0x0004)
			m005(Local1, 0x1004)
		}

		/*
		 * Store additionally ORef into packages.
		 */
		Method(m007, 3, Serialized)
		{
			Name(ii00, 0)
			Name(ii01, 0)
			Name(ii02, 0)

			/* ORef to LocalX */

			Store(RefOf(Local0), Index(p000, 2))
			Store(RefOf(Local1), Index(p000, 3))
			Store(RefOf(Local2), Index(p000, 4))

			Store(RefOf(Local0), Index(p001, 2))
			Store(RefOf(Local1), Index(p001, 3))
			Store(RefOf(Local2), Index(p001, 4))

			Store(RefOf(Local0), Index(arg0, 5))
			Store(RefOf(Local1), Index(arg0, 6))
			Store(RefOf(Local2), Index(arg0, 7))

			Store(RefOf(Local0), Index(arg1, 5))
			Store(RefOf(Local1), Index(arg1, 6))
			Store(RefOf(Local2), Index(arg1, 7))

			/* ORef to ArgX */

			Store(RefOf(arg2), Index(p000, 20))
			Store(RefOf(arg2), Index(p000, 21))
			Store(RefOf(arg2), Index(p000, 22))

			Store(RefOf(arg2), Index(p001, 20))
			Store(RefOf(arg2), Index(p001, 21))
			Store(RefOf(arg2), Index(p001, 22))

			Store(RefOf(arg2), Index(arg0, 23))
			Store(RefOf(arg2), Index(arg0, 24))
			Store(RefOf(arg2), Index(arg0, 25))

			Store(RefOf(arg2), Index(arg1, 23))
			Store(RefOf(arg2), Index(arg1, 24))
			Store(RefOf(arg2), Index(arg1, 25))

			/* ORef to Named */

			Store(RefOf(ii00), Index(p000, 29))
			Store(RefOf(ii01), Index(p000, 30))
			Store(RefOf(ii02), Index(p000, 31))

			Store(RefOf(ii00), Index(p001, 29))
			Store(RefOf(ii01), Index(p001, 30))
			Store(RefOf(ii02), Index(p001, 31))

			Store(RefOf(ii00), Index(arg0, 32))
			Store(RefOf(ii01), Index(arg0, 33))
			Store(RefOf(ii02), Index(arg0, 34))

			Store(RefOf(ii00), Index(arg1, 32))
			Store(RefOf(ii01), Index(arg1, 33))
			Store(RefOf(ii02), Index(arg1, 34))

			/* ORef to Named */

			Store(RefOf(i000), Index(p000, 39))
			Store(RefOf(i001), Index(p000, 40))
			Store(RefOf(i002), Index(p000, 41))

			Store(RefOf(i000), Index(p001, 39))
			Store(RefOf(i001), Index(p001, 40))
			Store(RefOf(i002), Index(p001, 41))

			Store(RefOf(i000), Index(arg0, 42))
			Store(RefOf(i001), Index(arg0, 43))
			Store(RefOf(i002), Index(arg0, 44))

			Store(RefOf(i000), Index(arg1, 42))
			Store(RefOf(i001), Index(arg1, 43))
			Store(RefOf(i002), Index(arg1, 44))
		}

		Method(m000, 3)
		{
			Store(DerefOf(Index(DerefOf(Index(DerefOf(Index(arg0, arg1)), 4)), 0)), Local0)
			if (LNotEqual(Local0, arg2)) {
				err("", zFFF, __LINE__, 0, 0, Local0, arg2)
			}
		}

		Method(m001, 3)
		{
			Store(arg2, Index(DerefOf(Index(DerefOf(Index(arg0, arg1)), 4)), 0))
		}

		Method(m002, 3)
		{
			Store(DerefOf(DerefOf(Index(DerefOf(Index(DerefOf(Index(arg0, arg1)), 4)), 0))), Local0)
			if (LNotEqual(Local0, arg2)) {
				err("", zFFF, __LINE__, 0, 0, Local0, arg2)
			}
		}

		Method(m003, 3)
		{
			Store(DerefOf(DerefOf(Index(arg0, arg1))), Local0)
			if (LNotEqual(Local0, arg2)) {
				err("", zFFF, __LINE__, 0, 0, Local0, arg2)
			}
		}

		m000(p000, 0, 0x0004)
		m000(p000, 9, 0x0014)
		m000(p000, 18, 0x0024)
		m000(p000, 27, 0x0034)
		m000(p000, 36, 0x0044)
		m000(p000, 45, 0x0054)
		m000(p000, 54, 0x0064)
		m000(p000, 63, 0x0074)
		m000(p000, 72, 0x0084)
		m000(p000, 81, 0x0094)
		m000(p000, 90, 0x00a4)
		m000(p000, 99, 0x00b4)
		m000(p000, 108, 0x00c4)
		m000(p000, 117, 0x00d4)
		m000(p000, 126, 0x00e4)
		m000(p000, 135, 0x00f4)

		m000(p001, 0, 0x1004)
		m000(p001, 9, 0x1014)
		m000(p001, 18, 0x1024)
		m000(p001, 27, 0x1034)
		m000(p001, 36, 0x1044)
		m000(p001, 45, 0x1054)
		m000(p001, 54, 0x1064)
		m000(p001, 63, 0x1074)
		m000(p001, 72, 0x1084)
		m000(p001, 81, 0x1094)
		m000(p001, 90, 0x10a4)
		m000(p001, 99, 0x10b4)
		m000(p001, 108, 0x10c4)
		m000(p001, 117, 0x10d4)
		m000(p001, 126, 0x10e4)
		m000(p001, 135, 0x10f4)


		/* 3-th level access */

		/* Store IRef to element of p000 into element of p001 */

		Store(Index(DerefOf(Index(DerefOf(Index(p000, 0)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p001, 72)), 4)), 0))
		m002(p001, 72, 0x0004)

		Store(Index(DerefOf(Index(DerefOf(Index(p000, 9)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p001, 81)), 4)), 0))
		m002(p001, 81, 0x0014)

		Store(Index(DerefOf(Index(DerefOf(Index(p000, 18)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p001, 90)), 4)), 0))
		m002(p001, 90, 0x0024)

		Store(Index(DerefOf(Index(DerefOf(Index(p000, 27)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p001, 99)), 4)), 0))
		m002(p001, 99, 0x0034)

		Store(Index(DerefOf(Index(DerefOf(Index(p000, 36)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p001, 108)), 4)), 0))
		m002(p001, 108, 0x0044)

		Store(Index(DerefOf(Index(DerefOf(Index(p000, 45)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p001, 117)), 4)), 0))
		m002(p001, 117, 0x0054)

		Store(Index(DerefOf(Index(DerefOf(Index(p000, 54)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p001, 126)), 4)), 0))
		m002(p001, 126, 0x0064)

		Store(Index(DerefOf(Index(DerefOf(Index(p000, 63)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p001, 135)), 4)), 0))
		m002(p001, 135, 0x0074)

		/* Store IRef to element of p001 into element of p000 */

		Store(Index(DerefOf(Index(DerefOf(Index(p001, 0)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p000, 72)), 4)), 0))
		m002(p000, 72, 0x1004)

		Store(Index(DerefOf(Index(DerefOf(Index(p001, 9)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p000, 81)), 4)), 0))
		m002(p000, 81, 0x1014)

		Store(Index(DerefOf(Index(DerefOf(Index(p001, 18)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p000, 90)), 4)), 0))
		m002(p000, 90, 0x1024)

		Store(Index(DerefOf(Index(DerefOf(Index(p001, 27)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p000, 99)), 4)), 0))
		m002(p000, 99, 0x1034)

		Store(Index(DerefOf(Index(DerefOf(Index(p001, 36)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p000, 108)), 4)), 0))
		m002(p000, 108, 0x1044)

		Store(Index(DerefOf(Index(DerefOf(Index(p001, 45)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p000, 117)), 4)), 0))
		m002(p000, 117, 0x1054)

		Store(Index(DerefOf(Index(DerefOf(Index(p001, 54)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p000, 126)), 4)), 0))
		m002(p000, 126, 0x1064)

		Store(Index(DerefOf(Index(DerefOf(Index(p001, 63)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p000, 135)), 4)), 0))
		m002(p000, 135, 0x1074)


		/* The same repeatedly */

		/* Store IRef to element of p000 into element of p001 */

		Store(Index(DerefOf(Index(DerefOf(Index(p000, 0)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p001, 72)), 4)), 0))
		m002(p001, 72, 0x0004)

		Store(Index(DerefOf(Index(DerefOf(Index(p000, 9)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p001, 81)), 4)), 0))
		m002(p001, 81, 0x0014)

		Store(Index(DerefOf(Index(DerefOf(Index(p000, 18)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p001, 90)), 4)), 0))
		m002(p001, 90, 0x0024)

		Store(Index(DerefOf(Index(DerefOf(Index(p000, 27)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p001, 99)), 4)), 0))
		m002(p001, 99, 0x0034)

		Store(Index(DerefOf(Index(DerefOf(Index(p000, 36)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p001, 108)), 4)), 0))
		m002(p001, 108, 0x0044)

		Store(Index(DerefOf(Index(DerefOf(Index(p000, 45)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p001, 117)), 4)), 0))
		m002(p001, 117, 0x0054)

		Store(Index(DerefOf(Index(DerefOf(Index(p000, 54)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p001, 126)), 4)), 0))
		m002(p001, 126, 0x0064)

		Store(Index(DerefOf(Index(DerefOf(Index(p000, 63)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p001, 135)), 4)), 0))
		m002(p001, 135, 0x0074)

		/* Store IRef to element of p001 into element of p000 */

		Store(Index(DerefOf(Index(DerefOf(Index(p001, 0)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p000, 72)), 4)), 0))
		m002(p000, 72, 0x1004)

		Store(Index(DerefOf(Index(DerefOf(Index(p001, 9)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p000, 81)), 4)), 0))
		m002(p000, 81, 0x1014)

		Store(Index(DerefOf(Index(DerefOf(Index(p001, 18)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p000, 90)), 4)), 0))
		m002(p000, 90, 0x1024)

		Store(Index(DerefOf(Index(DerefOf(Index(p001, 27)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p000, 99)), 4)), 0))
		m002(p000, 99, 0x1034)

		Store(Index(DerefOf(Index(DerefOf(Index(p001, 36)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p000, 108)), 4)), 0))
		m002(p000, 108, 0x1044)

		Store(Index(DerefOf(Index(DerefOf(Index(p001, 45)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p000, 117)), 4)), 0))
		m002(p000, 117, 0x1054)

		Store(Index(DerefOf(Index(DerefOf(Index(p001, 54)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p000, 126)), 4)), 0))
		m002(p000, 126, 0x1064)

		Store(Index(DerefOf(Index(DerefOf(Index(p001, 63)), 4)), 0),
			Index(DerefOf(Index(DerefOf(Index(p000, 135)), 4)), 0))
		m002(p000, 135, 0x1074)

		/* Restore the initial state of Packages */

		m001(p000, 72, 0x0084)
		m001(p000, 81, 0x0094)
		m001(p000, 90, 0x00a4)
		m001(p000, 99, 0x00b4)
		m001(p000, 108, 0x00c4)
		m001(p000, 117, 0x00d4)
		m001(p000, 126, 0x00e4)
		m001(p000, 135, 0x00f4)

		m001(p001, 72, 0x1084)
		m001(p001, 81, 0x1094)
		m001(p001, 90, 0x10a4)
		m001(p001, 99, 0x10b4)
		m001(p001, 108, 0x10c4)
		m001(p001, 117, 0x10d4)
		m001(p001, 126, 0x10e4)
		m001(p001, 135, 0x10f4)

		/* Check the initial state of Packages */

		m000(p000, 0, 0x0004)
		m000(p000, 9, 0x0014)
		m000(p000, 18, 0x0024)
		m000(p000, 27, 0x0034)
		m000(p000, 36, 0x0044)
		m000(p000, 45, 0x0054)
		m000(p000, 54, 0x0064)
		m000(p000, 63, 0x0074)
		m000(p000, 72, 0x0084)
		m000(p000, 81, 0x0094)
		m000(p000, 90, 0x00a4)
		m000(p000, 99, 0x00b4)
		m000(p000, 108, 0x00c4)
		m000(p000, 117, 0x00d4)
		m000(p000, 126, 0x00e4)
		m000(p000, 135, 0x00f4)

		m000(p001, 0, 0x1004)
		m000(p001, 9, 0x1014)
		m000(p001, 18, 0x1024)
		m000(p001, 27, 0x1034)
		m000(p001, 36, 0x1044)
		m000(p001, 45, 0x1054)
		m000(p001, 54, 0x1064)
		m000(p001, 63, 0x1074)
		m000(p001, 72, 0x1084)
		m000(p001, 81, 0x1094)
		m000(p001, 90, 0x10a4)
		m000(p001, 99, 0x10b4)
		m000(p001, 108, 0x10c4)
		m000(p001, 117, 0x10d4)
		m000(p001, 126, 0x10e4)
		m000(p001, 135, 0x10f4)


		/* 1-th level access */

		/* Store IRef to element of p000 into element of p001 */

		Store(Index(p000, 1), Index(p001, 72))
		m003(p001, 72, 0x0008)

		Store(Index(p000, 19), Index(p001, 81))
		m003(p001, 81, 0x0028)

		Store(Index(p000, 28), Index(p001, 90))
		m003(p001, 90, 0x0038)

		Store(Index(p000, 37), Index(p001, 99))
		m003(p001, 99, 0x0048)

		Store(Index(p000, 46), Index(p001, 108))
		m003(p001, 108, 0x0058)

		Store(Index(p000, 55), Index(p001, 117))
		m003(p001, 117, 0x0068)

		Store(Index(p000, 64), Index(p001, 126))
		m003(p001, 126, 0x0078)

		Store(Index(p000, 71), Index(p001, 135))
		m003(p001, 135, 0x007f)

		/* Store IRef to element of p001 into element of p000 */

		Store(Index(p001, 1), Index(p000, 72))
		m003(p000, 72, 0x1008)

		Store(Index(p001, 19), Index(p000, 81))
		m003(p000, 81, 0x1028)

		Store(Index(p001, 28), Index(p000, 90))
		m003(p000, 90, 0x1038)

		Store(Index(p001, 37), Index(p000, 99))
		m003(p000, 99, 0x1048)

		Store(Index(p001, 46), Index(p000, 108))
		m003(p000, 108, 0x1058)

		Store(Index(p001, 55), Index(p000, 117))
		m003(p000, 117, 0x1068)

		Store(Index(p001, 64), Index(p000, 126))
		m003(p000, 126, 0x1078)

		Store(Index(p001, 71), Index(p000, 135))
		m003(p000, 135, 0x107f)

		if (y127) {
			m004()
		}

		m006()
		m007(p000, p001, 0x12345678)
}

Method(mfca)
{
	SRMT("mfcb")
	mfcb()

	SRMT("mfcf")
	mfcf()

	SRMT("mfd0")
	mfd0()

	SRMT("mfd1")
	mfd1()

	SRMT("mfd2")
	mfd2()

	SRMT("mfd3")
	mfd3()

	SRMT("mfd4")
	mfd4()

	SRMT("mfd5")
	mfd5()

	SRMT("mfd6")
	mfd6()

	SRMT("mfd7")
	mfd7(0,0,0,0,0,0,0)

	SRMT("mfe9")
	mfe9()

	SRMT("mfea")
	mfea()

	SRMT("mfeb")
	mfeb()

	SRMT("mf01")
	mf01()
}
