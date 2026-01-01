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
 * Tests originated from bdemo/0262
 */

Name(z162, 162)

/*
 * Bug 262 (Fiodor Suietov):
 *
 * SUMMARY: Unexpected AE_STACK_OVERFLOW for a method call expression with nested calls
 */
Method(ms00,, Serialized)
{
	Name(ts, "ms00")

	Name(iad1, 0x1)
	Name(iad2, 0x10)
	Name(iad3, 0x100)
	Name(iad4, 0x1000)
	Name(iad5, 0x10000)
	Name(iad6, 0x100000)
	Name(iad7, 0x1000000)

	Method(mad1, 1) {Return(Arg0)}
	Method(mad7, 7) {Return(Add(Add(Add(Add(Add(Add(Arg0, Arg1), Arg2), Arg3), Arg4), Arg5), Arg6))}

	Method(m000)
	{
		Store(mad7(mad1(iad1), mad1(iad2), mad1(iad3), mad1(iad4), mad1(iad5), mad1(iad6),
			mad7(mad1(iad1), mad1(iad2), mad1(iad3), mad1(iad4), mad1(iad5), mad1(iad6),
			mad7(mad1(iad1), mad1(iad2), mad1(iad3), mad1(iad4), mad1(iad5), mad1(iad6),
			mad7(mad1(iad1), mad1(iad2), mad1(iad3), mad1(iad4), mad1(iad5), mad1(iad6),
			mad7(mad1(iad1), mad1(iad2), mad1(iad3), mad1(iad4), mad1(iad5), mad1(iad6),
			mad7(mad1(iad1), mad1(iad2), mad1(iad3), mad1(iad4), mad1(iad5), mad1(iad6),
			mad7(mad1(iad1), mad1(iad2), mad1(iad3), mad1(iad4), mad1(iad5), mad1(iad6),
			mad1(iad7)))))))), Local0)

		Store (Local0, Debug)

		if (LNotEqual(Local0, 0x1777777)) {
			err(ts, z162, __LINE__, 0, 0, Local0, 0x1777777)
		}
	}

	CH03(ts, z162, 0x001, __LINE__, 0)
	m000()
	CH03(ts, z162, 0x002, __LINE__, 0)
}

/*
 * This is how MS actually works
 */
Method(ms01, 1, Serialized)
{
	Name(ts, "ms01")
	Name(i000, 0)
	Name(b000, Buffer(9) {0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18})
	CreateField(b000, 0, 8, bf00)

	Name(tp00, 0)

	Method(m000, 1)
	{
		Store(ObjectType(arg0), Local0)
		if (LNotEqual(Local0, tp00)) {
			err(ts, z162, __LINE__, 0, 0, Local0, tp00)
		}
	}

	// This is how it should be:
	Store(c009, tp00)

	// This is how MS actually works:
	Store(c00b, tp00)


	Store(ObjectType(bf00), Local0)
	if (LNotEqual(Local0, c016)) {
		err(ts, z162, __LINE__, 0, 0, Local0, c016)
	}

	m000(bf00)

	Store(bf00, i000)
	Store(ObjectType(i000), Local0)
	if (LNotEqual(Local0, c009)) {
		err(ts, z162, __LINE__, 0, 0, Local0, c009)
	}

	Store(bf00, Local1)
	Store(ObjectType(Local1), Local0)
	if (LNotEqual(Local0, tp00)) {
		err(ts, z162, __LINE__, 0, 0, Local0, tp00)
	}

	Store(bf00, arg0)
	Store(ObjectType(arg0), Local0)
	if (LNotEqual(Local0, tp00)) {
		err(ts, z162, __LINE__, 0, 0, Local0, tp00)
	}
}

/*
 * This is how MS actually works
 */
Method(ms02, 1, Serialized)
{
	Name(ts, "ms02")
	Name(i000, 0)
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) { f000, 8 }

	Name(tp00, 0)

	Method(m000, 1)
	{
		Store(ObjectType(arg0), Local0)
		if (LNotEqual(Local0, tp00)) {
			err(ts, z162, __LINE__, 0, 0, Local0, tp00)
		}
	}

	Store(c009, tp00)

	Store(ObjectType(f000), Local0)
	if (LNotEqual(Local0, c00d)) {
		err(ts, z162, __LINE__, 0, 0, Local0, c00d)
	}

	m000(f000)

	Store(f000, i000)
	Store(ObjectType(i000), Local0)
	if (LNotEqual(Local0, c009)) {
		err(ts, z162, __LINE__, 0, 0, Local0, c009)
	}

	Store(f000, Local1)
	Store(ObjectType(Local1), Local0)
	if (LNotEqual(Local0, tp00)) {
		err(ts, z162, __LINE__, 0, 0, Local0, tp00)
	}

	Store(f000, arg0)
	Store(ObjectType(arg0), Local0)
	if (LNotEqual(Local0, tp00)) {
		err(ts, z162, __LINE__, 0, 0, Local0, tp00)
	}
}

/*
 * Bug 275:
 *
 * SUMMARY: Pop result from bottom principle doesn't work
 */
Method(ms03,, Serialized)
{
	Name(i000, 0x11000000)
	Name(i001, 0x00220000)
	Name(p000, Package () {0xabcd0000, 0xabcd0001, 0xabcd0002})

	Method(m000)
	{
		Return (p000)
	}

	Method(m001, 1)
	{
		Return (0xabcd0003)
	}

	Method(m002, 2)
	{
		Index(arg0, 1, Local0)
		Store(DerefOf(Local0), Local1)

		if (LNotEqual(Local1, 0xabcd0001)) {
			err("ms03", z162, __LINE__, 0, 0, Local0, c00d)
		}
	}

	// Works correctly:
	m002(p000, 0xabcd0004)
	m002(m000(), 0xabcd0004)
	m002(p000, m001(Add(i000, i001)))

	// Works incorrectly (bug 275):
	m002(m000(), m001(Add(i000, i001)))
}

Method(msff)
{
	SRMT("ms00")
	if (y262) {
		ms00()
	} else {
		BLCK()
	}

	SRMT("ms01")
	ms01(0)
	SRMT("ms02")
	ms02(0)
	SRMT("ms03")
	if (y275) {
		ms03()
	} else {
		BLCK()
	}
}
