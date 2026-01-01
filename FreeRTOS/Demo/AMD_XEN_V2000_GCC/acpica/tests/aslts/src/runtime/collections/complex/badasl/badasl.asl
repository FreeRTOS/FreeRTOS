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
 * The tests which require utilyzing of
 * the -f option on the ASL compilation
 * stage.
 *
 * (ASL-incorrect tests compiled with -f option of ASL)
 *
 * ASL Compiler:
 *
 *   -f  -  Ignore errors, force creation of AML output file(s)
 */

Name(z146, 146)

/*
 *         Name(n000, 0)
 * Error 1034 - ^ Name already exists in scope (N000)
 */
Method(m101,, Serialized)
{
	Name(ts, "m101")

	Name (VV, 0x1234)
	Store (32, Local0)

	CH03(ts, z146, 0, __LINE__, 0)

	Name (VV, 0xBBBBAAAA)
	Store (12, Local2)

	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)
}

/*
 * The test is intended to check that interpreter issue an
 * exception when detects that the actual number of elements
 * in Package is greater than the value of NumElements. But,
 * ACPICA ASL Compiler run with -f option replaces the specified
 * value of NumElements by the actual number of elements in
 * PackageList. So - no exceptions. We can't specify the ASL
 * test - because we can't obtain AML code of Package with the
 * actual number of elements in it greater than the value of
 * NumElements.
 *
 * So, the test is inefficient.
 *
 * Name (p000, Package(3) {0xabcd0000, 0xabcd0001, 0xabcd0002, 0xabcd0003})
 * Error 4046 - Initializer list too long ^
 */
Method(m102,, Serialized)
{
	Name(ts, "m102")

	Name (p000, Package(3) {0xabcd0000, 0xabcd0001, 0xabcd0002, 0xabcd0003})

	CH03(ts, z146, 2, __LINE__, 0)
	Store(DerefOf(Index(p000, 3)), Local0)
	CH03(ts, z146, 2, __LINE__, 0)
}

/*
 * Exception on Acquire.
 * Access to inappropriate type data.
 */
Method(m103,, Serialized)
{
	Name(ts, "m103")
	Name(i900, 0xfe7cb391d65a0000)
	Name(s900, "12340002")
	Name(b900, Buffer() {0xb0,0xb1,0xb2,0xb3,0xb4})
	Name(b9Z0, Buffer() {0xb0,0xb1,0xb2,0xb3,0xb4})
	Name(p900, Package(1) {})

	Event(e900)
	Mutex(mx90, 0)
	Device(d900) { Name(i900, 0xabcd0017) }
	ThermalZone(tz90) {}
	Processor(pr90, 0, 0xFFFFFFFF, 0) {}
	PowerResource(pw90, 1, 0) {Method(mmmm){return (0)}}
	OperationRegion(r900, SystemMemory, 0x100, 0x100)
	OperationRegion(r9Z0, SystemMemory, 0x100, 0x100)

	CreateField(b9Z0, 0, 8, bf90)
	Field(r9Z0, ByteAcc, NoLock, Preserve) {f900,8,f901,8,f902,8,f903,8}
	BankField(r9Z0, f901, 0, ByteAcc, NoLock, Preserve) {bn90,4}
	IndexField(f902, f903, ByteAcc, NoLock, Preserve) {if90,8,if91,8}

	/* Acquire */

	CH03(ts, z146, 0, __LINE__, 0)
	Acquire(i900, 0xffff)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Acquire(s900, 0xffff)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Acquire(b900, 0xffff)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Acquire(p900, 0xffff)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Acquire(e900, 0xffff)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Acquire(d900, 0xffff)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Acquire(tz90, 0xffff)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Acquire(pr90, 0xffff)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Acquire(pw90, 0xffff)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Acquire(r900, 0xffff)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Acquire(bf90, 0xffff)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Acquire(f900, 0xffff)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Acquire(bn90, 0xffff)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Acquire(if90, 0xffff)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)


	/* Release */

	CH03(ts, z146, 0, __LINE__, 0)
	Release(i900)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Release(s900)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Release(b900)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Release(p900)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Release(e900)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Release(d900)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Release(tz90)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Release(pr90)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Release(pw90)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Release(r900)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Release(bf90)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Release(f900)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Release(bn90)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)

	CH03(ts, z146, 0, __LINE__, 0)
	Release(if90)
	CH04(ts, 0, 0xff, z146, __LINE__, 0, 0)
}

// Run-method
Method(m100)
{
	SRMT("m101")
	m101()

	SRMT("m102")
	m102()

	SRMT("m103")
	m103()
}
