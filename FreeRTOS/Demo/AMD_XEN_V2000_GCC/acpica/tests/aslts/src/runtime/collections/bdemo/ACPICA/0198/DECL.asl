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
 * Bug 198:
 *
 * SUMMARY: AML interpretation in 32-bit slack mode becomes unstable after some exceptions
 */

/* SEE below: "Would be useful to continue for other ASL operators" */

Name(id24, 0)

Method(mfa9,, Serialized) {

	Event(e900)
	Event(e9Z0)
	Mutex(mx90, 0)
	Mutex(mx91, 0)
	Device(d900) { Name(i900, 0xabcd0017) }
	Device(d9Z0) { Name(i900, 0xabcd0017) }
	ThermalZone(tz90) {}
	ThermalZone(tz91) {}
	Processor(pr90, 0, 0xFFFFFFFF, 0) {}
	Processor(pr91, 0, 0xFFFFFFFF, 0) {}
	OperationRegion(r900, SystemMemory, 0x100, 0x100)
	OperationRegion(r9Z0, SystemMemory, 0x100, 0x100)
	PowerResource(pw90, 1, 0) {Method(mmmm){return (0)}}
	PowerResource(pw91, 1, 0) {Method(mmmm){return (0)}}

	Name(RMRC, 0)
	Name(NRMT, "QQQQ")
	Name(CTST, "CTST")
	Name(RR44, Package(8) {})
	Name(RR55, Package(8) {})
	Name(s000, "The expected contents of 0-th elements of both Packages - RR44 and RR55")

	// Error checking
	Method(m000, 1) {
		Store("======================================== sit 1", Debug)
		Store(arg0, Debug)
		Store(RMRC, Debug)
		Store(DerefOf(Index(RR44, 0)), Debug)
		Store(DerefOf(Index(RR55, 0)), Debug)

		Store(DerefOf(Index(RR44, 0)), Local0)
		Store(DerefOf(Index(RR55, 0)), Local1)

		if (LNotEqual(Local0, s000)) {
			// Store("Error 0", Debug)
			err("", zFFF, __LINE__, 0, 0, Local0, s000)
		}
		if (LNotEqual(Local1, s000)) {
			// Store("Error 1", Debug)
			err("", zFFF, __LINE__, 0, 0, Local0, s000)
		}

		Store("========================================.", Debug)
	}

	Method(m001,, Serialized) {

		Name(b000, Buffer(4) {})

		if (SizeOf(NRMT)) {
			Store("vvvvvv", Local0)
			Concatenate(Local0, "PASS:", Local1)
			Concatenate(":", CTST, Local0)

			// This - eliminates the effect
			// Store(s000, Local0)

			Store("The expected contents of 0-th elements of both Packages - RR44 and RR55", Local0)

			// The order of RR55 and RR44 is essential, only the first is then corrupted:

			Store(Local0, Index(RR44, RMRC))
			Store(Local0, Index(RR55, RMRC))

			m000(0x1000)
//			m000()

			Increment(RMRC)
		}

		m000(0x1001)
//		m000()
	}

	Method(m002)
	{
		Store("ZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ RR44", Index(RR44, 0))
		Store("ZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ RR55", Index(RR55, 0))

		Store(10000000000, Local0)
		Store(0, Local1)

		if (LEqual(id24, 0)) {
			// Only this causes the effect:
			ToBCD(Local0, Local2)
		} elseif (LEqual(id24, 1)) {
			Divide(1, Local1, Local2)
		} elseif (LEqual(id24, 2)) {
			Divide(1, Local1, Local7, Local2)
		} elseif (LEqual(id24, 3)) {
			Store(SizeOf(d9Z0), Local2)
		} elseif (LEqual(id24, 4)) {
			Store(0, Local0)
			Store(Acquire (Local0, 1), Local2)
		} elseif (LEqual(id24, 5)) {
			CopyObject(e900, Local0)
			Add(0, Local0, Local2)
		} elseif (LEqual(id24, 6)) {
			CopyObject(e900, Local0)
			And(0, Local0, Local2)
		} elseif (LEqual(id24, 7)) {
			Store("zzzzzxx", Local0)
			CopyObject(e900, Local1)
			Concatenate(Local0, Local1, Local2)
		} elseif (LEqual(id24, 8)) {
			CopyObject(e900, Local0)
			CondRefOf(Local0, Local2)
		}

		if (LNotEqual(Local2, 0)) {
			Store("Zizi 012345", Debug)
		}

		// If you uncomment this Store the effect will disappear

		// Store(0, Local0)
	}


	// If you uncomment this Store then another one of RR44 and RR55 will be corrupted
	// (see comment to m001)

	// Store("m002", NRMT)

//	Store("--------------!!!!!!!!!!!--------- RR44", Debug)
//	Store(Index(RR44, 0), Debug)
//	Store("--------------!!!!!!!!!!!--------- RR55", Debug)
//	Store(Index(RR55, 0), Debug)
	Store("---------------------------------- SSSSSSSS 0", Debug)

	CH03("", 0, 0x002, __LINE__, 0)
	m002()

//	Store("---------------------------------- SSSSSSSS 1", Debug)

	m001()

//	Store("---------------------------------- SSSSSSSS 2", Debug)

	m000(0x1009)

//	m000()

	if (LEqual(id24, 0)) {
		if (F64) {
			CH03("", 0, 0x003, __LINE__, 0)
		} else {
			CH04("", 0, 0xff, 0, __LINE__, 0, 0) // AE_AML_NUMERIC_OVERFLOW
		}
	} else {
		CH04("", 0, 0xff, 0, __LINE__, 0, 0) // AE_AML_NUMERIC_OVERFLOW
	}
}

Method(mfaa) {

	Store(0, id24)
	mfa9()

	Store(1, id24)
	mfa9()

	Store(2, id24)
	mfa9()

	Store(3, id24)
	mfa9()

	Store(4, id24)
	mfa9()

	Store(5, id24)
	mfa9()

	Store(6, id24)
	mfa9()

	Store(7, id24)
	mfa9()

	Store(8, id24)
	mfa9()

	/* Would be useful to continue for other ASL operators */
}
