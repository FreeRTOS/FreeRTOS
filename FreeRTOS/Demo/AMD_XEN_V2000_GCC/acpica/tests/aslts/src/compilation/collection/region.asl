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

// Operation Regions


Method(mb00)
{
	//     Field(arg0, ByteAcc, NoLock, Preserve) {...}
	// Error 1037 - ^ parse error
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Method(m000, 1)
	{
		Field(arg0, ByteAcc, NoLock, Preserve) {f900,8,f901,8,f902,8,f903,8}
		BankField(arg0, f901, 0, ByteAcc, NoLock, Preserve) {bn90,4}
		IndexField(f902, f903, ByteAcc, NoLock, Preserve) {if90,8,if91,8}
	}

	m000(r000)

	// Invalid RegionSpaceKeyword, should cause ASL compiler's
	// diagnostics like:
	//     OperationRegion(RGNy, 0x7f, 0, 0x100)
	// Error    4094 -              ^ Value below valid range 0x80-0xFF
	// Error    4094 -              ^ Value above valid range 0x80-0xFF

	OperationRegion(RGNx, 0x00, 0, 0x100)
	OperationRegion(RGNy, 0x7f, 0, 0x100)
	OperationRegion(RGNz, 0x100, 0, 0x100)

	// Additional Invalid RegionName arguments, should cause
	// ASL compiler's diagnostics like:
	//         OperationRegion(0xabcd, SystemMemory, 0, 0x100)
	// Error    4094 -  parse error ^

	OperationRegion("arg0", SystemMemory, 0, 0x100)
	OperationRegion(0xabcd, SystemMemory, 0, 0x100)

	// Invalid Field's Offset and Length arguments, should cause
	// ASL compiler's diagnostics like:
	//                                    Offset(0x2000000), f000, 1,
	// Error    4023 - Package length too long to encode ^

/*  Now it below causes crash of iASL compiler, bug 225
	OperationRegion(OPR0, SystemMemory, 0, 0x2000001)

	Field(OPR0, ByteAcc, NoLock, Preserve) {
		Offset(0x2000000), f000, 1,
	}

	Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
		, 0xffffffc, f001, 6,
	}

	Field(OPR0, ByteAcc, NoLock, WriteAsOnes) {
		f002, 0xffffffc,
	}
*/
}
