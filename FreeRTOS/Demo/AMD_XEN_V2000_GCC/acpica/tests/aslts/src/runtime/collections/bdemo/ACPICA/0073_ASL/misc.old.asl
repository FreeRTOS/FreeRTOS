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

// Miscellaneous not systematized tests

Name(z054, 54)

// Looks like Default is at all not implemented

Method(m100, 1)
{
	Store(0, Local0)
	Store(0, Local1)

	// Bug XXX. This Switch code below causes ASL-compiler to fail
	// for full.asl file with the diagnostics like this:
	// nssearch-0397: *** Error: NsSearchAndEnter:
	//                    Bad character in ACPI Name: 5B5F545F
	// and fall into recursion:
	// Remark   3040 -     Recursive method call ^  (ERR_)
	// Note: (0x5B5F545F is equal to "[_T_")

	Switch (Local1) {
		Case (5) {
			Store(5, Local0)
		}
		Default {
			Store(1, Local0)
		}
	}

	if (LNotEqual(Local0, 1)) {
		err(arg0, z054, __LINE__, Local0, 0)
	}
}

// Concatenate operator affects the object passed as Source2 parameter

Method(m101, 1) {
	Concatenate("qwertyuiop", arg0)
}

Method(m102, 1)
{
	Store(0, Local0)
	m101(Local0)
	if (LNotequal(Local0, 0)) {
		err(arg0, z054, __LINE__, Local0, 0)
	}

	Store(0, Local0)
	Concatenate("qwertyuiop", Local0)
	if (LNotequal(Local0, 0)) {
		err(arg0, z054, __LINE__, Local0, 0)
	}
}

// Unexpected value returned by ObjectType for Field Unit objects

// The field passed as explicit reference (RefOf)
Method(m105, 1)
{
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field (r000, ByteAcc, NoLock, Preserve) {
		f000, 32
	}

	Store(ObjectType(RefOf(f000)), Local0)
	if (LNotEqual(Local0, 5)) {
		err(arg0, z054, __LINE__, Local0, 0)
	}
}

// The BankField corrupts the contents of OperationRegion

Method(m106, 1)
{
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field (r000, ByteAcc, NoLock, Preserve) {
		bnk0, 8
	}

	BankField (r000, bnk0, 0, ByteAcc, NoLock, Preserve) {
		Offset(16),
		bf00, 8,
	}

	BankField (r000, bnk0, 1, ByteAcc, NoLock, Preserve) {
		Offset(17),
		bf01, 8,
	}

	Store(1, bnk0)
	if (LNotEqual(bnk0, 1)) {
		err(arg0, z054, __LINE__, bnk0, 0)
	}

	Store(0x96, bf01)
	if (LNotEqual(bnk0, 1)) {
		err(arg0, z054, __LINE__, bnk0, 0)
	}

	Store(0x87, bf00)
	if (LNotEqual(bnk0, 1)) {
		err(arg0, z054, __LINE__, bnk0, 0)
	}

	if (LNotEqual(bf00, 0x87)) {
		err(arg0, z054, __LINE__, bf00, 0)
	}

	if (LNotEqual(bf01, 0x96)) {
		err(arg0, z054, __LINE__, bf01, 0)
	}
}

// ToBuffer caused destroying of source buffer passed by Data parameter
Method(m107, 1)
{
	Store(Buffer(4){10, 11, 12, 13}, Local0)
	Store(ObjectType(Local0), Local1)

	if (LNotEqual(Local1, c00b)) {
		err(arg0, z054, __LINE__, Local1, 0)
	}

	ToBuffer(Local0, Local2)

	Store(0xaa, Local3)

	Store(ObjectType(Local0), Local3)

	if (LNotEqual(Local3, c00b)) {
		err(arg0, z054, __LINE__, Local3, 0)
	}
}

// ObjectType() operator should be allowed to deal with the
// uninitialized objects.

// Uncomment this when the problem will be fixed and compile
// will not fail in this case like it do now: "Method local
// variable is not initialized (Local0)".
Method(m108, 1)
{
	Store(ObjectType(Local0), Local1)
}

// Now, this cause exception but should not
Method(m109, 2)
{
	if (arg1) {
		Store(0, Local0)
	}

	CH03()

	Store(ObjectType(Local0), Local1)

	if (LNotEqual(Local1, 0)) {
		err(arg0, z054, __LINE__, Local1, 0)
	}

	CH03()
}

Method(m10a, 1)
{
	m109(arg0, 0)
}

// DerefOf. If the Source evaluates to a string, the string is evaluated
// as an ASL name (relative to the current scope) and the contents of that
// object are returned.
Method(m10b, 1)
{
	Name(b000, Buffer(){ 1, 2, 3, 4, 5, 6, 7, 8 })

	Store("b000", Local0)

	Store("================ 0:", Debug)

	Store(DerefOf(Local0), Local1)

	Store("================ 1:", Debug)

	Store(ObjectType(Local1), Local2)

	if (LNotEqual(Local2, 3)) {
		err(arg0, z054, __LINE__, Local2, 0)
	}

	Store("================ 2:", Debug)

	Store(Local1, Debug)
	Store(Local2, Debug)

	return (0)
}

/*
// Currently, incorrect test
// The size of Strings in Package is determined incorrectly
Method(m10c, 1)
{
	Name(p000, Package() {
		"012",
		"0123456789abcdef",
		Buffer() {17,28,69,11,22,34,35,56,67,11},
		"012345",
	})

	Store(DeRefOf(Index(p000, 1)), Local0)
	Store(0, Index(Local0, 5))

	Store(0, Index(p000, 1))

	Store(DeRefOf(Index(p000, 1)), Local0)
//	Store(0, Index(Local0, 5))

	Store("=================:", Debug)
	Store(Local0, Debug)

	// 0
	Store(DeRefOf(Index(p000, 0)), Local2)
	Store(SizeOf(Local2), Local3)

	Store(Local3, Debug)

	if (LNotEqual(Local3, 3)) {
		err(arg0, z054, __LINE__, Local3, 3)
	}

	// 1
	Store(DeRefOf(Index(p000, 1)), Local2)
	Store(SizeOf(Local2), Local3)

	Store(Local3, Debug)

	if (LNotEqual(Local3, 9)) {
		err(arg0, z054, __LINE__, Local3, 9)
	}

	// 2
	Store(DeRefOf(Index(p000, 2)), Local2)
	Store(SizeOf(Local2), Local3)

	Store(Local3, Debug)

	if (LNotEqual(Local3, 6)) {
		err(arg0, z054, __LINE__, Local3, 6)
	}

	Store(SizeOf(p000), Local0)

	Store(Local0, Debug)

	if (LNotEqual(Local0, 3)) {
		err(arg0, z054, __LINE__, Local0, 3)
	}
}
*/

/*
// ATTENTION: such type tests have to be added and extended
Method(m10d, 1)
{
	Name(p000, Package() {
		0x12345678, 0x90abcdef,
	})
	Name(b000, Buffer() {0x78,0x56,0x34,0x12, 0xef,0xcd,0xab,0x90})

	Store(DeRefOf(Index(p000, 0)), Local7)

	if (LEqual(b000, Local7)) {
		err(arg0, z054, __LINE__, b000, Local7)
	}

	if (LEqual(Local7, b000)) {
		err(arg0, z054, __LINE__, Local7, b000)
	}

	return (0)
}
*/


// Bug 54: All the ASL Operators which deal with at least two Buffer type
// objects cause unexpected exceptions in cases when both Buffer type objects
// are passed immediately
Method(m10e, 1)
{
	CH03()

	Add( Buffer() {0x79}, Buffer() {0x79} )

	CH03()
}

// Bug 57: The empty Return operator (without specifying the returning value)
// is processed incorrectly
Method(m10f, 1) {

	Method(m110, 2) {

		if (arg1) {
			return (0x1234)

			// ASL-compiler report Warning in this case
			// Store("ERROR 0: m113, after Return !!!", Debug)
		}
		err(arg0, z054, __LINE__, 0, 0)

		return (0x5678)
	}

	Method(m111, 2) {

		if (arg1) {

			return

			// ASL-compiler DOESN'T report Warning in this case!!!
			// And the Store operator below is actually processed!!!

			err(arg0, z054, __LINE__, 0, 0)
		}

		err(arg0, z054, __LINE__, 0, 0)

		return
	}

	Store(m110(arg0, 1), Local7)

	m111(arg0, 1)

	return (0)
}

// Bug 59: The String to Buffer Rule from the Table 17-8 "Object Conversion
// Rules" says "If the string is shorter than the buffer, the buffer size is
// reduced".
Method(m110, 1) {
	Name(str0, "\x01\x02")
	Name(buf0, Buffer(){0x03, 0x04, 0x05})

	Store(str0, buf0)

	if (LNotEqual(Sizeof(buf0), 2)) {
		// Error: length of the buffer not reduced to the stored string
		err(arg0, z054, __LINE__, 0, 0)
	}
	return (0)
}

// Bug 65: The Buffer Field type objects should be passed
// to Methods without any conversion, but instead
// they are converted to Buffers or Integers depending
// on the size of the Buffer Field object and the
// run mode (32-bit or 64/bit mode).
Method(m111, 1) {
	Name(b000, Buffer(200) {})
	CreateField(b000, 0, 8, bf00)

	Method(m000, 2)
	{
		Store(ObjectType(arg1), Local0)
		if (LNotEqual(Local0, 14)) {
			err(arg0, z054, __LINE__, Local0, 14)
		}
	}

	Method(m001, 1)
	{
		Store(ObjectType(bf00), Local0)
		if (LNotEqual(Local0, 14)) {
			err(arg0, z054, __LINE__, Local0, 14)
		} else {
			m000(arg0, bf00)
		}
	}

	m001(arg0)
}

// Bug 66: The Field Unit type objects should be passed
// to Methods without any conversion, but instead
// they are converted to Buffers or Integers depending
// on the size of the Buffer Field object and the
// run mode (32-bit or 64/bit mode).
Method(m112, 1) {
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) { f000, 8 }

	Method(m000, 2)
	{
		Store(ObjectType(arg1), Local0)
		if (LNotEqual(Local0, 5)) {
			err(arg0, z054, __LINE__, Local0, 5)
		}
	}

	Method(m001, 1)
	{
		Store(ObjectType(f000), Local0)
		if (LNotEqual(Local0, 5)) {
			err(arg0, z054, __LINE__, Local0, 5)
		} else {
			m000(arg0, f000)
		}
	}

	m001(arg0)
}

// Bug 67: The Buffer Field type objects should be RETURNED
// by Methods without any conversion, but instead
// they are converted to Buffers or Integers depending
// on the size of the Buffer Field object and the
// run mode (32-bit or 64/bit mode).
Method(m113, 1) {
	Name(b000, Buffer(200) {})
	CreateField(b000, 0, 8, bf00)

	Method(m000)
	{
		return (bf00)
	}

	Method(m001, 1)
	{
		Store(ObjectType(bf00), Local0)
		if (LNotEqual(Local0, 14)) {
			err(arg0, z054, __LINE__, Local0, 14)
		} else {
			Store(m000(), Local7)
			Store(ObjectType(Local7), Local0)
			if (LNotEqual(Local0, 14)) {
				err(arg0, z054, __LINE__, Local0, 14)
			}
		}
	}

	m001(arg0)
}

// Bug 68: The Field Unit type objects should be RETURNED
// by Methods without any conversion, but instead
// they are converted to Buffers or Integers depending
// on the size of the Buffer Field object and the
// run mode (32-bit or 64/bit mode).
Method(m114, 1) {
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) { f000, 8 }

	Method(m000)
	{
		return (f000)
	}

	Method(m001, 1)
	{
		Store(ObjectType(f000), Local0)
		if (LNotEqual(Local0, 5)) {
			err(arg0, z054, __LINE__, Local0, 5)
		} else {
			Store(m000(), Local7)
			Store(ObjectType(Local7), Local0)
			if (LNotEqual(Local0, 5)) {
				err(arg0, z054, __LINE__, Local0, 5)
			}
		}
	}

	m001(arg0)
}

// Bug 30. This test may be removed there after
// the Field relative tests will be implemented.
// Caused crash.
Method(m115, 1)
{
	Method(m000)
	{
		// Field Unit
		OperationRegion(r000, SystemMemory, 0x100, 0x100)
		Field(r000, ByteAcc, NoLock, Preserve) {
			f000, 8,
			f001, 16,
			f002, 32,
			f003, 33,
			f004, 1,
			f005, 64,
		}

		Store("------------ Fields:", Debug)
		Store(f000, Debug)
		Store(f001, Debug)
		Store(f002, Debug)
		Store(f003, Debug)
		Store(f004, Debug)
		Store(f005, Debug)
		Store("------------.", Debug)

		return (0)
	}

	Method(m001)
	{
		// Field Unit
		OperationRegion(r000, SystemMemory, 0x100, 0x100)
		Field(r000, ByteAcc, NoLock, Preserve) {
			f000, 8,
			f001, 16,
			f002, 32,
			f003, 33,
			f004, 7,
			f005, 64,
		}

		Store("------------ Fields:", Debug)
		Store(f000, Debug)
		Store(f001, Debug)
		Store(f002, Debug)
		Store(f003, Debug)
		Store(f004, Debug)
		Store(f005, Debug)
		Store("------------.", Debug)

		return (0)
	}

	m000()
	m001()
	return (0)
}

Method(m116, 1)
{
	Method(m000)
	{
		return (0x12345678)
	}

	Method(m001, 1)
	{
		return (0x12345678)
	}

	Store(ObjectType(m000), Local0)
	if (LNotEqual(Local0, c010)) {
		err(arg0, z054, __LINE__, Local0, c010)
	}

    /* Nov. 2012: Method invocation as arg to ObjectType is now illegal */
//
//	Store(ObjectType(m000()), Local0)
//	if (LNotEqual(Local0, c009)) {
//		err(arg0, z054, __LINE__, Local0, c009)
//	}
//
//	Store(ObjectType(m001(123)), Local1)
//	if (LNotEqual(Local1, c009)) {
//		err(arg0, z054, __LINE__, Local1, c009)
//	}
}

// Run-method
Method(MSC0)
{
	Name(ts, "MSC0")

	m100(ts)
	m102(ts)
	m105(ts)
	m106(ts)
	m107(ts)
	m108(ts)
	m10a(ts)
	m10b(ts)
	m10e(ts)
	m10f(ts)
	m110(ts)
	m111(ts)
	m112(ts)
	m113(ts)
	m114(ts)
	m115(ts)
	m116(ts)
}
