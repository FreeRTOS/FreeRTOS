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
 * Tests exercized during ACPICA to MS implementation comparison
 */

Name(z179, 179)

/*
 *
 * Stuff not working under MS:
 *
 *  1) String to Integer Implicit operand conversion, ms10: a063, b063, c063 -
 *     a failure when a String in a position of an Integer; errors in e063,
 *     f063, g063, h063 are inverted by q004 flag (Implicit Operand conversion
 *     on MS contradicts ACPI Spec).
 *  2) No exception on DerefOf of an arbitrary Source, ms11: b083, d083 -
 *     an expected failure on DerefOf of an Integer.
 *  3) Access to FieldObject element of Package causes exception, ms16: f118 -
 *     a failure when an Integer is stored to a Named Package.
 *  4) The Read access automatic dereference ... doesn't work, ms17: b126,
 *     c126 - a failure when a reference in ArgX is used in a position of Data.
 *  5) CopyObject of immediately passed Index ... is not a reference, ms18:
 *     a127 - a failure due to the CopyObject operator in AML code.
 *  6) Copying the RefOf reference to Named object ..., ms19: d128, e128 -
 *     a failure when a reference is stored to a Package element.
 *  7) Store to the Index reference ... returned by Method ..., ms1a: a131,
 *     b131, c131 - a failure when a Method call is the Target of Store.
 *  8) Read access automatic dereference for Index reference ..., ms1b: a132,
 *     b132 - a failure when the Index argument is used without Derefof.
 *  9) Write access automatic dereference for Index reference ..., ms1c: b133 -
 *     a failure when a String element is to be changed.
 * 10) Forward reference within a control method, ms20: cmfr - an expected
 *     failure when a Named Object is accessed before its declaration.
 * 11) Recursive Serialized method execution, ms21: erec - an expected
 *     failure for the enough deep recursion.
 * 12) Implicit return, ms23: emir?, fmir?, gmir - Break in the specifically
 *     declared while doesn't work.
 * 13) Store(..., DeRefof(...)) behavior, ms25: a failure when a Refof or
 *     Derefof is the Target of Store.
 * 14) IndexField implementation, my27: jife - a failure when the Access type
 *     of a Field is specified to be QWordAcc.
 * 15) Acquire/Release, ms29: a hang when used with the Dynamic Mutex.
 * 16) ToBuffer optional store, ms2a: it looks like ToBuffer does not work.
 * 17) Package size calculation, ms2b: pac2 actually should be used with
 *     Package(3){1, 2, 3, 4, 5}) declaration, but iASL reports "Initializer
 *     list too long" error. Use it with -f iASL option.
 * 18) Bug 246 issue, ms2f: c246 actually should be used without
 *     While(1){... Break) declaration, but iASL reports "No enclosing While
 *     statement" error. Use it with -f iASL option.
 * 19) Storing of an improper specified Device object ..., ms33:
 *     a blue screen appears on the MS OS booting if that Device is global.
 *
 * 99)
 */

// Useful for indirect storing

Method(RSTO, 2) {Store(arg0, arg1)}

Method(DSTO, 2) {Store(Derefof(arg0), arg1)}

/*
 * Bug 63 issue:
 *
 * SUMMARY: String to Integer conversion contradicts new April 2005 Conversion Rules
 */
Method(ms10, 1, Serialized)
{
	Name(ts, "ms10")

	Method(m063, 2)
	{
		OUTP("Bug 63: Add(\"0x1111\", 0, Local0) should return 0?")

		OUTP("Addend1:")
		OUTP(arg0)

		Add(arg0, 0, Local0)

		OUTP("Result (Local0):")
		OUTP(Local0)

		if (LNotEqual(arg1, Local0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, arg1)
		}
	}

	Method(n063, 3, Serialized)
	{
		Name (INT0, 0xffff)

		OUTP("Bug 63upd: Implicit conversion \"0x1111\" to Integer should return 0?")

		OUTP("String:")
		OUTP(arg0)

		Store(arg0, INT0)

		OUTP("Result (INT0):")
		OUTP(INT0)

		if (LAnd(ABUU, LNot(q004))) {
			// Implicit Operand conversion on MS contradicts ACPI Spec
			if (LNotEqual(arg2, INT0)) {
				err(ts, z179, __LINE__, 0, 0, INT0, arg2)
			}
		} else {
			if (LNotEqual(arg1, INT0)) {
				err(ts, z179, __LINE__, 0, 0, INT0, arg1)
			}
		}
	}

	Method(m000)
	{
		if (ABUU) {
		} else {
			m063("0", 0)
			m063("0x", 0)
			m063("0x1111", 0)
		}
		m063(1, 1)

		n063("0", 0, 0x30)
		n063("0x", 0, 0x7830)
		n063("0x1111", 0, 0x31317830)
		n063("0x111111111",  0, 0x31317830)
	}

	CH03(ts, z179, 0x002, __LINE__, 0)

	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { m063("0", 0) }
		case (2) { m063("0x", 0) }
		case (3) { m063("0x1111", 0) }
		case (4) { m063(1, 1) }

		case (5) { n063("0", 0, 0x30) }
		case (6) { n063("0x", 0, 0x7830) }
		case (7) { n063("0x1111", 0, 0x31317830) }
		case (8) { n063("0x111111111", 0, 0x31317830) }
	}

	CH03(ts, z179, 0x003, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(a063) { IIN0() ms10(1) Return(POUT) }
Method(b063) { IIN0() ms10(2) Return(POUT) }
Method(c063) { IIN0() ms10(3) Return(POUT) }
Method(d063) { IIN0() ms10(4) Return(POUT) }
Method(e063) { IIN0() ms10(5) Return(POUT) }
Method(f063) { IIN0() ms10(6) Return(POUT) }
Method(g063) { IIN0() ms10(7) Return(POUT) }
Method(h063) { IIN0() ms10(8) Return(POUT) }

/*
 * Bug 83 issue:
 *
 * SUMMARY: No exception on DerefOf of an arbitrary Source
 */
Method(ms11, 1, Serialized)
{
	Name(ts, "ms11")

	Method(m083, 1, Serialized)
	{
		Name(i000, 0x89abcdef)

		OUTP("Bug 83: Derefof of non-Ref. (f.e. Integer) should produce exception")

		OUTP("Name(i000, 0x89abcdef)")

		if (arg0) {
			Store(Derefof(i000), Local0)
			CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
		} else {
			Store(Derefof(Refof(i000)), Local0)
			CH03(ts, z179, 0x005, __LINE__, 0)
		}
	}

	Method(n083, 1, Serialized)
	{
		Name(i000, 0x89abcdef)

		OUTP("Bug 83upd: Derefof of non-Ref. (f.e. Integer) should produce exception")

		if (arg0) {
			Store(0x89abcdef, Local0)
			OUTP("Store(0x89abcdef, Local0)")
		} else {
			Store(Refof(i000), Local0)
			OUTP("Store(Refof(i000), Local0)")
		}
		Store(Derefof(Local0), Local1)
		if (arg0) {
			CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
		} else {
			CH03(ts, z179, 0x007, __LINE__, 0)
		}
	}

	Method(m000)
	{
		m083(0)
		if (ABUU) {
		} else {
			m083(1)
		}
		n083(0)
		if (ABUU) {
		} else {
			n083(1)
		}
	}

	CH03(ts, z179, 0x008, __LINE__, 0)

	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { m083(0) }
		case (2) { m083(1) }
		case (3) { n083(0) }
		case (4) { n083(1) }
	}

	CH03(ts, z179, 0x009, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(a083) { IIN0() ms11(1) Return(POUT) }
Method(b083) { IIN0() ms11(2) Return(POUT) }
Method(x083) { IIN0() ms11(3) Return(POUT) }
Method(d083) { IIN0() ms11(4) Return(POUT) }

/*
 * Bug 100 issue:
 *
 * SUMMARY: The specific combination of operators aborts execution
 */
Method(ms12,, Serialized)
{
	Name(ts, "ms12")

	Method(m100)
	{
		Method(m000)
		{
			return (0)
		}

		Method(m001,, Serialized)
		{
			m000()

			Device(d000) {}

			Name(i000, 0xabcdef)

			OUTP("Finish of test")
		}

		OUTP("Bug 100 (fixed for 20050526): some combination of operators aborts execution")

		m001()
	}
	CH03(ts, z179, 0x00a, __LINE__, 0)
	m100()
	CH03(ts, z179, 0x00b, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(a100) { IIN0() ms12() Return(POUT) }

/*
 * Bug 113 issue:
 *
 * SUMMARY: Unexpected dereference of Index reference immediately passed to Method
 */

Method(ms13, 1, Serialized)
{
	Name(ts, "ms13")

	Name(p001, Package(){0x10, 0x11, 0x12, 0x13, 0x14})
	Name(p002, Package(){0x20, 0x21, 0x22, 0x23, 0x24})
	Name(p003, Package(){0x30, 0x31, 0x32, 0x33, 0x34})
	Name(p004, Package(){0x40, 0x41, 0x42, 0x43, 0x44})
	Name(p005, Package(){0x50, 0x51, 0x52, 0x53, 0x54})

	Method(a113)
	{
		Method(m000, 2)
		{
			Store(Derefof(arg0), Local0)
			if (CH03(ts, z179, 0x00c, __LINE__, 0)) {
			} elseif (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
		}

		OUTP("Bug 113: immediate Indexed Ref. as parameters of Methods are unexpectedly dereferenced 1")

		m000(Index(p001, 0), 0x10)
	}

	Method(b113)
	{
		Method(m000, 2)
		{
			Store(Derefof(arg0), Local0)
			if (CH03(ts, z179, 0x00e, __LINE__, 0)) {
			} elseif (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
		}

		OUTP("Bug 113: immediate Indexed Ref. as parameters of Methods are unexpectedly dereferenced 2")

		Store(Index(p001, 0), Local0)

		m000(Local0, 0x10)
	}

	Method(s113)
	{
		Method(m000, 6)
		{
			OUTP(Derefof(arg0))
			CH03(ts, z179, 0x012, __LINE__, 0)
			OUTP(Derefof(arg1))
			CH03(ts, z179, 0x013, __LINE__, 0)
			OUTP(Derefof(arg2))
			CH03(ts, z179, 0x014, __LINE__, 0)
			OUTP(Derefof(arg3))
			CH03(ts, z179, 0x015, __LINE__, 0)
			OUTP(Derefof(arg4))
			CH03(ts, z179, 0x016, __LINE__, 0)
			OUTP(Derefof(arg5))
			CH03(ts, z179, 0x017, __LINE__, 0)
		}

		OUTP("Bug 113 MS: immediate Indexed Ref. as parameters of Methods can be dereferenced 3")

		Store(Index(p002, 1), Local0)

		Index(p004, 3, Local1)

		Store(Index(p005, 4, Local2), Local3)

		m000(Index(p001, 0), Local0, Index(p003, 2, Local4), Local1, Local2, Local3)

		OUTP(Derefof(Local4))
	}

	CH03(ts, z179, 0x018, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { a113() b113() s113()}
		case (1) { a113() }
		case (2) { b113() }
		case (3) { s113() }
	}
	CH03(ts, z179, 0x019, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(a113) { IIN0() ms13(1) Return(POUT) }
Method(b113) { IIN0() ms13(2) Return(POUT) }
Method(c113) { IIN0() ms13(3) Return(POUT) }

/*
 * Bug 114 issue:
 *
 * SUMMARY: Method object as a Source of Index operation is treated by iASL as a call to that Method
 * Note: M001 will become a method call. No parens needed because it has no argument.
 */
Method(ms14, 1, Serialized)
{
	Name(ts, "ms14")

	Method(m114, 1)
	{
		Method(m000, 1, Serialized)
		{
			Name(i001, 0)
			Name(b001, Buffer(){10,2,3,4,5})

			Method(m001)
			{
				Increment(i001)
				return (Buffer(){10,2,3,4,5})
			}

			Method(m002)
			{
				Increment(i001)
				return (Package(){10,2,3,4,5})
			}

			if (LEqual(arg0, 0)) {
				OUTP("Start of test: Method returns (Buffer(){10,2,3,4,5})")
				OUTP("Index(m001, 0, Local0)")
				Index(m001, 0, Local0)
				if (LAnd(ABUU, LNot(q005))) {
				} elseif (LNot(i001)) {
					err(ts, z179, __LINE__, 0, 0, i001, 0)
				}
			} elseif (LEqual(arg0, 1)) {
				OUTP("Start of test: Method returns (Package(){10,2,3,4,5})")
				OUTP("Index(m001, 0, Local0)")
				Index(m001, 0, Local0)
				if (LAnd(ABUU, LNot(q005))) {
				} elseif (LNot(i001)) {
					err(ts, z179, __LINE__, 0, 0, i001, 0)
				}
			} elseif (LEqual(arg0, 2)) {
				OUTP("Start of test: Name(b001, Buffer(){10,2,3,4,5})")
				OUTP("Index(b001, 0, Local0)")
				Index(b001, 0, Local0)
				OUTP(i001)
				Store(DerefOf(Local0), Local1)
				OUTP(Local1)
			}

			OUTP("Finish of test")
		}

		OUTP("Bug 114: Method object as a Source of Index operation")
		m000(arg0)
	}

	Method(m000)
	{
		m114(0)
		m114(1)
		m114(2)
	}

	CH03(ts, z179, 0x01e, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000()}
		case (1) { m114(0) }
		case (2) { m114(1) }
		case (3) { m114(2) }
	}
	CH03(ts, z179, 0x01f, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(a114) { IIN0() ms14(1) Return(POUT) }
Method(b114) { IIN0() ms14(2) Return(POUT) }
Method(c114) { IIN0() ms14(3) Return(POUT) }

/*
 * Bug 115 issue:
 *
 * SUMMARY: Unexpected dereference of Index reference returned by Method and immediately passed to another Method
 */
Method(ms15, 1, Serialized)
{
	Name(ts, "ms15")

	Name(p001, Package(){0x10})
	Name(p002, Package(){0x20})
	Name(p003, Package(){0x30})
	Name(p004, Package(){0x40})
	Name(p005, Package(){0x50})
	Name(p006, Package(){0x60})

	Method(m001) {Return(Index(p001, 0))}
	Method(m002) {Store(Index(p002, 0), Local0)
				  Return(Local0)}
	Method(m003) {Return(Index(p003, 0, Local0))}
	Method(m004) {Index(p004, 0, Local0)
				  Return(Local0)}

	Method(m005) {Store(Index(p005, 0, Local0), Local1)
				  Return(Local1)}
	Method(m006) {Store(Index(p006, 0, Local0), Local1)
				  Return(Local0)}

	Method(a115)
	{

		Method(m000, 2)
		{
			Store(Derefof(arg0), Local0)
			if (CH03(ts, z179, 0x020, __LINE__, 0)) {
			} elseif (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
		}

		OUTP("Bug 115: immediately returned Indexed Ref. as parameters of Methods are unexpectedly dereferenced 1")

		m000(m001(), 0x10)
	}

	Method(b115)
	{

		Method(m000, 2)
		{
			Store(Derefof(arg0), Local0)
			if (CH03(ts, z179, 0x022, __LINE__, 0)) {
			} elseif (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
		}

		OUTP("Bug 115: immediately returned Indexed Ref. as parameters of Methods are unexpectedly dereferenced 2")

		m000(m002(), 0x20)
	}

	Method(c115)
	{

		Method(m000, 2)
		{
			Store(Derefof(arg0), Local0)
			if (CH03(ts, z179, 0x024, __LINE__, 0)) {
			} elseif (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
		}

		OUTP("Bug 115: immediately returned Indexed Ref. as parameters of Methods are unexpectedly dereferenced 3")

		m000(m003(), 0x30)
	}

	Method(d115)
	{

		Method(m000, 2)
		{
			Store(Derefof(arg0), Local0)
			if (CH03(ts, z179, 0x026, __LINE__, 0)) {
			} elseif (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
		}

		OUTP("Bug 115: immediately returned Indexed Ref. as parameters of Methods are unexpectedly dereferenced 4")

		m000(m004(), 0x40)
	}

	Method(e115)
	{

		Method(m000, 2)
		{
			Store(Derefof(arg0), Local0)
			if (CH03(ts, z179, 0x028, __LINE__, 0)) {
			} elseif (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
		}

		OUTP("Bug 115: immediately returned Indexed Ref. as parameters of Methods are unexpectedly dereferenced 5")

		m000(m005(), 0x50)
	}

	Method(f115)
	{

		Method(m000, 2)
		{
			Store(Derefof(arg0), Local0)
			if (CH03(ts, z179, 0x02a, __LINE__, 0)) {
			} elseif (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
		}

		OUTP("Bug 115: immediately returned Indexed Ref. as parameters of Methods are unexpectedly dereferenced 6")

		m000(m006(), 0x60)
	}

	CH03(ts, z179, 0x02c, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { a115() b115() c115() d115() e115() f115()}
		case (1) { a115() }
		case (2) { b115() }
		case (3) { c115() }
		case (4) { d115() }
		case (5) { e115() }
		case (6) { f115() }
	}
	CH03(ts, z179, 0x02d, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(a115) { IIN0() ms15(1) Return(POUT) }
Method(b115) { IIN0() ms15(2) Return(POUT) }
Method(c115) { IIN0() ms15(3) Return(POUT) }
Method(d115) { IIN0() ms15(4) Return(POUT) }
Method(e115) { IIN0() ms15(5) Return(POUT) }
Method(f115) { IIN0() ms15(6) Return(POUT) }

/*
 * Bug 118 issue:
 *
 * SUMMARY: Access to FieldObject element of Package causes exception
 */
Method(ms16, 1, Serialized)
{
	Name(ts, "ms16")

	Method(a118,, Serialized)
	{
		Name(p90d, Package() {0xd650a284})

		// Access to the Integer data as an element of Package
		Method(m000)
		{
			OUTP("Test m000 started")

			Store(Index(p90d, 0), Local0)
			Store(DerefOf(Local0), Local1)
			Store(ObjectType(Local1), Local2)

			if (LNotEqual(Local2, 1)) {
				err(ts, z179, __LINE__, 0, 0, Local2, 1)
				if (LEqual(Local2, 2)) {
					OUTP(Local1)
				} else {
					OUTP(Local2)
				}
			} else {
				OUTP(Local1)
				if (LNotEqual(Local1, 0xd650a284)) {
					err(ts, z179, __LINE__, 0, 0, Local1, 0xd650a284)
				} else {
					OUTP("Ok")
				}
			}

			OUTP("Test m000 finished")
		}

		OUTP("Bug 118: Integer data as an element of Package")

		m000()
	}

	Method(b118,, Serialized)
	{
		Name(i900, 0xd650a284)

		Name(p90d, Package() {i900})

		// Access to the named Integer object as an element of Package
		Method(m000)
		{
			OUTP("Test m000 started")

			Store(Index(p90d, 0), Local0)
			Store(DerefOf(Local0), Local1)
			Store(ObjectType(Local1), Local2)

			if (LAnd(ABUU, LNot(q006))) {
				if (LNotEqual(Local2, 2)) {
					err(ts, z179, __LINE__, 0, 0, Local2, 2)
				}
			} elseif (LNotEqual(Local2, 1)) {
				err(ts, z179, __LINE__, 0, 0, Local2, 1)
			} else {
				OUTP(Local1)
				if (LNotEqual(Local1, 0xd650a284)) {
					err(ts, z179, __LINE__, 0, 0, Local1, 0xd650a284)
				} else {
					OUTP("Ok")
				}
			}

			OUTP("Test m000 finished")
		}

		OUTP("Bug 118: Named Integer Object reference in Package")

		m000()
	}

	Method(c118,, Serialized)
	{
		Name(b900, Buffer() {10,2,3,4,5,6,7,8,9})

		CreateField(b900, 0, 8, bf90)

		Name(p915, Package() {bf90})

		// Access to the Buffer Field object as an element of Package
		Method(m001)
		{
			OUTP("Test m001 started")

			Store(Index(p915, 0), Local0)
			Store(DerefOf(Local0), Local1)
			Store(ObjectType(Local1), Local2)

			if (LAnd(ABUU, LNot(q006))) {
				if (LNotEqual(Local2, 2)) {
					err(ts, z179, __LINE__, 0, 0, Local2, 2)
				}
			} elseif (LNotEqual(Local2, 0x3)) {
				err(ts, z179, __LINE__, 0, 0, Local2, 0x3)
			} elseif (y118) {
				OUTP(Local1)
				if (LNotEqual(Local1, 10)) {
					err(ts, z179, __LINE__, 0, 0, Local1, 10)
				} else {
					OUTP("Ok")
				}
			}

			OUTP("Test m001 finished")
		}

		OUTP("Bug 118: Named Buffer Field Object reference in Package")

		m001()
	}

	Method(d118,, Serialized)
	{
		Name(b900, Buffer() {10,2,3,4,5,6,7,8,9})

		CreateField(b900, 0, 8, bf90)

		// Access to the Buffer Field object by Reference
		Method(m001)
		{
			OUTP("Test m001 started: Store bf90 to Local1")

			Store(bf90, Local1)
			Store(ObjectType(Local1), Local2)

			if (LAnd(ABUU, LNot(q007))) {
				if (LNotEqual(Local2, 3)) {
					err(ts, z179, __LINE__, 0, 0, Local2, 3)
				}
			} elseif (LNotEqual(Local2, 0x3)) {
				err(ts, z179, __LINE__, 0, 0, Local2, 0x3)
			} else {
				OUTP(Local1)
				if (LNotEqual(Local1, Buffer(){0xA})) {
					err(ts, z179, __LINE__, 0, 0, Local1, Buffer(){0xA})
				} else {
					OUTP("Ok")
				}
			}

			OUTP("Test m001 finished")
		}

		OUTP("Bug 118 issue: Fields are immediately resolved to integers/buffers.")

		m001()
	}

	Method(e118,, Serialized)
	{
		Name(b900, Buffer() {10,2,3,4,5,6,7,8,9})

		CreateField(b900, 0, 8, bf90)

		// Access to the Buffer Field object by Reference
		Method(m001)
		{
			OUTP("Test m001 started: Store DerefOf(Refof(bf90)) to Local1")

			Store(Refof(bf90), Local0)
			Store(DerefOf(Local0), Local1)
			Store(ObjectType(Local1), Local2)

			if (LAnd(ABUU, LNot(q007))) {
				if (LNotEqual(Local2, 3)) {
					err(ts, z179, __LINE__, 0, 0, Local2, 3)
				}
			} elseif (LNotEqual(Local2, 0x3)) {
				err(ts, z179, __LINE__, 0, 0, Local2, 0x3)
			} else {
				OUTP(Local1)
				if (LNotEqual(Local1, Buffer(){0xA})) {
					err(ts, z179, __LINE__, 0, 0, Local1, Buffer(){0xA})
				} else {
					OUTP("Ok")
				}
			}

			OUTP("Test m001 finished")
		}

		OUTP("Bug 118 issue: Fields are immediately resolved to integers/buffers.")

		m001()
	}

	Method(f118,, Serialized)
	{
		Name(b900, Buffer() {10,2,3,4,5,6,7,8,9})

		CreateField(b900, 0, 8, bf90)

		Name(p915, Package(1) {})

		// Access to the Buffer Field object by Reference
		Method(m001)
		{
			Method(m000, 1) {return(arg0)}

			OUTP("Test m001 started: Store DerefOf(Refof(bf90)) to Named Package")

			Store(Refof(bf90), Local0)
			Store(DerefOf(Local0), p915)
			Store(ObjectType(p915), Local2)

			if (LNotEqual(Local2, 1)) {
				err(ts, z179, __LINE__, 0, 0, Local2, 1)
			} else {
				OUTP(p915)
				if (LNotEqual(m000(p915), 10)) {
					err(ts, z179, __LINE__, 0, 0, p915, 10)
				} else {
					OUTP("Ok")
				}
			}

			OUTP("Test m001 finished")
		}

		OUTP("Bug 118 issue: Fields are immediately resolved to integers/buffers.")

		m001()
	}

	Method(g118,, Serialized)
	{
		Name(i900, 0xd650a284)

		Name(p90d, Package() {i900})

		// Access to the named Integer object as an element of Package
		Method(m000)
		{
			OUTP("Test m000 started")

			Store(Index(p90d, 0), Local0)
			Store(DerefOf(Local0), Local1)
			Store(ObjectType(Local1), Local2)

			if (LAnd(ABUU, LNot(q006))) {
				if (LNotEqual(Local2, 2)) {
					err(ts, z179, __LINE__, 0, 0, Local2, 2)
				}
			} elseif (LNotEqual(Local2, 1)) {
				err(ts, z179, __LINE__, 0, 0, Local2, 1)
			} else {
				OUTP(Local1)
				if (LNotEqual(Local1, 0xd650a284)) {
					err(ts, z179, __LINE__, 0, 0, Local1, 0xd650a284)
				} else {
					OUTP("Ok")
				}
			}

			OUTP("Test m000 finished")
		}

		OUTP("Bug 118: DerefOf Named Integer Object reference in Package")

		m000()
	}

	Method(m000)
	{
		a118()
		b118()
		c118()
		d118()
		e118()
		if (ABUU) {
		} else {
			f118()
		}
		g118()
	}

	CH03(ts, z179, 0x03c, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { a118() }
		case (2) { b118() }
		case (3) { c118() }
		case (4) { d118() }
		case (5) { e118() }
		case (6) { f118() }
		case (7) { g118() }
	}
	CH03(ts, z179, 0x03d, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(a118) { IIN0() ms16(1) Return(POUT) }
Method(b118) { IIN0() ms16(2) Return(POUT) }
Method(c118) { IIN0() ms16(3) Return(POUT) }
Method(d118) { IIN0() ms16(4) Return(POUT) }
Method(e118) { IIN0() ms16(5) Return(POUT) }
Method(f118) { IIN0() ms16(6) Return(POUT) }
Method(g118) { IIN0() ms16(7) Return(POUT) }

/*
 * Bug 126 issue:
 *
 * SUMMARY: The Read access automatic dereference for RefOf reference doesn't work
 */
Method(ms17, 1, Serialized)
{
	Name(ts, "ms17")

	Method(m126, 1, Serialized)
	{
		Method(m000, 1, Serialized)
		{
			Name(i001, 0)

			OUTP("m000 started, apply DerefOf()")

			Store(DerefOf(arg0), Local0)
			Add(Local0, 1, Local6)
			CH03(ts, z179, 0x03e, __LINE__, 0)
			OUTP(Local6)

			Store(DerefOf(arg0), i001)
			OUTP(i001)
			Add(i001, 1, Local7)
			CH03(ts, z179, 0x03f, __LINE__, 0)
			OUTP(Local7)

			if (LNotEqual(Local6, Local7)) {
				err(ts, z179, __LINE__, 0, 0, Local6, Local7)
			}

			OUTP("m000 finished")
		}

		Method(m001, 1, Serialized)
		{

			Name(i001, 0)

			OUTP("m001 started, DON'T apply DerefOf()")

			Store(arg0, Local0)
			OUTP("Before Add")
			Add(Local0, 1, Local6)
			CH03(ts, z179, 0x041, __LINE__, 0)
			OUTP("After Add")
			OUTP(Local6)

			OUTP("sit 1")

			Store(arg0, i001)
			CH03(ts, z179, 0x042, __LINE__, 0)
			OUTP(i001)
			Add(i001, 1, Local7)
			CH03(ts, z179, 0x043, __LINE__, 0)
			if (LNotEqual(Local6, Local7)) {
				err(ts, z179, __LINE__, 0, 0, Local6, Local7)
			}

			OUTP("m001 finished")
		}

		Method(m002, 1)
		{
			OUTP("m002 started, immediate Arg")

			OUTP("Before Add")
			Add(arg0, 1, Local7)
			CH03(ts, z179, 0x045, __LINE__, 0)
			OUTP("After Add")
			if (LNotEqual(8, Local7)) {
				err(ts, z179, __LINE__, 0, 0, Local7, 8)
			}

			OUTP("m002 finished")
		}

		Method(m003, 1)
		{
			OUTP("m003 started, apply DerefOf(Arg)")

			OUTP("Before Add")
			Add(DerefOf(arg0), 1, Local7)
			CH03(ts, z179, 0x047, __LINE__, 0)
			OUTP("After Add")
			if (LNotEqual(8, Local7)) {
				err(ts, z179, __LINE__, 0, 0, Local7, 8)
			}

			OUTP("m003 finished")
		}

		Name(i000, 7)
		Name(i001, 7)
		Name(i002, 7)
		Name(i003, 7)


		OUTP("Bug 126: automatic dereference on reading issue")
		if (LEqual(arg0, 0)) {
			m000(RefOf(i000))
		} elseif (LEqual(arg0, 1)) {
			m001(RefOf(i001))
		} elseif (LEqual(arg0, 2)) {
			m002(RefOf(i002))
		} elseif (LEqual(arg0, 3)) {
			m003(RefOf(i003))
		}
	}

	Method(m000)
	{
		m126(0)
		if (ABUU) {
		} else {
			m126(1)
			m126(2)
		}
		m126(3)
	}

	CH03(ts, z179, 0x049, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { m126(0) }
		case (2) { m126(1) }
		case (3) { m126(2) }
		case (4) { m126(3) }
	}
	CH03(ts, z179, 0x04a, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(a126) { IIN0() ms17(1) Return(POUT) }
Method(b126) { IIN0() ms17(2) Return(POUT) }
Method(c126) { IIN0() ms17(3) Return(POUT) }
Method(d126) { IIN0() ms17(4) Return(POUT) }


/*
 * Bug 127 issue:
 *
 * SUMMARY: Unexpectedly CopyObject of immediately passed Index reference is not reference
 */
Method(ms18,, Serialized)
{
	Name(ts, "ms18")

	Method(m127,, Serialized)
	{
		Name (p000, Package(2) {1, 2})

		OUTP("Bug 127: CopyObject unexpectedly performs dereference")

		OUTP("Store(Index(p000, 0, Local0), Local1):")

		Store(Index(p000, 0, Local0), Local1)

		Store(Derefof(Local0), Local4)
		CH03(ts, z179, 0x04b, __LINE__, 0)

		Store(Derefof(Local1), Local4)
		CH03(ts, z179, 0x04c, __LINE__, 0)

		OUTP("CopyObject(Index(p000, 0, Local2), Local3):")

		CopyObject(Index(p000, 0, Local2), Local3)

		Store(Derefof(Local2), Local4)
		CH03(ts, z179, 0x04d, __LINE__, 0)

		Store(Derefof(Local3), Local4)
		CH03(ts, z179, 0x04e, __LINE__, 0)
	}

	CH03(ts, z179, 0x04f, __LINE__, 0)
	m127()
	CH03(ts, z179, 0x050, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(a127) { IIN0() ms18() Return(POUT) }

/*
 * Bug 128 issue:
 *
 * SUMMARY: Copying the RefOf reference to Named object spoils that reference
 */
Method(ms19, 1, Serialized)
{
	Name(ts, "ms19")

	// Store Object_Reference to LocalX (No exception, Ok)
	Method(a128,, Serialized)
	{
		Name(i000, 0x1234)

		OUTP("Bug 128:")

		OUTP("a128 started: Store Object_Reference to LocalX (No exception, Ok)")

		Store(RefOf(i000), Local0)

		Store(DerefOf(Local0), Local1)

		if (LNotEqual(Local1, 0x1234)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 0x1234)
		}

		OUTP("a128 finished")
	}

	// Store Object_Reference to NamedX (Exception, Ok)
	Method(b128,, Serialized)
	{
		Name(i000, 0x1234)
		Name(ref0, 0)

		OUTP("Bug 128:")

		OUTP("b128 started: Store Object_Reference to NamedX (Exception, Ok)")

		Store(RefOf(i000), ref0)
		CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)

		OUTP("b128 finished")
	}

	// CopyObject Object_Reference to NamedX (Exception, Bug)
	Method(c128,, Serialized)
	{
		Name(i000, 0x1234)
		Name(ref0, 0)

		OUTP("Bug 128:")

		OUTP("c128 started: CopyObject Object_Reference to NamedX (Exception, Bug)")

		CopyObject(RefOf(i000), ref0)
		if (CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)) {
			return
		}

		// When an invocation of a Method tries to return a Package,
		// where some reference was saved, the AE_TYPE exception occurs.
		//OUTP(ref0)

		Store(DerefOf(ref0), Local1)

		if (LNotEqual(Local1, 0x1234)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 0x1234)
		}

		OUTP("c128 finished")
	}

	// Store Object_Reference to uninit Package element (No exception, Ok)
	Method(d128,, Serialized)
	{
		Name(i000, 0x1234)
		Name(p000, Package(1){})

		OUTP("Bug 128:")

		OUTP("d128 started: Store Object_Reference to uninit Package element (No exception, Ok)")

		Store(RefOf(i000), Index(p000, 0))

		Store(DerefOf(DerefOf(Index(p000, 0))), Local1)

		if (LNotEqual(Local1, 0x1234)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 0x1234)
		}

		OUTP("d128 finished")
	}

	// Store Object_Reference to init Package element (No exception, Ok)
	Method(e128,, Serialized)
	{
		Name(i000, 0x1234)
		Name(p000, Package(1){0x5678})

		OUTP("Bug 128:")

		OUTP("d128 started: Store Object_Reference to init Package element (No exception, Ok)")

		Store(RefOf(i000), Index(p000, 0))

		Store(DerefOf(DerefOf(Index(p000, 0))), Local1)

		if (LNotEqual(Local1, 0x1234)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 0x1234)
		}

		OUTP("d128 finished")
	}

	Method(m000)
	{
		a128()

		// Causes exception
		if (ABUU) {
		} else {
			b128()
		}

		// Causes exception
		if (ABUU) {
		} else {
			c128()
		}

		if (ABUU) {
		} else {
			d128()
		}

		if (ABUU) {
		} else {
			e128()
		}
	}

	CH03(ts, z179, 0x057, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { a128() }
		case (2) { b128() }
		case (3) { c128() }
		case (4) { d128() }
		case (5) { e128() }
	}
	CH03(ts, z179, 0x058, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(a128) { IIN0() ms19(1) Return(POUT) }
Method(b128) { IIN0() ms19(2) Return(POUT) }
Method(c128) { IIN0() ms19(3) Return(POUT) }
Method(d128) { IIN0() ms19(4) Return(POUT) }
Method(e128) { IIN0() ms19(5) Return(POUT) }

/*
 * Bug 131 issue:
 *
 * SUMMARY: Store to the Index reference immediately returned by Method doesn't work
 */
Method(ms1a, 1, Serialized)
{
	Name(ts, "ms1a")

	Method(a131,, Serialized)
	{
		Name(i000, 0x77)
		Name(i001, 0)

		Method(m000)
		{
			Increment(i001)
			return (RefOf(i000))
		}

		Method(m001)
		{
			Increment(i001)
			Store(RefOf(i000), Local0)
			return (Local0)
		}

		OUTP("Case return (RefOf(i000))")

/*
// Removed 09/2015. iASL store to method invocation is not supported
		Store(5, m000())
*/

		if (LEqual(i001, 0)) {
			err(ts, z179, __LINE__, 0, 0, i001, 0)
		} elseif (LNotEqual(i000, 5)) {
			err(ts, z179, __LINE__, 0, 0, i000, 5)
		} else {
			OUTP("Ok a131")
		}
	}

	Method(b131,, Serialized)
	{
		Name(i000, 0x77)
		Name(i001, 0)

		Method(m000)
		{
			Increment(i001)
			return (RefOf(i000))
		}

		Method(m001)
		{
			Increment(i001)
			Store(RefOf(i000), Local0)
			return (Local0)
		}

		OUTP("Case return (Local0) (= RefOf(i000))")

/*
// Removed 09/2015. iASL store to method invocation not supported

		Store(0x15, m001())
*/

		if (LEqual(i001, 0)) {
			err(ts, z179, __LINE__, 0, 0, i001, 0)
		} elseif (LNotEqual(i000, 0x15)) {
			err(ts, z179, __LINE__, 0, 0, i000, 0x15)
		} else {
			OUTP("Ok b131")
		}
	}

	Method(c131,, Serialized)
	{
		Name(i000, 0x77)
		Name(i001, 0)

		Method(m000)
		{
			Increment(i001)
			return (RefOf(i000))
		}

		Method(m001)
		{
			Increment(i001)
			Store(RefOf(i000), Local0)
			return (Local0)
		}

		Store(Refof(Local0), Local1)

		OUTP("Case Store(return (RefOf(i000)), Local0)")

		Store(m000(), Local0)

		Store(0x25, Derefof(Local1))

		if (LEqual(i001, 0)) {
			err(ts, z179, __LINE__, 0, 0, i001, 0)
		} elseif (LNotEqual(i000, 0x25)) {
			err(ts, z179, __LINE__, 0, 0, i000, 0x25)
		} else {
			OUTP("Ok c131")
		}
	}

	Method(d131,, Serialized)
	{
		Name(i000, 0x77)
		Name(i001, 0)

		Method(m000)
		{
			Increment(i001)
			return (RefOf(i000))
		}

		Method(m001)
		{
			Increment(i001)
			Store(RefOf(i000), Local0)
			return (Local0)
		}

		OUTP("Case - test tools proper work indication")

		RSTO(0x35, m000())

		if (LEqual(i001, 0)) {
			err(ts, z179, __LINE__, 0, 0, i001, 0)
		} elseif (LNotEqual(i000, 0x35)) {
			err(ts, z179, __LINE__, 0, 0, i000, 0x35)
		} else {
			OUTP("Ok d131")
		}
	}

	Method(e131,, Serialized)
	{
		Name(i000, 0x77)
		Name(i001, 0)

		Method(m000)
		{
			Increment(i001)
			return (RefOf(i000))
		}

		OUTP("Case Store(return (RefOf(i000)), Local0), step 1")

		Store(m000(), Local0)

		if (LEqual(i001, 0)) {
			err(ts, z179, __LINE__, 0, 0, i001, 0)
		} else {
			OUTP("Ok e131")
		}
	}

	Method(m000)
	{
		if (ABUU) {
		} else {
			a131()
		}

		if (ABUU) {
		} else {
			b131()
		}

		if (ABUU) {
		} else {
			c131()
		}

		d131()
		e131()
	}

	OUTP("Bug 131: Writing to the reference immediately returned by Method")

	CH03(ts, z179, 0x062, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { a131() }
		case (2) { b131() }
		case (3) { c131() }
		case (4) { d131() }
		case (5) { e131() }
	}
	CH03(ts, z179, 0x063, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(a131) { IIN0() ms1a(1) Return(POUT) }
Method(b131) { IIN0() ms1a(2) Return(POUT) }
Method(c131) { IIN0() ms1a(3) Return(POUT) }
Method(d131) { IIN0() ms1a(4) Return(POUT) }
Method(e131) { IIN0() ms1a(4) Return(POUT) }

/*
 * Bug 132 issue:
 *
 * SUMMARY: The Read access automatic dereference for Index reference doesn't work
 */
Method(ms1b, 1, Serialized)
{
	Name(ts, "ms1b")

	Method(m132, 2, Serialized)
	{
		Name(p000, Package(1) {0x77})

		Method(m000, 2)
		{

			OUTP("m000 started")

			if (arg1) {
				Add(DerefOf(arg0), 1, Local7)
			} else {
				Add(arg0, 1, Local7)
			}
			CH03(ts, z179, 0x064, __LINE__, 0)

			OUTP("After Add")

			if (LNotEqual(Local7, 0x78)) {
				err(ts, z179, __LINE__, 0, 0, Local7, 0x78)
			} else {
				OUTP("Ok 0")
			}
			OUTP(Local7)

			if (arg1) {
				OUTP("Accessed with DerefOf properly!")
			} else {
				OUTP("Accessed without DerefOf properly!")
			}
		}

		OUTP("Bug 132: read access \"Automatic dereference\" for Index Reference")

		if (arg0) {
			OUTP("Transfer Index reference by LocalX:")
			Index(p000, 0, Local0)
			m000(Local0, arg1)
		} else {
			OUTP("Specify Index reference immediately:")
			m000(Index(p000, 0), arg1)
		}
	}

	Method(m000)
	{
		if (ABUU) {
		} else {
			m132(0, 0)
		}

		if (ABUU) {
		} else {
			m132(1, 0)
		}

		m132(0, 1)
		m132(1, 1)
	}

	CH03(ts, z179, 0x066, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { m132(0, 0) }
		case (2) { m132(1, 0) }
		case (3) { m132(0, 1) }
		case (4) { m132(1, 1) }
	}
	CH03(ts, z179, 0x067, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(a132) { IIN0() ms1b(1) Return(POUT) }
Method(b132) { IIN0() ms1b(2) Return(POUT) }
Method(c132) { IIN0() ms1b(3) Return(POUT) }
Method(d132) { IIN0() ms1b(4) Return(POUT) }

/*
 * Bug 133 issue:
 *
 * SUMMARY: The Write access automatic dereference for Index reference doesn't work
 */
Method(ms1c, 1, Serialized)
{
	Name(ts, "ms1c")

	Method(m133, 1, Serialized)
	{
		Name(i000, 0)
		Name(s000, "q_er0000")
		Name(b000, Buffer(4) {1,0,3,4})
		Name(p000, Package(3) {5,0,7})

		Method(m000, 1)
		{
			Store(0x77, arg0)
		}

		OUTP("Bug 133: WRITE access to the initial object by reference in ArgX")

		if (LEqual(arg0, 0)) {
			OUTP("Writing by RefOf reference to Integer")

			Store(RefOf(i000), Local0)
			m000(Local0)
			if (LNotEqual(i000, 0x77)) {
				err(ts, z179, __LINE__, 0, 0, i000, 0x77)
			} else {
				OUTP("Ok 0")
			}
			OUTP(i000)

		} elseif (LEqual(arg0, 1)) {
			OUTP("Writing by Index to String")

			Index(s000, 1, Local0)
			m000(Local0)
			Store(Derefof(Local0), Local1)
			if (LNotEqual(Local1, 0x77)) {
				err(ts, z179, __LINE__, 0, 0, Local1, 0x77)
			} else {
				OUTP("Ok 1")
			}
			OUTP(s000)

		} elseif (LEqual(arg0, 2)) {
			OUTP("Writing by Index to Buffer")

			Index(b000, 1, Local0)
			m000(Local0)

			Store(Derefof(Local0), Local1)
			if (LNotEqual(Local1, 0x77)) {
				err(ts, z179, __LINE__, 0, 0, Local1, 0x77)
			} else {
				OUTP("Ok 2")
			}
			OUTP(b000)

		} elseif (LEqual(arg0, 3)) {
			OUTP("Check Index of Package")

			Index(p000, 1, Local0)

			Store(DerefOf(Local0), Local1)
			if (LNotEqual(Local1, 0)) {
				err(ts, z179, __LINE__, 0, 0, Local1, 0)
			} else {
				OUTP("Ok 3")
			}
			OUTP(Local1)

		} elseif (LEqual(arg0, 4)) {
			OUTP("Writing by Index to Package")

			Index(p000, 1, Local0)
			m000(Local0)

			Store(DerefOf(Local0), Local1)

			if (LNotEqual(Local1, 0x77)) {
				err(ts, z179, __LINE__, 0, 0, Local1, 0x77)
			} else {
				OUTP("Ok 4")
			}
			OUTP(Local1)
		}
	}

	Method(m000)
	{
		m133(0)

		if (ABUU) {
		} else {
			m133(1)
		}

		m133(2)
		m133(3)
		m133(4)
	}

	CH03(ts, z179, 0x06d, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { m133(0) }
		case (2) { m133(1) }
		case (3) { m133(2) }
		case (4) { m133(3) }
		case (5) { m133(4) }
	}
	CH03(ts, z179, 0x06e, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(a133) { IIN0() ms1c(1) Return(POUT) }
Method(b133) { IIN0() ms1c(2) Return(POUT) }
Method(c133) { IIN0() ms1c(3) Return(POUT) }
Method(d133) { IIN0() ms1c(4) Return(POUT) }
Method(e133) { IIN0() ms1c(5) Return(POUT) }

/*
 * Bug 134 issue:
 *
 * SUMMARY: Writing RefOf reference from inside Method breaks effectively local Arg
 */
Method(ms1d, 1, Serialized)
{
	Name(ts, "ms1d")

	Method(m134, 1, Serialized)
	{
		Name(i000, 0x11)
		Name(i001, 0x22)
		Name(i002, 0x33)
		Name(i003, 0x44)
		Name(i004, 0x55)
		Name(i005, 0x66)
		Name(i006, 0x77)

		Method(m000, 7)
		{
			OUTP("LocalX case of Method started:")

			Store(RefOf(i000), Local0)
			Store(Local0, Local1)
			Store(Local1, Local2)
			Store(Local2, Local3)
			Store(Local3, Local4)
			Store(Local4, Local5)
			Store(Local5, Local6)

			Store(0x88, Local6)

			if (LAnd(ABUU, LNot(q008))) {
				if (LNotEqual(i000, 0x88)) {
					err(ts, z179, __LINE__, 0, 0, i000, 0x88)
				}
			} elseif (LNotEqual(i000, 0x11)) {
				err(ts, z179, __LINE__, 0, 0, i000, 0x11)
			} else {
				if (LNotEqual(Local6, 0x88)) {
					err(ts, z179, __LINE__, 0, 0, Local6, 0x88)
				} else {
					OUTP("Ok 0:")
				}
				OUTP(Local6)
			}

			OUTP("LocalX case of Method finished")
		}

		Method(m001, 7)
		{
			OUTP("ArgX case of Method started:")

			Store(RefOf(i000), arg0)
			Store(arg0, arg1)
			Store(arg1, arg2)
			Store(arg2, arg3)
			Store(arg3, arg4)
			Store(arg4, arg5)
			Store(arg5, arg6)

			Store(0x88, arg6)

			if (LAnd(ABUU, LNot(q008))) {
				if (LNotEqual(i000, 0x88)) {
					err(ts, z179, __LINE__, 0, 0, i000, 0x88)
				}
			} elseif (LNotEqual(i000, 0x11)) {
				err(ts, z179, __LINE__, 0, 0, i000, 0x11)
			} else {
				if (LNotEqual(arg6, 0x88)) {
					err(ts, z179, __LINE__, 0, 0, arg6, 0x88)
				} else {
					OUTP("Ok 1:")
				}
				OUTP(arg6)
			}

			OUTP("ArgX case of Method finished")
		}

		Method(m002, 7)
		{
			OUTP("references in ArgX case of Method started:")

			Store(RefOf(i000), arg0)
			Store(arg0, arg1)
			Store(arg1, arg2)
			Store(arg2, arg3)
			Store(arg3, arg4)
			Store(arg4, arg5)
			Store(arg5, arg6)

			Store(0x88, arg6)

			if (LAnd(ABUU, LNot(q008))) {
				if (LNotEqual(i000, 0x88)) {
					err(ts, z179, __LINE__, 0, 0, i000, 0x88)
				}
			} elseif (LNotEqual(i000, 0x11)) {
				err(ts, z179, __LINE__, 0, 0, i000, 0x11)
				OUTP(i000)
			} else {
				Store(DerefOf(arg6), Local1)
				if (LNotEqual(Local1, 0x88)) {
					err(ts, z179, __LINE__, 0, 0, Local1, 0x88)
				} else {
					OUTP("Ok 1:")
				}
				OUTP(arg6)
			}

			OUTP("ArgX case of Method finished")
		}

		OUTP("Bug 134: ArgX term effectively becomes a LocalX term")

		if (LEqual(arg0, 0)) {
			m000(i000,i001,i002,i003,i004,i005,i006)
		} elseif (LEqual(arg0, 1)) {
			m001(i000,i001,i002,i003,i004,i005,i006)
		} elseif (LEqual(arg0, 2)) {
			m002(Refof(Local0),Refof(Local1),Refof(Local2),Refof(Local3),Refof(Local4),
				Refof(Local5),Refof(Local6))
		}
	}

	Method(m000)
	{
		m134(0)
		m134(1)
		m134(2)
	}

	CH03(ts, z179, 0x075, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { m134(0) }
		case (2) { m134(1) }
		case (3) { m134(2) }
	}
	CH03(ts, z179, 0x076, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(a134) { IIN0() ms1d(1) Return(POUT) }
Method(b134) { IIN0() ms1d(2) Return(POUT) }
Method(c134) { IIN0() ms1d(3) Return(POUT) }

/*
 * Bug 136 issue:
 *
 * SUMMARY: CopyObject of named Buffer to the longer named Buffer works incorrectly
 */
Method(ms1e,, Serialized)
{
	Name(ts, "ms1e")

	Method(m136,, Serialized)
	{
		Name(b000, Buffer(1){0x3c})
		Name(b001, Buffer(3){0x01, 0x02, 0x03})

		OUTP("Bug 136: CopyObject does not perform an implicit store")

		CopyObject(b000, b001)

		if (LEqual(b000, b001)) {
			OUTP("Ok")
		} else {
			err(ts, z179, __LINE__, 0, 0, b000, b001)
		}
		OUTP(b000)
		OUTP(b001)
	}

	CH03(ts, z179, 0x078, __LINE__, 0)
	m136()
	CH03(ts, z179, 0x079, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(a136) { IIN0() ms1e() Return(POUT) }

/*
 * Hot issue:
 *
 * Checks store of a Local Reference into the Package
 */
Method(ms1f, 1, Serialized)
{
	Name(ts, "ms1f")

	Name(I999, 0)
	Name(PREF, Package(4) {0xa5a5a5a5, I999, I999})

	Method(mlrp, 2)
	{
		Store(ObjectType(Arg0), Local0)
		Store(Arg0, Index(PREF, Arg1))
		CH03(ts, z179, 0x07a, __LINE__, 0)
		Store(ObjectType(Index(PREF, Arg1)), Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local1, Local0)
		}
	}

	Method(mlr0)
	{
		OUTP("Store a Local Reference to Uninit Package element")

		Store("Local0", Local0)

		mlrp(Refof(Local0), 3)
	}

	Method(mlr1)
	{
		OUTP("Store a Local Reference to Integer Package element")

		Store("Local0", Local0)

		mlrp(Refof(Local0), 0)
	}

	Method(mlr2)
	{
		OUTP("Store a Local Reference to Reference Package element")

		Store("Local0", Local0)

		mlrp(Refof(Local0), 1)
	}

	Method(mlr3)
	{
		OUTP("Store a Integer to Reference Package element")

		Store("Local0", Local0)

		mlrp(3, 2)
	}

	Method(m000)
	{
		mlr0()
		mlr1()
		mlr2()
		mlr3()
	}

	CH03(ts, z179, 0x07c, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { mlr0() }
		case (2) { mlr1() }
		case (3) { mlr2() }
		case (4) { mlr3() }
	}
	CH03(ts, z179, 0x07d, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(alrp) { IIN0() ms1f(1) Return(POUT) }
Method(blrp) { IIN0() ms1f(2) Return(POUT) }
Method(clrp) { IIN0() ms1f(3) Return(POUT) }
Method(dlrp) { IIN0() ms1f(4) Return(POUT) }
Method(elrp) { IIN0() ms1f(0) Return(POUT) }

/*
 * Hot issue:
 *
 * Forward reference within a control method
 */
Method(ms20, 1, Serialized)
{
	Name(ts, "ms20")

    Name (Y, 2)

	Method(mfr0,, Serialized)
	{
		OUTP("Forward reference within a control method 0")

	    Store (Y, Local0)
		if (LNotEqual(Local0, 2)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 2)
		}

	    Name (Y, 1)

	    Store (Y, Local0)
		if (LNotEqual(Local0, 1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 1)
		}
	}
	Method(mfr1,, Serialized)
	{
		OUTP("Natural reference within a control method")

	    Name (Y, 1)

	    Store (^Y, Local0)

		if (LNotEqual(Local0, 2)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 2)
		}

	    Store (Y, Local0)
		if (LNotEqual(Local0, 1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 1)
		}
	}

	Method(mfr2,, Serialized)
	{
		OUTP("Forward reference within a control method 2")

	    Store (^mfr2.Y, Local0)
		CH04(ts, 0, 0xff, z179, __LINE__, "^mfr2.Y", Local0)

	    Name (Y, 1)

	    Store (^mfr2.Y, Local0)
		if (LNotEqual(Local0, 1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 1)
		}
	}

	Method(mfr3,, Serialized)
	{
		OUTP("Forward reference within a control method 3")

	    Name (Y, 1)

	    Store (^mfr3.Y, Local0)
		if (LNotEqual(Local0, 1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 1)
		}
	}

	Method(m000)
	{
		mfr0()
		mfr1()

		if (ABUU) {
		} else {
			mfr2()
		}

		mfr3()
	}

	CH03(ts, z179, 0x085, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { mfr0() }
		case (2) { mfr1() }
		case (3) { mfr2() }
		case (4) { mfr3() }
	}
	CH03(ts, z179, 0x086, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(amfr) { IIN0() ms20(1) Return(POUT) }
Method(bmfr) { IIN0() ms20(2) Return(POUT) }
Method(cmfr) { IIN0() ms20(3) Return(POUT) }
Method(dmfr) { IIN0() ms20(4) Return(POUT) }

/*
 * Hot issue: AE_AML_METHOD_LIMIT
 *
 * Recursive Serialized method execution
 */
Method(ms21, 1, Serialized)
{
	Name(ts, "ms21")

	Method(aact, 1, Serialized)
	{
		if (Arg0) {
			Return (Add(Arg0, aact(Subtract(Arg0, 1))))
		} else {
			Return (0)
		}
	}

	Method(mac0)
	{
		OUTP("Recursive method execution aact(0)")
		OUTP(aact(0))
	}

	Method(mac1)
	{
		OUTP("Recursive method execution aact(1)")
		OUTP(aact(1))
	}

	Method(mac2)
	{
		OUTP("Recursive method execution aact(2)")
		OUTP(aact(2))
	}

	Method(mac3)
	{
		OUTP("Recursive method execution aact(6)")
		OUTP(aact(6))
	}

	Method(mac4)
	{
		OUTP("Recursive method execution aact(513)")
		OUTP(aact(513))
		CH04(ts, 0, 0xff, z179, __LINE__, "recursion", 513)
	}

	Method(m000)
	{
		mac0()
		mac1()
		mac2()
		mac3()

		if (ABUU) {
		} else {
			mac4()
		}
	}

	CH03(ts, z179, 0x088, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { mac0() }
		case (2) { mac1() }
		case (3) { mac2() }
		case (4) { mac3() }
		case (5) { mac4() }
	}
	CH03(ts, z179, 0x089, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(arec) { IIN0() ms21(1) Return(POUT) }
Method(brec) { IIN0() ms21(2) Return(POUT) }
Method(crec) { IIN0() ms21(3) Return(POUT) }
Method(drec) { IIN0() ms21(4) Return(POUT) }
Method(erec) { IIN0() ms21(5) Return(POUT) }

/*
 * Hot issue:
 *
 * Conditional reference within a control method
 */
Method(ms22, 1, Serialized)
{
	Name(ts, "ms22")

	Name(iact, 0)

	Method(cact, 1, Serialized)
	{
		if (Arg0) {
			Name(iact, 0xffffffff)
		}
		Return (iact)
	}

	Method(m000)
	{
		OUTP("Conditional reference within a control method 0")

		OUTP("expected iact 0:")
		Store(cact(0), Local0)

		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}
	}

	Method(m001)
	{
		OUTP("Conditional reference within a control method 1")

		OUTP("expected iact 0xffffffff:")
		Store(cact(1), Local0)

		if (LNotEqual(Local0, 0xffffffff)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0xffffffff)
		}
	}

	CH03(ts, z179, 0x08c, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000() m001() }
		case (1) { m000() }
		case (2) { m001() }
	}
	CH03(ts, z179, 0x08d, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(amcr) { IIN0() ms22(1) Return(POUT) }
Method(bmcr) { IIN0() ms22(2) Return(POUT) }

/*
 * Hot issue:
 *
 * Implicit return
 */
Method(ms23, 1, Serialized)
{
	Name(ts, "ms23")

	Method(mir0,, Serialized)
	{
		Name(fl00, 0)

		Method(m001)
		{
			if (fl00) {
				Store(Add (0xabcd, 0), Local1)
			} elseif (0) {
				return (1)
			}

		}

		OUTP("Implicit return no operator")

		OUTP("An exception is expected: ...")
		Store(m001(), Local0)
		CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
	}

	Method(mir1,, Serialized)
	{
		Name(fl00, 1)

		Method(m001)
		{
			if (fl00) {
				Store(Add (0xabcd, 0), Local1)
			} else {
				return (1)
			}
		}

		OUTP("Implicit return after Add")

		OUTP("0xabcd expected: ...")
		Store(m001(), Local0)

		if (SLCK) {
			if (CH03(ts, z179, 0x08f, __LINE__, 0)) {return}
			if (LNotEqual(Local0, 0xabcd)) {
				err(ts, z179, __LINE__, 0, 0, Local0, 0xabcd)
			}
		} else {
			CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
		}
	}

	Method(mir2,, Serialized)
	{
		Name(fl00, 0)

		Method(m001)
		{
			if (fl00) {
				Return (0xabce)
			} elseif (0) {
				return (1)
			}
		}

		OUTP("Implicit return no operator 2")

		OUTP("An exception is expected: ...")
		Store(m001(), Local0)
		CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
	}

	Method(mir3,, Serialized)
	{
		Name(fl00, 1)

		Method(m001)
		{
			if (fl00) {
				Return (0xabce)
			} else {
				return (1)
			}
		}

		OUTP("Explicit return conditionally")

		OUTP("0xabce expected: ...")
		Store(m001(), Local0)

		if (SLCK) {
			if (CH03(ts, z179, 0x093, __LINE__, 0)) {return}
			if (LNotEqual(Local0, 0xabce)) {
				err(ts, z179, __LINE__, 0, 0, Local0, 0xabce)
			}
		} else {
			CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
		}
	}

	Method(mir4,, Serialized)
	{
		Name(fl00, 0)
		Name(i000, 0xabcd0000)
		Name(i001, 0xabcd0001)

		Method(m000, 0, Serialized)
		{
			Switch (ToInteger (Store(0xabcd000f, i001))) {
				Case (0) {
					if (fl00) {
						Return (0)
					}
				}
			}
		}

		OUTP("Implicit return on Switch")

		Store(0xdddd9000, i000)

		Store(m000, i000)

		if (SLCK) {
			if (CH03(ts, z179, 0x096, __LINE__, 0)) {return}

			//y901: Predicate generates Implicit Return since ACPICA release 20080926
			if (y901) {
				Store(0, Local0)
			} else {
				Store(0xabcd000f, Local0)
			}
			if (LNotEqual(i000, Local0)) {
				err(ts, z179, __LINE__, 0, 0, i000, Local0)
			}
		} else {
			CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
		}
	}

	Method(mir5,, Serialized)
	{
		Name(fl00, 0)
		Name(i000, 0xabcd0000)
		Name(i001, 0xabcd0001)

		Method(m000)
		{
			if (Store(0xabcd000d, i001)) {
				if (fl00) {
					Return (0)
				}
			}
		}

		OUTP("Implicit return on If")

		Store(0xdddd9000, i000)

		Store(m000, i000)

		if (SLCK) {
			if (CH03(ts, z179, 0x099, __LINE__, 0)) {return}

			//y901: Predicate generates Implicit Return since ACPICA release 20080926
			if (y901) {
				Store(0, Local0)
			} else {
				Store(0xabcd000d, Local0)
			}
			if (LNotEqual(i000, Local0)) {
				err(ts, z179, __LINE__, 0, 0, i000, Local0)
			}
		} else {
			CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
		}
	}

	Method(mir6,, Serialized)
	{
		Name(fl00, 0)
		Name(i000, 0xabcd0000)
		Name(i001, 0xabcd0001)

		Method(m000)
		{
			While (Store(0xabcd000e, i001)) {
				if (fl00) {
					Return (0)
				}
				Break
			}
		}

		OUTP("Implicit return on While")

		Store(0xdddd9000, i000)

		Store(m000, i000)

		if (SLCK) {
			if (CH03(ts, z179, 0x09c, __LINE__, 0)) {return}

			//y901: Predicate generates Implicit Return since ACPICA release 20080926
			if (y901) {
				Store(0, Local0)
			} else {
				Store(0xabcd000e, Local0)
			}
			if (LNotEqual(i000, Local0)) {
				err(ts, z179, __LINE__, 0, 0, i000, Local0)
			}
		} else {
			CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
		}
	}

	Method(m000)
	{
		mir0()
		mir1()
		mir2()
		mir3()

		if (ABUU) {
		} else {
			mir4()
		}

		if (ABUU) {
		} else {
			mir5()
		}

		if (ABUU) {
		} else {
			mir6()
		}
	}

	CH03(ts, z179, 0x09f, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { mir0() }
		case (2) { mir1() }
		case (3) { mir2() }
		case (4) { mir3() }
		case (5) { mir4() }
		case (6) { mir5() }
		case (7) { mir6() }
	}
	CH03(ts, z179, 0x0a0, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(amir) { IIN0() ms23(1) Return(POUT) }
Method(bmir) { IIN0() ms23(2) Return(POUT) }
Method(cmir) { IIN0() ms23(3) Return(POUT) }
Method(dmir) { IIN0() ms23(4) Return(POUT) }
Method(emir) { IIN0() ms23(5) Return(POUT) }
Method(fmir) { IIN0() ms23(6) Return(POUT) }
Method(gmir) { IIN0() ms23(7) Return(POUT) }

/*
 * Hot issue:
 *
 * Increment/Decrement with String/Buffer
 */
Method(ms24,, Serialized)
{
	Name(ts, "ms24")

	Method(mmid,, Serialized)
	{
		Name(s000, "0321")
		Name(s001, "0321")
		Name(b000, Buffer(3){0x21, 0x03, 0x00})
		Name(b001, Buffer(3){0x21, 0x03, 0x00})

		OUTP("Increment/Decrement with String/Buffer")

		OUTP(s000)
		OUTP(s001)
		Subtract(s000, 1, s000)
		Decrement(s001)

		Store(ObjectType(s000), Local0)
		Store(ObjectType(s001), Local1)

		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		} elseif (LNotEqual(s000, s001)) {
			err(ts, z179, __LINE__, 0, 0, s000, s001)
		} else {
			OUTP("Ok Subtract/Decrement for String")
		}

		OUTP("======")

		OUTP(b000)
		OUTP(b001)
		Add(b000, 1, b000)
		Increment(b001)

		Store(ObjectType(b000), Local0)
		Store(ObjectType(b001), Local1)

		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		} elseif (LNotEqual(b000, b001)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		} else {
			OUTP("Ok Add/Increment for Buffer")
		}
	}

	CH03(ts, z179, 0x0a5, __LINE__, 0)
	mmid()
	CH03(ts, z179, 0x0a6, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(amid) { IIN0() ms24() Return(POUT) }


/*
 * Hot issue:
 *
 * Check Store(..., DeRefof(...)) behavior
 */
Method(ms25, 1, Serialized)
{
	Name(ts, "ms25")

	Method(msd0,, Serialized)
	{
		Name(i000, 0xffffffff)
		Name(i001, 0x12345678)

		OUTP("Check Store(..., DeRefof(...)) behavior: none DeRefof")

		Store(i001, Refof(i000))
		CH03(ts, z179, 0x0a7, __LINE__, 0)
		if (LNotEqual(i000, 0x12345678)) {
			err(ts, z179, __LINE__, 0, 0, i000, 0x12345678)
		}
	}

	Method(msd1,, Serialized)
	{
		Name(i000, 0xffffffff)
		Name(i001, 0x12345678)

		OUTP("Check Store(..., DeRefof(...)) behavior: Refof(Named)")

		Store(i001, DeRefof(Refof(i000)))
		CH03(ts, z179, 0x0a9, __LINE__, 0)
		if (LNotEqual(i000, 0x12345678)) {
			err(ts, z179, __LINE__, 0, 0, i000, 0x12345678)
		}
	}

	Method(msd2,, Serialized)
	{
		Name(i000, 0xffffffff)
		Name(i001, 0x12345678)

		OUTP("Check Store(..., DeRefof(...)) behavior: Refof in LocalX")

		Store(Refof(i000), Local2)

		Store(i001, DeRefof(Local2))
		CH03(ts, z179, 0x0ab, __LINE__, 0)
		if (LNotEqual(i000, 0x12345678)) {
			err(ts, z179, __LINE__, 0, 0, i000, 0x12345678)
		}
	}

	Method(msd3,, Serialized)
	{
		Name(i000, 0xffffffff)
		Name(i001, 0x12345678)

		OUTP("Check Store(..., DeRefof(...)) behavior: DeRefof(2xRefof)")

		Store(Refof(i000), Local1)
		Store(Refof(Local1), Local2)

		Store(i001, DeRefof(Local2))
		CH03(ts, z179, 0x0ad, __LINE__, 0)

		if (LNotEqual(i000, 0xffffffff)) {
			err(ts, z179, __LINE__, 0, 0, i000, 0xffffffff)
		}

		Store(Derefof(Local1), Local4)
		if (CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)) {
		} elseif (LNotEqual(Local1, 0x12345678)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 0x12345678)
		}
	}

	CH03(ts, z179, 0x0b1, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { msd0() msd1() msd2() msd3() }
		case (1) { msd0() }
		case (2) { msd1() }
		case (3) { msd2() }
		case (4) { msd3() }
	}
	CH03(ts, z179, 0x0b2, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(amsd) { IIN0() ms25(1) Return(POUT) }
Method(bmsd) { IIN0() ms25(2) Return(POUT) }
Method(cmsd) { IIN0() ms25(3) Return(POUT) }
Method(dmsd) { IIN0() ms25(4) Return(POUT) }

// Video memory address to maintain SystemMemory OpRegions
// Name(VMEM, 0xA0000) // VGA memory
// Name(VMEM, 0xF0000000) // T22 Savage3
// Name(VMEM, 0xD0000000) // IntelliStation Z Pro NVidia
Name(VMEM, 0xA0000) // VGA memory

// SystemMemory OpRegions base address is maintained flag
Name(SMBA, 1)

/*
 * Hot issue:
 *
 * Exceeding Field Unit
 */
Method(ms26, 1, Serialized)
{
	Name(ts, "ms26")

	OperationRegion(OPR0, SystemMemory, VMEM, 256)

	Method(rfu0,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, Preserve) {
			g001, 0x80,
		}

		Field(OPR0, ByteAcc, NoLock, Preserve) {
			Offset(0x8), FU01, 8,
		}

		OUTP("Store Integer exceeding Field Unit")

		Store(0, g001)

		Store(FU01, Local0)
		Store(0, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(0x5a, FU01)
		Store(FU01, Local0)
		Store(0x5a, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(0x3c69, FU01)
		Store(FU01, Local0)
		Store(0x69, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}
	}

	Method(rfu1,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, Preserve) {
			g001, 0x80,
		}

		Field(OPR0, ByteAcc, NoLock, Preserve) {
			Offset(0x8), FU01, 8,
		}

		OUTP("Store Buffer exceeding Field Unit")

		Store(0, g001)

		Store(FU01, Local0)
		Store(0, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(0x5a, FU01)
		Store(FU01, Local0)
		Store(0x5a, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(Buffer(){0x3c, 0x69}, FU01)
		Store(FU01, Local0)
		Store(0x3c, Local1)
		if (LAnd(ABUU, LNot(q009))) {
			Store(0x69, Local1)
			if (LNotEqual(Local0, Local1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, Local1)
			}
		} elseif (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}
	}

	Method(rfu2,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, Preserve) {
			g001, 0x80,
		}

		Field(OPR0, ByteAcc, NoLock, Preserve) {
			Offset(0x8), FU01, 8,
		}

		OUTP("Store String exceeding Field Unit")

		Store(0, g001)

		Store(FU01, Local0)
		Store(0, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(0x5a, FU01)
		Store(FU01, Local0)
		Store(0x5a, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store("79", FU01)
		Store(FU01, Local0)
		Store(0x37, Local1)
		if (LAnd(ABUU, LNot(q009))) {
			Store(0x39, Local1)
			if (LNotEqual(Local0, Local1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, Local1)
			}
		} elseif (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}
	}

	Method(rfu3,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, Preserve) {
			g001, 0x80,
		}

		Field(OPR0, ByteAcc, NoLock, Preserve) {
			Offset(0x8), FU01, 6, FU02, 2
		}

		OUTP("Store Buffer exceeding 6-bit Field Unit")

		Store(0, g001)

		Store(FU01, Local0)
		Store(0, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(0x5a, FU01)
		Store(FU01, Local0)
		Store(0x1a, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(Buffer(){0x7c, 0x69}, FU01)
		Store(FU01, Local0)
		Store(0x3c, Local1)
		if (LAnd(ABUU, LNot(q009))) {
			Store(0x29, Local1)
			if (LNotEqual(Local0, Local1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, Local1)
			}
		} elseif (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(FU02, Local0)
		Store(0, Local1)
		if (LAnd(ABUU, LNot(q009))) {
			Store(0x01, Local1)
			if (LNotEqual(Local0, Local1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, Local1)
			}
		} elseif (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}
	}

	Method(rfu4,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, Preserve) {
			g001, 0x80,
		}

		Field(OPR0, ByteAcc, NoLock, Preserve) {
			Offset(0x8), FU01, 6, FU02, 2
		}

		OUTP("Store String exceeding 6-bit Field Unit")

		Store(0, g001)

		Store(FU01, Local0)
		Store(0, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(0x5a, FU01)
		Store(FU01, Local0)
		Store(0x1a, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store("79", FU01)
		Store(FU01, Local0)
		Store(0x37, Local1)
		if (LAnd(ABUU, LNot(q009))) {
			Store(0x39, Local1)
			if (LNotEqual(Local0, Local1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, Local1)
			}
		} elseif (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(FU02, Local0)
		Store(0, Local1)
		if (LAnd(ABUU, LNot(q009))) {
			Store(0x01, Local1)
			if (LNotEqual(Local0, Local1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, Local1)
			}
		} elseif (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}
	}

	Method(rfu5,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, Preserve) {
			g001, 0x80,
		}

		Field(OPR0, ByteAcc, NoLock, Preserve) {
			Offset(0x8), FU01, 10, FU02, 6
		}

		OUTP("Store Buffer exceeding 10-bit Field Unit")

		Store(0, g001)

		Store(FU01, Local0)
		Store(0, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(0x5a, FU01)
		Store(FU01, Local0)
		Store(0x5a, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(Buffer(){0x3c, 0x69}, FU01)
		Store(FU01, Local0)
		Store(0x13c, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(FU02, Local0)
		Store(0, Local1)
		if (LAnd(ABUU, LNot(q009))) {
			Store(0x1a, Local1)
			if (LNotEqual(Local0, Local1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, Local1)
			}
		} elseif (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}
	}

	Method(rfu6,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, Preserve) {
			g001, 0x80,
		}

		Field(OPR0, ByteAcc, NoLock, Preserve) {
			Offset(0x8), FU01, 10, FU02, 6
		}

		OUTP("Store String exceeding 10-bit Field Unit")

		Store(0, g001)

		Store(FU01, Local0)
		Store(0, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(0x5a, FU01)
		Store(FU01, Local0)
		Store(0x5a, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store("79", FU01)
		Store(FU01, Local0)
		Store(0x137, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(FU02, Local0)
		Store(0, Local1)
		if (LAnd(ABUU, LNot(q009))) {
			Store(0x0e, Local1)
			if (LNotEqual(Local0, Local1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, Local1)
			}
		} elseif (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}
	}

	Method(rfu7,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, Preserve) {
			g001, 0x80,
		}

		Field(OPR0, ByteAcc, NoLock, Preserve) {
			Offset(0x8), FU01, 10, FU02, 6
		}

		OUTP("Store 3-byte Buffer exceeding 10-bit Field Unit")

		Store(0, g001)

		Store(FU01, Local0)
		Store(0, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(0x5a, FU01)
		Store(FU01, Local0)
		Store(0x5a, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(Buffer(){0x3c, 0x69, 0xa5}, FU01)
		Store(FU01, Local0)
		Store(0x13c, Local1)
		if (LAnd(ABUU, LNot(q009))) {
			Store(0xa5, Local1)
			if (LNotEqual(Local0, Local1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, Local1)
			}
		} elseif (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(FU02, Local0)
		Store(0, Local1)
		if (LAnd(ABUU, LNot(q009))) {
			Store(0x1a, Local1)
			if (LNotEqual(Local0, Local1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, Local1)
			}
		} elseif (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}
	}

	Method(rfu8,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, Preserve) {
			g001, 0x80,
		}

		Field(OPR0, ByteAcc, NoLock, Preserve) {
			Offset(0x8), FU01, 10, FU02, 6
		}

		OUTP("Store 3-char String exceeding 10-bit Field Unit")

		Store(0, g001)

		Store(FU01, Local0)
		Store(0, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(0x5a, FU01)
		Store(FU01, Local0)
		Store(0x5a, Local1)
		if (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store("795", FU01)
		Store(FU01, Local0)
		Store(0x137, Local1)
		if (LAnd(ABUU, LNot(q009))) {
			Store(0x35, Local1)
			if (LNotEqual(Local0, Local1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, Local1)
			}
		} elseif (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}

		Store(FU02, Local0)
		Store(0, Local1)
		if (LAnd(ABUU, LNot(q009))) {
			Store(0x0e, Local1)
			if (LNotEqual(Local0, Local1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, Local1)
			}
		} elseif (LNotEqual(Local0, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}
	}

	Method(m000)
	{
		rfu0()
		rfu1()
		rfu2()
		rfu3()
		rfu4()
		rfu5()
		rfu6()
		rfu7()
		rfu8()
	}

	CH03(ts, z179, 0x0d4, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { rfu0() }
		case (2) { rfu1() }
		case (3) { rfu2() }
		case (4) { rfu3() }
		case (5) { rfu4() }
		case (6) { rfu5() }
		case (7) { rfu6() }
		case (8) { rfu7() }
		case (9) { rfu8() }
	}
	CH03(ts, z179, 0x0d5, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(arfu) { IIN0() ms26(1) Return(POUT) }
Method(brfu) { IIN0() ms26(2) Return(POUT) }
Method(crfu) { IIN0() ms26(3) Return(POUT) }
Method(drfu) { IIN0() ms26(4) Return(POUT) }
Method(erfu) { IIN0() ms26(5) Return(POUT) }
Method(frfu) { IIN0() ms26(6) Return(POUT) }
Method(grfu) { IIN0() ms26(7) Return(POUT) }
Method(hrfu) { IIN0() ms26(8) Return(POUT) }
Method(irfu) { IIN0() ms26(9) Return(POUT) }


/*
 * Hot issue:
 *
 * Check IndexField implementation
 */
Method(ms27, 1, Serialized)
{
	Name(ts, "ms27")

	OperationRegion(OPR0, SystemMemory, VMEM, 256)

	Field(OPR0, ByteAcc, NoLock, Preserve) {
		tot0, 32,
		tot1, 32,
	}

	Method(ifd0,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx1, 4,
			dta1, 3,
		}

		IndexField(idx1, dta1, ByteAcc, NoLock, WriteAsZeros) {
			re10, 3,
			re11, 3,
			re12, 3,
			re13, 3,
		}

		Method(TRY0, 3, Serialized)
		{
			Store(Zero, tot0)
			switch (ToInteger (Arg0)) {
			Case (0) {Store(Ones, ^re10)}
			Case (1) {Store(Ones, ^re11)}
			Case (2) {Store(Ones, ^re12)}
			Case (3) {Store(Ones, ^re13)}
			}

			Store(idx1, Local0)
			Store(dta1, Local1)

			Multiply(arg0, 2, Local2)
			if (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
			if (LNotEqual(Local1, arg2)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg2)
			}
		}

		OUTP("Check IndexField ByteAcc 4-3 Ones write 3-3-3-3")

		TRY0(0, 0, 0x7)
		TRY0(1, 0, 0x0)

		Store(0x1, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0x07, Local0)
		}
		TRY0(2, 0, Local0)

		TRY0(3, 0, 0x06)
	}

	Method(ifd1,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx1, 8,
			dta1, 8,
		}

		IndexField(idx1, dta1, ByteAcc, NoLock, WriteAsZeros) {
			re10, 8,
			re11, 8,
			re12, 8,
			re13, 8,
		}

		Method(TRY0, 3, Serialized)
		{
			Store(Zero, tot0)
			switch (ToInteger (Arg0)) {
			Case (0) {Store(0x12345678, ^re10)}
			Case (1) {Store(0x12345678, ^re11)}
			Case (2) {Store(0x12345678, ^re12)}
			Case (3) {Store(0x12345678, ^re13)}
			}

			Store(idx1, Local0)
			Store(dta1, Local1)

			Multiply(arg0, 2, Local2)
			if (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
			if (LNotEqual(Local1, arg2)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg2)
			}
		}

		OUTP("Check IndexField ByteAcc 0x12345678 write 8-8-8-8")

		TRY0(0, 0, 0x78)
		TRY0(1, 1, 0x78)
		TRY0(2, 2, 0x78)
		TRY0(3, 3, 0x78)
	}

	Method(ifd2,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx1, 8,
			dta1, 8,
		}

		IndexField(idx1, dta1, ByteAcc, NoLock, WriteAsZeros) {
			, 7,
			re10, 1,
			re11, 1,
			Offset(2),
			re12, 4,
			re13, 4,
		}

		Method(TRY0, 3, Serialized)
		{
			Store(Zero, tot0)
			switch (ToInteger (Arg0)) {
			Case (0) {Store(Ones, ^re10)}
			Case (1) {Store(Ones, ^re11)}
			Case (2) {Store(Ones, ^re12)}
			Case (3) {Store(Ones, ^re13)}
			}

			Store(idx1, Local0)
			Store(dta1, Local1)

			Multiply(arg0, 2, Local2)
			if (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
			if (LNotEqual(Local1, arg2)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg2)
			}
		}

		OUTP("Check IndexField ByteAcc Ones write Offset (0:7)1-(1:0)1-(2:0)4-4")

		TRY0(0, 0, 0x80)

		Store(0x01, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0xff, Local0)
		}
		TRY0(1, 1, Local0)

		Store(0x0f, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0xff, Local0)
		}
		TRY0(2, 2, Local0)

		TRY0(3, 2, 0xf0)
	}

	Method(ifd3,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx1, 8,
			dta1, 8,
		}

		IndexField(idx1, dta1, ByteAcc, NoLock, WriteAsZeros) {
			Offset(1),
			re10, 8,
			Offset(2),
			re11, 8,
			Offset(7),
			re12, 8,
			Offset(16),
			re13, 8,
		}

		Method(TRY0, 3, Serialized)
		{
			Store(Zero, tot0)
			switch (ToInteger (Arg0)) {
			Case (0) {Store(0x12345678, ^re10)}
			Case (1) {Store(0x12345678, ^re11)}
			Case (2) {Store(0x12345678, ^re12)}
			Case (3) {Store(0x12345678, ^re13)}
			}

			Store(idx1, Local0)
			Store(dta1, Local1)

			Multiply(arg0, 2, Local2)
			if (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
			if (LNotEqual(Local1, arg2)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg2)
			}
		}

		OUTP("Check IndexField ByteAcc 0x12345678 write Offset (1:0)8-(2:0)8-(7:0)8-(16:0)8")

		TRY0(0, 1, 0x78)
		TRY0(1, 2, 0x78)
		TRY0(2, 7, 0x78)
		TRY0(3, 16, 0x78)
	}

	CH03(ts, z179, 0x0e6, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) {
			ifd0()
			ifd1()
			ifd2()
			ifd3()
		}
		case (1) { ifd0() }
		case (2) { ifd1() }
		case (3) { ifd2() }
		case (4) { ifd3() }
	}
	CH03(ts, z179, 0x0e7, __LINE__, 0)
}

Method(mt27, 1, Serialized)
{
	Name(ts, "mt27")

	OperationRegion(OPR0, SystemMemory, VMEM, 256)

	Field(OPR0, ByteAcc, NoLock, Preserve) {
		tot0, 32,
		tot1, 32,
	}

	Method(ifd4,, Serialized)
	{
		Field(OPR0, WordAcc, NoLock, WriteAsZeros) {
			idx1, 16,
			dta1, 16,
		}

		IndexField(idx1, dta1, WordAcc, NoLock, WriteAsZeros) {
			re10, 8,
			re11, 8,
			re12, 8,
			re13, 8,
		}

		Method(TRY0, 3, Serialized)
		{
			Store(Zero, tot0)
			switch (ToInteger (Arg0)) {
			Case (0) {Store(0x12345678, ^re10)}
			Case (1) {Store(0x12345678, ^re11)}
			Case (2) {Store(0x12345678, ^re12)}
			Case (3) {Store(0x12345678, ^re13)}
			}

			Store(idx1, Local0)
			Store(dta1, Local1)

			Multiply(arg0, 2, Local2)
			if (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
			if (LNotEqual(Local1, arg2)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg2)
			}
		}

		OUTP("Check IndexField WordAcc Ones write 8-8-8-8")

		Store(0x0078, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0x5678, Local0)
		}
		TRY0(0, 0, Local0)

		TRY0(1, 0, 0x7800)

		Store(0x0078, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0x5678, Local0)
		}
		TRY0(2, 2, Local0)

		TRY0(3, 2, 0x7800)
	}

	Method(ifd5,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx1, 8,
			dta1, 8,
		}

		IndexField(idx1, dta1, ByteAcc, NoLock, WriteAsZeros) {
			, 1,
			re10, 8,
			, 1,
			re11, 8,
			, 1,
			re12, 8,
			, 1,
			re13, 8,
		}

		Method(TRY0, 3, Serialized)
		{
			Store(Zero, tot0)
			switch (ToInteger (Arg0)) {
			Case (0) {Store(Ones, ^re10)}
			Case (1) {Store(Ones, ^re11)}
			Case (2) {Store(Ones, ^re12)}
			Case (3) {Store(Ones, ^re13)}
			}

			Store(idx1, Local0)
			Store(dta1, Local1)

			Multiply(arg0, 2, Local2)
			if (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
			if (LNotEqual(Local1, arg2)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg2)
			}
		}

		OUTP("Check IndexField ByteAcc Ones write (:1)8-(:1)8-(:1)8-(:1)8")

		TRY0(0, 1, 0x1)
		TRY0(1, 2, 0x3)
		TRY0(2, 3, 0x7)
		TRY0(3, 4, 0xf)
	}

	Method(ifd6,, Serialized)
	{
		Field(OPR0, DWordAcc, NoLock, WriteAsZeros) {
			idx1, 32,
			dta1, 32,
		}

		IndexField(idx1, dta1, DWordAcc, NoLock, WriteAsZeros) {
			re10, 8,
			re11, 8,
			re12, 8,
			re13, 8,
		}

		Method(TRY0, 3, Serialized)
		{
			Store(Zero, tot0)
			Store(Zero, tot1)
			switch (ToInteger (Arg0)) {
			Case (0) {Store(Ones, ^re10)}
			Case (1) {Store(Ones, ^re11)}
			Case (2) {Store(Ones, ^re12)}
			Case (3) {Store(Ones, ^re13)}
			}

			Store(idx1, Local0)
			Store(dta1, Local1)

			Multiply(arg0, 2, Local2)
			if (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
			if (LNotEqual(Local1, arg2)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg2)
			}
		}

		OUTP("Check IndexField DWordAcc Ones write 8-8-8-8")

		Store(0xff, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0xffffffff, Local0)
		}
		TRY0(0, 0, Local0)

		Store(0xff00, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0xffffff00, Local0)
		}
		TRY0(1, 0, Local0)

		Store(0xff0000, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0xffff0000, Local0)
		}
		TRY0(2, 0, Local0)

		TRY0(3, 0, 0xff000000)
	}

	Method(ifd7,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx1, 8,
			dta1, 8,
		}

		IndexField(idx1, dta1, ByteAcc, NoLock, WriteAsZeros) {
			, 2,
			re10, 7,
			, 2,
			re11, 7,
			, 2,
			re12, 7,
			, 2,
			re13, 7,
		}

		Method(TRY0, 3, Serialized)
		{
			Store(Zero, tot0)
			switch (ToInteger (Arg0)) {
			Case (0) {Store(Ones, ^re10)}
			Case (1) {Store(Ones, ^re11)}
			Case (2) {Store(Ones, ^re12)}
			Case (3) {Store(Ones, ^re13)}
			}

			Store(idx1, Local0)
			Store(dta1, Local1)

			Multiply(arg0, 2, Local2)
			if (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
			if (LNotEqual(Local1, arg2)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg2)
			}
		}

		OUTP("Check IndexField ByteAcc Ones write (:2)7-(:2)7-(:2)7-(:2)7")

		Store(0x1, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0x3, Local0)
		}
		TRY0(0, 1, Local0)

		Store(0x3, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0x7, Local0)
		}
		TRY0(1, 2, Local0)

		Store(0x7, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0xf, Local0)
		}
		TRY0(2, 3, Local0)

		Store(0xf, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0x1f, Local0)
		}
		TRY0(3, 4, Local0)
	}

	CH03(ts, z179, 0x0e8, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) {
			ifd4()
			ifd5()
			ifd6()
			ifd7()
		}
		case (5) { ifd4() }
		case (6) { ifd5() }
		case (7) { ifd6() }
		case (8) { ifd7() }
	}
	CH03(ts, z179, 0x0e9, __LINE__, 0)
}

Method(mu27, 1, Serialized)
{
	Name(ts, "mu27")

	OperationRegion(OPR0, SystemMemory, VMEM, 256)

	Field(OPR0, ByteAcc, NoLock, Preserve) {
		tot0, 32,
		tot1, 32,
	}

	Method(ifd8,, Serialized)
	{
		Field(OPR0, DWordAcc, NoLock, WriteAsZeros) {
			idx1, 32,
			dta1, 32,
		}

		IndexField(idx1, dta1, DWordAcc, NoLock, WriteAsZeros) {
			Offset(1),
			re10, 8,
			Offset(4),
			re11, 8,
			Offset(9),
			re12, 8,
			Offset(12),
			re13, 8,
		}

		Method(TRY0, 3, Serialized)
		{
			Store(Zero, tot0)
			Store(Zero, tot1)
			switch (ToInteger (Arg0)) {
			Case (0) {Store(0x12345678, ^re10)}
			Case (1) {Store(0x12345678, ^re11)}
			Case (2) {Store(0x12345678, ^re12)}
			Case (3) {Store(0x12345678, ^re13)}
			}

			Store(idx1, Local0)
			Store(dta1, Local1)

			Multiply(arg0, 2, Local2)
			if (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
			if (LNotEqual(Local1, arg2)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg2)
			}
		}

		OUTP("Check IndexField DWordAcc 0x12345678 write Offset (1)8-(4)8-(9)8-(12)8")

		Store(0x7800, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0x34567800, Local0)
		}
		TRY0(0, 0, Local0)

		Store(0x78, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0x12345678, Local0)
		}
		TRY0(1, 4, Local0)

		Store(0x7800, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0x34567800, Local0)
		}
		TRY0(2, 8, Local0)

		Store(0x78, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0x12345678, Local0)
		}
		TRY0(3, 12, Local0)
	}

	Method(ifd9,, Serialized)
	{
		Field(OPR0, WordAcc, NoLock, WriteAsZeros) {
			idx1, 16,
			dta1, 16,
		}

		IndexField(idx1, dta1, WordAcc, NoLock, WriteAsZeros) {
			Offset(1),
			re10, 8,
			Offset(4),
			re11, 8,
			Offset(9),
			re12, 8,
			Offset(12),
			re13, 8,
		}

		Method(TRY0, 3, Serialized)
		{
			Store(Zero, tot0)
			switch (ToInteger (Arg0)) {
			Case (0) {Store(0x12345678, ^re10)}
			Case (1) {Store(0x12345678, ^re11)}
			Case (2) {Store(0x12345678, ^re12)}
			Case (3) {Store(0x12345678, ^re13)}
			}

			Store(idx1, Local0)
			Store(dta1, Local1)

			Multiply(arg0, 2, Local2)
			if (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
			if (LNotEqual(Local1, arg2)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg2)
			}
		}

		OUTP("Check IndexField WordAcc 0x12345678 write Offset (1)8-(4)8-(9)8-(12)8")

		TRY0(0, 0, 0x7800)

		Store(0x78, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0x5678, Local0)
		}
		TRY0(1, 4, Local0)

		TRY0(2, 8, 0x7800)

		Store(0x78, Local0)
		if (LAnd(ABUU, LNot(q00a))) {
			Store(0x5678, Local0)
		}
		TRY0(3, 12, Local0)
	}

	Method(ifda,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx1, 16,
			dta1, 16,
		}

		IndexField(idx1, dta1, ByteAcc, NoLock, WriteAsZeros) {
			Offset(1),
			re10, 8,
			Offset(4),
			re11, 8,
			Offset(9),
			re12, 8,
			Offset(12),
			re13, 8,
		}

		Method(TRY0, 3, Serialized)
		{
			Store(Zero, tot0)
			switch (ToInteger (Arg0)) {
			Case (0) {Store(0x12345678, ^re10)}
			Case (1) {Store(0x12345678, ^re11)}
			Case (2) {Store(0x12345678, ^re12)}
			Case (3) {Store(0x12345678, ^re13)}
			}

			Store(idx1, Local0)
			Store(dta1, Local1)

			Multiply(arg0, 2, Local2)
			if (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
			if (LNotEqual(Local1, arg2)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg2)
			}
		}

		OUTP("Check IndexField ByteAcc 0x12345678 write Offset (1)8-(4)8-(9)8-(12)8")

		TRY0(0, 1, 0x78)
		TRY0(1, 4, 0x78)
		TRY0(2, 9, 0x78)
		TRY0(3, 12, 0x78)
	}

	Method(ifdb,, Serialized)
	{
		Field(OPR0, AnyAcc, NoLock, WriteAsZeros) {
			idx1, 16,
			dta1, 16,
		}

		IndexField(idx1, dta1, AnyAcc, NoLock, WriteAsZeros) {
			Offset(1),
			re10, 8,
			Offset(4),
			re11, 8,
			Offset(9),
			re12, 8,
			Offset(12),
			re13, 8,
		}

		Method(TRY0, 3, Serialized)
		{
			Store(Zero, tot0)
			switch (ToInteger (Arg0)) {
			Case (0) {Store(0x12345678, ^re10)}
			Case (1) {Store(0x12345678, ^re11)}
			Case (2) {Store(0x12345678, ^re12)}
			Case (3) {Store(0x12345678, ^re13)}
			}

			Store(idx1, Local0)
			Store(dta1, Local1)

			Multiply(arg0, 2, Local2)
			if (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
			if (LNotEqual(Local1, arg2)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg2)
			}
		}

		OUTP("Check IndexField AnyAcc 0x12345678 write Offset (1)8-(4)8-(9)8-(12)8")

		TRY0(0, 1, 0x78)
		TRY0(1, 4, 0x78)
		TRY0(2, 9, 0x78)
		TRY0(3, 12, 0x78)
	}

	CH03(ts, z179, 0x0ea, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) {
			ifd8()
			ifd9()
			ifda()
			ifdb()
		}
		case (9) { ifd8() }
		case (10) { ifd9() }
		case (11) { ifda() }
		case (12) { ifdb() }
	}
	CH03(ts, z179, 0x0eb, __LINE__, 0)
}

Method(mv27, 1, Serialized)
{
	Name(ts, "mv27")

	OperationRegion(OPR0, SystemMemory, VMEM, 256)

	Field(OPR0, ByteAcc, NoLock, Preserve) {
		tot0, 32,
		tot1, 32,
	}

	Method(ifdc,, Serialized)
	{
		Field(OPR0, WordAcc, NoLock, WriteAsZeros) {
			idx0, 16,
			dta0, 16,
		}
		IndexField(idx0, dta0, WordAcc, NoLock, WriteAsZeros) {
			idf0, 8,
			Offset(3),
			idf1, 8,
			Offset(6),
			idf2, 8,
			Offset(11),
			idf3, 8,
		}

		Method(TRY0, 4)
		{
			Store(idx0, Local0)
			Store(dta0, Local1)

			Multiply(arg0, 2, Local2)
			if (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
			if (LNotEqual(Local1, arg2)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg2)
			}
		}

		OUTP("Check IndexField WordAcc read")

		Store(0x1234ffff, tot0)
		TRY0(0, 0, 0x1234, idf0)

		Store(0x5678ffff, tot0)
		TRY0(2, 2, 0x5678, idf1)

		Store(0x9abcffff, tot0)
		TRY0(3, 6, 0x9abc, idf2)

		Store(0xde01ffff, tot0)
		TRY0(4, 10, 0xde01, idf3)
	}

	Method(TRY4, 5)
	{
		Method(TRY0, 3)
		{
			Store(arg0, tot0)
			Store(Derefof(arg1), Local0)
			Store(tot0, Local1)
			Store(DeRefof(Index(arg2, 0)), Local2)
			Store(DeRefof(Index(arg2, 1)), Local3)
			Store(DeRefof(Index(arg2, 2)), Local4)

			Add(0x140, Multiply(Local2, 2), Local2)
			if (LNotEqual(Local0, Local3)) {
				err(ts, z179, __LINE__, 0, 0, Local0, Local3)
			}
			if (LNotEqual(Local1, Local4)) {
				err(ts, z179, __LINE__, 0, 0, Local1, Local4)
			}
		}

		Store(DeRefof(Index(arg0, 0)), Local0)
		TRY0(Local0, arg1, DeRefof(Index(arg0, 1)))
		TRY0(Local0, arg2, DeRefof(Index(arg0, 2)))
		TRY0(Local0, arg3, DeRefof(Index(arg0, 3)))
		TRY0(Local0, arg4, DeRefof(Index(arg0, 4)))
	}

	Method(ifdd,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, Preserve) {
			idx1, 8,
			dta1, 8,
		}

		IndexField(idx1, dta1, ByteAcc, NoLock, Preserve) {
			, 4,
			re10, 1,
			re11, 1,
			re12, 3,
			re13, 3,
		}

		OUTP("Check IndexField implementation ByteAcc 4,1-1-3-3")

		Store(Package(){0xa5a5a5a5,
				Package(){0, 0x0, 0xa5a5a500},
				Package(){1, 0x1, 0xa5a5a500},
				Package(){2, 0x6, 0xa5a5a501},
				Package(){3, 0x2, 0xa5a5a501},},
			Local0)

		if (LAnd(ABUU, LNot(q00a))) {
			Store(0x96, Index(DeRefof(Index(Local0, 3)), 1))
		}

		TRY4(Local0, Refof(re10), Refof(re11), Refof(re12), Refof(re13))


		Store(Package(){0x5a5a5a5a,
				Package(){4, 0x1, 0x5a5a5a00},
				Package(){5, 0x0, 0x5a5a5a00},
				Package(){6, 0x1, 0x5a5a5a01},
				Package(){7, 0x5, 0x5a5a5a01},},
			Local0)

		if (LAnd(ABUU, LNot(q00a))) {
			Store(0x169, Index(DeRefof(Index(Local0, 3)), 1))
		}

		TRY4(Local0, Refof(re10), Refof(re11), Refof(re12), Refof(re13))
	}

	Method(ifde,, Serialized)
	{
		Field(OPR0, WordAcc, NoLock, Preserve) {
			idx1, 16,
			dta1, 16,
		}

		IndexField(idx1, dta1, WordAcc, NoLock, Preserve) {
			, 4,
			re10, 1,
			re11, 1,
			re12, 3,
			re13, 3,
		}

		OUTP("Check IndexField implementation WordAcc 4,1-1-3-3")

		Store(Package(){0xa5a5a5a5,
				Package(){8, 0x0, 0xa5a50000},
				Package(){9, 0x1, 0xa5a50000},
				Package(){10, 0x6, 0xa5a50000},
				Package(){11, 0x2, 0xa5a50000},},
			Local0)
		TRY4(Local0, Refof(re10), Refof(re11), Refof(re12), Refof(re13))


		Store(Package(){0x5a5a5a5a,
				Package(){12, 0x1, 0x5a5a0000},
				Package(){13, 0x0, 0x5a5a0000},
				Package(){14, 0x1, 0x5a5a0000},
				Package(){15, 0x5, 0x5a5a0000},},
			Local0)
		TRY4(Local0, Refof(re10), Refof(re11), Refof(re12), Refof(re13))
	}

	Method(ifdf,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, Preserve) {
			idx1, 8,
			dta1, 8,
		}

		IndexField(idx1, dta1, ByteAcc, NoLock, Preserve) {
			, 7,
			re10, 1,
			re11, 1,
			Offset(2),
			re12, 4,
			re13, 4,
		}

		OUTP("Check IndexField implementation ByteAcc 7,1-1,O2,4-4")

		Store(Package(){0xa5a5a5a5,
				Package(){16, 0x1, 0xa5a5a500},
				Package(){17, 0x1, 0xa5a5a501},
				Package(){18, 0x5, 0xa5a5a502},
				Package(){19, 0xa, 0xa5a5a502},},
			Local0)
		TRY4(Local0, Refof(re10), Refof(re11), Refof(re12), Refof(re13))


		Store(Package(){0x5a5a5a5a,
				Package(){20, 0x0, 0x5a5a5a00},
				Package(){21, 0x0, 0x5a5a5a01},
				Package(){22, 0xa, 0x5a5a5a02},
				Package(){23, 0x5, 0x5a5a5a02},},
			Local0)
		TRY4(Local0, Refof(re10), Refof(re11), Refof(re12), Refof(re13))
	}

	CH03(ts, z179, 0x0ec, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) {
			ifdc()
			ifdd()
			ifde()
			ifdf()
		}
		case (13) { ifdc() }
		case (14) { ifdd() }
		case (15) { ifde() }
		case (16) { ifdf() }
	}
	CH03(ts, z179, 0x0ed, __LINE__, 0)
}

Method(mw27, 1, Serialized)
{
	Name(ts, "mw27")

	OperationRegion(OPR0, SystemMemory, VMEM, 256)

	Field(OPR0, ByteAcc, NoLock, Preserve) {
		tot0, 32,
		tot1, 32,
	}

	Method(ife0,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx0, 16,
			dta0, 16,
		}
		IndexField(idx0, dta0, ByteAcc, NoLock, WriteAsZeros) {
			idf0, 1, , 6, idf1, 1,
			idf2, 1, , 6, idf3, 1,
			idf4, 1, , 6, idf5, 1,
			idf6, 1, , 6, idf7, 1,
		}
		Method(m000, 5)
		{
			Store(arg0, tot0)
			Store(Derefof(arg1), Local0)
			Store(tot0, Local1)

			if (LNotEqual(Local0, arg3)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg3)
			}
			if (LNotEqual(Local1, arg4)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg4)
			}
		}

		OUTP("Check IndexField implementation: ByteAcc2")

		m000(0x0001ffff, Refof(idf0), 0x150, 0x1, 0x00010000)
		m000(0x0080ffff, Refof(idf1), 0x152, 0x1, 0x00800000)
		m000(0x0001ffff, Refof(idf2), 0x154, 0x1, 0x00010001)
		m000(0x0080ffff, Refof(idf3), 0x156, 0x1, 0x00800001)
		m000(0x0001ffff, Refof(idf4), 0x158, 0x1, 0x00010002)
		m000(0x0080ffff, Refof(idf5), 0x15a, 0x1, 0x00800002)
		m000(0x0001ffff, Refof(idf6), 0x15c, 0x1, 0x00010003)
		m000(0x0080ffff, Refof(idf7), 0x15e, 0x1, 0x00800003)
	}

	Method(ife1,, Serialized)
	{
		Field(OPR0, WordAcc, NoLock, WriteAsZeros) {
			idx0, 16,
			dta0, 16,
		}
		IndexField(idx0, dta0, ByteAcc, NoLock, WriteAsZeros) {
			idf0, 1, , 6, idf1, 1,
			idf2, 1, , 6, idf3, 1,
			idf4, 1, , 6, idf5, 1,
			idf6, 1, , 6, idf7, 1,
		}
		Method(m000, 5)
		{
			Store(arg0, tot0)
			Store(Derefof(arg1), Local0)
			Store(tot0, Local1)

			if (LNotEqual(Local0, arg3)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg3)
			}
			if (LNotEqual(Local1, arg4)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg4)
			}
		}

		OUTP("Check IndexField implementation: WordAccByteAcc")

		m000(0x0001ffff, Refof(idf0), 0x160, 0x1, 0x00010000)
		m000(0x0080ffff, Refof(idf1), 0x162, 0x1, 0x00800000)
		m000(0x0001ffff, Refof(idf2), 0x164, 0x1, 0x00010001)
		m000(0x0080ffff, Refof(idf3), 0x166, 0x1, 0x00800001)
		m000(0x0001ffff, Refof(idf4), 0x168, 0x1, 0x00010002)
		m000(0x0080ffff, Refof(idf5), 0x16a, 0x1, 0x00800002)
		m000(0x0001ffff, Refof(idf6), 0x16c, 0x1, 0x00010003)
		m000(0x0080ffff, Refof(idf7), 0x16e, 0x1, 0x00800003)
	}

	Method(ife2,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx0, 16,
			dta0, 16,
		}
		IndexField(idx0, dta0, WordAcc, NoLock, WriteAsZeros) {
			idf0, 1, , 6, idf1, 1,
			idf2, 1, , 6, idf3, 1,
			idf4, 1, , 6, idf5, 1,
			idf6, 1, , 6, idf7, 1,
		}
		Method(m000, 5)
		{
			Store(arg0, tot0)
			Store(Derefof(arg1), Local0)
			Store(tot0, Local1)

			if (LNotEqual(Local0, arg3)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg3)
			}
			if (LNotEqual(Local1, arg4)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg4)
			}
		}

		OUTP("Check IndexField implementation: ByteAccWordAcc")

		m000(0x0001ffff, Refof(idf0), 0x170, 0x1, 0x00010000)
		m000(0x0080ffff, Refof(idf1), 0x172, 0x1, 0x00800000)
		m000(0x0001ffff, Refof(idf2), 0x174, 0x0, 0x00010000)
		m000(0x0080ffff, Refof(idf3), 0x176, 0x0, 0x00800000)
		m000(0x0001ffff, Refof(idf4), 0x178, 0x1, 0x00010002)
		m000(0x0080ffff, Refof(idf5), 0x17a, 0x1, 0x00800002)
		m000(0x0001ffff, Refof(idf6), 0x17c, 0x0, 0x00010002)
		m000(0x0080ffff, Refof(idf7), 0x17e, 0x0, 0x00800002)
	}

	Method(ife3,, Serialized)
	{
		Field(OPR0, WordAcc, NoLock, WriteAsZeros) {
			idx0, 16,
			dta0, 16,
		}
		IndexField(idx0, dta0, WordAcc, NoLock, WriteAsZeros) {
			idf0, 1, , 6, idf1, 1,
			idf2, 1, , 6, idf3, 1,
			idf4, 1, , 6, idf5, 1,
			idf6, 1, , 6, idf7, 1,
		}
		Method(m000, 5)
		{
			Store(arg0, tot0)
			Store(Derefof(arg1), Local0)
			Store(tot0, Local1)

			if (LNotEqual(Local0, arg3)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg3)
			}
			if (LNotEqual(Local1, arg4)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg4)
			}
		}

		OUTP("Check IndexField implementation: WordAcc2")

		m000(0x0001ffff, Refof(idf0), 0x180, 0x1, 0x00010000)
		m000(0x0080ffff, Refof(idf1), 0x182, 0x1, 0x00800000)
		m000(0x0001ffff, Refof(idf2), 0x184, 0x0, 0x00010000)
		m000(0x0080ffff, Refof(idf3), 0x186, 0x0, 0x00800000)
		m000(0x0001ffff, Refof(idf4), 0x188, 0x1, 0x00010002)
		m000(0x0080ffff, Refof(idf5), 0x18a, 0x1, 0x00800002)
		m000(0x0001ffff, Refof(idf6), 0x18c, 0x0, 0x00010002)
		m000(0x0080ffff, Refof(idf7), 0x18e, 0x0, 0x00800002)
	}


	CH03(ts, z179, 0x0ee, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) {
			ife0()
			ife1()
			ife2()
			ife3()
		}
		case (17) { ife0() }
		case (18) { ife1() }
		case (19) { ife2() }
		case (20) { ife3() }
	}
	CH03(ts, z179, 0x0ef, __LINE__, 0)
}

Method(mx27, 1, Serialized)
{
	Name(ts, "mx27")

	OperationRegion(OPR0, SystemMemory, VMEM, 256)

	Field(OPR0, ByteAcc, NoLock, Preserve) {
		tot0, 32,
		tot1, 32,
	}

	Method(ife4,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx0, 16,
			dta0, 4,
		}
		IndexField(idx0, dta0, ByteAcc, NoLock, WriteAsZeros) {
			idf0, 1, , 6, idf1, 1,
			idf2, 1, , 6, idf3, 1,
			idf4, 1, , 6, idf5, 1,
			idf6, 1, , 6, idf7, 1,
		}
		Method(m000, 5)
		{
			Store(arg0, tot0)
			Store(Derefof(arg1), Local0)
			Store(tot0, Local1)

			if (LNotEqual(Local0, arg3)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg3)
			}
			if (LNotEqual(Local1, arg4)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg4)
			}
		}

		OUTP("Check IndexField implementation: ByteAcc2, dta0:4")

		m000(0x0001ffff, Refof(idf0), 0x190, 0x1, 0x00010000)
		m000(0xffffffff, Refof(idf1), 0x192, 0x0, 0xffff0000)
		m000(0x0001ffff, Refof(idf2), 0x194, 0x1, 0x00010001)
		m000(0xffffffff, Refof(idf3), 0x196, 0x0, 0xffff0001)
		m000(0x0001ffff, Refof(idf4), 0x198, 0x1, 0x00010002)
		m000(0xffffffff, Refof(idf5), 0x19a, 0x0, 0xffff0002)
		m000(0x0001ffff, Refof(idf6), 0x19c, 0x1, 0x00010003)
		m000(0xffffffff, Refof(idf7), 0x19e, 0x0, 0xffff0003)
	}

	Method(ife5,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx0, 8,
			dta0, 8,
		}
		IndexField(idx0, dta0, WordAcc, NoLock, WriteAsZeros) {
			idf0, 1, , 6, idf1, 1,
			idf2, 1, , 6, idf3, 1,
			idf4, 1, , 6, idf5, 1,
			idf6, 1, , 6, idf7, 1,
		}
		Method(m000, 5)
		{
			Store(arg0, tot0)
			Store(Derefof(arg1), Local0)
			Store(tot0, Local1)

			if (LNotEqual(Local0, arg3)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg3)
			}
			if (LNotEqual(Local1, arg4)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg4)
			}
		}

		OUTP("Check IndexField implementation: ByteAccWordAcc, idx0, 8, dta0, 8")

		m000(0x000001ff, Refof(idf0), 0x1a0, 0x1, 0x00000100)
		m000(0x000080ff, Refof(idf1), 0x1a2, 0x1, 0x00008000)
		m000(0xffffffff, Refof(idf2), 0x1a4, 0x0, 0xffffff00)
		m000(0xffffffff, Refof(idf3), 0x1a6, 0x0, 0xffffff00)
		m000(0x000001ff, Refof(idf4), 0x1a8, 0x1, 0x00000102)
		m000(0x000080ff, Refof(idf5), 0x1aa, 0x1, 0x00008002)
		m000(0xffffffff, Refof(idf6), 0x1ac, 0x0, 0xffffff02)
		m000(0xffffffff, Refof(idf7), 0x1ae, 0x0, 0xffffff02)
	}

	Method(ife6,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx0, 32,
			dta0, 32,
		}
		IndexField(idx0, dta0, WordAcc, NoLock, WriteAsZeros) {
			idf0, 1, , 6, idf1, 1,
			idf2, 1, , 6, idf3, 1,
			idf4, 1, , 6, idf5, 1,
			idf6, 1, , 6, idf7, 1,
		}
		Method(m000, 6)
		{
			Store(0xffffffff, tot0)
			Store(arg0, tot1)
			Store(Derefof(arg1), Local0)
			Store(tot1, Local1)
			Store(tot0, Local2)

			if (LNotEqual(Local0, arg3)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg3)
			}
			if (LNotEqual(Local1, arg4)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg4)
			}
			if (LNotEqual(Local2, arg5)) {
				err(ts, z179, __LINE__, 0, 0, Local2, arg5)
			}
		}

		OUTP("Check IndexField implementation: ByteAccWordAcc, idx0, 32, dta0, 32")

		m000(0x00000001, Refof(idf0), 0x1b0, 0x1, 0x00000001, 0)
		m000(0x00000080, Refof(idf1), 0x1b3, 0x1, 0x00000080, 0)
		m000(0x00000100, Refof(idf2), 0x1b6, 0x1, 0x00000100, 0)
		m000(0x00008000, Refof(idf3), 0x1b9, 0x1, 0x00008000, 0)
		m000(0x00000001, Refof(idf4), 0x1bc, 0x1, 0x00000001, 2)
		m000(0x00000080, Refof(idf5), 0x1bf, 0x1, 0x00000080, 2)
		m000(0x00000100, Refof(idf6), 0x1c2, 0x1, 0x00000100, 2)
		m000(0x00008000, Refof(idf7), 0x1c5, 0x1, 0x00008000, 2)
	}

	Method(ife7,, Serialized)
	{
		Field(OPR0, DWordAcc, NoLock, WriteAsZeros) {
			idx0, 32,
			dta0, 32,
		}
		IndexField(idx0, dta0, WordAcc, NoLock, WriteAsZeros) {
			idf0, 1, , 6, idf1, 1,
			idf2, 1, , 6, idf3, 1,
			idf4, 1, , 6, idf5, 1,
			idf6, 1, , 6, idf7, 1,
		}
		Method(m000, 6)
		{
			Store(0xffffffff, tot0)
			Store(arg0, tot1)
			Store(Derefof(arg1), Local0)
			Store(tot1, Local1)
			Store(tot0, Local2)

			if (LNotEqual(Local0, arg3)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg3)
			}
			if (LNotEqual(Local1, arg4)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg4)
			}
			if (LNotEqual(Local2, arg5)) {
				err(ts, z179, __LINE__, 0, 0, Local2, arg5)
			}
		}

		OUTP("Check IndexField implementation: DWordAccWordAcc, idx0, 32, dta0, 32")

		m000(0x00000001, Refof(idf0), 0x1f0, 0x1, 0x00000001, 0)
		m000(0x00000080, Refof(idf1), 0x1f3, 0x1, 0x00000080, 0)
		m000(0x00000100, Refof(idf2), 0x1f6, 0x1, 0x00000100, 0)
		m000(0x00008000, Refof(idf3), 0x1f9, 0x1, 0x00008000, 0)
		m000(0x00000001, Refof(idf4), 0x1fc, 0x1, 0x00000001, 2)
		m000(0x00000080, Refof(idf5), 0x1ff, 0x1, 0x00000080, 2)
		m000(0x00000100, Refof(idf6), 0x202, 0x1, 0x00000100, 2)
		m000(0x00008000, Refof(idf7), 0x215, 0x1, 0x00008000, 2)
	}

	CH03(ts, z179, 0x1c8, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) {
			ife4()
			ife5()
			ife6()
			ife7()
		}
		case (21) { ife4() }
		case (22) { ife5() }
		case (23) { ife6() }
		case (24) { ife7() }
	}
	CH03(ts, z179, 0x1c9, __LINE__, 0)
}

Method(my27, 1, Serialized)
{
	Name(ts, "my27")

	OperationRegion(OPR0, SystemMemory, VMEM, 256)

	Field(OPR0, ByteAcc, NoLock, Preserve) {
		tot0, 32,
		tot1, 32,
	}

	Method(ife8,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx0, 32,
			dta0, 32,
		}
		IndexField(idx0, dta0, DWordAcc, NoLock, WriteAsZeros) {
			idf0, 1, , 14, idf1, 1,
			idf2, 1, , 14, idf3, 1,
			idf4, 1, , 14, idf5, 1,
			idf6, 1, , 14, idf7, 1,
		}
		Method(m000, 6)
		{
			Store(0xffffffff, tot0)
			Store(arg0, tot1)
			Store(Derefof(arg1), Local0)
			Store(tot1, Local1)
			Store(tot0, Local2)

			if (LNotEqual(Local0, arg3)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg3)
			}
			if (LNotEqual(Local1, arg4)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg4)
			}
			if (LNotEqual(Local2, arg5)) {
				err(ts, z179, __LINE__, 0, 0, Local2, arg5)
			}
		}

		OUTP("Check IndexField implementation: ByteAccDWordAcc, idx0, 32, dta0, 32")

		m000(0x00000001, Refof(idf0), 0x200, 0x1, 0x00000001, 0)
		m000(0x00008000, Refof(idf1), 0x203, 0x1, 0x00008000, 0)
		m000(0x00010000, Refof(idf2), 0x206, 0x1, 0x00010000, 0)
		m000(0x80000000, Refof(idf3), 0x209, 0x1, 0x80000000, 0)
		m000(0x00000001, Refof(idf4), 0x20c, 0x1, 0x00000001, 4)
		m000(0x00008000, Refof(idf5), 0x20f, 0x1, 0x00008000, 4)
		m000(0x00010000, Refof(idf6), 0x212, 0x1, 0x00010000, 4)
		m000(0x80000000, Refof(idf7), 0x215, 0x1, 0x80000000, 4)
	}

	Method(ife9,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx0, 32,
			dta0, 32,
		}
		IndexField(idx0, dta0, QWordAcc, NoLock, WriteAsZeros) {
			idf0, 1, , 14, idf1, 1,
			idf2, 1, , 14, idf3, 1,
			idf4, 1, , 14, idf5, 1,
			idf6, 1, , 14, idf7, 1,
		}
		Method(m000, 6)
		{
			Store(0xffffffff, tot0)
			Store(arg0, tot1)
			Store(Derefof(arg1), Local0)
			Store(tot1, Local1)
			Store(tot0, Local2)

			if (LNotEqual(Local0, arg3)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg3)
			}
			if (LNotEqual(Local1, arg4)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg4)
			}
			if (LNotEqual(Local2, arg5)) {
				err(ts, z179, __LINE__, 0, 0, Local2, arg5)
			}
		}

		OUTP("Check IndexField implementation: ByteAccQWordAcc, idx0, 32, dta0, 32")

		m000(0x00000001, Refof(idf0), 0x220, 0x1, 0x00000001, 0)
		m000(0x00008000, Refof(idf1), 0x223, 0x1, 0x00008000, 0)
		m000(0x00010000, Refof(idf2), 0x226, 0x1, 0x00010000, 0)
		m000(0x80000000, Refof(idf3), 0x229, 0x1, 0x80000000, 0)
		m000(0xffffffff, Refof(idf4), 0x22c, 0x0, 0xffffffff, 0)
		m000(0xffffffff, Refof(idf5), 0x22f, 0x0, 0xffffffff, 0)
		m000(0xffffffff, Refof(idf6), 0x232, 0x0, 0xffffffff, 0)
		m000(0xffffffff, Refof(idf7), 0x235, 0x0, 0xffffffff, 0)
	}

	Method(ifea,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx0, 16,
			dta0, 16,
		}
		IndexField(idx0, dta0, ByteAcc, NoLock, WriteAsZeros) {
			idf0, 1, , 6, idf1, 1,
			idf2, 1, , 6, idf3, 1,
			idf4, 1, , 6, idf5, 1,
			idf6, 1, , 6, idf7, 1,
		}
		Method(m000, 4, Serialized)
		{
			Store(arg0, tot0)
			switch (ToInteger (Arg1)) {
			case (0) {Store(1, idf0)}
			case (1) {Store(1, idf1)}
			case (2) {Store(1, idf2)}
			case (3) {Store(1, idf3)}
			case (4) {Store(1, idf4)}
			case (5) {Store(1, idf5)}
			case (6) {Store(1, idf6)}
			case (7) {Store(1, idf7)}
			}
			Store(tot0, Local0)

			if (LNotEqual(Local0, arg3)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg3)
			}
		}

		OUTP("Check IndexField implementation: ByteAcc2, Store")

		m000(0xffffffff, 0, 0x240, 0x00010000)
		m000(0xffffffff, 1, 0x241, 0x00800000)
		m000(0xffffffff, 2, 0x242, 0x00010001)
		m000(0xffffffff, 3, 0x243, 0x00800001)
		m000(0xffffffff, 4, 0x244, 0x00010002)
		m000(0xffffffff, 5, 0x245, 0x00800002)
		m000(0xffffffff, 6, 0x246, 0x00010003)
		m000(0xffffffff, 7, 0x247, 0x00800003)
	}

	Method(ifeb,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx0, 16,
			dta0, 16,
		}
		IndexField(idx0, dta0, WordAcc, NoLock, WriteAsZeros) {
			idf0, 1, , 6, idf1, 1,
			idf2, 1, , 6, idf3, 1,
			idf4, 1, , 6, idf5, 1,
			idf6, 1, , 6, idf7, 1,
		}
		Method(m000, 4, Serialized)
		{
			Store(arg0, tot0)
			switch (ToInteger (Arg1)) {
			case (0) {Store(1, idf0)}
			case (1) {Store(1, idf1)}
			case (2) {Store(1, idf2)}
			case (3) {Store(1, idf3)}
			case (4) {Store(1, idf4)}
			case (5) {Store(1, idf5)}
			case (6) {Store(1, idf6)}
			case (7) {Store(1, idf7)}
			}
			Store(tot0, Local0)

			if (LNotEqual(Local0, arg3)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg3)
			}
		}

		OUTP("Check IndexField implementation: ByteAccWordAcc, Store")

		m000(0xffffffff, 0, 0x248, 0x00010000)
		m000(0xffffffff, 1, 0x249, 0x00800000)
		m000(0xffffffff, 2, 0x24a, 0x01000000)
		m000(0xffffffff, 3, 0x24b, 0x80000000)
		m000(0xffffffff, 4, 0x24c, 0x00010002)
		m000(0xffffffff, 5, 0x24d, 0x00800002)
		m000(0xffffffff, 6, 0x24e, 0x01000002)
		m000(0xffffffff, 7, 0x24f, 0x80000002)
	}

	CH03(ts, z179, 0x1ca, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) {
			ife8()

			if (ABUU) {
			} else {
				ife9()
			}

			if (ABUU) {
			} else {
				ifea()
			}

			if (ABUU) {
			} else {
				ifeb()
			}
		}
		case (25) { ife8() }
		case (26) { ife9() }
		case (27) { ifea() }
		case (28) { ifeb() }
	}
	CH03(ts, z179, 0x1cb, __LINE__, 0)
}

Method(mz27, 1, Serialized)
{
	Name(ts, "mz27")

	OperationRegion(OPR0, SystemMemory, VMEM, 256)

	Field(OPR0, ByteAcc, NoLock, Preserve) {
		tot0, 32,
		tot1, 32,
	}

	Method(ifec,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx0, 32,
			dta0, 32,
		}
		IndexField(idx0, dta0, DWordAcc, NoLock, WriteAsZeros) {
			idf0, 1, , 14, idf1, 1,
			idf2, 1, , 14, idf3, 1,
			idf4, 1, , 14, idf5, 1,
			idf6, 1, , 14, idf7, 1,
		}
		Method(m000, 5, Serialized)
		{
			Store(0xffffffff, tot0)
			Store(arg0, tot1)
			switch (ToInteger (Arg1)) {
			case (0) {Store(1, idf0)}
			case (1) {Store(1, idf1)}
			case (2) {Store(1, idf2)}
			case (3) {Store(1, idf3)}
			case (4) {Store(1, idf4)}
			case (5) {Store(1, idf5)}
			case (6) {Store(1, idf6)}
			case (7) {Store(1, idf7)}
			}
			Store(tot1, Local0)
			Store(tot0, Local1)

			if (LNotEqual(Local0, arg3)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg3)
			}
			if (LNotEqual(Local1, arg4)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg4)
			}
		}

		OUTP("Check IndexField implementation: ByteAccDWordAcc, Store")

		m000(0xffffffff, 0, 0x250, 0x00000001, 0)
		m000(0xffffffff, 1, 0x252, 0x00008000, 0)
		m000(0xffffffff, 2, 0x254, 0x00010000, 0)
		m000(0xffffffff, 3, 0x256, 0x80000000, 0)
		m000(0xffffffff, 4, 0x258, 0x00000001, 4)
		m000(0xffffffff, 5, 0x25a, 0x00008000, 4)
		m000(0xffffffff, 6, 0x25c, 0x00010000, 4)
		m000(0xffffffff, 7, 0x25e, 0x80000000, 4)
	}

	Method(ifed,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx0, 8,
			dta0, 24,
		}
		IndexField(idx0, dta0, ByteAcc, NoLock, WriteAsZeros) {
			, 15,
			idf0, 1
		}

		OUTP("Check IndexField implementation: dta wider than idf Access width")

		Store(0x3FF, idf0)

		Store(tot0, Local0)
		if (LNotEqual(Local0, 0x8001)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0x8001)
		}
	}

	Method(ifee,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx0, 8,
			dta0, 24,
		}
		IndexField(idx0, dta0, ByteAcc, NoLock, WriteAsZeros) {
			, 7,
			idf0, 1
		}

		OUTP("Check IndexField implementation: dta wider than idf Access width 2")

		Store(0xFF, idf0)

		Store(tot0, Local0)
		if (LNotEqual(Local0, 0x8000)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0x8000)
		}
	}

	Method(ifef,, Serialized)
	{
		Field(OPR0, ByteAcc, NoLock, WriteAsZeros) {
			idx1, 8,
			dta1, 8,
		}

		IndexField(idx1, dta1, ByteAcc, NoLock, WriteAsZeros) {
			, 2,
			re10, 6,
			, 3,
			re11, 5,
			, 4,
			re12, 4,
			, 5,
			re13, 3,
		}

		Method(TRY0, 3, Serialized)
		{
			Store(Zero, tot0)
			switch (ToInteger (Arg0)) {
			Case (0) {Store(Ones, ^re10)}
			Case (1) {Store(Ones, ^re11)}
			Case (2) {Store(Ones, ^re12)}
			Case (3) {Store(Ones, ^re13)}
			}

			Store(idx1, Local0)
			Store(dta1, Local1)

			Multiply(arg0, 2, Local2)
			if (LNotEqual(Local0, arg1)) {
				err(ts, z179, __LINE__, 0, 0, Local0, arg1)
			}
			if (LNotEqual(Local1, arg2)) {
				err(ts, z179, __LINE__, 0, 0, Local1, arg2)
			}
		}

		OUTP("Check IndexField ByteAcc Ones write (:2)6-(:3)5-(:4)4-(:5)3")

		TRY0(0, 0, 0xfc)
		TRY0(1, 1, 0xf8)
		TRY0(2, 2, 0xf0)
		TRY0(3, 3, 0xe0)
	}

	CH03(ts, z179, 0x1cc, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) {
			ifec()
			ifed()
			ifee()
			ifef()
		}
		case (29) { ifec() }
		case (30) { ifed() }
		case (31) { ifee() }
		case (32) { ifef() }
	}
	CH03(ts, z179, 0x1cd, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(aifd) { IIN0() ms27(1) Return(POUT) }
Method(bifd) { IIN0() ms27(2) Return(POUT) }
Method(cifd) { IIN0() ms27(3) Return(POUT) }
Method(difd) { IIN0() ms27(4) Return(POUT) }
Method(sifd) { IIN0() ms27(0) Return(POUT) }
Method(eifd) { IIN0() mt27(5) Return(POUT) }
Method(fifd) { IIN0() mt27(6) Return(POUT) }
Method(gifd) { IIN0() mt27(7) Return(POUT) }
Method(hifd) { IIN0() mt27(8) Return(POUT) }
Method(tifd) { IIN0() mt27(0) Return(POUT) }
Method(iifd) { IIN0() mu27(9) Return(POUT) }
Method(jifd) { IIN0() mu27(10) Return(POUT) }
Method(kifd) { IIN0() mu27(11) Return(POUT) }
Method(lifd) { IIN0() mu27(12) Return(POUT) }
Method(uifd) { IIN0() mu27(0) Return(POUT) }
Method(mifd) { IIN0() mv27(13) Return(POUT) }
Method(nifd) { IIN0() mv27(14) Return(POUT) }
Method(oifd) { IIN0() mv27(15) Return(POUT) }
Method(pifd) { IIN0() mv27(16) Return(POUT) }
Method(vifd) { IIN0() mv27(0) Return(POUT) }
Method(aife) { IIN0() mw27(17) Return(POUT) }
Method(bife) { IIN0() mw27(18) Return(POUT) }
Method(cife) { IIN0() mw27(19) Return(POUT) }
Method(dife) { IIN0() mw27(20) Return(POUT) }
Method(wife) { IIN0() mw27(0) Return(POUT) }
Method(eife) { IIN0() mx27(21) Return(POUT) }
Method(fife) { IIN0() mx27(22) Return(POUT) }
Method(gife) { IIN0() mx27(23) Return(POUT) }
Method(hife) { IIN0() mx27(24) Return(POUT) }
Method(xife) { IIN0() mx27(0) Return(POUT) }
Method(iife) { IIN0() my27(25) Return(POUT) }
Method(jife) { IIN0() my27(26) Return(POUT) }
Method(kife) { IIN0() my27(27) Return(POUT) }
Method(life) { IIN0() my27(28) Return(POUT) }
Method(yife) { IIN0() my27(0) Return(POUT) }
Method(mife) { IIN0() mz27(29) Return(POUT) }
Method(nife) { IIN0() mz27(30) Return(POUT) }
Method(oife) { IIN0() mz27(31) Return(POUT) }
Method(pife) { IIN0() mz27(32) Return(POUT) }
Method(zife) { IIN0() mz27(0) Return(POUT) }

/*
 * Hot issue:
 *
 * Check BankField implementation
 */
Method(ms28,, Serialized)
{
	Name(ts, "ms28")

	OperationRegion(OPR0, SystemMemory, 0, 256)

	Field(OPR0, ByteAcc, NoLock, Preserve) {
		tot0, 32,
		tot1, 32,
	}

	Method(bfd0,, Serialized)
	{
		Field (OPR0, ByteAcc, NoLock, Preserve) {
			bnk0, 8
		}
		Field (OPR0, ByteAcc, NoLock, Preserve) {
			tot0, 80
		}

		BankField (OPR0, bnk0, 0, ByteAcc, NoLock, Preserve) {
			Offset(8),
			bf00, 8,
		}

		BankField (OPR0, bnk0, 1, ByteAcc, NoLock, Preserve) {
			Offset(9),
			bf01, 8,
		}

		OUTP("Check BankField implementation")

		// Deal with 0-th bank layout:

		Store(0, bnk0)
		if (LNotEqual(bnk0, 0)) {
			err(ts, z179, __LINE__, 0, 0, bnk0, 0)
		}

		Store(0x87, bf00)
		if (LNotEqual(bnk0, 0)) {
			err(ts, z179, __LINE__, 0, 0, bnk0, 0)
		}

		if (LNotEqual(bf00, 0x87)) {
			err(ts, z179, __LINE__, 0, 0, bf00, 0x87)
		}

		// Deal with 1-th bank layout:

		Store(1, bnk0)
		if (LNotEqual(bnk0, 1)) {
			err(ts, z179, __LINE__, 0, 0, bnk0, 1)
		}

		Store(0x96, bf01)

		if (LNotEqual(bnk0, 1)) {
			err(ts, z179, __LINE__, 0, 0, bnk0, 1)
		}

		if (LNotEqual(bf01, 0x96)) {
			err(ts, z179, __LINE__, 0, 0, bf01, 0x96)
		}
	}

	CH03(ts, z179, 0x276, __LINE__, 0)
	bfd0()
	CH03(ts, z179, 0x277, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(abfd) { IIN0() ms28() Return(POUT) }

Mutex (C152, 0)
Mutex (C153, 0)
Mutex (C154, 0)
Mutex (C155, 0)
Mutex (C156, 0)
Mutex (C159, 0)

/*
 * Hot issue:
 *
 * Check Acquire/Release
 */
Method(ms29, 1, Serialized)
{
	Name(ts, "ms29")

	Method (C157, 1, NotSerialized)
	{
		if (arg0) {
			Store(Acquire (C154, 0xFFFF), Local0)
		} else {
			Store(Acquire (C154, 0), Local0)
		}
		Return (Local0)
	}

	Method (C158, 0, NotSerialized)
	{
		Release (C154)
	}

	Method (C160, 0, NotSerialized)
	{
		Release (C152)
	}

	Method(mut0)
	{
		OUTP("Check Release by different ASL Methods")
		C160()
		CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
	}

	Method(mut1)
	{
		OUTP("Check Acquire/Release by different ASL Methods")

		OUTP("Acquire")
		Store(C157(1), Local0)

		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}

		OUTP("Release")
		C158()
	}

	Method(mut2)
	{
		OUTP("Check Acquire/Acquire by the different Method's calls")

		OUTP("Acquire 1")
		Store(C157(1), Local0)

		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}

		OUTP("Acquire 2")
		Store(C157(1), Local0)

		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}
	}

	Method(mut3)
	{
		OUTP("Check Acquire/Acquire in one Method")

		OUTP("Acquire 1")
        Store(Acquire (C155, 0xFFFF), Local0)

		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}

		OUTP("Acquire 2")
        Store(Acquire (C155, 0xFFFF), Local0)


		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}
	}

	Method(mut4)
	{
		OUTP("Check Acquire/Release/Release by different ASL Methods")

		OUTP("Acquire")
		Store(C157(1), Local0)

		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}

		OUTP("Release 1")
		C158()

		OUTP("Release 2")
		C158()

		CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
	}

	Method(mut5)
	{
		OUTP("Check Acquire(,0xFFFF)/Acquire(,0) in one Method")

		OUTP("Acquire( , 0xFFFF) 1")
        Store(Acquire (C156, 0xFFFF), Local0)

		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}

		OUTP("Acquire( , 0) 2")
        Store(Acquire (C156, 0), Local0)

		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}
	}

	Method(mut6)
	{
		OUTP("Check Acquire2/Release2 in one Method")

		OUTP("Acquire 1")
        Store(Acquire (C153, 0xFFFF), Local0)

		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}

		OUTP("Acquire 2")
        Store(Acquire (C153, 0xFFFF), Local0)


		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}

		OUTP("Release 1")
		Release (C153)

		OUTP("Release 2")
		Release (C153)
	}

	Method(mut7)
	{
		OUTP("Check Acquire2/Release3 in one Method")

		OUTP("Acquire 1")
        Store(Acquire (C159, 0xFFFF), Local0)

		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}

		OUTP("Acquire 2")
        Store(Acquire (C159, 0xFFFF), Local0)


		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}

		OUTP("Release 1")
		Release (C159)

		OUTP("Release 2")
		Release (C159)

		OUTP("Release 3")
		Release (C159)
		CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
	}

	Method(mut8)
	{
		OUTP("Check Acquire2/Release2 in one Method")

		OUTP("Acquire 1")
        Store(Acquire (C153, 0xFFFF), Local0)

		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}

		OUTP("Acquire 2")
        Store(Acquire (C153, 0xFFFF), Local0)


		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}

		OUTP("Release 1")
		Release (C153)

		OUTP("Release 2")
		Release (C153)
	}

	Method(mut9,, Serialized)
	{
		Mutex (C159, 0)

		OUTP("Check Acquire2/Release2 in one Method for dynamic Mutex")

		OUTP("Acquire 1")
        Store(Acquire (C159, 0xFFFF), Local0)

		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}

		OUTP("Acquire 2")
        Store(Acquire (C159, 0xFFFF), Local0)


		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}

		OUTP("Release 1")
		Release (C159)

		OUTP("Release 2")
		Release (C159)

		OUTP("Release 3")
		Release (C159)
		CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
	}

	Method(m000)
	{
		if (ABUU) {
		} else {
			mut0()
		}

		mut1()

		if (ABUU) {
		} else {
			mut3()
		}

		if (ABUU) {
		} else {
			mut4()
		}

		mut5()
		mut6()

		if (ABUU) {
		} else {
			mut7()
		}

		mut8()

		if (ABUU) {
		} else {
			mut9()
		}
	}

	CH03(ts, z179, 0x292, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { mut0() }
		case (2) { mut1() }
		case (3) { mut2() }
		case (4) { mut3() }
		case (5) { mut4() }
		case (6) { mut5() }
		case (7) { mut6() }
		case (8) { mut7() }
		case (9) { mut8() }
		case (10) { mut9() }
	}
	CH03(ts, z179, 0x293, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(amut) { IIN0() ms29(1) Return(POUT) }
Method(bmut) { IIN0() ms29(2) Return(POUT) }
Method(cmut) { IIN0() ms29(3) Return(POUT) }
Method(dmut) { IIN0() ms29(4) Return(POUT) }
Method(emut) { IIN0() ms29(5) Return(POUT) }
Method(fmut) { IIN0() ms29(6) Return(POUT) }
Method(gmut) { IIN0() ms29(7) Return(POUT) }
Method(hmut) { IIN0() ms29(8) Return(POUT) }
Method(imut) { IIN0() ms29(9) Return(POUT) }
Method(jmut) { IIN0() ms29(10) Return(POUT) }
Method(kmut) { IIN0() ms29(0) Return(POUT) }

// LEqual implementation for Buffers to use on MS
Method(BCMP, 2)
{
	if (ABUU) {
		Store(Sizeof(Arg0), Local0)

		if (LNotEqual(Local0, Sizeof(Arg1))) {
			return (0)
		}

		Store(Sizeof(Arg0), Local0)

		while(Local0) {
			Decrement(Local0)
			Store(Derefof(Index(Arg0, Local0)), Local1)
			Store(Derefof(Index(Arg1, Local0)), Local2)
			if (LNotEqual(Local1, Local2)) {
				return (0)
			}
		}
		return (1)
	} else {
		return (LEqual(arg0, arg1))
	}
}

/*
 * Hot issue:
 *
 * Check ToBuffer optional store (Bug 194)
 */
Method(ms2a, 1, Serialized)
{
	Name(ts, "ms2a")
	Name(F64, 0)

	Method(tob0)
	{

		Method(m000, 1, Serialized)
		{
			Name(b000, Buffer(1){0x3c})
			Name(b001, Buffer(3){0x01, 0x02, 0x03})

			if (arg0) {
				OUTP("ToBuffer(b001, b000)")
				ToBuffer(b001, b000)
			} else {
				OUTP("ToBuffer(b000, b001)")
				ToBuffer(b000, b001)
			}

			if (LNot(BCMP(b000, b001))) {
				err(ts, z179, __LINE__, 0, 0, b000, b001)
			}
		}

		OUTP("Check ToBuffer optional store behaves like CopyObject")

		m000(0)
		m000(1)
	}

	Method(tob1)
	{
		OUTP("Check ToBuffer(0x456789ab)")
		Store(ToBuffer(0x456789ab), Local0)
		if (F64) {
			Store(Buffer(8){0xab, 0x89, 0x67, 0x45}, Local1)
		} else {
			Store(Buffer(4){0xab, 0x89, 0x67, 0x45}, Local1)
		}
		if (LNot(BCMP(Local1, Local0))) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}
	}

	Method(tob2)
	{
		OUTP("Check ToBuffer(\"456789ab\")")
		Store(ToBuffer("456789ab"), Local0)
		Store(Buffer(){"456789ab"}, Local1)
		if (LNot(BCMP(Local1, Local0))) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}
	}

	Method(tob3)
	{
		OUTP("Check ToBuffer(Buffer(4){0x45, 0x67, 0x89, 0xab})")
		Store(ToBuffer(Buffer(4){0x45, 0x67, 0x89, 0xab}), Local0)
		Store(Buffer(4){0x45, 0x67, 0x89, 0xab}, Local1)
		if (LNot(BCMP(Local1, Local0))) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}
	}

	Method(tob4)
	{
		OUTP("Check ToBuffer(0x456789ab, Local0)")
		ToBuffer(0x456789ab, Local0)
		if (F64) {
			Store(Buffer(8){0xab, 0x89, 0x67, 0x45}, Local1)
		} else {
			Store(Buffer(4){0xab, 0x89, 0x67, 0x45}, Local1)
		}
		if (LNot(BCMP(Local1, Local0))) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}
	}

	Method(tob5)
	{
		OUTP("Check ToBuffer(\"456789ab\", Local0)")
		ToBuffer("456789ab", Local0)
		Store(Buffer(){"456789ab"}, Local1)
		if (LNot(BCMP(Local1, Local0))) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}
	}

	Method(tob6)
	{
		OUTP("Check ToBuffer(Buffer(4){0x45, 0x67, 0x89, 0xab}, Local0)")
		ToBuffer(Buffer(4){0x45, 0x67, 0x89, 0xab}, Local0)
		Store(Buffer(4){0x45, 0x67, 0x89, 0xab}, Local1)
		if (LNot(BCMP(Local1, Local0))) {
			err(ts, z179, __LINE__, 0, 0, Local0, Local1)
		}
	}

	Method(tob7,, Serialized)
	{
		Name(i000, 0)

		OUTP("Check ToBuffer(0x456789ab, i000)")
		ToBuffer(0x456789ab, i000)
		if (F64) {
			Store(Buffer(8){0xab, 0x89, 0x67, 0x45}, Local1)
		} else {
			Store(Buffer(4){0xab, 0x89, 0x67, 0x45}, Local1)
		}
		Store(ObjectType(i000), Local2)
		if (LNotEqual(Local2, 3)) {
			err(ts, z179, __LINE__, 0, 0, Local2, 3)
		} elseif (LNot(BCMP(Local1, i000))) {
			err(ts, z179, __LINE__, 0, 0, i000, Local1)
		}
	}

	Method(tob8,, Serialized)
	{
		Name(s000, "s000")

		OUTP("Check ToBuffer(\"456789ab\", s000)")
		ToBuffer("456789ab", s000)
		Store(Buffer(){"456789ab"}, Local1)
		Store(ObjectType(s000), Local2)
		if (LNotEqual(Local2, 3)) {
			err(ts, z179, __LINE__, 0, 0, Local2, 3)
		} elseif (LNot(BCMP(Local1, s000))) {
			err(ts, z179, __LINE__, 0, 0, s000, Local1)
		}
	}

	Method(tob9,, Serialized)
	{
		Name(b000, Buffer(2){})

		OUTP("Check ToBuffer(Buffer(4){0x45, 0x67, 0x89, 0xab}, b000)")
		ToBuffer(Buffer(4){0x45, 0x67, 0x89, 0xab}, b000)
		Store(Buffer(4){0x45, 0x67, 0x89, 0xab}, Local1)
		Store(ObjectType(b000), Local2)
		if (LNotEqual(Local2, 3)) {
			err(ts, z179, __LINE__, 0, 0, Local2, 3)
		} elseif (LNot(BCMP(Local1, b000))) {
			err(ts, z179, __LINE__, 0, 0, b000, Local1)
		}
	}

	Method(toba)
	{

		Method(m000, 1, Serialized)
		{
			Name(b000, Buffer(1){0x3c})
			Name(b001, Buffer(3){0x01, 0x02, 0x03})

			if (arg0) {
				OUTP("Store(b001, b000)")
				Store(b001, b000)

				Store(Buffer(1){0x01}, Local0)
				if (LNot(BCMP(b000, Local0))) {
					err(ts, z179, __LINE__, 0, 0, b000, Local0)
				}
			} else {
				OUTP("Store(b000, b001)")
				Store(b000, b001)

				Store(Buffer(3){0x3c}, Local0)
				if (LNot(BCMP(b001, Local0))) {
					err(ts, z179, __LINE__, 0, 0, b001, Local0)
				}
			}
		}

		OUTP("Check if Store fails the same way as ToBuffer optional store")

		m000(0)
		m000(1)
	}

	Method(m000)
	{
		if (ABUU) {
		} else {
			tob0()
			tob1()
			tob2()
			tob3()
			tob4()
			tob5()
			tob6()
			tob7()
			tob8()
			tob9()
		}

		toba()
	}

	if (ABUU) {
	} elseif (LEqual(SizeOf(F64), 8)) {
		Store (1, F64)
	}

	CH03(ts, z179, 0x2a4, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { tob0() }
		case (2) { tob1() }
		case (3) { tob2() }
		case (4) { tob3() }
		case (5) { tob4() }
		case (6) { tob5() }
		case (7) { tob6() }
		case (8) { tob7() }
		case (9) { tob8() }
		case (10) { tob9() }
		case (11) { toba() }
	}
	CH03(ts, z179, 0x2a5, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(atob) { IIN0() ms2a(1) Return(POUT) }
Method(btob) { IIN0() ms2a(2) Return(POUT) }
Method(ctob) { IIN0() ms2a(3) Return(POUT) }
Method(dtob) { IIN0() ms2a(4) Return(POUT) }
Method(etob) { IIN0() ms2a(5) Return(POUT) }
Method(ftob) { IIN0() ms2a(6) Return(POUT) }
Method(gtob) { IIN0() ms2a(7) Return(POUT) }
Method(htob) { IIN0() ms2a(8) Return(POUT) }
Method(itob) { IIN0() ms2a(9) Return(POUT) }
Method(jtob) { IIN0() ms2a(10) Return(POUT) }
Method(ktob) { IIN0() ms2a(11) Return(POUT) }

/*
 * Hot issue:
 *
 * Check Package size calculation
 */
Method(ms2b, 1, Serialized)
{
	Name(ts, "ms2b")

	Method(pac0,, Serialized)
	{
		Name(p000, Package(5){1, 2, 3})

		OUTP("Check if Package list < explicit size the last is in use")

		Store(SizeOf(p000), Local0)
		if (LNotEqual(Local0, 5)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 5)
		}
	}

	Method(pac1,, Serialized)
	{
		Name(p000, Package(5){1, 2, 3})

		OUTP("Check if Package list < explicit size there are undef elements")

		Store(ObjectType(Index(p000, 2)), Local0)
		if (Local0) {
		} else {
			err(ts, z179, __LINE__, 0, 0, Local0, 1)
		}

		Store(ObjectType(Index(p000, 3)), Local0)
		if (Local0) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}
	}

	// This test actually should be used with Package(3){1, 2, 3, 4, 5})
	// declaration, but iASL reports "Initializer list too long" error.
	// Uncomment, set 'fopt' below to 1 and use it with -f iASL option
	Method(pac2,, Serialized)
	{
		Name(fopt, 0)
//		Name(p000, Package(3){1, 2, 3, 4, 5})
		Name(p000, Package(3){1, 2, 3})

		OUTP("Check if Package list > explicit size the former is in use")

		if (fopt) {
			Store(SizeOf(p000), Local0)
		} else {
			Store(5, Local0)
		}
		if (LNotEqual(Local0, 5)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 5)
		}
	}

	CH03(ts, z179, 0x2ab, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { pac0() pac1() pac2() }
		case (1) { pac0() }
		case (2) { pac1() }
		case (3) { pac2() }
	}
	CH03(ts, z179, 0x2ac, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(apac) { IIN0() ms2b(1) Return(POUT) }
Method(bpac) { IIN0() ms2b(2) Return(POUT) }
Method(cpac) { IIN0() ms2b(3) Return(POUT) }

/*
 * Hot issue:
 *
 * Check Switch implementation
 *
 * isw0 test should expectedly fail
 */
Method(ms2c, 1, Serialized)
{
	Name(ts, "ms2c")

	Method(sw00, 0, Serialized)
	{
		Method(m000, 1, Serialized)
		{
			Store(0, Local1)

			switch (ToInteger (Arg0)) {
				case (1) { Store(1, Local1) }
				case (2) { Store(2, Local1) }
			}

			return (Local1)
		}

		OUTP("Check Switch implementation 0: standalone")

		Store(2, Local0)
		Store(0, Local1)

		switch (ToInteger (Local0)) {
			case (1) { Store(1, Local1) }
			case (2) { Store(2, Local1) }
		}

		if (LNotEqual(Local1, 2)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 2)
		}

		Store(m000(1), Local1)

		if (LNotEqual(Local1, 1)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 1)
		}
	}

	Method(sw01)
	{
		OUTP("Check While implementation 1: standalone")

		Store(2, Local0)
		Store(0, Local1)

		while (Local0) {
			if (LEqual(Local0, 1)) {
				Increment(Local1)
			} else {
				Increment(Local1)
			}
			Decrement(Local0)
		}
		if (LNotEqual(Local1, 2)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 2)
		}
	}

	Method(sw02, 0, Serialized)
	{
		OUTP("Check Switch implementation 2: inside While (1 step)")

		Store(1, Local0)
		Store(0, Local1)
		Store(0, Local2)

		while (Local0) {
			switch (ToInteger (Local0)) {
				case (1) { Increment(Local1) }
				case (2) { Increment(Local2) }
			}
			Decrement(Local0)
		}
		if (LNotEqual(Local1, 1)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 1)
		}
		if (LNotEqual(Local2, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local2, 0)
		}
	}

	Method(sw03, 0, Serialized)
	{
		OUTP("Check Switch implementation 3: inside While (2 steps)")

		Store(2, Local0)
		Store(0, Local1)
		Store(0, Local2)

		while (Local0) {
			switch (ToInteger (Local0)) {
				case (1) { Increment(Local1) }
				case (2) { Increment(Local2) }
			}
			Decrement(Local0)
		}
		if (LNotEqual(Local1, 1)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 1)
		}
		if (LNotEqual(Local2, 1)) {
			err(ts, z179, __LINE__, 0, 0, Local2, 1)
		}
	}

	Method(sw04, 0, Serialized)
	{
		OUTP("Check Switch implementation 4: inside While 2, 2 Breaks")

		Store(2, Local0)
		Store(0, Local1)
		Store(0, Local2)

		while (Local0) {
			switch (ToInteger (Local0)) {
				case (1) {
				 Increment(Local1)
				 Break
				}
				case (2) {
				 Increment(Local2)
				 Break
				}
			}
			Decrement(Local0)
		}
		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}
		if (LNotEqual(Local1, 1)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 1)
		}
		if (LNotEqual(Local2, 1)) {
			err(ts, z179, __LINE__, 0, 0, Local2, 1)
		}
	}

	Method(sw05, 0, Serialized)
	{
		OUTP("Check Switch implementation 5: inside While 1, 2 Breaks")

		Store(1, Local0)
		Store(0, Local1)
		Store(0, Local2)

		while (Local0) {
			switch (ToInteger (Local0)) {
				case (1) {
				 Increment(Local1)
				 Break
				}
				case (2) {
				 Increment(Local2)
				 Break
				}
			}
			Decrement(Local0)
		}
		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}
		if (LNotEqual(Local1, 1)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 1)
		}
		if (LNotEqual(Local2, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local2, 0)
		}
	}


	Method(sw06, 0, Serialized)
	{
		OUTP("Check Switch implementation 6: inside While 2, 1 Break")

		Store(2, Local0)
		Store(0, Local1)
		Store(0, Local2)

		while (Local0) {
			switch (ToInteger (Local0)) {
				case (1) {
				 Increment(Local1)
				}
				case (2) {
				 Increment(Local2)
				 Break
				}
			}
			Decrement(Local0)
		}
		if (LNotEqual(Local0, 0)) {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}
		if (LNotEqual(Local1, 1)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 1)
		}
		if (LNotEqual(Local2, 1)) {
			err(ts, z179, __LINE__, 0, 0, Local2, 1)
		}
	}

	Method(sw07,, Serialized)
	{
		OUTP("Check While implementation 7: Name inside, 1 step")

		Store(1, Local0)
		Store(0, Local1)

		Name(WHIN, Ones)

		while (Local0) {
			if (Local1) {
				CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
			} else {
				CH03(ts, z179, 0x2be, __LINE__, 0)
			}
			Store(Local1, WHIN)
			Decrement(Local0)
			Increment(Local1)
		}
	}

	Method(sw08,, Serialized)
	{
		OUTP("Check While implementation 8: Name inside, 2 steps")

		Store(2, Local0)
		Store(0, Local1)

		Name(WHIN, Ones)

		while (Local0) {
			if (LGreater(Local1, 2)) {
				CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
			} else {
				CH03(ts, z179, 0x2c0, __LINE__, 0)
			}
			Store(Local1, WHIN)
			Decrement(Local0)
			Increment(Local1)
		}
	}

	Method(m000)
	{
		sw00()
		sw01()
		sw02()
		sw03()

		if (LAnd(ABUU, LNot(q00a))) {
		} else {
			sw04()
			sw05()
			sw06()
		}

		sw07()

		if (ABUU) {
		} else {
			sw08()
		}
	}

	CH03(ts, z179, 0x2c1, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { sw00() }
		case (2) { sw01() }
		case (3) { sw02() }
		case (4) { sw03() }
		case (5) { sw04() }
		case (6) { sw05() }
		case (7) { sw06() }
		case (8) { sw07() }
		case (9) { sw08() }
	}
	CH03(ts, z179, 0x2c2, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(asw0) { IIN0() ms2c(1) Return(POUT) }
Method(bsw0) { IIN0() ms2c(2) Return(POUT) }
Method(csw0) { IIN0() ms2c(3) Return(POUT) }
Method(dsw0) { IIN0() ms2c(4) Return(POUT) }
Method(esw0) { IIN0() ms2c(5) Return(POUT) }
Method(fsw0) { IIN0() ms2c(6) Return(POUT) }
Method(gsw0) { IIN0() ms2c(7) Return(POUT) }
Method(hsw0) { IIN0() ms2c(8) Return(POUT) }
Method(isw0) { IIN0() ms2c(9) Return(POUT) }

/*
 * Hot issue:
 *
 * Recursive method with local named
 *
 * bwac & cwac tests should expectedly fail
 */
Method(ms2d, 1, Serialized)
{
	Name(ts, "ms2d")
	Name(Y, 0)

	Method (M001, 1, NotSerialized)
	{
		Name (X, Zero)

		If (Y) {
			If (y300) {
				CH03(ts, z179, 0x3c3, __LINE__, 0)
			} else {
				CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
			}
		} else {
			CH03(ts, z179, 0x2c4, __LINE__, 0)
		}

		Increment (Y)
		Increment (X)

		Decrement (Arg0)
		If (LGreater (Arg0, Zero)) {
			M001 (Arg0)
		}
	}

	Method(wac0)
	{
		OUTP("Recursive method with local named execution 1")

		Store(0, Y)
		M001 (0x1)
	}

	Method(wac1)
	{
		OUTP("Recursive method with local named execution 2")

		Store(0, Y)
		M001 (0x2)
	}

	Method(wac2)
	{
		OUTP("Recursive method with local named execution 4")

		Store(0, Y)
		M001 (0x4)
	}

	Method(m000)
	{
		wac0()

		if (ABUU) {
		} else {
			wac1()
		}

		if (ABUU) {
		} else {
			wac2()
		}
	}

	CH03(ts, z179, 0x2c5, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m000() }
		case (1) { wac0() }
		case (2) { wac1() }
		case (3) { wac2() }
	}
	CH03(ts, z179, 0x2c6, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(awac) { IIN0() ms2d(1) Return(POUT) }
Method(bwac) { IIN0() ms2d(2) Return(POUT) }
Method(cwac) { IIN0() ms2d(3) Return(POUT) }
Method(dwac) { IIN0() ms2d(4) Return(POUT) }

/*
 * Hot issue:
 *
 * Recursive method with local named: handmade asynchronous test:
 * - bzac can be called many times
 * - after azac any bzac should fail, but then after czac succeed again
 * - 3 consecutive execution of dzac in the different instances of ABBU
 *   should show actual behavior, on acpiexec run "thr 4 1 dzac"
 */

Event(EV00)

Method (MZAC, 1, NotSerialized)
{
	Name (X, Zero)
	Increment (X)
	OUTP(X)

	If (LGreater (Arg0, Zero))
	{
		// Block on event
		Wait(EV00, 0xFFFF)
	}
}

Method(zac0)
{
	OUTP("Method with local named execution 1: Block")

	MZAC (0x1)
}

Method(zac1)
{
	OUTP("Method with local named execution 2: Pass")

	MZAC (0x0)
}

Method(zac2)
{
	Sleep(5000)

	OUTP("Method with local named execution 3: Signal")

	Signal (EV00)
}

Name(zacz, 5)
Method(zac3)
{
	Sleep(1000)
	Decrement(zacz)

	if (LEqual(zacz, 4)) {zac0()}
	elseif (LEqual(zacz, 2)) {zac2()}
	else {zac1()}

	Return (zacz)
}

/* Methods to run manually (for ABBU only) */
Method(azac) { IIN0() zac0() Return(POUT) }
Method(bzac) { IIN0() zac1() Return(POUT) }
Method(czac) { IIN0() zac2() Return(POUT) }
Method(dzac) { IIN0() zac3() Return(POUT) }

/*
 * Hot issue:
 *
 * Example from Bob,
 * Buffer is not shortened on storing short string
 */
Method(ms2e,, Serialized)
{
	Name(ts, "ms2e")

	Name (BUF0, Buffer (12) {})

	OUTP("Buffer is not shortened on storing short string")

	CH03(ts, z179, 0x2c7, __LINE__, 0)

	Store ("ABCD", BUF0)

	Store(SizeOf (BUF0), Local0)

	if (LNotEqual(Local0, 12)) {
		err(ts, z179, __LINE__, 0, 0, Local0, 12)
	}

	CH03(ts, z179, 0x2c9, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(abuf) { IIN0() ms2e() Return(POUT) }

/*
 * Bug 246 issue:
 *
 * SUMMARY: Switch implementation can cause AE_ALREADY_EXISTS exception
 *          when Switch is within While
 */
Method(ms2f, 1, Serialized)
{
	Name(ts, "ms2f")

	Method(B246, 0, Serialized)
	{
		Name(LN00, 2)

		OUTP("Switch implementation can cause AE_ALREADY_EXISTS 1")

		Store(0, Local1)

		while (LN00) {
			switch (ToInteger (LN00)) {
				case (1) {
					Add(Local1, 1, Local1)
				}
				case (2) {
					Add(Local1, 2, Local1)
				}
			}
			Decrement(LN00)
		}

		if (LNotEqual(Local1, 3)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 3)
		}
	}

	Method(U246, 0, Serialized)
	{
		Name(LN00, 1)

		OUTP("Switch implementation can cause AE_ALREADY_EXISTS 2")

		Store(0, Local1)

		while (LN00) {
			switch (ToInteger (LN00)) {
				case (1) {
					Add(Local1, 1, Local1)
				}
				case (2) {
					Add(Local1, 2, Local1)
				}
			}
			Decrement(LN00)
		}

		if (LNotEqual(Local1, 1)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 1)
		}
	}

	CH03(ts, z179, 0x2cc, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { b246() u246() }
		case (1) { b246() }
		case (2) { u246() }
	}
	CH03(ts, z179, 0x2cd, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(a246) { IIN0() ms2f(1) Return(POUT) }
Method(b246) { IIN0() ms2f(2) Return(POUT) }

/*
 * Bug 247 issue:
 *
 * SUMMARY: ASL compiler incorrectly implements Break within Switch
 */
Method(ms30,, Serialized)
{
	Name(ts, "ms30")

	// This test actually should be used without "while (1) { ... Break}"
	// wrapping, but iASL reports "Initializer list too long" error.
	// Comment the wrappers and compile with -f iASL option.
	Method(B247)
	{
		Method(m000, 4, Serialized)
		{
			Name(LN00, 2)
			Name(CH10, 0)
			Name(CH11, 0)
			Name(CH20, 0)
			Name(CH21, 0)

			OUTP(arg0)

// Workaround for "No enclosing While statement" iASl error
while (1) {
			switch (ToInteger (arg3)) {
				case (1) {
					if (Arg1) {
						Store(1, CH10)
						Break
					}
					Store(1, CH11)
				}
				case (2) {
					if (Arg2) {
						Store(1, CH20)
						Break
					}
					Store(1, CH21)
				}
			}
Break }

			if (LEqual(Arg3, 1)) {
				if (LNotEqual(CH10, Arg1)) {
					err(ts, z179, __LINE__, 0, 0, CH10, Arg1)
				}
				if (LEqual(CH11, Arg1)) {
					err(ts, z179, __LINE__, 0, 0, CH11, Arg1)
				}
			}
			if (LEqual(Arg3, 2)) {
				if (LNotEqual(CH20, Arg2)) {
					err(ts, z179, __LINE__, 0, 0, CH20, Arg2)
				}
				if (LEqual(CH21, Arg2)) {
					err(ts, z179, __LINE__, 0, 0, CH21, Arg2)
				}
			}
		}

		OUTP("Switch implementation can cause AE_ALREADY_EXISTS 3")

		m000("Break 100", 0, 0, 1)
		m000("Break 101", 0, 1, 1)
		m000("Break 110", 1, 0, 1)
		m000("Break 111", 1, 1, 1)
		m000("Break 200", 0, 0, 2)
		m000("Break 201", 0, 1, 2)
		m000("Break 210", 1, 0, 2)
		m000("Break 211", 1, 1, 2)
	}

	CH03(ts, z179, 0x2d2, __LINE__, 0)
	b247()
	CH03(ts, z179, 0x2d3, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(a247) { IIN0() ms30() Return(POUT) }

/*
 * Hot issue:
 *
 * Load ASL operator
 */
Method(ms31, 1, Serialized)
{
	Name(ts, "ms31")

	// Originated from table/ssdt0.asl: iasl -tc ssdt0.asl
	Name(BUF0, Buffer() {
		0x53,0x53,0x44,0x54,0x34,0x00,0x00,0x00,  /* 00000000    "SSDT4..." */
		0x02,0xDE,0x49,0x6E,0x74,0x65,0x6C,0x00,  /* 00000008    "..Intel." */
		0x4D,0x61,0x6E,0x79,0x00,0x00,0x00,0x00,  /* 00000010    "Many...." */
		0x01,0x00,0x00,0x00,0x49,0x4E,0x54,0x4C,  /* 00000018    "....INTL" */
		0x15,0x12,0x06,0x20,0x14,0x0F,0x5C,0x53,  /* 00000020    "... ..\S" */
		0x53,0x30,0x30,0x00,0xA4,0x0D,0x5C,0x53,  /* 00000028    "S00...\S" */
		0x53,0x30,0x30,0x00,
	})

	OperationRegion (IST0, SystemMemory, VMEM, 0x34)

	Field(IST0, ByteAcc, NoLock, Preserve) {
		RFU0, 0x1a0,
	}

	Name(DDBH, 0)

	External(\SS00)

	Method(m000)
	{
		OUTP("ldt0: Simple Load/Unload(Field, LocalX) test")

		Store(BUF0, RFU0)

		Load(RFU0, Local0)
		CH03(ts, z179, 0x2d4, __LINE__, 0)
		OUTP("SSDT loaded")

		UnLoad(Local0)
		CH03(ts, z179, 0x2d5, __LINE__, 0)
		OUTP("SSDT unloaded")
	}

	// Manual test for ABBU
	Method(m001)
	{
		OUTP("ldt1: Simple Load(OpRegion, LocalX) test")

		Store(BUF0, RFU0)

		Load(IST0, Local0)
		CH03(ts, z179, 0x2d6, __LINE__, 0)
		OUTP("SSDT loaded")
	}

	Method(m002)
	{
		OUTP("ldt2: Simple Load/Unload(OpRegion, LocalX) test")

		Store(BUF0, RFU0)

		Load(IST0, DDBH)
		CH03(ts, z179, 0x2d7, __LINE__, 0)
		OUTP("SSDT loaded")

		Unload(DDBH)
		CH03(ts, z179, 0x2d8, __LINE__, 0)
		OUTP("SSDT unloaded")
	}

	Method(m003)
	{
		OUTP("ldt3: Simple Load/ObjectType(DDBHandle) test")

		Store(BUF0, RFU0)

		Load(IST0, Local0)
		CH03(ts, z179, 0x2d9, __LINE__, 0)
		OUTP("SSDT loaded")

		Store(ObjectType(Local0), Local1)
		if (LNotEqual(15, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 15)
		}

		Unload(DDBH)
		CH03(ts, z179, 0x2db, __LINE__, 0)
		OUTP("SSDT unloaded")
	}

	// Manual test for ABBU: hangs on MS
	Method(m013)
	{
		OUTP("ldt13: Simple Load/ObjectType(DDBHandle) test")

		Store(BUF0, RFU0)

		Load(IST0, Local0)
		CH03(ts, z179, 0x2dc, __LINE__, 0)
		OUTP("SSDT loaded")

		Store(ObjectType(Local0), Local1)
		if (LNotEqual(15, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 15)
		}
	}

	Method(m004,, Serialized)
	{
		Name(DDBH, 0)

		OUTP("ldt4: Simple Load/ObjectType(Named DDBHandle) test")

		Store(BUF0, RFU0)

		Load(IST0, DDBH)
		CH03(ts, z179, 0x2de, __LINE__, 0)
		OUTP("SSDT loaded")

		Store(ObjectType(DDBH), Local1)
		if (LNotEqual(15, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 15)
		}

		UnLoad(DDBH)
		CH03(ts, z179, 0x2e0, __LINE__, 0)
		OUTP("SSDT unloaded")
	}

	// Manual test for ABBU: hangs on MS
	Method(m014,, Serialized)
	{
		Name(DDBH, 0)

		OUTP("ldt14: Simple Load/ObjectType(Named DDBHandle) test")

		Store(BUF0, RFU0)

		Load(IST0, DDBH)
		CH03(ts, z179, 0x2e1, __LINE__, 0)
		OUTP("SSDT loaded")

		Store(ObjectType(DDBH), Local1)
		if (LNotEqual(15, Local1)) {
			err(ts, z179, __LINE__, 0, 0, Local1, 15)
		}
	}

	Method(m005,, Serialized)
	{
		Name(PAC0, Package(1){})

		OUTP("ldt5: Simple Load(OpRegion, Indexed DDBHandle) test")

		Store(BUF0, RFU0)

		Load(IST0, Index(PAC0, 0))
		CH03(ts, z179, 0x2e3, __LINE__, 0)
		OUTP("SSDT loaded")

		Store(Derefof(Index(PAC0, 0)), Local0)

		UnLoad(Local0)
		CH03(ts, z179, 0x2e4, __LINE__, 0)
		OUTP("SSDT unloaded")
	}

	// Manual test for ABBU
	Method(m015,, Serialized)
	{
		Name(PAC0, Package(1){})

		OUTP("ldt15: Simple Load(OpRegion, Indexed DDBHandle) test")

		Store(BUF0, RFU0)

		Load(IST0, Index(PAC0, 0))
		CH03(ts, z179, 0x2e5, __LINE__, 0)
		OUTP("SSDT loaded")
	}

	Method(m006)
	{
		OUTP("ldt6: Complex Load(OpRegion, LocalX) - CondRefof test")

		Store(BUF0, RFU0)

		Store(CondRefof(\SS00, Local1), Local2)
		OUTP("CondRefof before Load")
		if (Local2) {
			err(ts, z179, __LINE__, 0, 0, Local2, 0)
		}

		Load(IST0, Local0)
		CH03(ts, z179, 0x2e7, __LINE__, 0)

		Store(CondRefof(\SS00, Local3), Local4)
		OUTP("CondRefof after Load")
		if (Local4) {
		} else {
			err(ts, z179, __LINE__, 0, 0, Local4, 1)
		}

		UnLoad(Local0)
		CH03(ts, z179, 0x2e9, __LINE__, 0)

		Store(CondRefof(\SS00, Local5), Local6)
		OUTP("CondRefof after UnLoad")
		if (Local6) {
			err(ts, z179, __LINE__, 0, 0, Local6, 0)
		}
	}

	// Manual test for ABBU
	Method(m016)
	{
		OUTP("ldt16: Complex Load(OpRegion, LocalX) - CondRefof test")

		Store(BUF0, RFU0)

		Store(CondRefof(\SS00, Local1), Local2)
		OUTP("CondRefof before Load")
		if (Local2) {
			err(ts, z179, __LINE__, 0, 0, Local2, 0)
		}

		Load(IST0, Local0)
		CH03(ts, z179, 0x2ec, __LINE__, 0)

		Store(CondRefof(\SS00, Local3), Local4)
		OUTP("CondRefof after Load")
		if (Local4) {
		} else {
			err(ts, z179, __LINE__, 0, 0, Local4, 1)
		}
	}

	Method(m010)
	{
		m000()

		if (y290) {
			m002()
			m003()
			m004()
		}

		if (LAnd(y261, y290)) {
			m005()
		}

		if (y290) {
			m006()
		}
	}

	CH03(ts, z179, 0x2ee, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m010() }
		case (1) { m000() }
		case (2) { m001() }
		case (3) { m002() }
		case (4) { m003() }
		case (5) { m004() }
		case (6) { m005() }
		case (7) { m006() }
		case (8) { m013() }
		case (9) { m014() }
		case (10) { m015() }
		case (11) { m016() }
	}
	CH03(ts, z179, 0x2ef, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(aldt) { IIN0() ms31(1) Return(POUT) }
Method(bldt) { IIN0() ms31(2) Return(POUT) }
Method(cldt) { IIN0() ms31(3) Return(POUT) }
Method(dldt) { IIN0() ms31(4) Return(POUT) }
Method(eldt) { IIN0() ms31(5) Return(POUT) }
Method(fldt) { IIN0() ms31(6) Return(POUT) }
Method(gldt) { IIN0() ms31(7) Return(POUT) }
Method(hldt) { IIN0() ms31(8) Return(POUT) }
Method(ildt) { IIN0() ms31(9) Return(POUT) }
Method(jldt) { IIN0() ms31(10) Return(POUT) }
Method(kldt) { IIN0() ms31(11) Return(POUT) }

/*
 * Hot issue:
 *
 * CondRefOf ASL operator
 */
Method(ms32, 1, Serialized)
{
	Name(ts, "ms32")

	Method(m000)
	{
		OUTP("cnr0: Simple CondRefof() positive test")

		Store(CondRefof(\_SB.ABBU.IMAX), Local0)
		CH03(ts, z179, 0x2f0, __LINE__, 0)
	}

	Method(m001)
	{
		OUTP("cnr1: Simple CondRefof( , ) positive test 2")

		Store(CondRefof(\_SB.ABBU._HID, Local1), Local0)
		CH03(ts, z179, 0x2f1, __LINE__, 0)

		if (Local0) {
		} else {
			err(ts, z179, __LINE__, 0, 0, Local0, 1)
		}
	}

	Method(m002,, Serialized)
	{
		Name(I000, 0x76543210)

		OUTP("cnr2: Simple CondRefof( , ) positive test for dynamic object")

		Store(CondRefof(^m002.I000, Local1), Local0)
		if (Local0) {
			Store(Derefof(Local1), Local2)
			if (LNotEqual(0x76543210, Local2)) {
				err(ts, z179, __LINE__, 0, 0, Local2, 0x76543210)
			}
		} else {
			err(ts, z179, __LINE__, 0, 0, Local0, 1)
		}
	}

	Method(m003,, Serialized)
	{
		OUTP("cnr3: Simple CondRefof( , ) negative test for dynamic object")

		Store(CondRefof(^M003.I000, Local1), Local0)
		if (Local0) {
			err(ts, z179, __LINE__, 0, 0, Local0, 1)
		}

		Name(I000, 1)

		Store(CondRefof(^M003.I000, Local1), Local0)
		if (Local0) {
		} else {
			err(ts, z179, __LINE__, 0, 0, Local0, 0)
		}
	}

	Method(m004)
	{
		OUTP("cnr4: Simple CondRefof(_OSI, Local0) test")

		OUTP("if (CondRefOf (_OSI, Local0))")
		if (CondRefOf (_OSI, Local0))
		{
			OUTP("True")
			OUTP("_OSI (\"Windows 2001\"):")
			if (\_OSI ("Windows 2001"))
			{
				OUTP("True")
			} else {
				OUTP("False")
			}
		} else {
			OUTP("False")
		}
		CH03(ts, z179, 0x2f7, __LINE__, 0)
	}

	Method(m010)
	{
		m000()
		m001()
		m002()
		m003()
		m004()
	}

	CH03(ts, z179, 0x2f8, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) { m010() }
		case (1) { m000() }
		case (2) { m001() }
		case (3) { m002() }
		case (4) { m003() }
		case (5) { m004() }
	}
	CH03(ts, z179, 0x2f9, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(acnr) { IIN0() ms32(1) Return(POUT) }
Method(bcnr) { IIN0() ms32(2) Return(POUT) }
Method(ccnr) { IIN0() ms32(3) Return(POUT) }
Method(dcnr) { IIN0() ms32(4) Return(POUT) }
Method(ecnr) { IIN0() ms32(5) Return(POUT) }

/*
 * Hot issue:
 *
 * Check storing of a Device into LocalX
 */
Method(ms33, 1, Serialized)
{
	Name(ts, "ms33")

	Method(asdl)
	{
/*
// Removed 09/2015. iASL now disallows these stores

		OUTP("Store _SB.ABBU Device object into LocalX, don't check the type")

		Store(\_SB.ABBU, Local0)
*/

		if (LOr(ABUU, SLCK)) {
			CH03(ts, z179, 0x2fa, __LINE__, 0)
		} else {
			CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
		}
	}

	Method(bsdl)
	{
/*
// Removed 09/2015. iASL now disallows these stores
		OUTP("Store _SB.ABBU Device object into LocalX")

		Store(\_SB.ABBU, Local0)
*/

		if (LOr(ABUU, SLCK)) {
			Store(ObjectType(Local0), Local1)
			if (LNotEqual(6, Local1)) {
				err(ts, z179, __LINE__, 0, 0, Local1, 6)
			}
		} else {
			CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
		}
	}

	Method(csdl,, Serialized)
	{
		Device(DLOC) {}

/*
// Removed 09/2015. iASL now disallows these stores

		OUTP("Store an improper dynamic Device object into LocalX")

		Store(DLOC, Local0)
*/

		if (LOr(ABUU, SLCK)) {
			Store(ObjectType(Local0), Local1)
			if (LNotEqual(6, Local1)) {
				err(ts, z179, __LINE__, 0, 0, Local1, 6)
			} else {
				OUTP("Ok: ObjectType succeeded")
			}
		} else {
			CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
		}
	}

	Method(dsdl)
	{
		External(\_SB.LNKA)

		OUTP("Store _SB.LNKA Device object into LocalX")

		if (CondRefof(\_SB.LNKA, Local2)) {
		} else {
			OUTP("CondRefof for _SB.LNKA returns FALSE")
			return
		}

		Store(\_SB.LNKA, Local0)

		if (LOr(ABUU, SLCK)) {
			Store(ObjectType(Local0), Local1)
			if (LNotEqual(6, Local1)) {
				err(ts, z179, __LINE__, 0, 0, Local1, 6)
			}
		} else {
			CH04(ts, 0, 0xff, z179, __LINE__, 0, 0)
		}
	}

	CH03(ts, z179, 0x2a2, __LINE__, 0)
	switch (ToInteger (Arg0)) {
		case (0) {
			asdl()
			bsdl()
			csdl()
			dsdl()
		}
		case (1) { asdl() }
		case (2) { bsdl() }
		case (3) { csdl() }
		case (4) { dsdl() }
	}
	CH03(ts, z179, 0x2a3, __LINE__, 0)
}

/* Methods to run manually (for ABBU only) */
Method(asdl) { IIN0() ms33(1) Return(POUT) }
Method(bsdl) { IIN0() ms33(2) Return(POUT) }
Method(csdl) { IIN0() ms33(3) Return(POUT) }
Method(dsdl) { IIN0() ms33(4) Return(POUT) }

Method(msfe)
{
	// Bug 63 issues
	SRMT("ms10")
	ms10(0)

	// Bug 83 issues
	SRMT("ms11")
	ms11(0)

	// Bug 100 issues
	SRMT("ms12")
	ms12()

	// Bug 113 issues
	SRMT("ms13")
	ms13(0)

	// Bug 114 issues
	SRMT("ms14")
	ms14(0)

	// Bug 115 issues
	SRMT("ms15")
	ms15(0)

	// Bug 118 issues
	SRMT("ms16")
	ms16(0)

	// Bug 126 issues
	SRMT("ms17")
	ms17(0)

	// Bug 127 issues
	SRMT("ms18")
	if (ABUU) {
		BLCK()
	} else {
		ms18()
	}

	// Bug 128 issues
	SRMT("ms19")
	ms19(0)

	// Bug 131 issues
	SRMT("ms1a")
	ms1a(0)

	// Bug 132 issues
	SRMT("ms1b")
	ms1b(0)

	// Bug 133 issues
	SRMT("ms1c")
	ms1c(0)

	// Bug 134 issues
	SRMT("ms1d")
	ms1d(0)

	// Bug 136 issues
	SRMT("ms1e")
	if (ABUU) {
		BLCK()
	} else {
		ms1e()
	}

	// Local Reference into the Package issues
	SRMT("ms1f")
	ms1f(0)

	// Forward reference within a control method
	SRMT("ms20")
	ms20(0)

	// Recursive method execution
	SRMT("ms21")
	ms21(0)

	// Conditional reference within a control method
	SRMT("ms22")
	ms22(0)

	// Implicit return
	SRMT("ms23")
	ms23(0)

	// Increment/Decrement with String/Buffer
	SRMT("ms24")
	if (ABUU) {
		BLCK()
	} else {
		ms24()
	}

	// Check Store(..., DeRefof(...)) behavior
	SRMT("ms25")
	if (ABUU) {
		BLCK()
	} else {
		ms25(0)
	}

	// Exceeding Field Unit
	SRMT("ms26")
	if (SMBA) {
		ms26(0)
	} else {
		BLCK()
	}

	// Check IndexField implementation
	SRMT("ms27")
	if (SMBA) {
		ms27(0)
	} else {
		BLCK()
	}

	SRMT("mt27")
	if (SMBA) {
		mt27(0)
	} else {
		BLCK()
	}

	SRMT("mu27")
	if (SMBA) {
		mu27(0)
	} else {
		BLCK()
	}

	SRMT("mv27")
	if (SMBA) {
		mv27(0)
	} else {
		BLCK()
	}

	SRMT("mw27")
	if (SMBA) {
		mw27(0)
	} else {
		BLCK()
	}

	SRMT("mx27")
	if (SMBA) {
		mx27(0)
	} else {
		BLCK()
	}

	SRMT("my27")
	if (SMBA) {
		my27(0)
	} else {
		BLCK()
	}

	SRMT("mz27")
	if (SMBA) {
		mz27(0)
	} else {
		BLCK()
	}

	// Check BankField implementation
	SRMT("ms28")
	if (SMBA) {
		ms28()
	} else {
		BLCK()
	}

	// Check Acquire/Release
	SRMT("ms29")
	ms29(0)

	// Check ToBuffer optional store
	SRMT("ms2a")
	ms2a(0)

	// Check Package size calculation
	SRMT("ms2b")
	ms2b(0)

	// Check Switch implementation
	SRMT("ms2c")
	ms2c(0)

	// Recursive method with local named
	SRMT("ms2d")
	ms2d(0)

	// Buffer is not shortened on storing short string
	SRMT("ms2e")
	ms2e()

	// Bug 246 issues
	SRMT("ms2f")
	ms2f(0)

	// Bug 247 issues
	SRMT("ms30")
	if (ABUU) {
		BLCK()
	} else {
		ms30()
	}

	// Load ASL operator
	SRMT("ms31")
	if (ABUU) {
		BLCK()
	} else {
		ms31(0)
	}

	// CondRefOf ASL operator
	SRMT("ms32")
	ms32(0)

	// Storing of a Device into LocalX
	SRMT("ms33")
	ms33(0)
}
