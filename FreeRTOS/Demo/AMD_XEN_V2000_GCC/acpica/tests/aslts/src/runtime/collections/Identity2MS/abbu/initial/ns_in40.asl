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
 * Method invocations, Arguments, Locals...
 *
 * The same object is passed simultaneously by several Args,
 * thus, the same object is represented in stack several times.
 */

Name(z167, 167)

/*
 * See comment below why the functionally unnecessary
 * or commented branches 'if (chk0)' are not removed.
 *
 * They remind the problems of adjusting AML code for MS.
 */

Name(cmd0, 0)
Name(stp0, 0)

// Opcodes of actions
Name(OT00, 0)	// ObjectType
Name(AD00, 1)	// Add
Name(LN00, 2)	// LNotEqual
Name(LN01, 3)	// LNotEqual
Name(LN02, 4)	// LNotEqual
Name(LN03, 5)	// LNotEqual
Name(LN04, 6)	// LNotEqual
Name(LN05, 7)	// LNotEqual
Name(LN06, 8)	// LNotEqual
Name(LN07, 9)	// LNotEqual
Name(LN08, 10)	// LNotEqual

/*
 * Verify the type of object
 */
Method(obt0, 2)
{
	Store(ObjectType(arg0), Local0)
	if (LNotEqual(Local0, arg1)) {
		err("obt0", z167, __LINE__, 0, 0, Local0, arg1)
	}
	Return (5)
}

/*
 * Do simple verification actions
 *
 * arg0 - command to be performed
 * arg1 - object
 * arg2 - depends on arg0
 */
Method(act0, 4, Serialized)
{
	Name(ts, "act0")

	Switch (ToInteger (arg0)) {
	Case (0) {		// ObjectType
		Store(ObjectType(arg1), Local0)
		if (LNotEqual(Local0, arg2)) {
			err(ts, z167, __LINE__, 0, 0, Local0, arg2)
		}
	}
	Case (1) {		// Add
		Add(arg1, arg2, Local0)
		if (LNotEqual(Local0, arg3)) {
			err(ts, z167, __LINE__, 0, 0, Local0, arg3)
		}
	}
	Case (2) {		// LNotEqual
		if (LNotEqual(arg1, 0xabcd0000)) {
			err(ts, z167, __LINE__, 0, 0, arg1, 0xabcd0000)
		}
	}
	Case (3) {		// LNotEqual
		// if (chk0) {
		if (LNotEqual(arg1, "qwrtyu0003")) {
			err(ts, z167, __LINE__, 0, 0, arg1, "qwrtyu0003")
		}
		// }
	}
	Case (4) {		// LNotEqual
		// if (chk0) {
		if (LNotEqual(arg1, "abcd0800")) {
			err(ts, z167, __LINE__, 0, 0, arg1, "abcd0800")
		}
		// }
	}
	Case (5) {		// LNotEqual
		// if (chk0) {
		if (LNotEqual(arg1, Buffer() {0xb0,0xb1,0xb2,0xb3,0xb4})) {
			err(ts, z167, __LINE__, 0, 0, arg1, Buffer() {0xb0,0xb1,0xb2,0xb3,0xb4})
		}
		// }
	}
	Case (6) {		// LNotEqual
		Store(DerefOf(Index(arg1, 1)), Local0)
		if (LNotEqual(Local0, 0xabcd0902)) {
			err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0902)
		}
	}
	Case (7) {		// LNotEqual
		if (LNotEqual(arg1, 0xabcd0a00)) {
			err(ts, z167, __LINE__, 0, 0, arg1, 0xabcd0a00)
		}
	}
	Case (8) {		// LNotEqual
		if (LNotEqual(arg1, 0xabababab)) {
			err(ts, z167, __LINE__, 0, 0, arg1, 0xabababab)
		}
	}
	Case (9) {		// LNotEqual
		if (LNotEqual(arg1, 0)) {
			err(ts, z167, __LINE__, 0, 0, arg1, 0)
		}
	}
	Case (10) {		// LNotEqual
		if (LNotEqual(arg1, Buffer(){0x08, 0x0d, 0xcd, 0xab})) {
			err(ts, z167, __LINE__, 0, 0, arg1, Buffer(){0x08, 0x0d, 0xcd, 0xab})
		}
	}
	} // Switch (arg0)
}

/* Methods with different # of args but doing the same */

Method(mI01, 1, Serialized)
{
	if (LNot(chk0)) {

		/*
		 * This code helps for some branches to work on MS.
		 * This code being placed in Switch below doesn't work.
		 * I moved this code from the Switch below and replaced
		 * calls to Methods by the contents of those methods.
		 *
		 * Nevertheless, I have not removed the 'if (chk0)' in
		 * Switch below and beneath it to show additionally the
		 * problems I encountered, where MS doesn't work, while
		 * attempting to work with Switch.
		 */

		if (LEqual(cmd0, 1)) {		// Integer
			Store(ObjectType(arg0), Local0)
			if (LNotEqual(Local0, c009)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, c009)
			}
			Add(arg0, 1, Local0)
			if (LNotEqual(Local0, 0xabcd0001)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, 0xabcd0001)
			}
			if (LNotEqual(arg0, 0xabcd0000)) {
				err("mI01", z167, __LINE__, 0, 0, arg0, 0xabcd0000)
			}

			Return (arg0)
		}

		if (LEqual(cmd0, 2)) {		// String
			Store(ObjectType(arg0), Local0)
			if (LNotEqual(Local0, c00a)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, c00a)
			}

			if (LNot(run4)) { // Run on ACPICA only
				if (LNotEqual(arg0, "qwrtyu0003")) {
					err("mI01", z167, __LINE__, 0, 0, arg0, "qwrtyu0003")
				}
			}
			Return (arg0)
		}

		if (LEqual(cmd0, 3)) {		// String applicable to the Implicit Conversion Rules ("abcd0800")
			Store(ObjectType(arg0), Local0)
			if (LNotEqual(Local0, c00a)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, c00a)
			}

			if (LNot(run4)) { // Run on ACPICA only
				Add(arg0, 5, Local0)
				if (LNotEqual(Local0, 0xabcd0805)) {
					err("mI01", z167, __LINE__, 0, 0, Local0, 0xabcd0805)
				}
				if (LNotEqual(arg0, "abcd0800")) {
					err("mI01", z167, __LINE__, 0, 0, arg0, "abcd0800")
				}
			}

			Return (arg0)
		}

		if (LEqual(cmd0, 4)) {		// Buffer
			Store(ObjectType(arg0), Local0)
			if (LNotEqual(Local0, c00b)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, c00b)
			}

			if (LNot(run4)) { // Run on ACPICA only
				Add(arg0, 7, Local0)
				if (LNotEqual(Local0, 0xb4b3b2b1b7)) {
					err("mI01", z167, __LINE__, 0, 0, Local0, 0xb4b3b2b1b7)
				}
				if (LNotEqual(arg0, Buffer() {0xb0,0xb1,0xb2,0xb3,0xb4})) {
					err("mI01", z167, __LINE__, 0, 0, arg0, Buffer() {0xb0,0xb1,0xb2,0xb3,0xb4})
				}
			}

			Return (arg0)
		}

		if (LEqual(cmd0, 5)) {		// Package
			Store(ObjectType(arg0), Local0)
			if (LNotEqual(Local0, c00c)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, c00c)
			}
			Store(DerefOf(Index(arg0, 1)), Local0)
			if (LNotEqual(Local0, 0xabcd0902)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, 0xabcd0902)
			}
			Return (arg0)
		}

		if (LEqual(cmd0, 6)) {		// Field
			Store(ObjectType(arg0), Local0)
			if (LNotEqual(Local0, c009)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, c009)
			}
			Add(arg0, 9, Local0)
			if (LNotEqual(Local0, 0xabcd0a09)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, 0xabcd0a09)
			}
			if (LNotEqual(arg0, 0xabcd0a00)) {
				err("mI01", z167, __LINE__, 0, 0, arg0, 0xabcd0a00)
			}

			Return (arg0)
		}

		if (LEqual(cmd0, 7)) {		// Device
			Store(ObjectType(arg0), Local0)
			if (LNotEqual(Local0, c00e)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, c00e)
			}
			Return (arg0)
		}

		if (LEqual(cmd0, 8)) {		// Event
			Store(ObjectType(arg0), Local0)
			if (LNotEqual(Local0, c00f)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, c00f)
			}
			Return (arg0)
		}

		if (LEqual(cmd0, 9)) {		// Mutex
			Store(ObjectType(arg0), Local0)
			if (LNotEqual(Local0, c011)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, c011)
			}
			Return (arg0)
		}

		if (LEqual(cmd0, 10)) {		// Operation Region
			Store(ObjectType(arg0), Local0)
			if (LNotEqual(Local0, c012)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, c012)
			}
			Return (arg0)
		}

		if (LEqual(cmd0, 11)) {		// Power Resource
			Store(ObjectType(arg0), Local0)
			if (LNotEqual(Local0, c013)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, c013)
			}
			Return (arg0)
		}

		if (LEqual(cmd0, 12)) {		// Processor
			Store(ObjectType(arg0), Local0)
			if (LNotEqual(Local0, c014)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, c014)
			}
			Return (arg0)
		}

		if (LEqual(cmd0, 13)) {		// Thermal Zone
			Store(ObjectType(arg0), Local0)
			if (LNotEqual(Local0, c015)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, c015)
			}
			Return (arg0)
		}

		if (LEqual(cmd0, 14)) {		// Index Field
			Store(ObjectType(arg0), Local0)
			if (LNotEqual(Local0, c009)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, c009)
			}
			Add(arg0, 9, Local0)
			if (LNotEqual(Local0, 0xabababb4)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, 0xabababb4)
			}
			if (LNotEqual(arg0, 0xabababab)) {
				err("mI01", z167, __LINE__, 0, 0, arg0, 0xabababab)
			}
			Return (arg0)
		}

		if (LEqual(cmd0, 15)) {		// Bank Field
			Store(ObjectType(arg0), Local0)
			if (LNotEqual(Local0, c009)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, c009)
			}
			Add(arg0, 9, Local0)
			if (LNotEqual(Local0, 9)) {
				err("mI01", z167, __LINE__, 0, 0, Local0, 9)
			}
			if (LNotEqual(arg0, 0)) {
				err("mI01", z167, __LINE__, 0, 0, arg0, 0)
			}

			Return (arg0)
		}

		if (LEqual(cmd0, 16)) {		// Buffer Field

			// On MS ObjectType(BufferField) == c00b

			Store(ObjectType(arg0), Local0)
			if (LAnd(LNotEqual(Local0, c009), LNotEqual(Local0, c00b))) {
				err("mI01", z167, __LINE__, 0, 0, Local0, c00b)
			}

			if (chk0) {
				Add(arg0, 2, Local0)
				if (LNotEqual(Local0, 0xabcd0d0a)) {
					err("mI01", z167, __LINE__, 0, 0, Local0, 0xabcd0d0a)
				}
				if (LNotEqual(arg0, 0xabcd0d08)) {
					err("mI01", z167, __LINE__, 0, 0, arg0, 0xabcd0d08)
				}
			}
			Return (arg0)
		}
	}

	Switch (ToInteger (cmd0)) {
		Case (1) {		// Integer
			act0(OT00, arg0, c009, 0)
			act0(LN00, arg0, 0, 0)
			act0(AD00, arg0, 1, 0xabcd0001)
		}
		Case (2) {		// String ("qwrtyu0003")
			act0(OT00, arg0, c00a, 0)
			act0(LN01, arg0, 0, 0)
		}
		Case (3) {		// String applicable to the Implicit Conversion Rules ("abcd0800")
			act0(OT00, arg0, c00a, 0)
			act0(LN02, arg0, 0, 0)
			// if (chk0) {
			act0(AD00, arg0, 5, 0xabcd0805)
			// }
		}
		Case (4) {		// Buffer
			act0(OT00, arg0, c00b, 0)
			act0(LN03, arg0, 0, 0)
			// if (chk0) {
			act0(AD00, arg0, 7, 0xb4b3b2b1b7)
			// }
		}
		Case (5) {		// Package
			act0(OT00, arg0, c00c, 0)
			act0(LN04, arg0, 0, 0)
		}
		Case (6) {		// Field
			act0(OT00, arg0, c009, 0)
			// if (chk0) {
			// This breaks Field (see qqq below):
			act0(LN05, arg0, 0, 0)
			// }
			act0(AD00, arg0, 9, 0xabcd0a09)
		}
		Case (7) {		// Device
			act0(OT00, arg0, c00e, 0)
		}
		Case (8) {		// Event
			act0(OT00, arg0, c00f, 0)
		}
		Case (9) {		// Mutex
			act0(OT00, arg0, c011, 0)
		}
		Case (10) {		// Operation Region
			act0(OT00, arg0, c012, 0)
		}
		Case (11) {		// Power Resource
			// if (chk0) {
			act0(OT00, arg0, c013, 0)
			// }
		}
		Case (12) {		// Processor
			act0(OT00, arg0, c014, 0)
		}
		Case (13) {		// Thermal Zone
			act0(OT00, arg0, c015, 0)
		}
		Case (14) {		// Index Field
			act0(OT00, arg0, c009, 0)
			// if (chk0) {
			act0(LN06, arg0, 0, 0)
			// }
			act0(AD00, arg0, 9, 0xabababb4)
		}
		Case (15) {		// Bank Field
			// if (chk0) {
			act0(OT00, arg0, c009, 0)
			// }
			// if (chk0) {
			act0(LN07, arg0, 0, 0)
			// }
			// if (chk0) {
			act0(AD00, arg0, 9, 9)
			// }
		}
		Case (16) {		// Buffer Field
			// if (chk0) {
			act0(OT00, arg0, c00b, 0)
			// }
			// if (chk0) {
			act0(LN08, arg0, 0, 0)
			// }
			// if (chk0) {
			act0(AD00, arg0, 2, Buffer(){0x0a, 0x0d, 0xcd, 0xab})
			// }
		}
		Default {		// Uninitialized
			act0(OT00, arg0, c008, 0)
		}

	} // Switch (arg0)

	Return (arg0)
}

Method(mI02, 2) {
	mI01(arg0)
	mI01(arg1)
	Return (arg0)
}
Method(mI03, 3) {
	mI01(arg0)
	mI01(arg1)
	mI01(arg2)
	Return (arg0)
}
Method(mI04, 4) {
	mI01(arg0)
	mI01(arg1)
	mI01(arg2)
	mI01(arg3)
	Return (arg0)
}
Method(mI05, 5) {
	mI01(arg0)
	mI01(arg1)
	mI01(arg2)
	mI01(arg3)
	mI01(arg4)
	Return (arg0)
}
Method(mI06, 6) {
	mI01(arg0)
	mI01(arg1)
	mI01(arg2)
	mI01(arg3)
	mI01(arg4)
	mI01(arg5)
	Return (arg0)
}
Method(mI07, 7) {
	mI01(arg0)
	mI01(arg1)
	mI01(arg2)
	mI01(arg3)
	mI01(arg4)
	mI01(arg5)
	mI01(arg6)
	Return (arg0)
}

Method(in40, 7, Serialized)
{
	Name(ts, "in40")

	Name(i000, 0xabcd0000)
	Name(s000, "qwrtyu0003")
	Name(s001, "abcd0800")
	Name(b000, Buffer() {0xb0,0xb1,0xb2,0xb3,0xb4})
	Name(p000, Package() {0xabcd0901, 0xabcd0902, 0xabcd0903})
	Method(mmm0,, Serialized) {
		Name(im00, 0xabcd0004)
		Name(sm00, "qwertyui")
		// Return ( "qwertyui" )
	}
	Method(mmm1,, Serialized) {
		Name(im00, 0xabcd0004)
		Name(sm00, "qwertyui")
		// Return ( 0xabcd0004 )
		Return ( "qwertyui" )
	}


	/*
	 * Integer
	 */
	Name(ii00, 0)
	Name(ii01, 0)
	Name(ii03, 0)
	Name(ii05, 0)

	Store(1, cmd0)
	Store(i000, ii00)


	/*
	 * Modification 0:
	 */

	mI01(ii00)
	mI02(ii00, ii00)
	mI03(ii00, ii00, ii00)
	mI04(ii00, ii00, ii00, ii00)
	mI05(ii00, ii00, ii00, ii00, ii00)
	mI06(ii00, ii00, ii00, ii00, ii00, ii00)
	mI07(ii00, ii00, ii00, ii00, ii00, ii00, ii00)

	mI01(
		mI01(ii00))

	mI02(
		mI01(ii00),
		mI02(ii00, ii00))

	mI03(
		mI01(ii00),
		mI02(ii00, ii00),
		mI03(ii00, ii00, ii00))

	mI04(
		mI01(ii00),
		mI02(ii00, ii00),
		mI03(ii00, ii00, ii00),
		mI04(ii00, ii00, ii00, ii00))

	if (y262) {

	mI05(
		mI01(ii00),
		mI02(ii00, ii00),
		mI03(ii00, ii00, ii00),
		mI04(ii00, ii00, ii00, ii00),
		mI05(ii00, ii00, ii00, ii00, ii00))

	mI06(
		mI01(ii00),
		mI02(ii00, ii00),
		mI03(ii00, ii00, ii00),
		mI04(ii00, ii00, ii00, ii00),
		mI05(ii00, ii00, ii00, ii00, ii00),
		mI06(ii00, ii00, ii00, ii00, ii00, ii00))
	mI07(
		mI01(ii00),
		mI02(ii00, ii00),
		mI03(ii00, ii00, ii00),
		mI04(ii00, ii00, ii00, ii00),
		mI05(ii00, ii00, ii00, ii00, ii00),
		mI06(ii00, ii00, ii00, ii00, ii00, ii00),
		mI07(ii00, ii00, ii00, ii00, ii00, ii00, ii00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 1:
	 *
	 * Some params are intermediately stored to Locals
	 */

	Store(ii00, Local1)
	Store(ii00, Local3)
	Store(ii00, Local5)

	mI01(ii00)
	mI02(ii00, Local1)
	mI03(ii00, Local1, ii00)
	mI04(ii00, Local1, ii00, Local3)
	mI05(ii00, Local1, ii00, Local3, ii00)
	mI06(ii00, Local1, ii00, Local3, ii00, Local5)
	mI07(ii00, Local1, ii00, Local3, ii00, Local5, ii00)

	mI01(
		mI01(ii00))

	mI02(
		mI01(ii00),
		mI02(ii00, Local1))

	mI03(
		mI01(ii00),
		mI02(ii00, Local1),
		mI03(ii00, Local1, ii00))

	mI04(
		mI01(ii00),
		mI02(ii00, Local1),
		mI03(ii00, Local1, ii00),
		mI04(ii00, Local1, ii00, Local3))

	if (y262) {

	mI05(
		mI01(ii00),
		mI02(ii00, Local1),
		mI03(ii00, Local1, ii00),
		mI04(ii00, Local1, ii00, Local3),
		mI05(ii00, Local1, ii00, Local3, ii00))

	mI06(
		mI01(ii00),
		mI02(ii00, Local1),
		mI03(ii00, Local1, ii00),
		mI04(ii00, Local1, ii00, Local3),
		mI05(ii00, Local1, ii00, Local3, ii00),
		mI06(ii00, Local1, ii00, Local3, ii00, Local5))
	mI07(
		mI01(ii00),
		mI02(ii00, Local1),
		mI03(ii00, Local1, ii00),
		mI04(ii00, Local1, ii00, Local3),
		mI05(ii00, Local1, ii00, Local3, ii00),
		mI06(ii00, Local1, ii00, Local3, ii00, Local5),
		mI07(ii00, Local1, ii00, Local3, ii00, Local5, ii00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 2:
	 *
	 * Some params are intermediately stored to Args (effectively local)
	 */

	Store(ii00, Arg1)
	Store(ii00, Arg3)
	Store(ii00, Arg5)

	mI01(ii00)
	mI02(ii00, Arg1)
	mI03(ii00, Arg1, ii00)
	mI04(ii00, Arg1, ii00, Arg3)
	mI05(ii00, Arg1, ii00, Arg3, ii00)
	mI06(ii00, Arg1, ii00, Arg3, ii00, Arg5)
	mI07(ii00, Arg1, ii00, Arg3, ii00, Arg5, ii00)

	mI01(
		mI01(ii00))

	mI02(
		mI01(ii00),
		mI02(ii00, Arg1))

	mI03(
		mI01(ii00),
		mI02(ii00, Arg1),
		mI03(ii00, Arg1, ii00))

	mI04(
		mI01(ii00),
		mI02(ii00, Arg1),
		mI03(ii00, Arg1, ii00),
		mI04(ii00, Arg1, ii00, Arg3))

	if (y262) {

	mI05(
		mI01(ii00),
		mI02(ii00, Arg1),
		mI03(ii00, Arg1, ii00),
		mI04(ii00, Arg1, ii00, Arg3),
		mI05(ii00, Arg1, ii00, Arg3, ii00))

	mI06(
		mI01(ii00),
		mI02(ii00, Arg1),
		mI03(ii00, Arg1, ii00),
		mI04(ii00, Arg1, ii00, Arg3),
		mI05(ii00, Arg1, ii00, Arg3, ii00),
		mI06(ii00, Arg1, ii00, Arg3, ii00, Arg5))
	mI07(
		mI01(ii00),
		mI02(ii00, Arg1),
		mI03(ii00, Arg1, ii00),
		mI04(ii00, Arg1, ii00, Arg3),
		mI05(ii00, Arg1, ii00, Arg3, ii00),
		mI06(ii00, Arg1, ii00, Arg3, ii00, Arg5),
		mI07(ii00, Arg1, ii00, Arg3, ii00, Arg5, ii00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 3:
	 *
	 * Some params are intermediately stored to Named
	 */

	Store(ii00, ii01)
	Store(ii00, ii03)
	Store(ii00, ii05)

	mI01(ii00)
	mI02(ii00, ii01)
	mI03(ii00, ii01, ii00)
	mI04(ii00, ii01, ii00, ii03)
	mI05(ii00, ii01, ii00, ii03, ii00)
	mI06(ii00, ii01, ii00, ii03, ii00, ii05)
	mI07(ii00, ii01, ii00, ii03, ii00, ii05, ii00)

	mI01(
		mI01(ii00))

	mI02(
		mI01(ii00),
		mI02(ii00, ii01))

	mI03(
		mI01(ii00),
		mI02(ii00, ii01),
		mI03(ii00, ii01, ii00))

	mI04(
		mI01(ii00),
		mI02(ii00, ii01),
		mI03(ii00, ii01, ii00),
		mI04(ii00, ii01, ii00, ii03))

	if (y262) {

	mI05(
		mI01(ii00),
		mI02(ii00, ii01),
		mI03(ii00, ii01, ii00),
		mI04(ii00, ii01, ii00, ii03),
		mI05(ii00, ii01, ii00, ii03, ii00))

	mI06(
		mI01(ii00),
		mI02(ii00, ii01),
		mI03(ii00, ii01, ii00),
		mI04(ii00, ii01, ii00, ii03),
		mI05(ii00, ii01, ii00, ii03, ii00),
		mI06(ii00, ii01, ii00, ii03, ii00, ii05))
	mI07(
		mI01(ii00),
		mI02(ii00, ii01),
		mI03(ii00, ii01, ii00),
		mI04(ii00, ii01, ii00, ii03),
		mI05(ii00, ii01, ii00, ii03, ii00),
		mI06(ii00, ii01, ii00, ii03, ii00, ii05),
		mI07(ii00, ii01, ii00, ii03, ii00, ii05, ii00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * String
	 */
	Name(ss00, "v")
	Name(ss01, "v")
	Name(ss03, "v")
	Name(ss05, "v")

	Store(2, cmd0)
	Store(s000, ss00)


	/*
	 * Modification 0:
	 */

	mI01(ss00)
	mI02(ss00, ss00)
	mI03(ss00, ss00, ss00)
	mI04(ss00, ss00, ss00, ss00)
	mI05(ss00, ss00, ss00, ss00, ss00)
	mI06(ss00, ss00, ss00, ss00, ss00, ss00)
	mI07(ss00, ss00, ss00, ss00, ss00, ss00, ss00)

	mI01(
		mI01(ss00))

	mI02(
		mI01(ss00),
		mI02(ss00, ss00))

	mI03(
		mI01(ss00),
		mI02(ss00, ss00),
		mI03(ss00, ss00, ss00))

	mI04(
		mI01(ss00),
		mI02(ss00, ss00),
		mI03(ss00, ss00, ss00),
		mI04(ss00, ss00, ss00, ss00))

	if (y262) {

	mI05(
		mI01(ss00),
		mI02(ss00, ss00),
		mI03(ss00, ss00, ss00),
		mI04(ss00, ss00, ss00, ss00),
		mI05(ss00, ss00, ss00, ss00, ss00))

	mI06(
		mI01(ss00),
		mI02(ss00, ss00),
		mI03(ss00, ss00, ss00),
		mI04(ss00, ss00, ss00, ss00),
		mI05(ss00, ss00, ss00, ss00, ss00),
		mI06(ss00, ss00, ss00, ss00, ss00, ss00))
	mI07(
		mI01(ss00),
		mI02(ss00, ss00),
		mI03(ss00, ss00, ss00),
		mI04(ss00, ss00, ss00, ss00),
		mI05(ss00, ss00, ss00, ss00, ss00),
		mI06(ss00, ss00, ss00, ss00, ss00, ss00),
		mI07(ss00, ss00, ss00, ss00, ss00, ss00, ss00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 1:
	 *
	 * Some params are intermediately stored to Locals
	 */

	Store(ss00, Local1)
	Store(ss00, Local3)
	Store(ss00, Local5)

	mI01(ss00)
	mI02(ss00, Local1)
	mI03(ss00, Local1, ss00)
	mI04(ss00, Local1, ss00, Local3)
	mI05(ss00, Local1, ss00, Local3, ss00)
	mI06(ss00, Local1, ss00, Local3, ss00, Local5)
	mI07(ss00, Local1, ss00, Local3, ss00, Local5, ss00)

	mI01(
		mI01(ss00))

	mI02(
		mI01(ss00),
		mI02(ss00, Local1))

	mI03(
		mI01(ss00),
		mI02(ss00, Local1),
		mI03(ss00, Local1, ss00))

	mI04(
		mI01(ss00),
		mI02(ss00, Local1),
		mI03(ss00, Local1, ss00),
		mI04(ss00, Local1, ss00, Local3))

	if (y262) {

	mI05(
		mI01(ss00),
		mI02(ss00, Local1),
		mI03(ss00, Local1, ss00),
		mI04(ss00, Local1, ss00, Local3),
		mI05(ss00, Local1, ss00, Local3, ss00))

	mI06(
		mI01(ss00),
		mI02(ss00, Local1),
		mI03(ss00, Local1, ss00),
		mI04(ss00, Local1, ss00, Local3),
		mI05(ss00, Local1, ss00, Local3, ss00),
		mI06(ss00, Local1, ss00, Local3, ss00, Local5))
	mI07(
		mI01(ss00),
		mI02(ss00, Local1),
		mI03(ss00, Local1, ss00),
		mI04(ss00, Local1, ss00, Local3),
		mI05(ss00, Local1, ss00, Local3, ss00),
		mI06(ss00, Local1, ss00, Local3, ss00, Local5),
		mI07(ss00, Local1, ss00, Local3, ss00, Local5, ss00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 2:
	 *
	 * Some params are intermediately stored to Args (effectively local)
	 */

	Store(ss00, Arg1)
	Store(ss00, Arg3)
	Store(ss00, Arg5)

	mI01(ss00)
	mI02(ss00, Arg1)
	mI03(ss00, Arg1, ss00)
	mI04(ss00, Arg1, ss00, Arg3)
	mI05(ss00, Arg1, ss00, Arg3, ss00)
	mI06(ss00, Arg1, ss00, Arg3, ss00, Arg5)
	mI07(ss00, Arg1, ss00, Arg3, ss00, Arg5, ss00)

	mI01(
		mI01(ss00))

	mI02(
		mI01(ss00),
		mI02(ss00, Arg1))

	mI03(
		mI01(ss00),
		mI02(ss00, Arg1),
		mI03(ss00, Arg1, ss00))

	mI04(
		mI01(ss00),
		mI02(ss00, Arg1),
		mI03(ss00, Arg1, ss00),
		mI04(ss00, Arg1, ss00, Arg3))

	if (y262) {

	mI05(
		mI01(ss00),
		mI02(ss00, Arg1),
		mI03(ss00, Arg1, ss00),
		mI04(ss00, Arg1, ss00, Arg3),
		mI05(ss00, Arg1, ss00, Arg3, ss00))

	mI06(
		mI01(ss00),
		mI02(ss00, Arg1),
		mI03(ss00, Arg1, ss00),
		mI04(ss00, Arg1, ss00, Arg3),
		mI05(ss00, Arg1, ss00, Arg3, ss00),
		mI06(ss00, Arg1, ss00, Arg3, ss00, Arg5))
	mI07(
		mI01(ss00),
		mI02(ss00, Arg1),
		mI03(ss00, Arg1, ss00),
		mI04(ss00, Arg1, ss00, Arg3),
		mI05(ss00, Arg1, ss00, Arg3, ss00),
		mI06(ss00, Arg1, ss00, Arg3, ss00, Arg5),
		mI07(ss00, Arg1, ss00, Arg3, ss00, Arg5, ss00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 3:
	 *
	 * Some params are intermediately stored to Named
	 */

	Store(ss00, ss01)
	Store(ss00, ss03)
	Store(ss00, ss05)

	mI01(ss00)
	mI02(ss00, ss01)
	mI03(ss00, ss01, ss00)
	mI04(ss00, ss01, ss00, ss03)
	mI05(ss00, ss01, ss00, ss03, ss00)
	mI06(ss00, ss01, ss00, ss03, ss00, ss05)
	mI07(ss00, ss01, ss00, ss03, ss00, ss05, ss00)

	mI01(
		mI01(ss00))

	mI02(
		mI01(ss00),
		mI02(ss00, ss01))

	mI03(
		mI01(ss00),
		mI02(ss00, ss01),
		mI03(ss00, ss01, ss00))

	mI04(
		mI01(ss00),
		mI02(ss00, ss01),
		mI03(ss00, ss01, ss00),
		mI04(ss00, ss01, ss00, ss03))

	if (y262) {

	mI05(
		mI01(ss00),
		mI02(ss00, ss01),
		mI03(ss00, ss01, ss00),
		mI04(ss00, ss01, ss00, ss03),
		mI05(ss00, ss01, ss00, ss03, ss00))

	mI06(
		mI01(ss00),
		mI02(ss00, ss01),
		mI03(ss00, ss01, ss00),
		mI04(ss00, ss01, ss00, ss03),
		mI05(ss00, ss01, ss00, ss03, ss00),
		mI06(ss00, ss01, ss00, ss03, ss00, ss05))
	mI07(
		mI01(ss00),
		mI02(ss00, ss01),
		mI03(ss00, ss01, ss00),
		mI04(ss00, ss01, ss00, ss03),
		mI05(ss00, ss01, ss00, ss03, ss00),
		mI06(ss00, ss01, ss00, ss03, ss00, ss05),
		mI07(ss00, ss01, ss00, ss03, ss00, ss05, ss00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * String (applicable to Implicit Conversion Rules)
	 */
	Store(3, cmd0)
	Store(s001, ss00)


	/*
	 * Modification 0:
	 */

	mI01(ss00)
	mI02(ss00, ss00)
	mI03(ss00, ss00, ss00)
	mI04(ss00, ss00, ss00, ss00)
	mI05(ss00, ss00, ss00, ss00, ss00)
	mI06(ss00, ss00, ss00, ss00, ss00, ss00)
	mI07(ss00, ss00, ss00, ss00, ss00, ss00, ss00)

	mI01(
		mI01(ss00))

	mI02(
		mI01(ss00),
		mI02(ss00, ss00))

	mI03(
		mI01(ss00),
		mI02(ss00, ss00),
		mI03(ss00, ss00, ss00))

	mI04(
		mI01(ss00),
		mI02(ss00, ss00),
		mI03(ss00, ss00, ss00),
		mI04(ss00, ss00, ss00, ss00))

	if (y262) {

	mI05(
		mI01(ss00),
		mI02(ss00, ss00),
		mI03(ss00, ss00, ss00),
		mI04(ss00, ss00, ss00, ss00),
		mI05(ss00, ss00, ss00, ss00, ss00))

	mI06(
		mI01(ss00),
		mI02(ss00, ss00),
		mI03(ss00, ss00, ss00),
		mI04(ss00, ss00, ss00, ss00),
		mI05(ss00, ss00, ss00, ss00, ss00),
		mI06(ss00, ss00, ss00, ss00, ss00, ss00))
	mI07(
		mI01(ss00),
		mI02(ss00, ss00),
		mI03(ss00, ss00, ss00),
		mI04(ss00, ss00, ss00, ss00),
		mI05(ss00, ss00, ss00, ss00, ss00),
		mI06(ss00, ss00, ss00, ss00, ss00, ss00),
		mI07(ss00, ss00, ss00, ss00, ss00, ss00, ss00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 1:
	 *
	 * Some params are intermediately stored to Locals
	 */

	Store(ss00, Local1)
	Store(ss00, Local3)
	Store(ss00, Local5)

	mI01(ss00)
	mI02(ss00, Local1)
	mI03(ss00, Local1, ss00)
	mI04(ss00, Local1, ss00, Local3)
	mI05(ss00, Local1, ss00, Local3, ss00)
	mI06(ss00, Local1, ss00, Local3, ss00, Local5)
	mI07(ss00, Local1, ss00, Local3, ss00, Local5, ss00)

	mI01(
		mI01(ss00))

	mI02(
		mI01(ss00),
		mI02(ss00, Local1))

	mI03(
		mI01(ss00),
		mI02(ss00, Local1),
		mI03(ss00, Local1, ss00))

	mI04(
		mI01(ss00),
		mI02(ss00, Local1),
		mI03(ss00, Local1, ss00),
		mI04(ss00, Local1, ss00, Local3))

	if (y262) {

	mI05(
		mI01(ss00),
		mI02(ss00, Local1),
		mI03(ss00, Local1, ss00),
		mI04(ss00, Local1, ss00, Local3),
		mI05(ss00, Local1, ss00, Local3, ss00))

	mI06(
		mI01(ss00),
		mI02(ss00, Local1),
		mI03(ss00, Local1, ss00),
		mI04(ss00, Local1, ss00, Local3),
		mI05(ss00, Local1, ss00, Local3, ss00),
		mI06(ss00, Local1, ss00, Local3, ss00, Local5))
	mI07(
		mI01(ss00),
		mI02(ss00, Local1),
		mI03(ss00, Local1, ss00),
		mI04(ss00, Local1, ss00, Local3),
		mI05(ss00, Local1, ss00, Local3, ss00),
		mI06(ss00, Local1, ss00, Local3, ss00, Local5),
		mI07(ss00, Local1, ss00, Local3, ss00, Local5, ss00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 2:
	 *
	 * Some params are intermediately stored to Args (effectively local)
	 */

	Store(ss00, Arg1)
	Store(ss00, Arg3)
	Store(ss00, Arg5)

	mI01(ss00)
	mI02(ss00, Arg1)
	mI03(ss00, Arg1, ss00)
	mI04(ss00, Arg1, ss00, Arg3)
	mI05(ss00, Arg1, ss00, Arg3, ss00)
	mI06(ss00, Arg1, ss00, Arg3, ss00, Arg5)
	mI07(ss00, Arg1, ss00, Arg3, ss00, Arg5, ss00)

	mI01(
		mI01(ss00))

	mI02(
		mI01(ss00),
		mI02(ss00, Arg1))

	mI03(
		mI01(ss00),
		mI02(ss00, Arg1),
		mI03(ss00, Arg1, ss00))

	mI04(
		mI01(ss00),
		mI02(ss00, Arg1),
		mI03(ss00, Arg1, ss00),
		mI04(ss00, Arg1, ss00, Arg3))

	if (y262) {

	mI05(
		mI01(ss00),
		mI02(ss00, Arg1),
		mI03(ss00, Arg1, ss00),
		mI04(ss00, Arg1, ss00, Arg3),
		mI05(ss00, Arg1, ss00, Arg3, ss00))

	mI06(
		mI01(ss00),
		mI02(ss00, Arg1),
		mI03(ss00, Arg1, ss00),
		mI04(ss00, Arg1, ss00, Arg3),
		mI05(ss00, Arg1, ss00, Arg3, ss00),
		mI06(ss00, Arg1, ss00, Arg3, ss00, Arg5))
	mI07(
		mI01(ss00),
		mI02(ss00, Arg1),
		mI03(ss00, Arg1, ss00),
		mI04(ss00, Arg1, ss00, Arg3),
		mI05(ss00, Arg1, ss00, Arg3, ss00),
		mI06(ss00, Arg1, ss00, Arg3, ss00, Arg5),
		mI07(ss00, Arg1, ss00, Arg3, ss00, Arg5, ss00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 3:
	 *
	 * Some params are intermediately stored to Named
	 */

	Store(ss00, ss01)
	Store(ss00, ss03)
	Store(ss00, ss05)

	mI01(ss00)
	mI02(ss00, ss01)
	mI03(ss00, ss01, ss00)
	mI04(ss00, ss01, ss00, ss03)
	mI05(ss00, ss01, ss00, ss03, ss00)
	mI06(ss00, ss01, ss00, ss03, ss00, ss05)
	mI07(ss00, ss01, ss00, ss03, ss00, ss05, ss00)

	mI01(
		mI01(ss00))

	mI02(
		mI01(ss00),
		mI02(ss00, ss01))

	mI03(
		mI01(ss00),
		mI02(ss00, ss01),
		mI03(ss00, ss01, ss00))

	mI04(
		mI01(ss00),
		mI02(ss00, ss01),
		mI03(ss00, ss01, ss00),
		mI04(ss00, ss01, ss00, ss03))

	if (y262) {

	mI05(
		mI01(ss00),
		mI02(ss00, ss01),
		mI03(ss00, ss01, ss00),
		mI04(ss00, ss01, ss00, ss03),
		mI05(ss00, ss01, ss00, ss03, ss00))

	mI06(
		mI01(ss00),
		mI02(ss00, ss01),
		mI03(ss00, ss01, ss00),
		mI04(ss00, ss01, ss00, ss03),
		mI05(ss00, ss01, ss00, ss03, ss00),
		mI06(ss00, ss01, ss00, ss03, ss00, ss05))
	mI07(
		mI01(ss00),
		mI02(ss00, ss01),
		mI03(ss00, ss01, ss00),
		mI04(ss00, ss01, ss00, ss03),
		mI05(ss00, ss01, ss00, ss03, ss00),
		mI06(ss00, ss01, ss00, ss03, ss00, ss05),
		mI07(ss00, ss01, ss00, ss03, ss00, ss05, ss00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Buffer
	 */
	Name(bb00, Buffer(5) {})
	Name(bb01, Buffer(5) {})
	Name(bb03, Buffer(5) {})
	Name(bb05, Buffer(5) {})

	Store(4, cmd0)
	Store(b000, bb00)


	/*
	 * Modification 0:
	 */

	mI01(bb00)
	mI02(bb00, bb00)
	mI03(bb00, bb00, bb00)
	mI04(bb00, bb00, bb00, bb00)
	mI05(bb00, bb00, bb00, bb00, bb00)
	mI06(bb00, bb00, bb00, bb00, bb00, bb00)
	mI07(bb00, bb00, bb00, bb00, bb00, bb00, bb00)

	mI01(
		mI01(bb00))

	mI02(
		mI01(bb00),
		mI02(bb00, bb00))

	mI03(
		mI01(bb00),
		mI02(bb00, bb00),
		mI03(bb00, bb00, bb00))

	mI04(
		mI01(bb00),
		mI02(bb00, bb00),
		mI03(bb00, bb00, bb00),
		mI04(bb00, bb00, bb00, bb00))

	if (y262) {

	mI05(
		mI01(bb00),
		mI02(bb00, bb00),
		mI03(bb00, bb00, bb00),
		mI04(bb00, bb00, bb00, bb00),
		mI05(bb00, bb00, bb00, bb00, bb00))

	mI06(
		mI01(bb00),
		mI02(bb00, bb00),
		mI03(bb00, bb00, bb00),
		mI04(bb00, bb00, bb00, bb00),
		mI05(bb00, bb00, bb00, bb00, bb00),
		mI06(bb00, bb00, bb00, bb00, bb00, bb00))
	mI07(
		mI01(bb00),
		mI02(bb00, bb00),
		mI03(bb00, bb00, bb00),
		mI04(bb00, bb00, bb00, bb00),
		mI05(bb00, bb00, bb00, bb00, bb00),
		mI06(bb00, bb00, bb00, bb00, bb00, bb00),
		mI07(bb00, bb00, bb00, bb00, bb00, bb00, bb00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 1:
	 *
	 * Some params are intermediately stored to Locals
	 */

	Store(bb00, Local1)
	Store(bb00, Local3)
	Store(bb00, Local5)

	mI01(bb00)
	mI02(bb00, Local1)
	mI03(bb00, Local1, bb00)
	mI04(bb00, Local1, bb00, Local3)
	mI05(bb00, Local1, bb00, Local3, bb00)
	mI06(bb00, Local1, bb00, Local3, bb00, Local5)
	mI07(bb00, Local1, bb00, Local3, bb00, Local5, bb00)

	mI01(
		mI01(bb00))

	mI02(
		mI01(bb00),
		mI02(bb00, Local1))

	mI03(
		mI01(bb00),
		mI02(bb00, Local1),
		mI03(bb00, Local1, bb00))

	mI04(
		mI01(bb00),
		mI02(bb00, Local1),
		mI03(bb00, Local1, bb00),
		mI04(bb00, Local1, bb00, Local3))

	if (y262) {

	mI05(
		mI01(bb00),
		mI02(bb00, Local1),
		mI03(bb00, Local1, bb00),
		mI04(bb00, Local1, bb00, Local3),
		mI05(bb00, Local1, bb00, Local3, bb00))

	mI06(
		mI01(bb00),
		mI02(bb00, Local1),
		mI03(bb00, Local1, bb00),
		mI04(bb00, Local1, bb00, Local3),
		mI05(bb00, Local1, bb00, Local3, bb00),
		mI06(bb00, Local1, bb00, Local3, bb00, Local5))
	mI07(
		mI01(bb00),
		mI02(bb00, Local1),
		mI03(bb00, Local1, bb00),
		mI04(bb00, Local1, bb00, Local3),
		mI05(bb00, Local1, bb00, Local3, bb00),
		mI06(bb00, Local1, bb00, Local3, bb00, Local5),
		mI07(bb00, Local1, bb00, Local3, bb00, Local5, bb00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 2:
	 *
	 * Some params are intermediately stored to Args (effectively local)
	 */

	Store(bb00, Arg1)
	Store(bb00, Arg3)
	Store(bb00, Arg5)

	mI01(bb00)
	mI02(bb00, Arg1)
	mI03(bb00, Arg1, bb00)
	mI04(bb00, Arg1, bb00, Arg3)
	mI05(bb00, Arg1, bb00, Arg3, bb00)
	mI06(bb00, Arg1, bb00, Arg3, bb00, Arg5)
	mI07(bb00, Arg1, bb00, Arg3, bb00, Arg5, bb00)

	mI01(
		mI01(bb00))

	mI02(
		mI01(bb00),
		mI02(bb00, Arg1))

	mI03(
		mI01(bb00),
		mI02(bb00, Arg1),
		mI03(bb00, Arg1, bb00))

	mI04(
		mI01(bb00),
		mI02(bb00, Arg1),
		mI03(bb00, Arg1, bb00),
		mI04(bb00, Arg1, bb00, Arg3))

	if (y262) {

	mI05(
		mI01(bb00),
		mI02(bb00, Arg1),
		mI03(bb00, Arg1, bb00),
		mI04(bb00, Arg1, bb00, Arg3),
		mI05(bb00, Arg1, bb00, Arg3, bb00))

	mI06(
		mI01(bb00),
		mI02(bb00, Arg1),
		mI03(bb00, Arg1, bb00),
		mI04(bb00, Arg1, bb00, Arg3),
		mI05(bb00, Arg1, bb00, Arg3, bb00),
		mI06(bb00, Arg1, bb00, Arg3, bb00, Arg5))
	mI07(
		mI01(bb00),
		mI02(bb00, Arg1),
		mI03(bb00, Arg1, bb00),
		mI04(bb00, Arg1, bb00, Arg3),
		mI05(bb00, Arg1, bb00, Arg3, bb00),
		mI06(bb00, Arg1, bb00, Arg3, bb00, Arg5),
		mI07(bb00, Arg1, bb00, Arg3, bb00, Arg5, bb00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 3:
	 *
	 * Some params are intermediately stored to Named
	 */

	Store(bb00, bb01)
	Store(bb00, bb03)
	Store(bb00, bb05)

	mI01(bb00)
	mI02(bb00, bb01)
	mI03(bb00, bb01, bb00)
	mI04(bb00, bb01, bb00, bb03)
	mI05(bb00, bb01, bb00, bb03, bb00)
	mI06(bb00, bb01, bb00, bb03, bb00, bb05)
	mI07(bb00, bb01, bb00, bb03, bb00, bb05, bb00)

	mI01(
		mI01(bb00))

	mI02(
		mI01(bb00),
		mI02(bb00, bb01))

	mI03(
		mI01(bb00),
		mI02(bb00, bb01),
		mI03(bb00, bb01, bb00))

	mI04(
		mI01(bb00),
		mI02(bb00, bb01),
		mI03(bb00, bb01, bb00),
		mI04(bb00, bb01, bb00, bb03))

	if (y262) {

	mI05(
		mI01(bb00),
		mI02(bb00, bb01),
		mI03(bb00, bb01, bb00),
		mI04(bb00, bb01, bb00, bb03),
		mI05(bb00, bb01, bb00, bb03, bb00))

	mI06(
		mI01(bb00),
		mI02(bb00, bb01),
		mI03(bb00, bb01, bb00),
		mI04(bb00, bb01, bb00, bb03),
		mI05(bb00, bb01, bb00, bb03, bb00),
		mI06(bb00, bb01, bb00, bb03, bb00, bb05))
	mI07(
		mI01(bb00),
		mI02(bb00, bb01),
		mI03(bb00, bb01, bb00),
		mI04(bb00, bb01, bb00, bb03),
		mI05(bb00, bb01, bb00, bb03, bb00),
		mI06(bb00, bb01, bb00, bb03, bb00, bb05),
		mI07(bb00, bb01, bb00, bb03, bb00, bb05, bb00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Package
	 */
	Name(pp00, Package() {0xabcd0901, 0xabcd0902, 0xabcd0903})
	Name(pp01, Package(3) {})
	Name(pp03, Package(3) {})
	Name(pp05, Package(3) {})

	Store(5, cmd0)
	if (chk0) {
		Store(p000, pp00)
	}


	/*
	 * Modification 0:
	 */

	mI01(pp00)
	mI02(pp00, pp00)
	mI03(pp00, pp00, pp00)
	mI04(pp00, pp00, pp00, pp00)
	mI05(pp00, pp00, pp00, pp00, pp00)
	mI06(pp00, pp00, pp00, pp00, pp00, pp00)
	mI07(pp00, pp00, pp00, pp00, pp00, pp00, pp00)

	mI01(
		mI01(pp00))

	mI02(
		mI01(pp00),
		mI02(pp00, pp00))

	mI03(
		mI01(pp00),
		mI02(pp00, pp00),
		mI03(pp00, pp00, pp00))

	mI04(
		mI01(pp00),
		mI02(pp00, pp00),
		mI03(pp00, pp00, pp00),
		mI04(pp00, pp00, pp00, pp00))

	if (y262) {

	mI05(
		mI01(pp00),
		mI02(pp00, pp00),
		mI03(pp00, pp00, pp00),
		mI04(pp00, pp00, pp00, pp00),
		mI05(pp00, pp00, pp00, pp00, pp00))

	mI06(
		mI01(pp00),
		mI02(pp00, pp00),
		mI03(pp00, pp00, pp00),
		mI04(pp00, pp00, pp00, pp00),
		mI05(pp00, pp00, pp00, pp00, pp00),
		mI06(pp00, pp00, pp00, pp00, pp00, pp00))
	mI07(
		mI01(pp00),
		mI02(pp00, pp00),
		mI03(pp00, pp00, pp00),
		mI04(pp00, pp00, pp00, pp00),
		mI05(pp00, pp00, pp00, pp00, pp00),
		mI06(pp00, pp00, pp00, pp00, pp00, pp00),
		mI07(pp00, pp00, pp00, pp00, pp00, pp00, pp00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 1:
	 *
	 * Some params are intermediately stored to Locals
	 */

	Store(pp00, Local1)
	Store(pp00, Local3)
	Store(pp00, Local5)

	mI01(pp00)
	mI02(pp00, Local1)
	mI03(pp00, Local1, pp00)
	mI04(pp00, Local1, pp00, Local3)
	mI05(pp00, Local1, pp00, Local3, pp00)
	mI06(pp00, Local1, pp00, Local3, pp00, Local5)
	mI07(pp00, Local1, pp00, Local3, pp00, Local5, pp00)

	mI01(
		mI01(pp00))

	mI02(
		mI01(pp00),
		mI02(pp00, Local1))

	mI03(
		mI01(pp00),
		mI02(pp00, Local1),
		mI03(pp00, Local1, pp00))

	mI04(
		mI01(pp00),
		mI02(pp00, Local1),
		mI03(pp00, Local1, pp00),
		mI04(pp00, Local1, pp00, Local3))

	if (y262) {

	mI05(
		mI01(pp00),
		mI02(pp00, Local1),
		mI03(pp00, Local1, pp00),
		mI04(pp00, Local1, pp00, Local3),
		mI05(pp00, Local1, pp00, Local3, pp00))

	mI06(
		mI01(pp00),
		mI02(pp00, Local1),
		mI03(pp00, Local1, pp00),
		mI04(pp00, Local1, pp00, Local3),
		mI05(pp00, Local1, pp00, Local3, pp00),
		mI06(pp00, Local1, pp00, Local3, pp00, Local5))
	mI07(
		mI01(pp00),
		mI02(pp00, Local1),
		mI03(pp00, Local1, pp00),
		mI04(pp00, Local1, pp00, Local3),
		mI05(pp00, Local1, pp00, Local3, pp00),
		mI06(pp00, Local1, pp00, Local3, pp00, Local5),
		mI07(pp00, Local1, pp00, Local3, pp00, Local5, pp00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 2:
	 *
	 * Some params are intermediately stored to Args (effectively local)
	 */

	Store(pp00, Arg1)
	Store(pp00, Arg3)
	Store(pp00, Arg5)

	mI01(pp00)
	mI02(pp00, Arg1)
	mI03(pp00, Arg1, pp00)
	mI04(pp00, Arg1, pp00, Arg3)
	mI05(pp00, Arg1, pp00, Arg3, pp00)
	mI06(pp00, Arg1, pp00, Arg3, pp00, Arg5)
	mI07(pp00, Arg1, pp00, Arg3, pp00, Arg5, pp00)

	mI01(
		mI01(pp00))

	mI02(
		mI01(pp00),
		mI02(pp00, Arg1))

	mI03(
		mI01(pp00),
		mI02(pp00, Arg1),
		mI03(pp00, Arg1, pp00))

	mI04(
		mI01(pp00),
		mI02(pp00, Arg1),
		mI03(pp00, Arg1, pp00),
		mI04(pp00, Arg1, pp00, Arg3))

	if (y262) {

	mI05(
		mI01(pp00),
		mI02(pp00, Arg1),
		mI03(pp00, Arg1, pp00),
		mI04(pp00, Arg1, pp00, Arg3),
		mI05(pp00, Arg1, pp00, Arg3, pp00))

	mI06(
		mI01(pp00),
		mI02(pp00, Arg1),
		mI03(pp00, Arg1, pp00),
		mI04(pp00, Arg1, pp00, Arg3),
		mI05(pp00, Arg1, pp00, Arg3, pp00),
		mI06(pp00, Arg1, pp00, Arg3, pp00, Arg5))
	mI07(
		mI01(pp00),
		mI02(pp00, Arg1),
		mI03(pp00, Arg1, pp00),
		mI04(pp00, Arg1, pp00, Arg3),
		mI05(pp00, Arg1, pp00, Arg3, pp00),
		mI06(pp00, Arg1, pp00, Arg3, pp00, Arg5),
		mI07(pp00, Arg1, pp00, Arg3, pp00, Arg5, pp00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	if (chk0) {

	/*
	 * Modification 3:
	 *
	 * Some params are intermediately stored to Named
	 */

	Store(pp00, pp01)
	Store(pp00, pp03)
	Store(pp00, pp05)

	mI01(pp00)
	mI02(pp00, pp01)

	mI03(pp00, pp01, pp00)
	mI04(pp00, pp01, pp00, pp03)
	mI05(pp00, pp01, pp00, pp03, pp00)
	mI06(pp00, pp01, pp00, pp03, pp00, pp05)
	mI07(pp00, pp01, pp00, pp03, pp00, pp05, pp00)

	mI01(
		mI01(pp00))

	mI02(
		mI01(pp00),
		mI02(pp00, pp01))

	mI03(
		mI01(pp00),
		mI02(pp00, pp01),
		mI03(pp00, pp01, pp00))

	mI04(
		mI01(pp00),
		mI02(pp00, pp01),
		mI03(pp00, pp01, pp00),
		mI04(pp00, pp01, pp00, pp03))

	if (y262) {

	mI05(
		mI01(pp00),
		mI02(pp00, pp01),
		mI03(pp00, pp01, pp00),
		mI04(pp00, pp01, pp00, pp03),
		mI05(pp00, pp01, pp00, pp03, pp00))

	mI06(
		mI01(pp00),
		mI02(pp00, pp01),
		mI03(pp00, pp01, pp00),
		mI04(pp00, pp01, pp00, pp03),
		mI05(pp00, pp01, pp00, pp03, pp00),
		mI06(pp00, pp01, pp00, pp03, pp00, pp05))
	mI07(
		mI01(pp00),
		mI02(pp00, pp01),
		mI03(pp00, pp01, pp00),
		mI04(pp00, pp01, pp00, pp03),
		mI05(pp00, pp01, pp00, pp03, pp00),
		mI06(pp00, pp01, pp00, pp03, pp00, pp05),
		mI07(pp00, pp01, pp00, pp03, pp00, pp05, pp00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	} // if (chk0)
}

Method(in41, 7, Serialized)
{
	Name(ts, "in41")

	Event(e000)
	Mutex(mx00, 0)
	Method(mmm0,, Serialized) {
		Name(im00, 0xabcd0004)
		Name(sm00, "qwertyui")
		// Return ( "qwertyui" )
	}
	Method(mmm1,, Serialized) {
		Name(im00, 0xabcd0004)
		Name(sm00, "qwertyui")
		// Return ( 0xabcd0004 )
		Return ( "qwertyui" )
	}
	Device(d000) { Name(id00, 0xabcd0005) }
	ThermalZone(tz00) { Name(itz0, 0xabcd0006) }
	Processor(pr00, 0, 0xFFFFFFFF, 0) { Name(ipr0, 0xabcd0007) }
	PowerResource(pw00, 1, 0) { Name(ipw0, 0xabcd0008) }
	OperationRegion(r000, SystemMemory, 0x000, 0x080)

	Name(b001, Buffer() {0xa0,0xa1,0xa2,0xa3,0xa4})
	CreateField(b001, 0, 32, bf00)

	OperationRegion(r001, SystemMemory, 0x080, 0x080)
	Field(r001, ByteAcc, NoLock, Preserve) {f000,32, f001,32, f002,32, f003,32}
	BankField(r001, f001, 0, ByteAcc, NoLock, Preserve) {bnk0,32}
	IndexField(f002, f003, ByteAcc, NoLock, Preserve) {if00,32, if01,32}


	/*
	 * Field
	 */
	OperationRegion(r002, SystemMemory, 0x100, 0x080)
	Field(r002, ByteAcc, NoLock, Preserve) {ff00,32, ff01,32, ff03,32, ff05,32}

	Store(6, cmd0)
	Store(0xabcd0a00, f000)
	Store(f000, ff00)


	/*
	 * Modification 0:
	 */

	mI01(ff00)
	mI02(ff00, ff00)
	mI03(ff00, ff00, ff00)
	mI04(ff00, ff00, ff00, ff00)
	mI05(ff00, ff00, ff00, ff00, ff00)
	mI06(ff00, ff00, ff00, ff00, ff00, ff00)
	mI07(ff00, ff00, ff00, ff00, ff00, ff00, ff00)

	mI01(
		mI01(ff00))

	mI02(
		mI01(ff00),
		mI02(ff00, ff00))

	mI03(
		mI01(ff00),
		mI02(ff00, ff00),
		mI03(ff00, ff00, ff00))

	mI04(
		mI01(ff00),
		mI02(ff00, ff00),
		mI03(ff00, ff00, ff00),
		mI04(ff00, ff00, ff00, ff00))

	if (y262) {

	mI05(
		mI01(ff00),
		mI02(ff00, ff00),
		mI03(ff00, ff00, ff00),
		mI04(ff00, ff00, ff00, ff00),
		mI05(ff00, ff00, ff00, ff00, ff00))

	mI06(
		mI01(ff00),
		mI02(ff00, ff00),
		mI03(ff00, ff00, ff00),
		mI04(ff00, ff00, ff00, ff00),
		mI05(ff00, ff00, ff00, ff00, ff00),
		mI06(ff00, ff00, ff00, ff00, ff00, ff00))

	// if (chk0) {
	// qqq: This breaks Field:

	mI07(
		mI01(ff00),
		mI02(ff00, ff00),
		mI03(ff00, ff00, ff00),
		mI04(ff00, ff00, ff00, ff00),
		mI05(ff00, ff00, ff00, ff00, ff00),
		mI06(ff00, ff00, ff00, ff00, ff00, ff00),
		mI07(ff00, ff00, ff00, ff00, ff00, ff00, ff00))
	// }

	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 1:
	 *
	 * Some params are intermediately stored to Locals
	 */

	Store(ff00, Local1)
	Store(ff00, Local3)
	Store(ff00, Local5)

	mI01(ff00)
	mI02(ff00, Local1)
	mI03(ff00, Local1, ff00)
	mI04(ff00, Local1, ff00, Local3)
	mI05(ff00, Local1, ff00, Local3, ff00)
	mI06(ff00, Local1, ff00, Local3, ff00, Local5)
	mI07(ff00, Local1, ff00, Local3, ff00, Local5, ff00)

	mI01(
		mI01(ff00))

	mI02(
		mI01(ff00),
		mI02(ff00, Local1))

	mI03(
		mI01(ff00),
		mI02(ff00, Local1),
		mI03(ff00, Local1, ff00))

	mI04(
		mI01(ff00),
		mI02(ff00, Local1),
		mI03(ff00, Local1, ff00),
		mI04(ff00, Local1, ff00, Local3))

	if (y262) {

	mI05(
		mI01(ff00),
		mI02(ff00, Local1),
		mI03(ff00, Local1, ff00),
		mI04(ff00, Local1, ff00, Local3),
		mI05(ff00, Local1, ff00, Local3, ff00))

	mI06(
		mI01(ff00),
		mI02(ff00, Local1),
		mI03(ff00, Local1, ff00),
		mI04(ff00, Local1, ff00, Local3),
		mI05(ff00, Local1, ff00, Local3, ff00),
		mI06(ff00, Local1, ff00, Local3, ff00, Local5))

	// if (chk0) { // qqq: This breaks Field:
	mI07(
		mI01(ff00),
		mI02(ff00, Local1),
		mI03(ff00, Local1, ff00),
		mI04(ff00, Local1, ff00, Local3),
		mI05(ff00, Local1, ff00, Local3, ff00),
		mI06(ff00, Local1, ff00, Local3, ff00, Local5),
		mI07(ff00, Local1, ff00, Local3, ff00, Local5, ff00))
	// }

	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 2:
	 *
	 * Some params are intermediately stored to Args (effectively local)
	 */

	Store(ff00, Arg1)
	Store(ff00, Arg3)
	Store(ff00, Arg5)

	mI01(ff00)
	mI02(ff00, Arg1)
	mI03(ff00, Arg1, ff00)
	mI04(ff00, Arg1, ff00, Arg3)
	mI05(ff00, Arg1, ff00, Arg3, ff00)
	mI06(ff00, Arg1, ff00, Arg3, ff00, Arg5)
	mI07(ff00, Arg1, ff00, Arg3, ff00, Arg5, ff00)

	mI01(
		mI01(ff00))

	mI02(
		mI01(ff00),
		mI02(ff00, Arg1))

	mI03(
		mI01(ff00),
		mI02(ff00, Arg1),
		mI03(ff00, Arg1, ff00))

	mI04(
		mI01(ff00),
		mI02(ff00, Arg1),
		mI03(ff00, Arg1, ff00),
		mI04(ff00, Arg1, ff00, Arg3))

	if (y262) {

	mI05(
		mI01(ff00),
		mI02(ff00, Arg1),
		mI03(ff00, Arg1, ff00),
		mI04(ff00, Arg1, ff00, Arg3),
		mI05(ff00, Arg1, ff00, Arg3, ff00))

	mI06(
		mI01(ff00),
		mI02(ff00, Arg1),
		mI03(ff00, Arg1, ff00),
		mI04(ff00, Arg1, ff00, Arg3),
		mI05(ff00, Arg1, ff00, Arg3, ff00),
		mI06(ff00, Arg1, ff00, Arg3, ff00, Arg5))

	// if (chk0) { // qqq: This breaks Field:
	mI07(
		mI01(ff00),
		mI02(ff00, Arg1),
		mI03(ff00, Arg1, ff00),
		mI04(ff00, Arg1, ff00, Arg3),
		mI05(ff00, Arg1, ff00, Arg3, ff00),
		mI06(ff00, Arg1, ff00, Arg3, ff00, Arg5),
		mI07(ff00, Arg1, ff00, Arg3, ff00, Arg5, ff00))
	// }

	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 3:
	 *
	 * Some params are intermediately stored to Named
	 */

	Store(ff00, ff01)
	Store(ff00, ff03)
	Store(ff00, ff05)

	mI01(ff00)
	mI02(ff00, ff01)
	mI03(ff00, ff01, ff00)
	mI04(ff00, ff01, ff00, ff03)
	mI05(ff00, ff01, ff00, ff03, ff00)
	mI06(ff00, ff01, ff00, ff03, ff00, ff05)
	mI07(ff00, ff01, ff00, ff03, ff00, ff05, ff00)

	mI01(
		mI01(ff00))

	mI02(
		mI01(ff00),
		mI02(ff00, ff01))

	mI03(
		mI01(ff00),
		mI02(ff00, ff01),
		mI03(ff00, ff01, ff00))

	mI04(
		mI01(ff00),
		mI02(ff00, ff01),
		mI03(ff00, ff01, ff00),
		mI04(ff00, ff01, ff00, ff03))

	if (y262) {

	mI05(
		mI01(ff00),
		mI02(ff00, ff01),
		mI03(ff00, ff01, ff00),
		mI04(ff00, ff01, ff00, ff03),
		mI05(ff00, ff01, ff00, ff03, ff00))

	mI06(
		mI01(ff00),
		mI02(ff00, ff01),
		mI03(ff00, ff01, ff00),
		mI04(ff00, ff01, ff00, ff03),
		mI05(ff00, ff01, ff00, ff03, ff00),
		mI06(ff00, ff01, ff00, ff03, ff00, ff05))

	// if (chk0) { // qqq: This breaks Field:
	mI07(
		mI01(ff00),
		mI02(ff00, ff01),
		mI03(ff00, ff01, ff00),
		mI04(ff00, ff01, ff00, ff03),
		mI05(ff00, ff01, ff00, ff03, ff00),
		mI06(ff00, ff01, ff00, ff03, ff00, ff05),
		mI07(ff00, ff01, ff00, ff03, ff00, ff05, ff00))
	// }
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Index Field
	 */
	OperationRegion(r003, SystemMemory, 0x180, 0x080)
	Field(r003, ByteAcc, NoLock, Preserve) {f004,32, f005,32}
	IndexField(f004, f005, ByteAcc, NoLock, Preserve) {if02,32}

	Store(14, cmd0)
	Store(0xabcd0b04, if00)
	Store(if00, if02)


	/*
	 * Modification 0:
	 */

	mI01(if02)
	mI02(if02, if02)
	mI03(if02, if02, if02)
	mI04(if02, if02, if02, if02)
	mI05(if02, if02, if02, if02, if02)
	mI06(if02, if02, if02, if02, if02, if02)
	mI07(if02, if02, if02, if02, if02, if02, if02)

	// if (chk0) {

	mI01(
		mI01(if02))

	mI02(
		mI01(if02),
		mI02(if02, if02))

	mI03(
		mI01(if02),
		mI02(if02, if02),
		mI03(if02, if02, if02))

	mI04(
		mI01(if02),
		mI02(if02, if02),
		mI03(if02, if02, if02),
		mI04(if02, if02, if02, if02))

	if (y262) {

	mI05(
		mI01(if02),
		mI02(if02, if02),
		mI03(if02, if02, if02),
		mI04(if02, if02, if02, if02),
		mI05(if02, if02, if02, if02, if02))

	mI06(
		mI01(if02),
		mI02(if02, if02),
		mI03(if02, if02, if02),
		mI04(if02, if02, if02, if02),
		mI05(if02, if02, if02, if02, if02),
		mI06(if02, if02, if02, if02, if02, if02))
	mI07(
		mI01(if02),
		mI02(if02, if02),
		mI03(if02, if02, if02),
		mI04(if02, if02, if02, if02),
		mI05(if02, if02, if02, if02, if02),
		mI06(if02, if02, if02, if02, if02, if02),
		mI07(if02, if02, if02, if02, if02, if02, if02))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 1:
	 *
	 * Some params are intermediately stored to Locals
	 */

	Store(if02, Local1)
	Store(if02, Local3)
	Store(if02, Local5)

	mI01(if02)
	mI02(if02, Local1)
	mI03(if02, Local1, if02)
	mI04(if02, Local1, if02, Local3)
	mI05(if02, Local1, if02, Local3, if02)
	mI06(if02, Local1, if02, Local3, if02, Local5)
	mI07(if02, Local1, if02, Local3, if02, Local5, if02)

	mI01(
		mI01(if02))

	mI02(
		mI01(if02),
		mI02(if02, Local1))

	mI03(
		mI01(if02),
		mI02(if02, Local1),
		mI03(if02, Local1, if02))

	mI04(
		mI01(if02),
		mI02(if02, Local1),
		mI03(if02, Local1, if02),
		mI04(if02, Local1, if02, Local3))

	if (y262) {

	mI05(
		mI01(if02),
		mI02(if02, Local1),
		mI03(if02, Local1, if02),
		mI04(if02, Local1, if02, Local3),
		mI05(if02, Local1, if02, Local3, if02))

	mI06(
		mI01(if02),
		mI02(if02, Local1),
		mI03(if02, Local1, if02),
		mI04(if02, Local1, if02, Local3),
		mI05(if02, Local1, if02, Local3, if02),
		mI06(if02, Local1, if02, Local3, if02, Local5))
	mI07(
		mI01(if02),
		mI02(if02, Local1),
		mI03(if02, Local1, if02),
		mI04(if02, Local1, if02, Local3),
		mI05(if02, Local1, if02, Local3, if02),
		mI06(if02, Local1, if02, Local3, if02, Local5),
		mI07(if02, Local1, if02, Local3, if02, Local5, if02))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 2:
	 *
	 * Some params are intermediately stored to Args (effectively local)
	 */

	Store(if02, Arg1)
	Store(if02, Arg3)
	Store(if02, Arg5)

	mI01(if02)
	mI02(if02, Arg1)
	mI03(if02, Arg1, if02)
	mI04(if02, Arg1, if02, Arg3)
	mI05(if02, Arg1, if02, Arg3, if02)
	mI06(if02, Arg1, if02, Arg3, if02, Arg5)
	mI07(if02, Arg1, if02, Arg3, if02, Arg5, if02)

	mI01(
		mI01(if02))

	mI02(
		mI01(if02),
		mI02(if02, Arg1))

	mI03(
		mI01(if02),
		mI02(if02, Arg1),
		mI03(if02, Arg1, if02))

	mI04(
		mI01(if02),
		mI02(if02, Arg1),
		mI03(if02, Arg1, if02),
		mI04(if02, Arg1, if02, Arg3))

	if (y262) {

	mI05(
		mI01(if02),
		mI02(if02, Arg1),
		mI03(if02, Arg1, if02),
		mI04(if02, Arg1, if02, Arg3),
		mI05(if02, Arg1, if02, Arg3, if02))

	mI06(
		mI01(if02),
		mI02(if02, Arg1),
		mI03(if02, Arg1, if02),
		mI04(if02, Arg1, if02, Arg3),
		mI05(if02, Arg1, if02, Arg3, if02),
		mI06(if02, Arg1, if02, Arg3, if02, Arg5))
	mI07(
		mI01(if02),
		mI02(if02, Arg1),
		mI03(if02, Arg1, if02),
		mI04(if02, Arg1, if02, Arg3),
		mI05(if02, Arg1, if02, Arg3, if02),
		mI06(if02, Arg1, if02, Arg3, if02, Arg5),
		mI07(if02, Arg1, if02, Arg3, if02, Arg5, if02))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 3:
	 *
	 * Some params are intermediately stored to Named
	 */

	Store(if02, ff01)
	Store(if02, ff03)
	Store(if02, ff05)

	mI01(if02)
	mI02(if02, ff01)
	mI03(if02, ff01, if02)
	mI04(if02, ff01, if02, ff03)
	mI05(if02, ff01, if02, ff03, if02)
	mI06(if02, ff01, if02, ff03, if02, ff05)
	mI07(if02, ff01, if02, ff03, if02, ff05, if02)

	mI01(
		mI01(if02))

	mI02(
		mI01(if02),
		mI02(if02, ff01))

	mI03(
		mI01(if02),
		mI02(if02, ff01),
		mI03(if02, ff01, if02))

	mI04(
		mI01(if02),
		mI02(if02, ff01),
		mI03(if02, ff01, if02),
		mI04(if02, ff01, if02, ff03))

	if (y262) {

	mI05(
		mI01(if02),
		mI02(if02, ff01),
		mI03(if02, ff01, if02),
		mI04(if02, ff01, if02, ff03),
		mI05(if02, ff01, if02, ff03, if02))

	mI06(
		mI01(if02),
		mI02(if02, ff01),
		mI03(if02, ff01, if02),
		mI04(if02, ff01, if02, ff03),
		mI05(if02, ff01, if02, ff03, if02),
		mI06(if02, ff01, if02, ff03, if02, ff05))
	mI07(
		mI01(if02),
		mI02(if02, ff01),
		mI03(if02, ff01, if02),
		mI04(if02, ff01, if02, ff03),
		mI05(if02, ff01, if02, ff03, if02),
		mI06(if02, ff01, if02, ff03, if02, ff05),
		mI07(if02, ff01, if02, ff03, if02, ff05, if02))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	// } // if (chk0)


	/*
	 * Bank Field
	 */
	OperationRegion(r004, SystemMemory, 0x200, 0x080)
	Field(r004, ByteAcc, NoLock, Preserve) {f006,32}
	BankField(r004, f006, 0, ByteAcc, NoLock, Preserve) {bnk1,32}

	Store(15, cmd0)
	Store(0xabcd0c07, bnk0)
	Store(bnk0, bnk1)


	/*
	 * Modification 0:
	 */

	mI01(bnk1)
	mI02(bnk1, bnk1)
	mI03(bnk1, bnk1, bnk1)
	mI04(bnk1, bnk1, bnk1, bnk1)

	// if (chk0) {

	mI05(bnk1, bnk1, bnk1, bnk1, bnk1)
	mI06(bnk1, bnk1, bnk1, bnk1, bnk1, bnk1)
	mI07(bnk1, bnk1, bnk1, bnk1, bnk1, bnk1, bnk1)

	mI01(
		mI01(bnk1))

	mI02(
		mI01(bnk1),
		mI02(bnk1, bnk1))

	mI03(
		mI01(bnk1),
		mI02(bnk1, bnk1),
		mI03(bnk1, bnk1, bnk1))

	mI04(
		mI01(bnk1),
		mI02(bnk1, bnk1),
		mI03(bnk1, bnk1, bnk1),
		mI04(bnk1, bnk1, bnk1, bnk1))

	if (y262) {

	mI05(
		mI01(bnk1),
		mI02(bnk1, bnk1),
		mI03(bnk1, bnk1, bnk1),
		mI04(bnk1, bnk1, bnk1, bnk1),
		mI05(bnk1, bnk1, bnk1, bnk1, bnk1))

	mI06(
		mI01(bnk1),
		mI02(bnk1, bnk1),
		mI03(bnk1, bnk1, bnk1),
		mI04(bnk1, bnk1, bnk1, bnk1),
		mI05(bnk1, bnk1, bnk1, bnk1, bnk1),
		mI06(bnk1, bnk1, bnk1, bnk1, bnk1, bnk1))
	mI07(
		mI01(bnk1),
		mI02(bnk1, bnk1),
		mI03(bnk1, bnk1, bnk1),
		mI04(bnk1, bnk1, bnk1, bnk1),
		mI05(bnk1, bnk1, bnk1, bnk1, bnk1),
		mI06(bnk1, bnk1, bnk1, bnk1, bnk1, bnk1),
		mI07(bnk1, bnk1, bnk1, bnk1, bnk1, bnk1, bnk1))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	// } // if (chk0)


	/*
	 * Modification 1:
	 *
	 * Some params are intermediately stored to Locals
	 */

	Store(bnk1, Local1)
	Store(bnk1, Local3)
	Store(bnk1, Local5)

	mI01(bnk1)
	mI02(bnk1, Local1)
	mI03(bnk1, Local1, bnk1)

	// if (chk0) {

	mI04(bnk1, Local1, bnk1, Local3)
	mI05(bnk1, Local1, bnk1, Local3, bnk1)
	mI06(bnk1, Local1, bnk1, Local3, bnk1, Local5)
	mI07(bnk1, Local1, bnk1, Local3, bnk1, Local5, bnk1)

	mI01(
		mI01(bnk1))

	mI02(
		mI01(bnk1),
		mI02(bnk1, Local1))

	mI03(
		mI01(bnk1),
		mI02(bnk1, Local1),
		mI03(bnk1, Local1, bnk1))

	mI04(
		mI01(bnk1),
		mI02(bnk1, Local1),
		mI03(bnk1, Local1, bnk1),
		mI04(bnk1, Local1, bnk1, Local3))

	if (y262) {

	mI05(
		mI01(bnk1),
		mI02(bnk1, Local1),
		mI03(bnk1, Local1, bnk1),
		mI04(bnk1, Local1, bnk1, Local3),
		mI05(bnk1, Local1, bnk1, Local3, bnk1))

	mI06(
		mI01(bnk1),
		mI02(bnk1, Local1),
		mI03(bnk1, Local1, bnk1),
		mI04(bnk1, Local1, bnk1, Local3),
		mI05(bnk1, Local1, bnk1, Local3, bnk1),
		mI06(bnk1, Local1, bnk1, Local3, bnk1, Local5))
	mI07(
		mI01(bnk1),
		mI02(bnk1, Local1),
		mI03(bnk1, Local1, bnk1),
		mI04(bnk1, Local1, bnk1, Local3),
		mI05(bnk1, Local1, bnk1, Local3, bnk1),
		mI06(bnk1, Local1, bnk1, Local3, bnk1, Local5),
		mI07(bnk1, Local1, bnk1, Local3, bnk1, Local5, bnk1))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	// } // if (chk0) {


	/*
	 * Modification 2:
	 *
	 * Some params are intermediately stored to Args (effectively local)
	 */

	Store(bnk1, Arg1)
	Store(bnk1, Arg3)
	Store(bnk1, Arg5)

	mI01(bnk1)
	mI02(bnk1, Arg1)
	mI03(bnk1, Arg1, bnk1)
	mI04(bnk1, Arg1, bnk1, Arg3)

	// if (chk0) {

	mI05(bnk1, Arg1, bnk1, Arg3, bnk1)
	mI06(bnk1, Arg1, bnk1, Arg3, bnk1, Arg5)
	mI07(bnk1, Arg1, bnk1, Arg3, bnk1, Arg5, bnk1)

	mI01(
		mI01(bnk1))

	mI02(
		mI01(bnk1),
		mI02(bnk1, Arg1))

	mI03(
		mI01(bnk1),
		mI02(bnk1, Arg1),
		mI03(bnk1, Arg1, bnk1))

	mI04(
		mI01(bnk1),
		mI02(bnk1, Arg1),
		mI03(bnk1, Arg1, bnk1),
		mI04(bnk1, Arg1, bnk1, Arg3))

	if (y262) {

	mI05(
		mI01(bnk1),
		mI02(bnk1, Arg1),
		mI03(bnk1, Arg1, bnk1),
		mI04(bnk1, Arg1, bnk1, Arg3),
		mI05(bnk1, Arg1, bnk1, Arg3, bnk1))

	mI06(
		mI01(bnk1),
		mI02(bnk1, Arg1),
		mI03(bnk1, Arg1, bnk1),
		mI04(bnk1, Arg1, bnk1, Arg3),
		mI05(bnk1, Arg1, bnk1, Arg3, bnk1),
		mI06(bnk1, Arg1, bnk1, Arg3, bnk1, Arg5))
	mI07(
		mI01(bnk1),
		mI02(bnk1, Arg1),
		mI03(bnk1, Arg1, bnk1),
		mI04(bnk1, Arg1, bnk1, Arg3),
		mI05(bnk1, Arg1, bnk1, Arg3, bnk1),
		mI06(bnk1, Arg1, bnk1, Arg3, bnk1, Arg5),
		mI07(bnk1, Arg1, bnk1, Arg3, bnk1, Arg5, bnk1))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	// } // if (chk0) {


	/*
	 * Modification 3:
	 *
	 * Some params are intermediately stored to Named
	 */

	Store(bnk1, ff01)
	Store(bnk1, ff03)
	Store(bnk1, ff05)

	mI01(bnk1)
	mI02(bnk1, ff01)
	mI03(bnk1, ff01, bnk1)
	mI04(bnk1, ff01, bnk1, ff03)

	// if (chk0) {

	mI05(bnk1, ff01, bnk1, ff03, bnk1)
	mI06(bnk1, ff01, bnk1, ff03, bnk1, ff05)
	mI07(bnk1, ff01, bnk1, ff03, bnk1, ff05, bnk1)

	mI01(
		mI01(bnk1))

	mI02(
		mI01(bnk1),
		mI02(bnk1, ff01))

	mI03(
		mI01(bnk1),
		mI02(bnk1, ff01),
		mI03(bnk1, ff01, bnk1))

	mI04(
		mI01(bnk1),
		mI02(bnk1, ff01),
		mI03(bnk1, ff01, bnk1),
		mI04(bnk1, ff01, bnk1, ff03))

	if (y262) {

	mI05(
		mI01(bnk1),
		mI02(bnk1, ff01),
		mI03(bnk1, ff01, bnk1),
		mI04(bnk1, ff01, bnk1, ff03),
		mI05(bnk1, ff01, bnk1, ff03, bnk1))

	mI06(
		mI01(bnk1),
		mI02(bnk1, ff01),
		mI03(bnk1, ff01, bnk1),
		mI04(bnk1, ff01, bnk1, ff03),
		mI05(bnk1, ff01, bnk1, ff03, bnk1),
		mI06(bnk1, ff01, bnk1, ff03, bnk1, ff05))
	mI07(
		mI01(bnk1),
		mI02(bnk1, ff01),
		mI03(bnk1, ff01, bnk1),
		mI04(bnk1, ff01, bnk1, ff03),
		mI05(bnk1, ff01, bnk1, ff03, bnk1),
		mI06(bnk1, ff01, bnk1, ff03, bnk1, ff05),
		mI07(bnk1, ff01, bnk1, ff03, bnk1, ff05, bnk1))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	// } // if (chk0) {


	/*
	 * Buffer Field
	 */
	Name(b002, Buffer() {0xa0,0xa1,0xa2,0xa3,0xa4})
	CreateField(b002, 0, 32, bf01)

	Store(16, cmd0)
	Store(0xabcd0d08, bf00)
	Store(bf00, bf01)


	/*
	 * Modification 0:
	 */

	mI01(bf01)
	mI02(bf01, bf01)
	mI03(bf01, bf01, bf01)
	mI04(bf01, bf01, bf01, bf01)
	mI05(bf01, bf01, bf01, bf01, bf01)
	mI06(bf01, bf01, bf01, bf01, bf01, bf01)
	mI07(bf01, bf01, bf01, bf01, bf01, bf01, bf01)

	mI01(
		mI01(bf01))

	mI02(
		mI01(bf01),
		mI02(bf01, bf01))

	mI03(
		mI01(bf01),
		mI02(bf01, bf01),
		mI03(bf01, bf01, bf01))

	mI04(
		mI01(bf01),
		mI02(bf01, bf01),
		mI03(bf01, bf01, bf01),
		mI04(bf01, bf01, bf01, bf01))

	if (y262) {

	mI05(
		mI01(bf01),
		mI02(bf01, bf01),
		mI03(bf01, bf01, bf01),
		mI04(bf01, bf01, bf01, bf01),
		mI05(bf01, bf01, bf01, bf01, bf01))

	mI06(
		mI01(bf01),
		mI02(bf01, bf01),
		mI03(bf01, bf01, bf01),
		mI04(bf01, bf01, bf01, bf01),
		mI05(bf01, bf01, bf01, bf01, bf01),
		mI06(bf01, bf01, bf01, bf01, bf01, bf01))
	mI07(
		mI01(bf01),
		mI02(bf01, bf01),
		mI03(bf01, bf01, bf01),
		mI04(bf01, bf01, bf01, bf01),
		mI05(bf01, bf01, bf01, bf01, bf01),
		mI06(bf01, bf01, bf01, bf01, bf01, bf01),
		mI07(bf01, bf01, bf01, bf01, bf01, bf01, bf01))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 1:
	 *
	 * Some params are intermediately stored to Locals
	 */

	Store(bf01, Local1)
	Store(bf01, Local3)
	Store(bf01, Local5)

	mI01(bf01)

	// if (chk0) {

	mI02(bf01, Local1)
	mI03(bf01, Local1, bf01)
	mI04(bf01, Local1, bf01, Local3)
	mI05(bf01, Local1, bf01, Local3, bf01)
	mI06(bf01, Local1, bf01, Local3, bf01, Local5)
	mI07(bf01, Local1, bf01, Local3, bf01, Local5, bf01)

	mI01(
		mI01(bf01))

	mI02(
		mI01(bf01),
		mI02(bf01, Local1))

	mI03(
		mI01(bf01),
		mI02(bf01, Local1),
		mI03(bf01, Local1, bf01))

	mI04(
		mI01(bf01),
		mI02(bf01, Local1),
		mI03(bf01, Local1, bf01),
		mI04(bf01, Local1, bf01, Local3))

	if (y262) {

	mI05(
		mI01(bf01),
		mI02(bf01, Local1),
		mI03(bf01, Local1, bf01),
		mI04(bf01, Local1, bf01, Local3),
		mI05(bf01, Local1, bf01, Local3, bf01))

	mI06(
		mI01(bf01),
		mI02(bf01, Local1),
		mI03(bf01, Local1, bf01),
		mI04(bf01, Local1, bf01, Local3),
		mI05(bf01, Local1, bf01, Local3, bf01),
		mI06(bf01, Local1, bf01, Local3, bf01, Local5))
	mI07(
		mI01(bf01),
		mI02(bf01, Local1),
		mI03(bf01, Local1, bf01),
		mI04(bf01, Local1, bf01, Local3),
		mI05(bf01, Local1, bf01, Local3, bf01),
		mI06(bf01, Local1, bf01, Local3, bf01, Local5),
		mI07(bf01, Local1, bf01, Local3, bf01, Local5, bf01))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	// } // if (chk0) {


	/*
	 * Modification 2:
	 *
	 * Some params are intermediately stored to Args (effectively local)
	 */

	Store(bf01, Arg1)
	Store(bf01, Arg3)
	Store(bf01, Arg5)

	mI01(bf01)

	// if (chk0) {

	mI02(bf01, Arg1)
	mI03(bf01, Arg1, bf01)
	mI04(bf01, Arg1, bf01, Arg3)
	mI05(bf01, Arg1, bf01, Arg3, bf01)
	mI06(bf01, Arg1, bf01, Arg3, bf01, Arg5)
	mI07(bf01, Arg1, bf01, Arg3, bf01, Arg5, bf01)

	mI01(
		mI01(bf01))

	mI02(
		mI01(bf01),
		mI02(bf01, Arg1))

	mI03(
		mI01(bf01),
		mI02(bf01, Arg1),
		mI03(bf01, Arg1, bf01))

	mI04(
		mI01(bf01),
		mI02(bf01, Arg1),
		mI03(bf01, Arg1, bf01),
		mI04(bf01, Arg1, bf01, Arg3))

	if (y262) {

	mI05(
		mI01(bf01),
		mI02(bf01, Arg1),
		mI03(bf01, Arg1, bf01),
		mI04(bf01, Arg1, bf01, Arg3),
		mI05(bf01, Arg1, bf01, Arg3, bf01))

	mI06(
		mI01(bf01),
		mI02(bf01, Arg1),
		mI03(bf01, Arg1, bf01),
		mI04(bf01, Arg1, bf01, Arg3),
		mI05(bf01, Arg1, bf01, Arg3, bf01),
		mI06(bf01, Arg1, bf01, Arg3, bf01, Arg5))
	mI07(
		mI01(bf01),
		mI02(bf01, Arg1),
		mI03(bf01, Arg1, bf01),
		mI04(bf01, Arg1, bf01, Arg3),
		mI05(bf01, Arg1, bf01, Arg3, bf01),
		mI06(bf01, Arg1, bf01, Arg3, bf01, Arg5),
		mI07(bf01, Arg1, bf01, Arg3, bf01, Arg5, bf01))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	// } // if (chk0) {


	/*
	 * Modification 3:
	 *
	 * Some params are intermediately stored to Named
	 */

    /*
     * bf01 is always treated like a buffer rather than an integer or buffer.
     * The tests below assume that this bf01 is treated like an integer.
     * Skip these tests for now...
     */
    /*
	Name(ii06, 0)
	Name(ii07, 0)
	Name(ii08, 0)

	Store(bf01, ii06)
	Store(bf01, ii07)
	Store(bf01, ii08)

	mI01(bf01)
	mI02(bf01, ii06)
	mI03(bf01, ii06, bf01)
	mI04(bf01, ii06, bf01, ii07)
	mI05(bf01, ii06, bf01, ii07, bf01)
	mI06(bf01, ii06, bf01, ii07, bf01, ii08)
	mI07(bf01, ii06, bf01, ii07, bf01, ii08, bf01)

	mI01(
		mI01(bf01))

	mI02(
		mI01(bf01),
		mI02(bf01, ii06))

	mI03(
		mI01(bf01),
		mI02(bf01, ii06),
		mI03(bf01, ii06, bf01))

	mI04(
		mI01(bf01),
		mI02(bf01, ii06),
		mI03(bf01, ii06, bf01),
		mI04(bf01, ii06, bf01, ii07))


	if (y262) {

	mI05(
		mI01(bf01),
		mI02(bf01, ii06),
		mI03(bf01, ii06, bf01),
		mI04(bf01, ii06, bf01, ii07),
		mI05(bf01, ii06, bf01, ii07, bf01))

	mI06(
		mI01(bf01),
		mI02(bf01, ii06),
		mI03(bf01, ii06, bf01),
		mI04(bf01, ii06, bf01, ii07),
		mI05(bf01, ii06, bf01, ii07, bf01),
		mI06(bf01, ii06, bf01, ii07, bf01, ii08))
	mI07(
		mI01(bf01),
		mI02(bf01, ii06),
		mI03(bf01, ii06, bf01),
		mI04(bf01, ii06, bf01, ii07),
		mI05(bf01, ii06, bf01, ii07, bf01),
		mI06(bf01, ii06, bf01, ii07, bf01, ii08),
		mI07(bf01, ii06, bf01, ii07, bf01, ii08, bf01))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}
    */


	/*
	 * Device
	 */
	Store(7, cmd0)


	/*
	 * Modification 0:
	 */

	mI01(d000)
	mI02(d000, d000)
	mI03(d000, d000, d000)
	mI04(d000, d000, d000, d000)

	// if (chk0) {

	mI05(d000, d000, d000, d000, d000)
	mI06(d000, d000, d000, d000, d000, d000)
	mI07(d000, d000, d000, d000, d000, d000, d000)

	mI01(
		mI01(d000))

	mI02(
		mI01(d000),
		mI02(d000, d000))

	mI03(
		mI01(d000),
		mI02(d000, d000),
		mI03(d000, d000, d000))

	mI04(
		mI01(d000),
		mI02(d000, d000),
		mI03(d000, d000, d000),
		mI04(d000, d000, d000, d000))

	if (y262) {

	mI05(
		mI01(d000),
		mI02(d000, d000),
		mI03(d000, d000, d000),
		mI04(d000, d000, d000, d000),
		mI05(d000, d000, d000, d000, d000))

	mI06(
		mI01(d000),
		mI02(d000, d000),
		mI03(d000, d000, d000),
		mI04(d000, d000, d000, d000),
		mI05(d000, d000, d000, d000, d000),
		mI06(d000, d000, d000, d000, d000, d000))
	mI07(
		mI01(d000),
		mI02(d000, d000),
		mI03(d000, d000, d000),
		mI04(d000, d000, d000, d000),
		mI05(d000, d000, d000, d000, d000),
		mI06(d000, d000, d000, d000, d000, d000),
		mI07(d000, d000, d000, d000, d000, d000, d000))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	// } // if (chk0)


	if (SLC0) {

	/*
	 * Modification 1:
	 *
	 * Some params are intermediately stored to Locals
	 */

/*
// Removed 09/2015. iASL now disallows these stores

	Store(d000, Local1)
	Store(d000, Local3)
	Store(d000, Local5)
*/

	mI01(d000)
	mI02(d000, Local1)
	mI03(d000, Local1, d000)
	mI04(d000, Local1, d000, Local3)
	mI05(d000, Local1, d000, Local3, d000)
	mI06(d000, Local1, d000, Local3, d000, Local5)
	mI07(d000, Local1, d000, Local3, d000, Local5, d000)

	mI01(
		mI01(d000))

	mI02(
		mI01(d000),
		mI02(d000, Local1))

	mI03(
		mI01(d000),
		mI02(d000, Local1),
		mI03(d000, Local1, d000))

	mI04(
		mI01(d000),
		mI02(d000, Local1),
		mI03(d000, Local1, d000),
		mI04(d000, Local1, d000, Local3))

	if (y262) {

	mI05(
		mI01(d000),
		mI02(d000, Local1),
		mI03(d000, Local1, d000),
		mI04(d000, Local1, d000, Local3),
		mI05(d000, Local1, d000, Local3, d000))

	mI06(
		mI01(d000),
		mI02(d000, Local1),
		mI03(d000, Local1, d000),
		mI04(d000, Local1, d000, Local3),
		mI05(d000, Local1, d000, Local3, d000),
		mI06(d000, Local1, d000, Local3, d000, Local5))
	mI07(
		mI01(d000),
		mI02(d000, Local1),
		mI03(d000, Local1, d000),
		mI04(d000, Local1, d000, Local3),
		mI05(d000, Local1, d000, Local3, d000),
		mI06(d000, Local1, d000, Local3, d000, Local5),
		mI07(d000, Local1, d000, Local3, d000, Local5, d000))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 2:
	 *
	 * Some params are intermediately stored to Args (effectively local)
	 */

/*
// Removed 09/2015. iASL now disallows these stores

	Store(d000, Arg1)
	Store(d000, Arg3)
	Store(d000, Arg5)
*/
	mI01(d000)
	mI02(d000, Arg1)
	mI03(d000, Arg1, d000)
	mI04(d000, Arg1, d000, Arg3)

	// if (chk0) {

	mI05(d000, Arg1, d000, Arg3, d000)
	mI06(d000, Arg1, d000, Arg3, d000, Arg5)
	mI07(d000, Arg1, d000, Arg3, d000, Arg5, d000)

	mI01(
		mI01(d000))

	mI02(
		mI01(d000),
		mI02(d000, Arg1))

	mI03(
		mI01(d000),
		mI02(d000, Arg1),
		mI03(d000, Arg1, d000))

	mI04(
		mI01(d000),
		mI02(d000, Arg1),
		mI03(d000, Arg1, d000),
		mI04(d000, Arg1, d000, Arg3))

	if (y262) {

	mI05(
		mI01(d000),
		mI02(d000, Arg1),
		mI03(d000, Arg1, d000),
		mI04(d000, Arg1, d000, Arg3),
		mI05(d000, Arg1, d000, Arg3, d000))

	mI06(
		mI01(d000),
		mI02(d000, Arg1),
		mI03(d000, Arg1, d000),
		mI04(d000, Arg1, d000, Arg3),
		mI05(d000, Arg1, d000, Arg3, d000),
		mI06(d000, Arg1, d000, Arg3, d000, Arg5))
	mI07(
		mI01(d000),
		mI02(d000, Arg1),
		mI03(d000, Arg1, d000),
		mI04(d000, Arg1, d000, Arg3),
		mI05(d000, Arg1, d000, Arg3, d000),
		mI06(d000, Arg1, d000, Arg3, d000, Arg5),
		mI07(d000, Arg1, d000, Arg3, d000, Arg5, d000))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	// } // if (chk0) {

	} // if (SLC0)


	/*
	 * Event
	 */
	Store(8, cmd0)


	/*
	 * Modification 0:
	 */

	mI01(e000)

	// if (chk0) {

	mI02(e000, e000)
	mI03(e000, e000, e000)
	mI04(e000, e000, e000, e000)
	mI05(e000, e000, e000, e000, e000)
	mI06(e000, e000, e000, e000, e000, e000)
	mI07(e000, e000, e000, e000, e000, e000, e000)

	mI01(
		mI01(e000))

	mI02(
		mI01(e000),
		mI02(e000, e000))

	mI03(
		mI01(e000),
		mI02(e000, e000),
		mI03(e000, e000, e000))

	mI04(
		mI01(e000),
		mI02(e000, e000),
		mI03(e000, e000, e000),
		mI04(e000, e000, e000, e000))

	if (y262) {

	mI05(
		mI01(e000),
		mI02(e000, e000),
		mI03(e000, e000, e000),
		mI04(e000, e000, e000, e000),
		mI05(e000, e000, e000, e000, e000))

	mI06(
		mI01(e000),
		mI02(e000, e000),
		mI03(e000, e000, e000),
		mI04(e000, e000, e000, e000),
		mI05(e000, e000, e000, e000, e000),
		mI06(e000, e000, e000, e000, e000, e000))
	mI07(
		mI01(e000),
		mI02(e000, e000),
		mI03(e000, e000, e000),
		mI04(e000, e000, e000, e000),
		mI05(e000, e000, e000, e000, e000),
		mI06(e000, e000, e000, e000, e000, e000),
		mI07(e000, e000, e000, e000, e000, e000, e000))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	// } // if (chk0) {


	if (SLC0) {

	/*
	 * Modification 1:
	 *
	 * Some params are intermediately stored to Locals
	 *
	 * Note:
	 *   in the checking above the locals (Local1, Local3, Local5)
	 *   were assigned with the object of type Device. MS rejects
	 *   those locals to be rewritten after that assigning.
	 *   So, here I use Local0,Local2,Local4.
	 */

/*
// Removed 09/2015. iASL now disallows these stores

	Store(e000, Local0)
	Store(e000, Local2)
	Store(e000, Local4)
*/

	Store (0, Local0)
	Store (2, Local2)
	Store (4, Local4)

	mI01(e000)
	mI02(e000, Local0)
	mI03(e000, Local0, e000)
	mI04(e000, Local0, e000, Local2)
	mI05(e000, Local0, e000, Local2, e000)
	mI06(e000, Local0, e000, Local2, e000, Local4)
	mI07(e000, Local0, e000, Local2, e000, Local4, e000)

	mI01(
		mI01(e000))

	mI02(
		mI01(e000),
		mI02(e000, Local0))

	mI03(
		mI01(e000),
		mI02(e000, Local0),
		mI03(e000, Local0, e000))

	mI04(
		mI01(e000),
		mI02(e000, Local0),
		mI03(e000, Local0, e000),
		mI04(e000, Local0, e000, Local2))

	if (y262) {

	mI05(
		mI01(e000),
		mI02(e000, Local0),
		mI03(e000, Local0, e000),
		mI04(e000, Local0, e000, Local2),
		mI05(e000, Local0, e000, Local2, e000))

	mI06(
		mI01(e000),
		mI02(e000, Local0),
		mI03(e000, Local0, e000),
		mI04(e000, Local0, e000, Local2),
		mI05(e000, Local0, e000, Local2, e000),
		mI06(e000, Local0, e000, Local2, e000, Local4))
	mI07(
		mI01(e000),
		mI02(e000, Local0),
		mI03(e000, Local0, e000),
		mI04(e000, Local0, e000, Local2),
		mI05(e000, Local0, e000, Local2, e000),
		mI06(e000, Local0, e000, Local2, e000, Local4),
		mI07(e000, Local0, e000, Local2, e000, Local4, e000))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 2:
	 *
	 * Some params are intermediately stored to Args (effectively local)
	 *
	 * Note:
	 *   in the checking above the locals (Local1, Local3, Local5)
	 *   were assigned with the object of type Device. MS rejects
	 *   those locals to be rewritten after that assigning.
	 *   So, here I use Arg0,Arg2,Arg4.
	 */

/*
// Removed 09/2015. iASL now disallows these stores

	Store(e000, Arg0)
	Store(e000, Arg2)
	Store(e000, Arg4)
*/

	mI01(e000)
	mI02(e000, Arg0)
	mI03(e000, Arg0, e000)
	mI04(e000, Arg0, e000, Arg2)
	mI05(e000, Arg0, e000, Arg2, e000)
	mI06(e000, Arg0, e000, Arg2, e000, Arg4)
	mI07(e000, Arg0, e000, Arg2, e000, Arg4, e000)

	mI01(
		mI01(e000))

	mI02(
		mI01(e000),
		mI02(e000, Arg0))

	mI03(
		mI01(e000),
		mI02(e000, Arg0),
		mI03(e000, Arg0, e000))

	mI04(
		mI01(e000),
		mI02(e000, Arg0),
		mI03(e000, Arg0, e000),
		mI04(e000, Arg0, e000, Arg2))

	if (y262) {

	mI05(
		mI01(e000),
		mI02(e000, Arg0),
		mI03(e000, Arg0, e000),
		mI04(e000, Arg0, e000, Arg2),
		mI05(e000, Arg0, e000, Arg2, e000))

	mI06(
		mI01(e000),
		mI02(e000, Arg0),
		mI03(e000, Arg0, e000),
		mI04(e000, Arg0, e000, Arg2),
		mI05(e000, Arg0, e000, Arg2, e000),
		mI06(e000, Arg0, e000, Arg2, e000, Arg4))
	mI07(
		mI01(e000),
		mI02(e000, Arg0),
		mI03(e000, Arg0, e000),
		mI04(e000, Arg0, e000, Arg2),
		mI05(e000, Arg0, e000, Arg2, e000),
		mI06(e000, Arg0, e000, Arg2, e000, Arg4),
		mI07(e000, Arg0, e000, Arg2, e000, Arg4, e000))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	} // if (SLC0)


	/*
	 * Method
	 */


	/*
	 * Mutex
	 */
	Store(9, cmd0)


	/*
	 * Modification 0:
	 */

	mI01(mx00)

	// if (chk0) {

	mI02(mx00, mx00)
	mI03(mx00, mx00, mx00)
	mI04(mx00, mx00, mx00, mx00)
	mI05(mx00, mx00, mx00, mx00, mx00)
	mI06(mx00, mx00, mx00, mx00, mx00, mx00)
	mI07(mx00, mx00, mx00, mx00, mx00, mx00, mx00)

	mI01(
		mI01(mx00))

	mI02(
		mI01(mx00),
		mI02(mx00, mx00))

	mI03(
		mI01(mx00),
		mI02(mx00, mx00),
		mI03(mx00, mx00, mx00))

	mI04(
		mI01(mx00),
		mI02(mx00, mx00),
		mI03(mx00, mx00, mx00),
		mI04(mx00, mx00, mx00, mx00))

	if (y262) {

	mI05(
		mI01(mx00),
		mI02(mx00, mx00),
		mI03(mx00, mx00, mx00),
		mI04(mx00, mx00, mx00, mx00),
		mI05(mx00, mx00, mx00, mx00, mx00))

	mI06(
		mI01(mx00),
		mI02(mx00, mx00),
		mI03(mx00, mx00, mx00),
		mI04(mx00, mx00, mx00, mx00),
		mI05(mx00, mx00, mx00, mx00, mx00),
		mI06(mx00, mx00, mx00, mx00, mx00, mx00))
	mI07(
		mI01(mx00),
		mI02(mx00, mx00),
		mI03(mx00, mx00, mx00),
		mI04(mx00, mx00, mx00, mx00),
		mI05(mx00, mx00, mx00, mx00, mx00),
		mI06(mx00, mx00, mx00, mx00, mx00, mx00),
		mI07(mx00, mx00, mx00, mx00, mx00, mx00, mx00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	// } // if (chk0) {


	if (SLCK) {

	/*
	 * Modification 1:
	 *
	 * Some params are intermediately stored to Locals
	 *
	 * Note:
	 *   in the checkings above the locals (Local0-Local5)
	 *   were assigned with the object of type Device/Event.
	 *   MS rejects those locals to be rewritten after that assigning.
	 *   So, I have no more Locals for checking (SLCK here - because of that).
	 */

/*
// Removed 09/2015. iASL now disallows these stores

	Store(mx00, Local1)
	Store(mx00, Local3)
	Store(mx00, Local5)
*/

	mI01(mx00)
	mI02(mx00, Local1)
	mI03(mx00, Local1, mx00)
	mI04(mx00, Local1, mx00, Local3)
	mI05(mx00, Local1, mx00, Local3, mx00)
	mI06(mx00, Local1, mx00, Local3, mx00, Local5)
	mI07(mx00, Local1, mx00, Local3, mx00, Local5, mx00)

	mI01(
		mI01(mx00))

	mI02(
		mI01(mx00),
		mI02(mx00, Local1))

	mI03(
		mI01(mx00),
		mI02(mx00, Local1),
		mI03(mx00, Local1, mx00))

	mI04(
		mI01(mx00),
		mI02(mx00, Local1),
		mI03(mx00, Local1, mx00),
		mI04(mx00, Local1, mx00, Local3))

	if (y262) {

	mI05(
		mI01(mx00),
		mI02(mx00, Local1),
		mI03(mx00, Local1, mx00),
		mI04(mx00, Local1, mx00, Local3),
		mI05(mx00, Local1, mx00, Local3, mx00))

	mI06(
		mI01(mx00),
		mI02(mx00, Local1),
		mI03(mx00, Local1, mx00),
		mI04(mx00, Local1, mx00, Local3),
		mI05(mx00, Local1, mx00, Local3, mx00),
		mI06(mx00, Local1, mx00, Local3, mx00, Local5))
	mI07(
		mI01(mx00),
		mI02(mx00, Local1),
		mI03(mx00, Local1, mx00),
		mI04(mx00, Local1, mx00, Local3),
		mI05(mx00, Local1, mx00, Local3, mx00),
		mI06(mx00, Local1, mx00, Local3, mx00, Local5),
		mI07(mx00, Local1, mx00, Local3, mx00, Local5, mx00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 2:
	 *
	 * Some params are intermediately stored to Args (effectively local)
	 *
	 * Note:
	 *   in the checkings above the locals (Arg0-Arg5)
	 *   were assigned with the object of type Device/Event.
	 *   MS rejects those locals to be rewritten after that assigning.
	 *   So, I have no more Args for checking (SLCK here - because of that).
	 */

/*
// Removed 09/2015. iASL now disallows these stores

	Store(mx00, Arg1)
	Store(mx00, Arg3)
	Store(mx00, Arg5)
*/

	mI01(mx00)
	mI02(mx00, Arg1)
	mI03(mx00, Arg1, mx00)
	mI04(mx00, Arg1, mx00, Arg3)
	mI05(mx00, Arg1, mx00, Arg3, mx00)
	mI06(mx00, Arg1, mx00, Arg3, mx00, Arg5)
	mI07(mx00, Arg1, mx00, Arg3, mx00, Arg5, mx00)

	mI01(
		mI01(mx00))

	mI02(
		mI01(mx00),
		mI02(mx00, Arg1))

	mI03(
		mI01(mx00),
		mI02(mx00, Arg1),
		mI03(mx00, Arg1, mx00))

	mI04(
		mI01(mx00),
		mI02(mx00, Arg1),
		mI03(mx00, Arg1, mx00),
		mI04(mx00, Arg1, mx00, Arg3))

	if (y262) {

	mI05(
		mI01(mx00),
		mI02(mx00, Arg1),
		mI03(mx00, Arg1, mx00),
		mI04(mx00, Arg1, mx00, Arg3),
		mI05(mx00, Arg1, mx00, Arg3, mx00))

	mI06(
		mI01(mx00),
		mI02(mx00, Arg1),
		mI03(mx00, Arg1, mx00),
		mI04(mx00, Arg1, mx00, Arg3),
		mI05(mx00, Arg1, mx00, Arg3, mx00),
		mI06(mx00, Arg1, mx00, Arg3, mx00, Arg5))
	mI07(
		mI01(mx00),
		mI02(mx00, Arg1),
		mI03(mx00, Arg1, mx00),
		mI04(mx00, Arg1, mx00, Arg3),
		mI05(mx00, Arg1, mx00, Arg3, mx00),
		mI06(mx00, Arg1, mx00, Arg3, mx00, Arg5),
		mI07(mx00, Arg1, mx00, Arg3, mx00, Arg5, mx00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	} // if (SLCK)


	/*
	 * Operation Region
	 */
	Store(10, cmd0)


	/*
	 * Modification 0:
	 */

	mI01(r000)

	// if (chk0) {

	mI02(r000, r000)
	mI03(r000, r000, r000)
	mI04(r000, r000, r000, r000)
	mI05(r000, r000, r000, r000, r000)
	mI06(r000, r000, r000, r000, r000, r000)
	mI07(r000, r000, r000, r000, r000, r000, r000)

	mI01(
		mI01(r000))

	mI02(
		mI01(r000),
		mI02(r000, r000))

	mI03(
		mI01(r000),
		mI02(r000, r000),
		mI03(r000, r000, r000))

	mI04(
		mI01(r000),
		mI02(r000, r000),
		mI03(r000, r000, r000),
		mI04(r000, r000, r000, r000))

	if (y262) {

	mI05(
		mI01(r000),
		mI02(r000, r000),
		mI03(r000, r000, r000),
		mI04(r000, r000, r000, r000),
		mI05(r000, r000, r000, r000, r000))

	mI06(
		mI01(r000),
		mI02(r000, r000),
		mI03(r000, r000, r000),
		mI04(r000, r000, r000, r000),
		mI05(r000, r000, r000, r000, r000),
		mI06(r000, r000, r000, r000, r000, r000))
	mI07(
		mI01(r000),
		mI02(r000, r000),
		mI03(r000, r000, r000),
		mI04(r000, r000, r000, r000),
		mI05(r000, r000, r000, r000, r000),
		mI06(r000, r000, r000, r000, r000, r000),
		mI07(r000, r000, r000, r000, r000, r000, r000))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	// } // if (chk0) {


	if (SLCK) {

	/*
	 * Modification 1:
	 *
	 * Some params are intermediately stored to Locals
	 *
	 * Note:
	 *   in the checkings above the locals (Local0-Local5)
	 *   were assigned with the object of type Device/Event.
	 *   MS rejects those locals to be rewritten after that assigning.
	 *   So, I have no more Locals for checking (SLCK here - because of that).
	 */

/*
// Removed 09/2015. iASL now disallows these stores

	Store(r000, Local1)
	Store(r000, Local3)
	Store(r000, Local5)
*/

	mI01(r000)
	mI02(r000, Local1)
	mI03(r000, Local1, r000)
	mI04(r000, Local1, r000, Local3)
	mI05(r000, Local1, r000, Local3, r000)
	mI06(r000, Local1, r000, Local3, r000, Local5)
	mI07(r000, Local1, r000, Local3, r000, Local5, r000)

	mI01(
		mI01(r000))

	mI02(
		mI01(r000),
		mI02(r000, Local1))

	mI03(
		mI01(r000),
		mI02(r000, Local1),
		mI03(r000, Local1, r000))

	mI04(
		mI01(r000),
		mI02(r000, Local1),
		mI03(r000, Local1, r000),
		mI04(r000, Local1, r000, Local3))

	if (y262) {

	mI05(
		mI01(r000),
		mI02(r000, Local1),
		mI03(r000, Local1, r000),
		mI04(r000, Local1, r000, Local3),
		mI05(r000, Local1, r000, Local3, r000))

	mI06(
		mI01(r000),
		mI02(r000, Local1),
		mI03(r000, Local1, r000),
		mI04(r000, Local1, r000, Local3),
		mI05(r000, Local1, r000, Local3, r000),
		mI06(r000, Local1, r000, Local3, r000, Local5))
	mI07(
		mI01(r000),
		mI02(r000, Local1),
		mI03(r000, Local1, r000),
		mI04(r000, Local1, r000, Local3),
		mI05(r000, Local1, r000, Local3, r000),
		mI06(r000, Local1, r000, Local3, r000, Local5),
		mI07(r000, Local1, r000, Local3, r000, Local5, r000))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 2:
	 *
	 * Some params are intermediately stored to Args (effectively local)
	 *
	 * Note:
	 *   in the checkings above the locals (Arg0-Arg5)
	 *   were assigned with the object of type Device/Event.
	 *   MS rejects those locals to be rewritten after that assigning.
	 *   So, I have no more Args for checking (SLCK here - because of that).
	 */

/*
// Removed 09/2015. iASL now disallows these stores

	Store(r000, Arg1)
	Store(r000, Arg3)
	Store(r000, Arg5)
*/

	mI01(r000)
	mI02(r000, Arg1)
	mI03(r000, Arg1, r000)
	mI04(r000, Arg1, r000, Arg3)
	mI05(r000, Arg1, r000, Arg3, r000)
	mI06(r000, Arg1, r000, Arg3, r000, Arg5)
	mI07(r000, Arg1, r000, Arg3, r000, Arg5, r000)

	mI01(
		mI01(r000))

	mI02(
		mI01(r000),
		mI02(r000, Arg1))

	mI03(
		mI01(r000),
		mI02(r000, Arg1),
		mI03(r000, Arg1, r000))

	mI04(
		mI01(r000),
		mI02(r000, Arg1),
		mI03(r000, Arg1, r000),
		mI04(r000, Arg1, r000, Arg3))

	if (y262) {

	mI05(
		mI01(r000),
		mI02(r000, Arg1),
		mI03(r000, Arg1, r000),
		mI04(r000, Arg1, r000, Arg3),
		mI05(r000, Arg1, r000, Arg3, r000))

	mI06(
		mI01(r000),
		mI02(r000, Arg1),
		mI03(r000, Arg1, r000),
		mI04(r000, Arg1, r000, Arg3),
		mI05(r000, Arg1, r000, Arg3, r000),
		mI06(r000, Arg1, r000, Arg3, r000, Arg5))
	mI07(
		mI01(r000),
		mI02(r000, Arg1),
		mI03(r000, Arg1, r000),
		mI04(r000, Arg1, r000, Arg3),
		mI05(r000, Arg1, r000, Arg3, r000),
		mI06(r000, Arg1, r000, Arg3, r000, Arg5),
		mI07(r000, Arg1, r000, Arg3, r000, Arg5, r000))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	} // if (SLCK)


	/*
	 * Power Resource
	 */
	Store(11, cmd0)


	/*
	 * Modification 0:
	 */

	mI01(pw00)
	mI02(pw00, pw00)
	mI03(pw00, pw00, pw00)
	mI04(pw00, pw00, pw00, pw00)
	mI05(pw00, pw00, pw00, pw00, pw00)
	mI06(pw00, pw00, pw00, pw00, pw00, pw00)
	mI07(pw00, pw00, pw00, pw00, pw00, pw00, pw00)

	mI01(
		mI01(pw00))
	mI02(
		mI01(pw00),
		mI02(pw00, pw00))
	mI03(
		mI01(pw00),
		mI02(pw00, pw00),
		mI03(pw00, pw00, pw00))

	// if (chk0) {

	mI04(
		mI01(pw00),
		mI02(pw00, pw00),
		mI03(pw00, pw00, pw00),
		mI04(pw00, pw00, pw00, pw00))

	if (y262) {

	mI05(
		mI01(pw00),
		mI02(pw00, pw00),
		mI03(pw00, pw00, pw00),
		mI04(pw00, pw00, pw00, pw00),
		mI05(pw00, pw00, pw00, pw00, pw00))

	mI06(
		mI01(pw00),
		mI02(pw00, pw00),
		mI03(pw00, pw00, pw00),
		mI04(pw00, pw00, pw00, pw00),
		mI05(pw00, pw00, pw00, pw00, pw00),
		mI06(pw00, pw00, pw00, pw00, pw00, pw00))
	mI07(
		mI01(pw00),
		mI02(pw00, pw00),
		mI03(pw00, pw00, pw00),
		mI04(pw00, pw00, pw00, pw00),
		mI05(pw00, pw00, pw00, pw00, pw00),
		mI06(pw00, pw00, pw00, pw00, pw00, pw00),
		mI07(pw00, pw00, pw00, pw00, pw00, pw00, pw00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	// } // if (chk0)


	if (SLCK) {

	/*
	 * Modification 1:
	 *
	 * Some params are intermediately stored to Locals
	 *
	 * Note: no Locals for this checking (see comment above).
	 */

/*
// Removed 09/2015. iASL now disallows these stores

	Store(pw00, Local1)
	Store(pw00, Local3)
	Store(pw00, Local5)
*/

	mI01(pw00)
	mI02(pw00, Local1)
	mI03(pw00, Local1, pw00)
	mI04(pw00, Local1, pw00, Local3)
	mI05(pw00, Local1, pw00, Local3, pw00)
	mI06(pw00, Local1, pw00, Local3, pw00, Local5)
	mI07(pw00, Local1, pw00, Local3, pw00, Local5, pw00)

	mI01(
		mI01(pw00))

	mI02(
		mI01(pw00),
		mI02(pw00, Local1))

	mI03(
		mI01(pw00),
		mI02(pw00, Local1),
		mI03(pw00, Local1, pw00))

	mI04(
		mI01(pw00),
		mI02(pw00, Local1),
		mI03(pw00, Local1, pw00),
		mI04(pw00, Local1, pw00, Local3))

	if (y262) {

	mI05(
		mI01(pw00),
		mI02(pw00, Local1),
		mI03(pw00, Local1, pw00),
		mI04(pw00, Local1, pw00, Local3),
		mI05(pw00, Local1, pw00, Local3, pw00))

	mI06(
		mI01(pw00),
		mI02(pw00, Local1),
		mI03(pw00, Local1, pw00),
		mI04(pw00, Local1, pw00, Local3),
		mI05(pw00, Local1, pw00, Local3, pw00),
		mI06(pw00, Local1, pw00, Local3, pw00, Local5))
	mI07(
		mI01(pw00),
		mI02(pw00, Local1),
		mI03(pw00, Local1, pw00),
		mI04(pw00, Local1, pw00, Local3),
		mI05(pw00, Local1, pw00, Local3, pw00),
		mI06(pw00, Local1, pw00, Local3, pw00, Local5),
		mI07(pw00, Local1, pw00, Local3, pw00, Local5, pw00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 2:
	 *
	 * Some params are intermediately stored to Args (effectively local)
	 *
	 * Note: no Args for this checking (see comment above).
	 */

/*
// Removed 09/2015. iASL now disallows these stores

	Store(pw00, Arg1)
	Store(pw00, Arg3)
	Store(pw00, Arg5)
*/

	mI01(pw00)
	mI02(pw00, Arg1)
	mI03(pw00, Arg1, pw00)
	mI04(pw00, Arg1, pw00, Arg3)
	mI05(pw00, Arg1, pw00, Arg3, pw00)
	mI06(pw00, Arg1, pw00, Arg3, pw00, Arg5)
	mI07(pw00, Arg1, pw00, Arg3, pw00, Arg5, pw00)

	mI01(
		mI01(pw00))

	mI02(
		mI01(pw00),
		mI02(pw00, Arg1))

	mI03(
		mI01(pw00),
		mI02(pw00, Arg1),
		mI03(pw00, Arg1, pw00))

	mI04(
		mI01(pw00),
		mI02(pw00, Arg1),
		mI03(pw00, Arg1, pw00),
		mI04(pw00, Arg1, pw00, Arg3))

	if (y262) {

	mI05(
		mI01(pw00),
		mI02(pw00, Arg1),
		mI03(pw00, Arg1, pw00),
		mI04(pw00, Arg1, pw00, Arg3),
		mI05(pw00, Arg1, pw00, Arg3, pw00))

	mI06(
		mI01(pw00),
		mI02(pw00, Arg1),
		mI03(pw00, Arg1, pw00),
		mI04(pw00, Arg1, pw00, Arg3),
		mI05(pw00, Arg1, pw00, Arg3, pw00),
		mI06(pw00, Arg1, pw00, Arg3, pw00, Arg5))
	mI07(
		mI01(pw00),
		mI02(pw00, Arg1),
		mI03(pw00, Arg1, pw00),
		mI04(pw00, Arg1, pw00, Arg3),
		mI05(pw00, Arg1, pw00, Arg3, pw00),
		mI06(pw00, Arg1, pw00, Arg3, pw00, Arg5),
		mI07(pw00, Arg1, pw00, Arg3, pw00, Arg5, pw00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	} // if (SLCK)


	/*
	 * Processor
	 */
	Store(12, cmd0)


	/*
	 * Modification 0:
	 */

	mI01(pr00)
	mI02(pr00, pr00)
	mI03(pr00, pr00, pr00)
	mI04(pr00, pr00, pr00, pr00)
	mI05(pr00, pr00, pr00, pr00, pr00)
	mI06(pr00, pr00, pr00, pr00, pr00, pr00)
	mI07(pr00, pr00, pr00, pr00, pr00, pr00, pr00)

	mI01(
		mI01(pr00))

	mI02(
		mI01(pr00),
		mI02(pr00, pr00))

	mI03(
		mI01(pr00),
		mI02(pr00, pr00),
		mI03(pr00, pr00, pr00))

	mI04(
		mI01(pr00),
		mI02(pr00, pr00),
		mI03(pr00, pr00, pr00),
		mI04(pr00, pr00, pr00, pr00))

	if (y262) {

	mI05(
		mI01(pr00),
		mI02(pr00, pr00),
		mI03(pr00, pr00, pr00),
		mI04(pr00, pr00, pr00, pr00),
		mI05(pr00, pr00, pr00, pr00, pr00))

	mI06(
		mI01(pr00),
		mI02(pr00, pr00),
		mI03(pr00, pr00, pr00),
		mI04(pr00, pr00, pr00, pr00),
		mI05(pr00, pr00, pr00, pr00, pr00),
		mI06(pr00, pr00, pr00, pr00, pr00, pr00))
	mI07(
		mI01(pr00),
		mI02(pr00, pr00),
		mI03(pr00, pr00, pr00),
		mI04(pr00, pr00, pr00, pr00),
		mI05(pr00, pr00, pr00, pr00, pr00),
		mI06(pr00, pr00, pr00, pr00, pr00, pr00),
		mI07(pr00, pr00, pr00, pr00, pr00, pr00, pr00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	if (SLCK) {

	/*
	 * Modification 1:
	 *
	 * Some params are intermediately stored to Locals
	 *
	 * Note: no Locals for this checking (see comment above).
	 */

/*
// Removed 09/2015. iASL now disallows these stores

	Store(pr00, Local1)
	Store(pr00, Local3)
	Store(pr00, Local5)
*/

	mI01(pr00)
	mI02(pr00, Local1)
	mI03(pr00, Local1, pr00)
	mI04(pr00, Local1, pr00, Local3)
	mI05(pr00, Local1, pr00, Local3, pr00)
	mI06(pr00, Local1, pr00, Local3, pr00, Local5)
	mI07(pr00, Local1, pr00, Local3, pr00, Local5, pr00)

	mI01(
		mI01(pr00))

	mI02(
		mI01(pr00),
		mI02(pr00, Local1))

	mI03(
		mI01(pr00),
		mI02(pr00, Local1),
		mI03(pr00, Local1, pr00))

	mI04(
		mI01(pr00),
		mI02(pr00, Local1),
		mI03(pr00, Local1, pr00),
		mI04(pr00, Local1, pr00, Local3))

	if (y262) {

	mI05(
		mI01(pr00),
		mI02(pr00, Local1),
		mI03(pr00, Local1, pr00),
		mI04(pr00, Local1, pr00, Local3),
		mI05(pr00, Local1, pr00, Local3, pr00))

	mI06(
		mI01(pr00),
		mI02(pr00, Local1),
		mI03(pr00, Local1, pr00),
		mI04(pr00, Local1, pr00, Local3),
		mI05(pr00, Local1, pr00, Local3, pr00),
		mI06(pr00, Local1, pr00, Local3, pr00, Local5))
	mI07(
		mI01(pr00),
		mI02(pr00, Local1),
		mI03(pr00, Local1, pr00),
		mI04(pr00, Local1, pr00, Local3),
		mI05(pr00, Local1, pr00, Local3, pr00),
		mI06(pr00, Local1, pr00, Local3, pr00, Local5),
		mI07(pr00, Local1, pr00, Local3, pr00, Local5, pr00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 2:
	 *
	 * Some params are intermediately stored to Args (effectively local)
	 *
	 * Note: no Args for this checking (see comment above).
	 */

/*
// Removed 09/2015. iASL now disallows these stores

	Store(pr00, Arg1)
	Store(pr00, Arg3)
	Store(pr00, Arg5)
*/

	mI01(pr00)
	mI02(pr00, Arg1)
	mI03(pr00, Arg1, pr00)
	mI04(pr00, Arg1, pr00, Arg3)
	mI05(pr00, Arg1, pr00, Arg3, pr00)
	mI06(pr00, Arg1, pr00, Arg3, pr00, Arg5)
	mI07(pr00, Arg1, pr00, Arg3, pr00, Arg5, pr00)

	mI01(
		mI01(pr00))

	mI02(
		mI01(pr00),
		mI02(pr00, Arg1))

	mI03(
		mI01(pr00),
		mI02(pr00, Arg1),
		mI03(pr00, Arg1, pr00))

	mI04(
		mI01(pr00),
		mI02(pr00, Arg1),
		mI03(pr00, Arg1, pr00),
		mI04(pr00, Arg1, pr00, Arg3))

	if (y262) {

	mI05(
		mI01(pr00),
		mI02(pr00, Arg1),
		mI03(pr00, Arg1, pr00),
		mI04(pr00, Arg1, pr00, Arg3),
		mI05(pr00, Arg1, pr00, Arg3, pr00))

	mI06(
		mI01(pr00),
		mI02(pr00, Arg1),
		mI03(pr00, Arg1, pr00),
		mI04(pr00, Arg1, pr00, Arg3),
		mI05(pr00, Arg1, pr00, Arg3, pr00),
		mI06(pr00, Arg1, pr00, Arg3, pr00, Arg5))
	mI07(
		mI01(pr00),
		mI02(pr00, Arg1),
		mI03(pr00, Arg1, pr00),
		mI04(pr00, Arg1, pr00, Arg3),
		mI05(pr00, Arg1, pr00, Arg3, pr00),
		mI06(pr00, Arg1, pr00, Arg3, pr00, Arg5),
		mI07(pr00, Arg1, pr00, Arg3, pr00, Arg5, pr00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	} // if (SLCK)


	/*
	 * Thermal Zone
	 */
	Store(13, cmd0)


	/*
	 * Modification 0:
	 */

	mI01(tz00)
	mI02(tz00, tz00)
	mI03(tz00, tz00, tz00)
	mI04(tz00, tz00, tz00, tz00)
	mI05(tz00, tz00, tz00, tz00, tz00)
	mI06(tz00, tz00, tz00, tz00, tz00, tz00)
	mI07(tz00, tz00, tz00, tz00, tz00, tz00, tz00)

	mI01(
		mI01(tz00))

	mI02(
		mI01(tz00),
		mI02(tz00, tz00))

	mI03(
		mI01(tz00),
		mI02(tz00, tz00),
		mI03(tz00, tz00, tz00))

	mI04(
		mI01(tz00),
		mI02(tz00, tz00),
		mI03(tz00, tz00, tz00),
		mI04(tz00, tz00, tz00, tz00))

	if (y262) {

	mI05(
		mI01(tz00),
		mI02(tz00, tz00),
		mI03(tz00, tz00, tz00),
		mI04(tz00, tz00, tz00, tz00),
		mI05(tz00, tz00, tz00, tz00, tz00))

	mI06(
		mI01(tz00),
		mI02(tz00, tz00),
		mI03(tz00, tz00, tz00),
		mI04(tz00, tz00, tz00, tz00),
		mI05(tz00, tz00, tz00, tz00, tz00),
		mI06(tz00, tz00, tz00, tz00, tz00, tz00))
	mI07(
		mI01(tz00),
		mI02(tz00, tz00),
		mI03(tz00, tz00, tz00),
		mI04(tz00, tz00, tz00, tz00),
		mI05(tz00, tz00, tz00, tz00, tz00),
		mI06(tz00, tz00, tz00, tz00, tz00, tz00),
		mI07(tz00, tz00, tz00, tz00, tz00, tz00, tz00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	if (SLCK) {

	/*
	 * Modification 1:
	 *
	 * Some params are intermediately stored to Locals
	 *
	 * Note: no Locals for this checking (see comment above).
	 */

/*
// Removed 09/2015. iASL now disallows these stores

	Store(tz00, Local1)
	Store(tz00, Local3)
	Store(tz00, Local5)
*/

	mI01(tz00)
	mI02(tz00, Local1)
	mI03(tz00, Local1, tz00)
	mI04(tz00, Local1, tz00, Local3)
	mI05(tz00, Local1, tz00, Local3, tz00)
	mI06(tz00, Local1, tz00, Local3, tz00, Local5)
	mI07(tz00, Local1, tz00, Local3, tz00, Local5, tz00)

	mI01(
		mI01(tz00))

	mI02(
		mI01(tz00),
		mI02(tz00, Local1))

	mI03(
		mI01(tz00),
		mI02(tz00, Local1),
		mI03(tz00, Local1, tz00))

	mI04(
		mI01(tz00),
		mI02(tz00, Local1),
		mI03(tz00, Local1, tz00),
		mI04(tz00, Local1, tz00, Local3))

	if (y262) {

	mI05(
		mI01(tz00),
		mI02(tz00, Local1),
		mI03(tz00, Local1, tz00),
		mI04(tz00, Local1, tz00, Local3),
		mI05(tz00, Local1, tz00, Local3, tz00))

	mI06(
		mI01(tz00),
		mI02(tz00, Local1),
		mI03(tz00, Local1, tz00),
		mI04(tz00, Local1, tz00, Local3),
		mI05(tz00, Local1, tz00, Local3, tz00),
		mI06(tz00, Local1, tz00, Local3, tz00, Local5))
	mI07(
		mI01(tz00),
		mI02(tz00, Local1),
		mI03(tz00, Local1, tz00),
		mI04(tz00, Local1, tz00, Local3),
		mI05(tz00, Local1, tz00, Local3, tz00),
		mI06(tz00, Local1, tz00, Local3, tz00, Local5),
		mI07(tz00, Local1, tz00, Local3, tz00, Local5, tz00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}


	/*
	 * Modification 2:
	 *
	 * Some params are intermediately stored to Args (effectively local)
	 *
	 * Note: no Args for this checking (see comment above).
	 */

/*
// Removed 09/2015. iASL now disallows these stores

	Store(tz00, Arg1)
	Store(tz00, Arg3)
	Store(tz00, Arg5)
*/

	mI01(tz00)
	mI02(tz00, Arg1)
	mI03(tz00, Arg1, tz00)
	mI04(tz00, Arg1, tz00, Arg3)
	mI05(tz00, Arg1, tz00, Arg3, tz00)
	mI06(tz00, Arg1, tz00, Arg3, tz00, Arg5)
	mI07(tz00, Arg1, tz00, Arg3, tz00, Arg5, tz00)

	mI01(
		mI01(tz00))

	mI02(
		mI01(tz00),
		mI02(tz00, Arg1))

	mI03(
		mI01(tz00),
		mI02(tz00, Arg1),
		mI03(tz00, Arg1, tz00))

	mI04(
		mI01(tz00),
		mI02(tz00, Arg1),
		mI03(tz00, Arg1, tz00),
		mI04(tz00, Arg1, tz00, Arg3))

	if (y262) {

	mI05(
		mI01(tz00),
		mI02(tz00, Arg1),
		mI03(tz00, Arg1, tz00),
		mI04(tz00, Arg1, tz00, Arg3),
		mI05(tz00, Arg1, tz00, Arg3, tz00))

	mI06(
		mI01(tz00),
		mI02(tz00, Arg1),
		mI03(tz00, Arg1, tz00),
		mI04(tz00, Arg1, tz00, Arg3),
		mI05(tz00, Arg1, tz00, Arg3, tz00),
		mI06(tz00, Arg1, tz00, Arg3, tz00, Arg5))
	mI07(
		mI01(tz00),
		mI02(tz00, Arg1),
		mI03(tz00, Arg1, tz00),
		mI04(tz00, Arg1, tz00, Arg3),
		mI05(tz00, Arg1, tz00, Arg3, tz00),
		mI06(tz00, Arg1, tz00, Arg3, tz00, Arg5),
		mI07(tz00, Arg1, tz00, Arg3, tz00, Arg5, tz00))
	} else {
		OUTP("WARNING: some tests of ns_in40.asl are blocked!")
	}

	} // if (SLCK)
}

Method(ini4)
{
	SRMT("in40")
	in40(0,0,0,0,0,0,0)

	SRMT("in41")
	in41(0,0,0,0,0,0,0)

	CH03("ini4", z167, 0x000, __LINE__, 0)
}
