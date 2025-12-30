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
 * Methods of common use.
 *
 * Note: writing to the global objects - nm03, pd12 and pd13 forces
 * outstanding allocation reports.
 */

Name(id26, 8)
Name(nm03, 0)
Name(pd12, Package(Multiply(id26, 2)) {})
Name(pd13, Package(Multiply(id26, 2)) {})


/*
 * AcpiExec doesn't run the unload of the table have been processed.
 * Because of that the global objects are not forced to release. Thus,
 * if nm03, pd12 or pd13 were rewritten by the new objects during the
 * testing the outstanding allocations are reported.
 *
 * To get this known case of outstanding reports the same predictable
 * view this method could be used after completion of testing to rewrite
 * nm03, pd12 and pd13 with the same values.
 *
 * Nevertheless, these outstandings should be discussed and probably
 * eliminated by updating of AcpiExec (unload the table).
 */
Method(mfe8)
{
	mfe7(pd12, Multiply(id26, 2))
	mfe7(pd13, Multiply(id26, 2))

	Store(0, nm03)
}

/*
 * arg0 - Package
 * arg1 - number of elements in arg0
 */
Method(mfe7, 2, Serialized)
{
	Name(lpN0, 0)
	Name(lpC0, 0)

	Store(arg1, lpN0)
	Store(0, lpC0)

	While (lpN0) {

		Store(0, Index(arg0, lpC0))

		Decrement(lpN0)
		Increment(lpC0)
	}
}

/*
 * Initializing the Package with the monotone increasing Integers.
 *
 * arg0 - Package
 * arg1 - index of first element to be initialized
 * arg2 - number of elements to be initialized
 * arg3 - value to be written into first element (+1 for other)
 */
Method(mfc7, 4)
{
	While (arg2) {

		Store(arg3, Index(arg0, arg1))

		Increment(arg1)
		Increment(arg3)

		Decrement(arg2)
	}
}

/*
 * Initializing the Package with the same Integer.
 *
 * arg0 - Package
 * arg1 - index of first element to be initialized
 * arg2 - number of elements to be initialized
 * arg3 - value to be written
 */
Method(mfcd, 4)
{
	While (arg2) {

		Store(arg3, Index(arg0, arg1))
		Increment(arg1)

		Decrement(arg2)
	}
}

/*
 * Initializing the Package with IRefs.
 *
 * arg0 - (Package), IRefs to elements of this Package
 * arg1 - (Package), are stored into elements of this Package.
 * arg2 - first element inside arg0
 * arg3 - first element inside arg1
 * arg4 - number of elements to be initialized
 * arg5 - opcode of additional assignments of References (0-12):
 *        - none
 *        - to NamedX
 *        - to LocalX
 *        - to ArgX
 *
 *          Store(Index(arg0, arg2[, X0]), Index(arg1, arg3[, X1]))
 *
 *   X0       X1
 *
 *   none   , none
 *   LocalX , none
 *   ArgX   , none
 *   none   , LocalX
 *   LocalX , LocalX
 *   ArgX   , LocalX
 *   none   , ArgX
 *   LocalX , ArgX
 *  (ArgX   , ArgX) - not enough arg-variables for this
 *
 *   ************* exceptions:
 *   NamedX , none
 *   NamedX , LocalX
 *   NamedX , ArgX
 *   none   , NamedX
 *   NamedX , NamedX
 *   LocalX , NamedX
 *   ArgX   , NamedX
 *
 * arg6 - for auxiliary usage
 */
Method(mfc8, 7, Serialized)
{
	Name(i000, 0)
	Name(i001, 0)

	While (arg4) {

		Switch (ToInteger (arg5)) {

			/* (none, none) */

		Case (0) {
			Store(Index(arg0, arg2), Index(arg1, arg3))
		}

			/* (LocalX, none) */

		Case (1) {
			Index(arg0, arg2, Local0)
			Store(Local0, Index(arg1, arg3))
		}
		Case (2) {
			Store(Index(arg0, arg2, Local0), Index(arg1, arg3))
		}

			/* (ArgX, none) */

		Case (3) {
			Index(arg0, arg2, arg6)
			Store(arg6, Index(arg1, arg3))
		}
		Case (4) {
			Store(Index(arg0, arg2, arg6), Index(arg1, arg3))
		}

			/* (none, LocalX) */

		Case (5) {
			Store(Index(arg0, arg2), Index(arg1, arg3, Local0))
		}

			/* (LocalX, LocalX) */

		Case (6) {
			Index(arg0, arg2, Local0)
			Store(Local0, Index(arg1, arg3, Local1))
		}
		Case (7) {
			Store(Index(arg0, arg2, Local0), Index(arg1, arg3, Local1))
		}

			/* (ArgX, LocalX) */

		Case (8) {
			Index(arg0, arg2, arg6)
			Store(arg6, Index(arg1, arg3, Local1))
		}
		Case (9) {
			Store(Index(arg0, arg2, arg6), Index(arg1, arg3, Local1))
		}

			/* (none, ArgX) */

		Case (10) {
			Store(Index(arg0, arg2), Index(arg1, arg3, arg6))
		}

			/* (LocalX, ArgX) */

		Case (11) {
			Index(arg0, arg2, Local0)
			Store(Local0, Index(arg1, arg3, arg6))
		}
		Case (12) {
			Store(Index(arg0, arg2, Local0), Index(arg1, arg3, arg6))
		}

			/* (ArgX, ArgX) */

		Default {
			/* (none, none) */
			Store(Index(arg0, arg2), Index(arg1, arg3))
		}}

		Increment(arg2)
		Increment(arg3)

		Decrement(arg4)
	}
}

/*
 * Pack parameters for mfc6
 *
 * arg0 - opcode of additional assignments of packages Pkg0 and Pkg1
 * arg1 - different type of packages Pkg0 and Pkg1
 * arg2 - different type access through the IRefs
 * arg3 - what to do first
 * arg4 - opcode of additional assignments of References
 */
Method(mfc9, 5)
{
	And(arg0, 0x0ff, Local0)
	And(arg1, 0x0f, Local1)
	And(arg2, 0x0f, Local2)
	And(arg3, 0x0f, Local3)

	ShiftLeft(Local1, 8, Local4)
	ShiftLeft(Local2, 12, Local5)
	ShiftLeft(Local3, 16, Local6)

	Or(Local0, Local4, Local7)
	Or(Local7, Local5, Local0)
	Or(Local0, Local6, Local7)

	And(arg4, 0x0f, Local0)
	ShiftLeft(Local0, 20, Local1)
	Or(Local1, Local7, Local0)

	return (Local0)
}

/*
 * Self references.
 *
 * Different type packages
 *
 * arg0 - Package P0
 * arg1 - Package P1
 *
 * arg2 -
 *

 * 4. opcode of additional assignments of packages Pkg0 and Pkg1:
 *        Pkg0 (LocalX or ArgX or NamedX)
 *        Pkg1 (LocalX or ArgX or NamedX)
 *
 *        0       ,     ,       ;     ,     ,
 *
 *        1       ,     , Named0;     ,     , Named1
 *        2       , Arg5,       ;     ,     , Named1
 *        3   Loc4,     ,       ;     ,     , Named1
 *        4       ,     , Named0;     , Arg6,
 *        5       , Arg5,       ;     , Arg6,
 *        6   Loc4,     ,       ;     , Arg6,
 *        7       ,     , Named0; Loc5,     ,
 *        8       , Arg5,       ; Loc5,     ,
 *        9   Loc4,     ,       ; Loc5,     ,
 *
 *       10   Arg5              ; Arg5
 *       11   Loc4              ; Loc4
 *       12   Named0            ; Named0
 *
 *       13       ,     , Named0;     ,     ,
 *       14       , Arg5,       ;     ,     ,
 *       15   Loc4,     ,       ;     ,     ,
 *       16       ,     ,       ;     ,     , Named1
 *       17       ,     ,       ;     , Arg6,
 *       18       ,     ,       ; Loc5,     ,


 * 1. different type of packages Pkg0 and Pkg1:
 *        Pkg0 (P0 or p000 or pd12)
 *        Pkg1 (P1 or p001 or pd13)
 *
 *        0      ,     , pd12;   ,     , pd13
 *        1      ,     , pd12;   , p001,
 *        2      ,     , pd12; P1,     ,
 *        3      , p000,     ;   ,     , pd13
 *        4      , p000,     ;   , p001,
 *        5      , p000,     ; P1,     ,
 *        6    P0,     ,     ;   ,     , pd13
 *        7    P0,     ,     ;   , p001,
 *        8    P0,     ,     ; P1,     ,
 *        9   p000           ; p000
 *       10   pd12           ; pd12
 *       11   P0             ; P0
 *
 * 2. different type access through the IRefs
 *        1 - DerefOf()
 *            DerefOf()
 *        0 - DerefOf(DerefOf())
 *
 * 3. what to do first:
 *        1 - initializing elements of Pkg to be then accessed by references
 *        0 - or references to those elements.
 *
 *
 * arg3 - reserved
 * arg4 - reserved
 *
 * arg5 - for auxiliary usage (see comment to "additional assignments")
 * arg6 - for auxiliary usage (see comment to "additional assignments")
 */
Method(mfc6, 7, Serialized)
{
	Name(pr00, 0)
	Name(num, 0)		// half-size of Package
	Name(i000, 0xabcd0000)	// value of the first element of Package
	Name(i001, 0)
	Name(targ, 0)

	Name(b000, Buffer(1) {0})

	Name(nm00, 0)

	/* arg2 is divided to these */
	Name(AR20, 0)
	Name(AR21, 0)
	Name(AR22, 0)
	Name(AR23, 0)
	Name(AR24, 0)

	Name(lpN0, 0)
	Name(lpC0, 0)

	Store(id26, num)

	Name(p000, Package(Multiply(num, 2)) {})
	Name(p001, Package(Multiply(num, 2)) {})

	CH03("", 0, 0x000, __LINE__, 0)


	/* Unpack arg2 */

	And(arg2, 0x0ff, AR23)

	ShiftRight(arg2, 8, Local0)
	And(Local0, 0x0f, AR20)

	ShiftRight(arg2, 12, Local0)
	And(Local0, 0x0f, AR21)

	ShiftRight(arg2, 16, Local0)
	And(Local0, 0x0f, AR22)

	ShiftRight(arg2, 20, Local0)
	And(Local0, 0x0f, AR24)

	if (pr00) {

		Store(AR23, b000)
		Concatenate("mfc6: assign Pkgs ", b000, Local0)

		Store(AR24, b000)
		Concatenate(Local0, ", assign Refs ", Local1)
		Concatenate(Local1, b000, Local0)

		Store(AR20, b000)
		Concatenate(Local0, ", Pkg0/Pkg1 ", Local1)
		Concatenate(Local1, b000, Local0)

		Store(AR21, b000)
		Concatenate(Local0, ", IRef access ", Local1)
		Concatenate(Local1, b000, Local0)

		Store(AR22, b000)
		Concatenate(Local0, ", first ", Local1)
		Concatenate(Local1, b000, Local0)

		Store(Local0, Debug)
	}

	/* Identical calculations for different AR20 below */

	Switch (ToInteger (AR23)) {


	Case (0) {

	/* AR23: 0 ( , ) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		/* 0 - (pd12, pd13) */

		/* AR22 allows to change order of execution */

		if (AR22) {
			/*
			 * Initializing the first part of Package
			 */
			mfc7(pd12, 0, num, i000)
		} else {
			/*
			 * Initializing the second part of Package with IRefs
			 * to elements of its first part.
			 */
			mfc8(pd12, pd13, 0, num, num, AR24, 0)
		}

		if (AR22) {
			/*
			 * Initializing the second part of Package with IRefs
			 * to elements of its first part.
			 */
			mfc8(pd12, pd13, 0, num, num, AR24, 0)
		} else {
			/*
			 * Initializing the first part of Package
			 */
			mfc7(pd12, 0, num, i000)
		}

		Store(pd12, Local6)
		Store(pd13, Local7)
	}
	Case (1) {

		/* 1 - (pd12, p001) */

		if (AR22) {
			mfc7(pd12, 0, num, i000)
		} else {
			mfc8(pd12, p001, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(pd12, p001, 0, num, num, AR24, 0)
		} else {
			mfc7(pd12, 0, num, i000)
		}

		Store(pd12, Local6)
		Store(p001, Local7)
	}
	Case (2) {

		/* 2 - (pd12, P1) */

		if (AR22) {
			mfc7(pd12, 0, num, i000)
		} else {
			mfc8(pd12, arg1, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(pd12, arg1, 0, num, num, AR24, 0)
		} else {
			mfc7(pd12, 0, num, i000)
		}

		Store(pd12, Local6)
		Store(arg1, Local7)
	}
	Case (3) {

		/* 3 - (p000, pd13) */

		if (AR22) {
			mfc7(p000, 0, num, i000)
		} else {
			mfc8(p000, pd13, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(p000, pd13, 0, num, num, AR24, 0)
		} else {
			mfc7(p000, 0, num, i000)
		}

		Store(p000, Local6)
		Store(pd13, Local7)
	}
	Case (4) {

		/* 4 - (p000, p001) */

		if (AR22) {
			mfc7(p000, 0, num, i000)
		} else {
			mfc8(p000, p001, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(p000, p001, 0, num, num, AR24, 0)
		} else {
			mfc7(p000, 0, num, i000)
		}

		Store(p000, Local6)
		Store(p001, Local7)
	}
	Case (5) {

		/* 5 - (p000, P1) */

		if (AR22) {
			mfc7(p000, 0, num, i000)
		} else {
			mfc8(p000, arg1, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(p000, arg1, 0, num, num, AR24, 0)
		} else {
			mfc7(p000, 0, num, i000)
		}

		Store(p000, Local6)
		Store(arg1, Local7)
	}
	Case (6) {

		/* 6 - (P0,   pd13) */

		if (AR22) {
			mfc7(arg0, 0, num, i000)
		} else {
			mfc8(arg0, pd13, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg0, pd13, 0, num, num, AR24, 0)
		} else {
			mfc7(arg0, 0, num, i000)
		}

		Store(arg0, Local6)
		Store(pd13, Local7)
	}
	Case (7) {

		/* 7 - (P0,   p001) */

		if (AR22) {
			mfc7(arg0, 0, num, i000)
		} else {
			mfc8(arg0, p001, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg0, p001, 0, num, num, AR24, 0)
		} else {
			mfc7(arg0, 0, num, i000)
		}

		Store(arg0, Local6)
		Store(p001, Local7)
	}
	Case (8) {

		/* 8 - (P0,   P1) */

		if (AR22) {
			mfc7(arg0, 0, num, i000)
		} else {
			mfc8(arg0, arg1, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg0, arg1, 0, num, num, AR24, 0)
		} else {
			mfc7(arg0, 0, num, i000)
		}

		Store(arg0, Local6)
		Store(arg1, Local7)
	}
	Case (9) {

		/* 9 - (p000, p000) */

		if (AR22) {
			mfc7(p000, 0, num, i000)
		} else {
			mfc8(p000, p000, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(p000, p000, 0, num, num, AR24, 0)
		} else {
			mfc7(p000, 0, num, i000)
		}

		Store(p000, Local6)
		Store(p000, Local7)
	}
	Case (10) {

		/* 10 - (pd12, pd12) */

		if (AR22) {
			mfc7(pd12, 0, num, i000)
		} else {
			mfc8(pd12, pd12, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(pd12, pd12, 0, num, num, AR24, 0)
		} else {
			mfc7(pd12, 0, num, i000)
		}

		Store(pd12, Local6)
		Store(pd12, Local7)
	}
	Case (11) {

		/* 11 - (P0,   P0) */

		if (AR22) {
			mfc7(arg0, 0, num, i000)
		} else {
			mfc8(arg0, arg0, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg0, arg0, 0, num, num, AR24, 0)
		} else {
			mfc7(arg0, 0, num, i000)
		}

		Store(arg0, Local6)
		Store(arg0, Local7)
	}}

	} /* Case(0)/Switch(AR23) */


	Case (1) {

	/* AR23: 1 (Named0, Named1) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		CopyObject(pd12, nm00)
		CopyObject(pd13, nm03)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, nm03, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(nm03, Local7)
	}
	Case (1) {

		CopyObject(pd12, nm00)
		CopyObject(p001, nm03)

		mfc8(nm00, nm03, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(nm03, Local7)
	}
	Case (2) {

		CopyObject(pd12, nm00)
		CopyObject(arg1, nm03)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, nm03, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(nm03, Local7)
	}
	Case (3) {

		CopyObject(p000, nm00)
		CopyObject(pd13, nm03)

		mfc8(nm00, nm03, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(nm03, Local7)
	}
	Case (4) {

		CopyObject(p000, nm00)
		CopyObject(p001, nm03)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, nm03, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(nm03, Local7)
	}
	Case (5) {

		CopyObject(p000, nm00)
		CopyObject(arg1, nm03)

		mfc8(nm00, nm03, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(nm03, Local7)
	}
	Case (6) {

		CopyObject(arg0, nm00)
		CopyObject(pd13, nm03)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, nm03, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(nm03, Local7)
	}
	Case (7) {

		CopyObject(arg0, nm00)
		CopyObject(p001, nm03)

		mfc8(nm00, nm03, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(nm03, Local7)
	}
	Case (8) {

		CopyObject(arg0, nm00)
		CopyObject(arg1, nm03)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, nm03, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(nm03, Local7)
	}
	Case (9) {

		CopyObject(p000, nm00)
		CopyObject(p000, nm03)

		mfc8(nm00, nm03, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(nm03, Local7)
	}
	Case (10) {

		CopyObject(pd12, nm00)
		CopyObject(pd12, nm03)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, nm03, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(nm03, Local7)
	}
	Case (11) {

		CopyObject(arg0, nm00)
		CopyObject(arg0, nm03)

		mfc8(nm00, nm03, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(nm03, Local7)
	}}

	} /* Case(1)/Switch(AR23) */


	Case (2) {

	/* AR23: 2 (arg5, Named1) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		CopyObject(pd12, arg5)
		CopyObject(pd13, nm03)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, nm03, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(nm03, Local7)
	}
	Case (1) {

		CopyObject(pd12, arg5)
		CopyObject(p001, nm03)

		mfc8(arg5, nm03, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(nm03, Local7)
	}
	Case (2) {

		CopyObject(pd12, arg5)
		CopyObject(arg1, nm03)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, nm03, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(nm03, Local7)
	}
	Case (3) {

		CopyObject(p000, arg5)
		CopyObject(pd13, nm03)

		mfc8(arg5, nm03, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(nm03, Local7)
	}
	Case (4) {

		CopyObject(p000, arg5)
		CopyObject(p001, nm03)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, nm03, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(nm03, Local7)
	}
	Case (5) {

		CopyObject(p000, arg5)
		CopyObject(arg1, nm03)

		mfc8(arg5, nm03, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(nm03, Local7)
	}
	Case (6) {

		CopyObject(arg0, arg5)
		CopyObject(pd13, nm03)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, nm03, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(nm03, Local7)
	}
	Case (7) {

		CopyObject(arg0, arg5)
		CopyObject(p001, nm03)

		mfc8(arg5, nm03, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(nm03, Local7)
	}
	Case (8) {

		CopyObject(arg0, arg5)
		CopyObject(arg1, nm03)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, nm03, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(nm03, Local7)
	}
	Case (9) {

		CopyObject(p000, arg5)
		CopyObject(p000, nm03)

		mfc8(arg5, nm03, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(nm03, Local7)
	}
	Case (10) {

		CopyObject(pd12, arg5)
		CopyObject(pd12, nm03)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, nm03, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(nm03, Local7)
	}
	Case (11) {

		CopyObject(arg0, arg5)
		CopyObject(arg0, nm03)

		mfc8(arg5, nm03, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(nm03, Local7)
	}}

	} /* Case(2)/Switch(AR23) */


	Case (3) {

	/* AR23: 3 (Loc4, Named1) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		CopyObject(pd12, Local4)
		CopyObject(pd13, nm03)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, nm03, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(nm03, Local7)
	}
	Case (1) {

		CopyObject(pd12, Local4)
		CopyObject(p001, nm03)

		mfc8(Local4, nm03, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(nm03, Local7)
	}
	Case (2) {

		CopyObject(pd12, Local4)
		CopyObject(arg1, nm03)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, nm03, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(nm03, Local7)
	}
	Case (3) {

		CopyObject(p000, Local4)
		CopyObject(pd13, nm03)

		mfc8(Local4, nm03, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(nm03, Local7)
	}
	Case (4) {

		CopyObject(p000, Local4)
		CopyObject(p001, nm03)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, nm03, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(nm03, Local7)
	}
	Case (5) {

		CopyObject(p000, Local4)
		CopyObject(arg1, nm03)

		mfc8(Local4, nm03, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(nm03, Local7)
	}
	Case (6) {

		CopyObject(arg0, Local4)
		CopyObject(pd13, nm03)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, nm03, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(nm03, Local7)
	}
	Case (7) {

		CopyObject(arg0, Local4)
		CopyObject(p001, nm03)

		mfc8(Local4, nm03, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(nm03, Local7)
	}
	Case (8) {

		CopyObject(arg0, Local4)
		CopyObject(arg1, nm03)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, nm03, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(nm03, Local7)
	}
	Case (9) {

		CopyObject(p000, Local4)
		CopyObject(p000, nm03)

		mfc8(Local4, nm03, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(nm03, Local7)
	}
	Case (10) {

		CopyObject(pd12, Local4)
		CopyObject(pd12, nm03)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, nm03, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(nm03, Local7)
	}
	Case (11) {

		CopyObject(arg0, Local4)
		CopyObject(arg0, nm03)

		mfc8(Local4, nm03, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(nm03, Local7)
	}}

	} /* Case(3)/Switch(AR23) */


	Case (4) {

	/* AR23: 4 (Named0, Arg6) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		CopyObject(pd12, nm00)
		CopyObject(pd13, arg6)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, arg6, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(arg6, Local7)
	}
	Case (1) {

		CopyObject(pd12, nm00)
		CopyObject(p001, arg6)

		mfc8(nm00, arg6, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(arg6, Local7)
	}
	Case (2) {

		CopyObject(pd12, nm00)
		CopyObject(arg1, arg6)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, arg6, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(arg6, Local7)
	}
	Case (3) {

		CopyObject(p000, nm00)
		CopyObject(pd13, arg6)

		mfc8(nm00, arg6, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(arg6, Local7)
	}
	Case (4) {

		CopyObject(p000, nm00)
		CopyObject(p001, arg6)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, arg6, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(arg6, Local7)
	}
	Case (5) {

		CopyObject(p000, nm00)
		CopyObject(arg1, arg6)

		mfc8(nm00, arg6, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(arg6, Local7)
	}
	Case (6) {

		CopyObject(arg0, nm00)
		CopyObject(pd13, arg6)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, arg6, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(arg6, Local7)
	}
	Case (7) {

		CopyObject(arg0, nm00)
		CopyObject(p001, arg6)

		mfc8(nm00, arg6, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(arg6, Local7)
	}
	Case (8) {

		CopyObject(arg0, nm00)
		CopyObject(arg1, arg6)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, arg6, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(arg6, Local7)
	}
	Case (9) {

		CopyObject(p000, nm00)
		CopyObject(p000, arg6)

		mfc8(nm00, arg6, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(arg6, Local7)
	}
	Case (10) {

		CopyObject(pd12, nm00)
		CopyObject(pd12, arg6)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, arg6, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(arg6, Local7)
	}
	Case (11) {

		CopyObject(arg0, nm00)
		CopyObject(arg0, arg6)

		mfc8(nm00, arg6, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(arg6, Local7)
	}}

	} /* Case(4)/Switch(AR23) */


	Case (5) {

	/* AR23: 5 (Arg5, Arg6) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		CopyObject(pd12, arg5)
		CopyObject(pd13, arg6)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, arg6, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(arg6, Local7)
	}
	Case (1) {

		CopyObject(pd12, arg5)
		CopyObject(p001, arg6)

		mfc8(arg5, arg6, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(arg6, Local7)
	}
	Case (2) {

		CopyObject(pd12, arg5)
		CopyObject(arg1, arg6)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, arg6, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(arg6, Local7)
	}
	Case (3) {

		CopyObject(p000, arg5)
		CopyObject(pd13, arg6)

		mfc8(arg5, arg6, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(arg6, Local7)
	}
	Case (4) {

		CopyObject(p000, arg5)
		CopyObject(p001, arg6)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, arg6, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(arg6, Local7)
	}
	Case (5) {

		CopyObject(p000, arg5)
		CopyObject(arg1, arg6)

		mfc8(arg5, arg6, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(arg6, Local7)
	}
	Case (6) {

		CopyObject(arg0, arg5)
		CopyObject(pd13, arg6)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, arg6, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(arg6, Local7)
	}
	Case (7) {

		CopyObject(arg0, arg5)
		CopyObject(p001, arg6)

		mfc8(arg5, arg6, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(arg6, Local7)
	}
	Case (8) {

		CopyObject(arg0, arg5)
		CopyObject(arg1, arg6)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, arg6, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(arg6, Local7)
	}
	Case (9) {

		CopyObject(p000, arg5)
		CopyObject(p000, arg6)

		mfc8(arg5, arg6, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(arg6, Local7)
	}
	Case (10) {

		CopyObject(pd12, arg5)
		CopyObject(pd12, arg6)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, arg6, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(arg6, Local7)
	}
	Case (11) {

		CopyObject(arg0, arg5)
		CopyObject(arg0, arg6)

		mfc8(arg5, arg6, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(arg6, Local7)
	}}

	} /* Case(5)/Switch(AR23) */


	Case (6) {

	/* AR23: 6 (Loc4, Arg6) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		CopyObject(pd12, Local4)
		CopyObject(pd13, arg6)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, arg6, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(arg6, Local7)
	}
	Case (1) {

		CopyObject(pd12, Local4)
		CopyObject(p001, arg6)

		mfc8(Local4, arg6, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(arg6, Local7)
	}
	Case (2) {

		CopyObject(pd12, Local4)
		CopyObject(arg1, arg6)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, arg6, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(arg6, Local7)
	}
	Case (3) {

		CopyObject(p000, Local4)
		CopyObject(pd13, arg6)

		mfc8(Local4, arg6, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(arg6, Local7)
	}
	Case (4) {

		CopyObject(p000, Local4)
		CopyObject(p001, arg6)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, arg6, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(arg6, Local7)
	}
	Case (5) {

		CopyObject(p000, Local4)
		CopyObject(arg1, arg6)

		mfc8(Local4, arg6, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(arg6, Local7)
	}
	Case (6) {

		CopyObject(arg0, Local4)
		CopyObject(pd13, arg6)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, arg6, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(arg6, Local7)
	}
	Case (7) {

		CopyObject(arg0, Local4)
		CopyObject(p001, arg6)

		mfc8(Local4, arg6, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(arg6, Local7)
	}
	Case (8) {

		CopyObject(arg0, Local4)
		CopyObject(arg1, arg6)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, arg6, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(arg6, Local7)
	}
	Case (9) {

		CopyObject(p000, Local4)
		CopyObject(p000, arg6)

		mfc8(Local4, arg6, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(arg6, Local7)
	}
	Case (10) {

		CopyObject(pd12, Local4)
		CopyObject(pd12, arg6)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, arg6, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(arg6, Local7)
	}
	Case (11) {

		CopyObject(arg0, Local4)
		CopyObject(arg0, arg6)

		mfc8(Local4, arg6, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(arg6, Local7)
	}}

	} /* Case(6)/Switch(AR23) */


	Case (7) {

	/* AR23: 7 (Named0, Loc5) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		CopyObject(pd12, nm00)
		CopyObject(pd13, Local5)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, Local5, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(Local5, Local7)
	}
	Case (1) {

		CopyObject(pd12, nm00)
		CopyObject(p001, Local5)

		mfc8(nm00, Local5, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(Local5, Local7)
	}
	Case (2) {

		CopyObject(pd12, nm00)
		CopyObject(arg1, Local5)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, Local5, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(Local5, Local7)
	}
	Case (3) {

		CopyObject(p000, nm00)
		CopyObject(pd13, Local5)

		mfc8(nm00, Local5, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(Local5, Local7)
	}
	Case (4) {

		CopyObject(p000, nm00)
		CopyObject(p001, Local5)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, Local5, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(Local5, Local7)
	}
	Case (5) {

		CopyObject(p000, nm00)
		CopyObject(arg1, Local5)

		mfc8(nm00, Local5, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(Local5, Local7)
	}
	Case (6) {

		CopyObject(arg0, nm00)
		CopyObject(pd13, Local5)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, Local5, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(Local5, Local7)
	}
	Case (7) {

		CopyObject(arg0, nm00)
		CopyObject(p001, Local5)

		mfc8(nm00, Local5, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(Local5, Local7)
	}
	Case (8) {

		CopyObject(arg0, nm00)
		CopyObject(arg1, Local5)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, Local5, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(Local5, Local7)
	}
	Case (9) {

		CopyObject(p000, nm00)
		CopyObject(p000, Local5)

		mfc8(nm00, Local5, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(Local5, Local7)
	}
	Case (10) {

		CopyObject(pd12, nm00)
		CopyObject(pd12, Local5)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, Local5, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(Local5, Local7)
	}
	Case (11) {

		CopyObject(arg0, nm00)
		CopyObject(arg0, Local5)

		mfc8(nm00, Local5, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(Local5, Local7)
	}}

	} /* Case(7)/Switch(AR23) */


	Case (8) {

	/* AR23: 8 (Arg5, Loc5) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		CopyObject(pd12, arg5)
		CopyObject(pd13, Local5)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, Local5, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(Local5, Local7)
	}
	Case (1) {

		CopyObject(pd12, arg5)
		CopyObject(p001, Local5)

		mfc8(arg5, Local5, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(Local5, Local7)
	}
	Case (2) {

		CopyObject(pd12, arg5)
		CopyObject(arg1, Local5)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, Local5, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(Local5, Local7)
	}
	Case (3) {

		CopyObject(p000, arg5)
		CopyObject(pd13, Local5)

		mfc8(arg5, Local5, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(Local5, Local7)
	}
	Case (4) {

		CopyObject(p000, arg5)
		CopyObject(p001, Local5)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, Local5, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(Local5, Local7)
	}
	Case (5) {

		CopyObject(p000, arg5)
		CopyObject(arg1, Local5)

		mfc8(arg5, Local5, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(Local5, Local7)
	}
	Case (6) {

		CopyObject(arg0, arg5)
		CopyObject(pd13, Local5)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, Local5, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(Local5, Local7)
	}
	Case (7) {

		CopyObject(arg0, arg5)
		CopyObject(p001, Local5)

		mfc8(arg5, Local5, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(Local5, Local7)
	}
	Case (8) {

		CopyObject(arg0, arg5)
		CopyObject(arg1, Local5)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, Local5, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(Local5, Local7)
	}
	Case (9) {

		CopyObject(p000, arg5)
		CopyObject(p000, Local5)

		mfc8(arg5, Local5, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(Local5, Local7)
	}
	Case (10) {

		CopyObject(pd12, arg5)
		CopyObject(pd12, Local5)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, Local5, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(Local5, Local7)
	}
	Case (11) {

		CopyObject(arg0, arg5)
		CopyObject(arg0, Local5)

		mfc8(arg5, Local5, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(Local5, Local7)
	}}

	} /* Case(8)/Switch(AR23) */


	Case (9) {

	/* AR23: 9 (Loc4, Loc5) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		CopyObject(pd12, Local4)
		CopyObject(pd13, Local5)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, Local5, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(Local5, Local7)
	}
	Case (1) {

		CopyObject(pd12, Local4)
		CopyObject(p001, Local5)

		mfc8(Local4, Local5, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(Local5, Local7)
	}
	Case (2) {

		CopyObject(pd12, Local4)
		CopyObject(arg1, Local5)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, Local5, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(Local5, Local7)
	}
	Case (3) {

		CopyObject(p000, Local4)
		CopyObject(pd13, Local5)

		mfc8(Local4, Local5, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(Local5, Local7)
	}
	Case (4) {

		CopyObject(p000, Local4)
		CopyObject(p001, Local5)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, Local5, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(Local5, Local7)
	}
	Case (5) {

		CopyObject(p000, Local4)
		CopyObject(arg1, Local5)

		mfc8(Local4, Local5, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(Local5, Local7)
	}
	Case (6) {

		CopyObject(arg0, Local4)
		CopyObject(pd13, Local5)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, Local5, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(Local5, Local7)
	}
	Case (7) {

		CopyObject(arg0, Local4)
		CopyObject(p001, Local5)

		mfc8(Local4, Local5, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(Local5, Local7)
	}
	Case (8) {

		CopyObject(arg0, Local4)
		CopyObject(arg1, Local5)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, Local5, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(Local5, Local7)
	}
	Case (9) {

		CopyObject(p000, Local4)
		CopyObject(p000, Local5)

		mfc8(Local4, Local5, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(Local5, Local7)
	}
	Case (10) {

		CopyObject(pd12, Local4)
		CopyObject(pd12, Local5)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, Local5, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(Local5, Local7)
	}
	Case (11) {

		CopyObject(arg0, Local4)
		CopyObject(arg0, Local5)

		mfc8(Local4, Local5, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(Local5, Local7)
	}}

	} /* Case(9)/Switch(AR23) */


	Case (10) {

	/* AR23: 10 (Arg5, Arg5) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		CopyObject(pd12, arg5)
		CopyObject(pd13, arg5)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, arg5, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(arg5, Local7)
	}
	Case (1) {

		CopyObject(pd12, arg5)
		CopyObject(p001, arg5)

		mfc8(arg5, arg5, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(arg5, Local7)
	}
	Case (2) {

		CopyObject(pd12, arg5)
		CopyObject(arg1, arg5)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, arg5, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(arg5, Local7)
	}
	Case (3) {

		CopyObject(p000, arg5)
		CopyObject(pd13, arg5)

		mfc8(arg5, arg5, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(arg5, Local7)
	}
	Case (4) {

		CopyObject(p000, arg5)
		CopyObject(p001, arg5)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, arg5, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(arg5, Local7)
	}
	Case (5) {

		CopyObject(p000, arg5)
		CopyObject(arg1, arg5)

		mfc8(arg5, arg5, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(arg5, Local7)
	}
	Case (6) {

		CopyObject(arg0, arg5)
		CopyObject(pd13, arg5)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, arg5, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(arg5, Local7)
	}
	Case (7) {

		CopyObject(arg0, arg5)
		CopyObject(p001, arg5)

		mfc8(arg5, arg5, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(arg5, Local7)
	}
	Case (8) {

		CopyObject(arg0, arg5)
		CopyObject(arg1, arg5)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, arg5, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(arg5, Local7)
	}
	Case (9) {

		CopyObject(p000, arg5)
		CopyObject(p000, arg5)

		mfc8(arg5, arg5, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(arg5, Local7)
	}
	Case (10) {

		CopyObject(pd12, arg5)
		CopyObject(pd12, arg5)

		mfc7(arg5, 0, num, i000)
		mfc8(arg5, arg5, 0, num, num, AR24, 0)

		Store(arg5, Local6)
		Store(arg5, Local7)
	}
	Case (11) {

		CopyObject(arg0, arg5)
		CopyObject(arg0, arg5)

		mfc8(arg5, arg5, 0, num, num, AR24, 0)
		mfc7(arg5, 0, num, i000)

		Store(arg5, Local6)
		Store(arg5, Local7)
	}}

	} /* Case(10)/Switch(AR23) */


	Case (11) {

	/* AR23: 11 (Loc4, Loc4) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		CopyObject(pd12, Local4)
		CopyObject(pd13, Local4)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, Local4, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(Local4, Local7)
	}
	Case (1) {

		CopyObject(pd12, Local4)
		CopyObject(p001, Local4)

		mfc8(Local4, Local4, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(Local4, Local7)
	}
	Case (2) {

		CopyObject(pd12, Local4)
		CopyObject(arg1, Local4)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, Local4, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(Local4, Local7)
	}
	Case (3) {

		CopyObject(p000, Local4)
		CopyObject(pd13, Local4)

		mfc8(Local4, Local4, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(Local4, Local7)
	}
	Case (4) {

		CopyObject(p000, Local4)
		CopyObject(p001, Local4)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, Local4, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(Local4, Local7)
	}
	Case (5) {

		CopyObject(p000, Local4)
		CopyObject(arg1, Local4)

		mfc8(Local4, Local4, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(Local4, Local7)
	}
	Case (6) {

		CopyObject(arg0, Local4)
		CopyObject(pd13, Local4)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, Local4, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(Local4, Local7)
	}
	Case (7) {

		CopyObject(arg0, Local4)
		CopyObject(p001, Local4)

		mfc8(Local4, Local4, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(Local4, Local7)
	}
	Case (8) {

		CopyObject(arg0, Local4)
		CopyObject(arg1, Local4)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, Local4, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(Local4, Local7)
	}
	Case (9) {

		CopyObject(p000, Local4)
		CopyObject(p000, Local4)

		mfc8(Local4, Local4, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(Local4, Local7)
	}
	Case (10) {

		CopyObject(pd12, Local4)
		CopyObject(pd12, Local4)

		mfc7(Local4, 0, num, i000)
		mfc8(Local4, Local4, 0, num, num, AR24, 0)

		Store(Local4, Local6)
		Store(Local4, Local7)
	}
	Case (11) {

		CopyObject(arg0, Local4)
		CopyObject(arg0, Local4)

		mfc8(Local4, Local4, 0, num, num, AR24, 0)
		mfc7(Local4, 0, num, i000)

		Store(Local4, Local6)
		Store(Local4, Local7)
	}}

	} /* Case(11)/Switch(AR23) */


	Case (12) {

	/* AR23: 12 (Named0, Named0) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		CopyObject(pd12, nm00)
		CopyObject(pd13, nm00)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, nm00, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(nm00, Local7)
	}
	Case (1) {

		CopyObject(pd12, nm00)
		CopyObject(p001, nm00)

		mfc8(nm00, nm00, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(nm00, Local7)
	}
	Case (2) {

		CopyObject(pd12, nm00)
		CopyObject(arg1, nm00)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, nm00, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(nm00, Local7)
	}
	Case (3) {

		CopyObject(p000, nm00)
		CopyObject(pd13, nm00)

		mfc8(nm00, nm00, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(nm00, Local7)
	}
	Case (4) {

		CopyObject(p000, nm00)
		CopyObject(p001, nm00)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, nm00, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(nm00, Local7)
	}
	Case (5) {

		CopyObject(p000, nm00)
		CopyObject(arg1, nm00)

		mfc8(nm00, nm00, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(nm00, Local7)
	}
	Case (6) {

		CopyObject(arg0, nm00)
		CopyObject(pd13, nm00)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, nm00, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(nm00, Local7)
	}
	Case (7) {

		CopyObject(arg0, nm00)
		CopyObject(p001, nm00)

		mfc8(nm00, nm00, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(nm00, Local7)
	}
	Case (8) {

		CopyObject(arg0, nm00)
		CopyObject(arg1, nm00)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, nm00, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(nm00, Local7)
	}
	Case (9) {

		CopyObject(p000, nm00)
		CopyObject(p000, nm00)

		mfc8(nm00, nm00, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(nm00, Local7)
	}
	Case (10) {

		CopyObject(pd12, nm00)
		CopyObject(pd12, nm00)

		mfc7(nm00, 0, num, i000)
		mfc8(nm00, nm00, 0, num, num, AR24, 0)

		Store(nm00, Local6)
		Store(nm00, Local7)
	}
	Case (11) {

		CopyObject(arg0, nm00)
		CopyObject(arg0, nm00)

		mfc8(nm00, nm00, 0, num, num, AR24, 0)
		mfc7(nm00, 0, num, i000)

		Store(nm00, Local6)
		Store(nm00, Local7)
	}}

	} /* Case(12)/Switch(AR23) */


	Case (13) {

	/* AR23: 13 (Named0,  ) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		/* 0 - (pd12, pd13) */

		CopyObject(pd12, nm00)

		/* AR22 allows to change order of execution */

		if (AR22) {
			/*
			 * Initializing the first part of Package
			 */
			mfc7(nm00, 0, num, i000)
		} else {
			/*
			 * Initializing the second part of Package with IRefs
			 * to elements of its first part.
			 */
			mfc8(nm00, pd13, 0, num, num, AR24, 0)
		}

		if (AR22) {
			/*
			 * Initializing the second part of Package with IRefs
			 * to elements of its first part.
			 */
			mfc8(nm00, pd13, 0, num, num, AR24, 0)
		} else {
			/*
			 * Initializing the first part of Package
			 */
			mfc7(nm00, 0, num, i000)
		}

		Store(nm00, Local6)
		Store(pd13, Local7)
	}
	Case (1) {

		/* 1 - (pd12, p001) */

		CopyObject(pd12, nm00)

		if (AR22) {
			mfc7(nm00, 0, num, i000)
		} else {
			mfc8(nm00, p001, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(nm00, p001, 0, num, num, AR24, 0)
		} else {
			mfc7(nm00, 0, num, i000)
		}

		Store(nm00, Local6)
		Store(p001, Local7)
	}
	Case (2) {

		/* 2 - (pd12, P1) */

		CopyObject(pd12, nm00)

		if (AR22) {
			mfc7(nm00, 0, num, i000)
		} else {
			mfc8(nm00, arg1, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(nm00, arg1, 0, num, num, AR24, 0)
		} else {
			mfc7(nm00, 0, num, i000)
		}

		Store(nm00, Local6)
		Store(arg1, Local7)
	}
	Case (3) {

		/* 3 - (p000, pd13) */

		CopyObject(p000, nm00)

		if (AR22) {
			mfc7(nm00, 0, num, i000)
		} else {
			mfc8(nm00, pd13, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(nm00, pd13, 0, num, num, AR24, 0)
		} else {
			mfc7(nm00, 0, num, i000)
		}

		Store(nm00, Local6)
		Store(pd13, Local7)
	}
	Case (4) {

		/* 4 - (p000, p001) */

		CopyObject(p000, nm00)

		if (AR22) {
			mfc7(nm00, 0, num, i000)
		} else {
			mfc8(nm00, p001, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(nm00, p001, 0, num, num, AR24, 0)
		} else {
			mfc7(nm00, 0, num, i000)
		}

		Store(nm00, Local6)
		Store(p001, Local7)
	}
	Case (5) {

		/* 5 - (p000, P1) */

		CopyObject(p000, nm00)

		if (AR22) {
			mfc7(nm00, 0, num, i000)
		} else {
			mfc8(nm00, arg1, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(nm00, arg1, 0, num, num, AR24, 0)
		} else {
			mfc7(nm00, 0, num, i000)
		}

		Store(nm00, Local6)
		Store(arg1, Local7)
	}
	Case (6) {

		/* 6 - (P0,   pd13) */

		CopyObject(arg0, nm00)

		if (AR22) {
			mfc7(nm00, 0, num, i000)
		} else {
			mfc8(nm00, pd13, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(nm00, pd13, 0, num, num, AR24, 0)
		} else {
			mfc7(nm00, 0, num, i000)
		}

		Store(nm00, Local6)
		Store(pd13, Local7)
	}
	Case (7) {

		/* 7 - (P0,   p001) */

		CopyObject(arg0, nm00)

		if (AR22) {
			mfc7(nm00, 0, num, i000)
		} else {
			mfc8(nm00, p001, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(nm00, p001, 0, num, num, AR24, 0)
		} else {
			mfc7(nm00, 0, num, i000)
		}

		Store(nm00, Local6)
		Store(p001, Local7)
	}
	Case (8) {

		/* 8 - (P0,   P1) */

		CopyObject(arg0, nm00)

		if (AR22) {
			mfc7(nm00, 0, num, i000)
		} else {
			mfc8(nm00, arg1, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(nm00, arg1, 0, num, num, AR24, 0)
		} else {
			mfc7(nm00, 0, num, i000)
		}

		Store(nm00, Local6)
		Store(arg1, Local7)
	}
	Case (9) {

		/* 9 - (p000, p000) */

		CopyObject(p000, nm00)

		if (AR22) {
			mfc7(nm00, 0, num, i000)
		} else {
			mfc8(nm00, p000, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(nm00, p000, 0, num, num, AR24, 0)
		} else {
			mfc7(nm00, 0, num, i000)
		}

		Store(nm00, Local6)
		Store(p000, Local7)
	}
	Case (10) {

		/* 10 - (pd12, pd12) */

		CopyObject(pd12, nm00)

		if (AR22) {
			mfc7(nm00, 0, num, i000)
		} else {
			mfc8(nm00, pd12, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(nm00, pd12, 0, num, num, AR24, 0)
		} else {
			mfc7(nm00, 0, num, i000)
		}

		Store(nm00, Local6)
		Store(pd12, Local7)
	}
	Case (11) {

		/* 11 - (P0,   P0) */

		CopyObject(arg0, nm00)

		if (AR22) {
			mfc7(nm00, 0, num, i000)
		} else {
			mfc8(nm00, arg0, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(nm00, arg0, 0, num, num, AR24, 0)
		} else {
			mfc7(nm00, 0, num, i000)
		}

		Store(nm00, Local6)
		Store(arg0, Local7)
	}}

	} /* Case(13)/Switch(AR23) */


	Case (14) {

	/* AR23: 14 (Arg5,  ) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		/* 0 - (pd12, pd13) */

		CopyObject(pd12, arg5)

		/* AR22 allows to change order of execution */

		if (AR22) {
			/*
			 * Initializing the first part of Package
			 */
			mfc7(arg5, 0, num, i000)
		} else {
			/*
			 * Initializing the second part of Package with IRefs
			 * to elements of its first part.
			 */
			mfc8(arg5, pd13, 0, num, num, AR24, 0)
		}

		if (AR22) {
			/*
			 * Initializing the second part of Package with IRefs
			 * to elements of its first part.
			 */
			mfc8(arg5, pd13, 0, num, num, AR24, 0)
		} else {
			/*
			 * Initializing the first part of Package
			 */
			mfc7(arg5, 0, num, i000)
		}

		Store(arg5, Local6)
		Store(pd13, Local7)
	}
	Case (1) {

		/* 1 - (pd12, p001) */

		CopyObject(pd12, arg5)

		if (AR22) {
			mfc7(arg5, 0, num, i000)
		} else {
			mfc8(arg5, p001, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg5, p001, 0, num, num, AR24, 0)
		} else {
			mfc7(arg5, 0, num, i000)
		}

		Store(arg5, Local6)
		Store(p001, Local7)
	}
	Case (2) {

		/* 2 - (pd12, P1) */

		CopyObject(pd12, arg5)

		if (AR22) {
			mfc7(arg5, 0, num, i000)
		} else {
			mfc8(arg5, arg1, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg5, arg1, 0, num, num, AR24, 0)
		} else {
			mfc7(arg5, 0, num, i000)
		}

		Store(arg5, Local6)
		Store(arg1, Local7)
	}
	Case (3) {

		/* 3 - (p000, pd13) */

		CopyObject(p000, arg5)

		if (AR22) {
			mfc7(arg5, 0, num, i000)
		} else {
			mfc8(arg5, pd13, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg5, pd13, 0, num, num, AR24, 0)
		} else {
			mfc7(arg5, 0, num, i000)
		}

		Store(arg5, Local6)
		Store(pd13, Local7)
	}
	Case (4) {

		/* 4 - (p000, p001) */

		CopyObject(p000, arg5)

		if (AR22) {
			mfc7(arg5, 0, num, i000)
		} else {
			mfc8(arg5, p001, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg5, p001, 0, num, num, AR24, 0)
		} else {
			mfc7(arg5, 0, num, i000)
		}

		Store(arg5, Local6)
		Store(p001, Local7)
	}
	Case (5) {

		/* 5 - (p000, P1) */

		CopyObject(p000, arg5)

		if (AR22) {
			mfc7(arg5, 0, num, i000)
		} else {
			mfc8(arg5, arg1, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg5, arg1, 0, num, num, AR24, 0)
		} else {
			mfc7(arg5, 0, num, i000)
		}

		Store(arg5, Local6)
		Store(arg1, Local7)
	}
	Case (6) {

		/* 6 - (P0,   pd13) */

		CopyObject(arg0, arg5)

		if (AR22) {
			mfc7(arg5, 0, num, i000)
		} else {
			mfc8(arg5, pd13, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg5, pd13, 0, num, num, AR24, 0)
		} else {
			mfc7(arg5, 0, num, i000)
		}

		Store(arg5, Local6)
		Store(pd13, Local7)
	}
	Case (7) {

		/* 7 - (P0,   p001) */

		CopyObject(arg0, arg5)

		if (AR22) {
			mfc7(arg5, 0, num, i000)
		} else {
			mfc8(arg5, p001, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg5, p001, 0, num, num, AR24, 0)
		} else {
			mfc7(arg5, 0, num, i000)
		}

		Store(arg5, Local6)
		Store(p001, Local7)
	}
	Case (8) {

		/* 8 - (P0,   P1) */

		CopyObject(arg0, arg5)

		if (AR22) {
			mfc7(arg5, 0, num, i000)
		} else {
			mfc8(arg5, arg1, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg5, arg1, 0, num, num, AR24, 0)
		} else {
			mfc7(arg5, 0, num, i000)
		}

		Store(arg5, Local6)
		Store(arg1, Local7)
	}
	Case (9) {

		/* 9 - (p000, p000) */

		CopyObject(p000, arg5)

		if (AR22) {
			mfc7(arg5, 0, num, i000)
		} else {
			mfc8(arg5, p000, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg5, p000, 0, num, num, AR24, 0)
		} else {
			mfc7(arg5, 0, num, i000)
		}

		Store(arg5, Local6)
		Store(p000, Local7)
	}
	Case (10) {

		/* 10 - (pd12, pd12) */

		CopyObject(pd12, arg5)

		if (AR22) {
			mfc7(arg5, 0, num, i000)
		} else {
			mfc8(arg5, pd12, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg5, pd12, 0, num, num, AR24, 0)
		} else {
			mfc7(arg5, 0, num, i000)
		}

		Store(arg5, Local6)
		Store(pd12, Local7)
	}
	Case (11) {

		/* 11 - (P0,   P0) */

		CopyObject(arg0, arg5)

		if (AR22) {
			mfc7(arg5, 0, num, i000)
		} else {
			mfc8(arg5, arg0, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg5, arg0, 0, num, num, AR24, 0)
		} else {
			mfc7(arg5, 0, num, i000)
		}

		Store(arg5, Local6)
		Store(arg0, Local7)
	}}

	} /* Case(14)/Switch(AR23) */


	Case (15) {

	/* AR23: 15 (Loc4,  ) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		/* 0 - (pd12, pd13) */

		CopyObject(pd12, Local4)

		/* AR22 allows to change order of execution */

		if (AR22) {
			/*
			 * Initializing the first part of Package
			 */
			mfc7(Local4, 0, num, i000)
		} else {
			/*
			 * Initializing the second part of Package with IRefs
			 * to elements of its first part.
			 */
			mfc8(Local4, pd13, 0, num, num, AR24, 0)
		}

		if (AR22) {
			/*
			 * Initializing the second part of Package with IRefs
			 * to elements of its first part.
			 */
			mfc8(Local4, pd13, 0, num, num, AR24, 0)
		} else {
			/*
			 * Initializing the first part of Package
			 */
			mfc7(Local4, 0, num, i000)
		}

		Store(Local4, Local6)
		Store(pd13, Local7)
	}
	Case (1) {

		/* 1 - (pd12, p001) */

		CopyObject(pd12, Local4)

		if (AR22) {
			mfc7(Local4, 0, num, i000)
		} else {
			mfc8(Local4, p001, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(Local4, p001, 0, num, num, AR24, 0)
		} else {
			mfc7(Local4, 0, num, i000)
		}

		Store(Local4, Local6)
		Store(p001, Local7)
	}
	Case (2) {

		/* 2 - (pd12, P1) */

		CopyObject(pd12, Local4)

		if (AR22) {
			mfc7(Local4, 0, num, i000)
		} else {
			mfc8(Local4, arg1, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(Local4, arg1, 0, num, num, AR24, 0)
		} else {
			mfc7(Local4, 0, num, i000)
		}

		Store(Local4, Local6)
		Store(arg1, Local7)
	}
	Case (3) {

		/* 3 - (p000, pd13) */

		CopyObject(p000, Local4)

		if (AR22) {
			mfc7(Local4, 0, num, i000)
		} else {
			mfc8(Local4, pd13, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(Local4, pd13, 0, num, num, AR24, 0)
		} else {
			mfc7(Local4, 0, num, i000)
		}

		Store(Local4, Local6)
		Store(pd13, Local7)
	}
	Case (4) {

		/* 4 - (p000, p001) */

		CopyObject(p000, Local4)

		if (AR22) {
			mfc7(Local4, 0, num, i000)
		} else {
			mfc8(Local4, p001, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(Local4, p001, 0, num, num, AR24, 0)
		} else {
			mfc7(Local4, 0, num, i000)
		}

		Store(Local4, Local6)
		Store(p001, Local7)
	}
	Case (5) {

		/* 5 - (p000, P1) */

		CopyObject(p000, Local4)

		if (AR22) {
			mfc7(Local4, 0, num, i000)
		} else {
			mfc8(Local4, arg1, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(Local4, arg1, 0, num, num, AR24, 0)
		} else {
			mfc7(Local4, 0, num, i000)
		}

		Store(Local4, Local6)
		Store(arg1, Local7)
	}
	Case (6) {

		/* 6 - (P0,   pd13) */

		CopyObject(arg0, Local4)

		if (AR22) {
			mfc7(Local4, 0, num, i000)
		} else {
			mfc8(Local4, pd13, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(Local4, pd13, 0, num, num, AR24, 0)
		} else {
			mfc7(Local4, 0, num, i000)
		}

		Store(Local4, Local6)
		Store(pd13, Local7)
	}
	Case (7) {

		/* 7 - (P0,   p001) */

		CopyObject(arg0, Local4)

		if (AR22) {
			mfc7(Local4, 0, num, i000)
		} else {
			mfc8(Local4, p001, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(Local4, p001, 0, num, num, AR24, 0)
		} else {
			mfc7(Local4, 0, num, i000)
		}

		Store(Local4, Local6)
		Store(p001, Local7)
	}
	Case (8) {

		/* 8 - (P0,   P1) */

		CopyObject(arg0, Local4)

		if (AR22) {
			mfc7(Local4, 0, num, i000)
		} else {
			mfc8(Local4, arg1, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(Local4, arg1, 0, num, num, AR24, 0)
		} else {
			mfc7(Local4, 0, num, i000)
		}

		Store(Local4, Local6)
		Store(arg1, Local7)
	}
	Case (9) {

		/* 9 - (p000, p000) */

		CopyObject(p000, Local4)

		if (AR22) {
			mfc7(Local4, 0, num, i000)
		} else {
			mfc8(Local4, p000, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(Local4, p000, 0, num, num, AR24, 0)
		} else {
			mfc7(Local4, 0, num, i000)
		}

		Store(Local4, Local6)
		Store(p000, Local7)
	}
	Case (10) {

		/* 10 - (pd12, pd12) */

		CopyObject(pd12, Local4)

		if (AR22) {
			mfc7(Local4, 0, num, i000)
		} else {
			mfc8(Local4, pd12, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(Local4, pd12, 0, num, num, AR24, 0)
		} else {
			mfc7(Local4, 0, num, i000)
		}

		Store(Local4, Local6)
		Store(pd12, Local7)
	}
	Case (11) {

		/* 11 - (P0,   P0) */

		CopyObject(arg0, Local4)

		if (AR22) {
			mfc7(Local4, 0, num, i000)
		} else {
			mfc8(Local4, arg0, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(Local4, arg0, 0, num, num, AR24, 0)
		} else {
			mfc7(Local4, 0, num, i000)
		}

		Store(Local4, Local6)
		Store(arg0, Local7)
	}}

	} /* Case(15)/Switch(AR23) */


	Case (16) {

	/* AR23: 16 (  , Named1) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		/* 0 - (pd12, pd13) */

		CopyObject(pd13, nm03)

		/* AR22 allows to change order of execution */

		if (AR22) {
			/*
			 * Initializing the first part of Package
			 */
			mfc7(pd12, 0, num, i000)
		} else {
			/*
			 * Initializing the second part of Package with IRefs
			 * to elements of its first part.
			 */
			mfc8(pd12, nm03, 0, num, num, AR24, 0)
		}

		if (AR22) {
			/*
			 * Initializing the second part of Package with IRefs
			 * to elements of its first part.
			 */
			mfc8(pd12, nm03, 0, num, num, AR24, 0)
		} else {
			/*
			 * Initializing the first part of Package
			 */
			mfc7(pd12, 0, num, i000)
		}

		Store(pd12, Local6)
		Store(nm03, Local7)
	}
	Case (1) {

		/* 1 - (pd12, p001) */

		CopyObject(p001, nm03)

		if (AR22) {
			mfc7(pd12, 0, num, i000)
		} else {
			mfc8(pd12, nm03, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(pd12, nm03, 0, num, num, AR24, 0)
		} else {
			mfc7(pd12, 0, num, i000)
		}

		Store(pd12, Local6)
		Store(nm03, Local7)
	}
	Case (2) {

		/* 2 - (pd12, P1) */

		CopyObject(arg1, nm03)

		if (AR22) {
			mfc7(pd12, 0, num, i000)
		} else {
			mfc8(pd12, nm03, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(pd12, nm03, 0, num, num, AR24, 0)
		} else {
			mfc7(pd12, 0, num, i000)
		}

		Store(pd12, Local6)
		Store(nm03, Local7)
	}
	Case (3) {

		/* 3 - (p000, pd13) */

		CopyObject(pd13, nm03)

		if (AR22) {
			mfc7(p000, 0, num, i000)
		} else {
			mfc8(p000, nm03, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(p000, nm03, 0, num, num, AR24, 0)
		} else {
			mfc7(p000, 0, num, i000)
		}

		Store(p000, Local6)
		Store(nm03, Local7)
	}
	Case (4) {

		/* 4 - (p000, p001) */

		CopyObject(p001, nm03)

		if (AR22) {
			mfc7(p000, 0, num, i000)
		} else {
			mfc8(p000, nm03, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(p000, nm03, 0, num, num, AR24, 0)
		} else {
			mfc7(p000, 0, num, i000)
		}

		Store(p000, Local6)
		Store(nm03, Local7)
	}
	Case (5) {

		/* 5 - (p000, P1) */

		CopyObject(arg1, nm03)

		if (AR22) {
			mfc7(p000, 0, num, i000)
		} else {
			mfc8(p000, nm03, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(p000, nm03, 0, num, num, AR24, 0)
		} else {
			mfc7(p000, 0, num, i000)
		}

		Store(p000, Local6)
		Store(nm03, Local7)
	}
	Case (6) {

		/* 6 - (P0,   pd13) */

		CopyObject(pd13, nm03)

		if (AR22) {
			mfc7(arg0, 0, num, i000)
		} else {
			mfc8(arg0, nm03, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg0, nm03, 0, num, num, AR24, 0)
		} else {
			mfc7(arg0, 0, num, i000)
		}

		Store(arg0, Local6)
		Store(nm03, Local7)
	}
	Case (7) {

		/* 7 - (P0,   p001) */

		CopyObject(p001, nm03)

		if (AR22) {
			mfc7(arg0, 0, num, i000)
		} else {
			mfc8(arg0, nm03, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg0, nm03, 0, num, num, AR24, 0)
		} else {
			mfc7(arg0, 0, num, i000)
		}

		Store(arg0, Local6)
		Store(nm03, Local7)
	}
	Case (8) {

		/* 8 - (P0,   P1) */

		CopyObject(arg1, nm03)

		if (AR22) {
			mfc7(arg0, 0, num, i000)
		} else {
			mfc8(arg0, nm03, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg0, nm03, 0, num, num, AR24, 0)
		} else {
			mfc7(arg0, 0, num, i000)
		}

		Store(arg0, Local6)
		Store(nm03, Local7)
	}
	Case (9) {

		/* 9 - (p000, p000) */

		CopyObject(p000, nm03)

		if (AR22) {
			mfc7(p000, 0, num, i000)
		} else {
			mfc8(p000, nm03, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(p000, nm03, 0, num, num, AR24, 0)
		} else {
			mfc7(p000, 0, num, i000)
		}

		Store(p000, Local6)
		Store(nm03, Local7)
	}
	Case (10) {

		/* 10 - (pd12, pd12) */

		CopyObject(pd12, nm03)

		if (AR22) {
			mfc7(pd12, 0, num, i000)
		} else {
			mfc8(pd12, nm03, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(pd12, nm03, 0, num, num, AR24, 0)
		} else {
			mfc7(pd12, 0, num, i000)
		}

		Store(pd12, Local6)
		Store(nm03, Local7)
	}
	Case (11) {

		/* 11 - (P0,   P0) */

		CopyObject(arg0, nm03)

		if (AR22) {
			mfc7(arg0, 0, num, i000)
		} else {
			mfc8(arg0, nm03, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg0, nm03, 0, num, num, AR24, 0)
		} else {
			mfc7(arg0, 0, num, i000)
		}

		Store(arg0, Local6)
		Store(nm03, Local7)
	}}

	} /* Case(16)/Switch(AR23) */


	Case (17) {

	/* AR23: 17 (  , Arg6) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		/* 0 - (pd12, pd13) */

		CopyObject(pd13, arg6)

		/* AR22 allows to change order of execution */

		if (AR22) {
			/*
			 * Initializing the first part of Package
			 */
			mfc7(pd12, 0, num, i000)
		} else {
			/*
			 * Initializing the second part of Package with IRefs
			 * to elements of its first part.
			 */
			mfc8(pd12, arg6, 0, num, num, AR24, 0)
		}

		if (AR22) {
			/*
			 * Initializing the second part of Package with IRefs
			 * to elements of its first part.
			 */
			mfc8(pd12, arg6, 0, num, num, AR24, 0)
		} else {
			/*
			 * Initializing the first part of Package
			 */
			mfc7(pd12, 0, num, i000)
		}

		Store(pd12, Local6)
		Store(arg6, Local7)
	}
	Case (1) {

		/* 1 - (pd12, p001) */

		CopyObject(p001, arg6)

		if (AR22) {
			mfc7(pd12, 0, num, i000)
		} else {
			mfc8(pd12, arg6, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(pd12, arg6, 0, num, num, AR24, 0)
		} else {
			mfc7(pd12, 0, num, i000)
		}

		Store(pd12, Local6)
		Store(arg6, Local7)
	}
	Case (2) {

		/* 2 - (pd12, P1) */

		CopyObject(arg1, arg6)

		if (AR22) {
			mfc7(pd12, 0, num, i000)
		} else {
			mfc8(pd12, arg6, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(pd12, arg6, 0, num, num, AR24, 0)
		} else {
			mfc7(pd12, 0, num, i000)
		}

		Store(pd12, Local6)
		Store(arg6, Local7)
	}
	Case (3) {

		/* 3 - (p000, pd13) */

		CopyObject(pd13, arg6)

		if (AR22) {
			mfc7(p000, 0, num, i000)
		} else {
			mfc8(p000, arg6, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(p000, arg6, 0, num, num, AR24, 0)
		} else {
			mfc7(p000, 0, num, i000)
		}

		Store(p000, Local6)
		Store(arg6, Local7)
	}
	Case (4) {

		/* 4 - (p000, p001) */

		CopyObject(p001, arg6)

		if (AR22) {
			mfc7(p000, 0, num, i000)
		} else {
			mfc8(p000, arg6, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(p000, arg6, 0, num, num, AR24, 0)
		} else {
			mfc7(p000, 0, num, i000)
		}

		Store(p000, Local6)
		Store(arg6, Local7)
	}
	Case (5) {

		/* 5 - (p000, P1) */

		CopyObject(arg1, arg6)

		if (AR22) {
			mfc7(p000, 0, num, i000)
		} else {
			mfc8(p000, arg6, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(p000, arg6, 0, num, num, AR24, 0)
		} else {
			mfc7(p000, 0, num, i000)
		}

		Store(p000, Local6)
		Store(arg6, Local7)
	}
	Case (6) {

		/* 6 - (P0,   pd13) */

		CopyObject(pd13, arg6)

		if (AR22) {
			mfc7(arg0, 0, num, i000)
		} else {
			mfc8(arg0, arg6, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg0, arg6, 0, num, num, AR24, 0)
		} else {
			mfc7(arg0, 0, num, i000)
		}

		Store(arg0, Local6)
		Store(arg6, Local7)
	}
	Case (7) {

		/* 7 - (P0,   p001) */

		CopyObject(p001, arg6)

		if (AR22) {
			mfc7(arg0, 0, num, i000)
		} else {
			mfc8(arg0, arg6, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg0, arg6, 0, num, num, AR24, 0)
		} else {
			mfc7(arg0, 0, num, i000)
		}

		Store(arg0, Local6)
		Store(arg6, Local7)
	}
	Case (8) {

		/* 8 - (P0,   P1) */

		CopyObject(arg1, arg6)

		if (AR22) {
			mfc7(arg0, 0, num, i000)
		} else {
			mfc8(arg0, arg6, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg0, arg6, 0, num, num, AR24, 0)
		} else {
			mfc7(arg0, 0, num, i000)
		}

		Store(arg0, Local6)
		Store(arg6, Local7)
	}
	Case (9) {

		/* 9 - (p000, p000) */

		CopyObject(p000, arg6)

		if (AR22) {
			mfc7(p000, 0, num, i000)
		} else {
			mfc8(p000, arg6, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(p000, arg6, 0, num, num, AR24, 0)
		} else {
			mfc7(p000, 0, num, i000)
		}

		Store(p000, Local6)
		Store(arg6, Local7)
	}
	Case (10) {

		/* 10 - (pd12, pd12) */

		CopyObject(pd12, arg6)

		if (AR22) {
			mfc7(pd12, 0, num, i000)
		} else {
			mfc8(pd12, arg6, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(pd12, arg6, 0, num, num, AR24, 0)
		} else {
			mfc7(pd12, 0, num, i000)
		}

		Store(pd12, Local6)
		Store(arg6, Local7)
	}
	Case (11) {

		/* 11 - (P0,   P0) */

		CopyObject(arg0, arg6)

		if (AR22) {
			mfc7(arg0, 0, num, i000)
		} else {
			mfc8(arg0, arg6, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg0, arg6, 0, num, num, AR24, 0)
		} else {
			mfc7(arg0, 0, num, i000)
		}

		Store(arg0, Local6)
		Store(arg6, Local7)
	}}

	} /* Case(17)/Switch(AR23) */


	Case (18) {

	/* AR23: 18 (  , Loc5) */

	Switch (ToInteger (AR20)) {
	Case (0) {

		/* 0 - (pd12, pd13) */

		CopyObject(pd13, Local5)

		/* AR22 allows to change order of execution */

		if (AR22) {
			/*
			 * Initializing the first part of Package
			 */
			mfc7(pd12, 0, num, i000)
		} else {
			/*
			 * Initializing the second part of Package with IRefs
			 * to elements of its first part.
			 */
			mfc8(pd12, Local5, 0, num, num, AR24, 0)
		}

		if (AR22) {
			/*
			 * Initializing the second part of Package with IRefs
			 * to elements of its first part.
			 */
			mfc8(pd12, Local5, 0, num, num, AR24, 0)
		} else {
			/*
			 * Initializing the first part of Package
			 */
			mfc7(pd12, 0, num, i000)
		}

		Store(pd12, Local6)
		Store(Local5, Local7)
	}
	Case (1) {

		/* 1 - (pd12, p001) */

		CopyObject(p001, Local5)

		if (AR22) {
			mfc7(pd12, 0, num, i000)
		} else {
			mfc8(pd12, Local5, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(pd12, Local5, 0, num, num, AR24, 0)
		} else {
			mfc7(pd12, 0, num, i000)
		}

		Store(pd12, Local6)
		Store(Local5, Local7)
	}
	Case (2) {

		/* 2 - (pd12, P1) */

		CopyObject(arg1, Local5)

		if (AR22) {
			mfc7(pd12, 0, num, i000)
		} else {
			mfc8(pd12, Local5, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(pd12, Local5, 0, num, num, AR24, 0)
		} else {
			mfc7(pd12, 0, num, i000)
		}

		Store(pd12, Local6)
		Store(Local5, Local7)
	}
	Case (3) {

		/* 3 - (p000, pd13) */

		CopyObject(pd13, Local5)

		if (AR22) {
			mfc7(p000, 0, num, i000)
		} else {
			mfc8(p000, Local5, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(p000, Local5, 0, num, num, AR24, 0)
		} else {
			mfc7(p000, 0, num, i000)
		}

		Store(p000, Local6)
		Store(Local5, Local7)
	}
	Case (4) {

		/* 4 - (p000, p001) */

		CopyObject(p001, Local5)

		if (AR22) {
			mfc7(p000, 0, num, i000)
		} else {
			mfc8(p000, Local5, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(p000, Local5, 0, num, num, AR24, 0)
		} else {
			mfc7(p000, 0, num, i000)
		}

		Store(p000, Local6)
		Store(Local5, Local7)
	}
	Case (5) {

		/* 5 - (p000, P1) */

		CopyObject(arg1, Local5)

		if (AR22) {
			mfc7(p000, 0, num, i000)
		} else {
			mfc8(p000, Local5, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(p000, Local5, 0, num, num, AR24, 0)
		} else {
			mfc7(p000, 0, num, i000)
		}

		Store(p000, Local6)
		Store(Local5, Local7)
	}
	Case (6) {

		/* 6 - (P0,   pd13) */

		CopyObject(pd13, Local5)

		if (AR22) {
			mfc7(arg0, 0, num, i000)
		} else {
			mfc8(arg0, Local5, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg0, Local5, 0, num, num, AR24, 0)
		} else {
			mfc7(arg0, 0, num, i000)
		}

		Store(arg0, Local6)
		Store(Local5, Local7)
	}
	Case (7) {

		/* 7 - (P0,   p001) */

		CopyObject(p001, Local5)

		if (AR22) {
			mfc7(arg0, 0, num, i000)
		} else {
			mfc8(arg0, Local5, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg0, Local5, 0, num, num, AR24, 0)
		} else {
			mfc7(arg0, 0, num, i000)
		}

		Store(arg0, Local6)
		Store(Local5, Local7)
	}
	Case (8) {

		/* 8 - (P0,   P1) */

		CopyObject(arg1, Local5)

		if (AR22) {
			mfc7(arg0, 0, num, i000)
		} else {
			mfc8(arg0, Local5, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg0, Local5, 0, num, num, AR24, 0)
		} else {
			mfc7(arg0, 0, num, i000)
		}

		Store(arg0, Local6)
		Store(Local5, Local7)
	}
	Case (9) {

		/* 9 - (p000, p000) */

		CopyObject(p000, Local5)

		if (AR22) {
			mfc7(p000, 0, num, i000)
		} else {
			mfc8(p000, Local5, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(p000, Local5, 0, num, num, AR24, 0)
		} else {
			mfc7(p000, 0, num, i000)
		}

		Store(p000, Local6)
		Store(Local5, Local7)
	}
	Case (10) {

		/* 10 - (pd12, pd12) */

		CopyObject(pd12, Local5)

		if (AR22) {
			mfc7(pd12, 0, num, i000)
		} else {
			mfc8(pd12, Local5, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(pd12, Local5, 0, num, num, AR24, 0)
		} else {
			mfc7(pd12, 0, num, i000)
		}

		Store(pd12, Local6)
		Store(Local5, Local7)
	}
	Case (11) {

		/* 11 - (P0,   P0) */

		CopyObject(arg0, Local5)

		if (AR22) {
			mfc7(arg0, 0, num, i000)
		} else {
			mfc8(arg0, Local5, 0, num, num, AR24, 0)
		}

		if (AR22) {
			mfc8(arg0, Local5, 0, num, num, AR24, 0)
		} else {
			mfc7(arg0, 0, num, i000)
		}

		Store(arg0, Local6)
		Store(Local5, Local7)
	}}

	} /* Case(18)/Switch(AR23) */

	} /* Switch(AR23) */


	/*
	 * Verifying the contents of Package by
	 * accessing elements of its first part
	 * (monotone increasing Integers) through
	 * the IRefs of its second part.
	 */
	mfcc(Local7, num, num, i000, AR21, 0x001)

	CH03("", 0, 0x002, __LINE__, 0)
}

/*
 * Verifying the contents of Package by
 * accessing elements of its first part
 * (monotone increasing Integers) through
 * the IRefs of its second part.
 *
 * arg0 - Package to be verified
 * arg1 - index inside of Package
 * arg2 - how many elements to check
 * arg3 - expected value of the first element of Package
 * arg4 - type of access through the IRefs
 * arg5 - index of error (inside the file)
 */
Method(mfcc, 6, Serialized)
{
	Name(lpN0, 0)
	Name(lpC0, 0)

	Name(i000, 0)
	Name(targ, 0)

	Store(arg2, lpN0)
	Store(0, lpC0)

	Store(arg1, targ)
	Store(arg3, i000)

	While (lpN0) {

		Store(Index(arg0, targ), Local0)

		if (arg4) {
			Store(DerefOf(Local0), Local1)
			Store(DerefOf(Local1), Local2)
		} else {
			Store(DerefOf(DerefOf(Local0)), Local2)
		}

		if (LNotEqual(Local2, i000)) {
			err("", zFFF, __LINE__, 0, 0, Local2, i000)
		}

		Increment(i000)
		Increment(targ)

		Decrement(lpN0)
		Increment(lpC0)
	}
}

/*
 * Verifying the contents of Package by
 * accessing elements of its first part
 * through the IRefs of its second part.
 * All IRefs points to the same element.
 *
 * arg0 - Package to be verified
 * arg1 - index inside of Package
 * arg2 - how many elements to check
 * arg3 - expected value of element
 * arg4 - type of access through the IRefs
 * arg5 - index of error (inside the file)
 */
Method(mfce, 6, Serialized)
{
	Name(lpN0, 0)
	Name(lpC0, 0)
	Name(targ, 0)

	Store(arg2, lpN0)
	Store(0, lpC0)

	Store(arg1, targ)

	While (lpN0) {

		Store(Index(arg0, targ), Local0)

		if (arg4) {
			Store(DerefOf(Local0), Local1)
			Store(DerefOf(Local1), Local2)
		} else {
			Store(DerefOf(DerefOf(Local0)), Local2)
		}

		if (LNotEqual(Local2, arg3)) {
			err("", zFFF, __LINE__, 0, 0, Local2, arg3)
		}

		Increment(targ)

		Decrement(lpN0)
		Increment(lpC0)
	}
}

/*
 * Verifying the contents of value pointed to by Reference.
 *
 * arg0 - Index reference
 * arg1 - expected value of element
 * arg2 - index of error (inside the file)
 */
Method(mfd8, 3)
{
	Store(DerefOf(arg0), Local0)

	if (LNotEqual(Local0, arg1)) {
		err("", zFFF, __LINE__, 0, 0, Local0, arg1)
	}
}
