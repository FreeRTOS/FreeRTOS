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
 * Method execution control
 *
 * While, Break, Continue operators
 *
 * DESCRIPTION:
 *
 * The main test method consists of 50 enclosed While operators
 * of identical structure. Each While should perform prescribed
 * number of Continue and Break operators and also execute the
 * child operator While so many times which are necessary to
 * fulfill the tasks of that child.
 *
 * The number of levels to be traveled may be
 * restricted by tvl0 variable in the range {1,50}.
 *
 * After completion of the test method the verification is performed
 * which checks that each level While actually produced the specified
 * number of Continue and Break operators (specified by p001) and
 * handled its child.
 *
 * Set up the pr00 variable to turn on the debug information.
 *
 * Calculation depends on the values of the following variables:
 *
 *    tvl0 - the number of While operators to be traveled
 *    nnXX - repetition on WhileXX on each iteration
 *    iiXX - first element in sequence of works
 *           {0 - Run Child, 1 - Do Continue, 2 - Do Break}
 *
 * See also comment to nn00 below.
 */

Name(z074, 74)

// Debug information
Name(pr00, 0)

/*
 * The number of While operators to be traveled.
 * Maximal possible is equal to 50 (restricted by
 * the test (not ACPI) - implemented for 50 only).
 */
Name(tvl0, 50)

// Relative indexes of Buffers of counters of works
Name(CHL0, 0) // children (my children have done all)
Name(CNT0, 1) // Continue (I have done running continue)
Name(BRK0, 2) // Break    (I have done running break)

// Increment the counter of work
// arg0 - trace of repetition Package
// arg1 - index of Buffer in Package
// arg2 - (level) index of element in Buffer
Method(m0f2, 3)
{
	if (pr00) {
		Store("???", Local0)
		Switch (arg1) {
			case (0) {
				Store("Child    ", Local0)
			}
			case (1) {
				Store("Continue ", Local0)
			}
			case (2) {
				Store("Break    ", Local0)
			}
			Default {
				Store("???      ", Local0)
			}
		}
		Store(Concatenate(Local0, arg2), Debug)
	}

	Store(DerefOf(Index(DerefOf(Index(arg0, arg1)), arg2)), Local0)
	Increment(Local0)
	Store(Local0, Index(DerefOf(Index(arg0, arg1)), arg2))
}

// Set given value to counter of work
// arg0 - trace of repetition Package
// arg1 - index of Buffer in Package
// arg2 - (level) index of element in Buffer
Method(m0f3, 4)
{
	Store(arg3, Index(DerefOf(Index(arg0, arg1)), arg2))
}

// Return the counter of work
// arg0 - trace of repetition Package
// arg1 - index of Buffer in Package
// arg2 - (level) index of element in Buffer
Method(m0f4, 3)
{
	Store(DerefOf(Index(DerefOf(Index(arg0, arg1)), arg2)), Local0)
	return (Local0)
}

// Return status of level
// arg0 - trace of repetition Package
// arg1 - task of repetition Package
// arg2 - (level) index of element in Buffer
Method(m0f5, 3)
{
	Store(0, Local0)

	if (m0f4(arg0, CHL0, arg2)) {
		Or(Local0, 0x01, Local0)
	}

	Store(m0f4(arg0, CNT0, arg2), Local1)
	Store(m0f4(arg1, CNT0, arg2), Local2)
	if (LGreaterEqual(Local1, Local2)) {
		Or(Local0, 0x02, Local0)
	}

	Store(m0f4(arg0, BRK0, arg2), Local1)
	Store(m0f4(arg1, BRK0, arg2), Local2)
	if (LGreaterEqual(Local1, Local2)) {
		Or(Local0, 0x04, Local0)
	}

	return (Local0)
}

// Print all Buffers of Package
Method(m0f6, 1)
{
	Store(DerefOf(Index(arg0, CHL0)), Debug)
	Store(DerefOf(Index(arg0, CNT0)), Debug)
	Store(DerefOf(Index(arg0, BRK0)), Debug)
}

// Conditional printing
Method(m0f7, 1)
{
	if (pr00) {
		Store(Arg0, Debug)
	}
}

// Verification of run
// arg0 - name of test
// arg1 - trace of repetition Package
// arg2 - task of repetition Package
// arg3 - number of levels
Method(m0f8, 4, Serialized)
{
	Name(lpN0, 0)
	Name(lpC0, 0)

	// Children

	Store(arg3, lpN0)
	Store(0, lpC0)

	While (lpN0) {

		Store(m0f4(arg1, CHL0, lpC0), Local0)

		if (LEqual(Local0, 0)) {
			err(arg0, z074, __LINE__, 0, 0, 0, lpC0)
		}

		Decrement(lpN0)
		Increment(lpC0)
	}

	// Continue

	Store(arg3, lpN0)
	Store(0, lpC0)

	While (lpN0) {

		Store(m0f4(arg1, CNT0, lpC0), Local0)
		Store(m0f4(arg2, CNT0, lpC0), Local1)

		if (LNotEqual(Local0, Local1)) {
			err(arg0, z074, __LINE__, 0, 0, Local0, Local1)
		}

		Decrement(lpN0)
		Increment(lpC0)
	}

	// Break

	Store(arg3, lpN0)
	Store(0, lpC0)

	While (lpN0) {

		Store(m0f4(arg1, BRK0, lpC0), Local0)
		Store(m0f4(arg2, BRK0, lpC0), Local1)

		if (LNotEqual(Local0, Local1)) {
			err(arg0, z074, __LINE__, 0, 0, Local0, Local1)
		}

		Decrement(lpN0)
		Increment(lpC0)
	}
}

// Mix consecution of works
// arg0 - current flag of Run
// arg1 - current flag of Continue
// arg2 - current flag of Break
// arg3 - current index
Method(m0f9, 4)
{
	Store(0, Local0)

	if (arg0) {
		Or(Local0, 0x01, Local0)
	}
	if (arg1) {
		Or(Local0, 0x02, Local0)
	}
	if (arg2) {
		Or(Local0, 0x04, Local0)
	}

	Mod(arg3, 3, Local1)

	Store(0, Local7)

	if (LEqual(Local1, 0)) {
		And(Local0, 0x01, Local7)
	} elseif (LEqual(Local1, 0)) {
		And(Local0, 0x02, Local7)
	} else {
		And(Local0, 0x04, Local7)
	}

	// Some iterations may be empty
	// even for non-empty Arg-s.

	return (Local0)
}

// The test
// arg0 - name of test
// arg1 - the number of While operators to be traveled
Method(m0fa, 2, Serialized)
{
	Concatenate("The number of While operators to be traveled: ", arg1, Local0)
	Store(Local0, Debug)

	if (LEqual(arg1, 0)) {
		err(arg0, z074, __LINE__, 0, 0, 0, 0)
	}

	Add(arg1, 1, Local0)

	// Trace of repetition Package
	Name(p000, Package() {
		Buffer(Local0) {}, // 0 - Children (my children have done all)
		Buffer(Local0) {}, // 1 - Continue (I have done running continue)
		Buffer(Local0) {}, // 2 - Break    (I have done running break)
	})

	// Task of repetition Package
	Name(p001, Package() {
		0,                // 0 - Children (my children have done all)
		Buffer(Local0) {  // 1 - Continue (I have done running continue)
			1,2,3,4,5,6,7,8,9,10,
			11,12,13,14,15,16,17,18,19,20,
			19,18,17,16,15,14,13,12,11,10,
			9,8,7,6,5,4,3,2,1,2,
			1,
			},
		Buffer(Local0) {  // 2 - Break    (I have done running break)
			1,2,3,4,5,6,7,8,9,8,
			7,6,5,4,3,2,1,2,3,4,
			5,6,7,8,9,8,7,6,5,4,
			3,2,1,2,3,4,5,6,7,8,
			1,
			}
	})

	// The last While has no children, so mark him
	// "no works of his children remained".

	m0f3(p000, CHL0, arg1, 1)

	Store(m0f4(p001, CNT0, arg1), Local0)
	m0f3(p000, CNT0, arg1, Local0)

	Store(m0f4(p001, BRK0, arg1), Local0)
	m0f3(p000, BRK0, arg1, Local0)

	// ////////////////
	// Enclosed Whiles
	//
	// Code of one While differs others
	// by the following variables:
	//
	//	lc0x - this level
	//	ln0x - next level
	//	c00x - flag of Continue
	//	b00x - flag of Break
	//	i00x - current index of iteration
	//	n00x - number of iterations
	// ////////////////

	/*
	 * Calculation depends on all these nnXX below.
	 *
	 * nn00 is not a constant just in case only to prevent
	 * infinitive loop in testing due to any mistake in
	 * implementation.
	 *
	 * For the proposed in test contents of p001 and tvl0
	 * equal t0 50 the strict needed value of nn00 is 18449.
	 */
	Name(nn00, 18449)
	Name(nn01, 1)
	Name(nn02, 1)
	Name(nn03, 1)
	Name(nn04, 1)
	Name(nn05, 1)
	Name(nn06, 1)
	Name(nn07, 1)
	Name(nn08, 1)
	Name(nn09, 1)
	Name(nn10, 1)
	Name(nn11, 1)
	Name(nn12, 1)
	Name(nn13, 1)
	Name(nn14, 1)
	Name(nn15, 1)
	Name(nn16, 1)
	Name(nn17, 1)
	Name(nn18, 1)
	Name(nn19, 1)
	Name(nn20, 1)
	Name(nn21, 1)
	Name(nn22, 1)
	Name(nn23, 1)
	Name(nn24, 1)
	Name(nn25, 1)
	Name(nn26, 1)
	Name(nn27, 1)
	Name(nn28, 1)
	Name(nn29, 1)
	Name(nn30, 1)
	Name(nn31, 1)
	Name(nn32, 1)
	Name(nn33, 1)
	Name(nn34, 1)
	Name(nn35, 1)
	Name(nn36, 1)
	Name(nn37, 1)
	Name(nn38, 1)
	Name(nn39, 1)
	Name(nn40, 1)
	Name(nn41, 1)
	Name(nn42, 1)
	Name(nn43, 1)
	Name(nn44, 1)
	Name(nn45, 1)
	Name(nn46, 1)
	Name(nn47, 1)
	Name(nn48, 1)
	Name(nn49, 1)

	// Calculation depends on these iiXX:
	Name(ii01, 1)
	Name(ii02, 2)
	Name(ii03, 0)
	Name(ii04, 1)
	Name(ii05, 2)
	Name(ii06, 0)
	Name(ii07, 1)
	Name(ii08, 2)
	Name(ii09, 0)
	Name(ii10, 1)
	Name(ii11, 2)
	Name(ii12, 0)
	Name(ii13, 1)
	Name(ii14, 2)
	Name(ii15, 0)
	Name(ii16, 1)
	Name(ii17, 2)
	Name(ii18, 0)
	Name(ii19, 1)
	Name(ii20, 2)
	Name(ii21, 0)
	Name(ii22, 1)
	Name(ii23, 2)
	Name(ii24, 0)
	Name(ii25, 1)
	Name(ii26, 2)
	Name(ii27, 0)
	Name(ii28, 1)
	Name(ii29, 2)
	Name(ii30, 0)
	Name(ii31, 1)
	Name(ii32, 2)
	Name(ii33, 0)
	Name(ii34, 1)
	Name(ii35, 2)
	Name(ii36, 0)
	Name(ii37, 1)
	Name(ii38, 2)
	Name(ii39, 0)
	Name(ii40, 1)
	Name(ii41, 2)
	Name(ii42, 0)
	Name(ii43, 1)
	Name(ii44, 2)
	Name(ii45, 0)
	Name(ii46, 1)
	Name(ii47, 2)
	Name(ii48, 0)
	Name(ii49, 1)

	// Variables

	Name(lc00, 0)
	Name(ln00, 1)
	Name(c000, 0)
	Name(b000, 0)
	Name(r000, 0)
	Name(i000, 0)
	Name(n000, 0)

	Name(lc01, 1)
	Name(ln01, 2)
	Name(c001, 0)
	Name(b001, 0)
	Name(r001, 0)
	Name(i001, 0)
	Name(n001, 0)

	Name(lc02, 2)
	Name(ln02, 3)
	Name(c002, 0)
	Name(b002, 0)
	Name(r002, 0)
	Name(i002, 0)
	Name(n002, 0)

	Name(lc03, 3)
	Name(ln03, 4)
	Name(c003, 0)
	Name(b003, 0)
	Name(r003, 0)
	Name(i003, 0)
	Name(n003, 0)

	Name(lc04, 4)
	Name(ln04, 5)
	Name(c004, 0)
	Name(b004, 0)
	Name(r004, 0)
	Name(i004, 0)
	Name(n004, 0)

	Name(lc05, 5)
	Name(ln05, 6)
	Name(c005, 0)
	Name(b005, 0)
	Name(r005, 0)
	Name(i005, 0)
	Name(n005, 0)

	Name(lc06, 6)
	Name(ln06, 7)
	Name(c006, 0)
	Name(b006, 0)
	Name(r006, 0)
	Name(i006, 0)
	Name(n006, 0)

	Name(lc07, 7)
	Name(ln07, 8)
	Name(c007, 0)
	Name(b007, 0)
	Name(r007, 0)
	Name(i007, 0)
	Name(n007, 0)

	Name(lc08, 8)
	Name(ln08, 9)
	Name(c008, 0)
	Name(b008, 0)
	Name(r008, 0)
	Name(i008, 0)
	Name(n008, 0)

	Name(lc09, 9)
	Name(ln09, 10)
	Name(c009, 0)
	Name(b009, 0)
	Name(r009, 0)
	Name(i009, 0)
	Name(n009, 0)

	Name(lc10, 10)
	Name(ln10, 11)
	Name(c010, 0)
	Name(b010, 0)
	Name(r010, 0)
	Name(i010, 0)
	Name(n010, 0)

	Name(lc11, 11)
	Name(ln11, 12)
	Name(c011, 0)
	Name(b011, 0)
	Name(r011, 0)
	Name(i011, 0)
	Name(n011, 0)

	Name(lc12, 12)
	Name(ln12, 13)
	Name(c012, 0)
	Name(b012, 0)
	Name(r012, 0)
	Name(i012, 0)
	Name(n012, 0)

	Name(lc13, 13)
	Name(ln13, 14)
	Name(c013, 0)
	Name(b013, 0)
	Name(r013, 0)
	Name(i013, 0)
	Name(n013, 0)

	Name(lc14, 14)
	Name(ln14, 15)
	Name(c014, 0)
	Name(b014, 0)
	Name(r014, 0)
	Name(i014, 0)
	Name(n014, 0)

	Name(lc15, 15)
	Name(ln15, 16)
	Name(c015, 0)
	Name(b015, 0)
	Name(r015, 0)
	Name(i015, 0)
	Name(n015, 0)

	Name(lc16, 16)
	Name(ln16, 17)
	Name(c016, 0)
	Name(b016, 0)
	Name(r016, 0)
	Name(i016, 0)
	Name(n016, 0)

	Name(lc17, 17)
	Name(ln17, 18)
	Name(c017, 0)
	Name(b017, 0)
	Name(r017, 0)
	Name(i017, 0)
	Name(n017, 0)

	Name(lc18, 18)
	Name(ln18, 19)
	Name(c018, 0)
	Name(b018, 0)
	Name(r018, 0)
	Name(i018, 0)
	Name(n018, 0)

	Name(lc19, 19)
	Name(ln19, 20)
	Name(c019, 0)
	Name(b019, 0)
	Name(r019, 0)
	Name(i019, 0)
	Name(n019, 0)

	Name(lc20, 20)
	Name(ln20, 21)
	Name(c020, 0)
	Name(b020, 0)
	Name(r020, 0)
	Name(i020, 0)
	Name(n020, 0)

	Name(lc21, 21)
	Name(ln21, 22)
	Name(c021, 0)
	Name(b021, 0)
	Name(r021, 0)
	Name(i021, 0)
	Name(n021, 0)

	Name(lc22, 22)
	Name(ln22, 23)
	Name(c022, 0)
	Name(b022, 0)
	Name(r022, 0)
	Name(i022, 0)
	Name(n022, 0)

	Name(lc23, 23)
	Name(ln23, 24)
	Name(c023, 0)
	Name(b023, 0)
	Name(r023, 0)
	Name(i023, 0)
	Name(n023, 0)

	Name(lc24, 24)
	Name(ln24, 25)
	Name(c024, 0)
	Name(b024, 0)
	Name(r024, 0)
	Name(i024, 0)
	Name(n024, 0)

	Name(lc25, 25)
	Name(ln25, 26)
	Name(c025, 0)
	Name(b025, 0)
	Name(r025, 0)
	Name(i025, 0)
	Name(n025, 0)

	Name(lc26, 26)
	Name(ln26, 27)
	Name(c026, 0)
	Name(b026, 0)
	Name(r026, 0)
	Name(i026, 0)
	Name(n026, 0)

	Name(lc27, 27)
	Name(ln27, 28)
	Name(c027, 0)
	Name(b027, 0)
	Name(r027, 0)
	Name(i027, 0)
	Name(n027, 0)

	Name(lc28, 28)
	Name(ln28, 29)
	Name(c028, 0)
	Name(b028, 0)
	Name(r028, 0)
	Name(i028, 0)
	Name(n028, 0)

	Name(lc29, 29)
	Name(ln29, 30)
	Name(c029, 0)
	Name(b029, 0)
	Name(r029, 0)
	Name(i029, 0)
	Name(n029, 0)

	Name(lc30, 30)
	Name(ln30, 31)
	Name(c030, 0)
	Name(b030, 0)
	Name(r030, 0)
	Name(i030, 0)
	Name(n030, 0)

	Name(lc31, 31)
	Name(ln31, 32)
	Name(c031, 0)
	Name(b031, 0)
	Name(r031, 0)
	Name(i031, 0)
	Name(n031, 0)

	Name(lc32, 32)
	Name(ln32, 33)
	Name(c032, 0)
	Name(b032, 0)
	Name(r032, 0)
	Name(i032, 0)
	Name(n032, 0)

	Name(lc33, 33)
	Name(ln33, 34)
	Name(c033, 0)
	Name(b033, 0)
	Name(r033, 0)
	Name(i033, 0)
	Name(n033, 0)

	Name(lc34, 34)
	Name(ln34, 35)
	Name(c034, 0)
	Name(b034, 0)
	Name(r034, 0)
	Name(i034, 0)
	Name(n034, 0)

	Name(lc35, 35)
	Name(ln35, 36)
	Name(c035, 0)
	Name(b035, 0)
	Name(r035, 0)
	Name(i035, 0)
	Name(n035, 0)

	Name(lc36, 36)
	Name(ln36, 37)
	Name(c036, 0)
	Name(b036, 0)
	Name(r036, 0)
	Name(i036, 0)
	Name(n036, 0)

	Name(lc37, 37)
	Name(ln37, 38)
	Name(c037, 0)
	Name(b037, 0)
	Name(r037, 0)
	Name(i037, 0)
	Name(n037, 0)

	Name(lc38, 38)
	Name(ln38, 39)
	Name(c038, 0)
	Name(b038, 0)
	Name(r038, 0)
	Name(i038, 0)
	Name(n038, 0)

	Name(lc39, 39)
	Name(ln39, 40)
	Name(c039, 0)
	Name(b039, 0)
	Name(r039, 0)
	Name(i039, 0)
	Name(n039, 0)

	Name(lc40, 40)
	Name(ln40, 41)
	Name(c040, 0)
	Name(b040, 0)
	Name(r040, 0)
	Name(i040, 0)
	Name(n040, 0)

	Name(lc41, 41)
	Name(ln41, 42)
	Name(c041, 0)
	Name(b041, 0)
	Name(r041, 0)
	Name(i041, 0)
	Name(n041, 0)

	Name(lc42, 42)
	Name(ln42, 43)
	Name(c042, 0)
	Name(b042, 0)
	Name(r042, 0)
	Name(i042, 0)
	Name(n042, 0)

	Name(lc43, 43)
	Name(ln43, 44)
	Name(c043, 0)
	Name(b043, 0)
	Name(r043, 0)
	Name(i043, 0)
	Name(n043, 0)

	Name(lc44, 44)
	Name(ln44, 45)
	Name(c044, 0)
	Name(b044, 0)
	Name(r044, 0)
	Name(i044, 0)
	Name(n044, 0)

	Name(lc45, 45)
	Name(ln45, 46)
	Name(c045, 0)
	Name(b045, 0)
	Name(r045, 0)
	Name(i045, 0)
	Name(n045, 0)

	Name(lc46, 46)
	Name(ln46, 47)
	Name(c046, 0)
	Name(b046, 0)
	Name(r046, 0)
	Name(i046, 0)
	Name(n046, 0)

	Name(lc47, 47)
	Name(ln47, 48)
	Name(c047, 0)
	Name(b047, 0)
	Name(r047, 0)
	Name(i047, 0)
	Name(n047, 0)

	Name(lc48, 48)
	Name(ln48, 49)
	Name(c048, 0)
	Name(b048, 0)
	Name(r048, 0)
	Name(i048, 0)
	Name(n048, 0)

	Name(lc49, 49)
	Name(ln49, 50)
	Name(c049, 0)
	Name(b049, 0)
	Name(r049, 0)
	Name(i049, 0)
	Name(n049, 0)

	////////////////////////////////////////////////////////////// START, 00

	Store(0, c000)
	Store(0, b000)
	Store(0, r000)
	Store(0, i000)
	Store(nn00, n000)

	While (n000) {

		m0f7("n000")

		Store(m0f5(p000, p001, ln00), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc00)
			Store(0, r000)
		} else {
			Store(1, r000)
		}

		Store(m0f5(p000, p001, lc00), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c000)
		} else {
			Store(1, c000)
		}
		if (And(Local0, 0x04)) {
			Store(0, b000)
		} else {
			// Don't break there from 0-th While
			Store(0, b000)
			m0f2(p000, BRK0, lc00)
		}

		// Don't use these variables below
		Decrement(n000)
		Increment(i000)

		////////////////////////// Actions

		if (r000) {
			m0f7("r000")

	////////////////////////////////////////////////////////////// START, 01

	Store(0, c001)
	Store(0, b001)
	Store(0, r001)
	Store(0, i001)
	Store(nn01, n001)

	While (n001) {

		m0f7("n001")

		Store(m0f5(p000, p001, ln01), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc01)
			Store(0, r001)
		} else {
			Store(1, r001)
		}

		Store(m0f5(p000, p001, lc01), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c001)
		} else {
			Store(1, c001)
		}
		if (And(Local0, 0x04)) {
			Store(0, b001)
		} else {
			Store(1, b001)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r001, c001, b001, ii01), Local0)
		Increment(ii01)
		Store(0, r001)
		Store(0, c001)
		Store(0, b001)
		if (And(Local0, 0x01)) {
			Store(1, r001)
		} elseif (And(Local0, 0x02)) {
			Store(1, c001)
		} elseif (And(Local0, 0x04)) {
			Store(1, b001)
		}

		// Don't use these variables below
		Decrement(n001)
		Increment(i001)

		////////////////////////// Actions

		if (r001) {
			m0f7("r001")

	////////////////////////////////////////////////////////////// START, 02

	Store(0, c002)
	Store(0, b002)
	Store(0, r002)
	Store(0, i002)
	Store(nn02, n002)

	While (n002) {

		m0f7("n002")

		Store(m0f5(p000, p001, ln02), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc02)
			Store(0, r002)
		} else {
			Store(1, r002)
		}

		Store(m0f5(p000, p001, lc02), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c002)
		} else {
			Store(1, c002)
		}
		if (And(Local0, 0x04)) {
			Store(0, b002)
		} else {
			Store(1, b002)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r002, c002, b002, ii02), Local0)
		Increment(ii02)
		Store(0, r002)
		Store(0, c002)
		Store(0, b002)
		if (And(Local0, 0x01)) {
			Store(1, r002)
		} elseif (And(Local0, 0x02)) {
			Store(1, c002)
		} elseif (And(Local0, 0x04)) {
			Store(1, b002)
		}

		// Don't use these variables below
		Decrement(n002)
		Increment(i002)

		////////////////////////// Actions

		if (r002) {
			m0f7("r002")

	////////////////////////////////////////////////////////////// START, 03

	Store(0, c003)
	Store(0, b003)
	Store(0, r003)
	Store(0, i003)
	Store(nn03, n003)

	While (n003) {

		m0f7("n003")

		Store(m0f5(p000, p001, ln03), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc03)
			Store(0, r003)
		} else {
			Store(1, r003)
		}

		Store(m0f5(p000, p001, lc03), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c003)
		} else {
			Store(1, c003)
		}
		if (And(Local0, 0x04)) {
			Store(0, b003)
		} else {
			Store(1, b003)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r003, c003, b003, ii03), Local0)
		Increment(ii03)
		Store(0, r003)
		Store(0, c003)
		Store(0, b003)
		if (And(Local0, 0x01)) {
			Store(1, r003)
		} elseif (And(Local0, 0x02)) {
			Store(1, c003)
		} elseif (And(Local0, 0x04)) {
			Store(1, b003)
		}

		// Don't use these variables below
		Decrement(n003)
		Increment(i003)

		////////////////////////// Actions

		if (r003) {
			m0f7("r003")

	////////////////////////////////////////////////////////////// START, 04

	Store(0, c004)
	Store(0, b004)
	Store(0, r004)
	Store(0, i004)
	Store(nn04, n004)

	While (n004) {

		m0f7("n004")

		Store(m0f5(p000, p001, ln04), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc04)
			Store(0, r004)
		} else {
			Store(1, r004)
		}

		Store(m0f5(p000, p001, lc04), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c004)
		} else {
			Store(1, c004)
		}
		if (And(Local0, 0x04)) {
			Store(0, b004)
		} else {
			Store(1, b004)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r004, c004, b004, ii04), Local0)
		Increment(ii04)
		Store(0, r004)
		Store(0, c004)
		Store(0, b004)
		if (And(Local0, 0x01)) {
			Store(1, r004)
		} elseif (And(Local0, 0x02)) {
			Store(1, c004)
		} elseif (And(Local0, 0x04)) {
			Store(1, b004)
		}

		// Don't use these variables below
		Decrement(n004)
		Increment(i004)

		////////////////////////// Actions

		if (r004) {
			m0f7("r004")

	////////////////////////////////////////////////////////////// START, 05

	Store(0, c005)
	Store(0, b005)
	Store(0, r005)
	Store(0, i005)
	Store(nn05, n005)

	While (n005) {

		m0f7("n005")

		Store(m0f5(p000, p001, ln05), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc05)
			Store(0, r005)
		} else {
			Store(1, r005)
		}

		Store(m0f5(p000, p001, lc05), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c005)
		} else {
			Store(1, c005)
		}
		if (And(Local0, 0x04)) {
			Store(0, b005)
		} else {
			Store(1, b005)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r005, c005, b005, ii05), Local0)
		Increment(ii05)
		Store(0, r005)
		Store(0, c005)
		Store(0, b005)
		if (And(Local0, 0x01)) {
			Store(1, r005)
		} elseif (And(Local0, 0x02)) {
			Store(1, c005)
		} elseif (And(Local0, 0x04)) {
			Store(1, b005)
		}

		// Don't use these variables below
		Decrement(n005)
		Increment(i005)

		////////////////////////// Actions

		if (r005) {
			m0f7("r005")

	////////////////////////////////////////////////////////////// START, 06

	Store(0, c006)
	Store(0, b006)
	Store(0, r006)
	Store(0, i006)
	Store(nn06, n006)

	While (n006) {

		m0f7("n006")

		Store(m0f5(p000, p001, ln06), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc06)
			Store(0, r006)
		} else {
			Store(1, r006)
		}

		Store(m0f5(p000, p001, lc06), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c006)
		} else {
			Store(1, c006)
		}
		if (And(Local0, 0x04)) {
			Store(0, b006)
		} else {
			Store(1, b006)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r006, c006, b006, ii06), Local0)
		Increment(ii06)
		Store(0, r006)
		Store(0, c006)
		Store(0, b006)
		if (And(Local0, 0x01)) {
			Store(1, r006)
		} elseif (And(Local0, 0x02)) {
			Store(1, c006)
		} elseif (And(Local0, 0x04)) {
			Store(1, b006)
		}

		// Don't use these variables below
		Decrement(n006)
		Increment(i006)

		////////////////////////// Actions

		if (r006) {
			m0f7("r006")

	////////////////////////////////////////////////////////////// START, 07

	Store(0, c007)
	Store(0, b007)
	Store(0, r007)
	Store(0, i007)
	Store(nn07, n007)

	While (n007) {

		m0f7("n007")

		Store(m0f5(p000, p001, ln07), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc07)
			Store(0, r007)
		} else {
			Store(1, r007)
		}

		Store(m0f5(p000, p001, lc07), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c007)
		} else {
			Store(1, c007)
		}
		if (And(Local0, 0x04)) {
			Store(0, b007)
		} else {
			Store(1, b007)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r007, c007, b007, ii07), Local0)
		Increment(ii07)
		Store(0, r007)
		Store(0, c007)
		Store(0, b007)
		if (And(Local0, 0x01)) {
			Store(1, r007)
		} elseif (And(Local0, 0x02)) {
			Store(1, c007)
		} elseif (And(Local0, 0x04)) {
			Store(1, b007)
		}

		// Don't use these variables below
		Decrement(n007)
		Increment(i007)

		////////////////////////// Actions

		if (r007) {
			m0f7("r007")


	////////////////////////////////////////////////////////////// START, 08

	Store(0, c008)
	Store(0, b008)
	Store(0, r008)
	Store(0, i008)
	Store(nn08, n008)

	While (n008) {

		m0f7("n008")

		Store(m0f5(p000, p001, ln08), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc08)
			Store(0, r008)
		} else {
			Store(1, r008)
		}

		Store(m0f5(p000, p001, lc08), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c008)
		} else {
			Store(1, c008)
		}
		if (And(Local0, 0x04)) {
			Store(0, b008)
		} else {
			Store(1, b008)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r008, c008, b008, ii08), Local0)
		Increment(ii08)
		Store(0, r008)
		Store(0, c008)
		Store(0, b008)
		if (And(Local0, 0x01)) {
			Store(1, r008)
		} elseif (And(Local0, 0x02)) {
			Store(1, c008)
		} elseif (And(Local0, 0x04)) {
			Store(1, b008)
		}

		// Don't use these variables below
		Decrement(n008)
		Increment(i008)

		////////////////////////// Actions

		if (r008) {
			m0f7("r008")

	////////////////////////////////////////////////////////////// START, 09

	Store(0, c009)
	Store(0, b009)
	Store(0, r009)
	Store(0, i009)
	Store(nn09, n009)

	While (n009) {

		m0f7("n009")

		Store(m0f5(p000, p001, ln09), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc09)
			Store(0, r009)
		} else {
			Store(1, r009)
		}

		Store(m0f5(p000, p001, lc09), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c009)
		} else {
			Store(1, c009)
		}
		if (And(Local0, 0x04)) {
			Store(0, b009)
		} else {
			Store(1, b009)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r009, c009, b009, ii09), Local0)
		Increment(ii09)
		Store(0, r009)
		Store(0, c009)
		Store(0, b009)
		if (And(Local0, 0x01)) {
			Store(1, r009)
		} elseif (And(Local0, 0x02)) {
			Store(1, c009)
		} elseif (And(Local0, 0x04)) {
			Store(1, b009)
		}

		// Don't use these variables below
		Decrement(n009)
		Increment(i009)

		////////////////////////// Actions

		if (r009) {
			m0f7("r009")

	////////////////////////////////////////////////////////////// START, 10

	Store(0, c010)
	Store(0, b010)
	Store(0, r010)
	Store(0, i010)
	Store(nn10, n010)

	While (n010) {

		m0f7("n010")

		Store(m0f5(p000, p001, ln10), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc10)
			Store(0, r010)
		} else {
			Store(1, r010)
		}

		Store(m0f5(p000, p001, lc10), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c010)
		} else {
			Store(1, c010)
		}
		if (And(Local0, 0x04)) {
			Store(0, b010)
		} else {
			Store(1, b010)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r010, c010, b010, ii10), Local0)
		Increment(ii10)
		Store(0, r010)
		Store(0, c010)
		Store(0, b010)
		if (And(Local0, 0x01)) {
			Store(1, r010)
		} elseif (And(Local0, 0x02)) {
			Store(1, c010)
		} elseif (And(Local0, 0x04)) {
			Store(1, b010)
		}

		// Don't use these variables below
		Decrement(n010)
		Increment(i010)

		////////////////////////// Actions

		if (r010) {
			m0f7("r010")

	////////////////////////////////////////////////////////////// START, 11

	Store(0, c011)
	Store(0, b011)
	Store(0, r011)
	Store(0, i011)
	Store(nn11, n011)

	While (n011) {

		m0f7("n011")

		Store(m0f5(p000, p001, ln11), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc11)
			Store(0, r011)
		} else {
			Store(1, r011)
		}

		Store(m0f5(p000, p001, lc11), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c011)
		} else {
			Store(1, c011)
		}
		if (And(Local0, 0x04)) {
			Store(0, b011)
		} else {
			Store(1, b011)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r011, c011, b011, ii11), Local0)
		Increment(ii11)
		Store(0, r011)
		Store(0, c011)
		Store(0, b011)
		if (And(Local0, 0x01)) {
			Store(1, r011)
		} elseif (And(Local0, 0x02)) {
			Store(1, c011)
		} elseif (And(Local0, 0x04)) {
			Store(1, b011)
		}

		// Don't use these variables below
		Decrement(n011)
		Increment(i011)

		////////////////////////// Actions

		if (r011) {
			m0f7("r011")

	////////////////////////////////////////////////////////////// START, 12

	Store(0, c012)
	Store(0, b012)
	Store(0, r012)
	Store(0, i012)
	Store(nn12, n012)

	While (n012) {

		m0f7("n012")

		Store(m0f5(p000, p001, ln12), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc12)
			Store(0, r012)
		} else {
			Store(1, r012)
		}

		Store(m0f5(p000, p001, lc12), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c012)
		} else {
			Store(1, c012)
		}
		if (And(Local0, 0x04)) {
			Store(0, b012)
		} else {
			Store(1, b012)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r012, c012, b012, ii12), Local0)
		Increment(ii12)
		Store(0, r012)
		Store(0, c012)
		Store(0, b012)
		if (And(Local0, 0x01)) {
			Store(1, r012)
		} elseif (And(Local0, 0x02)) {
			Store(1, c012)
		} elseif (And(Local0, 0x04)) {
			Store(1, b012)
		}

		// Don't use these variables below
		Decrement(n012)
		Increment(i012)

		////////////////////////// Actions

		if (r012) {
			m0f7("r012")

	////////////////////////////////////////////////////////////// START, 13

	Store(0, c013)
	Store(0, b013)
	Store(0, r013)
	Store(0, i013)
	Store(nn13, n013)

	While (n013) {

		m0f7("n013")

		Store(m0f5(p000, p001, ln13), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc13)
			Store(0, r013)
		} else {
			Store(1, r013)
		}

		Store(m0f5(p000, p001, lc13), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c013)
		} else {
			Store(1, c013)
		}
		if (And(Local0, 0x04)) {
			Store(0, b013)
		} else {
			Store(1, b013)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r013, c013, b013, ii13), Local0)
		Increment(ii13)
		Store(0, r013)
		Store(0, c013)
		Store(0, b013)
		if (And(Local0, 0x01)) {
			Store(1, r013)
		} elseif (And(Local0, 0x02)) {
			Store(1, c013)
		} elseif (And(Local0, 0x04)) {
			Store(1, b013)
		}

		// Don't use these variables below
		Decrement(n013)
		Increment(i013)

		////////////////////////// Actions

		if (r013) {
			m0f7("r013")

	////////////////////////////////////////////////////////////// START, 14

	Store(0, c014)
	Store(0, b014)
	Store(0, r014)
	Store(0, i014)
	Store(nn14, n014)

	While (n014) {

		m0f7("n014")

		Store(m0f5(p000, p001, ln14), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc14)
			Store(0, r014)
		} else {
			Store(1, r014)
		}

		Store(m0f5(p000, p001, lc14), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c014)
		} else {
			Store(1, c014)
		}
		if (And(Local0, 0x04)) {
			Store(0, b014)
		} else {
			Store(1, b014)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r014, c014, b014, ii14), Local0)
		Increment(ii14)
		Store(0, r014)
		Store(0, c014)
		Store(0, b014)
		if (And(Local0, 0x01)) {
			Store(1, r014)
		} elseif (And(Local0, 0x02)) {
			Store(1, c014)
		} elseif (And(Local0, 0x04)) {
			Store(1, b014)
		}

		// Don't use these variables below
		Decrement(n014)
		Increment(i014)

		////////////////////////// Actions

		if (r014) {
			m0f7("r014")

	////////////////////////////////////////////////////////////// START, 15

	Store(0, c015)
	Store(0, b015)
	Store(0, r015)
	Store(0, i015)
	Store(nn15, n015)

	While (n015) {

		m0f7("n015")

		Store(m0f5(p000, p001, ln15), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc15)
			Store(0, r015)
		} else {
			Store(1, r015)
		}

		Store(m0f5(p000, p001, lc15), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c015)
		} else {
			Store(1, c015)
		}
		if (And(Local0, 0x04)) {
			Store(0, b015)
		} else {
			Store(1, b015)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r015, c015, b015, ii15), Local0)
		Increment(ii15)
		Store(0, r015)
		Store(0, c015)
		Store(0, b015)
		if (And(Local0, 0x01)) {
			Store(1, r015)
		} elseif (And(Local0, 0x02)) {
			Store(1, c015)
		} elseif (And(Local0, 0x04)) {
			Store(1, b015)
		}

		// Don't use these variables below
		Decrement(n015)
		Increment(i015)

		////////////////////////// Actions

		if (r015) {
			m0f7("r015")

	////////////////////////////////////////////////////////////// START, 16

	Store(0, c016)
	Store(0, b016)
	Store(0, r016)
	Store(0, i016)
	Store(nn16, n016)

	While (n016) {

		m0f7("n016")

		Store(m0f5(p000, p001, ln16), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc16)
			Store(0, r016)
		} else {
			Store(1, r016)
		}

		Store(m0f5(p000, p001, lc16), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c016)
		} else {
			Store(1, c016)
		}
		if (And(Local0, 0x04)) {
			Store(0, b016)
		} else {
			Store(1, b016)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r016, c016, b016, ii16), Local0)
		Increment(ii16)
		Store(0, r016)
		Store(0, c016)
		Store(0, b016)
		if (And(Local0, 0x01)) {
			Store(1, r016)
		} elseif (And(Local0, 0x02)) {
			Store(1, c016)
		} elseif (And(Local0, 0x04)) {
			Store(1, b016)
		}

		// Don't use these variables below
		Decrement(n016)
		Increment(i016)

		////////////////////////// Actions

		if (r016) {
			m0f7("r016")

	////////////////////////////////////////////////////////////// START, 17

	Store(0, c017)
	Store(0, b017)
	Store(0, r017)
	Store(0, i017)
	Store(nn17, n017)

	While (n017) {

		m0f7("n017")

		Store(m0f5(p000, p001, ln17), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc17)
			Store(0, r017)
		} else {
			Store(1, r017)
		}

		Store(m0f5(p000, p001, lc17), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c017)
		} else {
			Store(1, c017)
		}
		if (And(Local0, 0x04)) {
			Store(0, b017)
		} else {
			Store(1, b017)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r017, c017, b017, ii17), Local0)
		Increment(ii17)
		Store(0, r017)
		Store(0, c017)
		Store(0, b017)
		if (And(Local0, 0x01)) {
			Store(1, r017)
		} elseif (And(Local0, 0x02)) {
			Store(1, c017)
		} elseif (And(Local0, 0x04)) {
			Store(1, b017)
		}

		// Don't use these variables below
		Decrement(n017)
		Increment(i017)

		////////////////////////// Actions

		if (r017) {
			m0f7("r017")

	////////////////////////////////////////////////////////////// START, 18

	Store(0, c018)
	Store(0, b018)
	Store(0, r018)
	Store(0, i018)
	Store(nn18, n018)

	While (n018) {

		m0f7("n018")

		Store(m0f5(p000, p001, ln18), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc18)
			Store(0, r018)
		} else {
			Store(1, r018)
		}

		Store(m0f5(p000, p001, lc18), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c018)
		} else {
			Store(1, c018)
		}
		if (And(Local0, 0x04)) {
			Store(0, b018)
		} else {
			Store(1, b018)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r018, c018, b018, ii18), Local0)
		Increment(ii18)
		Store(0, r018)
		Store(0, c018)
		Store(0, b018)
		if (And(Local0, 0x01)) {
			Store(1, r018)
		} elseif (And(Local0, 0x02)) {
			Store(1, c018)
		} elseif (And(Local0, 0x04)) {
			Store(1, b018)
		}

		// Don't use these variables below
		Decrement(n018)
		Increment(i018)

		////////////////////////// Actions

		if (r018) {
			m0f7("r018")

	////////////////////////////////////////////////////////////// START, 19

	Store(0, c019)
	Store(0, b019)
	Store(0, r019)
	Store(0, i019)
	Store(nn19, n019)

	While (n019) {

		m0f7("n019")

		Store(m0f5(p000, p001, ln19), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc19)
			Store(0, r019)
		} else {
			Store(1, r019)
		}

		Store(m0f5(p000, p001, lc19), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c019)
		} else {
			Store(1, c019)
		}
		if (And(Local0, 0x04)) {
			Store(0, b019)
		} else {
			Store(1, b019)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r019, c019, b019, ii19), Local0)
		Increment(ii19)
		Store(0, r019)
		Store(0, c019)
		Store(0, b019)
		if (And(Local0, 0x01)) {
			Store(1, r019)
		} elseif (And(Local0, 0x02)) {
			Store(1, c019)
		} elseif (And(Local0, 0x04)) {
			Store(1, b019)
		}

		// Don't use these variables below
		Decrement(n019)
		Increment(i019)

		////////////////////////// Actions

		if (r019) {
			m0f7("r019")

	////////////////////////////////////////////////////////////// START, 20

	Store(0, c020)
	Store(0, b020)
	Store(0, r020)
	Store(0, i020)
	Store(nn20, n020)

	While (n020) {

		m0f7("n020")

		Store(m0f5(p000, p001, ln20), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc20)
			Store(0, r020)
		} else {
			Store(1, r020)
		}

		Store(m0f5(p000, p001, lc20), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c020)
		} else {
			Store(1, c020)
		}
		if (And(Local0, 0x04)) {
			Store(0, b020)
		} else {
			Store(1, b020)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r020, c020, b020, ii20), Local0)
		Increment(ii20)
		Store(0, r020)
		Store(0, c020)
		Store(0, b020)
		if (And(Local0, 0x01)) {
			Store(1, r020)
		} elseif (And(Local0, 0x02)) {
			Store(1, c020)
		} elseif (And(Local0, 0x04)) {
			Store(1, b020)
		}

		// Don't use these variables below
		Decrement(n020)
		Increment(i020)

		////////////////////////// Actions

		if (r020) {
			m0f7("r020")

	////////////////////////////////////////////////////////////// START, 21

	Store(0, c021)
	Store(0, b021)
	Store(0, r021)
	Store(0, i021)
	Store(nn21, n021)

	While (n021) {

		m0f7("n021")

		Store(m0f5(p000, p001, ln21), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc21)
			Store(0, r021)
		} else {
			Store(1, r021)
		}

		Store(m0f5(p000, p001, lc21), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c021)
		} else {
			Store(1, c021)
		}
		if (And(Local0, 0x04)) {
			Store(0, b021)
		} else {
			Store(1, b021)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r021, c021, b021, ii21), Local0)
		Increment(ii21)
		Store(0, r021)
		Store(0, c021)
		Store(0, b021)
		if (And(Local0, 0x01)) {
			Store(1, r021)
		} elseif (And(Local0, 0x02)) {
			Store(1, c021)
		} elseif (And(Local0, 0x04)) {
			Store(1, b021)
		}

		// Don't use these variables below
		Decrement(n021)
		Increment(i021)

		////////////////////////// Actions

		if (r021) {
			m0f7("r021")

	////////////////////////////////////////////////////////////// START, 22

	Store(0, c022)
	Store(0, b022)
	Store(0, r022)
	Store(0, i022)
	Store(nn22, n022)

	While (n022) {

		m0f7("n022")

		Store(m0f5(p000, p001, ln22), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc22)
			Store(0, r022)
		} else {
			Store(1, r022)
		}

		Store(m0f5(p000, p001, lc22), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c022)
		} else {
			Store(1, c022)
		}
		if (And(Local0, 0x04)) {
			Store(0, b022)
		} else {
			Store(1, b022)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r022, c022, b022, ii22), Local0)
		Increment(ii22)
		Store(0, r022)
		Store(0, c022)
		Store(0, b022)
		if (And(Local0, 0x01)) {
			Store(1, r022)
		} elseif (And(Local0, 0x02)) {
			Store(1, c022)
		} elseif (And(Local0, 0x04)) {
			Store(1, b022)
		}

		// Don't use these variables below
		Decrement(n022)
		Increment(i022)

		////////////////////////// Actions

		if (r022) {
			m0f7("r022")

	////////////////////////////////////////////////////////////// START, 23

	Store(0, c023)
	Store(0, b023)
	Store(0, r023)
	Store(0, i023)
	Store(nn23, n023)

	While (n023) {

		m0f7("n023")

		Store(m0f5(p000, p001, ln23), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc23)
			Store(0, r023)
		} else {
			Store(1, r023)
		}

		Store(m0f5(p000, p001, lc23), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c023)
		} else {
			Store(1, c023)
		}
		if (And(Local0, 0x04)) {
			Store(0, b023)
		} else {
			Store(1, b023)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r023, c023, b023, ii23), Local0)
		Increment(ii23)
		Store(0, r023)
		Store(0, c023)
		Store(0, b023)
		if (And(Local0, 0x01)) {
			Store(1, r023)
		} elseif (And(Local0, 0x02)) {
			Store(1, c023)
		} elseif (And(Local0, 0x04)) {
			Store(1, b023)
		}

		// Don't use these variables below
		Decrement(n023)
		Increment(i023)

		////////////////////////// Actions

		if (r023) {
			m0f7("r023")

	////////////////////////////////////////////////////////////// START, 24

	Store(0, c024)
	Store(0, b024)
	Store(0, r024)
	Store(0, i024)
	Store(nn24, n024)

	While (n024) {

		m0f7("n024")

		Store(m0f5(p000, p001, ln24), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc24)
			Store(0, r024)
		} else {
			Store(1, r024)
		}

		Store(m0f5(p000, p001, lc24), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c024)
		} else {
			Store(1, c024)
		}
		if (And(Local0, 0x04)) {
			Store(0, b024)
		} else {
			Store(1, b024)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r024, c024, b024, ii24), Local0)
		Increment(ii24)
		Store(0, r024)
		Store(0, c024)
		Store(0, b024)
		if (And(Local0, 0x01)) {
			Store(1, r024)
		} elseif (And(Local0, 0x02)) {
			Store(1, c024)
		} elseif (And(Local0, 0x04)) {
			Store(1, b024)
		}

		// Don't use these variables below
		Decrement(n024)
		Increment(i024)

		////////////////////////// Actions

		if (r024) {
			m0f7("r024")

	////////////////////////////////////////////////////////////// START, 25

	Store(0, c025)
	Store(0, b025)
	Store(0, r025)
	Store(0, i025)
	Store(nn25, n025)

	While (n025) {

		m0f7("n025")

		Store(m0f5(p000, p001, ln25), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc25)
			Store(0, r025)
		} else {
			Store(1, r025)
		}

		Store(m0f5(p000, p001, lc25), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c025)
		} else {
			Store(1, c025)
		}
		if (And(Local0, 0x04)) {
			Store(0, b025)
		} else {
			Store(1, b025)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r025, c025, b025, ii25), Local0)
		Increment(ii25)
		Store(0, r025)
		Store(0, c025)
		Store(0, b025)
		if (And(Local0, 0x01)) {
			Store(1, r025)
		} elseif (And(Local0, 0x02)) {
			Store(1, c025)
		} elseif (And(Local0, 0x04)) {
			Store(1, b025)
		}

		// Don't use these variables below
		Decrement(n025)
		Increment(i025)

		////////////////////////// Actions

		if (r025) {
			m0f7("r025")

	////////////////////////////////////////////////////////////// START, 26

	Store(0, c026)
	Store(0, b026)
	Store(0, r026)
	Store(0, i026)
	Store(nn26, n026)

	While (n026) {

		m0f7("n026")

		Store(m0f5(p000, p001, ln26), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc26)
			Store(0, r026)
		} else {
			Store(1, r026)
		}

		Store(m0f5(p000, p001, lc26), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c026)
		} else {
			Store(1, c026)
		}
		if (And(Local0, 0x04)) {
			Store(0, b026)
		} else {
			Store(1, b026)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r026, c026, b026, ii26), Local0)
		Increment(ii26)
		Store(0, r026)
		Store(0, c026)
		Store(0, b026)
		if (And(Local0, 0x01)) {
			Store(1, r026)
		} elseif (And(Local0, 0x02)) {
			Store(1, c026)
		} elseif (And(Local0, 0x04)) {
			Store(1, b026)
		}

		// Don't use these variables below
		Decrement(n026)
		Increment(i026)

		////////////////////////// Actions

		if (r026) {
			m0f7("r026")

	////////////////////////////////////////////////////////////// START, 27

	Store(0, c027)
	Store(0, b027)
	Store(0, r027)
	Store(0, i027)
	Store(nn27, n027)

	While (n027) {

		m0f7("n027")

		Store(m0f5(p000, p001, ln27), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc27)
			Store(0, r027)
		} else {
			Store(1, r027)
		}

		Store(m0f5(p000, p001, lc27), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c027)
		} else {
			Store(1, c027)
		}
		if (And(Local0, 0x04)) {
			Store(0, b027)
		} else {
			Store(1, b027)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r027, c027, b027, ii27), Local0)
		Increment(ii27)
		Store(0, r027)
		Store(0, c027)
		Store(0, b027)
		if (And(Local0, 0x01)) {
			Store(1, r027)
		} elseif (And(Local0, 0x02)) {
			Store(1, c027)
		} elseif (And(Local0, 0x04)) {
			Store(1, b027)
		}

		// Don't use these variables below
		Decrement(n027)
		Increment(i027)

		////////////////////////// Actions

		if (r027) {
			m0f7("r027")

	////////////////////////////////////////////////////////////// START, 28

	Store(0, c028)
	Store(0, b028)
	Store(0, r028)
	Store(0, i028)
	Store(nn28, n028)

	While (n028) {

		m0f7("n028")

		Store(m0f5(p000, p001, ln28), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc28)
			Store(0, r028)
		} else {
			Store(1, r028)
		}

		Store(m0f5(p000, p001, lc28), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c028)
		} else {
			Store(1, c028)
		}
		if (And(Local0, 0x04)) {
			Store(0, b028)
		} else {
			Store(1, b028)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r028, c028, b028, ii28), Local0)
		Increment(ii28)
		Store(0, r028)
		Store(0, c028)
		Store(0, b028)
		if (And(Local0, 0x01)) {
			Store(1, r028)
		} elseif (And(Local0, 0x02)) {
			Store(1, c028)
		} elseif (And(Local0, 0x04)) {
			Store(1, b028)
		}

		// Don't use these variables below
		Decrement(n028)
		Increment(i028)

		////////////////////////// Actions

		if (r028) {
			m0f7("r028")

	////////////////////////////////////////////////////////////// START, 29

	Store(0, c029)
	Store(0, b029)
	Store(0, r029)
	Store(0, i029)
	Store(nn29, n029)

	While (n029) {

		m0f7("n029")

		Store(m0f5(p000, p001, ln29), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc29)
			Store(0, r029)
		} else {
			Store(1, r029)
		}

		Store(m0f5(p000, p001, lc29), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c029)
		} else {
			Store(1, c029)
		}
		if (And(Local0, 0x04)) {
			Store(0, b029)
		} else {
			Store(1, b029)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r029, c029, b029, ii29), Local0)
		Increment(ii29)
		Store(0, r029)
		Store(0, c029)
		Store(0, b029)
		if (And(Local0, 0x01)) {
			Store(1, r029)
		} elseif (And(Local0, 0x02)) {
			Store(1, c029)
		} elseif (And(Local0, 0x04)) {
			Store(1, b029)
		}

		// Don't use these variables below
		Decrement(n029)
		Increment(i029)

		////////////////////////// Actions

		if (r029) {
			m0f7("r029")

	////////////////////////////////////////////////////////////// START, 30

	Store(0, c030)
	Store(0, b030)
	Store(0, r030)
	Store(0, i030)
	Store(nn30, n030)

	While (n030) {

		m0f7("n030")

		Store(m0f5(p000, p001, ln30), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc30)
			Store(0, r030)
		} else {
			Store(1, r030)
		}

		Store(m0f5(p000, p001, lc30), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c030)
		} else {
			Store(1, c030)
		}
		if (And(Local0, 0x04)) {
			Store(0, b030)
		} else {
			Store(1, b030)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r030, c030, b030, ii30), Local0)
		Increment(ii30)
		Store(0, r030)
		Store(0, c030)
		Store(0, b030)
		if (And(Local0, 0x01)) {
			Store(1, r030)
		} elseif (And(Local0, 0x02)) {
			Store(1, c030)
		} elseif (And(Local0, 0x04)) {
			Store(1, b030)
		}

		// Don't use these variables below
		Decrement(n030)
		Increment(i030)

		////////////////////////// Actions

		if (r030) {
			m0f7("r030")

	////////////////////////////////////////////////////////////// START, 31

	Store(0, c031)
	Store(0, b031)
	Store(0, r031)
	Store(0, i031)
	Store(nn31, n031)

	While (n031) {

		m0f7("n031")

		Store(m0f5(p000, p001, ln31), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc31)
			Store(0, r031)
		} else {
			Store(1, r031)
		}

		Store(m0f5(p000, p001, lc31), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c031)
		} else {
			Store(1, c031)
		}
		if (And(Local0, 0x04)) {
			Store(0, b031)
		} else {
			Store(1, b031)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r031, c031, b031, ii31), Local0)
		Increment(ii31)
		Store(0, r031)
		Store(0, c031)
		Store(0, b031)
		if (And(Local0, 0x01)) {
			Store(1, r031)
		} elseif (And(Local0, 0x02)) {
			Store(1, c031)
		} elseif (And(Local0, 0x04)) {
			Store(1, b031)
		}

		// Don't use these variables below
		Decrement(n031)
		Increment(i031)

		////////////////////////// Actions

		if (r031) {
			m0f7("r031")

	////////////////////////////////////////////////////////////// START, 32

	Store(0, c032)
	Store(0, b032)
	Store(0, r032)
	Store(0, i032)
	Store(nn32, n032)

	While (n032) {

		m0f7("n032")

		Store(m0f5(p000, p001, ln32), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc32)
			Store(0, r032)
		} else {
			Store(1, r032)
		}

		Store(m0f5(p000, p001, lc32), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c032)
		} else {
			Store(1, c032)
		}
		if (And(Local0, 0x04)) {
			Store(0, b032)
		} else {
			Store(1, b032)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r032, c032, b032, ii32), Local0)
		Increment(ii32)
		Store(0, r032)
		Store(0, c032)
		Store(0, b032)
		if (And(Local0, 0x01)) {
			Store(1, r032)
		} elseif (And(Local0, 0x02)) {
			Store(1, c032)
		} elseif (And(Local0, 0x04)) {
			Store(1, b032)
		}

		// Don't use these variables below
		Decrement(n032)
		Increment(i032)

		////////////////////////// Actions

		if (r032) {
			m0f7("r032")

	////////////////////////////////////////////////////////////// START, 33

	Store(0, c033)
	Store(0, b033)
	Store(0, r033)
	Store(0, i033)
	Store(nn33, n033)

	While (n033) {

		m0f7("n033")

		Store(m0f5(p000, p001, ln33), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc33)
			Store(0, r033)
		} else {
			Store(1, r033)
		}

		Store(m0f5(p000, p001, lc33), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c033)
		} else {
			Store(1, c033)
		}
		if (And(Local0, 0x04)) {
			Store(0, b033)
		} else {
			Store(1, b033)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r033, c033, b033, ii33), Local0)
		Increment(ii33)
		Store(0, r033)
		Store(0, c033)
		Store(0, b033)
		if (And(Local0, 0x01)) {
			Store(1, r033)
		} elseif (And(Local0, 0x02)) {
			Store(1, c033)
		} elseif (And(Local0, 0x04)) {
			Store(1, b033)
		}

		// Don't use these variables below
		Decrement(n033)
		Increment(i033)

		////////////////////////// Actions

		if (r033) {
			m0f7("r033")

	////////////////////////////////////////////////////////////// START, 34

	Store(0, c034)
	Store(0, b034)
	Store(0, r034)
	Store(0, i034)
	Store(nn34, n034)

	While (n034) {

		m0f7("n034")

		Store(m0f5(p000, p001, ln34), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc34)
			Store(0, r034)
		} else {
			Store(1, r034)
		}

		Store(m0f5(p000, p001, lc34), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c034)
		} else {
			Store(1, c034)
		}
		if (And(Local0, 0x04)) {
			Store(0, b034)
		} else {
			Store(1, b034)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r034, c034, b034, ii34), Local0)
		Increment(ii34)
		Store(0, r034)
		Store(0, c034)
		Store(0, b034)
		if (And(Local0, 0x01)) {
			Store(1, r034)
		} elseif (And(Local0, 0x02)) {
			Store(1, c034)
		} elseif (And(Local0, 0x04)) {
			Store(1, b034)
		}

		// Don't use these variables below
		Decrement(n034)
		Increment(i034)

		////////////////////////// Actions

		if (r034) {
			m0f7("r034")

	////////////////////////////////////////////////////////////// START, 35

	Store(0, c035)
	Store(0, b035)
	Store(0, r035)
	Store(0, i035)
	Store(nn35, n035)

	While (n035) {

		m0f7("n035")

		Store(m0f5(p000, p001, ln35), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc35)
			Store(0, r035)
		} else {
			Store(1, r035)
		}

		Store(m0f5(p000, p001, lc35), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c035)
		} else {
			Store(1, c035)
		}
		if (And(Local0, 0x04)) {
			Store(0, b035)
		} else {
			Store(1, b035)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r035, c035, b035, ii35), Local0)
		Increment(ii35)
		Store(0, r035)
		Store(0, c035)
		Store(0, b035)
		if (And(Local0, 0x01)) {
			Store(1, r035)
		} elseif (And(Local0, 0x02)) {
			Store(1, c035)
		} elseif (And(Local0, 0x04)) {
			Store(1, b035)
		}

		// Don't use these variables below
		Decrement(n035)
		Increment(i035)

		////////////////////////// Actions

		if (r035) {
			m0f7("r035")

	////////////////////////////////////////////////////////////// START, 36

	Store(0, c036)
	Store(0, b036)
	Store(0, r036)
	Store(0, i036)
	Store(nn36, n036)

	While (n036) {

		m0f7("n036")

		Store(m0f5(p000, p001, ln36), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc36)
			Store(0, r036)
		} else {
			Store(1, r036)
		}

		Store(m0f5(p000, p001, lc36), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c036)
		} else {
			Store(1, c036)
		}
		if (And(Local0, 0x04)) {
			Store(0, b036)
		} else {
			Store(1, b036)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r036, c036, b036, ii36), Local0)
		Increment(ii36)
		Store(0, r036)
		Store(0, c036)
		Store(0, b036)
		if (And(Local0, 0x01)) {
			Store(1, r036)
		} elseif (And(Local0, 0x02)) {
			Store(1, c036)
		} elseif (And(Local0, 0x04)) {
			Store(1, b036)
		}

		// Don't use these variables below
		Decrement(n036)
		Increment(i036)

		////////////////////////// Actions

		if (r036) {
			m0f7("r036")

	////////////////////////////////////////////////////////////// START, 37

	Store(0, c037)
	Store(0, b037)
	Store(0, r037)
	Store(0, i037)
	Store(nn37, n037)

	While (n037) {

		m0f7("n037")

		Store(m0f5(p000, p001, ln37), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc37)
			Store(0, r037)
		} else {
			Store(1, r037)
		}

		Store(m0f5(p000, p001, lc37), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c037)
		} else {
			Store(1, c037)
		}
		if (And(Local0, 0x04)) {
			Store(0, b037)
		} else {
			Store(1, b037)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r037, c037, b037, ii37), Local0)
		Increment(ii37)
		Store(0, r037)
		Store(0, c037)
		Store(0, b037)
		if (And(Local0, 0x01)) {
			Store(1, r037)
		} elseif (And(Local0, 0x02)) {
			Store(1, c037)
		} elseif (And(Local0, 0x04)) {
			Store(1, b037)
		}

		// Don't use these variables below
		Decrement(n037)
		Increment(i037)

		////////////////////////// Actions

		if (r037) {
			m0f7("r037")

	////////////////////////////////////////////////////////////// START, 38

	Store(0, c038)
	Store(0, b038)
	Store(0, r038)
	Store(0, i038)
	Store(nn38, n038)

	While (n038) {

		m0f7("n038")

		Store(m0f5(p000, p001, ln38), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc38)
			Store(0, r038)
		} else {
			Store(1, r038)
		}

		Store(m0f5(p000, p001, lc38), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c038)
		} else {
			Store(1, c038)
		}
		if (And(Local0, 0x04)) {
			Store(0, b038)
		} else {
			Store(1, b038)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r038, c038, b038, ii38), Local0)
		Increment(ii38)
		Store(0, r038)
		Store(0, c038)
		Store(0, b038)
		if (And(Local0, 0x01)) {
			Store(1, r038)
		} elseif (And(Local0, 0x02)) {
			Store(1, c038)
		} elseif (And(Local0, 0x04)) {
			Store(1, b038)
		}

		// Don't use these variables below
		Decrement(n038)
		Increment(i038)

		////////////////////////// Actions

		if (r038) {
			m0f7("r038")

	////////////////////////////////////////////////////////////// START, 39

	Store(0, c039)
	Store(0, b039)
	Store(0, r039)
	Store(0, i039)
	Store(nn39, n039)

	While (n039) {

		m0f7("n039")

		Store(m0f5(p000, p001, ln39), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc39)
			Store(0, r039)
		} else {
			Store(1, r039)
		}

		Store(m0f5(p000, p001, lc39), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c039)
		} else {
			Store(1, c039)
		}
		if (And(Local0, 0x04)) {
			Store(0, b039)
		} else {
			Store(1, b039)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r039, c039, b039, ii39), Local0)
		Increment(ii39)
		Store(0, r039)
		Store(0, c039)
		Store(0, b039)
		if (And(Local0, 0x01)) {
			Store(1, r039)
		} elseif (And(Local0, 0x02)) {
			Store(1, c039)
		} elseif (And(Local0, 0x04)) {
			Store(1, b039)
		}

		// Don't use these variables below
		Decrement(n039)
		Increment(i039)

		////////////////////////// Actions

		if (r039) {
			m0f7("r039")

	////////////////////////////////////////////////////////////// START, 40

	Store(0, c040)
	Store(0, b040)
	Store(0, r040)
	Store(0, i040)
	Store(nn40, n040)

	While (n040) {

		m0f7("n040")

		Store(m0f5(p000, p001, ln40), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc40)
			Store(0, r040)
		} else {
			Store(1, r040)
		}

		Store(m0f5(p000, p001, lc40), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c040)
		} else {
			Store(1, c040)
		}
		if (And(Local0, 0x04)) {
			Store(0, b040)
		} else {
			Store(1, b040)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r040, c040, b040, ii40), Local0)
		Increment(ii40)
		Store(0, r040)
		Store(0, c040)
		Store(0, b040)
		if (And(Local0, 0x01)) {
			Store(1, r040)
		} elseif (And(Local0, 0x02)) {
			Store(1, c040)
		} elseif (And(Local0, 0x04)) {
			Store(1, b040)
		}

		// Don't use these variables below
		Decrement(n040)
		Increment(i040)

		////////////////////////// Actions

		if (r040) {
			m0f7("r040")


	////////////////////////////////////////////////////////////// START, 41

	Store(0, c041)
	Store(0, b041)
	Store(0, r041)
	Store(0, i041)
	Store(nn41, n041)

	While (n041) {

		m0f7("n041")

		Store(m0f5(p000, p001, ln41), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc41)
			Store(0, r041)
		} else {
			Store(1, r041)
		}

		Store(m0f5(p000, p001, lc41), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c041)
		} else {
			Store(1, c041)
		}
		if (And(Local0, 0x04)) {
			Store(0, b041)
		} else {
			Store(1, b041)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r041, c041, b041, ii41), Local0)
		Increment(ii41)
		Store(0, r041)
		Store(0, c041)
		Store(0, b041)
		if (And(Local0, 0x01)) {
			Store(1, r041)
		} elseif (And(Local0, 0x02)) {
			Store(1, c041)
		} elseif (And(Local0, 0x04)) {
			Store(1, b041)
		}

		// Don't use these variables below
		Decrement(n041)
		Increment(i041)

		////////////////////////// Actions

		if (r041) {
			m0f7("r041")

	////////////////////////////////////////////////////////////// START, 42

	Store(0, c042)
	Store(0, b042)
	Store(0, r042)
	Store(0, i042)
	Store(nn42, n042)

	While (n042) {

		m0f7("n042")

		Store(m0f5(p000, p001, ln42), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc42)
			Store(0, r042)
		} else {
			Store(1, r042)
		}

		Store(m0f5(p000, p001, lc42), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c042)
		} else {
			Store(1, c042)
		}
		if (And(Local0, 0x04)) {
			Store(0, b042)
		} else {
			Store(1, b042)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r042, c042, b042, ii42), Local0)
		Increment(ii42)
		Store(0, r042)
		Store(0, c042)
		Store(0, b042)
		if (And(Local0, 0x01)) {
			Store(1, r042)
		} elseif (And(Local0, 0x02)) {
			Store(1, c042)
		} elseif (And(Local0, 0x04)) {
			Store(1, b042)
		}

		// Don't use these variables below
		Decrement(n042)
		Increment(i042)

		////////////////////////// Actions

		if (r042) {
			m0f7("r042")

	////////////////////////////////////////////////////////////// START, 43

	Store(0, c043)
	Store(0, b043)
	Store(0, r043)
	Store(0, i043)
	Store(nn43, n043)

	While (n043) {

		m0f7("n043")

		Store(m0f5(p000, p001, ln43), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc43)
			Store(0, r043)
		} else {
			Store(1, r043)
		}

		Store(m0f5(p000, p001, lc43), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c043)
		} else {
			Store(1, c043)
		}
		if (And(Local0, 0x04)) {
			Store(0, b043)
		} else {
			Store(1, b043)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r043, c043, b043, ii43), Local0)
		Increment(ii43)
		Store(0, r043)
		Store(0, c043)
		Store(0, b043)
		if (And(Local0, 0x01)) {
			Store(1, r043)
		} elseif (And(Local0, 0x02)) {
			Store(1, c043)
		} elseif (And(Local0, 0x04)) {
			Store(1, b043)
		}

		// Don't use these variables below
		Decrement(n043)
		Increment(i043)

		////////////////////////// Actions

		if (r043) {
			m0f7("r043")

	////////////////////////////////////////////////////////////// START, 44

	Store(0, c044)
	Store(0, b044)
	Store(0, r044)
	Store(0, i044)
	Store(nn44, n044)

	While (n044) {

		m0f7("n044")

		Store(m0f5(p000, p001, ln44), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc44)
			Store(0, r044)
		} else {
			Store(1, r044)
		}

		Store(m0f5(p000, p001, lc44), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c044)
		} else {
			Store(1, c044)
		}
		if (And(Local0, 0x04)) {
			Store(0, b044)
		} else {
			Store(1, b044)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r044, c044, b044, ii44), Local0)
		Increment(ii44)
		Store(0, r044)
		Store(0, c044)
		Store(0, b044)
		if (And(Local0, 0x01)) {
			Store(1, r044)
		} elseif (And(Local0, 0x02)) {
			Store(1, c044)
		} elseif (And(Local0, 0x04)) {
			Store(1, b044)
		}

		// Don't use these variables below
		Decrement(n044)
		Increment(i044)

		////////////////////////// Actions

		if (r044) {
			m0f7("r044")

	////////////////////////////////////////////////////////////// START, 45

	Store(0, c045)
	Store(0, b045)
	Store(0, r045)
	Store(0, i045)
	Store(nn45, n045)

	While (n045) {

		m0f7("n045")

		Store(m0f5(p000, p001, ln45), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc45)
			Store(0, r045)
		} else {
			Store(1, r045)
		}

		Store(m0f5(p000, p001, lc45), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c045)
		} else {
			Store(1, c045)
		}
		if (And(Local0, 0x04)) {
			Store(0, b045)
		} else {
			Store(1, b045)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r045, c045, b045, ii45), Local0)
		Increment(ii45)
		Store(0, r045)
		Store(0, c045)
		Store(0, b045)
		if (And(Local0, 0x01)) {
			Store(1, r045)
		} elseif (And(Local0, 0x02)) {
			Store(1, c045)
		} elseif (And(Local0, 0x04)) {
			Store(1, b045)
		}

		// Don't use these variables below
		Decrement(n045)
		Increment(i045)

		////////////////////////// Actions

		if (r045) {
			m0f7("r045")

	////////////////////////////////////////////////////////////// START, 46

	Store(0, c046)
	Store(0, b046)
	Store(0, r046)
	Store(0, i046)
	Store(nn46, n046)

	While (n046) {

		m0f7("n046")

		Store(m0f5(p000, p001, ln46), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc46)
			Store(0, r046)
		} else {
			Store(1, r046)
		}

		Store(m0f5(p000, p001, lc46), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c046)
		} else {
			Store(1, c046)
		}
		if (And(Local0, 0x04)) {
			Store(0, b046)
		} else {
			Store(1, b046)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r046, c046, b046, ii46), Local0)
		Increment(ii46)
		Store(0, r046)
		Store(0, c046)
		Store(0, b046)
		if (And(Local0, 0x01)) {
			Store(1, r046)
		} elseif (And(Local0, 0x02)) {
			Store(1, c046)
		} elseif (And(Local0, 0x04)) {
			Store(1, b046)
		}

		// Don't use these variables below
		Decrement(n046)
		Increment(i046)

		////////////////////////// Actions

		if (r046) {
			m0f7("r046")

	////////////////////////////////////////////////////////////// START, 47

	Store(0, c047)
	Store(0, b047)
	Store(0, r047)
	Store(0, i047)
	Store(nn47, n047)

	While (n047) {

		m0f7("n047")

		Store(m0f5(p000, p001, ln47), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc47)
			Store(0, r047)
		} else {
			Store(1, r047)
		}

		Store(m0f5(p000, p001, lc47), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c047)
		} else {
			Store(1, c047)
		}
		if (And(Local0, 0x04)) {
			Store(0, b047)
		} else {
			Store(1, b047)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r047, c047, b047, ii47), Local0)
		Increment(ii47)
		Store(0, r047)
		Store(0, c047)
		Store(0, b047)
		if (And(Local0, 0x01)) {
			Store(1, r047)
		} elseif (And(Local0, 0x02)) {
			Store(1, c047)
		} elseif (And(Local0, 0x04)) {
			Store(1, b047)
		}

		// Don't use these variables below
		Decrement(n047)
		Increment(i047)

		////////////////////////// Actions

		if (r047) {
			m0f7("r047")

	////////////////////////////////////////////////////////////// START, 48

	Store(0, c048)
	Store(0, b048)
	Store(0, r048)
	Store(0, i048)
	Store(nn48, n048)

	While (n048) {

		m0f7("n048")

		Store(m0f5(p000, p001, ln48), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc48)
			Store(0, r048)
		} else {
			Store(1, r048)
		}

		Store(m0f5(p000, p001, lc48), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c048)
		} else {
			Store(1, c048)
		}
		if (And(Local0, 0x04)) {
			Store(0, b048)
		} else {
			Store(1, b048)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r048, c048, b048, ii48), Local0)
		Increment(ii48)
		Store(0, r048)
		Store(0, c048)
		Store(0, b048)
		if (And(Local0, 0x01)) {
			Store(1, r048)
		} elseif (And(Local0, 0x02)) {
			Store(1, c048)
		} elseif (And(Local0, 0x04)) {
			Store(1, b048)
		}

		// Don't use these variables below
		Decrement(n048)
		Increment(i048)

		////////////////////////// Actions

		if (r048) {
			m0f7("r048")

	////////////////////////////////////////////////////////////// START, 49

	Store(0, c049)
	Store(0, b049)
	Store(0, r049)
	Store(0, i049)
	Store(nn49, n049)

	While (n049) {

		m0f7("n049")

		Store(m0f5(p000, p001, ln49), Local0)
		if (LEqual(Local0, 0x07)) {
			// Set up - my children complited
			m0f2(p000, CHL0, lc49)
			Store(0, r049)
		} else {
			Store(1, r049)
		}

		Store(m0f5(p000, p001, lc49), Local0)

		if (And(Local0, 0x02)) {
			Store(0, c049)
		} else {
			Store(1, c049)
		}
		if (And(Local0, 0x04)) {
			Store(0, b049)
		} else {
			Store(1, b049)
		}

		// Mix consecution of works (may nullify all)
		Store(m0f9(r049, c049, b049, ii49), Local0)
		Increment(ii49)
		Store(0, r049)
		Store(0, c049)
		Store(0, b049)
		if (And(Local0, 0x01)) {
			Store(1, r049)
		} elseif (And(Local0, 0x02)) {
			Store(1, c049)
		} elseif (And(Local0, 0x04)) {
			Store(1, b049)
		}

		// Don't use these variables below
		Decrement(n049)
		Increment(i049)

		////////////////////////// Actions

		if (r049) {
			m0f7("r049")
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b049) {
			m0f2(p000, BRK0, lc49)
			break
		}
		if (c049) {
			m0f2(p000, CNT0, lc49)
			continue
		}

		if (c049) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b049) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln49), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc49)
			Store(m0f5(p000, p001, lc49), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b049)
				m0f7("b049, completed")
				break
			}
		}

		if (b049) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 49
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b048) {
			m0f2(p000, BRK0, lc48)
			break
		}
		if (c048) {
			m0f2(p000, CNT0, lc48)
			continue
		}

		if (c048) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b048) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln48), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc48)
			Store(m0f5(p000, p001, lc48), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b048)
				m0f7("b048, completed")
				break
			}
		}

		if (b048) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 48
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b047) {
			m0f2(p000, BRK0, lc47)
			break
		}
		if (c047) {
			m0f2(p000, CNT0, lc47)
			continue
		}

		if (c047) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b047) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln47), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc47)
			Store(m0f5(p000, p001, lc47), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b047)
				m0f7("b047, completed")
				break
			}
		}

		if (b047) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 47
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b046) {
			m0f2(p000, BRK0, lc46)
			break
		}
		if (c046) {
			m0f2(p000, CNT0, lc46)
			continue
		}

		if (c046) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b046) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln46), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc46)
			Store(m0f5(p000, p001, lc46), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b046)
				m0f7("b046, completed")
				break
			}
		}

		if (b046) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 46
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b045) {
			m0f2(p000, BRK0, lc45)
			break
		}
		if (c045) {
			m0f2(p000, CNT0, lc45)
			continue
		}

		if (c045) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b045) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln45), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc45)
			Store(m0f5(p000, p001, lc45), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b045)
				m0f7("b045, completed")
				break
			}
		}

		if (b045) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 45
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b044) {
			m0f2(p000, BRK0, lc44)
			break
		}
		if (c044) {
			m0f2(p000, CNT0, lc44)
			continue
		}

		if (c044) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b044) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln44), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc44)
			Store(m0f5(p000, p001, lc44), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b044)
				m0f7("b044, completed")
				break
			}
		}

		if (b044) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 44
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b043) {
			m0f2(p000, BRK0, lc43)
			break
		}
		if (c043) {
			m0f2(p000, CNT0, lc43)
			continue
		}

		if (c043) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b043) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0,  0, 0)
		}

		Store(m0f5(p000, p001, ln43), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc43)
			Store(m0f5(p000, p001, lc43), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b043)
				m0f7("b043, completed")
				break
			}
		}

		if (b043) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 43
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b042) {
			m0f2(p000, BRK0, lc42)
			break
		}
		if (c042) {
			m0f2(p000, CNT0, lc42)
			continue
		}

		if (c042) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b042) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln42), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc42)
			Store(m0f5(p000, p001, lc42), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b042)
				m0f7("b042, completed")
				break
			}
		}

		if (b042) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 42
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b041) {
			m0f2(p000, BRK0, lc41)
			break
		}
		if (c041) {
			m0f2(p000, CNT0, lc41)
			continue
		}

		if (c041) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b041) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln41), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc41)
			Store(m0f5(p000, p001, lc41), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b041)
				m0f7("b041, completed")
				break
			}
		}

		if (b041) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 41
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b040) {
			m0f2(p000, BRK0, lc40)
			break
		}
		if (c040) {
			m0f2(p000, CNT0, lc40)
			continue
		}

		if (c040) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b040) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln40), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc40)
			Store(m0f5(p000, p001, lc40), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b040)
				m0f7("b040, completed")
				break
			}
		}

		if (b040) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 40
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b039) {
			m0f2(p000, BRK0, lc39)
			break
		}
		if (c039) {
			m0f2(p000, CNT0, lc39)
			continue
		}

		if (c039) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b039) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln39), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc39)
			Store(m0f5(p000, p001, lc39), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b039)
				m0f7("b039, completed")
				break
			}
		}

		if (b039) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 39
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b038) {
			m0f2(p000, BRK0, lc38)
			break
		}
		if (c038) {
			m0f2(p000, CNT0, lc38)
			continue
		}

		if (c038) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b038) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln38), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc38)
			Store(m0f5(p000, p001, lc38), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b038)
				m0f7("b038, completed")
				break
			}
		}

		if (b038) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 38
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b037) {
			m0f2(p000, BRK0, lc37)
			break
		}
		if (c037) {
			m0f2(p000, CNT0, lc37)
			continue
		}

		if (c037) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b037) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln37), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc37)
			Store(m0f5(p000, p001, lc37), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b037)
				m0f7("b037, completed")
				break
			}
		}

		if (b037) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 37
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b036) {
			m0f2(p000, BRK0, lc36)
			break
		}
		if (c036) {
			m0f2(p000, CNT0, lc36)
			continue
		}

		if (c036) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b036) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln36), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc36)
			Store(m0f5(p000, p001, lc36), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b036)
				m0f7("b036, completed")
				break
			}
		}

		if (b036) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 36
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b035) {
			m0f2(p000, BRK0, lc35)
			break
		}
		if (c035) {
			m0f2(p000, CNT0, lc35)
			continue
		}

		if (c035) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b035) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln35), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc35)
			Store(m0f5(p000, p001, lc35), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b035)
				m0f7("b035, completed")
				break
			}
		}

		if (b035) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 35
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b034) {
			m0f2(p000, BRK0, lc34)
			break
		}
		if (c034) {
			m0f2(p000, CNT0, lc34)
			continue
		}

		if (c034) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b034) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln34), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc34)
			Store(m0f5(p000, p001, lc34), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b034)
				m0f7("b034, completed")
				break
			}
		}

		if (b034) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 34
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b033) {
			m0f2(p000, BRK0, lc33)
			break
		}
		if (c033) {
			m0f2(p000, CNT0, lc33)
			continue
		}

		if (c033) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b033) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln33), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc33)
			Store(m0f5(p000, p001, lc33), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b033)
				m0f7("b033, completed")
				break
			}
		}

		if (b033) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 33
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b032) {
			m0f2(p000, BRK0, lc32)
			break
		}
		if (c032) {
			m0f2(p000, CNT0, lc32)
			continue
		}

		if (c032) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b032) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln32), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc32)
			Store(m0f5(p000, p001, lc32), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b032)
				m0f7("b032, completed")
				break
			}
		}

		if (b032) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 32
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b031) {
			m0f2(p000, BRK0, lc31)
			break
		}
		if (c031) {
			m0f2(p000, CNT0, lc31)
			continue
		}

		if (c031) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b031) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln31), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc31)
			Store(m0f5(p000, p001, lc31), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b031)
				m0f7("b031, completed")
				break
			}
		}

		if (b031) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 31
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b030) {
			m0f2(p000, BRK0, lc30)
			break
		}
		if (c030) {
			m0f2(p000, CNT0, lc30)
			continue
		}

		if (c030) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b030) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln30), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc30)
			Store(m0f5(p000, p001, lc30), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b030)
				m0f7("b030, completed")
				break
			}
		}

		if (b030) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 30
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b029) {
			m0f2(p000, BRK0, lc29)
			break
		}
		if (c029) {
			m0f2(p000, CNT0, lc29)
			continue
		}

		if (c029) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b029) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln29), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc29)
			Store(m0f5(p000, p001, lc29), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b029)
				m0f7("b029, completed")
				break
			}
		}

		if (b029) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 29
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b028) {
			m0f2(p000, BRK0, lc28)
			break
		}
		if (c028) {
			m0f2(p000, CNT0, lc28)
			continue
		}

		if (c028) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b028) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln28), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc28)
			Store(m0f5(p000, p001, lc28), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b028)
				m0f7("b028, completed")
				break
			}
		}

		if (b028) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 28
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b027) {
			m0f2(p000, BRK0, lc27)
			break
		}
		if (c027) {
			m0f2(p000, CNT0, lc27)
			continue
		}

		if (c027) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b027) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln27), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc27)
			Store(m0f5(p000, p001, lc27), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b027)
				m0f7("b027, completed")
				break
			}
		}

		if (b027) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 27
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b026) {
			m0f2(p000, BRK0, lc26)
			break
		}
		if (c026) {
			m0f2(p000, CNT0, lc26)
			continue
		}

		if (c026) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b026) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln26), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc26)
			Store(m0f5(p000, p001, lc26), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b026)
				m0f7("b026, completed")
				break
			}
		}

		if (b026) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 26
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b025) {
			m0f2(p000, BRK0, lc25)
			break
		}
		if (c025) {
			m0f2(p000, CNT0, lc25)
			continue
		}

		if (c025) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b025) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln25), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc25)
			Store(m0f5(p000, p001, lc25), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b025)
				m0f7("b025, completed")
				break
			}
		}

		if (b025) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 25
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b024) {
			m0f2(p000, BRK0, lc24)
			break
		}
		if (c024) {
			m0f2(p000, CNT0, lc24)
			continue
		}

		if (c024) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b024) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln24), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc24)
			Store(m0f5(p000, p001, lc24), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b024)
				m0f7("b024, completed")
				break
			}
		}

		if (b024) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 24
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b023) {
			m0f2(p000, BRK0, lc23)
			break
		}
		if (c023) {
			m0f2(p000, CNT0, lc23)
			continue
		}

		if (c023) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b023) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln23), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc23)
			Store(m0f5(p000, p001, lc23), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b023)
				m0f7("b023, completed")
				break
			}
		}

		if (b023) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 23
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b022) {
			m0f2(p000, BRK0, lc22)
			break
		}
		if (c022) {
			m0f2(p000, CNT0, lc22)
			continue
		}

		if (c022) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b022) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln22), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc22)
			Store(m0f5(p000, p001, lc22), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b022)
				m0f7("b022, completed")
				break
			}
		}

		if (b022) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 22
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b021) {
			m0f2(p000, BRK0, lc21)
			break
		}
		if (c021) {
			m0f2(p000, CNT0, lc21)
			continue
		}

		if (c021) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b021) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln21), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc21)
			Store(m0f5(p000, p001, lc21), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b021)
				m0f7("b021, completed")
				break
			}
		}

		if (b021) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 21
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b020) {
			m0f2(p000, BRK0, lc20)
			break
		}
		if (c020) {
			m0f2(p000, CNT0, lc20)
			continue
		}

		if (c020) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b020) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln20), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc20)
			Store(m0f5(p000, p001, lc20), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b020)
				m0f7("b020, completed")
				break
			}
		}

		if (b020) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 20
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b019) {
			m0f2(p000, BRK0, lc19)
			break
		}
		if (c019) {
			m0f2(p000, CNT0, lc19)
			continue
		}

		if (c019) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b019) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln19), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc19)
			Store(m0f5(p000, p001, lc19), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b019)
				m0f7("b019, completed")
				break
			}
		}

		if (b019) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 19
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b018) {
			m0f2(p000, BRK0, lc18)
			break
		}
		if (c018) {
			m0f2(p000, CNT0, lc18)
			continue
		}

		if (c018) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b018) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln18), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc18)
			Store(m0f5(p000, p001, lc18), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b018)
				m0f7("b018, completed")
				break
			}
		}

		if (b018) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 18
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b017) {
			m0f2(p000, BRK0, lc17)
			break
		}
		if (c017) {
			m0f2(p000, CNT0, lc17)
			continue
		}

		if (c017) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b017) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln17), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc17)
			Store(m0f5(p000, p001, lc17), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b017)
				m0f7("b017, completed")
				break
			}
		}

		if (b017) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 17
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b016) {
			m0f2(p000, BRK0, lc16)
			break
		}
		if (c016) {
			m0f2(p000, CNT0, lc16)
			continue
		}

		if (c016) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b016) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln16), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc16)
			Store(m0f5(p000, p001, lc16), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b016)
				m0f7("b016, completed")
				break
			}
		}

		if (b016) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 16
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b015) {
			m0f2(p000, BRK0, lc15)
			break
		}
		if (c015) {
			m0f2(p000, CNT0, lc15)
			continue
		}

		if (c015) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b015) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln15), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc15)
			Store(m0f5(p000, p001, lc15), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b015)
				m0f7("b015, completed")
				break
			}
		}

		if (b015) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 15
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b014) {
			m0f2(p000, BRK0, lc14)
			break
		}
		if (c014) {
			m0f2(p000, CNT0, lc14)
			continue
		}

		if (c014) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b014) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln14), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc14)
			Store(m0f5(p000, p001, lc14), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b014)
				m0f7("b014, completed")
				break
			}
		}

		if (b014) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 14
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b013) {
			m0f2(p000, BRK0, lc13)
			break
		}
		if (c013) {
			m0f2(p000, CNT0, lc13)
			continue
		}

		if (c013) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b013) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln13), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc13)
			Store(m0f5(p000, p001, lc13), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b013)
				m0f7("b013, completed")
				break
			}
		}

		if (b013) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 13
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b012) {
			m0f2(p000, BRK0, lc12)
			break
		}
		if (c012) {
			m0f2(p000, CNT0, lc12)
			continue
		}

		if (c012) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b012) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln12), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc12)
			Store(m0f5(p000, p001, lc12), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b012)
				m0f7("b012, completed")
				break
			}
		}

		if (b012) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 12
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b011) {
			m0f2(p000, BRK0, lc11)
			break
		}
		if (c011) {
			m0f2(p000, CNT0, lc11)
			continue
		}

		if (c011) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b011) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln11), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc11)
			Store(m0f5(p000, p001, lc11), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b011)
				m0f7("b011, completed")
				break
			}
		}

		if (b011) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 11
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b010) {
			m0f2(p000, BRK0, lc10)
			break
		}
		if (c010) {
			m0f2(p000, CNT0, lc10)
			continue
		}

		if (c010) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b010) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln10), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc10)
			Store(m0f5(p000, p001, lc10), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b010)
				m0f7("b010, completed")
				break
			}
		}

		if (b010) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 10
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b009) {
			m0f2(p000, BRK0, lc09)
			break
		}
		if (c009) {
			m0f2(p000, CNT0, lc09)
			continue
		}

		if (c009) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b009) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln09), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc09)
			Store(m0f5(p000, p001, lc09), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b009)
				m0f7("b009, completed")
				break
			}
		}

		if (b009) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 09
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b008) {
			m0f2(p000, BRK0, lc08)
			break
		}
		if (c008) {
			m0f2(p000, CNT0, lc08)
			continue
		}

		if (c008) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b008) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln08), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc08)
			Store(m0f5(p000, p001, lc08), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b008)
				m0f7("b008, completed")
				break
			}
		}

		if (b008) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 08
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b007) {
			m0f2(p000, BRK0, lc07)
			break
		}
		if (c007) {
			m0f2(p000, CNT0, lc07)
			continue
		}

		if (c007) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b007) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln07), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc07)
			Store(m0f5(p000, p001, lc07), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b007)
				m0f7("b007, completed")
				break
			}
		}

		if (b007) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 07
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b006) {
			m0f2(p000, BRK0, lc06)
			break
		}
		if (c006) {
			m0f2(p000, CNT0, lc06)
			continue
		}

		if (c006) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b006) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln06), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc06)
			Store(m0f5(p000, p001, lc06), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b006)
				m0f7("b006, completed")
				break
			}
		}

		if (b006) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 06
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b005) {
			m0f2(p000, BRK0, lc05)
			break
		}
		if (c005) {
			m0f2(p000, CNT0, lc05)
			continue
		}

		if (c005) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b005) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln05), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc05)
			Store(m0f5(p000, p001, lc05), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b005)
				m0f7("b005, completed")
				break
			}
		}

		if (b005) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 05
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b004) {
			m0f2(p000, BRK0, lc04)
			break
		}
		if (c004) {
			m0f2(p000, CNT0, lc04)
			continue
		}

		if (c004) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b004) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln04), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc04)
			Store(m0f5(p000, p001, lc04), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b004)
				m0f7("b004, completed")
				break
			}
		}

		if (b004) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 04
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b003) {
			m0f2(p000, BRK0, lc03)
			break
		}
		if (c003) {
			m0f2(p000, CNT0, lc03)
			continue
		}

		if (c003) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b003) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln03), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc03)
			Store(m0f5(p000, p001, lc03), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b003)
				m0f7("b003, completed")
				break
			}
		}

		if (b003) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 03
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (b002) {
			m0f2(p000, BRK0, lc02)
			break
		}
		if (c002) {
			m0f2(p000, CNT0, lc02)
			continue
		}

		if (c002) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b002) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln02), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc02)
			Store(m0f5(p000, p001, lc02), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b002)
				m0f7("b002, completed")
				break
			}
		}

		if (b002) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 02
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (c001) {
			m0f2(p000, CNT0, lc01)
			continue
		}
		if (b001) {
			m0f2(p000, BRK0, lc01)
			break
		}

		if (c001) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b001) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln01), Local0)

		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc01)
			Store(m0f5(p000, p001, lc01), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b001)
				m0f7("b001, completed")
				break
			}
		}

		if (b001) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 01
		}

		// CAUTION: don't use below any common variables
		//          being set up before this poin.

		if (c000) {
			m0f2(p000, CNT0, lc00)
			continue
		}
		if (c000) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
		if (b000) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}

		Store(m0f5(p000, p001, ln00), Local0)
		if (LEqual(Local0, 0x07)) {
			m0f2(p000, CHL0, lc00)
			Store(m0f5(p000, p001, lc00), Local0)
			if (LEqual(Local0, 0x07)) {
				Store(1, b000)
				m0f7("b000, completed")
				break
			}
		}

		if (b000) {
			// We should not be there
			err(arg0, z074, __LINE__, 0, 0, 0, 0)
		}
	}

	////////////////////////////////////////////////////////////// FINISH, 00

	m0f8(arg0, p000, p001, tvl0)

	m0f6(p000)
}

// Run-method
Method(WHL0,, Serialized)
{
	Store("TEST: WHL0, While, Break, Continue operators", Debug)

	Name(ts, "WHL0")

	m0fa(ts, tvl0)

	return (0)
}
