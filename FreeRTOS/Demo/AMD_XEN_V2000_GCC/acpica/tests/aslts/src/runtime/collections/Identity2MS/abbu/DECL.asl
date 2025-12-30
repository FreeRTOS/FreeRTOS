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
in progress:

Do these:
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
+++ 1) clean up the current set of tests
+++ 2) Make automatically aslst_abbu.aml which include the original common.asl and ehandle.asl files
+++ 3) introduce 'stack' directory for the stuff from ns8
+++ 4) slways should be place in POUT for lines below:
       OUTP(":STST:Identity2MS:abbu:mmmm:FAIL:Errors # 12 34 56 78:")
       OUTP(":STST:Identity2MS:abbu:mmmm:PASS:")
       Store("******** POUT exceeded ********, number of lost messages:", Index(POUT, Local0))
+++ 3) do the method examples and run points for each of the enumerated by 'Stuff not working under MS'

4) add the tests of namespace test case with the root names \_SB.d000.p000 ...
10) do ns6
   .....
11) develop the test to achieve cover, do methodically other urgent tests inside abbu
12) complete the namespace test case
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
13) fix bug of m01e
 *
 */

/*
 * Common declarations
 */

/*
 * Broke ACPICA (m01e)
 *
 * 0 - blocks execution
 */
Name(fix0, 1) // blocks m01e
Name(fix1, 1) // causes break of path for ACPICA

/*
 * Do additional checking
 */
Name(chk0, 0) // use it for those which break execution on MS (should be 0 for run on MS)
Name(chk1, 1) // use it for those which don't break execution on MS
Name(chk2, 0) // use it for those which break execution while re-bootin on MS

Name(prt0, 0) // conditional OUTP printing

Name(SLC0, 0) // modification of SCLK

/*
 * Initialization of msfail
 */
Method(IIN1)
{
	if (run4) {
		Store(1, y262)
		Store(1, y275)
		Store(1, SLC0)
		Store(0, SLCK)
	} else {
		OUTP("WARNING: don't forget to check run4 !!!!!!!!!!")

		Store(0, SLC0)
		if (SLCK) {
			Store(1, SLC0)
		}
	}

	if (ABUU) {
		Store(0, chk0)
		Store(1, chk1)
		Store(0, chk2)
		Store(0, fix0)
		Store(0, fix1)
	} else {
		Store(1, chk0)
		Store(1, chk1)
		Store(1, chk2)
		Store(1, fix0)
		Store(0, fix1)
	}
}

Include("./run_points.asl")

// NameSpace

// Initial
Include("./initial/ns_in00.asl")
Include("./initial/ns_in10.asl")
Include("./initial/ns_in20.asl")
Include("./initial/ns_in30.asl")
Include("./initial/ns_in40.asl")
Include("./initial/ns_in50.asl")

// Device
// Include("./device/ns_dv00.asl")
Include("./device/device.asl")

// Include("./ns3.asl")
Include("./ns4.asl")
Include("./ns6.asl")

// Miscellaneous

Include("./misc/ms0.asl")
Include("./misc/ms1.asl")

// MsFail

Include("./MsFail/msfail.asl")


// Specific initialization of abbu

// Reset to the initial state
Method(RST8)
{
	Store(0, ERRS)
	Store(0, RMRC)
}

// Specific initialization of abbu
Method(IIN0)
{
	// Reset to the initial state
	RST8()

	// Reset POUT service to the initial state
	RST9()

	// Initialization of msfail
	IIN1()
}

// Conditional output
Method(OUTC, 1)
{
	if (prt0) {
		OUTP(arg0)
	}
}

// Run the tests

Method(MAIN) {

	// Initialization
	STRT(0)

	// Specific initialization of abbu
	IIN0()

	// Run verification methods
	Include("./RUN.asl")

	// Final actions
	Store(FNSH(), Local7)

	if (ABUU) {
		Return(POUT)
	}
	Return(Local7)
}
