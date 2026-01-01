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
 * Tests applicable to both AcpiExec and MS-abbu utilities
 */
DefinitionBlock("extra.aml", "DSDT", 0x1, "INTEL", "ABCDE", 0x1)
{
	Scope(\_SB)
	{
		Device(ABBU)
		{
			Name(_HID, "ACPIABB0")
			Method(ENBL)
			{
				Return(Zero)
			}

			Method(TEST)
			{
				Return(Zero)
			}

			Method(TST)
			{
				Return(TSTS)
			}

	/* Definitions of common use */

	/*
	 * AI00:
	 *
	 * The abbu utility provides some restricted amount of elements of POUT,
	 * it is not the constant number of elements of Package (!), not good interface,
	 * but looks like some restricted amount of memory. When that variable number of
	 * elements is exceeded, abbu returns FAILURE which we can't differentiate from
	 * the actual failure of MS being examined. So, don't use the big AI00 to be sure
	 * that returned FAILURE, if any, is not caused by the mentioned fact.
	 */
	Name (AI00, 17) // MAX
	Name (POUT, Package(17) {})

	Name (AI01, 0) // current OUT
	Name (AI02, 0) // counter of lost POUT messages
	Name (AI07, 0) // print once only the end-message
	Name (AI08, 0) // total number of messages

	Method(OUUP, 2)
	{
		/* Last 6 lines are reserved for the test run summary and end-message */
		Subtract(AI00, 6, Local0)

		if (LLess(AI01, Local0)) {
			Store(arg0, Index(POUT, AI01))
			Increment(AI01)
		} else {
			/* Last 2 lines are reserved for the end-message */
			Subtract(AI00, 2, Local0)
			if (LAnd(arg1, LLess(AI01, Local0))) {
				Store(arg0, Index(POUT, AI01))
				Increment(AI01)
			} else {
				if (LNot(AI07)) {
					Store(1, AI07)
					Subtract(AI00, 2, Local0)
					Store("******** POUT exceeded ********", Index(POUT, Local0))
				}
			}
		}

		/* Last element of POUT is the total number of messages */

		Increment(AI08)
		Subtract(AI00, 1, Local0)
		Store(AI08, Index(POUT, Local0))
	}

	Method(OUTP, 1)
	{
		OUUP(arg0, 0)
	}

	/*
	 * Reset POUT service to the initial state
	 */
	Method(RST9,, Serialized)
	{
		Name(lpN0, 0)
		Name(lpC0, 0)

		Store (0, AI01)
		Store (0, AI02)
		Store (0, AI07)
		Store (0, AI08)

		Store(AI00, lpN0)
		Store(0, lpC0)
		While (lpN0) {
			Store(" ", Index(POUT, lpC0))
			Decrement(lpN0)
			Increment(lpC0)
		}

		Subtract(AI00, 2, Local0)
		Store("Total number of messages:", Index(POUT, Local0))
		Increment(Local0)
		Store(0, Index(POUT, Local0))
	}

// ====================================================== //
// ====================================================== //
// ====================================================== //

/* Definitions relative to the subject */

Include("./DECL_ABBU.asl")

// ====================================================== //
// ====================================================== //
// ====================================================== //


			Name(TSTS, Package()
			{
				"ENBL",
				"TEST",
				"TST_",
				"MAIN",
				"IN00",
			})
		}
	}
	Method(MAIN)
	{
		Return (\_SB_.ABBU.MAIN())
	}
	Method(MN00)
	{
		Return (\_SB_.ABBU.MN00())
	}
	Method(MN01)
	{
		Return (\_SB_.ABBU.MN01())
	}
}
