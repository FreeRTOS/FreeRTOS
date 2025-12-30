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

DefinitionBlock(
	"B251.aml", // Output filename
	"DSDT",     // Signature
	0x02,       // DSDT Revision
	"Intel",    // OEMID
	"Many",     // TABLE ID
	0x00000001  // OEM Revision
	) {

	// All declarations
	Include("../../../../../runtime/cntl/common.asl")
	Include("../../../../../runtime/cntl/mt_runpoint.asl")
	Include("../../../../../runtime/cntl/runmode.asl")
	Include("../../../../../runtime/cntl/ehandle.asl")

	Name(num, 10) // repetition of While number

	Method(m02b)
	{
		Store("================ Test m02b started", Debug)
		Store(num, Local0)
		While (Local0) {
			Concatenate("Iteration ", Local0, Debug)
			Store(0, Local3)
			Switch (Local3) {
				Case (0) {
					Store("Case (0)", Debug)
				}
			}
			Sleep(100)
			Decrement(Local0)
		}
		Store("================ Test m02b completed", Debug)
	}

	/* The same as m02b but without While */
	Method(m02c)
	{
		Store("================ Test m02c started", Debug)
		Store(num, Local0)
		// While (Local0) {
			Concatenate("Iteration ", Local0, Debug)
			Store(0, Local3)
			Switch (Local3) {
				Case (0) {
					Store("Case (0)", Debug)
				}
			}
			Sleep(100)
			Decrement(Local0)
		// }
		Store("================ Test m02c completed", Debug)
	}

	/*
	 * Note: advanced for mt-tests -
	 *	in case of Threads command
	 *	the arguments passed to method are:
	 *
	 * arg0 - total number of threads created by Threads command
	 * arg1 - ID of the current thread
	 * arg2 - index of the current thread (0, 1, 2 ... )
	 */
	Method(MAIN, 3) {

		// Initialization
		STRT(0)

		// Run verification methods

		CH03("", 0, 0x000, __LINE__, 0)

		if (LEqual(arg1, "AML Debugger")) {
			Store("========== args of Execute command of AcpiExec:", Debug)
			Store(arg0, Debug)
			Store(arg1, Debug)
			Store("==========.", Debug)
		} else {
			Store("========== args of Threads command of AcpiExec:", Debug)
			Store(arg0, Debug)
			Store(arg1, Debug)
			Store(arg2, Debug)
			Store("==========.", Debug)

			if (1) {
				m02b()
			} else {
				m02c()
			}
		}

		CH03("", 0, 0x001, __LINE__, 0)

		// Final actions
		Store(FNSH(), Local7)

		return (Local7)
	}
}
