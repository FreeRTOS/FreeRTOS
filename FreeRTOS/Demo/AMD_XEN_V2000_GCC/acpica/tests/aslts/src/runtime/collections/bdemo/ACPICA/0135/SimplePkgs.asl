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
 * Checkings for simple one-level hierarchy of Packages.
 *
 * 0x5C Outstanding allocations because of
 * AcpiExec doesn't run the unload of the table have been processed.
 *
 * Outstanding: 0x5C allocations after execution.
 */

Method(mfc5,, Serialized)
{
	Name(num0, 12)	// different types of packages Pkg0 and Pkg1
	Name(num1, 19)	// opcodes of additional assignments of packages Pkg0 and Pkg1
	Name(num2, 13)	// max opcode of additional assignments of References (0-12)
	Name(cur0, 0)	// cur opcode of additional assignments of References (0-12)
	Name(i000, 0)

	Name(AR20, 0)

	Name(lpN0, 0)
	Name(lpC0, 0)

	Name(lpN1, 0)
	Name(lpC1, 0)

	Name(loc0, Package(Multiply(id26, 2)) {})
	Name(loc1, Package(Multiply(id26, 2)) {})


	Store(num1, lpN1)
	Store(0, lpC1)

	SRMT("Simple-Pkg")

	While (lpN1) {

		Store(num0, lpN0)
		Store(0, lpC0)

		While (lpN0) {

			Divide(i000, num2, cur0)
			Increment(i000)

			Store(mfc9(lpC1, lpC0, 0, 0, cur0), Local0)
			mfc6(loc0, loc1, Local0,   0, 0,   0, 0)

			Divide(i000, num2, cur0)
			Increment(i000)

			Store(mfc9(lpC1, lpC0, 0, 1, cur0), Local0)
			mfc6(loc0, loc1, Local0,   0, 0,   0, 0)

			Divide(i000, num2, cur0)
			Increment(i000)

			Store(mfc9(lpC1, lpC0, 1, 0, cur0), Local0)
			mfc6(loc0, loc1, Local0,   0, 0,   0, 0)

			Divide(i000, num2, cur0)
			Increment(i000)

			Store(mfc9(lpC1, lpC0, 1, 1, cur0), Local0)
			mfc6(loc0, loc1, Local0,   0, 0,   0, 0)


			Decrement(lpN0)
			Increment(lpC0)
		}

		Decrement(lpN1)
		Increment(lpC1)
	}

	/*
	 * To eliminate the known outstanding allocations -
	 * releasing of global data are not forces by AcpiExec -
	 * no unload of the processed ACPI table is automatically
	 * initiated by AcpiExec after completion the ex command.
	 */
	if (0) {
		mfe8()
	}
}
