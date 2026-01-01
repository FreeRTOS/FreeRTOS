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
 * Bug 168:
 *
 * SUMMARY: Wrong specific Package obtained for not optimized AML code
 *
 * The demo shows different behavior of the AML codes
 * obtained without and with -oa option:
 *
 * Method(mf59, 1) {Return(Index(Package(){2, 12}, arg0)}
 * Both AML codes deal with 2-element Packages, but unexpectedly
 * the elements of the Package in the not optimized case are:
 *
 *   [ACPI Debug] (00) Integer: 0x000000000000000C
 *   [ACPI Debug] (01) <Null Object>
 *
 * against the properly built elements in the optimized case:
 *
 *   [ACPI Debug] (00) Integer: 0x0000000000000002
 *   [ACPI Debug] (01) Integer: 0x000000000000000C
 *
 *
 * NOTE: run it in both modes - opt & nopt
 */

	Method(mf59, 1) {Return (Index(Package(){2, 12}, arg0))}

	Method(mf5a)
	{
		Store(mf59(0), Debug)

		Store(mf59(0), Local0)
		Store(DerefOf(Local0), Local1)
		if (LNotEqual(Local1, 2)){
			err("", zFFF, __LINE__, 0, 0, Local1, 2)
		}

		Store(mf59(1), Debug)

		Store(mf59(1), Local0)
		Store(DerefOf(Local0), Local1)
		if (LNotEqual(Local1, 12)){
			err("", zFFF, __LINE__, 0, 0, Local1, 12)
		}
	}
