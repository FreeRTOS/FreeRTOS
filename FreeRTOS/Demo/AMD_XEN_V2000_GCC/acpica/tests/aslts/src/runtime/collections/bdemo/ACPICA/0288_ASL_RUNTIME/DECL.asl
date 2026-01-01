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
 * Bug 288:
 *
 * SUMMARY: iASL unexpectedly forbids ParameterData of Loadtable to be LocalX or UserTerm
 */

Device (D288) {
	Name(PLDT, 0)

	Method(m000, 1) {Return (Arg0)}

	Method(T288)
	{
		Store(1, Local0)

		Store(LoadTable("OEM1", "", "", , "\\D288.PLDT", Local0), Local1)

		if (LNotEqual(PLDT, 1)) {
			err("", zFFF, __LINE__, 0, 0, PLDT, 1)
		}

		UnLoad(Local1)

		Store(LoadTable("OEM1", "", "", , "\\PLDT", m000(2)), Local1)

		if (LNotEqual(PLDT, 2)) {
			err("", zFFF, __LINE__, 0, 0, PLDT, 2)
		}

		UnLoad(Local1)
	}
}

Method(m288)
{
	\D288.T288()
}
