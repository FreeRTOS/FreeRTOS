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
 * Bug 0096:
 *
 * SUMMARY: The ASL Compiler fails to recognize specific Uninitialized LocalX
 */

	Method(me49, 1)
	{
		Store("============= Test started:", Debug)

		if (Arg0) {

			Store(0, Local0)

		} else {

			Store("============= Before using uninitialized Local0:", Debug)

			Store(Local0, Debug)
		}

		Store("============= Test finished.", Debug)
	}

	Method(me4a, 1)
	{
		Store("============= Test started:", Debug)

		if (Arg0) {

			Store(0, Local0)

		}

		Store("============= Before using uninitialized Local0:", Debug)

		Store(Local0, Debug)

		Store("============= Test finished.", Debug)
	}

	Method(me4b)
	{
		if (SLCK) {
			CH03("", 0, 0x000, __LINE__, 0)
			me49(0)
			CH03("", 0, 0x001, __LINE__, 0)
			me4a(0)
			CH03("", 0, 0x002, __LINE__, 0)
		} else {
			CH03("", 0, 0x003, __LINE__, 0)
			me49(0)
			CH04("", 0, 49, 0, __LINE__, 0, 0) // AE_AML_UNINITIALIZED_LOCAL
			CH03("", 0, 0x005, __LINE__, 0)
			me4a(0)
			CH04("", 0, 49, 0, __LINE__, 0, 0) // AE_AML_UNINITIALIZED_LOCAL
		}
	}
