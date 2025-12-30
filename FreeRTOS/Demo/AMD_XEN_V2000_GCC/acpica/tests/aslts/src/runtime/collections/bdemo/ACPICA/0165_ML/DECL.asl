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
 * Bug 165:
 *
 * SUMMARY: Unnecessary memory allocation for CreateField should be eliminated
 *
 * Only, to run some CreateField-s (it is
 * checked completely by the bfield.asl test)
 */

	Method(mf4d)
	{
		CreateField(bd0a, 0, 8, bfd2)
	}

	Method(mf4e)
	{
		Name(b001, Buffer(9){0x20,0x21,0x22,0x23})

		CreateField(bd0a, 8, 8, bf01)

		CreateField(b001, 0, 8, bf02)

		Store(bfd2, Debug)
		if (LNotEqual(bfd2, 0x10)) {
			Store("Error 0", Debug)
		} else {
			Store("Ok 0", Debug)
		}

		Store(bf01, Debug)
		if (LNotEqual(bf01, 0x11)) {
			Store("Error 1", Debug)
		} else {
			Store("Ok 1", Debug)
		}

		Store(bf02, Debug)
		if (LNotEqual(bf02, 0x20)) {
			Store("Error 2", Debug)
		} else {
			Store("Ok 2", Debug)
		}
	}
