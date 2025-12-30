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
 * Bug 121:
 *
 * SUMMARY: Crash on attempt to deal with the invalid BufferFields (zero NumBits passed to CreateField)
 *
 * This DECL.asl is for iASL compiler, it should result in Error for this DECL.asl.
 */

	Method(mf03)
	{
		Name(b000, Buffer(2){0xff, 0xff})

		CH03("", 0, 0x000, __LINE__, 0)
		CreateField(b000, 0,16, bf00)
		CH03("", 0, 0x000, __LINE__, 0)

		CH03("", 0, 0x002, __LINE__, 0)
		CreateField(b000, 0, 0, bf01)
		CH04("", 0, 0xff, 0, __LINE__, 0, 0)

		CH03("", 0, 0x004, __LINE__, 0)
		CreateField(b000, 1, 0, bf02)
		CH04("", 0, 0xff, 0, __LINE__, 0, 0)

		CH03("", 0, 0x006, __LINE__, 0)
		CreateField(b000, 7, 0, bf03)
		CH04("", 0, 0xff, 0, __LINE__, 0, 0)

		CH03("", 0, 0x008, __LINE__, 0)
		CreateField(b000, 8, 0, bf04)
		CH04("", 0, 0xff, 0, __LINE__, 0, 0)

		CH03("", 0, 0x00a, __LINE__, 0)
		CreateField(b000,15, 0, bf05)
		CH04("", 0, 0xff, 0, __LINE__, 0, 0)

		CH03("", 0, 0x00c, __LINE__, 0)
		CreateField(b000,16, 0, bf06)
		CH04("", 0, 0xff, 0, __LINE__, 0, 0)

		CH03("", 0, 0x00e, __LINE__, 0)

		Store("All CreateField-s finished", Debug)

		Store(bf00, Debug)
		Store(bf01, Debug)
		Store(bf02, Debug)
		Store(bf03, Debug)
		Store(bf04, Debug)
		Store(bf05, Debug)
		Store(bf06, Debug)

		CH04("", 0, 0xff, 0, __LINE__, 0, 0)

		Store("All Store-to-Debug-s finished", Debug)
	}
