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
 * Store Integer/String/Buffer to Integer
 */

// Integer

Method(md59,, Serialized)
{
	Name(i000, 0)
	Name(i001, 1)

	Store(i000, i001)
	Store (0x61, i001)

	if (LNotEqual(i001, 0x61)) {
		err("", zFFF, __LINE__, 0, 0, i001, 0x61)
	}
	if (LNotEqual(i000, 0)) {
		err("", zFFF, __LINE__, 0, 0, i000, 0)
	}
}

// String

Method(md21,, Serialized)
{
	Name(s000, "String")
	Name(i000, 0x1234)

	Store(s000, i000)
	Store(0x61, i000)

	if (LNotEqual(i000, 0x61)) {
		err("", zFFF, __LINE__, 0, 0, i000, 0x61)
	}
	if (LNotEqual(s000, "String")) {
		err("", zFFF, __LINE__, 0, 0, s000, "String")
	}
}

// Buffer

Method(md22,, Serialized)
{
	Name(b000, Buffer() {1,2,3,4})
	Name(i000, 0x5678)

	Store(b000, i000)
	Store (0x61, i000)

	if (LNotEqual(i000, 0x61)) {
		err("", zFFF, __LINE__, 0, 0, i000, 0x61)
	}
	if (LNotEqual(b000, Buffer() {1,2,3,4})) {
		err("", zFFF, __LINE__, 0, 0, b000, Buffer() {1,2,3,4})
	}
}

Method(md23)
{
	CH03("", 0, 0xf0c, __LINE__, 0)
	md59()
	md21()
	md22()
	CH03("", 0, 0xf0d, __LINE__, 0)
}
