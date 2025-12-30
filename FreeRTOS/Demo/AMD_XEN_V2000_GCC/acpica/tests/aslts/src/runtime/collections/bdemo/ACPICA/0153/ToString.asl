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
 * Store Integer/String/Buffer to String
 */

// Integer

Method(md4d,, Serialized)
{
	Name(i000, 0xabcd)
	Name(s000, "String")

	Store(i000, s000)
	Store (0x61, s000)

	if (LNotEqual(s000, 0x61)) {
		err("", zFFF, __LINE__, 0, 0, s000, 0x61)
	}
	if (LNotEqual(i000, 0xabcd)) {
		err("", zFFF, __LINE__, 0, 0, i000, 0xabcd)
	}
}

// String

Method(md4e,, Serialized)
{
	Name(s000, "zxcvbqwertynm")
	Name(s001, "String")

	Store(s000, s001)
	Store("ADb", s001)

	if (LNotEqual(s001, "ADb")) {
		err("", zFFF, __LINE__, 0, 0, s001, "ADb")
	}
	if (LNotEqual(s000, "zxcvbqwertynm")) {
		err("", zFFF, __LINE__, 0, 0, s000, "zxcvbqwertynm")
	}
}

// Buffer

Method(md4f,, Serialized)
{
	Name(b000, Buffer() {1,2,3,4})
	Name(s000, "String")

	Store(b000, s000)
	Store (Buffer() {5,6}, s000)

	if (LNotEqual(s000, Buffer() {5,6})) {
		err("", zFFF, __LINE__, 0, 0, s000, Buffer() {5,6})
	}
	if (LNotEqual(b000, Buffer() {1,2,3,4})) {
		err("", zFFF, __LINE__, 0, 0, b000, Buffer() {1,2,3,4})
	}
}

Method(md50)
{
	CH03("", 0, 0xf18, __LINE__, 0)
	md4d()
	md4e()
	md4f()
	CH03("", 0, 0xf19, __LINE__, 0)
}
