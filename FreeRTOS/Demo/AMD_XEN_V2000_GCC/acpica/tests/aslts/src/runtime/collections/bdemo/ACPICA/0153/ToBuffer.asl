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
 * Store Integer/String/Buffer to Buffer
 */

// Integer

Method(md08,, Serialized)
{
	Name(i000, 0xabcd)
	Name(b000, Buffer() {1,2,3,4})

	Store(i000, b000)
	Store (0x61, b000)

	if (LNotEqual(b000, Buffer() {0x61,0,0,0})) {
		err("", zFFF, __LINE__, 0, 0, b000, Buffer() {0x61,0,0,0})
	}
	if (LNotEqual(i000, 0xabcd)) {
		err("", zFFF, __LINE__, 0, 0, i000, 0xabcd)
	}
}

// String

Method(md09,, Serialized)
{
	Name(s000, "zxcvbqwertynm")
	Name(b000, Buffer() {1,2,3,4})

	Store(s000, b000)
	Store("ADb", b000)

	if (LNotEqual(b000, Buffer() {0x41,0x44,0x62,0})) {
		err("", zFFF, __LINE__, 0, 0, b000, Buffer() {0x41,0x44,0x62,0})
	}
	if (LNotEqual(s000, "zxcvbqwertynm")) {
		err("", zFFF, __LINE__, 0, 0, s000, "zxcvbqwertynm")
	}
}

// Buffer

Method(md0a,, Serialized)
{
	Name(b000, Buffer() {1,2,3,4})
	Name(b001, Buffer() {5,6,7,8})

	Store(b000, b001)
	Store (Buffer() {5,6}, b001)

	if (LNotEqual(b001, Buffer() {5,6,0,0})) {
		err("", zFFF, __LINE__, 0, 0, b001, Buffer() {5,6,0,0})
	}
	if (LNotEqual(b000, Buffer() {1,2,3,4})) {
		err("", zFFF, __LINE__, 0, 0, b000, Buffer() {1,2,3,4})
	}
}

/* Constants */

// Integer

Method(md0b,, Serialized)
{
	Name(b000, Buffer() {1,2,3,4})

	Store(0xabcd, b000)
	Store (0x61, b000)

	if (LNotEqual(b000, Buffer() {0x61,0,0,0})) {
		err("", zFFF, __LINE__, 0, 0, b000, Buffer() {0x61,0,0,0})
	}
}

// String

Method(md0c,, Serialized)
{
	Name(b000, Buffer() {1,2,3,4})

	Store("zxcvbqwertynm", b000)
	Store("ADb", b000)

	if (LNotEqual(b000, Buffer() {0x41,0x44,0x62,0})) {
		err("", zFFF, __LINE__, 0, 0, b000, Buffer() {0x41,0x44,0x62,0})
	}
}

// Buffer

Method(md0d,, Serialized)
{
	Name(b001, Buffer() {5,6,7,8})

	Store(Buffer() {1,2,3,4}, b001)
	Store (Buffer() {5,6}, b001)

	if (LNotEqual(b001, Buffer() {5,6,0,0})) {
		err("", zFFF, __LINE__, 0, 0, b001, Buffer() {5,6,0,0})
	}
}

Method(m00e)
{
	CH03("", 0, 0xf04, __LINE__, 0)
	md08()
	md09()
	md0a()
	md0b()
	md0c()
	md0d()
	CH03("", 0, 0xf05, __LINE__, 0)
}
