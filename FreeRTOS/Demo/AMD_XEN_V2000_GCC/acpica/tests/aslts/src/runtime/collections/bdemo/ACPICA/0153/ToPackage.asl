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
 * Store Integer/String/Buffer/Package to Package
 */

// Integer

Method(md2d,, Serialized)
{
	Name(i000, 0xe0385bcd)
	Name(OOO2, Package(1){"Package"})

	Store(i000, OOO2)
	Store (0x61, OOO2)

	Store(DeRefof(Refof(OOO2)), Local1)

	if (LNotEqual(Local1, 0x61)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x61)
	}
	if (LNotEqual(i000, 0xe0385bcd)) {
		err("", zFFF, __LINE__, 0, 0, i000, 0xe0385bcd)
	}
}

// String

Method(md2e,, Serialized)
{
	Name(s000, "String")
	Name(OOO2, Package(1){"Package"})

	Store(s000, OOO2)
	Store (0x61, Index(OOO2, 3))

	Store(Refof(OOO2), Local0)
	Store(DeRefof(Local0), Local1)

	if (LNotEqual(Local1, "Strang")) {
		err("", zFFF, __LINE__, 0, 0, Local1, "Strang")
	}
	if (LNotEqual(s000, "String")) {
		err("", zFFF, __LINE__, 0, 0, s000, "String")
	}
}

// Buffer

Method(md2f,, Serialized)
{
	Name(b000, Buffer() {1,2,3,4})
	Name(OOO2, Package(1){Buffer() {5,6,7,8}})

	Store(b000, OOO2)
	Store (0x61, Index(OOO2, 3))

	Store(Refof(OOO2), Local0)
	Store(DeRefof(Local0), Local1)

	if (LNotEqual(Local1, Buffer() {1,2,3,0x61})) {
		err("", zFFF, __LINE__, 0, 0, Local1, Buffer() {1,2,3,0x61})
	}
	if (LNotEqual(b000, Buffer() {1,2,3,4})) {
		err("", zFFF, __LINE__, 0, 0, b000, Buffer() {1,2,3,4})
	}
}

// Package

Method(md30,, Serialized)
{
	Name(pppp, Package(1){Buffer() {1,2,3,4}})
	Name(OOO2, Package(1){Buffer() {5,6,7,8}})

	Store(pppp, OOO2)
	Store (0x61, Index(DerefOf(Index(OOO2, 0)), 3))

	// OOO2

	Store(DeRefof(Index(DerefOf(Index(OOO2, 0)), 0)), Local0)
	if (LNotEqual(Local0, 1)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 1)
	}
	Store(DeRefof(Index(DerefOf(Index(OOO2, 0)), 1)), Local0)
	if (LNotEqual(Local0, 2)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 2)
	}
	Store(DeRefof(Index(DerefOf(Index(OOO2, 0)), 2)), Local0)
	if (LNotEqual(Local0, 3)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 3)
	}
	Store(DeRefof(Index(DerefOf(Index(OOO2, 0)), 3)), Local0)
	if (LNotEqual(Local0, 0x61)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 0x61)
	}

	// pppp

	Store(DeRefof(Index(DerefOf(Index(pppp, 0)), 0)), Local0)
	if (LNotEqual(Local0, 1)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 1)
	}
	Store(DeRefof(Index(DerefOf(Index(pppp, 0)), 1)), Local0)
	if (LNotEqual(Local0, 2)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 2)
	}
	Store(DeRefof(Index(DerefOf(Index(pppp, 0)), 2)), Local0)
	if (LNotEqual(Local0, 3)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 3)
	}
	Store(DeRefof(Index(DerefOf(Index(pppp, 0)), 3)), Local0)
	if (LNotEqual(Local0, 4)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 4)
	}
}

Method(md31)
{
	CH03("", 0, 0xf10, __LINE__, 0)
	md2d()
	md2e()
	md2f()
	md30()
	CH03("", 0, 0xf11, __LINE__, 0)
}
