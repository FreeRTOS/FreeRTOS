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
 * Store Integer/String/Buffer/Package to Device
 */

// Integer

Method(md0f,, Serialized)
{
	Name(i000, 0xe0385bcd)
	Device(OOO2) { Name(i900, 0xabcd0017) }

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

Method(md10,, Serialized)
{
	Name(s000, "String")
	Device(OOO2) { Name(i900, 0xabcd0017) }

	Store(s000, OOO2)
	Store(Refof(OOO2), Local0)
	Store (0x61, Index(DeRefof(Local0), 3))

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

Method(md11,, Serialized)
{
	Name(b000, Buffer() {1,2,3,4})
	Device(OOO2) { Name(i900, 0xabcd0017) }

	Store(b000, OOO2)

	Store(Refof(OOO2), Local0)
	Store (0x61, Index(DeRefof(Local0), 3))
	Store(DeRefof(Local0), Local1)

	if (LNotEqual(Local1, Buffer() {1,2,3,0x61})) {
		err("", zFFF, __LINE__, 0, 0, Local1, Buffer() {1,2,3,0x61})
	}
	if (LNotEqual(b000, Buffer() {1,2,3,4})) {
		err("", zFFF, __LINE__, 0, 0, b000, Buffer() {1,2,3,4})
	}
}

// Package

Method(md12,, Serialized)
{
	Name(pppp, Package(1){Buffer() {1,2,3,4}})
	Device(OOO2) { Name(i900, 0xabcd0017) }

	Store(pppp, OOO2)
	Store(Refof(OOO2), Local0)
	Store (0x61, Index(DerefOf(Index(DeRefof(Local0), 0)), 3))

	// OOO2

	Store(DeRefof(Index(DerefOf(Index(DeRefof(Local0), 0)), 0)), Local1)
	if (LNotEqual(Local1, 1)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 1)
	}
	Store(DeRefof(Index(DerefOf(Index(DeRefof(Local0), 0)), 1)), Local1)
	if (LNotEqual(Local1, 2)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 2)
	}
	Store(DeRefof(Index(DerefOf(Index(DeRefof(Local0), 0)), 2)), Local1)
	if (LNotEqual(Local1, 3)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 3)
	}
	Store(DeRefof(Index(DerefOf(Index(DeRefof(Local0), 0)), 3)), Local1)
	if (LNotEqual(Local1, 0x61)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x61)
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

/* Constant */

// Integer

Method(md13,, Serialized)
{
	Device(OOO2) { Name(i900, 0xabcd0017) }

	Store(0xe0385bcd, OOO2)
	Store (0x61, OOO2)

	Store(DeRefof(Refof(OOO2)), Local1)

	if (LNotEqual(Local1, 0x61)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x61)
	}
}

// String

Method(md14,, Serialized)
{
	Device(OOO2) { Name(i900, 0xabcd0017) }

	Store("String", OOO2)
	Store(Refof(OOO2), Local0)
	Store (0x61, Index(DeRefof(Local0), 3))

	Store(Refof(OOO2), Local0)
	Store(DeRefof(Local0), Local1)

	if (LNotEqual(Local1, "Strang")) {
		err("", zFFF, __LINE__, 0, 0, Local1, "Strang")
	}
}

// Buffer

Method(md15,, Serialized)
{
	Device(OOO2) { Name(i900, 0xabcd0017) }

	Store(Buffer() {1,2,3,4}, OOO2)

	Store(Refof(OOO2), Local0)
	Store (0x61, Index(DeRefof(Local0), 3))
	Store(DeRefof(Local0), Local1)

	if (LNotEqual(Local1, Buffer() {1,2,3,0x61})) {
		err("", zFFF, __LINE__, 0, 0, Local1, Buffer() {1,2,3,0x61})
	}
}

// Package

Method(md16,, Serialized)
{
	Device(OOO2) { Name(i900, 0xabcd0017) }

	Store(Package(1){Buffer() {1,2,3,4}}, OOO2)
	Store(Refof(OOO2), Local0)
	Store (0x61, Index(DerefOf(Index(DeRefof(Local0), 0)), 3))

	// OOO2

	Store(DeRefof(Index(DerefOf(Index(DeRefof(Local0), 0)), 0)), Local1)
	if (LNotEqual(Local1, 1)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 1)
	}
	Store(DeRefof(Index(DerefOf(Index(DeRefof(Local0), 0)), 1)), Local1)
	if (LNotEqual(Local1, 2)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 2)
	}
	Store(DeRefof(Index(DerefOf(Index(DeRefof(Local0), 0)), 2)), Local1)
	if (LNotEqual(Local1, 3)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 3)
	}
	Store(DeRefof(Index(DerefOf(Index(DeRefof(Local0), 0)), 3)), Local1)
	if (LNotEqual(Local1, 0x61)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x61)
	}
}

Method(md17)
{
	CH03("", 0, 0xf06, __LINE__, 0)
	md0f()
	md10()
	md11()
	md12()
	md13()
	md14()
	md15()
	md16()
	CH03("", 0, 0xf07, __LINE__, 0)
}
