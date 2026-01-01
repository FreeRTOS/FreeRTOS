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


Method(md05,, Serialized)
{
	Event(e000)
	Mutex(mx00, 0)
	ThermalZone(tz00) {}
	Processor(pr00, 0, 0xFFFFFFFF, 0) {}
	PowerResource(pw00, 1, 0) {Method(mmmm){return (0)}}
	Method(m000) {return (0xabcd0006)}
	Device(d000) { Name(i900, 0xabcd0017) }
	OperationRegion(r000, SystemMemory, 0x100, 0x100)

	Name(i000, 0xabcd0000)
	Name(i001, 0xabcd0001)
	Name(i002, 0xabcd0002)
	Name(i003, 0xabcd0003)
	Name(i004, 0xabcd0004)
	Name(i005, 0xabcd0005)

	Store(Store(Store(Store(Store(Store(Store(Store(0x1a2b3c4d, i000), i001), i002), i003), i004), i005), d000), r000)

	if (LNotEqual(i000, 0x1a2b3c4d)) {
		err("", zFFF, __LINE__, 0, 0, i000, 0x1a2b3c4d)
	}
	if (LNotEqual(i001, 0x1a2b3c4d)) {
		err("", zFFF, __LINE__, 0, 0, i001, 0x1a2b3c4d)
	}
	if (LNotEqual(i002, 0x1a2b3c4d)) {
		err("", zFFF, __LINE__, 0, 0, i002, 0x1a2b3c4d)
	}
	if (LNotEqual(i003, 0x1a2b3c4d)) {
		err("", zFFF, __LINE__, 0, 0, i003, 0x1a2b3c4d)
	}
	if (LNotEqual(i004, 0x1a2b3c4d)) {
		err("", zFFF, __LINE__, 0, 0, i004, 0x1a2b3c4d)
	}
	if (LNotEqual(i005, 0x1a2b3c4d)) {
		err("", zFFF, __LINE__, 0, 0, i005, 0x1a2b3c4d)
	}
	Store(Refof(d000), Local0)
	if (LNotEqual(DerefOf(Local0), 0x1a2b3c4d)) {
		err("", zFFF, __LINE__, 0, 0, d000, 0x1a2b3c4d)
	}
	Store(Refof(r000), Local0)
	if (LNotEqual(DerefOf(Local0), 0x1a2b3c4d)) {
		err("", zFFF, __LINE__, 0, 0, r000, 0x1a2b3c4d)
	}

	Store(Store(Store(Store(Store(Store(Store(Store(Store(0x91827364, e000), mx00), tz00), pr00), pw00), m000), i000), d000), r000)

	Store(Refof(e000), Local0)
	if (LNotEqual(DerefOf(Local0), 0x91827364)) {
		err("", zFFF, __LINE__, 0, 0, e000, 0x91827364)
	}
	Store(Refof(mx00), Local0)
	if (LNotEqual(DerefOf(Local0), 0x91827364)) {
		err("", zFFF, __LINE__, 0, 0, mx00, 0x91827364)
	}
	Store(Refof(tz00), Local0)
	if (LNotEqual(DerefOf(Local0), 0x91827364)) {
		err("", zFFF, __LINE__, 0, 0, tz00, 0x91827364)
	}
	Store(Refof(pr00), Local0)
	if (LNotEqual(DerefOf(Local0), 0x91827364)) {
		err("", zFFF, __LINE__, 0, 0, pr00, 0x91827364)
	}
	Store(Refof(pw00), Local0)
	if (LNotEqual(DerefOf(Local0), 0x91827364)) {
		err("", zFFF, __LINE__, 0, 0, pw00, 0x91827364)
	}
	Store(Refof(m000), Local0)
	if (LNotEqual(DerefOf(Local0), 0x91827364)) {
		err("", zFFF, __LINE__, 0, 0, m000, 0x91827364)
	}
	Store(Refof(i000), Local0)
	if (LNotEqual(DerefOf(Local0), 0x91827364)) {
		err("", zFFF, __LINE__, 0, 0, i000, 0x91827364)
	}
	Store(Refof(d000), Local0)
	if (LNotEqual(DerefOf(Local0), 0x91827364)) {
		err("", zFFF, __LINE__, 0, 0, d000, 0x91827364)
	}
	Store(Refof(r000), Local0)
	if (LNotEqual(DerefOf(Local0), 0x91827364)) {
		err("", zFFF, __LINE__, 0, 0, r000, 0x91827364)
	}
}

Method(md06,, Serialized)
{
	Event(e000)
	Mutex(mx00, 0)
	ThermalZone(tz00) {}
	Processor(pr00, 0, 0xFFFFFFFF, 0) {}
	PowerResource(pw00, 1, 0) {Method(mmmm){return (0)}}
	Method(m000) {return (0xabcd0006)}
	Device(d000) { Name(i900, 0xabcd0017) }
	OperationRegion(r000, SystemMemory, 0x100, 0x100)

	Name(i000, 0xabcd0006)
	Name(i001, 0xabcd0007)
	Name(i002, 0xabcd0008)
	Name(i003, 0xabcd0009)
	Name(i004, 0xabcd000a)
	Name(i005, 0xabcd000b)
	Name(i006, 0xabcd000c)

	Store(Store(Store(Store(Store(Store(i006, i000), i001), i002), i003), i004), i005)

	if (LNotEqual(i006, i000)) {
		err("", zFFF, __LINE__, 0, 0, i006, i000)
	}
	if (LNotEqual(i006, i001)) {
		err("", zFFF, __LINE__, 0, 0, i006, i001)
	}
	if (LNotEqual(i006, i002)) {
		err("", zFFF, __LINE__, 0, 0, i006, i002)
	}
	if (LNotEqual(i006, i003)) {
		err("", zFFF, __LINE__, 0, 0, i006, i003)
	}
	if (LNotEqual(i006, i004)) {
		err("", zFFF, __LINE__, 0, 0, i006, i004)
	}
	if (LNotEqual(i006, i005)) {
		err("", zFFF, __LINE__, 0, 0, i006, i005)
	}
	if (LNotEqual(i006, i006)) {
		err("", zFFF, __LINE__, 0, 0, i006, i006)
	}
	Store(Store(Store(Store(Store(Store(Store(i006, e000), mx00), tz00), pr00), pw00), m000), i000)

	Store(Refof(e000), Local0)
	if (LNotEqual(DerefOf(Local0), i006)) {
		err("", zFFF, __LINE__, 0, 0, e000, i006)
	}
	Store(Refof(mx00), Local0)
	if (LNotEqual(DerefOf(Local0), i006)) {
		err("", zFFF, __LINE__, 0, 0, mx00, i006)
	}
	Store(Refof(tz00), Local0)
	if (LNotEqual(DerefOf(Local0), i006)) {
		err("", zFFF, __LINE__, 0, 0, tz00, i006)
	}
	Store(Refof(pr00), Local0)
	if (LNotEqual(DerefOf(Local0), i006)) {
		err("", zFFF, __LINE__, 0, 0, pr00, i006)
	}
	Store(Refof(pw00), Local0)
	if (LNotEqual(DerefOf(Local0), i006)) {
		err("", zFFF, __LINE__, 0, 0, pw00, i006)
	}
	Store(Refof(m000), Local0)
	if (LNotEqual(DerefOf(Local0), i006)) {
		err("", zFFF, __LINE__, 0, 0, m000, i006)
	}
	Store(Refof(i000), Local0)
	if (LNotEqual(DerefOf(Local0), i006)) {
		err("", zFFF, __LINE__, 0, 0, i000, i006)
	}
}

Method(md68,, Serialized)
{
	Name(i000, 0xe0385bcd)
	Event(OOO2)
	Name(p000, Package(8){})
	Name(p001, Package(8){OOO2})

	Store(Refof(OOO2), Local7)
	Store(Refof(OOO2), Index(p000, 0))

	Store(ObjectType(DeRefof(Local7)), Local0)
	if (LNotEqual(Local0, c00f)) {
		err("", zFFF, __LINE__, 0, 0, Local0, c00f)
	}
	Store(Derefof(Index(p000, 0)), Local6)
	Store(ObjectType(DeRefof(Local6)), Local0)
	if (LNotEqual(Local0, c00f)) {
		err("", zFFF, __LINE__, 0, 0, Local0, c00f)
	}

	Store(i000, OOO2)
	Store (0x61, OOO2)

	Store(DeRefof(Refof(OOO2)), Local0)

	if (LNotEqual(Local0, 0x61)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 0x61)
	}
	if (LNotEqual(i000, 0xe0385bcd)) {
		err("", zFFF, __LINE__, 0, 0, i000, 0xe0385bcd)
	}

	Store(ObjectType(DeRefof(Local7)), Local0)
	if (LNotEqual(Local0, c009)) {
		err("", zFFF, __LINE__, 0, 0, Local0, c009)
	}

	Store(Refof(OOO2), Local7)
	Store(ObjectType(DeRefof(Local7)), Local0)
	if (LNotEqual(Local0, c009)) {
		err("", zFFF, __LINE__, 0, 0, Local0, c009)
	}

	Store(ObjectType(OOO2), Local0)
	if (LNotEqual(Local0, c009)) {
		err("", zFFF, __LINE__, 0, 0, Local0, c009)
	}

	Store(Derefof(Index(p000, 0)), Local7)
	Store(ObjectType(DeRefof(Local7)), Local0)
	if (LNotEqual(Local0, c009)) {
		err("", zFFF, __LINE__, 0, 0, Local0, c009)
	}
}

Method(md69,, Serialized)
{
	Name(i000, 0xe0385bcd)
	Device(OOO2) {
		Name(i001, 0xabcd0011)
		Name(i002, 0xabcd0012)
		Name(i003, 0xabcd0013)
		Name(i004, 0xabcd0014)
		Name(i005, 0xabcd0015)
		Name(i006, 0xabcd0016)
		Name(i007, 0xabcd0017)
	}

	Store(RefOf(OOO2.i001), Local1)
	Store(RefOf(OOO2.i002), Local2)
	Store(RefOf(OOO2.i003), Local3)
	Store(RefOf(OOO2.i004), Local4)
	Store(RefOf(OOO2.i005), Local5)
	Store(RefOf(OOO2.i006), Local6)
	Store(RefOf(OOO2.i007), Local7)

	Store(i000, OOO2)
	Store (0x61, OOO2)

	Store(DeRefof(Refof(OOO2)), Local0)

	if (LNotEqual(Local0, 0x61)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 0x61)
	}
	if (LNotEqual(i000, 0xe0385bcd)) {
		err("", zFFF, __LINE__, 0, 0, i000, 0xe0385bcd)
	}

	// Are the locals save?

	Store(DerefOf(Local1), Local0)
	if (LNotEqual(Local0, 0xabcd0011)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 0xabcd0011)
	}
	Store(DerefOf(Local2), Local0)
	if (LNotEqual(Local0, 0xabcd0012)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 0xabcd0012)
	}
	Store(DerefOf(Local3), Local0)
	if (LNotEqual(Local0, 0xabcd0013)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 0xabcd0013)
	}
	Store(DerefOf(Local4), Local0)
	if (LNotEqual(Local0, 0xabcd0014)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 0xabcd0014)
	}
	Store(DerefOf(Local5), Local0)
	if (LNotEqual(Local0, 0xabcd0015)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 0xabcd0015)
	}
	Store(DerefOf(Local6), Local0)
	if (LNotEqual(Local0, 0xabcd0016)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 0xabcd0016)
	}
	Store(DerefOf(Local7), Local0)
	if (LNotEqual(Local0, 0xabcd0017)) {
		err("", zFFF, __LINE__, 0, 0, Local0, 0xabcd0017)
	}
}

Method(md07)
{
	CH03("", 0, 0xf02, __LINE__, 0)
	md05()
	md06()
	md68()
	md69()
	CH03("", 0, 0xf03, __LINE__, 0)
}
