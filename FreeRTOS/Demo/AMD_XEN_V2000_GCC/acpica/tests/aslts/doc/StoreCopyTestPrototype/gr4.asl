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


DefinitionBlock(
	"gr4.aml",   // Output filename
	"DSDT",     // Signature
	0x02,       // DSDT Revision
	"Intel",    // OEMID
	"Many",     // TABLE ID
	0x00000001  // OEM Revision
	) {

	Method(mm04)
	{
		Store("Store to NamedX without any conversion", Debug)

		Store("mm04 started", Debug)


		Name(i000, 0x12345678)
		Name(i001, 0x12345678)
		Name(i002, 0x12345678)
		Name(i003, 0x12345678)
		Name(i004, 0x12345678)
		Name(i005, 0x12345678)
		Name(i006, 0x12345678)
		Name(i007, 0x12345678)
		Name(i008, 0x12345678)
		Name(i009, 0x12345678)
		Name(i00a, 0x12345678)
		Name(i00b, 0x12345678)

		Name(s000, "12345678")
		Name(s001, "12345678")
		Name(s002, "12345678")
		Name(s003, "12345678")
		Name(s004, "12345678")
		Name(s005, "12345678")
		Name(s006, "12345678")
		Name(s007, "12345678")
		Name(s008, "12345678")
		Name(s009, "12345678")
		Name(s00a, "12345678")
		Name(s00b, "12345678")

		Name(b000, Buffer() {1,2,3,4,5})
		Name(b001, Buffer() {1,2,3,4,5})
		Name(b002, Buffer() {1,2,3,4,5})
		Name(b003, Buffer() {1,2,3,4,5})
		Name(b004, Buffer() {1,2,3,4,5})
		Name(b005, Buffer() {1,2,3,4,5})
		Name(b006, Buffer() {1,2,3,4,5})
		Name(b007, Buffer() {1,2,3,4,5})
		Name(b008, Buffer() {1,2,3,4,5})
		Name(b009, Buffer() {1,2,3,4,5})
		Name(b00a, Buffer() {1,2,3,4,5})
		Name(b00b, Buffer() {1,2,3,4,5})

		Name(p000, Package() {0})
		Name(p001, Package() {0})
		Name(p002, Package() {0})
		Name(p003, Package() {0})
		Name(p004, Package() {0})
		Name(p005, Package() {0})
		Name(p006, Package() {0})
		Name(p007, Package() {0})
		Name(p008, Package() {0})
		Name(p009, Package() {0})
		Name(p00a, Package() {0})
		Name(p00b, Package() {0})

		Device(d000) { Name(i900, 0xabcd0017) }
		Device(d001) { Name(i900, 0xabcd0017) }
		Device(d002) { Name(i900, 0xabcd0017) }
		Device(d003) { Name(i900, 0xabcd0017) }
		Device(d004) { Name(i900, 0xabcd0017) }
		Device(d005) { Name(i900, 0xabcd0017) }
		Device(d006) { Name(i900, 0xabcd0017) }
		Device(d007) { Name(i900, 0xabcd0017) }
		Device(d008) { Name(i900, 0xabcd0017) }
		Device(d009) { Name(i900, 0xabcd0017) }
		Device(d00a) { Name(i900, 0xabcd0017) }
		Device(d00b) { Name(i900, 0xabcd0017) }

		Event(e000)
		Event(e001)
		Event(e002)
		Event(e003)
		Event(e004)
		Event(e005)
		Event(e006)
		Event(e007)
		Event(e008)
		Event(e009)
		Event(e00a)
		Event(e00b)

		Method(m000) { return (0) }
		Method(m001) { return (0) }
		Method(m002) { return (0) }
		Method(m003) { return (0) }
		Method(m004) { return (0) }
		Method(m005) { return (0) }
		Method(m006) { return (0) }
		Method(m007) { return (0) }
		Method(m008) { return (0) }
		Method(m009) { return (0) }
		Method(m00a) { return (0) }
		Method(m00b) { return (0) }

		Mutex(mx00, 0)
		Mutex(mx01, 0)
		Mutex(mx02, 0)
		Mutex(mx03, 0)
		Mutex(mx04, 0)
		Mutex(mx05, 0)
		Mutex(mx06, 0)
		Mutex(mx07, 0)
		Mutex(mx08, 0)
		Mutex(mx09, 0)
		Mutex(mx0a, 0)
		Mutex(mx0b, 0)

		OperationRegion(r000, SystemMemory, 0x100, 0x100)
		OperationRegion(r001, SystemMemory, 0x100, 0x100)
		OperationRegion(r002, SystemMemory, 0x100, 0x100)
		OperationRegion(r003, SystemMemory, 0x100, 0x100)
		OperationRegion(r004, SystemMemory, 0x100, 0x100)
		OperationRegion(r005, SystemMemory, 0x100, 0x100)
		OperationRegion(r006, SystemMemory, 0x100, 0x100)
		OperationRegion(r007, SystemMemory, 0x100, 0x100)
		OperationRegion(r008, SystemMemory, 0x100, 0x100)
		OperationRegion(r009, SystemMemory, 0x100, 0x100)
		OperationRegion(r00a, SystemMemory, 0x100, 0x100)
		OperationRegion(r00b, SystemMemory, 0x100, 0x100)

		PowerResource(pw00, 1, 0) {}
		PowerResource(pw01, 1, 0) {}
		PowerResource(pw02, 1, 0) {}
		PowerResource(pw03, 1, 0) {}
		PowerResource(pw04, 1, 0) {}
		PowerResource(pw05, 1, 0) {}
		PowerResource(pw06, 1, 0) {}
		PowerResource(pw07, 1, 0) {}
		PowerResource(pw08, 1, 0) {}
		PowerResource(pw09, 1, 0) {}
		PowerResource(pw0a, 1, 0) {}
		PowerResource(pw0b, 1, 0) {}

		Processor(pr00, 0, 0xFFFFFFFF, 0) {}
		Processor(pr01, 0, 0xFFFFFFFF, 0) {}
		Processor(pr02, 0, 0xFFFFFFFF, 0) {}
		Processor(pr03, 0, 0xFFFFFFFF, 0) {}
		Processor(pr04, 0, 0xFFFFFFFF, 0) {}
		Processor(pr05, 0, 0xFFFFFFFF, 0) {}
		Processor(pr06, 0, 0xFFFFFFFF, 0) {}
		Processor(pr07, 0, 0xFFFFFFFF, 0) {}
		Processor(pr08, 0, 0xFFFFFFFF, 0) {}
		Processor(pr09, 0, 0xFFFFFFFF, 0) {}
		Processor(pr0a, 0, 0xFFFFFFFF, 0) {}
		Processor(pr0b, 0, 0xFFFFFFFF, 0) {}

		ThermalZone(tz00) {}
		ThermalZone(tz01) {}
		ThermalZone(tz02) {}
		ThermalZone(tz03) {}
		ThermalZone(tz04) {}
		ThermalZone(tz05) {}
		ThermalZone(tz06) {}
		ThermalZone(tz07) {}
		ThermalZone(tz08) {}
		ThermalZone(tz09) {}
		ThermalZone(tz0a) {}
		ThermalZone(tz0b) {}


		// i000

		Store(i000, p000)
		Store(i000, d000)
		Store(i000, e000)
		Store(i000, m000)
		Store(i000, mx00)
		Store(i000, r000)
		Store(i000, pw00)
		Store(i000, pr00)
		Store(i000, tz00)

		// s000

		Store(s000, p001)
		Store(s000, d001)
		Store(s000, e001)
		Store(s000, m001)
		Store(s000, mx01)
		Store(s000, r001)
		Store(s000, pw01)
		Store(s000, pr01)
		Store(s000, tz01)

		// b000

		Store(b000, p002)
		Store(b000, d002)
		Store(b000, e002)
		Store(b000, m002)
		Store(b000, mx02)
		Store(b000, r002)
		Store(b000, pw02)
		Store(b000, pr02)
		Store(b000, tz02)

		// p000

		Store(p000, p003)
		Store(p000, d003)
		Store(p000, e003)
		Store(p000, m003)
		Store(p000, mx03)
		Store(p000, r003)
		Store(p000, pw03)
		Store(p000, pr03)
		Store(p000, tz03)

		// d000

		Store(d000, p004)
		Store(d000, d004)
		Store(d000, e004)
		Store(d000, m004)
		Store(d000, mx04)
		Store(d000, r004)
		Store(d000, pw04)
		Store(d000, pr04)
		Store(d000, tz04)

		// e000

		Store(e000, p005)
		Store(e000, d005)
		Store(e000, e005)
		Store(e000, m005)
		Store(e000, mx05)
		Store(e000, r005)
		Store(e000, pw05)
		Store(e000, pr05)
		Store(e000, tz05)

		// m000

		Store(m000, p006)
		Store(m000, d006)
		Store(m000, e006)
		Store(m000, m006)
		Store(m000, mx06)
		Store(m000, r006)
		Store(m000, pw06)
		Store(m000, pr06)
		Store(m000, tz06)

		// mx00

		Store(mx00, p007)
		Store(mx00, d007)
		Store(mx00, e007)
		Store(mx00, m007)
		Store(mx00, mx07)
		Store(mx00, r007)
		Store(mx00, pw07)
		Store(mx00, pr07)
		Store(mx00, tz07)

		// r000

		Store(r000, p008)
		Store(r000, d008)
		Store(r000, e008)
		Store(r000, m008)
		Store(r000, mx08)
		Store(r000, r008)
		Store(r000, pw08)
		Store(r000, pr08)
		Store(r000, tz08)

		// pw00

		Store(pw00, p009)
		Store(pw00, d009)
		Store(pw00, e009)
		Store(pw00, m009)
		Store(pw00, mx09)
		Store(pw00, r009)
		Store(pw00, pw09)
		Store(pw00, pr09)
		Store(pw00, tz09)

		// pr00

		Store(pr00, p00a)
		Store(pr00, d00a)
		Store(pr00, e00a)
		Store(pr00, m00a)
		Store(pr00, mx0a)
		Store(pr00, r00a)
		Store(pr00, pw0a)
		Store(pr00, pr0a)
		Store(pr00, tz0a)

		// tz00

		Store(tz00, p00b)
		Store(tz00, d00b)
		Store(tz00, e00b)
		Store(tz00, m00b)
		Store(tz00, mx0b)
		Store(tz00, r00b)
		Store(tz00, pw0b)
		Store(tz00, pr0b)
		Store(tz00, tz0b)

		Store("mm04 finished", Debug)
	}

	Method(MAIN)
	{
		mm04()
	}
}
