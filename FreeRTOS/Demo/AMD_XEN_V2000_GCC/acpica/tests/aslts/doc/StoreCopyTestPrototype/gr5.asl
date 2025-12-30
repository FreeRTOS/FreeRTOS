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
	"gr5.aml",   // Output filename
	"DSDT",     // Signature
	0x02,       // DSDT Revision
	"Intel",    // OEMID
	"Many",     // TABLE ID
	0x00000001  // OEM Revision
	) {

	Method(mm05, 1)
	{
		Store("Store to NamedX with the improper conversion", Debug)

		Store("mm05 started", Debug)

		Name(i000, 0x12345678)
		Name(s000, "12345678")
		Name(b000, Buffer() {1,2,3,4,5})
		Name(p000, Package() {0})
		Device(d000) { Name(i900, 0xabcd0017) }
		Event(e000)
		Method(m000) { return (0) }
		Mutex(mx00, 0)
		OperationRegion(r000, SystemMemory, 0x100, 0x100)
		PowerResource(pw00, 1, 0) {}
		Processor(pr00, 0, 0xFFFFFFFF, 0) {}
		ThermalZone(tz00) {}

		if (LEqual(Arg0, 0)) {
			Store(p000, i000)
		} elseif (LEqual(Arg0, 1)) {
			Store(p000, s000)
		} elseif (LEqual(Arg0, 2)) {
			Store(p000, b000)
		} elseif (LEqual(Arg0, 3)) {
			Store(d000, i000)
		} elseif (LEqual(Arg0, 4)) {
			Store(e000, i000)
		} elseif (LEqual(Arg0, 5)) {
			Store(m000, i000)
		} elseif (LEqual(Arg0, 6)) {
			Store(mx00, i000)
		} elseif (LEqual(Arg0, 7)) {
			Store(r000, i000)
		} elseif (LEqual(Arg0, 8)) {
			Store(pw00, i000)
		} elseif (LEqual(Arg0, 9)) {
			Store(pr00, i000)
		} elseif (LEqual(Arg0, 10)) {
			Store(tz00, i000)
		}

		Store("mm05 finished", Debug)
	}

	Method(MAIN)
	{
		mm05(0)
	}
}
