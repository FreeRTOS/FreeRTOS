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
 * The Load operator tests auxiliary SSDT,
 * specifies the Objects of different types
 */

DefinitionBlock(
	"ssdt3.aml",   // Output filename
	"SSDT",     // Signature
	0x02,       // DSDT Revision
	"Intel",    // OEMID
	"Many",     // TABLE ID
	0x00000001  // OEM Revision
	) {

	Device (AUXD) {

		// Integer
		Name(INT0, 0xfedcba9876543210)

		// String
		Name(STR0, "source string0")

		// Buffer
		Name(BUF0, Buffer(9){9,8,7,6,5,4,3,2,1})

		// Package
		Name(PAC0, Package(3) {
			0xfedcba987654321f,
			"test package0",
			Buffer(9){19,18,17,16,15,14,13,12,11},
		})

		// Operation Region
		OperationRegion(OPR0, SystemMemory, 0x7654321, 0x98)

		// Field Unit
		Field(OPR0, ByteAcc, NoLock, Preserve) {
			FLU0, 32,
		}

		// Device
		Device(DEV0) {Name(s000, "DEV0")}

		// Event
		Event(EVE0)

		// Method
		Method(MMM0) {Return (0)}

		// Mutex
		Mutex(MTX0, 0)

		// Power Resource
		PowerResource(PWR0, 0, 0) {Name(s000, "PWR0")}

		// Processor
		Processor(CPU0, 0x0, 0xFFFFFFFF, 0x0) {Name(s000, "CPU0")}

		// Thermal Zone
		ThermalZone(TZN0) {Name(s000, "TZN0")}

		// Buffer Field
		Createfield(BUF0, 0, 69, BFL0)
	}
}
