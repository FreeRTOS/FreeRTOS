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
	"ssdt5.aml",   // Output filename
	"SSDT",     // Signature
	0x02,       // DSDT Revision
	"iASLTS",    // OEMID
	"LTBL0005",     // TABLE ID
	0x00000001  // OEM Revision
	) {

	Name(DDBX, 0)
	// Originated from ssdt0.asl: iasl -tc ssdt0.asl
	Name(BUFX, Buffer() {
		0x53,0x53,0x44,0x54,0x34,0x00,0x00,0x00,  /* 00000000    "SSDT4..." */
		0x02,0x98,0x49,0x6E,0x74,0x65,0x6C,0x00,  /* 00000008    "..Intel." */
		0x4D,0x61,0x6E,0x79,0x00,0x00,0x00,0x00,  /* 00000010    "Many...." */
		0x01,0x00,0x00,0x00,0x49,0x4E,0x54,0x4C,  /* 00000018    "....INTL" */
		0x15,0x12,0x06,0x20,0x14,0x0F,0x5C,0x53,  /* 00000020    "... ..\S" */
		0x53,0x53,0x30,0x00,0xA4,0x0D,0x5C,0x53,  /* 00000028    "SS0...\S" */
		0x53,0x53,0x30,0x00,
	})
	OperationRegion (ISTX, SystemMemory, 0, 0x34)
	Field(ISTX, ByteAcc, NoLock, Preserve) {
		RFUX, 0x1a0,
	}
	Store(BUFX, RFUX)
	Load(RFUX, DDBX)
}
