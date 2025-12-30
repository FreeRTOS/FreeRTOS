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

// Resource Descriptor macros

// For each Resource Descriptor Macro declaration
// below Error/Warning is expected.

// The same descriptor names, DN00, in the same scope
Method(m400)
{
	Name(RT00,
		ResourceTemplate () {
			IRQ (Edge, ActiveLow, Shared, DN00) {}
			IRQ (Edge, ActiveLow, Shared, DN00) {}
		})
	Name(RT01,
		ResourceTemplate () {
			DMA (Compatibility, NotBusMaster, Transfer8, DN00) {}
			DMA (Compatibility, NotBusMaster, Transfer8, DN00) {}
		})
	Name(RT02,
		ResourceTemplate () {
			IO (Decode16, 0xf0f1, 0xf2f3, 0xf4, 0xf5, DN00)
			IO (Decode16, 0xf0f1, 0xf2f3, 0xf4, 0xf5, DN00)
		})
	Name(RT03,
		ResourceTemplate () {
			Memory24 ( , 0x0000, 0xffff, 0x0001, 0xfffe, DN00)
			Memory24 ( , 0x0000, 0xffff, 0x0001, 0xfffe, DN00)
		})
	Name(RT04,
		ResourceTemplate () {
			IO (Decode16, 0xf0f1, 0xf2f3, 0xf4, 0xf5, DN00)
			IO (Decode16, 0xf0f1, 0xf2f3, 0xf4, 0xf5, DN00)
		})
}

Method(m401)
{
	Name(RT00,
		ResourceTemplate () {
			DMA (Compatibility, NotBusMaster, Transfer8) {8}
		})
	Name(RT01,
		ResourceTemplate () {
			DMA (TypeA, NotBusMaster, Transfer8) {0, 0}
		})
}

Method(m402)
{
	Name(RT00,
		ResourceTemplate () {
			DWordIO ( , , , , ,
				0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff, 0x0f)
		})
	Name(RT01,
		ResourceTemplate () {
			DWordIO ( , , , , ,
				0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff,, "PATHPATHPATH")
		})
}

Method(m403)
{
	Name(RT00,
		ResourceTemplate () {
			DWordMemory ( , , , , , ,
				0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff, 0x0f)
		})
	Name(RT01,
		ResourceTemplate () {
			DWordMemory ( , , , , , ,
				0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff,, "PATHPATHPATH")
		})
}

Method(m404)
{
	Name(RT00,
		ResourceTemplate () {
			DWordSpace (0xc0, , , , , 0x5a,
				0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff, 0x0f)
		})
	Name(RT01,
		ResourceTemplate () {
			DWordSpace (0xc0, , , , , 0x5a,
				0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff,, "PATHPATHPATH")
		})
}

Method(m405)
{
	Name(RT00,
		ResourceTemplate () {
			Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0x0f)
				{0xfcfdfeff}
		})
	Name(RT01,
		ResourceTemplate () {
			Interrupt (ResourceConsumer, Edge, ActiveLow, Shared,, "PATHPATHPATH")
				{0xfcfdfeff}
		})
	Name(RT02,
		ResourceTemplate () {
			Interrupt (ResourceConsumer, Edge, ActiveLow, Shared) {9, 9}
		})
	Name(RT03,
		ResourceTemplate () {
			Interrupt (ResourceConsumer, Edge, ActiveLow, Shared) {
				  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15, 16,
				 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
				 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
				 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64,
				 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80,
				 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96,
				 97, 98, 99,100,101,102,103,104,105,106,107,108,109,110,111,112,
				113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,
				129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,
				145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,
				161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,
				177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,
				193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,
				209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,
				225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,
				241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256}
		})
}

Method(m406)
{
	Name(RT00,
		ResourceTemplate () {
			IRQ (Edge, ActiveLow, Shared) {16}
		})
	Name(RT01,
		ResourceTemplate () {
			IRQ (Level, ActiveLow, Shared) {9, 9}
		})
}

Method(m407)
{
	Name(RT00,
		ResourceTemplate () {
			IRQNoFlags () {16}
		})
	Name(RT01,
		ResourceTemplate () {
			IRQNoFlags () {9, 9}
		})
}

Method(m408)
{
	Name(RT00,
		ResourceTemplate () {
			QWordIO ( , , , , ,
				0xd8d9dadbdcdddedf, 0xe0e1e2e3e4e5e6e7, 0xe8e9eaebecedeeef,
				0xf0f1f2f3f4f5f6f7, 0xf8f9fafbfcfdfeff, 0x0f)
		})
	Name(RT01,
		ResourceTemplate () {
			QWordIO ( , , , , ,
				0xd8d9dadbdcdddedf, 0xe0e1e2e3e4e5e6e7, 0xe8e9eaebecedeeef,
				0xf0f1f2f3f4f5f6f7, 0xf8f9fafbfcfdfeff,, "PATHPATHPATH")
		})
}

Method(m409)
{
	Name(RT00,
		ResourceTemplate () {
			QWordMemory ( , , , , , ,
				0xd8d9dadbdcdddedf, 0xe0e1e2e3e4e5e6e7, 0xe8e9eaebecedeeef,
				0xf0f1f2f3f4f5f6f7, 0xf8f9fafbfcfdfeff, 0x0f)
		})
	Name(RT01,
		ResourceTemplate () {
			QWordMemory ( , , , , , ,
				0xd8d9dadbdcdddedf, 0xe0e1e2e3e4e5e6e7, 0xe8e9eaebecedeeef,
				0xf0f1f2f3f4f5f6f7, 0xf8f9fafbfcfdfeff,, "PATHPATHPATH")
		})
}

Method(m40a)
{
	Name(RT00,
		ResourceTemplate () {
			QWordSpace (0xc0, , , , , 0x5a,
				0xd8d9dadbdcdddedf, 0xe0e1e2e3e4e5e6e7, 0xe8e9eaebecedeeef,
				0xf0f1f2f3f4f5f6f7, 0xf8f9fafbfcfdfeff, 0x0f)
		})
	Name(RT01,
		ResourceTemplate () {
			QWordSpace (0xc0, , , , , 0x5a,
				0xd8d9dadbdcdddedf, 0xe0e1e2e3e4e5e6e7, 0xe8e9eaebecedeeef,
				0xf0f1f2f3f4f5f6f7, 0xf8f9fafbfcfdfeff,, "PATHPATHPATH")
		})
}

Method(m40b)
{
	Name(RT00,
		ResourceTemplate () {
			Register (SystemMemory, 0xf0, 0xf1, 0xf2f3f4f5f6f7f8f9, 5)
		})
}

Method(m40c)
{
	Name(RT00,
		ResourceTemplate () {
			VendorShort () {0x00, 0x81, 0xa2, 0xb3, 0x76, 0xd5, 0xe6, 0xf7}
		})
	Name(RT01,
		ResourceTemplate () {
			VendorShort (VS00) {0x00, 0xa2, 0xb3, 0x76, 0xd5, 0xe6, 0xf7}
		})
}

Method(m40d)
{
	Name(RT00,
		ResourceTemplate () {
			WordBusNumber ( , , , ,
				0xf6f7, 0xf8f9, 0xfafb, 0xfcfd, 0xfeff, 0x0f)
		})
	Name(RT01,
		ResourceTemplate () {
			WordBusNumber ( , , , ,
				0xf6f7, 0xf8f9, 0xfafb, 0xfcfd, 0xfeff,, "PATHPATHPATH")
		})
}

Method(m40e)
{
	Name(RT00,
		ResourceTemplate () {
			WordIO ( , , , , ,
				0xf6f7, 0xf8f9, 0xfafb, 0xfcfd, 0xfeff, 0x0f)
		})
	Name(RT01,
		ResourceTemplate () {
			WordIO ( , , , , ,
				0xf6f7, 0xf8f9, 0xfafb, 0xfcfd, 0xfeff,, "PATHPATHPATH")
		})
}

Method(m40f)
{
	Name(RT00,
		ResourceTemplate () {
			WordSpace (0xc0, , , , , 0x5a,
				0xf6f7, 0xf8f9, 0xfafb, 0xfcfd, 0xfeff, 0x0f)
		})
	Name(RT01,
		ResourceTemplate () {
			WordSpace (0xc0, , , , , 0x5a,
				0xf6f7, 0xf8f9, 0xfafb, 0xfcfd, 0xfeff,, "PATHPATHPATH")
		})
}

// An example to provoke message:
// "nsaccess-0713: *** Warning: NsLookup: Type mismatch on
// M40f (Method), searching for (ResourceDesc)".
// Expect a compiler error because the Descriptorname M40f and
// the Method m40f are defined on the same scope.
Name(M410,
	ResourceTemplate () {
		DMA (Compatibility, NotBusMaster, Transfer8, M40f) {0}
})
