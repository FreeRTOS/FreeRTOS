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
 * Common use Data
 */

Name(id00, 0xe0385bcd)
Name(id01, 0) // Flag of error, used by demo-162
Name(id02, 0) // Flag of presence of demo-162 test

Name(id09, 0)
Name(id0a, 0)
Name(id0b, 0x89abcdef)

Name(sd00, "String")

Name(bd00, Buffer(32) {1,2,3,4})
Name(bd02, Buffer() {0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,
				0x1a,0x1b,0x1c,0x1d,0x1e,0x1f,0x20,0x21,0x22,0x23})

CreateField(bd00, 0, 8, bf30)
CreateField(bd00, 8, 65, bf31)

Name(pd00, Package(1){Buffer() {1,2,3,4}})

Device(dd00) { Name(i900, 0xabcd0017) }
Device(dd01) { Name(i900, 0xabcd0017) }
Device(dd02) { Name(i900, 0xabcd0017) }
Device(dd03) { Name(i900, 0xabcd0017) }

Device(dd04) { Name(i900, 0xabcd0017) }
Device(dd05) { Name(i900, 0xabcd0017) }
Device(dd06) { Name(i900, 0xabcd0017) }
Device(dd07) { Name(i900, 0xabcd0017) }

OperationRegion(rd00, SystemMemory, 0x100, 0x100)
Field(rd00, ByteAcc, NoLock, Preserve) {fd00,8,fd01,65}


/*
 * Global CreateField declarations for bug 161
 */

/*


!!!!!!!!!!!!!! uncomment !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!


Name(id03, 8)
Name(id04, 64)
Name(id05, 80)
Name(id06, 8)
Name(id07, 80)
Name(id08, 8)

Name(bd03, Buffer() {0x10,0x5d,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,
				0x1a,0x1b,0x1c,0x1d,0x1e,0x1f,0x20,0x21,0x22,0x23})

// Caused stack overflow
// CreateField(bd03, 32, id03, bf32)
CreateField(bd03, 32, 8, bf32)

CreateField(bd03, 40, Add(id03, 8), bf33)

// Caused stack overflow
// CreateField(bd03, id04, 8, bf34)
CreateField(bd03, 64, 8, bf34)

CreateField(bd03, Add(id04, 8), 8, bf35)

// Caused stack overflow
// CreateField(bd03, id05, id06, bf36)
CreateField(bd03, 80, 8, bf36)

CreateField(bd03, Add(id07, 8), Add(id08, 8), bf37)

// ==================== Additional:

CreateBitField(bd03, 8, bf40)
CreateByteField(bd03, 1, bf41)
CreateWordField(bd03, 1, bf42)
CreateDWordField(bd03, 1, bf43)
CreateQWordField(bd03, 1, bf44)
CreateField(bd03, 8, 8, bf45)

Name(id21, 1)
Name(id22, 8)

CreateBitField(bd03, id22, bf46)
CreateByteField(bd03, id21, bf47)
CreateWordField(bd03, id21, bf48)
CreateDWordField(bd03, id21, bf49)
CreateQWordField(bd03, id21, bf4a)
CreateField(bd03, 8, id22, bf4b)
CreateField(bd03, id22, 8, bf4c)
CreateField(bd03, id22, id22, bf4d)


*/


// ==================== bug 161.

Mutex(mxd0, 0)
Event(ed00)
OperationRegion(rd01, SystemMemory, 0x100, 0x100)
OperationRegion(rd02, SystemMemory, 0x100, 0x100)
Name(pd01, Package(){0x89abcdef})

Name(dd08, 0x12)
Name(sd01, "123456789")
Name(bd04, Buffer() {1,2,3,4,5,6,7,8,9})

Name(id0c, 0x12)
Name(sd02, "123456789")
Name(bd05, Buffer() {1,2,3,4,5,6,7,8,9})
Name(pd02, Package() {1,2,3,4,5,6,7,8,9})
OperationRegion(rd03, SystemMemory, 0x100, 0x100)
Field(rd03, ByteAcc, NoLock, Preserve) { fd02, 8 }
Device(dd09) {}
Event(ed01)
Method(me53) { return (0x12) }
Mutex(mxd1, 0)
PowerResource(pwd0, 1, 0) {Method(m001){return (0)}}
Processor(prd0, 0, 0xFFFFFFFF, 0) {}
ThermalZone(tzd0) {}
CreateField(bd05, 0, 8, bfd0)

Name(id0d, 0)
Name(id0e, 0)

Method(me69) { return (0x12345678) }
Name(pd03, Package() {me69})

Name(id0f, 0)
Name(id10, 0x1234)

Name(pd04, Package(){0x10})
Name(pd05, Package(){0x20})
Name(pd06, Package(){0x30})
Name(pd07, Package(){0x40})
Name(pd08, Package(){0x50})
Name(pd09, Package(){0x60})


Name(id11, 0xfe7cb391d650a284)
Name(bd06, Buffer() {1,2,3,4,0x59,6,7,8,9})
CreateField(bd06, 40, 8, bfd1)
OperationRegion(rd04, SystemMemory, 0x100, 0x100)
Field(rd04, ByteAcc, NoLock, Preserve) {fd03,8}
Name(pd0a, Package() {id11})
Name(pd0b, Package() {bfd1})
Name(pd0c, Package() {fd03})

Name(sd03, "0123456789a")
Name(bd07, Buffer(8193){})

Name(sd04, "qwer0000")
Name(bd08, Buffer(4) {1,0x77,3,4})
Name(pd0d, Package(3) {5,0x77,7})

Name(id12, 0x77)
Name(pd0e, Package(1) {0x77})

Name(id13, 0)
Name(sd05, "q_er0000")
Name(bd09, Buffer(4) {1,0,3,4})
Name(pd0f, Package(3) {5,0,7})

Name(id14, 0x11)
Name(id15, 0x22)
Name(id16, 0x33)
Name(id17, 0x44)
Name(id18, 0x55)
Name(id19, 0x66)
Name(id1a, 0x77)

Name(id1b, 0xfedcba9876543210)
Name(id1c, 0xfedcba9876543211)

Name(id1d, 0xfedcba9876543210)
Device(dd0b) {Name(s000, "DEV0")}
Event(ed02)

OperationRegion(rd05, SystemMemory, 0x100, 0x100)

Name(bd0a, Buffer(9){0x10,0x11,0x12,0x13})
CreateField(bd0a, 0, 8, bfd2)

Name (rtd0, ResourceTemplate () {
		IRQNoFlags () {1}
		DMA (Compatibility, NotBusMaster, Transfer16) {2}
	})

Name (bd0b, Buffer () {
		0x22, 0x02, 0x00,
		0x2a, 0x04, 0x02,
		0x22, 0x02, 0x00,
		0x2a, 0x04, 0x02,
		0x79, 0xdf,
	})

Device(dd0c){}
Processor(prd1, 0, 0xFFFFFFFF, 0) {}
OperationRegion(rd06, SystemMemory, 0x100, 0x100)
PowerResource(pwd1, 1, 0) {Method(mmmm){return (0)}}
ThermalZone(tzd1) {}
Event(ed03)
Mutex(mxd2, 0)

Event(ed04)
Name(id1e, 0x19283746)
Name(pd10, Package(1){"Package"})

Name (rtd1, ResourceTemplate () {
	QWordSpace (0xc0, ResourceProducer, PosDecode, MinNotFixed, MaxNotFixed, 0x0a,
		0xd8d9dadbdcdddedf, 0xe0e1e2e3e4e5e6e7, 0xe8e9eaebecedeeef,
		0xf0f1f2f3f4f5f6f7, 0xf8f9fafbfcfdfeff)})

Name (bd0c, Buffer () {
	0x8a, 0x2b, 0x00, 0xc0, 0x00, 0x0a,
	0xdf, 0xde, 0xdd, 0xdc, 0xdb, 0xda, 0xd9, 0xd8,
	0xe7, 0xe6, 0xe5, 0xe4, 0xe3, 0xe2, 0xe1, 0xe0,
	0xef, 0xee, 0xed, 0xec, 0xeb, 0xea, 0xe9, 0xe8,
	0xf7, 0xf6, 0xf5, 0xf4, 0xf3, 0xf2, 0xf1, 0xf0,
	0xff, 0xfe, 0xfd, 0xfc, 0xfb, 0xfa, 0xf9, 0xf8, 0x79, 0x00})

Device(dd0d){}
Processor(prd2, 0, 0xFFFFFFFF, 0) {}
OperationRegion(rd07, SystemMemory, 0x100, 0x100)
PowerResource(pwd2, 1, 0) {Method(mmmm){return (0)}}
ThermalZone(tzd2) {}
Event(ed05)
Mutex(mxd3, 0)


Name(id1f, 49)
Name(id20, 7)
OperationRegion(rd08, SystemMemory, 0, Increment(id1f))
Name(bd0d, Buffer(8) {0x80, 0x99, 0xff, 0x83, 0x84, 0x85, 0x86, 0x87})
CreateField(bd0d, 8, Increment(id20), bfd3)

Name(pd11, Package(2) {1})

Name(bd0e, Buffer(4) {1,0x77,3,4})

// Base of Buffer Field
Name(bd0f, Buffer(9){})

// Benchmark buffer
Name(bd10, Buffer(9){})
