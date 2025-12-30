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
 * Object references
 */


// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!
// ????? don't forget to remove DefinitionBlock from there !!!!!!!!!!!
// ???????????????????????????????

DefinitionBlock(
	"reference.aml",   // Output filename
	"DSDT",     // Signature
	0x02,       // DSDT Revision
	"Intel",    // OEMID
	"Many",     // TABLE ID
	0x00000001  // OEM Revision
	) {


// ///////////////////////////////////////////////////////////////////////////
//
// TABLE 1: all the legal ways to generate references
//          to the immediate images (constants)
//
// ///////////////////////////////////////////////////////////////////////////

Name(b100, Buffer(32) {0x12})
OperationRegion(r100, SystemMemory, 0x100, 0x100)
Field(r100, ByteAcc, NoLock, Preserve) {bnk0, 8, f00a, 8, f00b, 8}

/*
Method(ma00)
{
	// T1:x,I1,+,+,+,I5-I7,,I9-I14,x,I16

	Store(Index(0xabcdef, 0), Local0)
	Store(Index(Field(r100, ByteAcc, NoLock, Preserve) { f000, 8 }, 0), Local0)
	Store(Index(BankField(r100, bnk0, 0, ByteAcc, NoLock, Preserve) {bkf0, 8}, 0), Local0)
	Store(Index(IndexField (f00a, f00b, ByteAcc, NoLock, Preserve) {if00,8,if01,8}, 0), Local0)
	Store(Index(Device(d000) {}, 0), Local0)
	Store(Index(Event(e000), 0), Local0)
	Store(Index(Mutex(mx00, 0), 0), Local0)
	Store(Index(OperationRegion(r000, SystemMemory, 0x100, 0x100), 0), Local0)
	Store(Index(PowerResource(pwr0, 1, 0) {}, 0), Local0)
	Store(Index(Processor(prc0, 0, 0xFFFFFFFF, 0) {}, 0), Local0)
	Store(Index(ThermalZone(tz00) {}, 0), Local0)
	Store(Index(CreateField(b100, 0, 8, bf00), 0), Local0)
	Store(Index(Debug, 0), Local0)
}
*/
/*
Method(ma01)
{
	// T1:x,IR1,+,+,+,IR5-IR7,,IR9-IR14,x,IR16

	Store(Index(0xabcdef, 0, Local1), Local0)
	Store(Index(Field(r100, ByteAcc, NoLock, Preserve) { f000, 8 }, 0, Local1), Local0)
	Store(Index(BankField(r100, bnk0, 0, ByteAcc, NoLock, Preserve) {bkf0, 8}, 0, Local1), Local0)
	Store(Index(IndexField (f00a, f00b, ByteAcc, NoLock, Preserve) {if00,8,if01,8}, 0, Local1), Local0)
	Store(Index(Device(d000) {}, 0, Local1), Local0)
	Store(Index(Event(e000), 0, Local1), Local0)
	Store(Index(Mutex(mx00, 0), 0, Local1), Local0)
	Store(Index(OperationRegion(r000, SystemMemory, 0x100, 0x100), 0, Local1), Local0)

	Store(Index(PowerResource(pwr0, 1, 0) {}, 0, Local1), Local0)
	Store(Index(Processor(prc0, 0, 0xFFFFFFFF, 0) {}, 0, Local1), Local0)
	Store(Index(ThermalZone(tz00) {}, 0, Local1), Local0)
	Store(Index(CreateField(b100, 0, 8, bf00), 0, Local1), Local0)
	Store(Index(Debug, 0, Local1), Local0)
}
*/
/*
// Currently commented, because it breaks further compilation
Method(ma02)
{
	// T1:I8

	Name(b000, Buffer() {1,2,3,4,5,6,7,8,9})
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) {f000,8}
	Field(r000, ByteAcc, NoLock, Preserve) {bnk0,8,f00a,8,f00b,8}
	BankField(r000, bnk0, 0, ByteAcc, NoLock, Preserve) {bkf0,4}
	IndexField (f00a, f00b, ByteAcc, NoLock, Preserve) {if00,1,if01,1}
	Device(d000) {}
	Event(e000)
	Mutex(mx00, 0)
	PowerResource(pwr0, 1, 0) {Method(mmmm){return (0)}}
	Processor(prc0, 0, 0xFFFFFFFF, 0) {}
	ThermalZone(tz00) {}
	CreateField(b000, 0, 8, bf00)

	Store(Index(Method(m000){}, 0), Local0)
	Store(Index(Method(m001){return (0x12345678)}, 0), Local0)
	Store(Index(Method(m002){return ("zxvgswquiy")}, 0), Local0)
	Store(Index(Method(m003){return (Buffer() {0x11})}, 0), Local0)
	Store(Index(Method(m004){return (Package() {0x22})}, 0), Local0)
	Store(Index(Method(m005){return (Package() {"zxvgswquiy"})}, 0), Local0)
	Store(Index(Method(m006){return (Package() {Buffer() {0x11}})}, 0), Local0)
	Store(Index(Method(m007){return (Package() {Package() {0x22}})}, 0), Local0)
	Store(Index(Method(m008){return (f000)}, 0), Local0)
	Store(Index(Method(m009){return (bkf0)}, 0), Local0)
	Store(Index(Method(m00a){return (if00)}, 0), Local0)
	Store(Index(Method(m00b){return (d000)}, 0), Local0)
	Store(Index(Method(m00c){return (e000)}, 0), Local0)
	Store(Index(Method(m00d){return (m001)}, 0), Local0)
	Store(Index(Method(m00e){return (mx00)}, 0), Local0)
	Store(Index(Method(m00f){return (r000)}, 0), Local0)
	Store(Index(Method(m010){return (pwr0)}, 0), Local0)
	Store(Index(Method(m011){return (prc0)}, 0), Local0)
	Store(Index(Method(m012){return (tz00)}, 0), Local0)
	Store(Index(Method(m013){return (bf00)}, 0), Local0)
}
*/
/*
Method(ma03)
{
	// T1:IR8

	Name(b000, Buffer() {1,2,3,4,5,6,7,8,9})
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) {f000,8}
	Field(r000, ByteAcc, NoLock, Preserve) {bnk0,8,f00a,8,f00b,8}
	BankField(r000, bnk0, 0, ByteAcc, NoLock, Preserve) {bkf0,4}
	IndexField (f00a, f00b, ByteAcc, NoLock, Preserve) {if00,1,if01,1}
	Device(d000) {}
	Event(e000)
	Mutex(mx00, 0)
	PowerResource(pwr0, 1, 0) {Method(mmmm){return (0)}}
	Processor(prc0, 0, 0xFFFFFFFF, 0) {}
	ThermalZone(tz00) {}
	CreateField(b000, 0, 8, bf00)

	Store(Index(Method(m000){}, 0, Local1), Local0)
	Store(Index(Method(m001){return (0x12345678)}, 0, Local1), Local0)
	Store(Index(Method(m002){return ("zxvgswquiy")}, 0, Local1), Local0)
	Store(Index(Method(m003){return (Buffer() {0x11})}, 0, Local1), Local0)
	Store(Index(Method(m004){return (Package() {0x22})}, 0, Local1), Local0)
	Store(Index(Method(m005){return (Package() {"zxvgswquiy"})}, 0, Local1), Local0)
	Store(Index(Method(m006){return (Package() {Buffer() {0x11}})}, 0, Local1), Local0)
	Store(Index(Method(m007){return (Package() {Package() {0x22}})}, 0, Local1), Local0)
	Store(Index(Method(m008){return (f000)}, 0, Local1), Local0)
	Store(Index(Method(m009){return (bkf0)}, 0, Local1), Local0)
	Store(Index(Method(m00a){return (if00)}, 0, Local1), Local0)
	Store(Index(Method(m00b){return (d000)}, 0, Local1), Local0)
	Store(Index(Method(m00c){return (e000)}, 0, Local1), Local0)
	Store(Index(Method(m00d){return (m001)}, 0, Local1), Local0)
	Store(Index(Method(m00e){return (mx00)}, 0, Local1), Local0)
	Store(Index(Method(m00f){return (r000)}, 0, Local1), Local0)
	Store(Index(Method(m010){return (pwr0)}, 0, Local1), Local0)
	Store(Index(Method(m011){return (prc0)}, 0, Local1), Local0)
	Store(Index(Method(m012){return (tz00)}, 0, Local1), Local0)
	Store(Index(Method(m013){return (bf00)}, 0, Local1), Local0)
}
*/
/*
Method(ma04)
{
	// T1:x,R1-R7,,R9-R14,x,R16

	Store(RefOf(0xabcdef), Local0)
	Store(RefOf("qwrtyuiop"), Local0)
	Store(RefOf(Buffer() {1,2,3,4,5,6,7,8}), Local0)
	Store(RefOf(Package() {1,2,3,4,5,6,7,8}), Local0)
	Store(RefOf(Field(r100, ByteAcc, NoLock, Preserve) { f000, 8 }), Local0)
	Store(RefOf(BankField(r100, bnk0, 0, ByteAcc, NoLock, Preserve) {bkf0, 8}), Local0)
	Store(RefOf(IndexField (f00a, f00b, ByteAcc, NoLock, Preserve) {if00,8,if01,8}), Local0)
	Store(RefOf(Device(d000) {}), Local0)
	Store(RefOf(Event(e000)), Local0)
	Store(RefOf(Mutex(mx00, 0)), Local0)
	Store(RefOf(OperationRegion(r000, SystemMemory, 0x100, 0x100)), Local0)
	Store(RefOf(PowerResource(pwr0, 1, 0) {}), Local0)
	Store(RefOf(Processor(prc0, 0, 0xFFFFFFFF, 0) {}), Local0)
	Store(RefOf(ThermalZone(tz00) {}), Local0)
	Store(RefOf(CreateField(b100, 0, 8, bf00)), Local0)
	Store(RefOf(Debug), Local0)
}
*/
/*
// Currently commented, because it breaks further compilation
Method(ma05)
{
	// T1:R8

	Name(b000, Buffer() {1,2,3,4,5,6,7,8,9})
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) {f000,8}
	Field(r000, ByteAcc, NoLock, Preserve) {bnk0,8,f00a,8,f00b,8}
	BankField(r000, bnk0, 0, ByteAcc, NoLock, Preserve) {bkf0,4}
	IndexField (f00a, f00b, ByteAcc, NoLock, Preserve) {if00,1,if01,1}
	Device(d000) {}
	Event(e000)
	Mutex(mx00, 0)
	PowerResource(pwr0, 1, 0) {Method(mmmm){return (0)}}
	Processor(prc0, 0, 0xFFFFFFFF, 0) {}
	ThermalZone(tz00) {}
	CreateField(b000, 0, 8, bf00)

	Store(RefOf(Method(m000){}), Local0)
	Store(RefOf(Method(m001){return (0x12345678)}), Local0)
	Store(RefOf(Method(m002){return ("zxvgswquiy")}), Local0)
	Store(RefOf(Method(m003){return (Buffer() {0x11})}), Local0)
	Store(RefOf(Method(m004){return (Package() {0x22})}), Local0)
	Store(RefOf(Method(m005){return (Package() {"zxvgswquiy"})}), Local0)
	Store(RefOf(Method(m006){return (Package() {Buffer() {0x11}})}), Local0)
	Store(RefOf(Method(m007){return (Package() {Package() {0x22}})}), Local0)
	Store(RefOf(Method(m008){return (f000)}), Local0)
	Store(RefOf(Method(m009){return (bkf0)}), Local0)
	Store(RefOf(Method(m00a){return (if00)}), Local0)
	Store(RefOf(Method(m00b){return (d000)}), Local0)
	Store(RefOf(Method(m00c){return (e000)}), Local0)
	Store(RefOf(Method(m00d){return (m001)}), Local0)
	Store(RefOf(Method(m00e){return (mx00)}), Local0)
	Store(RefOf(Method(m00f){return (r000)}), Local0)
	Store(RefOf(Method(m010){return (pwr0)}), Local0)
	Store(RefOf(Method(m011){return (prc0)}), Local0)
	Store(RefOf(Method(m012){return (tz00)}), Local0)
	Store(RefOf(Method(m013){return (bf00)}), Local0)
}
*/
/*
Method(ma06)
{
	// T1:x,C1-C7,,C9-C14,x,C16

	Store(CondRefOf(0xabcdef), Local0)
	Store(CondRefOf("qwrtyuiop"), Local0)
	Store(CondRefOf(Buffer() {1,2,3,4,5,6,7,8}), Local0)
	Store(CondRefOf(Package() {1,2,3,4,5,6,7,8}), Local0)
	Store(CondRefOf(Field(r100, ByteAcc, NoLock, Preserve) { f000, 8 }), Local0)
	Store(CondRefOf(BankField(r100, bnk0, 0, ByteAcc, NoLock, Preserve) {bkf0, 8}), Local0)
	Store(CondRefOf(IndexField (f00a, f00b, ByteAcc, NoLock, Preserve) {if00,8,if01,8}), Local0)
	Store(CondRefOf(Device(d000) {}), Local0)
	Store(CondRefOf(Event(e000)), Local0)
	Store(CondRefOf(Mutex(mx00, 0)), Local0)
	Store(CondRefOf(OperationRegion(r000, SystemMemory, 0x100, 0x100)), Local0)
	Store(CondRefOf(PowerResource(pwr0, 1, 0) {}), Local0)
	Store(CondRefOf(Processor(prc0, 0, 0xFFFFFFFF, 0) {}), Local0)
	Store(CondRefOf(ThermalZone(tz00) {}), Local0)
	Store(CondRefOf(CreateField(b100, 0, 8, bf00)), Local0)
	Store(CondRefOf(Debug), Local0)
}
*/
/*
Method(ma07)
{
	// T1:x,CR1-CR7,,CR9-CR14,x,CR16

	Store(CondRefOf(0xabcdef, Local1), Local0)
	Store(CondRefOf("qwrtyuiop", Local1), Local0)
	Store(CondRefOf(Buffer() {1,2,3,4,5,6,7,8}, Local1), Local0)
	Store(CondRefOf(Package() {1,2,3,4,5,6,7,8}, Local1), Local0)
	Store(CondRefOf(Field(r100, ByteAcc, NoLock, Preserve) { f000, 8 }, Local1), Local0)
	Store(CondRefOf(BankField(r100, bnk0, 0, ByteAcc, NoLock, Preserve) {bkf0, 8}, Local1), Local0)
	Store(CondRefOf(IndexField (f00a, f00b, ByteAcc, NoLock, Preserve) {if00,8,if01,8}, Local1), Local0)
	Store(CondRefOf(Device(d000) {}, Local1), Local0)
	Store(CondRefOf(Event(e000), Local1), Local0)
	Store(CondRefOf(Mutex(mx00, 0), Local1), Local0)
	Store(CondRefOf(OperationRegion(r000, SystemMemory, 0x100, 0x100), Local1), Local0)
	Store(CondRefOf(PowerResource(pwr0, 1, 0) {}, Local1), Local0)
	Store(CondRefOf(Processor(prc0, 0, 0xFFFFFFFF, 0) {}, Local1), Local0)
	Store(CondRefOf(ThermalZone(tz00) {}, Local1), Local0)
	Store(CondRefOf(CreateField(b100, 0, 8, bf00), Local1), Local0)
	Store(CondRefOf(Debug, Local1), Local0)
}
*/
/*
// Currently commented, because it breaks further compilation
Method(ma08)
{
	// T1:C8

	Name(b000, Buffer() {1,2,3,4,5,6,7,8,9})
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) {f000,8}
	Field(r000, ByteAcc, NoLock, Preserve) {bnk0,8,f00a,8,f00b,8}
	BankField(r000, bnk0, 0, ByteAcc, NoLock, Preserve) {bkf0,4}
	IndexField (f00a, f00b, ByteAcc, NoLock, Preserve) {if00,1,if01,1}
	Device(d000) {}
	Event(e000)
	Mutex(mx00, 0)
	PowerResource(pwr0, 1, 0) {Method(mmmm){return (0)}}
	Processor(prc0, 0, 0xFFFFFFFF, 0) {}
	ThermalZone(tz00) {}
	CreateField(b000, 0, 8, bf00)

	Store(CondRefOf(Method(m000){}), Local0)
	Store(CondRefOf(Method(m001){return (0x12345678)}), Local0)
	Store(CondRefOf(Method(m002){return ("zxvgswquiy")}), Local0)
	Store(CondRefOf(Method(m003){return (Buffer() {0x11})}), Local0)
	Store(CondRefOf(Method(m004){return (Package() {0x22})}), Local0)
	Store(CondRefOf(Method(m005){return (Package() {"zxvgswquiy"})}), Local0)
	Store(CondRefOf(Method(m006){return (Package() {Buffer() {0x11}})}), Local0)
	Store(CondRefOf(Method(m007){return (Package() {Package() {0x22}})}), Local0)
	Store(CondRefOf(Method(m008){return (f000)}), Local0)
	Store(CondRefOf(Method(m009){return (bkf0)}), Local0)
	Store(CondRefOf(Method(m00a){return (if00)}), Local0)
	Store(CondRefOf(Method(m00b){return (d000)}), Local0)
	Store(CondRefOf(Method(m00c){return (e000)}), Local0)
	Store(CondRefOf(Method(m00d){return (m001)}), Local0)
	Store(CondRefOf(Method(m00e){return (mx00)}), Local0)
	Store(CondRefOf(Method(m00f){return (r000)}), Local0)
	Store(CondRefOf(Method(m010){return (pwr0)}), Local0)
	Store(CondRefOf(Method(m011){return (prc0)}), Local0)
	Store(CondRefOf(Method(m012){return (tz00)}), Local0)
	Store(CondRefOf(Method(m013){return (bf00)}), Local0)
}
*/
/*
Method(ma09)
{
	// T1:CR8

	Name(b000, Buffer() {1,2,3,4,5,6,7,8,9})
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) {f000,8}
	Field(r000, ByteAcc, NoLock, Preserve) {bnk0,8,f00a,8,f00b,8}
	BankField(r000, bnk0, 0, ByteAcc, NoLock, Preserve) {bkf0,4}
	IndexField (f00a, f00b, ByteAcc, NoLock, Preserve) {if00,1,if01,1}
	Device(d000) {}
	Event(e000)
	Mutex(mx00, 0)
	PowerResource(pwr0, 1, 0) {Method(mmmm){return (0)}}
	Processor(prc0, 0, 0xFFFFFFFF, 0) {}
	ThermalZone(tz00) {}
	CreateField(b000, 0, 8, bf00)

	Store(CondRefOf(Method(m000){}, Local1), Local0)
	Store(CondRefOf(Method(m001){return (0x12345678)}, Local1), Local0)
	Store(CondRefOf(Method(m002){return ("zxvgswquiy")}, Local1), Local0)
	Store(CondRefOf(Method(m003){return (Buffer() {0x11})}, Local1), Local0)
	Store(CondRefOf(Method(m004){return (Package() {0x22})}, Local1), Local0)
	Store(CondRefOf(Method(m005){return (Package() {"zxvgswquiy"})}, Local1), Local0)
	Store(CondRefOf(Method(m006){return (Package() {Buffer() {0x11}})}, Local1), Local0)
	Store(CondRefOf(Method(m007){return (Package() {Package() {0x22}})}, Local1), Local0)
	Store(CondRefOf(Method(m008){return (f000)}, Local1), Local0)
	Store(CondRefOf(Method(m009){return (bkf0)}, Local1), Local0)
	Store(CondRefOf(Method(m00a){return (if00)}, Local1), Local0)
	Store(CondRefOf(Method(m00b){return (d000)}, Local1), Local0)
	Store(CondRefOf(Method(m00c){return (e000)}, Local1), Local0)
	Store(CondRefOf(Method(m00d){return (m001)}, Local1), Local0)
	Store(CondRefOf(Method(m00e){return (mx00)}, Local1), Local0)
	Store(CondRefOf(Method(m00f){return (r000)}, Local1), Local0)
	Store(CondRefOf(Method(m010){return (pwr0)}, Local1), Local0)
	Store(CondRefOf(Method(m011){return (prc0)}, Local1), Local0)
	Store(CondRefOf(Method(m012){return (tz00)}, Local1), Local0)
	Store(CondRefOf(Method(m013){return (bf00)}, Local1), Local0)
}
*/

// ///////////////////////////////////////////////////////////////////////////
//
// TABLE 2: all the legal ways to generate references to the named objects
//
// ///////////////////////////////////////////////////////////////////////////
/*
Method(ma0a)
{
	Name(i000, 0x12)
	Name(s000, "123456789")
	Name(b000, Buffer() {1,2,3,4,5,6,7,8,9})
	Name(p000, Package() {1,2,3,4,5,6,7,8,9})
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) {f000,8}
	Field(r000, ByteAcc, NoLock, Preserve) {bnk0,8,f00a,8,f00b,8}
	BankField(r000, bnk0, 0, ByteAcc, NoLock, Preserve) {bkf0,4}
	IndexField (f00a, f00b, ByteAcc, NoLock, Preserve) {if00,1,if01,1}
	Device(d000) {}
	Event(e000)
	Method(m000) { return ("zxvgswquiy") }
	Method(m001) { return (0x12345678) }
	Mutex(mx00, 0)
	PowerResource(pwr0, 1, 0) {Method(mmmm){return (0)}}
	Processor(prc0, 0, 0xFFFFFFFF, 0) {}
	ThermalZone(tz00) {}
	CreateField(b000, 0, 8, bf00)

	// T2:x,I1,+,+,+,I5-I7,,I9-I14

	Store(Index(i000, 0), Local0)
	Store(Index(f000, 0), Local0)
	Store(Index(bkf0, 0), Local0)
	Store(Index(if00, 0), Local0)
	Store(Index(bf00, 0), Local0)

	Store(Index(d000, 0), Local0)
	Store(Index(e000, 0), Local0)
	Store(Index(mx00, 0), Local0)
	Store(Index(r000, 0), Local0)
	Store(Index(pwr0, 0), Local0)
	Store(Index(prc0, 0), Local0)
	Store(Index(tz00, 0), Local0)

	// T2:x,IR1,+,+,+,IR5-IR7,,IR9-IR14

	Store(Index(i000, 0, Local1), Local0)
	Store(Index(d000, 0, Local1), Local0)
	Store(Index(e000, 0, Local1), Local0)
	Store(Index(mx00, 0, Local1), Local0)
	Store(Index(r000, 0, Local1), Local0)
	Store(Index(pwr0, 0, Local1), Local0)
	Store(Index(prc0, 0, Local1), Local0)
	Store(Index(tz00, 0, Local1), Local0)
}
*/

/*
Method(ma0b)
{
	Name(i000, 0xabcdef)
	Name(s000, "123456789")
	Name(s001, "qwrtyuiop")
	Name(b000, Buffer() {1,2,3,4,5,6,7,8,9})
	Name(p000, Package() {1,2,3,4,5,6,7,8,9})
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) {f000,8}
	Field(r000, ByteAcc, NoLock, Preserve) {bnk0,8,f00a,8,f00b,8}
	BankField(r000, bnk0, 0, ByteAcc, NoLock, Preserve) {bkf0,4}
	IndexField (f00a, f00b, ByteAcc, NoLock, Preserve) {if00,1,if01,1}
	Device(d000) {}
	Event(e000)
	Mutex(mx00, 0)
	PowerResource(pwr0, 1, 0) {Method(mmmm){return (0)}}
	Processor(prc0, 0, 0xFFFFFFFF, 0) {}
	ThermalZone(tz00) {}
	CreateField(b000, 0, 8, bf00)
	Method(m000) {}
	Method(m001) { return (0x12345678) }
	Method(m002) { return ("zxvgswquiy") }
	Method(m003) { return (Buffer() {0x11}) }
	Method(m004) { return (Package() {0x22}) }
	Method(m005) { return (Package() {"zxvgswquiy"}) }
	Method(m006) { return (Package() {Buffer() {0x11}}) }
	Method(m007) { return (Package() {Package() {0x22}}) }
	Method(m008) { return (f000) }
	Method(m009) { return (bkf0) }
	Method(m00a) { return (if00) }
	Method(m00b) { return (d000) }
	Method(m00c) { return (e000) }
	Method(m00d) { return (m001) }
	Method(m00e) { return (mx00) }
	Method(m00f) { return (r000) }
	Method(m010) { return (pwr0) }
	Method(m011) { return (prc0) }
	Method(m012) { return (tz00) }
	Method(m013) { return (bf00) }

	// T2:I8

	Store(Index(m000, 0), Local0)
	Store(Index(m001, 0), Local0)
	Store(Index(m002, 0), Local0)
	Store(Index(m003, 0), Local0)
	Store(Index(m004, 0), Local0)
	Store(Index(m005, 0), Local0)
	Store(Index(m006, 0), Local0)
	Store(Index(m007, 0), Local0)
	Store(Index(m008, 0), Local0)
	Store(Index(m009, 0), Local0)
	Store(Index(m00a, 0), Local0)
	Store(Index(m00b, 0), Local0)
	Store(Index(m00c, 0), Local0)
	Store(Index(m00d, 0), Local0)
	Store(Index(m00e, 0), Local0)
	Store(Index(m00f, 0), Local0)
	Store(Index(m010, 0), Local0)
	Store(Index(m011, 0), Local0)
	Store(Index(m012, 0), Local0)
	Store(Index(m013, 0), Local0)

	// T2:IR8

	Store(Index(m000, 0, Local1), Local0)
	Store(Index(m001, 0, Local1), Local0)
	Store(Index(m002, 0, Local1), Local0)
	Store(Index(m003, 0, Local1), Local0)
	Store(Index(m004, 0, Local1), Local0)
	Store(Index(m005, 0, Local1), Local0)
	Store(Index(m006, 0, Local1), Local0)
	Store(Index(m007, 0, Local1), Local0)
	Store(Index(m008, 0, Local1), Local0)
	Store(Index(m009, 0, Local1), Local0)
	Store(Index(m00a, 0, Local1), Local0)
	Store(Index(m00b, 0, Local1), Local0)
	Store(Index(m00c, 0, Local1), Local0)
	Store(Index(m00d, 0, Local1), Local0)
	Store(Index(m00e, 0, Local1), Local0)
	Store(Index(m00f, 0, Local1), Local0)
	Store(Index(m010, 0, Local1), Local0)
	Store(Index(m011, 0, Local1), Local0)
	Store(Index(m012, 0, Local1), Local0)
	Store(Index(m013, 0, Local1), Local0)
}
*/
/*
Method(ma0c)
{
	// T3:5-14,16 for all (I,IR,R,C,CR)

	Name(bbbb, Buffer() {1,2,3,4,5,6,7,8,9})
	OperationRegion(rrrr, SystemMemory, 0x100, 0x100)
	Field(rrrr, ByteAcc, NoLock, Preserve) {bnk0,8,f00a,8,f00b,8}

	// These should be checked for RefOf and CondRefOf

	Name(u000, Package(1) {})
	Name(i000, Package() {0xabcdef})
	Name(s000, Package() {"123456789"})
	Name(s001, Package() {"qwrtyuiop"})
	Name(b000, Package() {Buffer() {1,2,3,4,5,6,7,8,9}})
	Name(p000, Package() {Package() {1,2,3,4,5,6,7,8,9}})

	// The entries below show that there is no necessity to
	// check the lines 5-14,16 for all the I,IR,R,C,CR columns.

	Name(ffuu, Package() {Field(rrrr, ByteAcc, NoLock, Preserve) {f000,8}})
	Name(bbnk, Package() {BankField(rrrr, bnk0, 0, ByteAcc, NoLock, Preserve) {bkf0,4}})
	Name(iiff, Package() {IndexField (f00a, f00b, ByteAcc, NoLock, Preserve) {if00,1,if01,1}})
	Name(dddd, Package() {Device(d000) {}})
	Name(eeee, Package() {Event(e000)})
	Name(mmtt, Package() {Method(m001) { return (0x12345678) }})
	Name(mmxx, Package() {Mutex(mx00, 0)})
	Name(r000, Package() {OperationRegion(r000, SystemMemory, 0x100, 0x100)})
	Name(ppww, Package() {PowerResource(pwr0, 1, 0) {Method(mmmm){return (0)}}})
	Name(pprr, Package() {Processor(prc0, 0, 0xFFFFFFFF, 0) {}})
	Name(ttzz, Package() {ThermalZone(tz00) {}})
	Name(bbff, Package() {CreateField(bbbb, 0, 8, bf00)})
	Name(ddbb, Package() {Debug})
}
*/
/*
Method(ma0d)
{
	// T3:R0-R4

	RefOf(Package(1) {})
	RefOf(Package() {0xabcdef})
	RefOf(Package() {"123456789"})
	RefOf(Package() {"qwrtyuiop"})
	RefOf(Package() {Buffer() {1,2,3,4,5,6,7,8,9}})
	RefOf(Package() {Package() {1,2,3,4,5,6,7,8,9}})
}
*/
/*
Method(ma0e)
{
	// T3:C0-C4

	CondRefOf(Package(1) {})
	CondRefOf(Package() {0xabcdef})
	CondRefOf(Package() {"123456789"})
	CondRefOf(Package() {"qwrtyuiop"})
	CondRefOf(Package() {Buffer() {1,2,3,4,5,6,7,8,9}})
	CondRefOf(Package() {Package() {1,2,3,4,5,6,7,8,9}})
}
*/

/*
Method(ma0f)
{
	// T3:CR0-CR4

	CondRefOf(Package(1) {}, Local0)
	CondRefOf(Package() {0xabcdef}, Local0)
	CondRefOf(Package() {"123456789"}, Local0)
	CondRefOf(Package() {"qwrtyuiop"}, Local0)
	CondRefOf(Package() {Buffer() {1,2,3,4,5,6,7,8,9}}, Local0)
	CondRefOf(Package() {Package() {1,2,3,4,5,6,7,8,9}}, Local0)
}
*/
