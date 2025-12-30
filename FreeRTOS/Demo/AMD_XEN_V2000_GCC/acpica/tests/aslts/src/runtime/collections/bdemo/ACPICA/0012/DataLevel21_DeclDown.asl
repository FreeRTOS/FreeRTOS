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
 * 2-level model: \\m12e.<Method>
 *
 * Data for DerefOf(<String>) are 1 levels up.
 *
 * DataLevel<number_of_levels_in_model><data_are_N_levels_up>.asl
 */

Method(m12e,, Serialized)
{

/*
 * 0 - Check different ways to pass String
 */
Method(mdac)
{
	Store("b000", Local0)
	CopyObject("b000", i000)
	Store(s000, Local7)

	// Checkings

	CH03("", 0, 0x000, __LINE__, 0)

	Store(DerefOf("b000"), Local1)
	mf88(Local1, c00b, bb00, 0x001, 0x002, 1)

	Store(DerefOf(Local0), Local1)
	mf88(Local1, c00b, bb00, 0x003, 0x004, 1)

	Store(DerefOf(Local7), Local1)
	mf88(Local1, c00b, bb00, 0x005, 0x006, 1)

	Store(DerefOf(s000), Local1)
	Store(DerefOf(s000), Local1)
	Store(DerefOf(s000), Local1)
	Store(DerefOf(s000), Local1)
	Store(DerefOf(s000), Local1)
	Store(DerefOf(s000), Local1)
	Store(DerefOf(s000), Local1)
	Store(DerefOf(s000), Local1)
	Store(DerefOf(s000), Local1)
	mf88(Local1, c00b, bb00, 0x007, 0x008, 1)

	Store(DerefOf(mm00()), Local1)
	mf88(Local1, c00b, bb00, 0x009, 0x00a, 1)

	Store(DerefOf(mm01(ss00)), Local1)
	mf88(Local1, c00b, bb00, 0x00b, 0x00c, 1)

	Store(DerefOf(ToString("b000")), Local1)
	mf88(Local1, c00b, bb00, 0x00d, 0x00e, 1)

	Store(DerefOf(Store("b000", Local6)), Local1)
	mf88(Local1, c00b, bb00, 0x00f, 0x010, 1)

	Store(DerefOf(i000), Local1)
	mf88(Local1, c00b, bb00, 0x011, 0x012, 1)

	Store(mm02("^b000"), Local1)
	mf88(Local1, c00b, bb00, 0x013, 0x014, 1)

	CH03("", 0, 0x015, __LINE__, 0)
}

/*
 * 1 - Check different ways to specify elements of NameSpace
 */
Method(mf89)
{
	// Checkings

	Store(DerefOf("b001"), Local1)
	mf88(Local1, c00b, bb01, 0x016, 0x017, 1)

	Store(DerefOf("^b001"), Local1)
	mf88(Local1, c00b, bb01, 0x018, 0x019, 1)

	Store(DerefOf("^pr01.i000"), Local1)
	mf88(Local1, c009, 0xaabc0000, 0x01a, 0x01b, 1)

	Store(DerefOf("\\m12e.pr01.i000"), Local1)
	if (FLG9) {
		mf88(Local1, c009, 0xaabc0000, 0x01c, 0x01d, 1)
	} else {
		CH04("", 0, 0xff, 0, __LINE__, 0, 0) // AE_NOT_FOUND
	}

	Store(DerefOf("^i010"), Local1)
	mf88(Local1, c009, ii00, 0x01f, 0x020, 1)

	Store(DerefOf("^i987"), Local1)
	mf88(Local1, c009, ii01, 0x021, 0x022, 1)

	CH03("", 0, 0x023, __LINE__, 0)
}

/*
 * 2 - Check access to calculated type objects - DerefOf(<String>)
 */
Method(mf8a)
{
	CH03("", 0, 0x01f, __LINE__, 0)

	// Checkings

	Store(DerefOf("b002"), Local1)
	mf88(Local1, c00b, bb02, 0x020, 0x021, 1)

	Store(DerefOf("s002"), Local1)
	mf88(Local1, c00a, ss02, 0x022, 0x023, 1)

	Store(DerefOf("i002"), Local1)
	mf88(Local1, c009, ii02, 0x024, 0x025, 1)

	Store(DerefOf("p002"), Local1)
	mf88(Local1, c00c, 0, 0x026, 0x027, 0)

	CH03("", 0, 0x028, __LINE__, 0)
}

/*
 * 3 - Check access to special type objects - DerefOf(<String>)
 */
Method(mf8b)
{
	// Checkings

	CH03("", 0, 0x029, __LINE__, 0)
	CopyObject(DerefOf("e003"), Local1)
	mf88(Local1, c00f, 0, 0x02a, 0x02b, 0)

	CH03("", 0, 0x02c, __LINE__, 0)
	CopyObject(DerefOf("mx03"), Local1)
	mf88(Local1, c011, 0, 0x02d, 0x02e, 0)

	CH03("", 0, 0x02f, __LINE__, 0)
	CopyObject(DerefOf("d003"), Local1)
	mf88(Local1, c00e, 0, 0x030, 0x031, 0)

	CH03("", 0, 0x032, __LINE__, 0)
	CopyObject(DerefOf("tz03"), Local1)
	mf88(Local1, c015, 0, 0x033, 0x034, 0)

	CH03("", 0, 0x035, __LINE__, 0)
	CopyObject(DerefOf("pr03"), Local1)
	mf88(Local1, c014, 0, 0x036, 0x037, 0)

	if (y510) {
		CH03("", 0, 0x038, __LINE__, 0)
		CopyObject(DerefOf("r003"), Local1)
		mf88(Local1, c012, 0, 0x039, 0x03a, 0)
	}

	CH03("", 0, 0x03b, __LINE__, 0)
	CopyObject(DerefOf("pw03"), Local1)
	mf88(Local1, c013, 0, 0x03c, 0x03d, 0)
}

/*
 * 4 - Check DerefOf(<Not-String>) - calculated type objects
 */
Method(mf8c)
{
	// Checkings

	CH03("", 0, 0x03e, __LINE__, 0)
	Store(DerefOf(b004), Local1)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x040, __LINE__, 0)
	Store(DerefOf(i004), Local1)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x042, __LINE__, 0)
	Store(DerefOf(p004), Local1)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)
}

/*
 * 5 - Check DerefOf(<String>) - but String doesn't refer NameSpace object
 */
Method(mf8d)
{
	CH03("", 0, 0x044, __LINE__, 0)
	Store(DerefOf("0123"), Local1)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x046, __LINE__, 0)
	Store(DerefOf("zxcvbnm,./;'\][0123"), Local1)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x048, __LINE__, 0)
	Store(DerefOf("b0qv"), Local1)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)
}

/*
 * 6 - Check different ways to pass String (mdac
 * but without Store). Check - no exceptions.
 */
Method(mf8e)
{
	Store("b006", Local0)
	CopyObject("b006", i006)
	Store(s006, Local7)

	// Checkings

	CH03("", 0, 0x04a, __LINE__, 0)

	Store(DerefOf("b006"), Local2)

	Store(DerefOf(Local0), Local2)

	Store(DerefOf(Local7), Local2)

	Store(DerefOf(s006), Local2)
	Store(DerefOf(s006), Local2)
	Store(DerefOf(s006), Local2)
	Store(DerefOf(s006), Local2)
	Store(DerefOf(s006), Local2)
	Store(DerefOf(s006), Local2)
	Store(DerefOf(s006), Local2)
	Store(DerefOf(s006), Local2)
	Store(DerefOf(s006), Local2)

	Store(DerefOf(mm60()), Local2)

	Store(DerefOf(mm61(ss06)), Local2)

	Store(DerefOf(ToString("b006")), Local2)

	Store(DerefOf(Store("b006", Local6)), Local2)

	Store(DerefOf(i006), Local2)

	CH03("", 0, 0x04b, __LINE__, 0)
}

/*
 * 7 - Check access to special type objects - DerefOf(<String>)
 */
Method(mf8f)
{
	// Checkings

	CH03("", 0, 0x04c, __LINE__, 0)
	Store(DerefOf("e007"), Local2)
	if(LNot(SLCK)){
		CH04("", 0, 47, 0, __LINE__, 0, 0)
	}

	CH03("", 0, 0x04e, __LINE__, 0)
	Store(DerefOf("mx07"), Local2)
	if(LNot(SLCK)){
		CH04("", 0, 47, 0, __LINE__, 0, 0)
	}

	CH03("", 0, 0x050, __LINE__, 0)
	Store(DerefOf("d007"), Local2)
	if(LNot(SLCK)){
		CH04("", 0, 47, 0, __LINE__, 0, 0)
	}

	CH03("", 0, 0x052, __LINE__, 0)
	Store(DerefOf("tz07"), Local2)
	if(LNot(SLCK)){
		CH04("", 0, 47, 0, __LINE__, 0, 0)
	}

	CH03("", 0, 0x054, __LINE__, 0)
	Store(DerefOf("pr07"), Local2)
	if(LNot(SLCK)){
		CH04("", 0, 47, 0, __LINE__, 0, 0)
	}

	CH03("", 0, 0x056, __LINE__, 0)
	Store(DerefOf("r007"), Local2)
	if(LNot(SLCK)){
		CH04("", 0, 47, 0, __LINE__, 0, 0)
	}

	CH03("", 0, 0x058, __LINE__, 0)
	Store(DerefOf("pw07"), Local2)
	if(LNot(SLCK)){
		CH04("", 0, 47, 0, __LINE__, 0, 0)
	}
}

/*
 * 8 - Check DerefOf(<Not-String>) - calculated type objects
 */
Method(mf90)
{
	// Checkings

	CH03("", 0, 0x05a, __LINE__, 0)
	Store(DerefOf(b008), Local2)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x05c, __LINE__, 0)
	Store(DerefOf(i008), Local2)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x05e, __LINE__, 0)
	Store(DerefOf(p008), Local2)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)
}

/*
 * 9 - Check DerefOf(<String>) - but String doesn't refer NameSpace object
 */
Method(mf91)
{
	CH03("", 0, 0x060, __LINE__, 0)
	Store(DerefOf("0123"), Local2)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x062, __LINE__, 0)
	Store(DerefOf("zxcvbnm,./;'\][0123"), Local2)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x064, __LINE__, 0)
	Store(DerefOf("mf_d"), Local2)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x066, __LINE__, 0)
	Store(DerefOf("b009"), Local2)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)
}

/*
 * a - Check access to special type objects - DerefOf(<String>)
 */
Method(mfa0)
{
	CH03("", 0, 0x068, __LINE__, 0)

	Store(DerefOf("bfa0"), Local1)
	mf88(Local1, c009, 0xb1, 0x069, 0x06a, 1)

	Store(DerefOf("f0a0"), Local1)
	mf88(Local1, c009, 0, 0x06b, 0x06c, 0)

	Store(DerefOf("f0a1"), Local1)
	mf88(Local1, c009, 0, 0x06d, 0x06e, 0)

	Store(DerefOf("f0a2"), Local1)
	mf88(Local1, c009, 0, 0x06f, 0x070, 0)

	Store(DerefOf("f0a3"), Local1)
	mf88(Local1, c009, 0, 0x071, 0x072, 0)

	Store(DerefOf("bna0"), Local1)
	mf88(Local1, c009, 0, 0x073, 0x074, 0)

	Store(DerefOf("ifa0"), Local1)
	mf88(Local1, c009, 0, 0x075, 0x076, 0)

	Store(DerefOf("ifa1"), Local1)
	mf88(Local1, c009, 0, 0x077, 0x078, 0)

	CH03("", 0, 0x079, __LINE__, 0)
}

// b
Method(mfa1)
{
	CH03("", 0, 0x07a, __LINE__, 0)
	Store(DerefOf(bfb0), Local1)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x07c, __LINE__, 0)
	Store(DerefOf(f0b0), Local1)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x07e, __LINE__, 0)
	Store(DerefOf(f0b1), Local1)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x080, __LINE__, 0)
	Store(DerefOf(f0b2), Local1)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x082, __LINE__, 0)
	Store(DerefOf(f0b3), Local1)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x084, __LINE__, 0)
	Store(DerefOf(bnb0), Local1)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x086, __LINE__, 0)
	Store(DerefOf(ifb0), Local1)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x088, __LINE__, 0)
	Store(DerefOf(ifb1), Local1)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)
}

// c
Method(mfa2)
{
	// Checkings

	CH03("", 0, 0x08a, __LINE__, 0)
	Store(DerefOf(e00c), Local2)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x08c, __LINE__, 0)
	Store(DerefOf(mx0c), Local2)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x08e, __LINE__, 0)
	Store(DerefOf(d00c), Local2)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x090, __LINE__, 0)
	Store(DerefOf(tz0c), Local2)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x092, __LINE__, 0)
	Store(DerefOf(pr0c), Local2)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x094, __LINE__, 0)
	Store(DerefOf(r00c), Local2)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)

	CH03("", 0, 0x096, __LINE__, 0)
	Store(DerefOf(pw0c), Local2)
	CH04("", 0, 0xff, 0, __LINE__, 0, 0)
}

Method(m12a)
{
	SRMT("mdac-21-down")
	mdac()
	SRMT("mf89-21-down")
	mf89()
	SRMT("mf8a-21-down")
	mf8a()
	SRMT("mf8b-21-down")
	mf8b()
	SRMT("mf8c-21-down")
	mf8c()
	SRMT("mf8d-21-down")
	mf8d()
	SRMT("mf8e-21-down")
	mf8e()
	SRMT("mf8f-21-down")
	mf8f()
	SRMT("mf90-21-down")
	mf90()
	SRMT("mf91-21-down")
	mf91()
	SRMT("mfa0-21-down")
	mfa0()
	SRMT("mfa1-21-down")
	mfa1()
	SRMT("mfa2-21-down")
	mfa2()
}

	/* 0 */

	Method(mm00)
	{
		Return("b000")
	}

	Method(mm01, 1)
	{
		Return(arg0)
	}

	Method(mm02, 1)
	{
		Store(DerefOf(arg0), Local7)

		Return(Local7)
	}

	Name(b000, Buffer(){ 1, 2, 3, 4, 0x95, 6, 7, 8})
	Name(bb00, Buffer(){ 1, 2, 3, 4, 0x95, 6, 7, 8})
	Name(s000, "b000")
	Name(ss00, "b000")
	Name(i000, 0)

	/* 1 */

	Name(i010, 0xaabc0123)
	Name(i987, 0xaabc0987)
	Processor(pr01, 0, 0xFFFFFFFF, 0)
	{
		Name(i000, 0xaabc0000)
	}
	Name(ii00, 0xaabc0123)
	Name(ii01, 0xaabc0987)

	Name(b001, Buffer(){ 1, 2, 3, 4, 0x95, 6, 7, 8})
	Name(bb01, Buffer(){ 1, 2, 3, 4, 0x95, 6, 7, 8})

	/* 2 */

	Name(b002, Buffer(){ 1, 2, 3, 4, 0x95, 6, 7, 8})
	Name(bb02, Buffer(){ 1, 2, 3, 4, 0x95, 6, 7, 8})
	Name(s002, "String")
	Name(ss02, "String")
	Name(i002, 0xabbc0000)
	Name(ii02, 0xabbc0000)
	Name(p002, Package() {1,2,3,4})

	/* 3 */

	Event(e003)
	Mutex(mx03, 0)
	Device(d003) { Name(i900, 0xabcd0017) }
	ThermalZone(tz03) {}
	Processor(pr03, 0, 0xFFFFFFFF, 0) {}
	OperationRegion(r003, SystemMemory, 0x100, 0x100)
	PowerResource(pw03, 1, 0) {Method(mmmm){return (0)}}

	/* 4 */

	Name(b004, Buffer(){ 1, 2, 3, 4, 0x95, 6, 7, 8})
	Name(i004, 0xabbc0000)
	Name(p004, Package() {1,2,3,4})

	/* 6 */

	Method(mm60)
	{
		Return("b006")
	}

	Method(mm61, 1)
	{
		Return(arg0)
	}

	Name(b006, Buffer(){ 1, 2, 3, 4, 0x95, 6, 7, 8})
	Name(bb06, Buffer(){ 1, 2, 3, 4, 0x95, 6, 7, 8})
	Name(s006, "b006")
	Name(ss06, "b006")
	Name(i006, 0)

	/* 7 */

	Event(e007)
	Mutex(mx07, 0)
	Device(d007) { Name(i900, 0xabcd0017) }
	ThermalZone(tz07) {}
	Processor(pr07, 0, 0xFFFFFFFF, 0) {}
	OperationRegion(r007, SystemMemory, 0x100, 0x100)
	PowerResource(pw07, 1, 0) {Method(mmmm){return (0)}}

	/* 8 */

	Name(b008, Buffer(){ 1, 2, 3, 4, 0x95, 6, 7, 8})
	Name(i008, 0xabbc0000)
	Name(p008, Package() {1,2,3,4})

	/* a */

	Name(b00a, Buffer() {0xb0,0xb1,0xb2,0xb3,0xb4})
	OperationRegion(r00a, SystemMemory, 0x100, 0x100)

	CreateField(b00a, 8, 8, bfa0)
	Field(r00a, ByteAcc, NoLock, Preserve) {f0a0,8,f0a1,8,f0a2,8,f0a3,8}
	BankField(r00a, f0a1, 0, ByteAcc, NoLock, Preserve) {bna0,4}
	IndexField(f0a2, f0a3, ByteAcc, NoLock, Preserve) {ifa0,8,ifa1,8}

	/* b */

	Name(b00b, Buffer() {0xb0,0xb1,0xb2,0xb3,0xb4})
	OperationRegion(r00b, SystemMemory, 0x100, 0x100)

	CreateField(b00b, 8, 8, bfb0)
	Field(r00b, ByteAcc, NoLock, Preserve) {f0b0,8,f0b1,8,f0b2,8,f0b3,8}
	BankField(r00b, f0b1, 0, ByteAcc, NoLock, Preserve) {bnb0,4}
	IndexField(f0b2, f0b3, ByteAcc, NoLock, Preserve) {ifb0,8,ifb1,8}

	/* c */

	Event(e00c)
	Mutex(mx0c, 0)
	Device(d00c) { Name(i900, 0xabcd0017) }
	ThermalZone(tz0c) {}
	Processor(pr0c, 0, 0xFFFFFFFF, 0) {}
	OperationRegion(r00c, SystemMemory, 0x100, 0x100)
	PowerResource(pw0c, 1, 0) {Method(mmmm){return (0)}}

	m12a()
} /* m12e */
