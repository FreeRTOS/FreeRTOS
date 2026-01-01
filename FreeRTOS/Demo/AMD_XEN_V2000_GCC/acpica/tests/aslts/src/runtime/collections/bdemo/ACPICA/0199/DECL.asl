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
 * Bug 199:
 *
 * SUMMARY: No exception on DerefOf for parameter which is none of ObjectReference/IndexReference/String
 */

Method(mfb2,, Serialized)
	{
	Name(b000, Buffer(){ 1, 2, 3, 4, 0x95, 6, 7, 8})
	Name(i000, 0xabbc0000)
	Name(p000, Package() {1,2,3,4})

	CH03("", 0, 0x000, __LINE__, 0)
	Store(DerefOf(b000), Local0)
	CH04("", 1, 47, 0, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE

	CH03("", 0, 0x002, __LINE__, 0)
	Store(DerefOf(i000), Local0)
	CH04("", 1, 47, 0, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE

	CH03("", 0, 0x004, __LINE__, 0)
	Store(DerefOf(p000), Local0)
	CH04("", 1, 47, 0, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE
}

Method(mfb3,, Serialized)
{
	Event(e000)
	Mutex(mx00, 0)
	Device(d000) { Name(i900, 0xabcd0017) }
	ThermalZone(tz00) {}
	Processor(pr00, 0, 0xFFFFFFFF, 0) {}
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	PowerResource(pw00, 1, 0) {Method(mmmm){return (0)}}

	CH03("", 0, 0x006, __LINE__, 0)
	Store(DerefOf(e000), Local0)
	CH04("", 1, 47, 0, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE

	CH03("", 0, 0x008, __LINE__, 0)
	Store(DerefOf(mx00), Local0)
	CH04("", 1, 47, 0, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE

	CH03("", 0, 0x00a, __LINE__, 0)
	Store(DerefOf(d000), Local0)
	CH04("", 1, 47, 0, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE

	CH03("", 0, 0x00c, __LINE__, 0)
	Store(DerefOf(tz00), Local0)
	CH04("", 1, 47, 0, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE

	CH03("", 0, 0x00e, __LINE__, 0)
	Store(DerefOf(pr00), Local0)
	CH04("", 1, 47, 0, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE

	CH03("", 0, 0x010, __LINE__, 0)
	Store(DerefOf(r000), Local0)
	CH04("", 1, 47, 0, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE

	CH03("", 0, 0x012, __LINE__, 0)
	Store(DerefOf(pw00), Local0)
	CH04("", 1, 47, 0, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE
}
