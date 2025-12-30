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
 * Bug 116:
 *
 * SUMMARY: The ASL Compiler doesn't recognize attempts to generate IRefs to arbitrary type objects
 *
 * Compiler should return error...
 */

	Method(me87)
	{
		Name(i000, 0xabcdef)
		Name(b000, Buffer() {1,2,3,4,5,6,7,8,9})
		OperationRegion(r000, SystemMemory, 0x100, 0x100)
		Field(r000, ByteAcc, NoLock, Preserve) {f000,8}
		Field(r000, ByteAcc, NoLock, Preserve) {bnk0,8,f00a,8,f00b,8}
		BankField(r000, bnk0, 0, ByteAcc, NoLock, Preserve) {bkf0,4}
		IndexField(f00a, f00b, ByteAcc, NoLock, Preserve) {if00,1,if01,1}
		CreateField(b000, 0, 8, bf00)

		Index(i000, 0)    // i000 - Integer
		Index(bf00, 0)    // bf00 - Buffer Field
		Index(f000, 0)    // f000 - Field Unit by Field()
		Index(bkf0, 0)    // bkf0 - Field Unit by BankField()
		Index(if00, 0)    // if00 - Field Unit by IndexField()
	}
