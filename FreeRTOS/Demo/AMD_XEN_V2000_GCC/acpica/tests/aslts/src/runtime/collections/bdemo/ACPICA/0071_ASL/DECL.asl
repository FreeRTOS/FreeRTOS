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
 * Bug 0071:
 *
 * SUMMARY: The ASL Compiler should reject Resource Descriptors where ResourceSourceIndex is omitted but ResourceSource is present
 *
 * Compiler should return error...
 */

Method(me0a)
{
	Name (RT00,	ResourceTemplate () {
		DWordIO ( , , , , ,
			0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff,, "PATHPATHPATH")

		DWordMemory ( , , , , , ReadOnly,
			0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff,, "PATHPATHPATH")

		Interrupt (ResourceConsumer, Edge, ActiveLow, Shared            ,, "PATHPATHPATH")
			{0xfcfdfeff}

		QWordIO ( , , , , ,
			0xd8d9dadbdcdddedf, 0xe0e1e2e3e4e5e6e7, 0xe8e9eaebecedeeef,
			0xf0f1f2f3f4f5f6f7, 0xf8f9fafbfcfdfeff                    ,, "PATHPATHPATH")

		QWordMemory ( , , , , , ReadOnly,
			0xd8d9dadbdcdddedf, 0xe0e1e2e3e4e5e6e7, 0xe8e9eaebecedeeef,
			0xf0f1f2f3f4f5f6f7, 0xf8f9fafbfcfdfeff                    ,, "PATHPATHPATH")

		WordBusNumber ( , , , ,
			0xf6f7, 0xf8f9, 0xfafb, 0xfcfd, 0xfeff                    ,, "PATHPATHPATH")

		WordIO ( , , , , ,
			0xf6f7, 0xf8f9, 0xfafb, 0xfcfd, 0xfeff                    ,, "PATHPATHPATH")

		DWordSpace (0xc0, , , , , 0x5a,
			0xecedeeef, 0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff,, "PATHPATHPATH")

		QWordSpace (0xc0, , , , , 0x5a,
			0xd8d9dadbdcdddedf, 0xe0e1e2e3e4e5e6e7, 0xe8e9eaebecedeeef,
			0xf0f1f2f3f4f5f6f7, 0xf8f9fafbfcfdfeff                    ,, "PATHPATHPATH")

		WordSpace (0xc0, , , , , 0x5a,
			0xf6f7, 0xf8f9, 0xfafb, 0xfcfd, 0xfeff                    ,, "PATHPATHPATH")
	})

	Store(RT00, Debug)
}
