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
 * Spec: Store of Non-computational type objects
 * to Computational type object causes exceptions.
 */

// Package --> Integer

Method(md01,, Serialized)
{
	Name(pppp, Package(1){Buffer() {1,2,3,4}})
	Name(i000, 0x5678)

	CH03("", 0, 0x000, __LINE__, 0)
	Store(pppp, i000)
	CH04("", 0, 47, 0, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE
}

// Package --> String

Method(md02,, Serialized)
{
	Name(pppp, Package(1){Buffer() {1,2,3,4}})
	Name(s000, "String")

	CH03("", 0, 0x002, __LINE__, 0)
	Store(pppp, s000)
	CH04("", 0, 47, 0, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE
}

// Package --> Buffer

Method(md03,, Serialized)
{
	Name(pppp, Package(1){Buffer() {1,2,3,4}})
	Name(b000, Buffer() {1,2,3,4})

	CH03("", 0, 0x004, __LINE__, 0)
	Store(pppp, b000)
	CH04("", 0, 47, 0, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE
}

Method(md04)
{
	CH03("", 0, 0xf00, __LINE__, 0)
	md01()
	md02()
	md03()
	CH03("", 0, 0xf01, __LINE__, 0)
}
