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
 * Access to Method type objects
 *
 * SEE ALSO: misc/m15b
 *
 * Add here the tests of types:
 * - \xx.xx (relative to the root)
 * - ^xx.xx (relative to the parent)
 * -  xx.xx
 * - Methods inside another type objects
 */

/* Access to Method in one level up */

Method(m13b)
{
	return (0xabcd0000)
}

Method(m138)
{
	CH03("", 0, 0x098, __LINE__, 0)
	Store(DerefOf("m13b"), Local0)
	if (SLCK) {
		CH03("", 0, 0x099, __LINE__, 0)
		Store(ObjectType(Local0), Local1)
		if (LNotEqual(Local1, c010)) {
			err("", zFFF, __LINE__, 0, 0, Local1, c010)
		}
	} else {
		CH04("", 0, 47, 0, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE
	}
}

/* Access to the Method itself */

Method(m12c)
{
	CH03("", 0, 0x09c, __LINE__, 0)
	Store(DerefOf("m12c"), Local0)
	if (SLCK) {
		CH03("", 0, 0x09d, __LINE__, 0)
		Store(ObjectType(Local0), Local1)
		if (LNotEqual(Local1, c010)) {
			err("", zFFF, __LINE__, 0, 0, Local1, c010)
		}
	} else {
		CH04("", 0, 47, 0, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE
	}
}

/* Access to Method of the same level */

Method(m139)
{
	Method(m13c)
	{
		return (0xabcd0003)
	}

	CH03("", 0, 0x0a0, __LINE__, 0)
	Store(DerefOf("m13c"), Local0)
	if (SLCK) {
		CH03("", 0, 0x0a1, __LINE__, 0)
		Store(ObjectType(Local0), Local1)
		if (LNotEqual(Local1, c010)) {
			err("", zFFF, __LINE__, 0, 0, Local1, c010)
		}
	} else {
		CH04("", 0, 47, 0, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE
	}
}

/* Access to Method in one level up inside another Method */

Method(m13a)
{
	Method(m13d)
	{
		return (0xabcd0004)
	}
	Method(m138)
	{
		CH03("", 0, 0x0a4, __LINE__, 0)
		Store(DerefOf("m13d"), Local0)
		if (SLCK) {
			CH03("", 0, 0x0a5, __LINE__, 0)
			Store(ObjectType(Local0), Local1)
			if (LNotEqual(Local1, c010)) {
				err("", zFFF, __LINE__, 0, 0, Local1, c010)
			}
		} else {
			CH04("", 0, 47, 0, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE
		}
	}
	m138()
}

Method(m12f)
{
	SRMT("m138")
	m138()
	SRMT("m12c")
	m12c()
	SRMT("m139")
	m139()
	SRMT("m13a")
	m13a()
}
