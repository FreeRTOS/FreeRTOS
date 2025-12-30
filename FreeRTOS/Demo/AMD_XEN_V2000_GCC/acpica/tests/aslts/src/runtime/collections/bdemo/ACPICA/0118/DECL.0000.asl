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
 * Bug 118:
 *
 * SUMMARY
 *
 * EXAMPLES
 *
 * ROOT CAUSE
 *
 * SEE ALSO:     bugs 65,66,67,68,118
 */

// Access to the named Integer object as an element of Package
Method(md79)
{
	Store(Index(pd0a, 0), Local0)
	Store(DerefOf(Local0), Local1)
	Store(ObjectType(Local1), Local0)

	if (LNotEqual(Local0, c009)) {
		err("", zFFF, __LINE__, 0, 0, Local0, c009)
	} else {
		if (LNotEqual(Local1, 0xfe7cb391d650a284)) {
			err("", zFFF, __LINE__, 0, 0, Local1, 0xfe7cb391d650a284)
		}
	}
}

// Access to the Buffer Field object as an element of Package
Method(md7a)
{
	Store(Index(pd0b, 0), Local0)
	Store(DerefOf(Local0), Local1)
	Store(ObjectType(Local1), Local0)

	if (LNotEqual(Local0, c016)) {
		err("", zFFF, __LINE__, 0, 0, Local0, c016)
	} else {
Store("=======================================", Debug)
Store(Local1, Debug)
Store(bfd1, Debug)
Store(Local1, Local0)
Store(Local0, Debug)
Store("=======================================", Debug)
if (1) {
		if (LNotEqual(Local1, 0x59)) {
			err("", zFFF, __LINE__, 0, 0, Local1, 0x59)
		}
}
	}
}

// Access to the Field Unit object as an element of Package
Method(md7b)
{
	Store(Index(pd0c, 0), Local0)
	Store(DerefOf(Local0), Local1)
	Store(ObjectType(Local1), Local0)

	if (LNotEqual(Local0, c00d)) {
		err("", zFFF, __LINE__, 0, 0, Local0, c00d)
	} else {

Store("=======================================", Debug)
Store(Local1, Debug)
Store(fd03, Debug)
Store(Local1, Local0)
Store(Local0, Debug)
Store("=======================================", Debug)
if (1) {
		if (LNotEqual(Local1, 0)) {
			err("", zFFF, __LINE__, 0, 0, Local1, 0)
		}
}
	}
}

Method(md7c)
{
	md79()
	md7a()
	md7b()
}
