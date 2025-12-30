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

// Miscellaneous tests which are difficult to bring
// into correlation with the particular known group

Method(me00)
{
	Store("\x00", Debug)
	Store("\x000123", Debug)
	Store("\x00123", Debug)
	Store("\x00xyz", Debug)
	Store("1\x00", Debug)
	Store("z\x00", Debug)
	Store("2\x000123", Debug)
	Store("x\x000123", Debug)
	Store("3\x00xyz", Debug)
	Store("w\x00xyz", Debug)
}

// Strings originally exceeding the maximal size, 200 symbols
Method(me01)
{
	Store("012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890", Local0)
	Store(Local0, Debug)
}

/*
 * Locally Created Data Objects are used before they
 * are actually created though they are dynamic objects
 * which appears only after execution of the relevant
 * operator (Name in our example).
 *
 * 5.5.2.4 Local Variables and Locally Created Data Objects:
 *	NameSpace objects created within the scope of a method
 *	are dynamic. They exist only for the duration of the
 *	method execution. They are created when specified by
 *	the code...
 */
Method(me02)
{
	Store(0x12345678, n000)
	Name(n000, 0)
}

// Commented, because it stops translation.
// // From Bug 62.
// Method(me02)
// {
// //	Name(s001, "\\sq\"v")
// 	Name(s002, "\sq"v")
// }

Method(me03)
{
	Store("me03", Debug)
}

//       Method(me03)
// Errorb1034 - ^ Name already exists in scope (ME03)
Method(me03)
{
	Store("me03", Debug)
}

//         Name(n000, 0)
// Error 1034 - ^ Name already exists in scope (N000)
Method(me04)
{
	Name(n000, 0)
	Name(n000, 0)

	Store(n000, Debug)
}

//         Name(n000, 0)
// Error 1034 - ^ Name already exists in scope (N000)
Method(me05)
{
	Name (VV, 0x1234)
	Store (32, Local0)

	Name (VV, 0xBBBBAAAA)
	Store (12, Local2)
}
