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
 * Method execution control
 *
 * Simple checkings for {if,elseif,else} operators
 * One level {if,elseif,else}
 */

Name(z003, 3)

Method(m070, 1)
{
	Store(0x12345678, Local0)

	if (LEqual(arg0, 0)) {
		Store(0, Local0)
	}

	return (Local0)
}

Method(m071, 1)
{
	Store(0x12345678, Local0)

	if (LEqual(arg0, 0)) {
		Store(0, Local0)
	} else {
		Store(1, Local0)
	}

	return (Local0)
}

Method(m072, 1)
{
	Store(0x12345678, Local0)

	if (LEqual(arg0, 0)) {
		Store(0, Local0)
	} elseif (LEqual(arg0, 1)) {
		Store(1, Local0)
	}

	return (Local0)
}

Method(m073, 1)
{
	Store(0x12345678, Local0)

	if (LEqual(arg0, 0)) {
		Store(0, Local0)
	} elseif (LEqual(arg0, 1)) {
		Store(1, Local0)
	} else {
		Store(2, Local0)
	}

	return (Local0)
}

// Run verify methods
// NOTE: use here as few control operators as possible
Method(m074,, Serialized)
{
	Name(ts, "m074")

	Store("TEST: m074, One level {if, elseif, else}", Debug)

	// m070

	Store(0, Local7)
	Store(m070(Local7), Local0)
	if (LNotEqual(Local0, Local7)){
		err(ts, z003, __LINE__, 0, 0, Local7, 0)
	}

	Store(0x12345678, Local7)
	Store(m070(Local7), Local0)
	if (LNotEqual(Local0, Local7)){
		err(ts, z003, __LINE__, 0, 0, Local7, 0)
	}

	// m071

	Store(0, Local7)
	While(LLess(Local7, 2)) {
		Store(m071(Local7), Local0)
		if (LNotEqual(Local0, Local7)){
			err(ts, z003, __LINE__, 0, 0, Local7, 0)
		}
		Increment(Local7)
	}

	Store(0x12345678, Local7)
	Store(m071(Local7), Local0)
	if (LNotEqual(Local0, 1)){
		err(ts, z003, __LINE__, 0, 0, Local7, 0)
	}

	// m072

	Store(0, Local7)
	While(LLess(Local7, 2)) {
		Store(m072(Local7), Local0)
		if (LNotEqual(Local0, Local7)){
			err(ts, z003, __LINE__, 0, 0, Local7, 0)
		}
		Increment(Local7)
	}

	Store(0x12345678, Local7)
	Store(m072(Local7), Local0)
	if (LNotEqual(Local0, Local7)){
		err(ts, z003, __LINE__, 0, 0, Local7, 0)
	}

	// m073

	Store(0, Local7)
	While(LLess(Local7, 3)) {
		Store(m073(Local7), Local0)
		if (LNotEqual(Local0, Local7)){
			err(ts, z003, __LINE__, 0, 0, Local7, 0)
		}
		Increment(Local7)
	}

	Store(0x12345678, Local7)
	Store(m073(Local7), Local0)
	if (LNotEqual(Local0, 2)){
		err(ts, z003, __LINE__, 0, 0, Local7, 0)
	}
}

// Run-method
Method(CTL0)
{
	Store("TEST: CTL0, Conditional execution", Debug)

	m074()
}
