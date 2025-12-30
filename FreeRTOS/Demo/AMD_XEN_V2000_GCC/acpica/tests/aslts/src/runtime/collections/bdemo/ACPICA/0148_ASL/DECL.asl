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
 * Bug 148:
 *
 * SUMMARY: Additional errors to be reported by iASL for Control Method Declaration
 *
 * Compiler should return error...
 */

Method(mf3e)
{
	// Some different from UnknownObj ObjectType Keyword specified in the
	// ReturnType position but no any actual Object specified to be returned.
	Method(mm1b, , , , IntObj) {Store(1, Debug)}

	// The same specific keyword in the ReturnType list twice
	Method(mm1c, , , , {IntObj, IntObj}) {Store(1, Debug)}
	Method(mm1d, , , , {UnknownObj, UnknownObj}) {Store(1, Debug)}

	// Simulteneously UnknownObj and a specific keyword in the ReturnType list
	Method(mm1e, , , , {UnknownObj, IntObj}) {Store(1, Debug)}

	// NumArgs 0 but non-empty list of parameters
	Method(mm1f, 0, , , , IntObj) {Return ("mm1f")}
	Method(mm20, 0, , , , {IntObj}) {Return ("mm20")}
	Method(mm21, , , , , {IntObj}) {Return ("mm21")}

	// NumArgs 1 but 2-element list of parameters
	Method(mm22, 1, , , , {IntObj, IntObj}) {Return ("mm22")}

	// NumArgs 2 but 1-element list of parameters
	Method(mm23, 2, , , , {IntObj}) {Return ("mm23")}

	// The same specific keyword in the ParameterType list twice
	Method(mm24, 1, , , , {{IntObj, IntObj}}) {Store(1, Debug)}
	Method(mm25, 1, , , , {{UnknownObj, UnknownObj}}) {Store(1, Debug)}

	// Simulteneously UnknownObj and a specific keyword in the ParameterType list
	Method(mm26, 1, , , , {{UnknownObj, IntObj}}) {Store(1, Debug)}

	// NumArgs 6 but 5-element list of parameters
	Method(mm27, 6, , , , {IntObj, IntObj, IntObj, IntObj,
			IntObj}) {Return ("mm27")}

	// NumArgs 6 but 7-element list of parameters
	Method(mm28, 7, , , , {IntObj, IntObj, IntObj, IntObj,
			IntObj, IntObj, IntObj}) {Return ("mm28")}

	// NumArgs 7 but 8-element list of parameters
	Method(mm29, 7, , , , {IntObj, IntObj, IntObj, IntObj,
			IntObj, IntObj, IntObj, IntObj}) {Return ("mm29")}
}
