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

// Method execution control

// The same values in Case: two Case(0)
Method(m300, 1)
{
	Switch(ToInteger(Arg0)) {
		case (0) {
			Store("Case 0", Debug)
		}
		case (0) {
			Store("Case 0, also", Debug)
		}
	}
}

// The same values in Case:
// two the same values in Package of Case.
Method(m301, 1)
{
	Switch(ToInteger(Arg0)) {
		Case (Package(2) {7, 7}) {
			Store("Case 0", Debug)
		}
	}
}

//       Switch(Arg0)
// Warning 2091 ^ Switch expression is not a static
// Integer/Buffer/String data type, defaulting to Integer
Method(m302, 1)
{
	Switch(Arg0) {
		case (0) {
			Store("Case 0", Debug)
		}
	}
}

// MicroSeconds parameter is too large
Method(m303)
{
	// Ok yet
	Stall(100)

	// To be reported
	Stall(101)
}

// Statement is unreachable
Method(m304)
{
	Store("Point 0", Debug)

	Return (0)

	Store("Point 1", Debug)
}
