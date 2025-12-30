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

// Miscellaneous named object creation


// Packages

// Effective AML package length is zero
Method(m900)
{
	Name(p000, Package() {})
}

// Effective AML package length is zero
Method(m901)
{
	Name(p000, Package(0) {})
}

// Effective AML package length is zero
Method(m902)
{
	Name(p000, Package(0) {0,1,2,3})
}

// Size exceeds 255 (It is an error for NumElements to exceed 255)
Method(m903)
{
	Name(p000, Package(256) {0,1,2,3,4,5,6,7,8,9})
}

// It is an error for NumElements to be less than the number
// of elements in the PackageList.
//
// Apparently, it will be updated:
//
// From: Moore, Robert
// Sent: Saturday, February 12, 2005 3:44 AM
// To: Therien, Guy; Hanumant Yadav; Tim Lewis
// Cc: Podrezov, Valery A; Suietov, Fiodor F
// Subject: ACPI errata for Package (2)
//
// "The Moscow validation team asked about this discrepancy"
// "Why is there a difference in behavior between BuffSize
// and NumElements? Aren’t they essentially the same thing?
// I would propose that we update Package to behave the same
// as Buffer. Bob"
Method(m904)
{
	Name(p000, Package(3) {0,1,2,3,4,5,6,7,8,9})
}

// NumElements > 255
Method(m905)
{
	Name(p000, Package() {
			// 0
			0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
			10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
			20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
			30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
			40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
			50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
			60, 61, 62, 63, 64, 65, 66, 67, 68, 69,
			70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
			80, 81, 82, 83, 84, 85, 86, 87, 88, 89,
			90, 91, 92, 93, 94, 95, 96, 97, 98, 99,

			// 100
			100, 101, 102, 103, 104, 105, 106, 107, 108, 109,
			110, 111, 112, 113, 114, 115, 116, 117, 118, 119,
			120, 121, 122, 123, 124, 125, 126, 127, 128, 129,
			130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
			140, 141, 142, 143, 144, 145, 146, 147, 148, 149,
			150, 151, 152, 153, 154, 155, 156, 157, 158, 159,
			160, 161, 162, 163, 164, 165, 166, 167, 168, 169,
			170, 171, 172, 173, 174, 175, 176, 177, 178, 179,
			180, 181, 182, 183, 184, 185, 186, 187, 188, 189,
			190, 191, 192, 193, 194, 195, 196, 197, 198, 199,

			// 200
			200, 201, 202, 203, 204, 205, 206, 207, 208, 209,
			210, 211, 212, 213, 214, 215, 216, 217, 218, 219,
			220, 221, 222, 223, 224, 225, 226, 227, 228, 229,
			230, 231, 232, 233, 234, 235, 236, 237, 238, 239,
			240, 241, 242, 243, 244, 245, 246, 247, 248, 249,
			250, 251, 252, 253, 254,

			// 255
			255
			})
}

// ArgX

Method(m906)
{
	return (0)
}

Method(m907, 1)
{
	return (0)
}

Method(m908, 2)
{
	return (0)
}

Method(m909, 3)
{
	return (0)
}

Method(m90a, 4)
{
	return (0)
}

Method(m90b, 5)
{
	return (0)
}

Method(m90c, 6)
{
	return (0)
}

Method(m90d, 7)
{
	return (0)
}

// Extra param
Method(m90e, 8)
{
	return (0)
}

Method(m90f, 7)
{
	m906(0)
	m907(0,0)
	m908(0,0,0)
	m909(0,0,0,0)
	m90a(0,0,0,0,0)
	m90b(0,0,0,0,0,0)
	m90c(0,0,0,0,0,0,0)
	m90d(0,0,0,0,0,0,0,0)
	m90e(0,0,0,0,0,0,0,0)

	return (0)
}

Method(m910)
{
	Store(Arg0, Debug)
	Store(Arg1, Debug)
	Store(Arg2, Debug)
	Store(Arg3, Debug)
	Store(Arg4, Debug)
	Store(Arg5, Debug)
	Store(Arg6, Debug)
	// Extra
	Store(Arg7, Debug)

	return (0)
}

Method(m911, 1)
{
	return (Arg1)
}

Method(m912, 2)
{
	return (Arg2)
}

Method(m913, 3)
{
	return (Arg3)
}

Method(m914, 4)
{
	return (Arg4)
}

Method(m915, 5)
{
	return (Arg5)
}

Method(m916, 6)
{
	return (Arg6)
}

Method(m917, 7)
{
	return (Arg7)
}

Method(m918)
{
	Name(db00, Debug)
}


// Data of not Namestring type in the MethodName position
Method("m919") {Return ("m919")}

// Too many arguments in Method declaration
Method(m91a, , , , , , ) {Return ("m91a")}

// NumArgs is outside of valid range 0x0-0x7
Method(m91b, 8) {Return ("m91b")}

// NumArgs as other than Type3Opcode (integer) expression
Method(m91c, Arg0) {Return ("m91c")}
Method(m91d, i000) {Return ("m91d")}
Method(m91e, Derefof(Index(Package(1){2}, 0))) {Return ("m91e")}
Method(m91f, Local0) {Return ("m91f")}

// NumArgs as Type3Opcode (integer) non-constant expression
Name(i920, 1)
Method(m920, Add(i920, 1)) {Return ("m920")}
Method(m921, Increment(i920)) {Return ("m921")}

// SerializeRule is not the keywords 'NotSerialized' and 'Serialized'
Method(m922, 7, 1, 0) {Return ("m922")}

//  SyncLevel specified when SerializeRule is not specified
Method(m923, , , 0) {Return ("m923")}

//  SyncLevel specified when SerializeRule is set up to NotSerialized
Method(m924, , NotSerialized, 0) {Return ("m924")}

// SyncLevel is outside of valid range 0x0-0xf
Method(m925, , Serialized, 16) {Return ("m925")}

// Both NumArgs and SyncLevel are outside of valid ranges
Method(m926, 8, Serialized, 16) {Return ("m926")}

// SyncLevel as other than Type3Opcode (integer) expression
Method(m927, , Serialized, Arg0, StrObj) {Return ("m927")}
Method(m928, , Serialized, i000, StrObj) {Return ("m928")}
Method(m929, , Serialized, Derefof(Index(Package(1){2}, 0)), StrObj) {Return ("m929")}
Method(m92a, , Serialized, Local0, StrObj) {Return ("m92a")}

// SyncLevel as Type3Opcode (integer) non-constant expression
Method(m92b, , Serialized, Add(i000, 1), StrObj) {Return ("m92b")}
Method(m92c, , Serialized, Increment(i000), StrObj) {Return ("m92c")}

// ReturnType is not an ObjectTypeKeywords package
Method(m92d, , , , 2) {Return ("m92d")}
Method(m92e, , , , {1, 2}) {Return ("m92e")}

// Actual Object specified to be returned is not of ReturnType type
Method(m92f, , , , PkgObj) {Return ("m92f")}

// At least one control path in the method returns no any actual Object
Method(m930, 1, , , StrObj) {if (Arg0) Return ("m930")}

// ParameterTypes is not an ObjectTypeKeywords package
Method(m931, 1, , , , 2) {Return ("m931")}
Method(m932, 2, , , , {1, StrObj}) {Return ("m932")}
Method(m933, 2, , , , {{StrObj, 1}, StrObj}) {Return ("m933")}

// Some different from UnknownObj ObjectType Keyword specified in the
// ReturnType position but no any actual Object specified to be returned.
Method(m934, , , , IntObj) {Store(1, Debug)}

// The same specific keyword in the ReturnType list twice
Method(m935, , , , {IntObj, IntObj}) {Store(1, Debug)}
Method(m936, , , , {UnknownObj, UnknownObj}) {Store(1, Debug)}

// Simulteneously UnknownObj and a specific keyword in the ReturnType list
Method(m937, , , , {UnknownObj, IntObj}) {Store(1, Debug)}

// NumArgs 0 but non-empty list of parameters
Method(m938, 0, , , , IntObj) {Return ("m938")}
Method(m939, 0, , , , {IntObj}) {Return ("m939")}
Method(m93a, , , , , {IntObj}) {Return ("m93a")}

// NumArgs 1 but 2-element list of parameters
Method(m93b, 1, , , , {IntObj, IntObj}) {Return ("m93b")}

// NumArgs 2 but 1-element list of parameters
Method(m93c, 2, , , , {IntObj}) {Return ("m93c")}

// NumArgs 6 but 5-element list of parameters
Method(m93d, 6, , , , {IntObj, IntObj, IntObj, IntObj,
	IntObj}) {Return ("m93d")}

// NumArgs 6 but 7-element list of parameters
Method(m93e, 7, , , , {IntObj, IntObj, IntObj, IntObj,
	IntObj, IntObj, IntObj}) {Return ("m93e")}

// NumArgs 7 but 8-element list of parameters
Method(m93f, 7, , , , {IntObj, IntObj, IntObj, IntObj,
	IntObj, IntObj, IntObj, IntObj}) {Return ("m93f")}

// The same specific keyword in the ParameterType list twice
Method(m940, , , , , {{IntObj, IntObj}}) {Store(1, Debug)}
Method(m941, , , , , {{UnknownObj, UnknownObj}}) {Store(1, Debug)}

// Simulteneously UnknownObj and a specific keyword in the ParameterType list
Method(m942, , , , , {{UnknownObj, IntObj}}) {Store(1, Debug)}

// An actual Object specified to be a respective argument
// of the Method is of inappropriate type
Method(m943, 1, , , , IntObj) {Store(Arg0, Debug)}
Method(m944) {m943(Package(2){255, 257})}


// Too many arguments in Function declaration
Function(m945, , , ) {Return ("m945")}

// There is at least one control path in the Function
// that returns no any actual Object:
Function(m946, IntObj) {
	Store(2, Local0)
	if (Local0) {
		Return ("m946")
	} else {
		Store(1, Debug)
	}
}

// Some different from UnknownObj ObjectType Keyword specified in the
// ReturnType position but no any actual Object specified to be returned.
Function(m947, IntObj) {Store(1, Debug)}

// The same specific keyword in the ReturnType list twice
Function(m948, {IntObj, IntObj}) {Store(1, Debug)}
Function(m949, {UnknownObj, UnknownObj}) {Store(1, Debug)}

// Simulteneously UnknownObj and a specific keyword in the ReturnType list
Function(m94a, {UnknownObj, IntObj}) {Store(1, Debug)}

// 8-element list of parameters
Function(m94b, 7, {IntObj, IntObj, IntObj, IntObj,
		IntObj, IntObj, IntObj, IntObj}) {Return ("m94b")}
