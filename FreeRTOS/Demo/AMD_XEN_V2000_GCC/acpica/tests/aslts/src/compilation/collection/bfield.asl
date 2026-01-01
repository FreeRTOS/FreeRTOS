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

// Buffer Fields

// Compiler crashed for Create*Field with FieldName specified
// by LocalX and ArgX.
Method(m100, 4)
{
	// Compiler crashes for each of these Create*Field
	// (FieldName specified by LocalX):

	Store("bf06", Local0)
	Store("bf07", Local1)
	Store("bf08", Local2)
	Store("bf09", Local3)
	Store("bf0a", Local4)
	Store("bf0b", Local5)

	CreateBitField   (arg0, arg1,       Local0)
	CreateByteField  (arg0, arg1,       Local1)
	CreateDWordField (arg0, arg1,       Local2)
	CreateField      (arg0, arg1, arg2, Local3)
	CreateQWordField (arg0, arg1,       Local4)
	CreateWordField  (arg0, arg1,       Local5)


	// Compiler crashes for each of these Create*Field
	// (FieldName specified by ArgX):

	CreateBitField   (arg0, arg1,       arg3)
	CreateByteField  (arg0, arg1,       arg3)
	CreateDWordField (arg0, arg1,       arg3)
	CreateField      (arg0, arg1, arg2, arg3)
	CreateQWordField (arg0, arg1,       arg3)
	CreateWordField  (arg0, arg1,       arg3)
}
