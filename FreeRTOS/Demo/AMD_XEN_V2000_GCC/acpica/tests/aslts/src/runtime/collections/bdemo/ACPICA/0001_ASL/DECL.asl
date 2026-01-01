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
 * Bug 0001:
 *
 * COMPONENT: Will not be fixed
 *
 * SUMMARY: The ASL Compiler doesn't allow non-constant TimeoutValue for Acquire
 */

Method(md9b)
{
	Name(TOUT, 0)

	Store(Acquire(mxd0, 0), Local0)
	if (Local0) {
		err("", zFFF, __LINE__, 0, 0, 0, Local0)
	}

	Store(Acquire(mxd0, 0x1000), Local0)
	if (Local0) {
		err("", zFFF, __LINE__, 0, 0, 0, Local0)
	}

	Store(0x1000, Local1)
	Store(Acquire(mxd0, Local1), Local0)
	if (Local0) {
		err("", zFFF, __LINE__, 0, 0, 0, Local0)
	}

	Store(Acquire(mxd0, TOUT), Local0)
	if (Local0) {
		err("", zFFF, __LINE__, 0, 0, 0, Local0)
	}
}

/*
Intel ACPI Component Architecture
ASL Optimizing Compiler version 20050930 [Oct 15 2005]
Copyright (C) 2000 - 2005 Intel Corporation
Supports ACPI Specification Revision 3.0

../../../../runtime/cntl/common.asl  1139:     switch (arg0) {
Warning  2092 -                                           ^ Switch expression is not a static Integer/Buffer/String data type, defaulting to Integer

../../../../runtime/cntl/common.asl  1353:     Switch (Local0) {
Warning  2092 -                                             ^ Switch expression is not a static Integer/Buffer/String data type, defaulting to Integer

../../../../runtime/collections/bdemo/0001/DECL.asl    24:     Store(Acquire(mxd0, Local1), Local0)
Error    1094 -                                                             parse error ^

../../../../runtime/collections/bdemo/0001/DECL.asl    24:     Store(Acquire(mxd0, Local1), Local0)
Error    1043 -                                                             Invalid type ^  ([NoReturnValue] found, Store operator requires [Integer|String|Buffer|Package|DdbHandle|Reference])

../../../../runtime/collections/bdemo/0001/DECL.asl    29:     Store(Acquire(mxd0, TOUT), Local0)
Error    1094 -                                                           parse error ^

../../../../runtime/collections/bdemo/0001/DECL.asl    29:     Store(Acquire(mxd0, TOUT), Local0)
Error    1043 -                                                           Invalid type ^  ([NoReturnValue] found, Store operator requires [Integer|String|Buffer|Package|DdbHandle|Reference])

ASL Input:  main.asl - 41 lines, 154106 bytes, 3969 keywords
Compilation complete. 4 Errors, 2 Warnings, 0 Remarks, 1818 Optimizations
*/