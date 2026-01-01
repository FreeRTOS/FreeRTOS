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
 * Module level execution under DefinitionBlock/Scope
 */

/*
 * Verify if Type1Opcode (ex., If) and Type2Opcode (ex., Store) is allowed
 * under DefinitionBlock or Scope
 *
 * ASL spec state:
 * 1. DefinitionBlockTerm supports TermList for ACPI 1.0 ~ 6.0.
 * 2. ScopeTerm supports TermList for ACPI 1.0 and ObjectList for
 *    ACPI 2.0 ~ 6.0.
 *
 * AML spec state:
 * 1. AMLCode supports TermList for ACPI 2.0 ~ 6.0.
 * 2. DefScope supports ObjectList for ACPI 1.0 and TermList for
 *    ACPI 2.0 ~ 6.0.
 *
 * It appears the AML interpreter should support TermList for both
 * DefinitionBlock and Scope, but the ASL grammar is not compliant to the
 * AML grammar and the real world.
 */

Name(z180, 180)

/* Tests for Type1Opcode */

Name(ml00, 0)
Name(ml01, 0)
Name(ml02, 0)

if (LEqual(ml00, 0)) {
	Store(2, ml00)
}
Scope(\)
{
	if (LEqual(ml01, 0)) {
		Store(2, ml01)
	}
}
Scope(\_SB)
{
	if (LEqual(ml02, 0)) {
		Store(2, ml02)
	}
}

Method(MLS0,, Serialized)
{
	Name(ts, "MLS0")

	Store("TEST: MLS0, Type1Opcode is executable under scopes", Debug)

	if (LNotEqual(ml00, 2)) {
		err(ts, z180, __LINE__, z180, 0, ml00, 2)
	}
	if (LNotEqual(ml01, 2)) {
		err(ts, z180, __LINE__, z180, 1, ml01, 2)
	}
	if (LNotEqual(ml02, 2)) {
		err(ts, z180, __LINE__, z180, 2, ml02, 2)
	}
}

/* Tests for Type2Opcode */

Name(ml03, 0)
Name(ml04, 0)
Name(ml05, 0)

Store (1, ml03)
if (LEqual(ml03, 1)) {
	Store(2, ml03)
}
Scope(\)
{
	Store (1, ml04)
	if (LEqual(ml04, 1)) {
		Store(2, ml04)
	}
}
Scope(\_SB)
{
	Store (1, ml05)
	if (LEqual(ml05, 1)) {
		Store(2, ml05)
	}
}

Method(MLS1,, Serialized)
{
	Name(ts, "MLS1")

	Store("TEST: MLS1, Type2Opcode is executable under scopes", Debug)

	if (LNotEqual(ml03, 2)) {
		err(ts, z180, __LINE__, z180, 3, ml03, 2)
	}
	if (LNotEqual(ml04, 2)) {
		err(ts, z180, __LINE__, z180, 4, ml04, 2)
	}
	if (LNotEqual(ml05, 2)) {
		err(ts, z180, __LINE__, z180, 5, ml05, 2)
	}
}
