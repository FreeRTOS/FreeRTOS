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

DefinitionBlock(
	"full.aml",   // Output filename
	"DSDT",     // Signature
	0x02,       // DSDT Revision
	"Intel",    // OEMID
	"Many",     // TABLE ID
	0x00000001  // OEM Revision
	) {

	Include("../../../../../runtime/cntl/DECL_5UP.asl")

	Include("../../../../../runtime/collections/functional/arithmetic/arithmetic.asl")

	Include("../../../../../runtime/collections/functional/bfield/crbuffield.asl")

	Include("../../../../../runtime/collections/functional/control/ctl0.asl")
	Include("../../../../../runtime/collections/functional/control/ctl1.asl")
	Include("../../../../../runtime/collections/functional/control/ctl2.asl")
	Include("../../../../../runtime/collections/functional/control/timing.asl")
	Include("../../../../../runtime/collections/functional/control/switch1.asl")
	Include("../../../../../runtime/collections/functional/control/switch2.asl")
	Include("../../../../../runtime/collections/functional/control/switch3.asl")
	Include("../../../../../runtime/collections/functional/control/switch4.asl")
	Include("../../../../../runtime/collections/functional/control/switch5.asl")
	Include("../../../../../runtime/collections/functional/control/switch6.asl")
	Include("../../../../../runtime/collections/functional/control/while.asl")
	Include("../../../../../runtime/collections/functional/control/Return/return.asl")
	Include("../../../../../runtime/collections/functional/control/ImplicitReturn/add.asl")
	Include("../../../../../runtime/collections/functional/control/ImplicitReturn/store.asl")
	Include("../../../../../runtime/collections/functional/control/ImplicitReturn/standaloneret.asl")

	Include("../../../../../runtime/collections/functional/manipulation/mid.asl")
	Include("../../../../../runtime/collections/functional/manipulation/concatenate.asl")
	Include("../../../../../runtime/collections/functional/manipulation/tointeger.asl")
	Include("../../../../../runtime/collections/functional/manipulation/tostring.asl")
	Include("../../../../../runtime/collections/functional/manipulation/tobuffer.asl")
	Include("../../../../../runtime/collections/functional/manipulation/todecimalstring.asl")
	Include("../../../../../runtime/collections/functional/manipulation/tohexstring.asl")
	Include("../../../../../runtime/collections/functional/manipulation/tofrombcd.asl")
	Include("../../../../../runtime/collections/functional/manipulation/eisaid.asl")
	Include("../../../../../runtime/collections/functional/manipulation/touuid.asl")
	Include("../../../../../runtime/collections/functional/manipulation/unicode.asl")
	Include("../../../../../runtime/collections/functional/manipulation/objecttype.asl")
	Include("../../../../../runtime/collections/functional/manipulation/store.asl")
	Include("../../../../../runtime/collections/functional/manipulation/match1.asl")
	Include("../../../../../runtime/collections/functional/manipulation/match2.asl")
	Include("../../../../../runtime/collections/functional/manipulation/sizeof.asl")

	Include("../../../../../runtime/collections/functional/logic/logical.asl")

	Include("../../../../../runtime/common/operations.asl")
	Include("../../../../../runtime/common/conversion/oproc.asl")
	Include("../../../../../runtime/common/conversion/otest.asl")

	Include("./misc.asl")

	Method(MAIN) {
		return (0)
	}
}
