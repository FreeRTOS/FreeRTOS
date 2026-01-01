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

	// All declarations
	Include("../../../../../runtime/cntl/DECL_5UP.asl")
	Include("../../../../../runtime/common/operations.asl")
	Include("../../../../../runtime/common/conversion/oproc.asl")
	Include("../../../../../runtime/common/conversion/otest.asl")
	Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand2/exc_00_undef.asl")
	Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand2/exc_01_int.asl")
	Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand2/exc_02_str.asl")
	Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand2/exc_03_buf.asl")
	Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand2/exc_04_pckg.asl")
	Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand2/exc_05_funit.asl")
	Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand2/exc_06_dev.asl")
	Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand2/exc_07_event.asl")
	Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand2/exc_08_method.asl")
	Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand2/exc_09_mux.asl")
	Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand2/exc_10_oreg.asl")
	Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand2/exc_11_pwr.asl")
	Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand2/exc_12_proc.asl")
	Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand2/exc_13_tzone.asl")
	Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand2/exc_14_bfield.asl")
	Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand2/exc_operand2.asl")
	Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand1/exc_operand1.asl")

	Method(MAIN) {

		// Initialization
		STRT(0)

		// Run verification methods

		Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand1/RUN.asl")
		Include("../../../../../runtime/collections/exceptions/exc_operand/exc_operand2/RUN.asl")

		// Final actions
		Store(FNSH(), Local7)

		return (Local7)
	}
}
