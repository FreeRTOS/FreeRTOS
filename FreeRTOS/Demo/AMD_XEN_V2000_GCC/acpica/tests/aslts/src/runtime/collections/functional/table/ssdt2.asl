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
 * The Load operator tests auxiliary SSDT,
 * specifies the _REG Methods for globally and
 * dynamically decleared OpRegions.
 */

DefinitionBlock(
	"ssdt2.aml",   // Output filename
	"SSDT",     // Signature
	0x02,       // DSDT Revision
	"Intel",    // OEMID
	"Many",     // TABLE ID
	0x00000001  // OEM Revision
	) {

	Device (AUXD) {

		OperationRegion (OPR0, 0x80, 0x1000000, 0x4)

		Field (OPR0, DWordAcc, NoLock, Preserve) {
			RF00,   32}

		Name (REGC, 0xFFFFFFFF)
		Name (REGP, 0)

		Name (REGD, 0xFFFFFFFF)
		Name (REGR, 0)

		Method(_REG, 2)
		{
			Store("\\AUXD._REG:", Debug)
			Store(arg0, Debug)
			Store(arg1, Debug)

			if (LEqual(arg0, 0x80)) {
				Store(REGC, REGP)
				Store(arg1, REGC)
			}
		}

		Method(M000)
		{
			Method(_REG, 2)
			{
				Store("\\AUXD.M000._REG:", Debug)
				Store(arg0, Debug)
				Store(arg1, Debug)

				if (LEqual(arg0, 0x80)) {
					Store(REGD, REGR)
					Store(arg1, REGD)
				}
			}

			OperationRegion (OPR1, 0x80, 0x1000010, 0x4)

			Field (OPR1, DWordAcc, NoLock, Preserve) {
				RF01,   32}

			Store("\\AUXD.M000:", Debug)
			Store(RF01, Debug)
			Store(REGR, Debug)
		}
	}
}
