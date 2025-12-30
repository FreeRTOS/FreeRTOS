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
 * Bug 239:
 *
 * SUMMARY: Crash in a slack-multi-threading mode when returning from the method experienced exception
 *
 * Note:
 *
 *   Run this in a slack mode (use AcpiExec -s <this_demo>)
 *   by the Threads debug operation on more than one thread
 *   (use <Threads 2 1 main> command). In this case the example
 *   causes crash of AcpiExec for any exception occurred during
 *   execution of methods (m000, m001).
 */

Mutex(MX08, 8)
Mutex(MX09, 9)

Method(m034)
{

	Method(mm00, 1)
	{
		Method(m000)
		{
			Acquire(MX09, 0xffff)
			/*
			 * Operation below causes AE_AML_MUTEX_ORDER exception
			 * (it is correct).
			 */
			Acquire(MX08, 0xffff)
		}

		Method(m001, 1)
		{
			/*
			 * Operation below causes AE_AML_DIVIDE_BY_ZERO exception
			 */
			Divide(1, arg0)
		}

		/* Any of these calls causes crash of AcpiExec */

		if (0) {
			m000()
		}
		if (1) {
			m001(0)
		}
	}

	/* This example doesn't cause crash */
	Method(mm01, 1)
	{
		Divide(1, arg0)
	}

	Method(mm02)
	{
		if (1) {
			mm00(0)
		}
		if (0) {
			/* This example doesn't cause crash */
			mm01(0)
		}
	}

	mm02()
}
