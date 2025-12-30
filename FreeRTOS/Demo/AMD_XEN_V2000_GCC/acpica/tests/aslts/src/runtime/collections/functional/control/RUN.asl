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

if (STTT("Method execution control", TCLF, 3, W003)) {

// m0ed()
// m0fd()
if (1) {
	SRMT("CTL0")
	CTL0()
	SRMT("CTL1")
	CTL1()
	SRMT("CTL2")
	CTL2()
	SRMT("TIM0")
	if (F64) {
		TIM0()
	} else {
		/*
		 * Skip the test in 32-bit mode.
		 *
		 * In the 32-bit mode the Timer with the 100
		 * nanosecond period can provide the gradually
		 * increased values during only 7 minutes before
		 * it overflows and starts from the beginning.
		 * We can't use the Timer operator at all because
		 * it can overflow inside any the measured period.
		 */
		SKIP()
	}
	SRMT("SW01")
	SW01()
	SRMT("SW02")
	SW02()
	SRMT("SW03")
	SW03()
	SRMT("SW04")
	SW04()
	SRMT("SW05")
	SW05()
	SRMT("SW06")
	SW06()
	SRMT("SW07")
	SW07()
	SRMT("SW08")
	SW08()
	SRMT("SW09")
	SW09()
	SRMT("SW10")
	SW10()
	SRMT("WHL0")
	WHL0()

	m0ed()
	m0fd()
}

}
FTTT()

Include("../../../../runtime/collections/functional/control/Return/RUN.asl")
Include("../../../../runtime/collections/functional/control/ImplicitReturn/RUN.asl")
