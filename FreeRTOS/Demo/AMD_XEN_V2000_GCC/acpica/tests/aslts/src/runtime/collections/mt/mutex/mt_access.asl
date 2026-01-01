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
 * Multi access to different type data
 *
 * Types:
 * - Buffer
 * - Package
 *
 * Notations:
 *
 * Leading thread - the worker thread #1 which plays in the relevant test
 *                  some control role.
 */


/* Leading thread (thread #1) put there commands for other threads */
Name(b900, Buffer(){0,0,0,0,0,0,0,0})

/*
 * This buffer is zeroed by the leading thread and then to
 * be filled by other worker threads, some non-zero respond to
 * the leading thread.
 */
Name(b901, Buffer(){0,0,0,0,0,0,0,0})

/*
 * This buffer is zeroed by the leading thread and then to be
 * filled by other worker threads when they see that i900 is zero.
 *
 * The leading thread uses it to check that all the worker threads
 * saw zero i900 before to start the next command.
 */
Name(b902, Buffer(){0,0,0,0,0,0,0,0})

Name(i900, 0)    // signal start fulfilling command
Name(i901, 0x30) // to do command 0x30 once only
Name(c900, 0x31) //

/*
 * Test #.
 *
 * Leading thread (thread #1) is a controlling thread other are worker threads here.
 *
 * arg0 - number of threads
 * arg1 - ID of current thread
 * arg2 - Index of current thread
 */
Method(m900, 1)
{
	if (LGreater(arg0, 8)) {
		se00(arg2, er06)
		return
	}
	if (LGreaterEqual(arg2, arg0)) {
		se00(arg2, er06)
	}

	if (LEqual(arg2, 1)) {

		/* Leading thread */

		While (1) {

			if (i901) {
				Store(0, i901)
				m200(b900, arg0, 0x30)
				m200(b901, arg0, 0)
				Store(1, i900)
			}

			m206(arg2, sl01)
		}
	} else {
		While (1) {

			/* Determine the command for particular thread */

			Store(c900, Local0)

			/* Control thread allows for worker threads to fulfill their commands */
			if (i900) {
				Store(DerefOf(Index(b901, arg2)), Local1)
				/* This thread doesn't yet fulfill its command */
				if (LNot(Local1)) {
					/* Command to be fulfilled */
					Store(DerefOf(Index(b900, arg2)), Local0)
				}
				/* Unnecessary */
				if (LNot(i900)) {
					Store(c900, Local0)
				}
			}

			if (LNot(i900)) {
				Store(DerefOf(Index(b902, arg2)), Local0)
				if (LNot(Local0)) {
					/* Any non-zero value */
					Store(rs00, Index(b902, arg2))
				}
			}
			m206(arg2, sl01)
		}
	}
}

/*
 * Thread 1 waits for all the worker threads to
 * fulfill the specified for them the buffer of commands.
 *
 * arg0 - number of threads
 * arg1 - flag if to check that all the worker threads saw my zero do00
 */
Method(m9ff, 2)
{
	Name(lpN0, 0)
	Name(lpC0, 0)
	Name(find, 0)

	/*
	 * Check that all the worker threads saw my
	 * non-zero do00 and fulfilled the proper command.
	 */
	While (1) {
		Store(0, find)
		Store(arg0, lpN0)
		Store(0, lpC0)
		While (lpN0) {

			/* For not a Control thread only */
			if (LNotEqual(lpC0, 0)) {
				Store(DerefOf(Index(b900, lpC0)), Local0)
				Store(DerefOf(Index(b901, lpC0)), Local1)
				if (LNotEqual(Local0, Local1)) {
					Store(1, find)
					break
				}
			}

			Decrement(lpN0)
			Increment(lpC0)
		}

		if (LNot(find)) {
			break
		}

		/*
		 * Don't report about Control thread sleeping -
		 * don't use m206(0, sl00).
		 */
		Sleep(sl00)
	}

	/*
	 * Check that all the worker threads saw my zero do00
	 * (if only it is not the EXIT command).
	 * Note: assumed that EXIT command is specified for all
	 *       the threads simultaneously, so only.
	 */
	if (arg1) {
		if (fl01) {
			m109()
		} else {
			m200(b902, arg0, 0)
		}
		Store(0, do00)
		While (1) {
			Store(0, find)
			if (fl01) {
				Store(m10a(), find)
			} else {
				Store(arg0, lpN0)
				Store(0, lpC0)
				While (lpN0) {

					/* For not a Control thread only */
					if (LNotEqual(lpC0, 0)) {
						Store(DerefOf(Index(b902, lpC0)), Local0)
						if (LNot(Local0)) {
							Store(1, find)
							break
						}
					}

					Decrement(lpN0)
					Increment(lpC0)
				}
			}

			if (LNot(find)) {
				break
			}

			/*
			 * Don't report about Control thread sleeping -
			 * don't use m206(0, sl00).
			 */
			Sleep(sl00)
		}

		/* All the worker threads are ready for any next command */
	}
}
