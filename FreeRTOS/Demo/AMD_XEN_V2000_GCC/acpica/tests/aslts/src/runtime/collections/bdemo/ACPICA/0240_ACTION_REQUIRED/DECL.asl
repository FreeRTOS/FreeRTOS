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
 * Bug 240:
 *
 * SUMMARY: No exception when not owner thread runs Release of Global lock
 *
 * Note:
 *
 *   Run this demo by the Threads debug operation
 *   on two threads (use <Threads 2 1 MAIN> command).
 */

Mutex(MX00, 0)

Name(i000, 0) // thread 0: succeeded to Acquire Mutex
Name(i001, 0) // thread 1: after attempt to Release Mutex

Name(cnt0, 0)
Name(cnt1, 0)

/*
 * Demo 1:
 * The expected exception AE_AML_NOT_OWNER doesn't occur when
 * some thread (thread 1) attempt to Release the Global lock
 * which is successfully Acquired by another thread (thread 0).
 *
 * Thread 0 Acquires the Global lock (\_GL),
 * then thread 1 attempts to Release that Global lock.
 * The mentioned exception should arisen there, but in fact - no exception -
 * the Global lock is successfully Released by another thread (by thread 1).
 * It is a bug.
 *
 *   arg0 - Index of current thread
 */
Method(m032, 1)
{
		While (1) {
			if (LEqual(arg0, 0)) {
				Store("Thread 0: start of cycle", Debug)
				if (LNot(cnt0)) {
					Store(Acquire(\_GL, 0xffff), Local0)
					if (Local0) {
						Store("Thread 0: failed to Acquire GL", Debug)
						err("", zFFF, __LINE__, 0, 0, 0, 0)
					} else {
						Store("Thread 0: succeeded to Acquire GL", Debug)
						Store(1, i000)
					}
				}
				Increment(cnt0)
				if (LEqual(cnt0, 20)) {
					break
				}
			} elseif (LEqual(arg0, 1)) {
				Store("Thread 1: start of cycle", Debug)
				if (i000) {
					if (LNot(i001)) {
						Store("Thread 1: before attempt to Release GL", Debug)
						Release(\_GL)
						CH04("", 0, 63, 0, __LINE__, 0, 0) // AE_AML_NOT_OWNER
						Store("Thread 1: after attempt to Release GL", Debug)
						Store(1, i001)
					}
				}
				Increment(cnt1)
				if (LEqual(cnt1, 20)) {
					break
				}
			} else {
				break
			}
			Sleep(100)
		}
}

/*
 * Demo 2:
 * The expected exception AE_AML_NOT_OWNER occurs when some
 * thread (thread 1) attempt to Release the usual mutex which
 * is successfully Acquired by another thread (thread 0).
 *
 * Identical to m000 but the usual mutex MX00 is substituted instead of Global lock.
 *
 *   arg0 - Index of current thread
 */
Method(m033, 1)
{
		While (1) {
			if (LEqual(arg0, 0)) {
				Store("Thread 0: start of cycle", Debug)
				if (LNot(cnt0)) {
					Store(Acquire(MX00, 0xffff), Local0)
					if (Local0) {
						Store("Thread 0: failed to Acquire MX00", Debug)
						err("", zFFF, __LINE__, 0, 0, 0, 0)
					} else {
						Store("Thread 0: succeeded to Acquire MX00", Debug)
						Store(1, i000)
					}
				}
				Increment(cnt0)
				if (LEqual(cnt0, 20)) {
					break
				}
			} elseif (LEqual(arg0, 1)) {
				Store("Thread 1: start of cycle", Debug)
				if (i000) {
					if (LNot(i001)) {
						Store("Thread 1: before attempt to Release MX00", Debug)
						Release(MX00)
						CH04("", 0, 63, 0, __LINE__, 0, 0) // AE_AML_NOT_OWNER
						Store("Thread 1: after attempt to Release MX00", Debug)
						Store(1, i001)
					}
				}
				Increment(cnt1)
				if (LEqual(cnt1, 20)) {
					break
				}
			} else {
				break
			}
			Sleep(100)
		}
}
