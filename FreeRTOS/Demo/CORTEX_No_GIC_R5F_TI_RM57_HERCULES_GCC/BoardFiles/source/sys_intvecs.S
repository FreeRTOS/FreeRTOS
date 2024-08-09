/*---------------------------------------------------------------------------
 sys_intvecs.s

 Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com


  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions
  are met:

    Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.

    Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in the
    documentation and/or other materials provided with the
    distribution.

    Neither the name of Texas Instruments Incorporated nor the names of
    its contributors may be used to endorse or promote products derived
    from this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

----------------------------------------------------------------------------*/

    .syntax unified
    .cpu cortex-r5
    .arm

    .section    .intvecs,"a",%progbits
    .type       resetEntry, %object
    .size       resetEntry, .-resetEntry

/*-------------------------------------------------------------------------------*/
@ import reference for interrupt routines

    .extern     _c_int00
    .extern     FreeRTOS_SVC_Handler
    .extern     _dabort
    .extern     phantomInterrupt
    .weak       resetEntry

/*-------------------------------------------------------------------------------*/
@ interrupt vectors

resetEntry:
    b   _c_int00
undefEntry:
    b   undefEntry
svcEntry:
    b   FreeRTOS_SVC_Handler
prefetchEntry:
    b   prefetchEntry
dataAbortEntry:
    b   _dabort
    b   phantomInterrupt
    /** This LDR loads the memory at ‘PC - 0x1B0’, which is the address of
     * IRQVECREG: 0x18 - 0x1B0 = 0xFFFFFE70. */
    ldr pc,[pc,#-0x1b0]
    /** This LDR loads the memory at ‘PC - 0x1B0’, which is the address of
     * FIQVECREG: 0x1C - 0x1B0 = 0xFFFFFE70. */
    ldr pc,[pc,#-0x1b0]

/*-------------------------------------------------------------------------------*/
