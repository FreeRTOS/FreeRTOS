/* ---------------------------------------------------------------------------- */
/*                  Atmel Microcontroller Software Support                      */
/*                       SAM Software Package License                           */
/* ---------------------------------------------------------------------------- */
/* Copyright (c) 2014, Atmel Corporation                                        */
/*                                                                              */
/* All rights reserved.                                                         */
/*                                                                              */
/* Redistribution and use in source and binary forms, with or without           */
/* modification, are permitted provided that the following condition is met:    */
/*                                                                              */
/* - Redistributions of source code must retain the above copyright notice,     */
/* this list of conditions and the disclaimer below.                            */
/*                                                                              */
/* Atmel's name may not be used to endorse or promote products derived from     */
/* this software without specific prior written permission.                     */
/*                                                                              */
/* DISCLAIMER:  THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR   */
/* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF */
/* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE   */
/* DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,      */
/* INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT */
/* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,  */
/* OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF    */
/* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING         */
/* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, */
/* EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                           */
/* ---------------------------------------------------------------------------- */

#ifndef _SAM_
#define _SAM_

#if defined __SAME70J19__
  #include "same70j19.h"
#elif defined __SAME70J20__
  #include "same70j20.h"
#elif defined __SAME70J21__
  #include "same70j21.h"
#elif defined __SAME70N19__
  #include "same70n19.h"
#elif defined __SAME70N20__
  #include "same70n20.h"
#elif defined __SAME70N21__
  #include "same70n21.h"
#elif defined __SAME70Q19__
  #include "same70q19.h"
#elif defined __SAME70Q20__
  #include "same70q20.h"
#elif defined __SAME70Q21__
  #include "same70q21.h"
#elif defined __SAMS70J19__
  #include "sams70j19.h"
#elif defined __SAMS70J20__
  #include "sams70j20.h"
#elif defined __SAMS70J21__
  #include "sams70j21.h"
#elif defined __SAMS70N19__
  #include "sams70n19.h"
#elif defined __SAMS70N20__
  #include "sams70n20.h"
#elif defined __SAMS70N21__
  #include "sams70n21.h"
#elif defined __SAMS70Q19__
  #include "sams70q19.h"
#elif defined __SAMS70Q20__
  #include "sams70q20.h"
#elif defined __SAMS70Q21__
  #include "sams70q21.h"
#elif defined __SAMV70J19__
  #include "samv70j19.h"
#elif defined __SAMV70J20__
  #include "samv70j20.h"
#elif defined __SAMV70N19__
  #include "samv70n19.h"
#elif defined __SAMV70N20__
  #include "samv70n20.h"
#elif defined __SAMV70Q19__
  #include "samv70q19.h"
#elif defined __SAMV70Q20__
  #include "samv70q20.h"
#elif defined __SAMV71J19__
  #include "samv71j19.h"
#elif defined __SAMV71J20__
  #include "samv71j20.h"
#elif defined __SAMV71J21__
  #include "samv71j21.h"
#elif defined __SAMV71N19__
  #include "samv71n19.h"
#elif defined __SAMV71N20__
  #include "samv71n20.h"
#elif defined __SAMV71N21__
  #include "samv71n21.h"
#elif defined __SAMV71Q19__
  #include "samv71q19.h"
#elif defined __SAMV71Q20__
  #include "samv71q20.h"
#elif defined __SAMV71Q21__
  #include "samv71q21.h"
#else
  #error Library does not support the specified device.
#endif

#endif /* _SAM_ */
