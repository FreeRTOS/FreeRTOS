/**
 * \file
 *
 * \brief Arch file for SAM.
 *
 * This file defines common SAM series.
 *
 * Copyright (c) 2011-2015 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */
/*
 * Support and FAQ: visit <a href="http://www.atmel.com/design-support/">Atmel Support</a>
 */

#ifndef _SAM_IO_
#define _SAM_IO_

/* SAM3 family */

/* SAM3S series */
#if (SAM3S)
# if (SAM3S8 || SAM3SD8)
#  include "sam3s8.h"
# else
#  include "sam3s.h"
# endif
#endif

/* SAM3U series */
#if (SAM3U)
#  include "sam3u.h"
#endif

/* SAM3N series */
#if (SAM3N)
#  include "sam3n.h"
#endif

/* SAM3XA series */
#if (SAM3XA)
#  include "sam3xa.h"
#endif

/* SAM4S series */
#if (SAM4S)
#  include "sam4s.h"
#endif

/* SAM4L series */
#if (SAM4L)
#  include "sam4l.h"
#endif

/* SAM4E series */
#if (SAM4E)
#  include "sam4e.h"
#endif

/* SAM4N series */
#if (SAM4N)
#  include "sam4n.h"
#endif

/* SAM4C series */
#if (SAM4C)
#  include "sam4c.h"
#endif

/* SAM4CM series */
#if (SAM4CM)
#  if (SAM4CMP32 || SAM4CMS32)
#    include "sam4cm32.h"
#  else
#    include "sam4cm.h"
#  endif
#endif

/* SAM4CP series */
#if (SAM4CP)
#  include "sam4cp.h"
#endif

/* SAMG51 series */
#if (SAMG51)
#  include "samg51.h"
#endif

/* SAMG53 series */
#if (SAMG53)
#  include "samg53.h"
#endif

/* SAMG54 series */
#if (SAMG54)
#  include "samg54.h"
#endif

/* SAMG55 series */
#if (SAMG55)
#  include "samg55.h"
#endif

/* SAMV71 series */
#if (SAMV71)
#  include "samv71.h"
#endif

/* SAMV70 series */
#if (SAMV70)
#  include "samv70.h"
#endif

/* SAME70 series */
#if (SAME70)
#  include "same70.h"
#endif

/* SAMS70 series */
#if (SAMS70)
#  include "sams70.h"
#endif

#endif /* _SAM_IO_ */
