/**
 * \file
 *
 * Copyright (c) 2012 Atmel Corporation. All rights reserved.
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

#ifndef _SAM3XA_GPBR_COMPONENT_
#define _SAM3XA_GPBR_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR General Purpose Backup Register */
/* ============================================================================= */
/** \addtogroup SAM3XA_GPBR General Purpose Backup Register */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Gpbr hardware registers */
typedef struct {
  RwReg SYS_GPBR[8]; /**< \brief (Gpbr Offset: 0x0) General Purpose Backup Register */
} Gpbr;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- SYS_GPBR[8] : (GPBR Offset: 0x0) General Purpose Backup Register -------- */
#define SYS_GPBR_GPBR_VALUE_Pos 0
#define SYS_GPBR_GPBR_VALUE_Msk (0xffffffffu << SYS_GPBR_GPBR_VALUE_Pos) /**< \brief (SYS_GPBR[8]) Value of GPBR x */
#define SYS_GPBR_GPBR_VALUE(value) ((SYS_GPBR_GPBR_VALUE_Msk & ((value) << SYS_GPBR_GPBR_VALUE_Pos)))

/*@}*/


#endif /* _SAM3XA_GPBR_COMPONENT_ */
