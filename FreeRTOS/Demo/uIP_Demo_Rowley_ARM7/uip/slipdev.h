/**
 * \addtogroup slip
 * @{
 */

/**
 * \file
 * SLIP header file.
 * \author Adam Dunkels <adam@dunkels.com>
 */

/*
 * Copyright (c) 2001, Adam Dunkels.
 * All rights reserved. 
 *
 * Redistribution and use in source and binary forms, with or without 
 * modification, are permitted provided that the following conditions 
 * are met: 
 * 1. Redistributions of source code must retain the above copyright 
 *    notice, this list of conditions and the following disclaimer. 
 * 2. Redistributions in binary form must reproduce the above copyright 
 *    notice, this list of conditions and the following disclaimer in the 
 *    documentation and/or other materials provided with the distribution. 
 * 3. The name of the author may not be used to endorse or promote
 *    products derived from this software without specific prior
 *    written permission.  
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS
 * OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
 * GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.  
 *
 * This file is part of the uIP TCP/IP stack.
 *
 * $Id: slipdev.h,v 1.1.2.3 2003/10/06 22:42:51 adam Exp $
 *
 */

#ifndef __SLIPDEV_H__
#define __SLIPDEV_H__

#include "uip.h"

/**
 * Put a character on the serial device.
 *
 * This function is used by the SLIP implementation to put a character
 * on the serial device. It must be implemented specifically for the
 * system on which the SLIP implementation is to be run.
 *
 * \param c The character to be put on the serial device.
 */
void slipdev_char_put(u8_t c);

/**
 * Poll the serial device for a character.
 *
 * This function is used by the SLIP implementation to poll the serial
 * device for a character. It must be implemented specifically for the
 * system on which the SLIP implementation is to be run.
 *
 * The function should return immediately regardless if a character is
 * available or not. If a character is available it should be placed
 * at the memory location pointed to by the pointer supplied by the
 * arguement c.
 *
 * \param c A pointer to a byte that is filled in by the function with
 * the received character, if available.
 *
 * \retval 0 If no character is available.
 * \retval Non-zero If a character is available.
 */
u8_t slipdev_char_poll(u8_t *c);

void slipdev_init(void);
void slipdev_send(void);
u16_t slipdev_poll(void);

#endif /* __SLIPDEV_H__ */

/** @} */
