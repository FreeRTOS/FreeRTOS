/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/*------------------------------------------------------------------------------
 *         Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

/*------------------------------------------------------------------------------
 *         Exported functions
 *----------------------------------------------------------------------------*/

/**
 *  Returns the minimum value between two integers.
 *
 *  \param a  First integer to compare.
 *  \param b  Second integer to compare.
 */
extern uint32_t min( uint32_t dwA, uint32_t dwB )
{
	if ( dwA < dwB ) {
		return dwA ;
	} else {
		return dwB ;
	}
}

/*------------------------------------------------------------------------------
 *  Returns the absolute value of an integer.
 *
 *  \param value  Integer value.
 *
 *  \note Do not call this function "abs", problem with gcc !
 */
extern uint32_t absv( int32_t lValue )
{
	if ( lValue < 0 ) {
		return -lValue ;
	} else {
		return lValue ;
	}
}

/*------------------------------------------------------------------------------
 *  Computes and returns x power of y.
 *
 *  \param x  Value.
 *  \param y  Power.
 */
extern uint32_t power( uint32_t dwX, uint32_t dwY )
{
	uint32_t dwResult = 1 ;

	while ( dwY > 0 ) {
		dwResult *= dwX ;
		dwY-- ;
	}
	return dwResult ;
}

