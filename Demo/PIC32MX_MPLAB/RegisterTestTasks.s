/*
	FreeRTOS.org V4.8.0 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and 
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety 
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting, 
	licensing and training services.
*/


#include <p32xxxx.h>
#include <sys/asm.h>
 
	.set	nomips16
 	.set 	noreorder
 	
 	
 	.global	vRegTest1
 	.global vRegTest2


/*	.section	.FreeRTOS, ax, @progbits */
	.set		noreorder
	.set 		noat
	.ent		vRegTest1

/* Address of $4 ulStatus1 is held in A0, so don't mess with the value of $4 */

vRegTest1:
			addiu	$1, $0, 0x11
			addiu	$2, $0, 0x12						
			addiu	$3, $0, 0x13						
			addiu	$5, $0, 0x15						
			addiu	$6, $0, 0x16						
			addiu	$7, $0, 0x17						
			addiu	$8, $0, 0x18						
			addiu	$9, $0, 0x19						
			addiu	$10, $0, 0x110						
			addiu	$11, $0, 0x111						
			addiu	$12, $0, 0x112						
			addiu	$13, $0, 0x113						
			addiu	$14, $0, 0x114						
			addiu	$15, $0, 0x115						
			addiu	$16, $0, 0x116						
			addiu	$17, $0, 0x117						
			addiu	$18, $0, 0x118						
			addiu	$19, $0, 0x119						
			addiu	$20, $0, 0x120						
			addiu	$21, $0, 0x121						
			addiu	$22, $0, 0x122						
			addiu	$23, $0, 0x123						
			addiu	$24, $0, 0x124						
			addiu	$25, $0, 0x125						
			addiu	$30, $0, 0x130						

			#if configUSE_PREEMPTION == 0
				syscall 0
			#endif

			addiu	$1, $1, -0x11
			beq		$1, $0, .+12
			nop
			sw		$0,	0($4) 
			addiu	$2, $2, -0x12					
			beq	$2, $0, .+12					
			nop									
			sw		$0,	0($4) 
			addiu	$3, $3, -0x13					
			beq	$3, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$5, $5, -0x15					
			beq	$5, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$6, $6, -0x16					
			beq	$6, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$7, $7, -0x17					
			beq	$7, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$8, $8, -0x18					
			beq	$8, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$9, $9, -0x19					
			beq	$9, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$10, $10, -0x110				
			beq	$10, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$11, $11, -0x111				
			beq	$11, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$12, $12, -0x112				
			beq	$12, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$13, $13, -0x113				
			beq	$13, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$14, $14, -0x114				
			beq	$14, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$15, $15, -0x115				
			beq	$15, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$16, $16, -0x116				
			beq	$16, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$17, $17, -0x117				
			beq	$17, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$18, $18, -0x118				
			beq	$18, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$19, $19, -0x119				
			beq	$19, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$20, $20, -0x120				
			beq	$20, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$21, $21, -0x121				
			beq	$21, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$22, $22, -0x122				
			beq	$22, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$23, $23, -0x123				
			beq	$23, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$24, $24, -0x124				
			beq	$24, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$25, $25, -0x125				
			beq	$25, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$30, $30, -0x130				
			beq	$30, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			jr		$31
			nop

	.end		vRegTest1


/*	.section	.FreeRTOS, ax, @progbits */
	.set		noreorder
	.set 		noat
	.ent		vRegTest2

vRegTest2:

			addiu	$1, $0, 0x10
			addiu	$2, $0, 0x20					
			addiu	$3, $0, 0x30					
			addiu	$5, $0, 0x50					
			addiu	$6, $0, 0x60					
			addiu	$7, $0, 0x70					
			addiu	$8, $0, 0x80					
			addiu	$9, $0, 0x90					
			addiu	$10, $0, 0x100					
			addiu	$11, $0, 0x110					
			addiu	$12, $0, 0x120					
			addiu	$13, $0, 0x130					
			addiu	$14, $0, 0x140					
			addiu	$15, $0, 0x150					
			addiu	$16, $0, 0x160					
			addiu	$17, $0, 0x170					
			addiu	$18, $0, 0x180					
			addiu	$19, $0, 0x190					
			addiu	$20, $0, 0x200					
			addiu	$21, $0, 0x210					
			addiu	$22, $0, 0x220					
			addiu	$23, $0, 0x230					
			addiu	$24, $0, 0x240					
			addiu	$25, $0, 0x250					
			addiu	$30, $0, 0x300					

			#if configUSE_PREEMPTION == 0
				syscall 0
			#endif

			addiu	$1, $1, -0x10
			beq		$1, $0, .+12
			nop
			sw		$0,	0($4) 
			addiu	$2, $2, -0x20					
			beq	$2, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$3, $3, -0x30					
			beq	$3, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$5, $5, -0x50					
			beq	$5, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$6, $6, -0x60					
			beq	$6, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$7, $7, -0x70					
			beq	$7, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$8, $8, -0x80					
			beq	$8, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$9, $9, -0x90					
			beq	$9, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$10, $10, -0x100				
			beq	$10, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$11, $11, -0x110				
			beq	$11, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$12, $12, -0x120				
			beq	$12, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$13, $13, -0x130				
			beq	$13, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$14, $14, -0x140				
			beq	$14, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$15, $15, -0x150				
			beq	$15, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$16, $16, -0x160				
			beq	$16, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$17, $17, -0x170				
			beq	$17, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$18, $18, -0x180				
			beq	$18, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$19, $19, -0x190				
			beq	$19, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$20, $20, -0x200				
			beq	$20, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$21, $21, -0x210				
			beq	$21, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$22, $22, -0x220				
			beq	$22, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$23, $23, -0x230				
			beq	$23, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$24, $24, -0x240				
			beq	$24, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$25, $25, -0x250				
			beq	$25, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			addiu	$30, $30, -0x300				
			beq	$30, $0, .+12					
			nop									
			sw		$0,	0($4) 					
			jr		$31
			nop

	.end vRegTest2
