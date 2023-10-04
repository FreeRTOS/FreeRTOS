/*
 * File:	vectors.s
 * Purpose:	MCF5225x vector table
 * 
 * License:     All software covered by license agreement in -
 *              docs/Freescale_Software_License.pdf
 */

#ifdef __GNUC__ /* { */
#define sr %sr
#define _asm_exception_handler      irq_handler
#define _timer_handler    timer_handler
#endif /* } __GNUC__ */

	.global VECTOR_TABLE
	.global _VECTOR_TABLE
	.global start

	.extern ___SP_INIT
	.extern _asm_startmeup
	.extern _asm_exception_handler
	.extern _vPIT0InterruptHandler
	.extern vPortYieldISR
	.extern _vFECISRHandler	
	.text

/*
 * Exception Vector Table
 */
VECTOR_TABLE:
_VECTOR_TABLE:
INITSP:		.long	___SP_INIT				/* Initial SP			*/
INITPC:		.long	_asm_startmeup			/* Initial PC			*/
vector02:	.long	_asm_exception_handler	/* Access Error			*/
vector03:	.long	_asm_exception_handler	/* Address Error		*/
vector04:	.long	_asm_exception_handler	/* Illegal Instruction	*/
vector05:	.long	_asm_exception_handler	/* Reserved				*/
vector06:	.long	_asm_exception_handler	/* Reserved				*/
vector07:	.long	_asm_exception_handler	/* Reserved				*/
vector08:	.long	_asm_exception_handler	/* Privilege Violation	*/
vector09:	.long	_asm_exception_handler	/* Trace				*/
vector0A:	.long	_asm_exception_handler	/* Unimplemented A-Line	*/
vector0B:	.long	_asm_exception_handler	/* Unimplemented F-Line	*/
vector0C:	.long	_asm_exception_handler	/* Debug Interrupt		*/
vector0D:	.long	_asm_exception_handler	/* Reserved				*/
vector0E:	.long	_asm_exception_handler	/* Format Error			*/
vector0F:	.long	_asm_exception_handler	/* Unitialized Int.		*/
vector10:	.long	_asm_exception_handler	/* Reserved				*/
vector11:	.long	_asm_exception_handler	/* Reserved				*/
vector12:	.long	_asm_exception_handler	/* Reserved				*/
vector13:	.long	_asm_exception_handler	/* Reserved				*/
vector14:	.long	_asm_exception_handler	/* Reserved				*/
vector15:	.long	_asm_exception_handler	/* Reserved				*/
vector16:	.long	_asm_exception_handler	/* Reserved				*/
vector17:	.long	_asm_exception_handler	/* Reserved				*/
vector18:	.long	_asm_exception_handler	/* Spurious Interrupt	*/
vector19:	.long	_asm_exception_handler	/* Autovector Level 1	*/
vector1A:	.long	_asm_exception_handler	/* Autovector Level 2	*/
vector1B:	.long	_asm_exception_handler	/* Autovector Level 3	*/
vector1C:	.long	_asm_exception_handler	/* Autovector Level 4	*/
vector1D:	.long	_asm_exception_handler	/* Autovector Level 5	*/
vector1E:	.long	_asm_exception_handler	/* Autovector Level 6	*/
vector1F:	.long	_asm_exception_handler	/* Autovector Level 7	*/
vector20:	.long	_asm_exception_handler	/* TRAP #0				*/
vector21:	.long	_asm_exception_handler	/* TRAP #1				*/
vector22:	.long	_asm_exception_handler	/* TRAP #2				*/
vector23:	.long	_asm_exception_handler	/* TRAP #3				*/
vector24:	.long	_asm_exception_handler	/* TRAP #4				*/
vector25:	.long	_asm_exception_handler	/* TRAP #5				*/
vector26:	.long	_asm_exception_handler	/* TRAP #6				*/
vector27:	.long	_asm_exception_handler	/* TRAP #7				*/
vector28:	.long	_asm_exception_handler	/* TRAP #8				*/
vector29:	.long	_asm_exception_handler	/* TRAP #9				*/
vector2A:	.long	_asm_exception_handler	/* TRAP #10				*/
vector2B:	.long	_asm_exception_handler	/* TRAP #11				*/
vector2C:	.long	_asm_exception_handler	/* TRAP #12				*/
vector2D:	.long	_asm_exception_handler	/* TRAP #13				*/
vector2E:	.long	_asm_exception_handler	/* TRAP #14				*/
vector2F:	.long	_asm_exception_handler	/* TRAP #15				*/
vector30:	.long	_asm_exception_handler	/* Reserved				*/
vector31:	.long	_asm_exception_handler	/* Reserved				*/
vector32:	.long	_asm_exception_handler	/* Reserved				*/
vector33:	.long	_asm_exception_handler	/* Reserved				*/
vector34:	.long	_asm_exception_handler	/* Reserved				*/
vector35:	.long	_asm_exception_handler	/* Reserved				*/
vector36:	.long	_asm_exception_handler	/* Reserved				*/
vector37:	.long	_asm_exception_handler	/* Reserved				*/
vector38:	.long	_asm_exception_handler	/* Reserved				*/
vector39:	.long	_asm_exception_handler	/* Reserved				*/
vector3A:	.long	_asm_exception_handler	/* Reserved				*/
vector3B:	.long	_asm_exception_handler	/* Reserved				*/
vector3C:	.long	_asm_exception_handler	/* Reserved				*/
vector3D:	.long	_asm_exception_handler	/* Reserved				*/
vector3E:	.long	_asm_exception_handler	/* Reserved				*/
vector3F:	.long	_asm_exception_handler	/* Reserved				*/
vector40:	.long	_asm_exception_handler
vector41:	.long	_asm_exception_handler
vector42:	.long	_asm_exception_handler
vector43:	.long	_asm_exception_handler
vector44:	.long	_asm_exception_handler
vector45:	.long	_asm_exception_handler
vector46:	.long	_asm_exception_handler
vector47:	.long	_asm_exception_handler
vector48:	.long	_asm_exception_handler
vector49:	.long	_asm_exception_handler
vector4A:	.long	_asm_exception_handler
vector4B:	.long	_asm_exception_handler
vector4C:	.long	_asm_exception_handler
vector4D:	.long	_asm_exception_handler
vector4E:	.long	_asm_exception_handler
vector4F:	.long	_asm_exception_handler
vector50:	.long	vPortYieldISR
vector51:	.long	_asm_exception_handler
vector52:	.long	_asm_exception_handler
vector53:	.long	_asm_exception_handler
vector54:	.long	_asm_exception_handler
vector55:	.long	_asm_exception_handler
vector56:	.long	_asm_exception_handler
vector57:	.long	_asm_exception_handler
vector58:	.long	_asm_exception_handler
vector59:	.long	_vFECISRHandler
vector5A:	.long	_vFECISRHandler
vector5B:	.long	_vFECISRHandler
vector5C:	.long	_vFECISRHandler
vector5D:	.long	_vFECISRHandler
vector5E:	.long	_vFECISRHandler
vector5F:	.long	_vFECISRHandler
vector60:	.long	_asm_exception_handler
vector61:	.long	_vFECISRHandler
vector62:	.long	_vFECISRHandler
vector63:	.long	_vFECISRHandler
vector64:	.long	_asm_exception_handler
vector65:	.long	_asm_exception_handler
vector66:	.long	_asm_exception_handler
vector67:	.long	_asm_exception_handler
vector68:	.long	_asm_exception_handler
vector69:	.long	_asm_exception_handler
vector6A:	.long	_asm_exception_handler
vector6B:	.long	_asm_exception_handler
vector6C:	.long	_asm_exception_handler
vector6D:	.long	_asm_exception_handler
vector6E:	.long	_asm_exception_handler
vector6F:	.long	_asm_exception_handler
vector70:	.long	_asm_exception_handler
vector71:	.long	_asm_exception_handler
vector72:	.long	_asm_exception_handler
vector73:	.long	_asm_exception_handler
vector74:	.long	_asm_exception_handler
vector75:	.long	_asm_exception_handler
vector76:	.long	_asm_exception_handler
vector77:	.long	_vPIT0InterruptHandler
vector78:	.long	_asm_exception_handler
vector79:	.long	_asm_exception_handler
vector7A:	.long	_asm_exception_handler
vector7B:	.long	_asm_exception_handler
vector7C:	.long	_asm_exception_handler
vector7D:	.long	_asm_exception_handler
vector7E:	.long	_asm_exception_handler
vector7F:	.long	_asm_exception_handler	
vector80:	.long	_asm_exception_handler
vector81:	.long	_asm_exception_handler
vector82:	.long	_asm_exception_handler
vector83:	.long	_asm_exception_handler
vector84:	.long	_asm_exception_handler
vector85:	.long	_asm_exception_handler
vector86:	.long	_asm_exception_handler
vector87:	.long	_asm_exception_handler
vector88:	.long	_asm_exception_handler
vector89:	.long	_asm_exception_handler
vector8A:	.long	_asm_exception_handler
vector8B:	.long	_asm_exception_handler
vector8C:	.long	_asm_exception_handler
vector8D:	.long	_asm_exception_handler
vector8E:	.long	_asm_exception_handler
vector8F:	.long	_asm_exception_handler
vector90:	.long	_asm_exception_handler
vector91:	.long	_asm_exception_handler
vector92:	.long	_asm_exception_handler
vector93:	.long	_asm_exception_handler
vector94:	.long	_asm_exception_handler
vector95:	.long	_asm_exception_handler
vector96:	.long	_asm_exception_handler
vector97:	.long	_asm_exception_handler
vector98:	.long	_asm_exception_handler
vector99:	.long	_asm_exception_handler
vector9A:	.long	_asm_exception_handler
vector9B:	.long	_asm_exception_handler
vector9C:	.long	_asm_exception_handler
vector9D:	.long	_asm_exception_handler
vector9E:	.long	_asm_exception_handler
vector9F:	.long	_asm_exception_handler
vectorA0:	.long	_asm_exception_handler
vectorA1:	.long	_asm_exception_handler
vectorA2:	.long	_asm_exception_handler
vectorA3:	.long	_asm_exception_handler
vectorA4:	.long	_asm_exception_handler
vectorA5:	.long	_asm_exception_handler
vectorA6:	.long	_asm_exception_handler
vectorA7:	.long	_asm_exception_handler
vectorA8:	.long	_asm_exception_handler
vectorA9:	.long	_asm_exception_handler
vectorAA:	.long	_asm_exception_handler
vectorAB:	.long	_asm_exception_handler
vectorAC:	.long	_asm_exception_handler
vectorAD:	.long	_asm_exception_handler
vectorAE:	.long	_asm_exception_handler
vectorAF:	.long	_asm_exception_handler
vectorB0:	.long	_asm_exception_handler
vectorB1:	.long	_asm_exception_handler
vectorB2:	.long	_asm_exception_handler
vectorB3:	.long	_asm_exception_handler
vectorB4:	.long	_asm_exception_handler
vectorB5:	.long	_asm_exception_handler
vectorB6:	.long	_asm_exception_handler
vectorB7:	.long	_asm_exception_handler
vectorB8:	.long	_asm_exception_handler
vectorB9:	.long	_asm_exception_handler
vectorBA:	.long	_asm_exception_handler
vectorBB:	.long	_asm_exception_handler
vectorBC:	.long	_asm_exception_handler
vectorBD:	.long	_asm_exception_handler
vectorBE:	.long	_asm_exception_handler
vectorBF:	.long	_asm_exception_handler

    .org 0x400

/* 
 * CFM Flash Configuration Field 
 */
KEY_UPPER:  .long   0x00000000
KEY_LOWER:  .long   0x00000000
CFMPROT:    .long   0x00000000
CFMSACC:    .long   0x00000000
CFMDACC:    .long   0x00000000
CFMSEC:     .long   0x00000000


/********************************************************************/



	.end
