/*
 * File: exceptions.h
 * Purpose: Generic exception handling for ColdFire processors
 *
 * Notes:
 */

#ifndef _MCF_EXCEPTIONS_H
#define _MCF_EXCEPTIONS_H

#ifdef __cplusplus
extern "C" {
#endif

/***********************************************************************/
/*
 * This is the handler for all exceptions which are not common to all 
 * ColdFire Chips.  
 *
 * Called by mcf_exception_handler
 * 
 */
void derivative_interrupt(unsigned long vector);

/***********************************************************************/
/*
 * This is the exception handler for all  exceptions common to all 
 * chips ColdFire.  Most exceptions do nothing, but some of the more 
 * important ones are handled to some extent.
 *
 * Called by asm_exception_handler 
 */
void mcf_exception_handler(void *framepointer);


/***********************************************************************/
/*
 * This is the assembly exception handler defined in the vector table.  
 * This function is in assembler so that the frame pointer can be read  
 * from the stack.
 * Note that the way to give the stack frame as argument to the c handler
 * depends on the used ABI (Register, Compact or Standard).
 *
 */
asm void asm_exception_handler(void);

/***********************************************************************/
/* MCF5xxx exceptions table initialization:
 *
 * Set VBR and performs RAM vector table initialization.
 * The following symbol should be defined in the lcf:
 * __VECTOR_RAM
 *
 * _vect is the start of the exception table in the code
 * In case _vect address is different from __VECTOR_RAM,
 * the vector table is copied from _vect to __VECTOR_RAM.
 * In any case VBR is set to __VECTOR_RAM.
 */ 
void initialize_exceptions(void);


#ifdef __cplusplus
}
#endif

#endif   /* _MCF_EXCEPTIONS_H */

