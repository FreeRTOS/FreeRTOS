/*
 * File:    mcf5xxx.c
 * Purpose: Generic high-level routines for generic ColdFire processors
 *
 * Notes:       
 * 
 * License:     All software covered by license agreement in -
 *              docs/Freescale_Software_License.pdf
 */

#include "common.h"

/********************************************************************/

#define EXCEPTFMT  "%s -- PC = %#08X\n"

/********************************************************************/
/*
 * This is the exception handler for all defined exceptions.  Most
 * exceptions do nothing, but some of the more important ones are
 * handled to some extent.
 *
 * Called by asm_exception_handler 
 */
void 
mcf5xxx_exception_handler (void *framep) 
{
    switch (MCF5XXX_RD_SF_FORMAT(framep))
    {
        case 4:
        case 5:
        case 6:
        case 7:
            break;
        default:
            printf(EXCEPTFMT,"Illegal stack type", MCF5XXX_SF_PC(framep));
            break;
    }

    switch (MCF5XXX_RD_SF_VECTOR(framep))
    {
        case 2:
            printf(EXCEPTFMT, "Access Error", MCF5XXX_SF_PC(framep));
            switch (MCF5XXX_RD_SF_FS(framep))
            {
                case 4:
                    printf("Error on instruction fetch\n");
                    break;
                case 8:
                    printf("Error on operand write\n");
                    break;
                case 9:
                    printf("Attempted write to write-protected space\n");
                    break;
                case 12:
                    printf("Error on operand read\n");
                    break;
                default:
                    printf("Reserved Fault Status Encoding\n");
                    break;
            }
            break;
        case 3:
            printf(EXCEPTFMT, "Address Error", MCF5XXX_SF_PC(framep));
            switch (MCF5XXX_RD_SF_FS(framep))
            {
                case 4:
                    printf("Error on instruction fetch\n");
                    break;
                case 8:
                    printf("Error on operand write\n");
                    break;
                case 9:
                    printf("Attempted write to write-protected space\n");
                    break;
                case 12:
                    printf("Error on operand read\n");
                    break;
                default:
                    printf("Reserved Fault Status Encoding\n");
                    break;
            }
            break;
        case 4:
            printf(EXCEPTFMT, "Illegal instruction", MCF5XXX_SF_PC(framep));
            break;
        case 8:
            printf(EXCEPTFMT, "Privilege violation", MCF5XXX_SF_PC(framep));
            break;
        case 9:
            printf(EXCEPTFMT, "Trace Exception", MCF5XXX_SF_PC(framep));
            break;
        case 10:
            printf(EXCEPTFMT, "Unimplemented A-Line Instruction", \
                MCF5XXX_SF_PC(framep));
            break;
        case 11:
            printf(EXCEPTFMT, "Unimplemented F-Line Instruction", \
                MCF5XXX_SF_PC(framep));
            break;
        case 12:
            printf(EXCEPTFMT, "Debug Interrupt", MCF5XXX_SF_PC(framep));
            break;
        case 14:
            printf(EXCEPTFMT, "Format Error", MCF5XXX_SF_PC(framep));
            break;
        case 15:
            printf(EXCEPTFMT, "Unitialized Interrupt", MCF5XXX_SF_PC(framep));
            break;
        case 24:
            printf(EXCEPTFMT, "Spurious Interrupt", MCF5XXX_SF_PC(framep));
            break;
        case 25:
        case 26:
        case 27:
        case 28:
        case 29:
        case 30:
        case 31:
            printf("Autovector interrupt level %d\n",
                MCF5XXX_RD_SF_VECTOR(framep) - 24);
            break;
        case 32:
        case 33:
        case 34:
        case 35:
        case 36:
        case 37:
        case 38:
        case 39:
        case 40:
        case 41:
        case 42:
        case 43:
        case 44:
        case 45:
        case 46:
        case 47:
            printf("TRAP #%d\n", MCF5XXX_RD_SF_VECTOR(framep) - 32);
            break;
        case 5:
        case 6:
        case 7:
        case 13:
        case 16:
        case 17:
        case 18:
        case 19:
        case 20:
        case 21:
        case 22:
        case 23:
        case 48:
        case 49:
        case 50:
        case 51:
        case 52:
        case 53:
        case 54:
        case 55:
        case 56:
        case 57:
        case 58:
        case 59:
        case 60:
        case 61:
        case 62:
        case 63:
            printf("Reserved: #%d\n", MCF5XXX_RD_SF_VECTOR(framep));
            break;
        default:
            cpu_handle_interrupt(MCF5XXX_RD_SF_VECTOR(framep));
            break;
    }
}

/********************************************************************/
/*
 * Interpret the reset values of D0 and D1
 *
 * Parameters:
 *  d0  - the reset value of data register zero
 *  d1  - the reset value of data register one
 */
void
mcf5xxx_interpret_d0d1(int d0, int d1)
{
#ifdef DEBUG_PRINT
    printf("\nColdFire Core Configuration:\n");
    printf("----------------------------\n");
    printf("Processor Family       %#02x\n",MCF5XXX_D0_PF(d0));
    printf("ColdFire Core Version: %d\n",MCF5XXX_D0_VER(d0));
    printf("Processor Revision:    %d\n",MCF5XXX_D0_REV(d1));
    printf("Bus Width:             ");
    switch (MCF5XXX_D1_BUSW(d1))
    {
        case 0:
            printf("32-bit\n");
            break;
        default:
            printf("Reserved\n");
    }
    printf("ISA Version:           ");
    switch (MCF5XXX_D0_ISA(d0))
    {
        case 0:
            printf("A\n");
            break;
        case 1:
            printf("B\n");
            break;
        case 2:
            printf("C\n");
            break;
        case 8:
            printf("A+\n");
            break;
        default:
            printf("Reserved\n");
    }
    printf("Debug Version:         ");
    switch (MCF5XXX_D0_DEBUG(d0))
    {
        case 0:
            printf("A\n");
            break;
        case 1:
            printf("B\n");
            break;
        case 2:
            printf("C\n");
            break;
        case 3:
            printf("D\n");
            break;
        case 4:
            printf("E\n");
            break;
        case 9:
            printf("B+\n");
            break;
        default :
            printf("Reserved\n");
    }
    printf("MAC:                   %s\n", MCF5XXX_D0_MAC(d0) ? "Yes" : "No");
    printf("DIV:                   %s\n", MCF5XXX_D0_DIV(d0) ? "Yes" : "No");
    printf("EMAC:                  %s\n", MCF5XXX_D0_EMAC(d0) ? "Yes" : "No");
    printf("FPU:                   %s\n", MCF5XXX_D0_FPU(d0) ? "Yes" : "No");
    printf("MMU:                   %s\n", MCF5XXX_D0_MMU(d0) ? "Yes" : "No");
    printf("RAM Bank 0 Size:       ");
    switch (MCF5XXX_D1_RAM0SIZ(d1))
    {
        case 0:
        case 1:
        case 2:
        case 3:
            printf("None\n");
            break;
        case 4:
            printf("4KB\n");
            break;
        case 5:
            printf("8KB\n");
            break;
        case 6:
            printf("16KB\n");
            break;
        case 7:
            printf("32KB\n");
            break;
        case 8:
            printf("64KB\n");
            break;
        case 9:
            printf("128KB\n");
            break;
        case 10:
            printf("256KB\n");
            break;
        case 11:
            printf("512KB\n");
            break;
        default:
            printf("Reserved\n");
    }
    printf("RAM Bank 1 Size:       ");
    switch (MCF5XXX_D1_RAM1SIZ(d1))
    {
        case 0:
        case 1:
        case 2:
        case 3:
            printf("None\n");
            break;
        case 4:
            printf("4KB\n");
            break;
        case 5:
            printf("8KB\n");
            break;
        case 6:
            printf("16KB\n");
            break;
        case 7:
            printf("32KB\n");
            break;
        case 8:
            printf("64KB\n");
            break;
        case 9:
            printf("128KB\n");
            break;
        case 10:
            printf("256KB\n");
            break;
        case 11:
            printf("512KB\n");
            break;
        default:
            printf("Reserved\n");
    }
    printf("ROM Bank 0 Size:       ");
    switch (MCF5XXX_D1_ROM0SIZ(d1))
    {
        case 0:
        case 1:
        case 2:
        case 3:
            printf("None\n");
            break;
        case 4:
            printf("4KB\n");
            break;
        case 5:
            printf("8KB\n");
            break;
        case 6:
            printf("16KB\n");
            break;
        case 7:
            printf("32KB\n");
            break;
        case 8:
            printf("64KB\n");
            break;
        case 9:
            printf("128KB\n");
        default:
            printf("Reserved\n");
    }
    printf("ROM Bank 1 Size:       ");
    switch (MCF5XXX_D1_ROM1SIZ(d1))
    {
        case 0:
        case 1:
        case 2:
        case 3:
            printf("None\n");
            break;
        case 4:
            printf("4KB\n");
            break;
        case 5:
            printf("8KB\n");
            break;
        case 6:
            printf("16KB\n");
            break;
        case 7:
            printf("32KB\n");
            break;
        case 8:
            printf("64KB\n");
            break;
        case 9:
            printf("128KB\n");
        default:
            printf("Reserved\n");
    }
    printf("Cache Line Size:       ");
    switch (MCF5XXX_D1_CL(d1))
    {
        case 0:
            printf("16-byte\n");
            break;
        default:
            printf("Reserved\n");
    }
    printf("I-Cache Associativity: ");
    switch (MCF5XXX_D1_ICA(d1))
    {
        case 0:
            printf("Four-way\n");
            break;
        case 1:
            printf("Direct mapped\n");
            break;
        default:
            printf("Reserved\n");
    }
    printf("D-Cache Associativity: ");
    switch (MCF5XXX_D1_DCA(d1))
    {
        case 0:
            printf("Four-way\n");
            break;
        case 1:
            printf("Direct mapped\n");
            break;
        default:
            printf("Reserved\n");
    }
    printf("I-Cache Size:          ");
    switch (MCF5XXX_D1_ICSIZ(d1))
    {
        case 0:
            printf("None\n");
            break;
        case 1:
            printf("512B\n");
            break;
        case 2:
            printf("1KB\n"); 
            break;
        case 3:
            printf("2KB\n");
            break;
        case 4:
            printf("4KB\n");
            break;
        case 5:
            printf("8KB\n");
            break;
        case 6:
            printf("16KB\n");
            break;
        case 7:
            printf("32KB\n");
            break;
        case 8:
            printf("64KB\n");
            break;
        default:
            printf("Reserved\n");
    }
    printf("D-Cache Size:          ");
    switch (MCF5XXX_D1_DCSIZ(d1))
    {
        case 0:
            printf("None\n");
            break;
        case 1:
            printf("512B\n");
            break;
        case 2:
            printf("1KB\n");
            break;
        case 3:
            printf("2KB\n");
            break;
        case 4:
            printf("4KB\n");
            break;
        case 5:
            printf("8KB\n");
            break;
        case 6:
            printf("16KB\n");
            break;
        case 7:
            printf("32KB\n");
            break;
        case 8:
            printf("64KB\n");
            break;
        default:
            printf("Reserved\n");
    }
    printf("\n");
#else
	/* Remove compiler warnings. */
	( void ) d0;
	( void ) d1;
#endif
}

/********************************************************************/
void
mcf5xxx_irq_enable (void)
{
    asm_set_ipl(0);
}
/********************************************************************/
void
mcf5xxx_irq_disable (void)
{
    asm_set_ipl(7);
}
/********************************************************************/
/*
 * Write new interrupt vector handler into the vector table
 * Return previous handler address
 */ 

ADDRESS
mcf5xxx_set_handler (int vector, ADDRESS new_handler)
{
    ADDRESS old_handler;
    extern uint32 __VECTOR_RAM[];

    old_handler = (ADDRESS) __VECTOR_RAM[vector];
    __VECTOR_RAM[vector] = (uint32)new_handler;
    return old_handler;
}

/********************************************************************/
