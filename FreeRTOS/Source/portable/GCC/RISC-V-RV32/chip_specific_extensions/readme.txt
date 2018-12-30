/*
 * The FreeRTOS kernel's RISC-V port is split between the the code that is
 * common across all currently supported RISC-V chips (implementations of the
 * RISC-V ISA), and code which tailors the port to a specific RISC-V chip:
 *
 * + FreeRTOS\Source\portable\GCC\RISC-V-RV32\portASM.S contains the code that
 *   is common to all currently supported RISC-V chips.  There is only one
 *   portASM.S file because the same file is built for all RISC-V target chips.
 *
 * + Header files called freertos_risc_v_chip_specific_extensions.h contain the
 *   code that tailors the FreeRTOS kernel's RISC-V port to a specific RISC-V
 *   chip.  There are multiple freertos_risc_v_chip_specific_extensions.h files
 *   as there are multiple RISC-V chip implementations.
 *
 * !!!NOTE!!!
 * CARE MUST BE TAKEN TO INCLUDE THE CORRECT
 * freertos_risc_v_chip_specific_extensions.h HEADER FILE FOR THE CHIP IN USE.
 * If the chip in use includes a core local interrupter (CLINT) and does not
 * include any chip specific register extensions then set the GNU assembler's
 * include path such that the header file contained in the
 * FreeRTOS\Source\portable\GCC\RISC-V-RV32 directory is the header file that is
 * actually inlcuded.  Otherwise set the assembler's include patch to the
 * sub-directory off of the
 * FreeRTOS\Source\portable\GCC\RISC-V-RV32\chip_specific_extensions directory
 * that contains the freertos_risc_v_chip_specific_extensions.h specific to the
 * target chip.
 *
 */
