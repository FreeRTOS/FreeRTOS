/* Workaround to make CC-RX linker optimization working better.
 *
 * Please refer to the following thread to understand the details of this workaround.
 * (Please note that the original title and all contents are in Japanese.)
 *
 * CC-RX's optimization which removes unused variables/functions is far weaker than GNURX/ICCRX
 * http://japan.renesasrulz.com/cafe_rene/f/forum21/6403/cc-rx-gnurx-iccrx/
 *
 * In conclusion of the thread, the entry function specified by such as '#pragma entry'
 * should be placed at the lowest address among all program codes. Therefore, two things
 * are necessary. One is that the entry function should be placed in a special section
 * by such as '#pragma section'. The other is that the special section should be placed
 * at the lowest address among all program codes by such as linker command line option.
 */
#if defined(__CCRX__)
#pragma section P PResetPRG
#endif /* defined(__CCRX__) */
#include "../../smc_gen/r_bsp/mcu/all/resetprg.c"
