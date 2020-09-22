#ifndef FIT_PATCH_H
#define FIT_PATCH_H

/* Workaround for the stand alone RX SmartConfigurator's missing support of FreeRTOS project.
 */
#define BSP_CFG_RTOS_USED (1)

/* Workaround for warning messages caused by undefined preprocessing identifier.
 */
#define SCI_CFG_DATA_MATCH_INCLUDED (0)
#define SCI_CFG_FIFO_INCLUDED (0)

/* Workaround for warning messages caused by missing 'void' argument prototype.
 */
void R_SCI_PinSet_SCI2(void);
void R_SCI_PinSet_SCI9(void);

#if defined(__ICCRX__)

/* Workaround to reduce the following remark messages caused in the r_rx_compiler.h.
 *
 *   #define R_BSP_ASM(...)            _R_BSP_ASM(__VA_ARGS__\n)
 *                                                           ^
 * "XXX\r_rx_compiler.h",NNN  Remark[Pe007]: unrecognized token
 *
 * Turn off the remark messages temporarily.
 */
#pragma diag_suppress = Pe007

#endif /* defined(__ICCRX__) */

#endif /* FIT_PATCH_H */
