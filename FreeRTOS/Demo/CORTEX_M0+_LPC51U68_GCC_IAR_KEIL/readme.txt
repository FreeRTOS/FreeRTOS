This directory contains three projects for LPCXpresso board for LPC51U68. 

MCUXpresso IDE (GCC compiler) -- .cproject and .project. 
IAR for ARM IDE (IAR compiler) -- CORTEX_M0+_LPC51U68_IAR.*
Keil uVision (ARM Keil compiler) -- CORTEX_M0+_LPC51U68_Keil.*

Known facts:
- IAR compiler shows Pa082 warning with SDK provided system_LPC51U68.c and fsl_usart.c. Since the warnings are legitimate, they are not ignored. 
  Refer to https://www.iar.com/support/tech-notes/compiler/warningpa082-undefined-behavior-the-order-of-volatile-accesses-is-undefined-in-this-statement/
