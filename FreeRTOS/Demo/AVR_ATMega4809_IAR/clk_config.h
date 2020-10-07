#ifndef CLK_CONFIG_H_
#define CLK_CONFIG_H_

#include "FreeRTOSConfig.h"
#include "protected_io/ccp.h"

#if ( configCPU_CLOCK_HZ == 20000000 )

    #define CLK_init()  { \
                        _PROTECTED_WRITE(CLKCTRL.MCLKCTRLA, CLKCTRL_CLKSEL_OSC20M_gc); \
                        _PROTECTED_WRITE(CLKCTRL.MCLKCTRLB, 0); \
                        }

#elif ( configCPU_CLOCK_HZ == 10000000 )

    #define CLK_init()  { \
                        ccp_write_io((void *)&(CLKCTRL.MCLKCTRLA), CLKCTRL_CLKSEL_OSC20M_gc); \
                        ccp_write_io((void *)&(CLKCTRL.MCLKCTRLB), CLKCTRL_PDIV_2X_gc | CLKCTRL_PEN_bm); \
                        }

#elif ( configCPU_CLOCK_HZ == 5000000 )

    #define CLK_init()  { \
                        ccp_write_io((void *)&(CLKCTRL.MCLKCTRLA), CLKCTRL_CLKSEL_OSC20M_gc); \
                        ccp_write_io((void *)&(CLKCTRL.MCLKCTRLB), CLKCTRL_PDIV_4X_gc | CLKCTRL_PEN_bm); \
                        }

#elif ( configCPU_CLOCK_HZ == 2000000 )

    #define CLK_init()  { \
                        ccp_write_io((void *)&(CLKCTRL.MCLKCTRLA), CLKCTRL_CLKSEL_OSC20M_gc); \
                        ccp_write_io((void *)&(CLKCTRL.MCLKCTRLB), CLKCTRL_PDIV_10X_gc | CLKCTRL_PEN_bm); \
                        }

#else

    #error The selected clock frequency is not supported. Choose a value from the NOTE in FreeRTOSConfig.h.

#endif

#endif /* CLK_CONFIG_H_ */