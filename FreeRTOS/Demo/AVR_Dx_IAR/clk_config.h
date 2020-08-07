#ifndef CLK_CONFIG_H_
#define CLK_CONFIG_H_

#include "FreeRTOSConfig.h"
#include "protected_io/ccp.h"

#if ( configCPU_CLOCK_HZ == 24000000 )

    #define CLK_init()  ccp_write_io((void *)&(CLKCTRL.OSCHFCTRLA), CLKCTRL_FREQSEL_24M_gc);

#elif ( configCPU_CLOCK_HZ == 20000000 )

    #define CLK_init()  ccp_write_io((void *)&(CLKCTRL.OSCHFCTRLA), CLKCTRL_FREQSEL_20M_gc);

#elif ( configCPU_CLOCK_HZ == 16000000 )

    #define CLK_init()  ccp_write_io((void *)&(CLKCTRL.OSCHFCTRLA), CLKCTRL_FREQSEL_16M_gc);

#elif ( configCPU_CLOCK_HZ == 12000000 )

    #define CLK_init()  ccp_write_io((void *)&(CLKCTRL.OSCHFCTRLA), CLKCTRL_FREQSEL_12M_gc);

#elif ( configCPU_CLOCK_HZ == 10000000 )

    #define CLK_init()  { \
                        ccp_write_io((void *)&(CLKCTRL.OSCHFCTRLA), CLKCTRL_FREQSEL_20M_gc); \
                        ccp_write_io((void *)&(CLKCTRL.MCLKCTRLB), CLKCTRL_PDIV_2X_gc | CLKCTRL_PEN_bm); \
                        }

#elif ( configCPU_CLOCK_HZ == 8000000 )

    #define CLK_init()  ccp_write_io((void *)&(CLKCTRL.OSCHFCTRLA), CLKCTRL_FREQSEL_8M_gc);

#elif ( configCPU_CLOCK_HZ == 6000000 )

    #define CLK_init()  { \
                        ccp_write_io((void *)&(CLKCTRL.OSCHFCTRLA), CLKCTRL_FREQSEL_12M_gc); \
                        ccp_write_io((void *)&(CLKCTRL.MCLKCTRLB), CLKCTRL_PDIV_2X_gc | CLKCTRL_PEN_bm); \
                        }

#elif ( configCPU_CLOCK_HZ == 5000000 )

    #define CLK_init()  { \
                        ccp_write_io((void *)&(CLKCTRL.OSCHFCTRLA), CLKCTRL_FREQSEL_20M_gc); \
                        ccp_write_io((void *)&(CLKCTRL.MCLKCTRLB), CLKCTRL_PDIV_4X_gc | CLKCTRL_PEN_bm); \
                        }

#elif ( configCPU_CLOCK_HZ == 4000000 )

    #define CLK_init()  ccp_write_io((void *)&(CLKCTRL.OSCHFCTRLA), CLKCTRL_FREQSEL_4M_gc);

#elif ( configCPU_CLOCK_HZ == 3000000 )

    #define CLK_init()  { \
                        ccp_write_io((void *)&(CLKCTRL.OSCHFCTRLA), CLKCTRL_FREQSEL_12M_gc); \
                        ccp_write_io((void *)&(CLKCTRL.MCLKCTRLB), CLKCTRL_PDIV_4X_gc | CLKCTRL_PEN_bm); \
                        }

#elif ( configCPU_CLOCK_HZ == 2000000 )

    #define CLK_init()  ccp_write_io((void *)&(CLKCTRL.OSCHFCTRLA), CLKCTRL_FREQSEL_2M_gc);

#elif ( configCPU_CLOCK_HZ == 1000000 )

    #define CLK_init()  ccp_write_io((void *)&(CLKCTRL.OSCHFCTRLA), CLKCTRL_FREQSEL_1M_gc);

#else

    #error The selected clock frequency is not supported. Choose a value from the NOTE in FreeRTOSConfig.h.

#endif

#endif /* CLK_CONFIG_H_ */