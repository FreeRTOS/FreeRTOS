#ifndef CGC_ERROR_H_
#define CGC_ERROR_H_

/* Error checking macros for the clock selction and clock enable defines */

#if ( (CLK_SOURCE != CLK_SOURCE_LOCO) && \
      (CLK_SOURCE != CLK_SOURCE_HOCO) && \
      (CLK_SOURCE != CLK_SOURCE_MAIN) && \
      (CLK_SOURCE != CLK_SOURCE_SUB)  && \
      (CLK_SOURCE != CLK_SOURCE_PLL) )
      #error "No CLK_SOURCE specified. Please specify a valid CLK_SOURCE";
#endif
      

#if (CLK_SOURCE == CLK_SOURCE_HOCO) && (ENABLE_HOCO == 0)
    #error "HOCO has been specified as the CLK_SOURCE but ENABLE_HOCO is (0). Please set to (1) in file cgc.h"
#endif

#if (CLK_SOURCE == CLK_SOURCE_MAIN) && (ENABLE_MAIN == 0)
    #error "HOCO has been specified as the CLK_SOURCE but ENABLE_HOCO is (0). Please set to (1) in file cgc.h"
#endif

#if (CLK_SOURCE == CLK_SOURCE_SUB) && (ENABLE_SUB == 0)
    #error "HOCO has been specified as the CLK_SOURCE but ENABLE_HOCO is (0). Please set to (1) in file cgc.h"
#endif

#if (CLK_SOURCE == CLK_SOURCE_PLL) && (ENABLE_PLL == 0)
    #error "PLL has been specified as the CLK_SOURCE but ENABLE_PLL is (0). Please set to (1) in file cgc.h"
#endif

#if ( FCLK_FREQUENCY > 50000000L )
    #error "FCLK_FREQUENCY Error: Please enter a valid divider value"
#endif

#if ( ICLK_FREQUENCY > 100000000L )
    #error "ICLK_FREQUENCY Error: Please enter a valid divider value"
#endif

#if ( BCLK_FREQUENCY > 100000000L )
    #error "BCLK_FREQUENCY Error: Please enter a valid divider value"
#endif
    
#if ( PCLKB_FREQUENCY > 50000000L )  
    #error "PCLKB_FREQUENCY Error: Please enter a valid divider value"
#endif
    
#endif