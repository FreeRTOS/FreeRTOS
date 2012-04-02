#ifndef CGC_SET_VALUES_H_
#define CGC_SET_VALUES_H_

/* Do not modify these macros.  These values are used to initialise  
   the SCKCR and SCKCR2 registers based upon the above values.      */
#if   (FCLK_DIV == 64)
    #define FCLK_SCKCR  0x60000000L
#elif (FCLK_DIV == 32)
    #define FCLK_SCKCR  0x50000000L
#elif (FCLK_DIV == 16)
    #define FCLK_SCKCR  0x40000000L
#elif (FCLK_DIV ==  8)
    #define FCLK_SCKCR  0x30000000L
#elif (FCLK_DIV ==  4)
    #define FCLK_SCKCR  0x20000000L
#elif (FCLK_DIV ==  2)
    #define FCLK_SCKCR  0x10000000L
#elif(FCLK_DIV == 1)
    #define FCLK_SCKCR  0x00000000L
#else
    #define FCLK_SCKCR  0x10000000L
#endif


#if   (ICLK_DIV == 64)
    #define ICLK_SCKCR  0x06000000L
#elif (ICLK_DIV == 32)
    #define ICLK_SCKCR  0x05000000L
#elif (ICLK_DIV == 16)
    #define ICLK_SCKCR  0x04000000L
#elif (ICLK_DIV ==  8)
    #define ICLK_SCKCR  0x03000000L
#elif (ICLK_DIV ==  4)
    #define ICLK_SCKCR  0x02000000L
#elif (ICLK_DIV ==  2)
    #define ICLK_SCKCR  0x01000000L
#elif (ICLK_DIV == 1)
    #define ICLK_SCKCR  0x00000000L
#else
    #define ICLK_SCKCR  0x01000000L
#endif

    
#if (BCLK_PIN == 1)
    #define PSTOP1_SCKCR 0x00800000L
#elif    
    #define PSTOP1_SCKCR 0x00000000L
#endif    


#if   (BCLK_DIV == 64)
    #define BCLK_SCKCR  0x00060000L
#elif (BCLK_DIV == 32)
    #define BCLK_SCKCR  0x00050000L
#elif (BCLK_DIV == 16)
    #define BCLK_SCKCR  0x00040000L
#elif (BCLK_DIV ==  8)
    #define BCLK_SCKCR  0x00030000L
#elif (BCLK_DIV ==  4)
    #define BCLK_SCKCR  0x00020000L
#elif (BCLK_DIV ==  2)
    #define BCLK_SCKCR  0x00010000L
#elif (BCLK_DIV == 1)
    #define BCLK_SCKCR  0x00000000L
#else
    #define BCLK_SCKCR  0x00010000L
#endif


#if   (PCLK1215_DIV == 64)
    #define PCLK1215_SCKCR  0x00006000L
#elif (PCLK1215_DIV == 32)
    #define PCLK1215_SCKCR  0x00005000L
#elif (PCLK1215_DIV == 16)
    #define PCLK1215_SCKCR  0x00004000L
#elif (PCLK1215_DIV ==  8)
    #define PCLK1215_SCKCR  0x00003000L
#elif (PCLK1215_DIV ==  4)
    #define PCLK1215_SCKCR  0x00002000L
#elif (PCLK1215_DIV ==  2)
    #define PCLK1215_SCKCR  0x00001000L
#elif (PCLK1215_DIV ==  1)
    #define PCLK1215_SCKCR  0x00000000L
#else
    #define PCLK1215_SCKCR  0x00001000L
#endif


#if   (PCLKB_DIV == 64)
    #define PCLKB_SCKCR  0x00000600L
#elif (PCLKB_DIV == 32)
    #define PCLKB_SCKCR  0x00000500L
#elif (PCLKB_DIV == 16)
    #define PCLKB_SCKCR  0x00000400L
#elif (PCLKB_DIV ==  8)
    #define PCLKB_SCKCR  0x00000300L
#elif (PCLKB_DIV ==  4)
    #define PCLKB_SCKCR  0x00000200L
#elif (PCLKB_DIV ==  2)
    #define PCLKB_SCKCR  0x00000100L
#elif (PCLKB_DIV ==  1)
    #define PCLKB_SCKCR  0x00000000L
#else
    #define PCLKB_SCKCR  0x00000100L
#endif


#if   (PCLK47_DIV == 64)
    #define PCLK47_SCKCR  0x00000060L
#elif (PCLK47_DIV == 32)
    #define PCLK47_SCKCR  0x00000050L
#elif (PCLK47_DIV == 16)
    #define PCLK47_SCKCR  0x00000040L
#elif (PCLK47_DIV ==  8)
    #define PCLK47_SCKCR  0x00000030L
#elif (PCLK47_DIV ==  4)
    #define PCLK47_SCKCR  0x00000020L
#elif (PCLK47_DIV ==  2)
    #define PCLK47_SCKCR  0x00000010L
#elif (PCLK47_DIV ==  1)
    #define PCLK47_SCKCR  0x00000000L
#else
    #define PCLK47_SCKCR  0x00000010L    
#endif


#if   (PCLK03_DIV == 64)
    #define PCLK03_SCKCR  0x00000006L
#elif (PCLK03_DIV == 32)
    #define PCLK03_SCKCR  0x00000005L
#elif (PCLK03_DIV == 16)
    #define PCLK03_SCKCR  0x00000004L
#elif (PCLK03_DIV ==  8)
    #define PCLK03_SCKCR  0x00000003L
#elif (PCLK03_DIV ==  4)
    #define PCLK03_SCKCR  0x00000002L
#elif (PCLK03_DIV ==  2)
    #define PCLK03_SCKCR  0x00000001L
#elif (PCLK03_DIV ==  1)
    #define PCLK03_SCKCR  0x00000000L
#else
    #define PCLK03_SCKCR  0x00000001L    
#endif


#if (UCK_DIV == 6)
    #define UCK_SCKCR2  0x00C0L
#elif   (UCK_DIV == 64)
    #define UCK_SCKCR2  0x0060L
#elif (UCK_DIV == 32)
    #define UCK_SCKCR2  0x0050L
#elif (UCK_DIV == 16)
    #define UCK_SCKCR2  0x0040L
#elif (UCK_DIV ==  8)
    #define UCK_SCKCR2  0x0030L
#elif (UCK_DIV ==  4)
    #define UCK_SCKCR2  0x0020L
#elif (UCK_DIV ==  2)
    #define UCK_SCKCR2  0x0010L
#else
    #define UCK_SCKCR2  0x0010L
#endif


#if   (IEBCK_DIV == 3)
    #define IEBCK_SCKCR2  0x00000020L
#elif (IEBCK_DIV == 4)
    #define IEBCK_SCKCR2  0x00000030L
#else
    #define IEBCK_SCKCR2  0x00000030L
#endif


#if (CLK_SOURCE == CLK_SOURCE_LOCO)
/* Internal LOCO circuit - 125kHz*/
#define     CLK_FREQUENCY       (125000L)	
#define     FCLK_FREQUENCY      (CLK_FREQUENCY / FCLK_DIV)
#define     ICLK_FREQUENCY      (CLK_FREQUENCY / ICLK_DIV)
#define     BCLK_FREQUENCY      (CLK_FREQUENCY / BCLK_DIV)
#define     PCLKA_FREQUENCY     (CLK_FREQUENCY / PCLK1215_DIV)
#define     PCLKB_FREQUENCY     (CLK_FREQUENCY / PCLKB_DIV)
#define     PCLK47_FREQUENCY    (CLK_FREQUENCY / PCLK47_DIV)
#define     PCLK03_FREQUENCY    (CLK_FREQUENCY / PCLK03_DIV)


#elif (CLK_SOURCE == CLK_SOURCE_HOCO)
/* Internal high speed on-chip oscillator (HOCO) */
#define     CLK_FREQUENCY       (50000000L)	
#define     FCLK_FREQUENCY      (CLK_FREQUENCY / FCLK_DIV)
#define     ICLK_FREQUENCY      (CLK_FREQUENCY / ICLK_DIV)
#define     BCLK_FREQUENCY      (CLK_FREQUENCY / BCLK_DIV)
#define     PCLKA_FREQUENCY     (CLK_FREQUENCY / PCLK1215_DIV)
#define     PCLKB_FREQUENCY     (CLK_FREQUENCY / PCLKB_DIV)
#define     PCLK47_FREQUENCY    (CLK_FREQUENCY / PCLK47_DIV)
#define     PCLK03_FREQUENCY    (CLK_FREQUENCY / PCLK03_DIV)


#elif (CLK_SOURCE == CLK_SOURCE_MAIN)
/* External XTAL, but not via the PLL circuit */	
#define     FCLK_FREQUENCY      (XTAL_FREQUENCY / FCLK_DIV)
#define     ICLK_FREQUENCY      (XTAL_FREQUENCY / ICLK_DIV)
#define     BCLK_FREQUENCY      (XTAL_FREQUENCY / BCLK_DIV)
#define     PCLKA_FREQUENCY     (XTAL_FREQUENCY / PCLK1215_DIV)
#define     PCLKB_FREQUENCY     (XTAL_FREQUENCY / PCLKB_DIV)
#define     PCLK47_FREQUENCY    (XTAL_FREQUENCY / PCLK47_DIV)
#define     PCLK03_FREQUENCY    (XTAL_FREQUENCY / PCLK03_DIV)


#elif (CLK_SOURCE == CLK_SOURCE_SUB)
/* External 32khZ XTAL */	
#define     FCLK_FREQUENCY      (SUB_FREQUENCY / FCLK_DIV)
#define     ICLK_FREQUENCY      (SUB_FREQUENCY / ICLK_DIV)
#define     BCLK_FREQUENCY      (SUB_FREQUENCY / BCLK_DIV)
#define     PCLKA_FREQUENCY     (SUB_FREQUENCY / PCLK1215_DIV)
#define     PCLKB_FREQUENCY     (SUB_FREQUENCY / PCLKB_DIV)
#define     PCLK47_FREQUENCY    (SUB_FREQUENCY / PCLK47_DIV)
#define     PCLK03_FREQUENCY    (SUB_FREQUENCY / PCLK03_DIV)


#elif (CLK_SOURCE == CLK_SOURCE_PLL)
/* External XTAL, but using the PLL circuit */
#define     PLL_FREQUENCY       (XTAL_FREQUENCY * (PLL_MUL / PLL_INPUT_FREQ_DIV))	
#define     FCLK_FREQUENCY      (PLL_FREQUENCY / FCLK_DIV)
#define     ICLK_FREQUENCY      (PLL_FREQUENCY / ICLK_DIV)
#define     BCLK_FREQUENCY      (PLL_FREQUENCY / BCLK_DIV)
#define     PCLKA_FREQUENCY     (PLL_FREQUENCY / PCLK1215_DIV)
#define     PCLKB_FREQUENCY     (PLL_FREQUENCY / PCLKB_DIV)
#define     PCLK47_FREQUENCY    (PLL_FREQUENCY / PCLK47_DIV)
#define     PCLK03_FREQUENCY    (PLL_FREQUENCY / PCLK03_DIV)

#endif

#endif