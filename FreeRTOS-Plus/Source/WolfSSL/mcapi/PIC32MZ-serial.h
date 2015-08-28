void _mon_putc(char c);

static void init_serial() {
    #ifdef MICROCHIP_PIC32
#if defined (__32MZ2048ECH144__) || (__32MZ2048ECM144__)
    /* Set up PB2 divisor for UART2 */
    SYSKEY = 0x00000000;
    SYSKEY = 0xAA996655;
    SYSKEY = 0x556699AA;
    PB2DIV = 0x00008018;
    SYSKEY = 0x33333333;
 
    /* UART2 Init */
//    U2BRG = 0x0C;
    U2BRG = 0x7;
    ANSELBCLR = 0x4000;
    ANSELGCLR = 0x0040;
    RPB14R = 0x02;
    U2RXR = 0x01;
    U2MODE = 0x8000;
    U2STA = 0x400;
#elif defined __PIC32MX__
    SYSTEMConfigPerformance(80000000);
    DBINIT();
#endif
 
#endif
}
