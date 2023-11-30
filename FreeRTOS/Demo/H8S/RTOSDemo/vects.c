/****************************************************************
KPIT Cummins Infosystems Ltd, Pune, India. - 19-June-2003.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
*****************************************************************/

void start(void); /* Startup code (in start.asm)  */

/*
 * Manual context switch trap function.
 */
void vPortYield( void );

/*
 * The RTOS tick ISR.
 */
void vTickISR( void );

/* 
 * Serial port ISR functions.
 */
void vCOM_1_Rx_ISR( void );
void vCOM_1_Tx_ISR( void );
void vCOM_1_Error_ISR( void );


typedef void (*fp) (void);
#define VECT_SECT          __attribute__ ((section (".vects")))

const fp HardwareVectors[] VECT_SECT = {
start,		/*  vector 0 */
(fp)(0),	/*  vector 1 */
(fp)(0),	/*  vector 2 */
(fp)(0),	/*  vector 3 */
(fp)(0),	/*  vector 4 */
(fp)(0),	/*  vector 5 */
(fp)(0),	/*  vector 6 */
(fp)(0),	/*  vector 7 */
vPortYield,	/*  vector 8 */
(fp)(0),	/*  vector 9 */
(fp)(0),	/*  vector 10 */
(fp)(0),	/*  vector 11 */
(fp)(0),	/*  vector 12 */
(fp)(0),	/*  vector 13 */
(fp)(0),	/*  vector 14 */
(fp)(0),	/*  vector 15 */
(fp)(0),	/*  vector 16 */
(fp)(0),	/*  vector 17 */
(fp)(0),	/*  vector 18 */
(fp)(0),	/*  vector 19 */
(fp)(0),	/*  vector 20 */
(fp)(0),	/*  vector 21 */
(fp)(0),	/*  vector 22 */
(fp)(0),	/*  vector 23 */
(fp)(0),	/*  vector 24 */
(fp)(0),	/*  vector 25 */
(fp)(0),	/*  vector 26 */
(fp)(0),	/*  vector 27 */
(fp)(0),	/*  vector 28 */
(fp)(0),	/*  vector 29 */
(fp)(0),	/*  vector 30 */
(fp)(0),	/*  vector 31 */
(fp)(0),	/*  vector 32 */
(fp)(0),	/*  vector 33 */
(fp)(0),	/*  vector 34 */
(fp)(0),	/*  vector 35 */
(fp)(0),	/*  vector 36 */
(fp)(0),	/*  vector 37 */
(fp)(0),	/*  vector 38 */
(fp)(0),	/*  vector 39 */
vTickISR,	/*  vector 40 */
(fp)(0),	/*  vector 41 */
(fp)(0),	/*  vector 42 */
(fp)(0),	/*  vector 43 */
(fp)(0),	/*  vector 44 */
(fp)(0),	/*  vector 45 */
(fp)(0),	/*  vector 46 */
(fp)(0),	/*  vector 47 */
(fp)(0),	/*  vector 48 */
(fp)(0),	/*  vector 49 */
(fp)(0),	/*  vector 50 */
(fp)(0),	/*  vector 51 */
(fp)(0),	/*  vector 52 */
(fp)(0),	/*  vector 53 */
(fp)(0),	/*  vector 54 */
(fp)(0),	/*  vector 55 */
(fp)(0),	/*  vector 56 */
(fp)(0),	/*  vector 57 */
(fp)(0),	/*  vector 58 */
(fp)(0),	/*  vector 59 */
(fp)(0),	/*  vector 60 */
(fp)(0),	/*  vector 61 */
(fp)(0),	/*  vector 62 */
(fp)(0),	/*  vector 63 */
(fp)(0),	/*  vector 64 */
(fp)(0),	/*  vector 65 */
(fp)(0),	/*  vector 66 */
(fp)(0),	/*  vector 67 */
(fp)(0),	/*  vector 68 */
(fp)(0),	/*  vector 69 */
(fp)(0),	/*  vector 70 */
(fp)(0),	/*  vector 71 */
(fp)(0),	/*  vector 72 */
(fp)(0),	/*  vector 73 */
(fp)(0),	/*  vector 74 */
(fp)(0),	/*  vector 75 */
(fp)(0),	/*  vector 76 */
(fp)(0),	/*  vector 77 */
(fp)(0),	/*  vector 78 */
(fp)(0),	/*  vector 79 */
(fp)(0),	/*  vector 80 */
(fp)(0),	/*  vector 81 */
(fp)(0),	/*  vector 82 */
(fp)(0),	/*  vector 83 */
vCOM_1_Error_ISR,	/*  vector 84 */
vCOM_1_Rx_ISR,		/*  vector 85 */
vCOM_1_Tx_ISR,		/*  vector 86 */
(fp)(0),	/*  vector 87 */
(fp)(0),	/*  vector 88 */
(fp)(0),	/*  vector 89 */
(fp)(0),	/*  vector 90 */
(fp)(0),	/*  vector 91 */
(fp)(0),	/*  vector 92 */
(fp)(0),	/*  vector 93 */
(fp)(0),	/*  vector 94 */
(fp)(0),	/*  vector 95 */
(fp)(0),	/*  vector 96 */
(fp)(0),	/*  vector 97 */
(fp)(0),	/*  vector 98 */
(fp)(0),	/*  vector 99 */
(fp)(0),	/*  vector 100 */
(fp)(0),	/*  vector 101 */
(fp)(0),	/*  vector 102 */
(fp)(0)		/*  vector 103 */
};
