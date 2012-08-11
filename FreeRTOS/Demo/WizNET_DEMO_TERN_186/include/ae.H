#ifndef _AE_H_
#define _AE_H_

/*********************************************************************
	ae.h	 	headers for AM188ES   6-20-99   7-16-98             
*********************************************************************/
/*  Data structure for Serial operation */

typedef struct  {
	unsigned char ready;          /* TRUE when ready */
	unsigned char baud;
	unsigned int mode;              
	unsigned char iflag;     /* interrupt status     */
	unsigned char* in_buf;        /* Input buffer */
	unsigned int in_tail;        /* Input buffer TAIL ptr */
	unsigned int in_head;        /* Input buffer HEAD ptr */
	unsigned int in_size;        /* Input buffer size */
	unsigned int in_crcnt;       /* Input <CR> count */
	unsigned char in_mt;          /* Input buffer FLAG */
	unsigned char in_full;        /* input buffer full */
	unsigned char* out_buf;       /* Output buffer */
	unsigned int out_tail;       /* Output buffer TAIL ptr */
	unsigned int out_head;       /* Output buffer HEAD ptr */
	unsigned int out_size;       /* Output buffer size */
	unsigned char out_full;       /* Output buffer FLAG */
	unsigned char out_mt;         /* Output buffer MT */
	unsigned char tmso;	// transmit macro service operation
	unsigned char rts;
	unsigned char dtr;
	unsigned char en485;
	unsigned char err;
	unsigned char node;
	unsigned char cr; /* scc CR register    */
	unsigned char slave;
	unsigned int in_segm;       /* input buffer segment */
	unsigned int in_offs;       /* input buffer offset */
	unsigned int out_segm;       /* output buffer segment */
	unsigned int out_offs;       /* output buffer offset */
	unsigned char byte_delay;	/* V25 macro service byte delay */
} COM;


typedef struct{
	unsigned char sec1;
	unsigned char sec10;
	unsigned char min1;
	unsigned char min10;
	unsigned char hour1;
	unsigned char hour10;
	unsigned char day1;
	unsigned char day10;
	unsigned char mon1;
	unsigned char mon10;
	unsigned char year1;
	unsigned char year10; 
	unsigned char wk;
} TIM;

void ae_init(void);
void ae_reset(void);
void led(int i);      //P12 used for led
void delay_ms(int m);
void delay0(unsigned int t);
void	HLPRsetvect(
				unsigned int	wVec,		/* Interrupt vector number */
				void	far		*ih		/* Interrupt handler to install */
			);

void clka_en(int i);
void clkb_en(int i);
void pwr_save_en(int i);
void hitwd(void);

//
//	reset ee to remain enabled for reads
//	where s = segment register value pointing to ee starting addr.
//		for example = 0x8000
//
void amd_ee_read_reset(unsigned int s);

//
//	sec=0x00-0x07 for AM29F010, 16K/sector
//		sec=0	0x00000-0x03fff
//		sec=1	0x04000-0x07fff
//		sec=2	0x08000-0x0bfff
//		sec=3	0x0c000-0x0ffff
//		sec=4	0x10000-0x13fff
//		sec=5	0x14000-0x17fff
//		sec=6	0x18000-0x1bfff
//		sec=7	0x1c000-0x1ffff
//
//	sec=0x10-0x17 for AM29F040
//		sec=10	0x00000-0x0ffff
//		sec=11	0x10000-0x1ffff
//		sec=12	0x20000-0x2ffff
//		sec=13	0x30000-0x3ffff
//		sec=14	0x40000-0x4ffff
//		sec=15	0x50000-0x5ffff
//		sec=16	0x60000-0x6ffff
//		sec=17	0x70000-0x7ffff
//	segm=segment register value pointing to ee address 0
// returns:		if pass, return(0);
// 				if fail, return(1);
//
int amd_ee_sec_erase(unsigned int segm, unsigned char sec );

//
//	write one byte dat to AM29F040, at address of s:o
//	Approximately 70 us for 0 wait, 80us for 1 wait.
//		where s=segment register, it is fixed to 0x8000
//				o=offset register
// returns:		if pass, return(0);
// 				if fail, return(1);
//
// Be aware of that a data bit "0" can not be programmed back to a "1" !!!
// Attempting to do so will hang up the system !!!
// you can program the "1"s to "0"s.
// Only erase operation can convert "0"s to "1"s
//
//

int amd_ee_byte_pro_512(unsigned int s, unsigned int o, unsigned char dat);

//
//	write one byte dat to AM29F010, at address of s:o, 80us per byte approx.
//		where s=segment register, you may use s=0x8000-0xe000
//				o=offset register
// returns:		if pass, return(0);
// 				if fail, return(1);
//
// Be aware of that a data bit "0" can not be programmed back to a "1" !!!
// Attempting to do so will hang up the system !!!
// you can program the "1"s to "0"s.
// Only erase operation can convert "0"s to "1"s
//

int amd_ee_byte_pro_128(unsigned int s, unsigned int o, unsigned char dat);

//
// unsigned char rtc_rds(char* time_string); 
// put a time string into time_string, based on the reading of RTC.
//	At least 15 bytes of buffer must be available for the time_string
//	returns 0, if RTC OK, or returns 1, if problem
//
unsigned char rtc_rds(char* time_string); 
int rtc_rd(TIM *r);
void rtc_init(unsigned char*);    
unsigned char r_rd(void);
int r_out(unsigned char v);


void t2_init(unsigned int tm,unsigned int ta,void interrupt far(*t2_isr)());
void t1_init(unsigned int tm,unsigned int ta,unsigned int tb,void interrupt far(*t1_isr)());
void t0_init(unsigned int tm,unsigned int ta,unsigned int tb,void interrupt far(*t0_isr)());
unsigned int t2_rd(void);
unsigned int t1_rd(void);
unsigned int t0_rd(void);

//	Analog to Digital conversion using TLC2543 on the A-Engine-88/86
//	Input:
//		unsigned char c = input channel 
//		c = 0,	input ch = AD0
//		c = 1,	input ch = AD1
//		c = 2,	input ch = AD2
//		c = 3,	input ch = AD3
//		c = 4,	input ch = AD4
//		c = 5,	input ch = AD5
//		c = 6,	input ch = AD6
//		c = 7,	input ch = AD7
//		c = 8,	input ch = AD8
//		c = 9,	input ch = AD9
//		c = a,	input ch = AD10
//	In order to operate ADC, P11 must be input.
//	P11 is shared by RTC, EE. It must be high while power on/reset
//	For AE88, using PPI for ADC, I20,I21,I22 must be output
//	For AE86, using PAL for ADC, T0=CLK, T1=DIN, T2=ADCS
//		Enter the ae_ad12(unsigned char c);  EE is stopped first.
//		Enter the ae86_ad12(unsigned char c);  EE is stopped first.
//
//	Output: 12 bit AD data of the previous channel !
//		Unipolar:
//		(Vref+ - Vref-)=0x7ff
//		Vref- = 0x000
//		Vref+ = 0xfff
//
//
int ae_ad12(unsigned char c);

//	outportb(0x120,1);  // T0=0, CLK
//	outportb(0x128,1);  // T1=0, DIN
//	outportb(0x130,1);  // T2=0, ADCS
int ae86_ad12(unsigned char c);

void nmi_init(void interrupt far (* nmi_isr)());
void int0_init(unsigned char i, void interrupt far (*int0_isr)());
void int1_init(unsigned char i, void interrupt far (*int1_isr)());
void int2_init(unsigned char i, void interrupt far (*int2_isr)());
void int3_init(unsigned char i, void interrupt far (*int3_isr)());
void int4_init(unsigned char i, void interrupt far (*int4_isr)());
void int5_init(unsigned char i, void interrupt far (*int5_isr)());
void int6_init(unsigned char i, void interrupt far (*int6_isr)());


//
// void pio_init(char bit, char mode)
//	where bit=0-31
//			mode=0, Normal operation
//			mode=1, Input with pullup/down
//			mode=2, Output
//			mode=3, input without pull
//
void pio_init(char bit, char mode);


//
//	void pio_wr(char bit, char dat)
//	where bit=0-31
//		dat=0/1
//
void pio_wr(char bit, char dat);

//
// unsigned int pio_rd(char port)
//	return P15-P0, if port=0
//	return P31-P16, if port=1
//
unsigned int pio_rd(char port);

// setup I/O wait states for I/O instructions
//	where wait = 0-7
//	wait=0,			wait states = 0, I/O enable for 100 ns
//	wait=1,			wait states = 1, I/O enable for 100+25 ns
//	wait=2,			wait states = 2, I/O enable for 100+50 ns
//	wait=3,			wait states = 3, I/O enable for 100+75 ns
//	wait=4,			wait states = 5, I/O enable for 100+125 ns
//	wait=5,			wait states = 7, I/O enable for 100+175 ns
//	wait=6,			wait states = 9, I/O enable for 100+225 ns
//	wait=7,			wait states = 15, I/O enable for 100+375 ns
void io_wait(char wait);

unsigned int crc16(unsigned char *wptr, unsigned int count);

/******************************************************
	void ae_da(int dat1, int dat2)
	output dat to U11 DAC of AE88
	Requires P12=CLK, P26=DI, P29=LD/CS as output pins !
	where dat1 for channel A, dat2 for channel B;	dat1/2 = 0-4095
*******************************************************/
void ae_da(int dat1, int dat2);

/******************************************************
	void ae86_da(int dat1, int dat2)
	output dat to U15 DAC of AE86
	Requires T0=CLK=0x120, T1=DI=0x128, T3=LD/CS=0x138
	where dat1 for channel A, dat2 for channel B;	dat1/2 = 0-4095
	Output 0-2.5V at VA=J4.16, VB=J4.18
*******************************************************/
void ae86_da(int dat1, int dat2);
void interrupt reset_io_trap();

#endif


