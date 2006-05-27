/*
********************************************************************************
* TERN, Inc.
* (c) Copyright 2005, http://www.tern.com
*
* - Created to support i2chip module on a variety of TERN hardware platforms.
********************************************************************************
*/

#include <embedded.h>
#include "i2chip_hw.h"

#ifdef I2CHIP_MMC
#include "mmc.h"
#endif

void i2chip_init(void)
{

#ifdef TERN_586
/*
	poke(MMCR,_BOOTCSCTL_,peek(MMCR,_BOOTCSCTL_)&0xffc9);	// ROM 1 wait
	poke(MMCR,_ROMCS2CTL_,peek(MMCR,_ROMCS2CTL_)&0xffc8);	// SRAM 0 wait

	pokeb(MMCR,	_GPCSRT_, 24); // set the GP CS recovery time, 12 works
	pokeb(MMCR,	_GPCSPW_, 128); // set the GP CS width, 64 works
	pokeb(MMCR,	_GPCSOFF_, 16); // set the GP CS offset, 8 works
	pokeb(MMCR,	_GPRDW_, 80); // set the GP RD pulse width, 50 works
	pokeb(MMCR,	_GPRDOFF_, 30); // set the GP RD offset, 15 works
	pokeb(MMCR,	_GPWRW_, 80); // set the GP WR pulse width, 50
	pokeb(MMCR,	_GPWROFF_, 30); // set the GP WR offset, 15
*/

#ifdef TERN_5E
	pokeb(MMCR,	_GPCSDW_, peekb(MMCR, _GPCSDW_)&0xf7); // set /CS3-/CSM Data Width=8
	pokeb(MMCR,	_CSPFS_, peekb(MMCR, _CSPFS_)|0x08); // set the GP CS3 PIN Function
	poke(MMCR,	_PAR15_, 0x2000); // set CS3 I/O region
	poke(MMCR,	_PAR15_+2, 0x2dff); // set CS3 I/O region, 512 bytes

	pokeb(MMCR,	_GPCSDW_, peekb(MMCR, _GPCSDW_)&0x7f); // CS7=J4.3 Data Width=8, /CSI
//	pokeb(MMCR,	_GPCSDW_, peekb(MMCR, _GPCSDW_)|0x80); // CS7=J4.3 Data Width=16
	pokeb(MMCR,	_CSPFS_, peekb(MMCR, _CSPFS_)|0x80); // set the GP CS7 PIN Function
	poke(MMCR,	_PAR7_, 0x4000); // set CS7 I/O region
	poke(MMCR,	_PAR7_+2, 0x3dff); // set CS7 I/O region, 512 bytes
#else
   // If it's not 5E, then it must be 5P... in which case, we use PCS0 and
   // PCS1 as the chip-selects.
	pokeb(MMCR,	_GPCSDW_, peekb(MMCR, _GPCSDW_)&0xfe); // CS0 Data Width=8
	poke(MMCR, _PIOPFS31_16_, peek(MMCR,_PIOPFS31_16_)|0x0800); // P27=/CS0
 	poke(MMCR,	_PAR13_, 0x1800); // CS0 I/O region
 	poke(MMCR,	_PAR13_+2, 0x21ff); // CS0 I/O RW, 512 bytes, start 0x1800
#endif

a	HLPRsetvect(0x47, (void far *) spu_m_isr);
	HLPRsetvect(0x4f, (void far *) spu_1_isr);
	HLPRsetvect(0x57, (void far *) spu_2_isr);
#endif  // 186, or RE

#ifdef TERN_186
   pio_init(18, 0);	//	P18=CTS1 for /PCS2

#ifdef TERN_16_BIT
	outport(0xfff2, 2);	// AUXCON, MCS, Bus 16-bit
#endif

#ifdef I2CHIP_MCS_DIRECT
	outport(0xffa0,0xc0bf); 						     // UMCS, 256K ROM, disable AD15-0
	outport(0xfff0,inport(0xfff0)|0x4000 );        // SYSCON, MCS0 0x80000-0xbffff
	outport(0xffa8,0xa0bf ); 					        // MPCS, MCS0=P14, 64KB, PCS I/O,
	outport(0xffa6,0x81ff); 						     // MMCS, base 0x80000,
	outport(0xffa2,0x7fbf);						        // 512K RAM,
	outport(0xffa4,0x007d); 						     // PACS, base 0,
	
#else

	outport( 0xffa0,0xc0bf); // UMCS, 256K ROM, 3 wait, disable AD15-0
	outport( 0xfff0,inport(0xfff0)|0x4000 ); // SYSCON, MCS0 0x80000-0xbffff
//   outport( 0xffa8,0xa0bc ); // MPCS, MCS0=P14, 64KB, PCS I/O 0 wait
//	outport( 0xffa8,0xa0bd ); // MPCS, MCS0=P14, 64KB, PCS I/O 1 wait
	outport( 0xffa8,0xa0bf ); // MPCS, MCS0=P14, 64KB, PCS I/O 1 wait
#endif // I2CHIP_MCS_DIRECT

#ifndef TERN_RE   // 80 MHz R- boards can't tolerate zero wait state.
	outport( 0xffa6,0x81ff ); // MMCS, base 0x80000
 	outport(0xffa2,0x7fbe);	// 512K RAM, 0 wait states
 	outport(0xffa4,0x007d); // PACS, base 0, 0 wait
#endif
	pio_init(14,0); 									     //  Enable /MCS0

#endif // TERN_186


#ifdef I2CHIP_WINDOW
#ifdef I2CHIP_SHIFTED_ADDRESS
	pio_init(12, 2); // Configure P12 as A7, an output we'll be using.
   pio_wr(12, 0);   // Set A7 low, initially.
#endif
	WINDOW_RESTORE_BASE;    // Equivalent to calling mmc_window(7, 0);
#endif
}

#ifdef I2CHIP_WINDOW

void i2chip_set_page(u_int page)
{
	u_int new_page = page;

#ifdef   I2CHIP_SHIFTED_ADDRESS
	if (page & 0x01)   // ... we're checking the right-most bit in the page.
    	outport(0xff74, inport(0xff74) | 0x1000 ); // Using P12 as A7...
   else
   	outport(0xff74, inport(0xff74) & 0xefff );

   new_page = page >> 1;
#endif

#ifdef   I2CHIP_MMC
	mmc_window(7, new_page);   // See mmc.c
#endif
#ifdef   I2CHIP_P51
	p51_window(new_page);
#endif
}

static u_int s_addr = 0xffff;
u_char far* i2chip_mkptr(u_int addr)
{
	if ((s_addr & 0xff00) == (addr & 0xff00)) // No point... no point...
		return MK_FP(WINDOW_BASE_SEGM, addr & 0xff);

	s_addr = addr ;

	// So the argument to this function is... what again?
   // I think it should be the highest 16-bits... or, in other words,
   // FP_SEG of a huge ptr.
   // Ok, and the *return* value should be a UINT value for the new
   // segment address to be used, if it's at all needed.  TODO
   I2CHIP_SET_PAGE(s_addr >> 8);  // Portable version
//	outportb(0x00, addr>>8); // quicker version

	return MK_FP(WINDOW_BASE_SEGM, addr & 0xff);
}

void i2chip_set_window(u_int window_addr)
{
	s_addr = window_addr;
   I2CHIP_SET_PAGE(s_addr >> 8);
}

// Still inside #define I2CHIP_WINDOW ...

u_int i2chip_get_window(void)
{
   return s_addr & 0xff00;
}

void i2chip_push_window(u_int addr)
{
	I2CHIP_SET_PAGE(addr>>8);
}

void i2chip_pop_window(void)
{
	I2CHIP_SET_PAGE(s_addr >> 8);
}

#ifdef I2CHIP_WINDOW_IO
u_char   io_read_value(u_char far* addr)
{
	// return value ... we assume the page is already set.  So, instead,
   // we just go ahead and output valeu.
   return inportb(I2CHIP_BASE_SEG + (FP_OFF(addr) & 0xff));
}

void     io_write_value(u_char far* addr, u_char value)
{
 	// Get the last whatever bytes... and write value.
	outportb(I2CHIP_BASE_SEG + (FP_OFF(addr) & 0xff), value);
}

#endif // I2CHIP_WINDOW_IO


#ifdef   I2CHIP_P51
void p51_window(unsigned int page)
{
asm xor ax, ax
asm mov ax, page
#ifdef   I2CHIP_WINDOW_IO
asm mov dx, 1040h
asm out dx, al
#else
asm out 040h, al
#endif
// use J1.19=/CS6
}
#endif  // I2CHIP_P51

#endif // I2CHIP_WINDOW

#ifdef TERN_586
/*
//	Function: spu_m_isr
//	P22=Master PIC IR7, interrupt vector=0x47, /INTA
*/
void interrupt far spu_m_isr(void)
{
disable();
// Issue the EOI to interrupt controller
outportb(_MPICOCW2_IO,0x67); // Specific EQI for master IR7
enable();
}

/*
//	Function: spu_1_isr
//	P10=slave1 PIC IR7, Master IR2, interrupt vector=0x4f, /INTC
*/
void interrupt far spu_1_isr(void)
{
disable();
// Issue the EOI to interrupt controller
	outportb(_S1PICOCW2_IO,0x67);	// Specific EOI for slave 1 IR7
  	outportb(_MPICOCW2_IO,0x62); // Specific EQI for master IR2
enable();
}

/*
//	Function: spu_2_isr
//	P20=Slave2 PIC IR7, Master IR5, interrupt vector=0x57, GPIRQ7=PIO16 GP timer1
*/
void interrupt far spu_2_isr(void)
{
disable();
// Issue the EOI to interrupt controller
	outportb(_S2PICOCW2_IO,0x67);	// Specific EOI for slave 1 IR7
  	outportb(_MPICOCW2_IO,0x65); // Specific EQI for master IR5
enable();
}
#endif
