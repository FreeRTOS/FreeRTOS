/*====================================================================
* Project:  Board Support Package (BSP)
* Developed using:
* Function: Determine the frequency the CPU is running at (TC1782)
*
* Copyright HighTec EDV-Systeme GmbH 1982-2010
*====================================================================*/

#include <machine/wdtcon.h>
#include <tc1782/scu.h>
#include <tc1782/cpu.h>


#ifndef DEF_FRQ
#define DEF_FRQ			20000000U	/* TriBoard-TC1782 quartz frequency is 20 MHz */
#endif /* DEF_FRQ */

#define VCOBASE_FREQ	400000000U	/* ?? */

/* divider values for 150 MHz */
#define SYS_CFG_PDIV	 2
#define SYS_CFG_NDIV	30
#define SYS_CFG_K1DIV	 2
#define SYS_CFG_K2DIV	 2


/* prototypes for global functions */
void set_cpu_frequency(void);
unsigned int get_cpu_frequency(void);

/* initialization flag: prevent multiple initialization of PLL_CLC */
static int freq_init = 0;


/* Set the frequency the CPU is running at */

void set_cpu_frequency(void)
{
	SCU_PLLCON0_t_nonv pllcon0;
	SCU_PLLCON1_t_nonv pllcon1;

	if (freq_init)
	{
		return;
	}

	freq_init = 1;

	/* check whether we are already running at desired clockrate */
	pllcon0 = SCU_PLLCON0;
	pllcon1 = SCU_PLLCON1;
	if (	((SYS_CFG_NDIV - 1)  == pllcon0.bits.NDIV)
		&&	((SYS_CFG_PDIV - 1)  == pllcon0.bits.PDIV)
		&&	((SYS_CFG_K1DIV - 1) == pllcon1.bits.K1DIV)
		&&	((SYS_CFG_K2DIV - 1) == pllcon1.bits.K2DIV)
		&&	SCU_PLLSTAT.bits.VCOLOCK)
	{
		return;
	}

	if (!SCU_PLLSTAT.bits.PWDSTAT)
	{
		/* set speed to 180 MHz with 20MHz Crystal */
		pllcon0.reg = 0;
		pllcon1.reg = 0;
		pllcon0.bits.NDIV  = SYS_CFG_NDIV - 1;
		pllcon0.bits.PDIV  = SYS_CFG_PDIV - 1;
		pllcon1.bits.K2DIV = SYS_CFG_K2DIV - 1;
		pllcon1.bits.K1DIV = SYS_CFG_K1DIV - 1;
		pllcon0.bits.VCOBYP = 1;
		pllcon0.bits.CLRFINDIS = 1;
		pllcon0.bits.PLLPWD = 1;
		pllcon0.bits.RESLD = 1;

		unlock_wdtcon();
		/* FPI at half CPU speed */
		SCU_CCUCON0.reg = 1;

		/* force prescaler mode */
		SCU_PLLCON0.bits.VCOBYP = 1;

		/* wait for prescaler mode */
		while (!SCU_PLLSTAT.bits.VCOBYST)
			;

		/* write new control values */
		SCU_PLLCON1 = pllcon1;
		SCU_PLLCON0 = pllcon0;
		lock_wdtcon();

		/* wait for stable VCO frequency */
		while (!SCU_PLLSTAT.bits.VCOLOCK)
			;

		unlock_wdtcon();
		/* leave prescaler mode */
		SCU_PLLCON0.bits.VCOBYP = 0;
		lock_wdtcon();
	}
}

/* Determine the frequency the CPU is running at */

unsigned int get_cpu_frequency(void)
{
	unsigned int frequency;
	unsigned int fpidiv;
	SCU_PLLCON0_t_nonv pllcon0;
	SCU_PLLCON1_t_nonv pllcon1;
	SCU_PLLSTAT_t_nonv pllstat;

	if (!freq_init)
	{
		set_cpu_frequency();

#ifdef ENABLE_ICACHE
		/* enable instruction cache (PMI_CON0) */
		unlock_wdtcon();
		PMI_CON0.bits.PCBYP = 0;
		lock_wdtcon();
#endif /* ENABLE_ICACHE */
	}

	pllcon0 = SCU_PLLCON0;
	pllcon1 = SCU_PLLCON1;
	pllstat = SCU_PLLSTAT;

	/* read FPI divider value */
	fpidiv = SCU_CCUCON0.bits.FPIDIV;

	if (pllstat.bits.VCOBYST)
	{
		/* prescaler mode */
		unsigned int k_div;

		k_div = pllcon1.bits.K1DIV + 1;
		frequency = DEF_FRQ / k_div;
	}
	else if (pllstat.bits.FINDIS)
	{
		/* freerunning mode */
		unsigned int k_div;

		k_div = pllcon1.bits.K2DIV + 1;
		frequency = VCOBASE_FREQ / k_div;
	}
	else
	{
		/* normal mode */
		unsigned int k_div, n_div, p_div;

		n_div = pllcon0.bits.NDIV + 1;
		p_div = pllcon0.bits.PDIV + 1;
		k_div = pllcon1.bits.K2DIV + 1;

		frequency = DEF_FRQ * n_div / (k_div * p_div);
	}

	frequency /= (fpidiv + 1);

	return frequency;
}
