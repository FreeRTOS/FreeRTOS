
/* CFM init */

#define KEY_UPPER   0
#define KEY_LOWER   0
#define CFMPROT  	0
#define CFMSACC  	0
#define CFMDACC  	0
#define CFMSEC  	0

#pragma define_section cfmconfig ".cfmconfig"  far_absolute R
#pragma explicit_zero_data on

__declspec(cfmconfig)  unsigned long _cfm[6] = {
	KEY_UPPER,   	/* 0x00000400 */
	KEY_LOWER,  	/* 0x00000404 */
	CFMPROT,	    /* 0x00000408 */
	CFMSACC,	    /* 0x0000040C */
	CFMDACC,	    /* 0x00000410 */
	CFMSEC,	        /* 0x00000414 */
};
