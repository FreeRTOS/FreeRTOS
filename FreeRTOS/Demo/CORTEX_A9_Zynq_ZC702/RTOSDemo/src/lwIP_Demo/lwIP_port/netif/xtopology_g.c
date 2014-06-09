#include "netif/xtopology.h"
#include "xparameters.h"

struct xtopology_t xtopology[] = {
	{
		0xE000B000,
		xemac_type_emacps,
		0x0,
		0x0,
		0xF8F00100,
		0x36,
	},
};

int xtopology_n_emacs = 1;
