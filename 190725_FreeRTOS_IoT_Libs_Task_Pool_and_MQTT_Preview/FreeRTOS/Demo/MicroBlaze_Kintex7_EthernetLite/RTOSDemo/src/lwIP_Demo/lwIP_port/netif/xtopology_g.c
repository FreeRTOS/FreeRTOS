#include "netif/xtopology.h"
#include "xparameters.h"

struct xtopology_t xtopology[] = {
	{
		0x40E00000,
		xemac_type_xps_emaclite,
		0x41200000,
		2,
		0x0,
		0x0,
	},
};

int xtopology_n_emacs = 1;
