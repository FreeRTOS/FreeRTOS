/******************************************************************************
 *
 * mmc_decode_cid() and sd_decode_csd()
 *
 * analyse the meta data of an SD-card to read its capacity and some other properties.
 *
 * CID and CSD Analysis borrowed from the Linux kernel.
 *
 ******************************************************************************/

#ifndef SDPS_INFO_H_

#define SDPS_INFO_H_  1

#include <stdint.h>

struct mmc_cid {
	uint32_t	manfid;
	char		prod_name[8];
	uint32_t	serial;
	uint16_t	oemid;
	uint16_t	year;
	uint8_t		hwrev;
	uint8_t		fwrev;
	uint8_t		month;
};

struct mmc_csd {
	volatile uint64_t	capacity_bytes;
	uint32_t	sd_last_block_address;
	uint8_t		mmca_vsn;
	uint16_t	erase_size;
	uint8_t		spare;
	uint16_t	cmdclass;
	uint16_t	tacc_clks;
	int32_t		erase_shift;
	uint32_t	tacc_ns;
	uint32_t	r2w_factor;
	uint32_t	max_dtr;
	uint32_t	read_blkbits;
	uint32_t	write_blkbits;
	uint32_t	capacity;
	uint32_t	pref_erase;
	uint32_t	read_partial : 1,
				read_misalign : 1,
				write_partial : 1,
				write_misalign : 1;
};

extern struct mmc_cid myCID;
extern struct mmc_csd myCSD;

int mmc_decode_cid( const struct mmc_csd *pxCSD, struct mmc_cid *pxCID, uint32_t *raw_data );
int sd_decode_csd( struct mmc_csd *pxCSD, uint32_t *ulResponse );

#endif /* SDPS_INFO_H_ */
