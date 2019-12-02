/******************************************************************************
 *
 * mmc_decode_cid() and sd_decode_csd()
 *
 * analyse the meta data of an SD-card to read its capacity and some other properties.
 *
 * CID and CSD Analysis borrowed from the Linux kernel.
 *
 ******************************************************************************/

#include "xsdps.h"

#include "xparameters.h"
#include "xil_cache.h"

#include "ff_headers.h"

#include "xsdps_info.h"

struct mmc_cid myCID;
struct mmc_csd myCSD;

u32 UNSTUFF_BITS( u32 *ulResponse, int iFirst, int iSize )
{
const u32 ulMask = ( iSize < 32 ? ( 1 << iSize ) : 0 ) - 1;
const int iOffset = 3 - ( iFirst / 32);
const int iShiftCount = iFirst & 31;
u32 ulResult;

	ulResult = ulResponse[ iOffset ] >> iShiftCount;
	if( iSize + iShiftCount > 32 )
	{
		ulResult |= ulResponse[ iOffset - 1 ] << ( ( 32 - iShiftCount ) % 32 );
	}
	return ulResult & ulMask;						\
}

int mmc_decode_cid( const struct mmc_csd *pxCSD, struct mmc_cid *pxCID, u32 *ulResponse )
{
int iResult = 0;

	/*
	 * The selection of the format here is based upon published
	 * specs from sandisk and from what people have reported.
	 */

	switch( pxCSD->mmca_vsn )
	{
	case 0: /* MMC v1.0 - v1.2 */
	case 1: /* MMC v1.4 */
		pxCID->manfid         = UNSTUFF_BITS( ulResponse, 104, 24 );
		pxCID->prod_name[ 0 ] = UNSTUFF_BITS( ulResponse, 96, 8 );
		pxCID->prod_name[ 1 ] = UNSTUFF_BITS( ulResponse, 88, 8 );
		pxCID->prod_name[ 2 ] = UNSTUFF_BITS( ulResponse, 80, 8 );
		pxCID->prod_name[ 3 ] = UNSTUFF_BITS( ulResponse, 72, 8 );
		pxCID->prod_name[ 4 ] = UNSTUFF_BITS( ulResponse, 64, 8 );
		pxCID->prod_name[ 5 ] = UNSTUFF_BITS( ulResponse, 56, 8 );
		pxCID->prod_name[ 6 ] = UNSTUFF_BITS( ulResponse, 48, 8 );
		pxCID->hwrev          = UNSTUFF_BITS( ulResponse, 44, 4 );
		pxCID->fwrev          = UNSTUFF_BITS( ulResponse, 40, 4 );
		pxCID->serial         = UNSTUFF_BITS( ulResponse, 16, 24 );
		pxCID->month          = UNSTUFF_BITS( ulResponse, 12, 4 );
		pxCID->year           = UNSTUFF_BITS( ulResponse, 8, 4 ) + 1997;
		break;

	case 2: /* MMC v2.0 - v2.2 */
	case 3: /* MMC v3.1 - v3.3 */
	case 4: /* MMC v4 */
		pxCID->manfid         = UNSTUFF_BITS( ulResponse, 120, 8 );
		pxCID->oemid          = UNSTUFF_BITS( ulResponse, 104, 16 );
		pxCID->prod_name[ 0 ] = UNSTUFF_BITS( ulResponse, 96, 8 );
		pxCID->prod_name[ 1 ] = UNSTUFF_BITS( ulResponse, 88, 8 );
		pxCID->prod_name[ 2 ] = UNSTUFF_BITS( ulResponse, 80, 8 );
		pxCID->prod_name[ 3 ] = UNSTUFF_BITS( ulResponse, 72, 8 );
		pxCID->prod_name[ 4 ] = UNSTUFF_BITS( ulResponse, 64, 8 );
		pxCID->prod_name[ 5 ] = UNSTUFF_BITS( ulResponse, 56, 8 );
		pxCID->serial         = UNSTUFF_BITS( ulResponse, 16, 32 );
		pxCID->month          = UNSTUFF_BITS( ulResponse, 12, 4 );
		pxCID->year           = UNSTUFF_BITS( ulResponse, 8, 4 ) + 1997;
		break;

	default:
		FF_PRINTF ("mmc_decode_cid: card has unknown MMCA version %d\n",
			pxCSD->mmca_vsn);
		iResult = -1;
		break;
	}
	if( iResult >= 0 )
	{
		FF_PRINTF ("CID: Manfid %lu (%-8.8s) serial %lu oem %u mon/year %u/%u rev %u fw %u\n",
			pxCID->manfid,
			pxCID->prod_name,
			pxCID->serial,
			pxCID->oemid,
			pxCID->month,
			pxCID->year,
			pxCID->hwrev,
			pxCID->fwrev);
	}

	return iResult;
}

static const unsigned int tran_exp[] =
{
	10000,		100000,		1000000,	10000000,
	0,		0,		0,		0
};

static const unsigned char tran_mant[] =
{
	0,	10,	12,	13,	15,	20,	25,	30,
	35,	40,	45,	50,	55,	60,	70,	80,
};

static const unsigned int tacc_exp[] =
{
	1,	10,	100,	1000,	10000,	100000,	1000000, 10000000,
};

static const unsigned int tacc_mant[] =
{
	0,	10,	12,	13,	15,	20,	25,	30,
	35,	40,	45,	50,	55,	60,	70,	80,
};

char mmc_is_block_addressed;

/* Given a 128-bit response, decode to our card CSD structure. */

static __inline unsigned tobe32( unsigned value )
{
	return
		( value >> 24 ) |
		( ( value >>  8 ) & 0x0000ff00 ) |
		( ( value <<  8 ) & 0x00ff0000 ) |
		( value << 24 );
	
}

int sd_decode_csd( struct mmc_csd *pxCSD, u32 *ulResponse )
{
unsigned int e, m, csd_struct;
int iResult = 0;

	csd_struct = UNSTUFF_BITS( ulResponse, 126, 2 );

	pxCSD->mmca_vsn = UNSTUFF_BITS( ulResponse, 122, 4 );

	FF_PRINTF("CSD data: %08x %08x %08x %08x mmca_vsn = %u\n",
		( unsigned )ulResponse[0],
		( unsigned )ulResponse[1],
		( unsigned )ulResponse[2],
		( unsigned )ulResponse[3],
		pxCSD->mmca_vsn);
//	pxCSD->mmca_vsn = 2;

	// CSD data: 005e0032 5f5a83cb 2db7ffbf 9680000f
	// sd_decode_csd: capacity 1989120 (byte addressed)
	switch (csd_struct) {
	case 0:
		m = UNSTUFF_BITS( ulResponse, 115, 4 );
		e = UNSTUFF_BITS( ulResponse, 112, 3 );
		pxCSD->tacc_ns = ( tacc_exp[ e ] * tacc_mant[ m ] + 9 ) / 10;
		pxCSD->tacc_clks = UNSTUFF_BITS( ulResponse, 104, 8 ) * 100;

		m = UNSTUFF_BITS( ulResponse, 99, 4 );
		e = UNSTUFF_BITS( ulResponse, 96, 3 );
		pxCSD->max_dtr = tran_exp[ e ] * tran_mant[ m ];
		pxCSD->cmdclass = UNSTUFF_BITS( ulResponse, 84, 12 );

		e = UNSTUFF_BITS( ulResponse, 47, 3 );
		m = UNSTUFF_BITS( ulResponse, 62, 12 );
		pxCSD->capacity = ( 1 + m ) << ( e + 2 );
		/*
		 * The CSD capacity field is in units of read_blkbits.
		 * set_capacity takes units of 512 bytes.
		 */

		pxCSD->read_blkbits = UNSTUFF_BITS( ulResponse, 80, 4 );
		pxCSD->read_partial = UNSTUFF_BITS( ulResponse, 79, 1 );
		pxCSD->write_misalign = UNSTUFF_BITS( ulResponse, 78, 1 );
		pxCSD->read_misalign = UNSTUFF_BITS( ulResponse, 77, 1 );
		pxCSD->r2w_factor = UNSTUFF_BITS( ulResponse, 26, 3 );
		pxCSD->write_blkbits = UNSTUFF_BITS( ulResponse, 22, 4 );
		pxCSD->write_partial = UNSTUFF_BITS( ulResponse, 21, 1 );

		pxCSD->capacity <<= ( pxCSD->read_blkbits - 9 );
		FF_PRINTF ("Capacity: (%u + 1) << (%u + 2) = %u Rd/Wr bits %u/%u\n",
			m, e,
			( unsigned )pxCSD->capacity,
			( unsigned )pxCSD->read_blkbits,
			( unsigned )pxCSD->write_blkbits);

		if( UNSTUFF_BITS( ulResponse, 46, 1 ) )
		{
			pxCSD->erase_size = 1;
		}
		else if( pxCSD->write_blkbits >= 9 )
		{
			pxCSD->erase_size = UNSTUFF_BITS( ulResponse, 39, 7 ) + 1;
			pxCSD->erase_size <<= pxCSD->write_blkbits - 9;
		}
		else
		{
			pxCSD->erase_size = 0; // Card is not eraseble
		}
		break;

	case 1:
		/*
		 * This is a block-addressed SDHC card. Most
		 * interesting fields are unused and have fixed
		 * values. To avoid getting tripped by buggy cards,
		 * we assume those fixed values ourselves.
		 */
		mmc_is_block_addressed = 1;

		pxCSD->tacc_ns = 0; /* Unused */
		pxCSD->tacc_clks = 0; /* Unused */

		m = UNSTUFF_BITS( ulResponse, 99, 4 );
		e = UNSTUFF_BITS( ulResponse, 96, 3 );
		// max_dtr gives 25,000,000
		pxCSD->max_dtr = tran_exp[ e ] * tran_mant[ m ];
		// cmdClass gives: 10110110101 (0x5B5)
		pxCSD->cmdclass = UNSTUFF_BITS( ulResponse, 84, 12 );

		m = UNSTUFF_BITS( ulResponse, 48, 22 );
		pxCSD->capacity = ( 1 + m ) << 10;

		FF_PRINTF( "capacity: (1 + %u) << 10  DTR %u Mhz\n", m, pxCSD->max_dtr / 1000000);

		pxCSD->read_blkbits = 9;
		pxCSD->read_partial = 0;
		pxCSD->write_misalign = 0;
		pxCSD->read_misalign = 0;
		pxCSD->r2w_factor = 4; /* Unused */
		pxCSD->write_blkbits = 9;
		pxCSD->write_partial = 0;
		pxCSD->erase_size = 1;
		break;
	default:
		FF_PRINTF ("sd_decode_csd: unrecognised CSD structure version %d\n", csd_struct);
		iResult = -1;
		break;
	}
	if( iResult >= 0 )
	{
	unsigned int sz;

		FF_PRINTF ("sd_decode_csd: capacity %lu (%s addressed)\n",
			pxCSD->capacity, mmc_is_block_addressed ? "block" : "byte");

		sz = (pxCSD->capacity << (pxCSD->read_blkbits - 9)) >> 11;
		if (sz < 128)
		{
			pxCSD->pref_erase = 512 * 1024 / 512;
		}
		else if (sz < 512)
		{
			pxCSD->pref_erase = 1024 * 1024 / 512;
		}
		else if (sz < 1024)
		{
			pxCSD->pref_erase = 2 * 1024 * 1024 / 512;
		}
		else
		{
			pxCSD->pref_erase = 4 * 1024 * 1024 / 512;
		}

		if (pxCSD->pref_erase < pxCSD->erase_size)
		{
			pxCSD->pref_erase = pxCSD->erase_size;
		}
		else
		{
			sz = ( pxCSD->pref_erase % pxCSD->erase_size );
			if( sz != 0 )
			{
				pxCSD->pref_erase += ( pxCSD->erase_size - sz );
			}
		}

		// compute last block addr

		pxCSD->sd_last_block_address = pxCSD->capacity - 1;

		// compute card capacity in bytes
		pxCSD->capacity_bytes = ( ( uint64_t )XSDPS_BLK_SIZE_512_MASK ) * pxCSD->capacity;

		FF_PRINTF( "sd_mmc_spi_get_capacity: Capacity %lu MB Erase %u Pref %lu\n",
			( uint32_t ) ( pxCSD->capacity_bytes / ( 1024LLU * 1024LLU ) ),
			pxCSD->erase_size,
			pxCSD->pref_erase );
	}

	return iResult;
}
