/*
 * FreeRTOS+FAT build 191128 - Note:  FreeRTOS+FAT is still in the lab!
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 * Authors include James Walmsley, Hein Tibosch and Richard Barry
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 *
 */

/**
 *	@file		ff_format.c
 *	@ingroup	FORMAT
 *
 *	@defgroup	FAT Fat File-System
 *	@brief		Format a drive, given the number of sectors.
 *
 **/

#include "ff_headers.h"

#include <time.h>
#include <string.h>

#if defined( __BORLANDC__ )
	#include "ff_windows.h"
#else
	#include "FreeRTOS.h"
	#include "task.h"	/* For FreeRTOS date/time function */
#endif


/*=========================================================================================== */

#define	OFS_PART_ACTIVE_8             0x000 /* 0x01BE 0x80 if active */
#define	OFS_PART_START_HEAD_8         0x001 /* 0x01BF */
#define	OFS_PART_START_SEC_TRACK_16   0x002 /* 0x01C0 */
#define	OFS_PART_ID_NUMBER_8          0x004 /* 0x01C2 */
#define	OFS_PART_ENDING_HEAD_8        0x005 /* 0x01C3 */
#define	OFS_PART_ENDING_SEC_TRACK_16  0x006 /* 0x01C4   = SectorCount - 1 - ulHiddenSectors */
#define	OFS_PART_STARTING_LBA_32      0x008 /* 0x01C6   = ulHiddenSectors (This is important) */
#define	OFS_PART_LENGTH_32            0x00C /* 0x01CA   = SectorCount - 1 - ulHiddenSectors */

#define	OFS_PTABLE_MACH_CODE          0x000 /* 0x0000 */
#define	OFS_PTABLE_PART_0             0x1BE /* 446 */
#define	OFS_PTABLE_PART_1             0x1CE /* 462 */
#define	OFS_PTABLE_PART_2             0x1DE /* 478 */
#define	OFS_PTABLE_PART_3             0x1FE /* 494 */
#define	OFS_PTABLE_PART_LEN           16

/*=========================================================================================== */

#define	OFS_BPB_jmpBoot_24           0x000 /* uchar jmpBoot[3] "0xEB 0x00 0x90" */
#define	OFS_BPB_OEMName_64           0x003 /* uchar BS_OEMName[8] "MSWIN4.1" */

#define	OFS_BPB_BytsPerSec_16        0x00B /* Only 512, 1024, 2048 or 4096 */
#define	OFS_BPB_SecPerClus_8         0x00D /* Only 1, 2, 4, 8, 16, 32, 64, 128 */
#define	OFS_BPB_ResvdSecCnt_16       0x00E /* ulFATReservedSectors, e.g. 1 (FAT12/16) or 32 (FAT32) */

#define	OFS_BPB_NumFATs_8            0x010 /* 2 recommended */
#define	OFS_BPB_RootEntCnt_16        0x011 /* ((iFAT16RootSectors * 512) / 32) 512 (FAT12/16) or 0 (FAT32) */
#define	OFS_BPB_TotSec16_16          0x013 /* xxx (FAT12/16) or 0 (FAT32) */
#define	OFS_BPB_Media_8              0x015 /* 0xF0 (rem media) also in FAT[0] low byte */

#define	OFS_BPB_FATSz16_16           0x016
#define	OFS_BPB_SecPerTrk_16         0x018 /* n.a. CF has no tracks */
#define	OFS_BPB_NumHeads_16          0x01A /* n.a. 1 ? */
#define	OFS_BPB_HiddSec_32           0x01C /* n.a.	0 for nonparitioned volume */
#define	OFS_BPB_TotSec32_32          0x020 /* >= 0x10000 */

#define	OFS_BPB_16_DrvNum_8          0x024 /* n.a. */
#define	OFS_BPB_16_Reserved1_8       0x025 /* n.a. */
#define	OFS_BPB_16_BootSig_8         0x026 /* n.a. */
#define	OFS_BPB_16_BS_VolID_32       0x027 /* "unique" number */
#define	OFS_BPB_16_BS_VolLab_88      0x02B /* "NO NAME    " */
#define	OFS_BPB_16_FilSysType_64     0x036 /* "FAT12   " */

#define	OFS_BPB_32_FATSz32_32        0x024 /* Only when BPB_FATSz16 = 0 */
#define	OFS_BPB_32_ExtFlags_16       0x028 /* FAT32 only */
#define	OFS_BPB_32_FSVer_16          0x02A /* 0:0 */
#define	OFS_BPB_32_RootClus_32       0x02C /* See 'iFAT32RootClusters' Normally 2 */
#define	OFS_BPB_32_FSInfo_16         0x030 /* Normally 1 */
#define	OFS_BPB_32_BkBootSec_16      0x032 /* Normally 6 */
#define	OFS_BPB_32_Reserved_96       0x034 /* Zeros */
#define	OFS_BPB_32_DrvNum_8          0x040 /* n.a. */
#define	OFS_BPB_32_Reserved1_8       0x041 /* n.a. */
#define	OFS_BPB_32_BootSig_8         0x042 /* n.a. */
#define	OFS_BPB_32_VolID_32          0x043 /* "unique" number */
#define	OFS_BPB_32_VolLab_88         0x047 /* "NO NAME    " */
#define	OFS_BPB_32_FilSysType_64     0x052 /* "FAT12   " */

#define	OFS_FSI_32_LeadSig			0x000 /* With contents 0x41615252 */
#define	OFS_FSI_32_Reserved1		0x004 /* 480 times 0 */
#define	OFS_FSI_32_StrucSig			0x1E4 /* With contents 0x61417272 */
#define	OFS_FSI_32_Free_Count		0x1E8 /* last known free cluster count on the volume, ~0 for unknown */
#define	OFS_FSI_32_Nxt_Free			0x1EC /* cluster number at which the driver should start looking for free clusters */
#define	OFS_FSI_32_Reserved2		0x1F0 /* zero's */
#define	OFS_FSI_32_TrailSig			0x1FC /* 0xAA550000 (little endian) */

#define RESV_COUNT					32

#ifdef ffconfigMIN_CLUSTERS_FAT32
	#define MIN_CLUSTER_COUNT_FAT32		ffconfigMIN_CLUSTERS_FAT32
#else
	#define MIN_CLUSTER_COUNT_FAT32		( 65525 )
#endif

#ifdef ffconfigMIN_CLUSTERS_FAT16
	#define MIN_CLUSTERS_FAT16			ffconfigMIN_CLUSTERS_FAT16
#else
	#define MIN_CLUSTERS_FAT16			( 4085 + 1 )
#endif

#ifndef ffconfigFAT16_ROOT_SECTORS
	#define ffconfigFAT16_ROOT_SECTORS    32
#endif

static portINLINE uint32_t ulMin32( uint32_t a, uint32_t b )
{
uint32_t ulReturn;

	if( a <= b )
	{
		ulReturn = a;
	}
	else
	{
		ulReturn = b;
	}
	return ulReturn;
}

/*_RB_ Candidate for splitting into multiple functions? */
FF_Error_t FF_Format( FF_Disk_t *pxDisk, BaseType_t xPartitionNumber, BaseType_t xPreferFAT16, BaseType_t xSmallClusters )
{
uint32_t ulHiddenSectors;              /* Space from MBR and partition table */
const uint32_t ulFSInfo = 1;           /* Sector number of FSINFO structure within the reserved area */
const uint32_t ulBackupBootSector = 6; /* Sector number of "copy of the boot record" within the reserved area */
const BaseType_t xFATCount = 2;        /* Number of FAT's */
uint32_t ulFATReservedSectors = 0;     /* Space between the partition table and FAT table. */
int32_t iFAT16RootSectors = 0;         /* Number of sectors reserved for root directory (FAT16 only) */
int32_t iFAT32RootClusters = 0;        /* Initial amount of clusters claimed for root directory (FAT32 only) */
uint8_t ucFATType = 0;                 /* Either 'FF_T_FAT16' or 'FF_T_FAT32' */
uint32_t ulVolumeID = 0;               /* A pseudo Volume ID */

uint32_t ulSectorsPerFAT = 0;          /* Number of sectors used by a single FAT table */
uint32_t ulClustersPerFATSector = 0;   /* # of clusters which can be described within a sector (256 or 128) */
uint32_t ulSectorsPerCluster = 0;      /* Size of a cluster (# of sectors) */
uint32_t ulUsableDataSectors = 0;      /* Usable data sectors (= SectorCount - (ulHiddenSectors + ulFATReservedSectors)) */
uint32_t ulUsableDataClusters = 0;     /* equals "ulUsableDataSectors / ulSectorsPerCluster" */
uint32_t ulNonDataSectors = 0;         /* ulFATReservedSectors + ulHiddenSectors + iFAT16RootSectors */
uint32_t ulClusterBeginLBA = 0;        /* Sector address of the first data cluster */
uint32_t ulSectorCount;
uint8_t *pucSectorBuffer = 0;
FF_SPartFound_t xPartitionsFound;
FF_Part_t *pxMyPartition = 0;
FF_IOManager_t *pxIOManager = pxDisk->pxIOManager;

	FF_PartitionSearch( pxIOManager, &xPartitionsFound );
	if( xPartitionNumber >= xPartitionsFound.iCount )
	{
		return FF_ERR_IOMAN_INVALID_PARTITION_NUM | FF_MODULE_FORMAT;
	}

	pxMyPartition = xPartitionsFound.pxPartitions + xPartitionNumber;
	ulSectorCount = pxMyPartition->ulSectorCount;

	ulHiddenSectors = pxMyPartition->ulStartLBA;

	if( ( ( xPreferFAT16 == pdFALSE ) && ( ( ulSectorCount - RESV_COUNT ) >= 65536 ) ) ||
		( ( ulSectorCount - RESV_COUNT ) >= ( 64 * MIN_CLUSTER_COUNT_FAT32 ) ) )
	{
		ucFATType = FF_T_FAT32;
		iFAT32RootClusters = 2;
		ulFATReservedSectors = RESV_COUNT;
		iFAT16RootSectors = 0;
	}
	else
	{
		ucFATType = FF_T_FAT16;
		iFAT32RootClusters = 0;
		ulFATReservedSectors = 1u;
		iFAT16RootSectors = ffconfigFAT16_ROOT_SECTORS; /* 32 sectors to get 512 dir entries */
	}

	/* Set start sector and length to allow FF_BlockRead/Write */
	pxIOManager->xPartition.ulTotalSectors = pxMyPartition->ulSectorCount;
	pxIOManager->xPartition.ulBeginLBA = pxMyPartition->ulStartLBA;

	/* TODO: Find some solution here to get a unique disk ID */
	ulVolumeID = ( rand() << 16 ) | rand(); /*_RB_ rand() has proven problematic in some environments. */

	/* Sectors within partition which can not be used */
	ulNonDataSectors = ulFATReservedSectors + iFAT16RootSectors;

	/* A fs dependent constant: */
	if( ucFATType == FF_T_FAT32 )
	{
		/* In FAT32, 4 bytes are needed to store the address (LBA) of a cluster.
		Each FAT sector of 512 bytes can contain 512 / 4 = 128 entries. */
		ulClustersPerFATSector = 128u;
	}
	else
	{
		/* In FAT16, 2 bytes are needed to store the address (LBA) of a cluster.
		Each FAT sector of 512 bytes can contain 512 / 2 = 256 entries. */
		ulClustersPerFATSector = 256u;
	}

	FF_PRINTF( "FF_Format: Secs %lu Rsvd %lu Hidden %lu Root %lu Data %lu\n",
		ulSectorCount, ulFATReservedSectors, ulHiddenSectors, iFAT16RootSectors, ulSectorCount - ulNonDataSectors );

	/* Either search from small to large or v.v. */
	if( xSmallClusters != 0 )
	{
		/* The caller prefers to have small clusters.
		Less waste but it can be slower. */
		ulSectorsPerCluster = 1u;
	}
	else
	{
		if( ucFATType == FF_T_FAT32 )
		{
			ulSectorsPerCluster = 64u;
		}
		else
		{
			ulSectorsPerCluster = 32u;
		}
	}

	for( ;; )
	{
		int32_t groupSize;
		/* Usable sectors */
		ulUsableDataSectors = ulSectorCount - ulNonDataSectors;
		/* Each group consists of 'xFATCount' sectors + 'ulClustersPerFATSector' clusters */
		groupSize = xFATCount + ulClustersPerFATSector * ulSectorsPerCluster;
		/* This amount of groups will fit: */
		ulSectorsPerFAT = ( ulUsableDataSectors + groupSize - ulSectorsPerCluster - xFATCount ) / groupSize;

		ulUsableDataClusters = ulMin32(
			( uint32_t ) ( ulUsableDataSectors - xFATCount * ulSectorsPerFAT ) / ulSectorsPerCluster,
			( uint32_t ) ( ulClustersPerFATSector * ulSectorsPerFAT ) );
		ulUsableDataSectors = ulUsableDataClusters * ulSectorsPerCluster;

		if( ( ucFATType == FF_T_FAT16 ) && ( ulUsableDataClusters >= MIN_CLUSTERS_FAT16 ) && ( ulUsableDataClusters < 65536 ) )
		{
			break;
		}

		if( ( ucFATType == FF_T_FAT32 ) && ( ulUsableDataClusters >= 65536 ) && ( ulUsableDataClusters < 0x0FFFFFEF ) )
		{
			break;
		}

		/* Was this the last test? */
		if( ( ( xSmallClusters != pdFALSE ) && ( ulSectorsPerCluster == 32 ) ) ||
			( ( xSmallClusters == pdFALSE ) && ( ulSectorsPerCluster == 1) ) )
		{
			FF_PRINTF( "FF_Format: Can not make a FAT%d (tried %d) with %lu sectors\n",
				ucFATType == FF_T_FAT32 ? 32 : 16, xPreferFAT16 ? 16 : 32, ulSectorCount );
			return FF_ERR_IOMAN_BAD_MEMSIZE | FF_MODULE_FORMAT;
		}
		/* No it wasn't, try next clustersize */
		if( xSmallClusters != pdFALSE )
		{
			ulSectorsPerCluster <<= 1;
		}
		else
		{
			ulSectorsPerCluster >>= 1;
		}
	}

	if( ( ucFATType == FF_T_FAT32 ) && ( ulSectorCount >= 0x100000UL ) )	/* Larger than 0.5 GB */
	{
	uint32_t ulRemaining;
		/*
		 * Putting the FAT-table into the second 4MB erase block gives
		 * a higher performance and a longer life-time.
		 * See e.g. here:
		 * http://3gfp.com/wp/2014/07/formatting-sd-cards-for-speed-and-lifetime/
		 */
		ulFATReservedSectors = 8192 - ulHiddenSectors;
		ulNonDataSectors = ulFATReservedSectors + iFAT16RootSectors;

		ulRemaining = (ulNonDataSectors + 2 * ulSectorsPerFAT) % 128;
		if( ulRemaining != 0 )
		{
			/* In order to get ClusterBeginLBA well aligned (on a 128 sector boundary) */
			ulFATReservedSectors += ( 128 - ulRemaining );
			ulNonDataSectors = ulFATReservedSectors + iFAT16RootSectors;
		}
		ulUsableDataSectors = ulSectorCount - ulNonDataSectors - 2 * ulSectorsPerFAT;
		ulUsableDataClusters = ulUsableDataSectors / ulSectorsPerCluster;
	}
	ulClusterBeginLBA	= ulHiddenSectors + ulFATReservedSectors + 2 * ulSectorsPerFAT;

	pucSectorBuffer = ( uint8_t * ) ffconfigMALLOC( 512 );
	if( pucSectorBuffer == NULL )
	{
		return FF_ERR_NOT_ENOUGH_MEMORY | FF_MODULE_FORMAT;
	}

/*  ======================================================================================= */

	memset( pucSectorBuffer, '\0', 512 );

	memcpy( pucSectorBuffer + OFS_BPB_jmpBoot_24, "\xEB\x00\x90" "FreeRTOS", 11 );   /* Includes OFS_BPB_OEMName_64 */

	FF_putShort( pucSectorBuffer, OFS_BPB_BytsPerSec_16, 512 );   /* 0x00B / Only 512, 1024, 2048 or 4096 */
	FF_putShort( pucSectorBuffer, OFS_BPB_ResvdSecCnt_16, ( uint32_t ) ulFATReservedSectors ); /*  0x00E / 1 (FAT12/16) or 32 (FAT32) */

	FF_putChar( pucSectorBuffer, OFS_BPB_NumFATs_8, 2);          /* 0x010 / 2 recommended */
	FF_putShort( pucSectorBuffer, OFS_BPB_RootEntCnt_16, ( uint32_t ) ( iFAT16RootSectors * 512 ) / 32 ); /* 0x011 / 512 (FAT12/16) or 0 (FAT32) */

	/* For FAT12 and FAT16 volumes, this field contains the count of 32- */
	/* byte directory entries in the root directory */

	FF_putChar( pucSectorBuffer, OFS_BPB_Media_8, 0xF8 );         /* 0x015 / 0xF0 (rem media) also in FAT[0] low byte */

	FF_putShort( pucSectorBuffer, OFS_BPB_SecPerTrk_16, 0x3F );	   /* 0x18 n.a. CF has no tracks */
	FF_putShort( pucSectorBuffer, OFS_BPB_NumHeads_16, 255 );         /* 0x01A / n.a. 1 ? */
	FF_putLong (pucSectorBuffer, OFS_BPB_HiddSec_32, ( uint32_t ) ulHiddenSectors ); /* 0x01C / n.a.	0 for nonparitioned volume */
	{
		int32_t fatBeginLBA;
		int32_t dirBegin;

		FF_putChar( pucSectorBuffer, OFS_BPB_SecPerClus_8, ( uint32_t ) ulSectorsPerCluster ); /*  0x00D / Only 1, 2, 4, 8, 16, 32, 64, 128 */
		FF_PRINTF("FF_Format: SecCluster %lu DatSec %lu DataClus %lu ulClusterBeginLBA %lu\n",
			ulSectorsPerCluster, ulUsableDataSectors, ulUsableDataClusters, ulClusterBeginLBA );

		/* This field is the new 32-bit total count of sectors on the volume. */
		/* This count includes the count of all sectors in all four regions of the volume */
		FF_putShort( pucSectorBuffer, OFS_BPB_TotSec16_16, 0 );        /* 0x013 / xxx (FAT12/16) or 0 (FAT32) */

		FF_putLong (pucSectorBuffer, OFS_BPB_TotSec32_32, ulSectorCount ); /* 0x020 / >= 0x10000 */

		if( ucFATType == FF_T_FAT32 )
		{
			FF_putLong( pucSectorBuffer,  OFS_BPB_32_FATSz32_32, ulSectorsPerFAT );      /* 0x24 / Only when BPB_FATSz16 = 0 */
			FF_putShort( pucSectorBuffer, OFS_BPB_32_ExtFlags_16, 0 );                               /* 0x28 / FAT32 only */
			FF_putShort( pucSectorBuffer, OFS_BPB_32_FSVer_16, 0 );                                  /* 0x2A / 0:0 */
			FF_putLong( pucSectorBuffer,  OFS_BPB_32_RootClus_32, ( uint32_t ) iFAT32RootClusters ); /* 0x2C / Normally 2 */
			FF_putShort( pucSectorBuffer, OFS_BPB_32_FSInfo_16, ulFSInfo );                          /* 0x30 / Normally 1 */
			FF_putShort( pucSectorBuffer, OFS_BPB_32_BkBootSec_16, ulBackupBootSector );             /* 0x32 / Normally 6 */
			FF_putChar( pucSectorBuffer,  OFS_BPB_32_DrvNum_8, 0 );                                  /* 0x40 / n.a. */
			FF_putChar( pucSectorBuffer,  OFS_BPB_32_BootSig_8, 0x29 );                              /* 0x42 / n.a. */
			FF_putLong( pucSectorBuffer,  OFS_BPB_32_VolID_32, ( uint32_t ) ulVolumeID );            /* 0x43 / "unique" number */
			memcpy( pucSectorBuffer + OFS_BPB_32_VolLab_88, "MY NAME    ", 11 );    /* 0x47 / "NO NAME    " */
			memcpy( pucSectorBuffer + OFS_BPB_32_FilSysType_64, "FAT32   ", 8 );    /* 0x52 / "FAT12   " */
		}
		else
		{
			FF_putChar( pucSectorBuffer, OFS_BPB_16_DrvNum_8, 0u );         /* 0x024 / n.a. */
			FF_putChar( pucSectorBuffer, OFS_BPB_16_Reserved1_8, 0 );      /* 0x025 / n.a. */
			FF_putChar( pucSectorBuffer, OFS_BPB_16_BootSig_8, 0x29 );     /* 0x026 / n.a. */
			FF_putLong (pucSectorBuffer, OFS_BPB_16_BS_VolID_32, ( uint32_t ) ulVolumeID ); /* 0x027 / "unique" number */

			FF_putShort( pucSectorBuffer, OFS_BPB_FATSz16_16, ulSectorsPerFAT );		/* 0x16 */

			memcpy( pucSectorBuffer + OFS_BPB_16_BS_VolLab_88, "MY NAME    ", 11 );            /* 0x02B / "NO NAME    " */
			memcpy( pucSectorBuffer + OFS_BPB_16_FilSysType_64, "FAT16   ", 8 );           /* 0x036 / "FAT12   " */
		}

		pucSectorBuffer[510] = 0x55;
		pucSectorBuffer[511] = 0xAA;

		FF_BlockWrite( pxIOManager, ulHiddenSectors, 1, pucSectorBuffer, 0u );
		if (ucFATType == FF_T_FAT32)
		{
			FF_BlockWrite( pxIOManager, ulHiddenSectors + ulBackupBootSector, 1, pucSectorBuffer, pdFALSE );
		}

		if( ucFATType == FF_T_FAT32 )
		{
			memset( pucSectorBuffer, '\0', 512 );

			FF_putLong( pucSectorBuffer, OFS_FSI_32_LeadSig, 0x41615252 );  /* to validate that this is in fact an FSInfo sector. */
			/* OFS_FSI_32_Reserved1		0x004 / 480 times 0 */
			FF_putLong( pucSectorBuffer, OFS_FSI_32_StrucSig, 0x61417272 ); /* Another signature that is more localized in the */
																	 /* sector to the location of the fields that are used. */
			FF_putLong( pucSectorBuffer, OFS_FSI_32_Free_Count, ulUsableDataClusters );      /* last known free cluster count on the volume, ~0 for unknown */
			FF_putLong( pucSectorBuffer, OFS_FSI_32_Nxt_Free, 2 );          /* cluster number at which the driver should start looking for free clusters */
			/* OFS_FSI_32_Reserved2		0x1F0 / zero's */
			FF_putLong( pucSectorBuffer, OFS_FSI_32_TrailSig, 0xAA550000 ); /* Will correct for endianness */

			FF_BlockWrite( pxIOManager, ulHiddenSectors + ulFSInfo, 1, pucSectorBuffer, pdFALSE );
			FF_BlockWrite( pxIOManager, ulHiddenSectors + ulFSInfo + ulBackupBootSector, 1, pucSectorBuffer, pdFALSE );
		}

		fatBeginLBA = ulHiddenSectors + ulFATReservedSectors;
		memset( pucSectorBuffer, '\0', 512 );
		switch( ucFATType )
		{
			case FF_T_FAT16:
				FF_putShort( pucSectorBuffer, 0, 0xFFF8 ); /* First FAT entry. */
				FF_putShort( pucSectorBuffer, 2, 0xFFFF ); /* RESERVED alloc. */
				break;
			case FF_T_FAT32:
				FF_putLong( pucSectorBuffer, 0, 0x0FFFFFF8 ); /* FAT32 FAT sig. */
				FF_putLong( pucSectorBuffer, 4, 0xFFFFFFFF ); /* RESERVED alloc. */
				FF_putLong( pucSectorBuffer, 8, 0x0FFFFFFF ); /* Root dir allocation. */
				break;
			default:
				break;
		}

		FF_BlockWrite( pxIOManager, ( uint32_t ) fatBeginLBA, 1, pucSectorBuffer, pdFALSE );
		FF_BlockWrite( pxIOManager, ( uint32_t ) fatBeginLBA + ulSectorsPerFAT, 1, pucSectorBuffer, pdFALSE );

		FF_PRINTF( "FF_Format: Clearing entire FAT (2 x %lu sectors):\n", ulSectorsPerFAT );
		{
		int32_t addr;

			memset( pucSectorBuffer, '\0', 512 );
			for( addr = fatBeginLBA+1;
				 addr < ( fatBeginLBA + ( int32_t ) ulSectorsPerFAT );
				 addr++ )
			{
				FF_BlockWrite( pxIOManager, ( uint32_t ) addr, 1, pucSectorBuffer, pdFALSE );
				FF_BlockWrite( pxIOManager, ( uint32_t ) addr + ulSectorsPerFAT, 1, pucSectorBuffer, pdFALSE );
			}
		}
		FF_PRINTF( "FF_Format: Clearing done\n" );
		dirBegin = fatBeginLBA + ( 2 * ulSectorsPerFAT );
#if( ffconfigTIME_SUPPORT != 0 )
		{
			FF_SystemTime_t	str_t;
			int16_t myShort;

			FF_GetSystemTime( &str_t );

			myShort = ( ( str_t.Hour << 11 ) & 0xF800 ) |
								( ( str_t.Minute  <<  5 ) & 0x07E0 ) |
								( ( str_t.Second   /  2 ) & 0x001F );
			FF_putShort( pucSectorBuffer, 22, ( uint32_t ) myShort );

			myShort = ( ( ( str_t.Year- 1980 )  <<  9 ) & 0xFE00 ) |
					   ( ( str_t.Month << 5 ) & 0x01E0 ) |
					   ( str_t.Day & 0x001F );
			FF_putShort( pucSectorBuffer, 24, ( uint32_t ) myShort);
		}
#endif	/* ffconfigTIME_SUPPORT */

		memcpy (pucSectorBuffer, "MY_DISK    ", 11);
		pucSectorBuffer[11] = FF_FAT_ATTR_VOLID;

		{
		int32_t lAddress;
		int32_t lLastAddress;

			if( iFAT16RootSectors != 0 )
			{
				lLastAddress = dirBegin + iFAT16RootSectors;
			}
			else
			{
				lLastAddress = dirBegin + ulSectorsPerCluster;
			}

			FF_PRINTF("FF_Format: Clearing root directory at %08lX: %lu sectors\n", dirBegin, lLastAddress - dirBegin );
			for( lAddress = dirBegin; lAddress < lLastAddress; lAddress++ )
			{
				FF_BlockWrite( pxIOManager, ( uint32_t ) lAddress, 1, pucSectorBuffer, 0u );
				if( lAddress == dirBegin )
				{
					memset( pucSectorBuffer, '\0', 512 );
				}
			}
		}
	}

	ffconfigFREE( pucSectorBuffer );

	return FF_ERR_NONE;
}

FF_Error_t FF_Partition( FF_Disk_t *pxDisk, FF_PartitionParameters_t *pParams )
{
	const uint32_t ulInterSpace = pParams->ulInterSpace ? pParams->ulInterSpace : 2048;  /* Hidden space between 2 extended partitions */
	BaseType_t xPartitionNumber;
	FF_Part_t pxPartitions[ ffconfigMAX_PARTITIONS ];
	uint32_t ulPartitionOffset; /* Pointer within partition table */
	FF_Buffer_t *pxSectorBuffer;
	uint8_t *pucBuffer;
	uint32_t ulSummedSizes = 0;	/* Summed sizes as a percentage or as number of sectors. */
	BaseType_t xPartitionCount = 0;
	BaseType_t xNeedExtended;
	uint32_t ulReservedSpace;
	uint32_t ulAvailable;
	FF_IOManager_t *pxIOManager = pxDisk->pxIOManager;


	/* Clear caching without flushing first. */
	FF_IOMAN_InitBufferDescriptors( pxIOManager );

	/* Avoid sanity checks by FF_BlockRead/Write. */
	pxIOManager->xPartition.ulTotalSectors = 0;

	/* Get the sum of sizes and number of actual partitions. */
	for( xPartitionNumber = 0; xPartitionNumber < ffconfigMAX_PARTITIONS; xPartitionNumber++ )
	{
		if( pParams->xSizes[ xPartitionNumber ] > 0 )
		{
			xPartitionCount++;
			ulSummedSizes += pParams->xSizes[ xPartitionNumber ];
		}
	}

	if( xPartitionCount == 0 )
	{
		xPartitionCount = 1;
		if( pParams->eSizeType == eSizeIsSectors)
		{
			pParams->xSizes[ 0 ] = pParams->ulSectorCount;
		}
		else
		{
			pParams->xSizes[ 0 ] = 100;
		}

		ulSummedSizes = pParams->xSizes[ 0 ];
	}

	/* Correct PrimaryCount if necessary. */
	if( pParams->xPrimaryCount > ( ( xPartitionCount > 4 ) ? 3 : xPartitionCount ) )
	{
		pParams->xPrimaryCount = ( xPartitionCount > 4 ) ? 3 : xPartitionCount;
	}

	/* Now see if extended is necessary. */
	xNeedExtended = ( xPartitionCount > pParams->xPrimaryCount );

	if( xNeedExtended != pdFALSE )
	{
		if( pParams->ulHiddenSectors < 4096 )
		{
			pParams->ulHiddenSectors = 4096;
		}

		ulReservedSpace = ulInterSpace * ( xPartitionCount - pParams->xPrimaryCount );
	}
	else
	{
		/* There must be at least 1 hidden sector. */
		if( pParams->ulHiddenSectors < 1 )
		{
			pParams->ulHiddenSectors = 1;
		}
		ulReservedSpace = 0;
	}

	ulAvailable = pParams->ulSectorCount - pParams->ulHiddenSectors - ulReservedSpace;

	/* Check validity of Sizes */
	switch( pParams->eSizeType )
	{
		case eSizeIsQuota:       /* Assign a quotum (sum of Sizes is free, all disk space will be allocated) */
			break;
		case eSizeIsPercent:  /* Assign a percentage of the available space (sum of Sizes must be <= 100) */
			if( ulSummedSizes > 100 )
			{
				return FF_FORMATPARTITION | FF_ERR_IOMAN_BAD_MEMSIZE;
			}
			ulSummedSizes = 100;
			break;
		case eSizeIsSectors:     /* Assign fixed number of sectors (512 byte each) */
			if( ulSummedSizes > ulAvailable )
			{
				return FF_FORMATPARTITION | FF_ERR_IOMAN_BAD_MEMSIZE;
			}
			break;
	}

	{
	uint32_t ulRemaining = ulAvailable;
	uint32_t ulLBA = pParams->ulHiddenSectors;

		/* Divide the available sectors among the partitions: */
		memset( pxPartitions, '\0', sizeof( pxPartitions ) );

		for( xPartitionNumber = 0; xPartitionNumber < xPartitionCount; xPartitionNumber++ )
		{
			if( pParams->xSizes[ xPartitionNumber ] > 0 )
			{
				uint32_t ulSize;
				switch( pParams->eSizeType )
				{
					case eSizeIsQuota:       /* Assign a quotum (sum of Sizes is free, all disk space will be allocated) */
					case eSizeIsPercent:  /* Assign a percentage of the available space (sum of Sizes must be <= 100) */
						ulSize = ( uint32_t ) ( ( ( uint64_t ) pParams->xSizes[ xPartitionNumber ] * ulAvailable) / ulSummedSizes );
						break;
					case eSizeIsSectors:     /* Assign fixed number of sectors (512 byte each) */
					default:                  /* Just for the compiler(s) */
						ulSize = pParams->xSizes[ xPartitionNumber ];
						break;
				}

				if( ulSize > ulRemaining )
				{
					ulSize = ulRemaining;
				}

				ulRemaining -= ulSize;
				pxPartitions[ xPartitionNumber ].ulSectorCount = ulSize;
				pxPartitions[ xPartitionNumber ].ucActive = 0x80;
				pxPartitions[ xPartitionNumber ].ulStartLBA = ulLBA; /* ulStartLBA might still change for logical partitions */
				pxPartitions[ xPartitionNumber ].ucPartitionID = 0x0B;
				ulLBA += ulSize;
			}
		}
	}

	if( xNeedExtended != pdFALSE )
	{
		/* Create at least 1 extended/logical partition */
		int index;
		/* Start of the big extended partition */
		unsigned extendedLBA = pParams->ulHiddenSectors;
		/* Where to write the table */
		uint32_t ulLBA = 0;
		/* Contents of the table */
		FF_Part_t writeParts[4];

		for( index = -1; index < xPartitionCount; index++ )
		{
		uint32_t ulNextLBA;

			memset (writeParts, '\0', sizeof( writeParts ) );
			if( index < 0 )
			{
			/* we're at secor 0: */
			/* write primary partitions, if any */
			/* create big extended partition */
			uint32_t ulStartLBA = pParams->ulHiddenSectors;
				for( xPartitionNumber = 0; xPartitionNumber < pParams->xPrimaryCount; xPartitionNumber++ )
				{
					writeParts[ xPartitionNumber ].ulStartLBA = ulStartLBA;
					writeParts[ xPartitionNumber ].ulSectorCount = pxPartitions[ xPartitionNumber ].ulSectorCount;
					writeParts[ xPartitionNumber ].ucActive = 0x80;
					writeParts[ xPartitionNumber ].ucPartitionID = 0x0B;
					ulStartLBA += writeParts[ xPartitionNumber ].ulSectorCount;
					index++;
				}
				extendedLBA = ulStartLBA;
				writeParts[ xPartitionNumber ].ulStartLBA = ulStartLBA;
				writeParts[ xPartitionNumber ].ulSectorCount = pParams->ulSectorCount - ulStartLBA;
				writeParts[ xPartitionNumber ].ucActive = 0x80;
				writeParts[ xPartitionNumber ].ucPartitionID = 0x05;
				ulNextLBA = ulStartLBA;
			}
			else
			{
				/* Create a logical partition with "ulSectorCount" sectors: */
				writeParts[ 0 ].ulStartLBA = ulInterSpace;
				writeParts[ 0 ].ulSectorCount = pxPartitions[index].ulSectorCount;
				writeParts[ 0 ].ucActive = 0x80;
				writeParts[ 0 ].ucPartitionID = 0x0B;
				if( index < xPartitionCount - 1 )
				{
					/* Next extended partition */
					writeParts[ 1 ].ulStartLBA = ulInterSpace + ulLBA - extendedLBA + writeParts[ 0 ].ulSectorCount;
					writeParts[ 1 ].ulSectorCount = pxPartitions[index+1].ulSectorCount + ulInterSpace;
					writeParts[ 1 ].ucActive = 0x80;
					writeParts[ 1 ].ucPartitionID = 0x05;
				}
				ulNextLBA = writeParts[ 1 ].ulStartLBA + extendedLBA;
			}
			pxSectorBuffer = FF_GetBuffer(pxIOManager, ( uint32_t ) ulLBA, ( uint8_t ) FF_MODE_WRITE );
			{
				if( pxSectorBuffer == NULL )
				{
					return FF_ERR_DEVICE_DRIVER_FAILED;
				}
			}
			pucBuffer = pxSectorBuffer->pucBuffer;
			memset ( pucBuffer, 0, 512 );
			memcpy ( pucBuffer + OFS_BPB_jmpBoot_24, "\xEB\x00\x90" "FreeRTOS", 11 );   /* Includes OFS_BPB_OEMName_64 */

			ulPartitionOffset = OFS_PTABLE_PART_0;
			for( xPartitionNumber = 0; xPartitionNumber < ffconfigMAX_PARTITIONS; xPartitionNumber++, ulPartitionOffset += 16 )
			{
				FF_putChar( pucBuffer, ulPartitionOffset + OFS_PART_ACTIVE_8,            writeParts[ xPartitionNumber ].ucActive );		/* 0x01BE 0x80 if active */
				FF_putChar( pucBuffer, ulPartitionOffset + OFS_PART_START_HEAD_8,        1 );											/* 0x001 / 0x01BF */
				FF_putShort(pucBuffer, ulPartitionOffset + OFS_PART_START_SEC_TRACK_16,  1 );											/* 0x002 / 0x01C0 */
				FF_putChar( pucBuffer, ulPartitionOffset + OFS_PART_ID_NUMBER_8,         writeParts[ xPartitionNumber ].ucPartitionID );/* 0x004 / 0x01C2 */
				FF_putChar( pucBuffer, ulPartitionOffset + OFS_PART_ENDING_HEAD_8,       0xFE );										/* 0x005 / 0x01C3 */
				FF_putShort(pucBuffer, ulPartitionOffset + OFS_PART_ENDING_SEC_TRACK_16, writeParts[ xPartitionNumber ].ulSectorCount );/* 0x006 / 0x01C4 */
				FF_putLong (pucBuffer, ulPartitionOffset + OFS_PART_STARTING_LBA_32,     writeParts[ xPartitionNumber ].ulStartLBA );	/* 0x008 / 0x01C6 This is important */
				FF_putLong (pucBuffer, ulPartitionOffset + OFS_PART_LENGTH_32,           writeParts[ xPartitionNumber ].ulSectorCount );/* 0x00C / 0x01CA Equal to total sectors */
			}
			pucBuffer[510] = 0x55;
			pucBuffer[511] = 0xAA;

			FF_ReleaseBuffer(pxIOManager, pxSectorBuffer );
			FF_FlushCache( pxIOManager );
			ulLBA = ulNextLBA;
		}
	}
	else
	{
		pxSectorBuffer = FF_GetBuffer( pxIOManager, 0, ( uint8_t ) FF_MODE_WRITE );
		{
			if( pxSectorBuffer == NULL )
			{
				return FF_ERR_DEVICE_DRIVER_FAILED;
			}
		}

		pucBuffer = pxSectorBuffer->pucBuffer;
		memset (pucBuffer, 0, 512 );
		memcpy (pucBuffer + OFS_BPB_jmpBoot_24, "\xEB\x00\x90" "FreeRTOS", 11 );   /* Includes OFS_BPB_OEMName_64 */
		ulPartitionOffset = OFS_PTABLE_PART_0;

		for( xPartitionNumber = 0; xPartitionNumber < ffconfigMAX_PARTITIONS; xPartitionNumber++ )
		{
			FF_putChar(  pucBuffer, ulPartitionOffset + OFS_PART_ACTIVE_8,            pxPartitions[ xPartitionNumber ].ucActive );		/* 0x01BE 0x80 if active */
			FF_putChar(  pucBuffer, ulPartitionOffset + OFS_PART_START_HEAD_8,        1 );         										/* 0x001 / 0x01BF */
			FF_putShort( pucBuffer, ulPartitionOffset + OFS_PART_START_SEC_TRACK_16,  1 );  											/* 0x002 / 0x01C0 */
			FF_putChar(  pucBuffer, ulPartitionOffset + OFS_PART_ID_NUMBER_8,         pxPartitions[ xPartitionNumber ].ucPartitionID );	/* 0x004 / 0x01C2 */
			FF_putChar(  pucBuffer, ulPartitionOffset + OFS_PART_ENDING_HEAD_8,       0xFE );     										/* 0x005 / 0x01C3 */
			FF_putShort( pucBuffer, ulPartitionOffset + OFS_PART_ENDING_SEC_TRACK_16, pxPartitions[ xPartitionNumber ].ulSectorCount );	/* 0x006 / 0x01C4 */
			FF_putLong(  pucBuffer, ulPartitionOffset + OFS_PART_STARTING_LBA_32,     pxPartitions[ xPartitionNumber ].ulStartLBA );	/* 0x008 / 0x01C6 This is important */
			FF_putLong(  pucBuffer, ulPartitionOffset + OFS_PART_LENGTH_32,           pxPartitions[ xPartitionNumber ].ulSectorCount );	/* 0x00C / 0x01CA Equal to total sectors */
			ulPartitionOffset += 16;
		}
		pucBuffer[ 510 ] = 0x55;
		pucBuffer[ 511 ] = 0xAA;

		FF_ReleaseBuffer( pxIOManager, pxSectorBuffer );
		FF_FlushCache( pxIOManager );
	}

	return FF_ERR_NONE;
}
