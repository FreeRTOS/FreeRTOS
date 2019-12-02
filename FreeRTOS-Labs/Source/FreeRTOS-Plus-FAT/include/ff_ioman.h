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
 *	@file		ff_ioman.h
 *	@ingroup	IOMAN
 **/

#ifndef _FF_IOMAN_H_
#define _FF_IOMAN_H_

#ifdef __cplusplus
extern "C" {
#endif

#include <stdlib.h>							/* Use of malloc() */

#ifndef PLUS_FAT_H
	#error this header will be included from "plusfat.h"
#endif

#define FF_T_FAT12				0x0A
#define FF_T_FAT16				0x0B
#define FF_T_FAT32				0x0C

#define FF_MODE_READ			0x01		/* Buffer / FILE Mode for Read Access. */
#define	FF_MODE_WRITE			0x02		/* Buffer / FILE Mode for Write Access. */
#define FF_MODE_APPEND			0x04		/* FILE Mode Append Access. */
#define	FF_MODE_CREATE			0x08		/* FILE Mode Create file if not existing. */
#define FF_MODE_TRUNCATE		0x10		/* FILE Mode Truncate an Existing file. */
#define FF_MODE_VIRGIN			0x40		/* Buffer mode: do not fetch content from disk. Used for write-only buffers. */
#define FF_MODE_DIR				0x80		/* Special Mode to open a Dir. (Internal use ONLY!) */

#define FF_MODE_RD_WR			( FF_MODE_READ | FF_MODE_WRITE ) /* Just for bit filtering. */

/* The buffer write-only mode saves a fetch from disk.
The write-only mode is used when a buffer is needed just
for clearing sectors. */
#define	FF_MODE_WR_ONLY			( FF_MODE_VIRGIN | FF_MODE_WRITE )		/* Buffer for Write-only Access (Internal use ONLY!) */

#define FF_BUF_MAX_HANDLES		0xFFFF		/* Maximum number handles sharing a buffer. (16 bit integer, we don't want to overflow it!) */

#define FF_MAX_ENTRIES_PER_DIRECTORY	0xFFFF
#define FF_SIZEOF_SECTOR				512
#define FF_SIZEOF_DIRECTORY_ENTRY		32

#ifndef pdTRUE_SIGNED
	/* Temporary solution: eventually the defines below will appear
	in 'Source\include\projdefs.h' */
	#define pdTRUE_SIGNED		pdTRUE
	#define pdFALSE_SIGNED		pdFALSE
	#define pdTRUE_UNSIGNED		( ( UBaseType_t ) 1u )
	#define pdFALSE_UNSIGNED	( ( UBaseType_t ) 0u )
#endif
/**
 *	I/O Driver Definitions
 *	Provide access to any Block Device via the following interfaces.
 *	Returns the number of blocks actually read or written.
 **/

/**
 *	A special information structure for the FreeRTOS+FAT mass storage device
 *	driver model.
 **/
typedef struct
{
	uint16_t BlkSize;
	uint32_t TotalBlocks;
} FF_DeviceInfo_t;

#if( ffconfigHASH_CACHE != 0 )
	#define FF_HASH_TABLE_ENTRY_COUNT		( ( ffconfigHASH_TABLE_SIZE + 3 ) / 4 )

	struct xHASH_TABLE
	{
		uint32_t ulDirCluster;	/* The Starting Cluster of the dir that the hash represents. */
		uint32_t ulNumHandles;	/* Number of active Handles using this hash table. */
		uint32_t ulMisses;		/* Number of times this Hash Table was missed, (i.e. how redundant it is). */
		uint32_t ulBitTable[ FF_HASH_TABLE_ENTRY_COUNT ];
	};

	typedef struct xHASH_TABLE FF_HashTable_t;

	void FF_ClearHash( FF_HashTable_t *pxHash, uint32_t ulHash );
	void FF_SetHash( FF_HashTable_t *pxHash, uint32_t ulHash );
	BaseType_t FF_isHashSet( FF_HashTable_t *pxHash, uint32_t ulHash );
#endif /* ffconfigHASH_CACHE */

/* A forward declaration for the I/O manager, to be used in 'struct xFFDisk'. */
struct _FF_IOMAN;
struct xFFDisk;

typedef void ( *FF_FlushApplicationHook )( struct xFFDisk *pxDisk );

/*
 * Some low-level drivers also need to flush data to a device.
 * Use an Application hook that will be called every time when
 * FF_FlushCache() is called. The semaphore will still be taken
 * to avoid unwanted reentrancy.
 * For example:
 *
 *     void FTL_FlushData( struct xFFDisk *pxDisk )
 *     {
 *         // You may or may not inspect 'pxDisk'
 *         FTL_FlushTableCache();
 *     }
 *
 * Make sure you bind the function to the disc object, right after creation:
 *
 *    pxDisk->fnFlushApplicationHook = FTL_FlushData;
 */

/* Structure that contains fields common to all media drivers, and can be
extended to contain additional fields to tailor it for use with a specific media
type. */
struct xFFDisk
{
	struct
	{
		/* Flags that can optionally be used by the media driver to ensure the
		disk has been initialised, registered and mounted before it is accessed. */
		uint32_t bIsInitialised : 1;
		uint32_t bIsMounted : 1;
		uint32_t spare0 : 5;

		/* The partition number on the media described by this structure. */
		uint32_t bPartitionNumber : 8;
		uint32_t spare1 : 16;
	} xStatus;

	/* Provided to allow this structure to be extended to include additional
	attributes that are specific to a media type. */
	void * pvTag;

	/* Points to input and output manager used by the disk described by this
	structure. */
	struct _FF_IOMAN *pxIOManager;

	/* The number of sectors on the disk. */
	uint32_t ulNumberOfSectors;

	/* See comments here above. */
	FF_FlushApplicationHook fnFlushApplicationHook;

	/* Field that can optionally be set to a signature that is unique to the
	media.  Read and write functions can check the ulSignature field to validate
	the media type before they attempt to access the pvTag field, or perform any
	read and write operations. */
	uint32_t ulSignature;
};

typedef struct xFFDisk FF_Disk_t;

typedef int32_t ( *FF_WriteBlocks_t ) ( uint8_t *pucBuffer, uint32_t ulSectorAddress, uint32_t ulCount, FF_Disk_t *pxDisk );
typedef int32_t ( *FF_ReadBlocks_t ) ( uint8_t *pucBuffer, uint32_t ulSectorAddress, uint32_t ulCount, FF_Disk_t *pxDisk );

/**
 *	@public
 *	@brief	Describes the block device driver interface to FreeRTOS+FAT.
 **/
typedef struct
{
	FF_WriteBlocks_t	fnpWriteBlocks;	/* Function Pointer, to write a block(s) from a block device. */
	FF_ReadBlocks_t	fnpReadBlocks;	/* Function Pointer, to read a block(s) from a block device. */
	FF_Disk_t *pxDisk;				/* Earlier called 'pParam': pointer to some parameters e.g. for a Low-Level Driver Handle. */
} FF_BlockDevice_t;

/**
 *	@private
 *	@brief	FreeRTOS+FAT handles memory with buffers, described as below.
 *	@note	This may change throughout development.
 **/
typedef struct
{
	uint32_t		ulSector;		/* The LBA of the Cached sector. */
	uint32_t		ulLRU;			/* For the Least Recently Used algorithm. */
	uint8_t			*pucBuffer;		/* Pointer to the cache block. */
	uint32_t		ucMode : 8,		/* Read or Write mode. */
					bModified : 1,	/* If the sector was modified since read. */
					bValid : 1;		/* Initially FALSE. */
	uint16_t		usNumHandles;	/* Number of objects using this buffer. */
	uint16_t		usPersistance;	/* For the persistance algorithm. */
} FF_Buffer_t;

typedef struct
{
#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	FF_T_WCHAR pcPath[ ffconfigMAX_FILENAME ];
#else
	char pcPath[ ffconfigMAX_FILENAME ];
#endif
	uint32_t ulDirCluster;
} FF_PathCache_t;

/**
 *	@private
 *	@brief	FreeRTOS+FAT identifies a partition with the following data.
 *	@note	This may shrink as development and optimisation goes on.
 **/
typedef struct
{
	 uint32_t		ulBeginLBA;			/* LBA start address of the partition. */
	 uint32_t		ulFATBeginLBA;		/* LBA of the FAT tables. */
	 uint32_t		ulSectorsPerFAT;	/* Number of sectors per Fat. */
	 uint32_t		ulTotalSectors;
	 uint32_t		ulDataSectors;
#if( ffconfigWRITE_FREE_COUNT != 0 )
	 uint32_t    	ulFSInfoLBA;		/* LBA of the FSINFO sector. */
#endif
	 uint32_t		ulRootDirSectors;
	 uint32_t		ulFirstDataSector;
	 uint32_t		ulClusterBeginLBA;	/* LBA of first cluster. */
	 uint32_t		ulNumClusters;		/* Number of clusters. */
	 uint32_t		ulRootDirCluster;	/* Cluster number of the root directory entry. */
	 uint32_t		ulLastFreeCluster;
	 uint32_t		ulFreeClusterCount;	/* Records free space on mount. */
	 uint32_t		ulSectorsPerCluster;/* Number of sectors per Cluster. */

	 char			pcVolumeLabel[ 12 ];/* Volume Label of the partition. */

	 uint16_t		usBlkSize;			/* Size of a Sector Block in bytes. */
	 uint16_t		usReservedSectors;

	 uint8_t		ucType;				/* Partition Type Identifier. */
	 uint8_t      	ucBlkFactor;		/* Scale Factor for block sizes above 512! */
	 uint8_t		ucNumFATS;			/* Number of FAT tables. */
	 uint8_t		ucPartitionMounted;	/* pdTRUE if the partition is mounted, otherwise pdFALSE. */

#if( ffconfigPATH_CACHE != 0 )
	 FF_PathCache_t	pxPathCache[ffconfigPATH_CACHE_DEPTH];
	 uint32_t		ulPCIndex;
#endif
} FF_Partition_t;



/**
 *	@public
 *	@brief	FF_IOManager_t Object description.
 *
 *	FreeRTOS+FAT functions around an object like this.
 **/
#define FF_FAT_LOCK			0x01	/* Lock bit mask for FAT table locking. */
#define FF_DIR_LOCK			0x02	/* Lock bit mask for DIR modification locking. */
#define FF_BUF_LOCK			0x04	/* Lock bit mask for buffers. */

/**
 *	@public
 *	@brief	FF_IOManager_t Object. A developer should not touch these values.
 *
 **/
typedef struct _FF_IOMAN
{
	FF_BlockDevice_t	xBlkDevice;			/* Pointer to a Block device description. */
	FF_Partition_t	xPartition;			/* A partition description. */
	FF_Buffer_t		*pxBuffers;			/* Pointer to an array of buffer descriptors. */
	void			*pvSemaphore;		/* Pointer to a Semaphore object. (For buffer description modifications only!). */
	void			*FirstFile;			/* Pointer to the first File object. */
	void			*xEventGroup;		/* An event group, used for locking FAT, DIR and Buffers. Replaces ucLocks. */
	uint8_t			*pucCacheMem;		/* Pointer to a block of memory for the cache. */
	uint16_t		usSectorSize;		/* The sector size that IOMAN is configured to. */
	uint16_t		usCacheSize;		/* Size of the cache in number of Sectors. */
	uint8_t			ucPreventFlush;		/* Flushing to disk only allowed when 0. */
	uint8_t			ucFlags;			/* Bit-Mask: identifying allocated pointers and other flags */
#if( ffconfigHASH_CACHE != 0 )
	FF_HashTable_t	xHashCache[ ffconfigHASH_CACHE_DEPTH ];
#endif
	void			*pvFATLockHandle;
} FF_IOManager_t;

/* Bit values for 'FF_IOManager_t::ucFlags': */
/* Memory Allocation testing and other flags. */
#define	FF_IOMAN_ALLOC_BUFDESCR	0x01	/* Flags the pxBuffers pointer is allocated. */
#define	FF_IOMAN_ALLOC_BUFFERS	0x02	/* Flags the pucCacheMem pointer is allocated. */
#define	FF_IOMAN_BLOCK_DEVICE_IS_REENTRANT		0x10	/* When true, ffRead/ffWrite are not protected by a semaphore. */
#if( ffconfigREMOVABLE_MEDIA != 0 )
	#define	FF_IOMAN_DEVICE_IS_EXTRACTED		0x20
#endif /* ffconfigREMOVABLE_MEDIA */

typedef struct xFF_CREATION_PARAMETERS
{
	uint8_t *pucCacheMemory;		/* User provided memory, or use NULL to malloc the cache memory. */
	uint32_t ulMemorySize;			/* Size of the cache memory, must be a multiple of 'ulSectorSize'. */
	BaseType_t ulSectorSize;		/* Sector size, unit for reading/writing to the disk, normally 512 bytes. */
	FF_WriteBlocks_t fnWriteBlocks;	/* A function to write sectors to the device. */
	FF_ReadBlocks_t fnReadBlocks;	/* A function to read sectors from the device. */
	FF_Disk_t *pxDisk;				/* Some properties of the disk driver. */
	void *pvSemaphore;				/* Pointer to a Semaphore object. */
	BaseType_t xBlockDeviceIsReentrant;	/* Make non-zero if ffRead/ffWrite are re-entrant. */
} FF_CreationParameters_t;

/*---------- PROTOTYPES (in order of appearance). */

/* PUBLIC (Interfaces): */
FF_IOManager_t *FF_CreateIOManger( FF_CreationParameters_t *pxParameters, FF_Error_t *pError );
FF_Error_t FF_DeleteIOManager( FF_IOManager_t *pxIOManager);
FF_Error_t FF_Mount( FF_Disk_t *pxDisk, BaseType_t xPartitionNumber );
FF_Error_t FF_Unmount( FF_Disk_t *pxDisk );
FF_Error_t FF_FlushCache( FF_IOManager_t *pxIOManager );
static portINLINE BaseType_t FF_Mounted( FF_IOManager_t *pxIOManager )
{
	return pxIOManager && pxIOManager->xPartition.ucPartitionMounted;
}

int32_t FF_GetPartitionBlockSize(FF_IOManager_t *pxIOManager);

#if( ffconfig64_NUM_SUPPORT != 0 )
	uint64_t FF_GetVolumeSize( FF_IOManager_t *pxIOManager );
#else
	uint32_t FF_GetVolumeSize( FF_IOManager_t *pxIOManager );
#endif

/* PUBLIC  (To FreeRTOS+FAT Only): */
int32_t FF_BlockRead( FF_IOManager_t *pxIOManager, uint32_t ulSectorLBA, uint32_t ulNumSectors, void *pBuffer, BaseType_t aSemLocked );
int32_t FF_BlockWrite( FF_IOManager_t *pxIOManager, uint32_t ulSectorLBA, uint32_t ulNumSectors, void *pBuffer, BaseType_t aSemLocked );
FF_Error_t FF_IncreaseFreeClusters( FF_IOManager_t *pxIOManager, uint32_t Count );
FF_Error_t FF_DecreaseFreeClusters( FF_IOManager_t *pxIOManager, uint32_t Count );
FF_Buffer_t *FF_GetBuffer( FF_IOManager_t *pxIOManager, uint32_t ulSector, uint8_t Mode );
FF_Error_t FF_ReleaseBuffer( FF_IOManager_t *pxIOManager, FF_Buffer_t *pBuffer );

/* 'Internal' to FreeRTOS+FAT. */
typedef struct _SPart
{
	uint32_t ulStartLBA;		/* FF_FAT_PTBL_LBA */
	uint32_t ulSectorCount;		/* FF_FAT_PTBL_SECT_COUNT */
	uint32_t
			ucActive : 8,		/* FF_FAT_PTBL_ACTIVE */
			ucPartitionID : 8,	/* FF_FAT_PTBL_ID */
			bIsExtended : 1;
} FF_Part_t;

typedef struct _SPartFound
{
	int iCount;
	FF_Part_t pxPartitions[ffconfigMAX_PARTITIONS];
} FF_SPartFound_t;

/* This function will parse the 4 entries in a partition table: */
void FF_ReadParts( uint8_t *pucBuffer, FF_Part_t *pxParts );

/* FF_PartitionCount() has now been replaced by FF_PartitionSearch()
 * It will enumerate all valid partitions found
 * If sector-0 happens to be a valid MBR, 1 partition will be returned
 */
FF_Error_t FF_PartitionSearch( FF_IOManager_t *pxIOManager, FF_SPartFound_t *pPartsFound );

/* HT : for debugging only. */
BaseType_t xIsFatSector( FF_IOManager_t *pxIOManager, uint32_t ulSectorNr );
BaseType_t xNeedLogging( FF_IOManager_t *pxIOManager );
BaseType_t xIsRootDirSector( FF_IOManager_t *pxIOManager, uint32_t ulSectorNr );
const char *pcSectorType( FF_IOManager_t *pxIOManager, uint32_t ulSectorNr );

/* Needed to make this public/private to be used in FF_Partition/FF_Format. */
void FF_IOMAN_InitBufferDescriptors( FF_IOManager_t *pxIOManager );

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif
