//
//
//

#define	SD_MMC_SPI_MEM 1

#include "ff_headers.h"

#include "logbuf.h"
#include "secCache.h"

#include "ff_flush.h"

extern BaseType_t FF_SemaphoreTaken( void *pxSemaphore );

FF_Error_t FF_FlushWrites( FF_IOManager_t *pxIOManager, BaseType_t xForced )
{
FF_Error_t xRetValue;

	if( ( pxIOManager == NULL ) || ( cache_dirt_count() == 0 ) )
	{
		xRetValue = FF_ERR_NONE;
	}
	else if( ( pxIOManager->ucPreventFlush != pdFALSE ) && ( xForced == pdFALSE ) )
	{
		xRetValue = FF_ERR_IOMAN_PARTITION_MOUNTED | FF_ERRFLAG;
	}
	else
	{
	BaseType_t rc = 0;
		if( xForced != pdFALSE )
		{
			FF_FlushCache( pxIOManager );
		}

//		if( FF_TrySemaphore( pxIOManager->pvSemaphore, xForced ? 5000 : 0 ) != pdFALSE )
		if( ( xForced != pdFALSE ) || ( FF_SemaphoreTaken( pxIOManager->pvSemaphore ) == pdFALSE ) )
		{
			rc = cache_flush( xForced );
//			FF_ReleaseSemaphore( pxIOManager->pvSemaphore );
		}
		xRetValue = rc;
	}
	return xRetValue;
}

FF_Error_t FF_StopFlush( FF_IOManager_t *pxIOManager, BaseType_t xFlag )
{
FF_Error_t xRetValue;

	if( pxIOManager == NULL )
	{
		xRetValue = 0;
	}
	else
	{
		vTaskSuspendAll();
		{
			xRetValue = pxIOManager->ucPreventFlush;
			if( xFlag != FLUSH_ENABLE )
			{
				xRetValue++;
			}
			else if ( xRetValue > 0 )
			{
				xRetValue--;
			}
			pxIOManager->ucPreventFlush = xRetValue;
		}
		xTaskResumeAll();

	}

	return xRetValue;
}
