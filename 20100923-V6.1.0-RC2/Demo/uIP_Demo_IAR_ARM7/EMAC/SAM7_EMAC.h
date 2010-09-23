#ifndef SAM_7_EMAC_H
#define SAM_7_EMAC_H


/*
 * Initialise the EMAC driver.  If successful a semaphore is returned that
 * is used by the EMAC ISR to indicate that Rx packets have been received.
 * If the initialisation fails then NULL is returned.
 */
xSemaphoreHandle xEMACInit( void );

/*
 * Send the current uIP buffer.  This copies the uIP buffer to one of the
 * EMAC Tx buffers, then indicates to the EMAC that the buffer is ready.
 */
long lEMACSend( void );

/*
 * Called in response to an EMAC Rx interrupt.  Copies the received frame
 * into the uIP buffer.
 */
unsigned long ulEMACPoll( void );

#endif
