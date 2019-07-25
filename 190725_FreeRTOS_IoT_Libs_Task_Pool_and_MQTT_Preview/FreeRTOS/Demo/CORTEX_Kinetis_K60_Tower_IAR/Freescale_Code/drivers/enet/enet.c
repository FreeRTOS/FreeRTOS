/*
 * File:    enet.c
 * Purpose: Driver for the ENET controller
 *
 * Notes:
 */

#include "common.h"
#include "enet.h"
#include "nbuf.h"
#include "eth.h"


/********************************************************************/
/* Initialize the MIB counters
 *
 * Parameters:
 *  ch      FEC channel
 */
void
enet_mib_init(int ch)
{
//To do
}
/********************************************************************/
/* Display the MIB counters
 *
 * Parameters:
 *  ch      FEC channel
 */
void
enet_mib_dump(int ch)
{
//To do
}
/********************************************************************/
/*
 * Set the duplex on the selected FEC controller
 *
 * Parameters:
 *  ch      FEC channel
 *  duplex  enet_MII_FULL_DUPLEX or enet_MII_HALF_DUPLEX
 */
void
enet_duplex (int ch, ENET_DUPLEX duplex)
{
    switch (duplex)
    {
        case MII_HDX:
            ENET_RCR/*(ch)*/ |= ENET_RCR_DRT_MASK;
            ENET_TCR/*(ch)*/ &= (uint32_t)~ENET_TCR_FDEN_MASK;
            break;
        case MII_FDX:
        default:
            ENET_RCR/*(ch)*/ &= ~ENET_RCR_DRT_MASK;
            ENET_TCR/*(ch)*/ |= ENET_TCR_FDEN_MASK;
            break;
    }
}

/********************************************************************/
/*
 * Generate the hash table settings for the given address
 *
 * Parameters:
 *  addr    48-bit (6 byte) Address to generate the hash for
 *
 * Return Value:
 *  The 6 most significant bits of the 32-bit CRC result
 */
uint8_t
enet_hash_address(const uint8_t* addr)
{
    uint32_t crc;
    uint8_t byte;
    int i, j;

    crc = 0xFFFFFFFF;
    for(i=0; i<6; ++i)
    {
        byte = addr[i];
        for(j=0; j<8; ++j)
        {
            if((byte & 0x01)^(crc & 0x01))
            {
                crc >>= 1;
                crc = crc ^ 0xEDB88320;
            }
            else
                crc >>= 1;
            byte >>= 1;
        }
    }
    return (uint8_t)(crc >> 26);
}
/********************************************************************/
/*
 * Set the Physical (Hardware) Address and the Individual Address
 * Hash in the selected FEC
 *
 * Parameters:
 *  ch  FEC channel
 *  pa  Physical (Hardware) Address for the selected FEC
 */
void
enet_set_address (int ch, const uint8_t *pa)
{
    uint8_t crc;

    /*
     * Set the Physical Address
     */
    ENET_PALR/*(ch)*/ = (uint32_t)((pa[0]<<24) | (pa[1]<<16) | (pa[2]<<8) | pa[3]);
    ENET_PAUR/*(ch)*/ = (uint32_t)((pa[4]<<24) | (pa[5]<<16));

    /*
     * Calculate and set the hash for given Physical Address
     * in the  Individual Address Hash registers
     */
    crc = enet_hash_address(pa);
    if(crc >= 32)
        ENET_IAUR/*(ch)*/ |= (uint32_t)(1 << (crc - 32));
    else
        ENET_IALR/*(ch)*/ |= (uint32_t)(1 << crc);
}
/********************************************************************/
/*
 * Reset the selected FEC controller
 *
 * Parameters:
 *  ch      FEC channel
 */
void
enet_reset (int ch)
{
    int i;

    /* Set the Reset bit and clear the Enable bit */
    ENET_ECR/*(ch)*/ = ENET_ECR_RESET_MASK;

    /* Wait at least 8 clock cycles */
    for (i=0; i<10; ++i)
        asm( "NOP" );
}
/********************************************************************/
/*
 * Initialize the selected FEC
 *
 * Parameters:
 *  config: ENET parameters
 *
 *
 */
void
enet_init (ENET_CONFIG *config)
{
    /* Clear the Individual and Group Address Hash registers */
    ENET_IALR/*(ch)*/ = 0;
    ENET_IAUR/*(ch)*/ = 0;
    ENET_GALR/*(ch)*/ = 0;
    ENET_GAUR/*(ch)*/ = 0;

    /* Set the Physical Address for the selected FEC */
    enet_set_address(config->ch, config->mac);

    /* Mask all FEC interrupts */
    ENET_EIMR/*(ch)*/ = 0;//FSL:ENET_EIMR_MASK_ALL_MASK;

    /* Clear all FEC interrupt events */
    ENET_EIR/*(ch)*/ = 0xFFFFFFFF;//FSL:ENET_EIR_CLEAR_ALL_MASK;
    
    /* Initialize the Receive Control Register */
    ENET_RCR/*(ch)*/ = 0
        | ENET_RCR_MAX_FL(ETH_MAX_FRM)
        | ENET_RCR_MII_MODE_MASK /*always*/
        | ENET_RCR_CRCFWD_MASK;  /*no CRC pad required*/

    if ( config->interface == mac_rmii )
    {
      ENET_RCR/*(ch)*/ |= ENET_RCR_RMII_MODE_MASK;
      
      /*only set speed in RMII mode*/
      if( config->speed == MII_10BASET )
      {
         ENET_RCR/*(ch)*/ |= ENET_RCR_RMII_10T_MASK;
      }
    }/*no need to configure MAC MII interface*/ 
    
    ENET_TCR/*(ch)*/ = 0;    
    
    /* Set the duplex */
    enet_duplex(config->ch, config->duplex);        
        
    if (config->prom)
    {
        ENET_RCR/*(ch)*/ |= ENET_RCR_PROM_MASK; 
    } 
    
#ifdef ENHANCED_BD
    ENET_ECR/*(ch)*/ = ENET_ECR_EN1588_MASK;
#else
    ENET_ECR/*(ch)*/ = 0;//clear register
#endif

    if(config->loopback == INTERNAL_LOOPBACK)
    {
        /*seems like RMII internal loopback works, even if it's not supported*/
        ENET_RCR/*(0)*/ |= ENET_RCR_LOOP_MASK;
    }
}
/********************************************************************/
void
enet_start (int ch)
{
  // Enable FEC
  ENET_ECR/*(ch)*/ |= ENET_ECR_ETHEREN_MASK;
}

/********************************************************************/
int 
enet_wait_for_frame_receive(int ch, int timeout)
{
	int i, return_val = 1;
        
	for (i=0; i < timeout; i++)
	{
		if (ENET_EIR/*(ch)*/ & ENET_EIR_RXF_MASK)
		{
			ENET_EIR/*(ch)*/ = ENET_EIR_RXF_MASK;
			break;		
		}
	}

	if(i == timeout)
	{
		return_val = 0;
	}
	return return_val;
}
/********************************************************************/



