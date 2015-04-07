/* ----------------------------------------------------------------------------
 *         SAM Software Package License  
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/** \file */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "chip.h"

#include <assert.h>




/**
 * \brief Check if Level 2 cache is enable.
 */
unsigned int L2CC_IsEnabled(L2cc* pL2CC)
{
  return ((pL2CC->L2CC_CR) & L2CC_CR_L2CEN);  
}

/**
 * \brief Enable Level 2 cache.
 */

void L2CC_Enable(L2cc* pL2CC)
{
  pL2CC->L2CC_CR |= L2CC_CR_L2CEN;
  TRACE_INFO("L2 cache is enabled");
}

/**
 * \brief Disbale Level 2 cache.
 */

void L2CC_Disable(L2cc* pL2CC)
{  
  pL2CC->L2CC_CR &= (!L2CC_CR_L2CEN);
  TRACE_INFO("L2 cache is Disabled");
}
   
/**
 * \brief Configures Level 2 cache as exclusive cache.
 */
void L2CC_ExclusiveCache(L2cc* pL2CC, uint8_t Enable)
{
  uint32_t Aux_Cfg;
  if(L2CC_IsEnabled(pL2CC))
  {
    pL2CC->L2CC_CR = DISABLE;
  }
  Aux_Cfg = pL2CC->L2CC_ACR;
  if(Enable)
  {
    CP15_ExclusiveCache();
    Aux_Cfg |= L2CC_ACR_EXCC;
    TRACE_INFO("L2 Exclusive mode Enabled\n\r");
  }
  else
  {
    CP15_NonExclusiveCache();
    Aux_Cfg &= ~L2CC_ACR_EXCC;
    TRACE_INFO("L2 Exclusive mode Disabled\n\r");
  }
  
  pL2CC->L2CC_ACR |= Aux_Cfg;
  
}

/**
 * \brief Configures Level 2 cache RAM Latency (Tag and Data).
 * \param pLat  Structure containing RAM Tag and Data latencies
 */
void L2CC_ConfigLatRAM(L2cc* pL2CC, RAMLatencyControl  *pLat)
{
  if(L2CC_IsEnabled(pL2CC))
  {
    pL2CC->L2CC_CR = DISABLE;
  }
  
  pL2CC->L2CC_TRCR = (L2CC_TRCR_TSETLAT(pLat->TagRAM.SetupLAT) | L2CC_TRCR_TRDLAT(pLat->TagRAM.ReadLAT) | L2CC_TRCR_TWRLAT(pLat->TagRAM.WriteLAT));
  pL2CC->L2CC_DRCR = (L2CC_DRCR_DSETLAT(pLat->DataRAM.SetupLAT) | L2CC_DRCR_DRDLAT(pLat->DataRAM.ReadLAT) | L2CC_DRCR_DWRLAT(pLat->DataRAM.WriteLAT));
  
}


/**
 * \brief Configures Level 2 cache.
 * \param L2cc_Config  Configuration values to put in Auxiliary, prefetch, debug and powercontrol registers
 */
void L2CC_Config(L2cc* pL2CC, L2CC_Control L2cc_Config)
{
  uint32_t AuxiliaryControl, DebugControl, PrefetchControl, PowerControl;
  
  if(L2cc_Config.OFFSET_Val >31)
  {
    assert(0);
  }
  if((L2cc_Config.OFFSET_Val >7) && (L2cc_Config.OFFSET_Val <15))
  {
    assert(0);
  }
  if((L2cc_Config.OFFSET_Val >15) && (L2cc_Config.OFFSET_Val <23))
  {
    assert(0);
  }
  if((L2cc_Config.OFFSET_Val >23) && (L2cc_Config.OFFSET_Val <31))
  {
    assert(0);
  }
  
//  if( ((L2cc_Config.IDLEN_Val==1) || (L2cc_Config.DLFWRDIS_Val==0)) && L2cc_Config.DLEN_Val==0)
//  {
//    TRACE_ERROR(" DLEN is not enabled for Double Line fill");
//    assert(0);
//  }
  
  if(L2CC_IsEnabled(pL2CC))
  {
    pL2CC->L2CC_CR = DISABLE;
  }
  
  AuxiliaryControl = ((L2cc_Config.HPSO_Val  << 10)  | 
                      (L2cc_Config.SBDLE_Val << 11)  |
                      (L2cc_Config.SAIE_Val  << 13)  |
                      (L2cc_Config.EMBEN_Val << 20)  |
                      (L2cc_Config.PEN_Val   << 21)  |
                      (L2cc_Config.SAOEN_Val << 22)  |
                      (L2CC_ACR_FWA(L2cc_Config.FWA_Val))   |
                      (L2cc_Config.CRPOL_Val << 25) |
                      (L2cc_Config.NSLEN_Val << 26) |
                      (L2cc_Config.NSIAC_Val << 27) |
                      (L2cc_Config.DPEN_Val  << 28) |
                      (L2cc_Config.IPEN_Val  << 29) );
                        
                       

    DebugControl =   ((L2cc_Config.DCL_Val   << 0)   | 
                      (L2cc_Config.DWB_Val <<   1) );
                         
    PrefetchControl = ((L2cc_Config.OFFSET_Val  << 0)   | 
                      (L2cc_Config.NSIDEN_Val   << 21)  |
                      (L2cc_Config.IDLEN_Val    << 23)  |
                      (L2cc_Config.PDEN_Val     << 24)  |
                      (L2cc_Config.DLFWRDIS_Val << 27)  |
                      (L2cc_Config.DPEN_Val     << 28)  |
                      (L2cc_Config.IPEN_Val     << 29)  |
                      (L2cc_Config.DLEN_Val     << 30));
                            
    PowerControl =    ((L2cc_Config.DCL_Val  << 0)  | 
                      (L2cc_Config.DWB_Val   << 1));
                        
  pL2CC->L2CC_ACR  = AuxiliaryControl;   
  
  pL2CC->L2CC_DCR = DebugControl;
  
  pL2CC->L2CC_PCR = PrefetchControl;
  
  pL2CC->L2CC_POWCR = PowerControl;
   
}


/**
 * \brief Enables Data prefetch on L2
 */
void L2CC_DataPrefetchEnable(L2cc* pL2CC )
{  

  pL2CC->L2CC_PCR |= L2CC_PCR_DATPEN;
    
}
             

/**
 * \brief Enables instruction prefetch on L2
 */
void L2CC_InstPrefetchEnable(L2cc* pL2CC )
{

  pL2CC->L2CC_PCR |= L2CC_PCR_INSPEN;  
  
}


/**
 * \brief Enables instruction prefetch on L2
 */
void L2CC_EnableResetCounter(L2cc* pL2CC , uint8_t EvenetCounter)
{

  assert((EvenetCounter>3)?0:1);
  
  pL2CC->L2CC_ECR = (L2CC_ECR_EVCEN | (EvenetCounter << 1 ));  
  
}

/**
 * \brief Configures Event of Level 2 cache.
 * \param EventCounter  Eventcounter 1 or 0
 * \param Source  Event Genration source
 * \param IntGen  Event Counter Interrupt Generation condition
 */
void L2CC_EventConfig(L2cc* pL2CC, uint8_t EventCounter, uint8_t Source, uint8_t IntGen)
{
  if(L2CC_IsEnabled(pL2CC))
  {
    pL2CC->L2CC_CR = DISABLE;
  }
  
  assert((EventCounter > 1)?0:1);
  
  if(!EventCounter)
  {
    pL2CC->L2CC_ECFGR0 = (Source | IntGen);  
  }
  else
  {
    pL2CC->L2CC_ECFGR1 = (Source | IntGen );  
  }
   
}


/**
 * \brief Reads Eventcounter value.
 * \param EventCounter  choose Eventcounter 1 or 0
 */
unsigned int L2CC_EventCounterValue(L2cc* pL2CC, uint8_t EventCounter)
{
    

  assert((EventCounter > 1)?0:1);
  
  if(!EventCounter)
  {
    return pL2CC->L2CC_EVR0;  
  }
  else
  {
    return pL2CC->L2CC_EVR1;
  }
  
}

/**
 * \brief Enable interrupts
 * \param ITSource  Interrupt source
 */
void L2CC_EnableIT(L2cc* pL2CC, uint16_t ITSource)
{
  pL2CC->L2CC_IMR  |= ITSource;
}


/**
 * \brief Disable interrupts
 * \param ITSource  Interrupt source
 */
void L2CC_DisableIT(L2cc* pL2CC, uint16_t ITSource)
{
  pL2CC->L2CC_IMR  &= (!ITSource);
}


/**
 * \brief Enabled interrupt's raw status
 * \param ITSource  Interrupt source
 */
unsigned short L2CC_ITStatusRaw(L2cc* pL2CC, uint16_t ITSource)
{
  return ((pL2CC->L2CC_RISR)  & ITSource)?1:0;
}

/**
 * \brief Status of masked interrupts
 * \param ITSource  Interrupt source
 */
unsigned short L2CC_ITStatusMask(L2cc* pL2CC, uint16_t ITSource)
{
   return ((pL2CC->L2CC_MISR)  & ITSource)?1:0;
}

/**
 * \brief Clear interrupts
 * \param ITSource  Interrupt source
 */
void L2CC_ITClear(L2cc* pL2CC, uint16_t ITSource)
{
    pL2CC->L2CC_ICR  |= ITSource;
}

                       
/**
 * \brief Poll SPNIDEN signal
 */
uint8_t L2CC_PollSPNIDEN(L2cc* pL2CC)
{
    return ((pL2CC->L2CC_DCR  & L2CC_DCR_SPNIDEN) >> 2);
}


/**
 * \brief Synchronizes the L2 cache
 */
void L2CC_CacheSync(L2cc* pL2CC)
{
   while((pL2CC->L2CC_CSR) & L2CC_CSR_C);
   pL2CC->L2CC_CSR = L2CC_CSR_C;
   while((pL2CC->L2CC_CSR) & L2CC_CSR_C);
}

/**
 * \brief Invalidate cache by Physical addersse
 * \param P_Address  Physical addresse
 */
void L2CC_InvalidatePAL(L2cc* pL2CC, uint32_t P_Address)
{
  static uint32_t Tag;
  static uint16_t Index;
  Tag   = (P_Address >> (OFFSET_BIT + INDEX_BIT));
  Index = (P_Address >> OFFSET_BIT) & ((1 << INDEX_BIT) - 1);
  
  pL2CC->L2CC_IPALR = (L2CC_IPALR_TAG(Tag) | L2CC_IPALR_IDX(Index) | L2CC_IPALR_C);
  
  while((pL2CC->L2CC_IPALR) & L2CC_IPALR_C);
}


/**
 * \brief Clean cache by Physical addersse
 * \param P_Address  Physical addresse
 */
void L2CC_CleanPAL(L2cc* pL2CC, uint32_t P_Address)
{
  static uint32_t Tag;
  static uint16_t Index;
  Tag   = (P_Address >> (OFFSET_BIT + INDEX_BIT));
  Index = (P_Address >> OFFSET_BIT) & ((1 << INDEX_BIT) - 1);
  
  pL2CC->L2CC_CPALR = (L2CC_CPALR_TAG(Tag) | L2CC_CPALR_IDX(Index) | L2CC_CPALR_C);
  
  while((pL2CC->L2CC_CPALR) & L2CC_CPALR_C);
}


/**
 * \brief Clean index cache by Physical addersse
 * \param P_Address  Physical addresse
 */
void L2CC_CleanIx(L2cc* pL2CC, uint32_t P_Address)
{
  static uint32_t Tag;
  static uint16_t Index;
  Tag   = (P_Address >> (OFFSET_BIT + INDEX_BIT));
  Index = (P_Address >> OFFSET_BIT) & ((1 << INDEX_BIT) - 1);
  
  pL2CC->L2CC_CIPALR = (L2CC_CIPALR_TAG(Tag) | L2CC_CIPALR_IDX(Index) | L2CC_CIPALR_C);
  
  while((pL2CC->L2CC_CIPALR) & L2CC_CIPALR_C);
}

/**
 * \brief Invalidate cache by way
 * \param Way  Way number
 */
void L2CC_InvalidateWay(L2cc* pL2CC, uint8_t Way)
{
  pL2CC->L2CC_IWR = Way;
  
  while(pL2CC->L2CC_IWR);
  while(pL2CC->L2CC_CSR);
  
}

/**
 * \brief Clean cache by way
 * \param Way  Way number
 */
void L2CC_CleanWay(L2cc* pL2CC, uint8_t Way)
{
  pL2CC->L2CC_CWR = Way;
  
  while(pL2CC->L2CC_CWR);
  while(pL2CC->L2CC_CSR);
  
}

/**
 * \brief Clean Invalidate cache by way
 * \param Way  Way number
 */
static void L2CC_CleanInvalidateWay(L2cc* pL2CC, uint8_t Way)
{
  pL2CC->L2CC_CIWR = Way;
  
  while(pL2CC->L2CC_CSR);
  
}


/**
 * \brief Clean cache by Index
 * \param P_Address  Physical addresse
 * \param Way  Way number
 */
void L2CC_CleanIndex(L2cc* pL2CC, uint32_t P_Address, uint8_t Way)
{  
  static uint16_t Index;
  Index = (P_Address >> OFFSET_BIT) & ((1 << INDEX_BIT) - 1);
  
  pL2CC->L2CC_CIR = (L2CC_CIR_IDX(Index) | L2CC_CIR_WAY(Way) | L2CC_CIR_C);
  
  while((pL2CC->L2CC_CIR) & L2CC_CIR_C);
}


/**
 * \brief Clean Invalidate cache by index
 * \param P_Address  Physical addresse
 * \param Way  Way number
 */
void L2CC_CleanInvalidateIndex(L2cc* pL2CC, uint32_t P_Address, uint8_t Way)
{  
  static uint16_t Index;
  Index = (P_Address >> OFFSET_BIT) & ((1 << INDEX_BIT) - 1);
  
  pL2CC->L2CC_CIIR = (L2CC_CIIR_IDX(Index) | L2CC_CIIR_WAY(Index) | L2CC_CIIR_C);
  
  while((pL2CC->L2CC_CIIR) & L2CC_CIIR_C);
}


/**
 * \brief cache Data lockdown
 * \param Way  Way number
 */
void L2CC_DataLockdown(L2cc* pL2CC, uint8_t Way)
{
  pL2CC->L2CC_DLKR = Way;
  
  while(pL2CC->L2CC_CSR);
}

/**
 * \brief cache instruction lockdown
 * \param Way  Way number
 */
void L2CC_InstructionLockdown(L2cc* pL2CC, uint8_t Way)
{
  pL2CC->L2CC_ILKR = Way;
  
  while(pL2CC->L2CC_CSR);
}



static void L2CC_Clean(void)
{  
  CP15_CacheClean(CP15_DCache);                 // Clean of L1; This is broadcast within the cluster
  L2CC_CleanWay(L2CC, 0xFF);                    // forces the address out past level 2
  L2CC_CacheSync(L2CC);                         // Ensures completion of the L2 clean
}

static void L2CC_Invalidate(void)
{    
  L2CC_InvalidateWay(L2CC, 0xFF);               // forces the address out past level 2
  L2CC_CacheSync(L2CC);                         // Ensures completion of the L2 inval
  CP15_CacheInvalidate(CP15_DCache);            // Inval of L1; This is broadcast within the cluster
}

static void L2CC_CleanInvalidate(void)
{    
  CP15_CacheClean(CP15_DCache);                 // Clean of L1; This is broadcast within the cluster
  L2CC_CleanInvalidateWay(L2CC, 0xFF);          // forces the address out past level 2
  L2CC_CacheSync(L2CC);                         // Ensures completion of the L2 inval
  CP15_CacheInvalidate(CP15_DCache);            // Inval of L1; This is broadcast within the cluster    
}

void L2CC_CacheMaintenance(uint8_t Maint_Op)
{
  
  switch(Maint_Op) {
  case DCACHE_CLEAN:
      L2CC_Clean();
      break;
  case DCACHE_INVAL:
      L2CC_Invalidate();
      break;
  case DCACHE_FLUSH:
      L2CC_CleanInvalidate();
      break;
  }
}

/**
 *  \brief Enable level two cache controller (L2CC) 
 */
void Enable_L2CC(void)
{
    L2CC_Control L2Config;
    /*****1. configure L2CC ************/
    L2Config.IPEN_Val = ENABLE;         // Instruction prefetch enable
    L2Config.DPEN_Val = ENABLE;         // Data prefetch enable
    
    L2Config.DLEN_Val = ENABLE; 
    L2Config.IDLEN_Val = ENABLE;
    //L2Config.DWB_Val = ENABLE;        // Disable Write back (enables write through, Use this setting if DDR2 mem is not write-back)
    L2Config.FWA_Val =  FWA_NO_ALLOCATE;
    
    L2Config.OFFSET_Val= 31;
    L2Config.PDEN_Val= ENABLE;
    
    L2Config.STBYEN_Val= ENABLE;
    L2Config.DCKGATEN_Val= ENABLE;

    L2CC_EventConfig(L2CC, 0, L2CC_ECFGR0_ESRC_SRC_DRHIT, L2CC_ECFGR0_EIGEN_INT_DIS);
    L2CC_EventConfig(L2CC, 1, L2CC_ECFGR0_ESRC_SRC_DWHIT, L2CC_ECFGR0_EIGEN_INT_DIS);
    L2CC_EnableResetCounter(L2CC, RESET_BOTH_COUNTER);
     
    L2CC_Config(L2CC, L2Config);

    /* Enable Prefetch */
    L2CC_InstPrefetchEnable(L2CC );
    L2CC_DataPrefetchEnable(L2CC );
    
    /*2. Inavlidate whole L2C     ***********/ 
    L2CC_InvalidateWay(L2CC, 0xFF);
    /*3. Diable all L2C Interrupt ***********/
    L2CC_DisableIT(L2CC, 0x1FF);
    /*4. Clear all L2C Interrupt ***********/    
    L2CC_ITClear(L2CC, 0); 

    L2CC_ExclusiveCache(L2CC, ENABLE);
    L2CC_Enable(L2CC);
}

