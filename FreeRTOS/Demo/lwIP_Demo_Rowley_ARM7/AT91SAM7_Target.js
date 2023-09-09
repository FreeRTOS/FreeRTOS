/******************************************************************************
  Target Script for ATMEL AT91SAM7.

  Copyright (c) 2004 Rowley Associates Limited.

  This file may be distributed under the terms of the License Agreement
  provided with this software.

  THIS FILE IS PROVIDED AS IS WITH NO WARRANTY OF ANY KIND, INCLUDING THE
  WARRANTY OF DESIGN, MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 ******************************************************************************/

function Reset()
{
  /* Reset and stop target */
  TargetInterface.pokeWord(0xFFFFFD00, 0xA500000D); // RSTC_CR
  TargetInterface.waitForDebugState(1000);
  /* Configure Clock */
  TargetInterface.pokeWord(0xFFFFFC20, 0x00000601); // CKGR_MOR
  TargetInterface.delay(10);
  TargetInterface.pokeWord(0xFFFFFC2C, 0x00191C05); // CKGR_PLLR
  TargetInterface.delay(10);
  TargetInterface.pokeWord(0xFFFFFC30, 0x00000007); // CKGR_MCKR
  TargetInterface.delay(10);
}

function RAMReset()
{
  Reset();
  /* Remap SRAM to 0x00000000 */
  TargetInterface.pokeWord(0xFFFFFF00, 1); // MC_RCR 
}

function FLASHReset()
{
  Reset();

// Mask All interrupt pAic->AIC_IDCR = 0xFFFFFFFF;
	
    TargetInterface.pokeWord(0xffffffff,0xFFFFF124);
    TargetInterface.pokeWord(0xffffffff,0xFFFFF128);
// disable peripheral clock  Peripheral Clock Disable Register
    TargetInterface.pokeWord(0xffffffff,0xFFFFFC14);

// #define AT91C_TC0_SR    ((AT91_REG *) 	0xFFFA0020) // (TC0) Status Register
// #define AT91C_TC1_SR    ((AT91_REG *) 	0xFFFA0060) // (TC1) Status Register
// #define AT91C_TC2_SR    ((AT91_REG *) 	0xFFFA00A0) // (TC2) Status Register
    TargetInterface.peekWord(0xFFFA0020);
    TargetInterface.peekWord(0xFFFA0060);
    TargetInterface.peekWord(0xFFFA00A0);

//    for (__mac_i=0;__mac_i < 8; __mac_i++)
//    {
      // AT91C_BASE_AIC->AIC_EOICR
//      __mac_pt  =  TargetInterface.peekWord(0xFFFFF130);
    
//    }
//   __message "------------------------------- AIC 2 INIT ---------------------------------------------";  

}

