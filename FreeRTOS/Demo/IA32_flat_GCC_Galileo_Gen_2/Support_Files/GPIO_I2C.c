/*--------------------------------------------------------------------
 Copyright(c) 2015 Intel Corporation. All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions
 are met:

 * Redistributions of source code must retain the above copyright
 notice, this list of conditions and the following disclaimer.
 * Redistributions in binary form must reproduce the above copyright
 notice, this list of conditions and the following disclaimer in
 the documentation and/or other materials provided with the
 distribution.
 * Neither the name of Intel Corporation nor the names of its
 contributors may be used to endorse or promote products derived
 from this software without specific prior written permission.

 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 --------------------------------------------------------------------*/

/*-----------------------------------------------------------------------
 * Any required includes
 *------------------------------------------------------------------------
 */
#include "GPIO_I2C.h"

/*-----------------------------------------------------------------------
 * Any required local definitions
 *------------------------------------------------------------------------
 */
#ifndef NULL
	#define NULL (void *)0
#endif
/*-----------------------------------------------------------------------
 * Function prototypes
 *------------------------------------------------------------------------
 */
static void vGalileoRouteLEDPins(void);

/*-----------------------------------------------------------------------
 * Static variables
 *------------------------------------------------------------------------
 */
static struct BOARD_GPIO_CONTROLLER_CONFIG GpioConfig;
static struct BOARD_LEGACY_GPIO_CONFIG LegacyGpioConfig;

static uint32_t LegacyGpioBase = 0;
static uint32_t IohGpioBase = 0;
static uint32_t I2CGpioBase = 0;

static uint32_t bGalileoGPIOInitialized = FALSE;

/*-----------------------------------------------------------------------
 * GPIO support functions
 *------------------------------------------------------------------------
 */
 static uint32_t pciIOread32(uint32_t addr)
 {
	  outl(IO_PCI_ADDRESS_PORT, addr);
	  uint32_t data = inl(IO_PCI_DATA_PORT);
 	  return data;
 }
 /*-----------------------------------------------------------*/

 static void pciIOwrite32(uint32_t addr, uint32_t IO_data)
 {
	 outl(IO_PCI_ADDRESS_PORT, addr);
	 outl(IO_PCI_DATA_PORT, IO_data );
 }
 /*-----------------------------------------------------------*/

 static int32_t uiGalileoGPIORead(uint32_t Offset, uint8_t UseMask)
 {
	 // Keep reserved bits [31:8]
	 if (UseMask)
		 return *((volatile uint32_t *) (uintn_t)(IohGpioBase + Offset)) & 0xFFFFFF00;
	 else
		 return *((volatile uint32_t *) (uintn_t)(IohGpioBase + Offset));
 }
 /*-----------------------------------------------------------*/

 static void vGalileoGPIOWrite(uint32_t Offset, uint32_t WriteData32)
 {
	 uint32_t Data32 = uiGalileoGPIORead(Offset, true);
     if (Offset !=  GPIO_INTSTATUS)
    	 Data32 |= (WriteData32 & 0x000FFFFF);
     *((volatile uint32_t *) (uintn_t)(IohGpioBase + Offset)) = Data32;
 }
 /*-----------------------------------------------------------*/

 static int32_t uiGalileoLegacyGPIOPCIRead(uint32_t addr, uint32_t Mask)
 {
	 // Keep reserved bits (Mask Varies)
	 return pciIOread32(addr) & Mask;
 }
 /*-----------------------------------------------------------*/

 static void vGalileoLegacyGPIOPCIWrite(uint32_t addr, uint32_t WriteData32, uint32_t Mask)
 {
	 uint32_t Data32 = uiGalileoLegacyGPIOPCIRead(addr, Mask);
     Data32 |= (WriteData32 & ~Mask);
     pciIOwrite32(addr, Data32);
 }
 /*-----------------------------------------------------------*/

 static int32_t uiGalileoLegacyGPIOPortRead(uint32_t addr, uint32_t Mask)
 {
	 // Keep reserved bits (Mask Varies)
	 return inl(addr) & Mask;
 }
 /*-----------------------------------------------------------*/

 static void vGalileoLegacyGPIOPortRMW(uint32_t addr, uint32_t WriteData32, uint32_t Mask)
 {
	 uint32_t Data32 = uiGalileoLegacyGPIOPortRead(addr, Mask);
     Data32 |= (WriteData32 & ~Mask);
     outl(addr, Data32);
 }
 /*-----------------------------------------------------------*/

 /*-----------------------------------------------------------------------
  * Controller initialization functions
  *------------------------------------------------------------------------
  */
 void vGalileoInitializeLegacyGPIO(void)
 {
	 // Read Register Default Values into Structure
	 struct BOARD_LEGACY_GPIO_CONFIG LegacyGPIOConfigTable[] =
	 { PLATFORM_LEGACY_GPIO_CONFIG_DEFINITION };

	 // BDF for Legacy GPIO (from the Quark Datasheet)
	 uint8_t Bus = LEGACY_GPIO_BUS_NUMBER;
	 uint8_t Device = LEGACY_GPIO_DEVICE_NUMBER;
	 uint8_t Func = LEGACY_GPIO_FUNCTION_NUMBER;

	 // Get PCI Configuration IO Address
	 LegacyGpioBase =
	 uiGalileoLegacyGPIOPCIRead(IO_PCI_ADDRESS(Bus, Device, Func, R_QNC_LPC_GBA_BASE), B_QNC_LPC_GPA_BASE_MASK);

	 // Quiet compiler by doing a legacy GPIO write
	 uint32_t PciCmd = uiGalileoLegacyGPIOPCIRead((LegacyGpioBase + PCI_REG_PCICMD), 0xFFFFFFFF);
	 vGalileoLegacyGPIOPCIWrite((LegacyGpioBase + PCI_REG_PCICMD), (PciCmd | 0x7), 0xFFFFFFFF);

	 // Setup Structure
	 LegacyGpioConfig = LegacyGPIOConfigTable[0];

	 // Update values
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_CGEN_CORE_WELL, LegacyGpioConfig.CoreWellEnable, 0xFFFFFFFC);
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_CGIO_CORE_WELL, LegacyGpioConfig.CoreWellIoSelect, 0xFFFFFFFC);
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_CGLVL_CORE_WELL, LegacyGpioConfig.CoreWellLvlForInputOrOutput, 0xFFFFFFFC);
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_CGTPE_CORE_WELL, LegacyGpioConfig.CoreWellTriggerPositiveEdge, 0xFFFFFFFC);
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_CGTNE_CORE_WELL, LegacyGpioConfig.CoreWellTriggerNegativeEdge, 0xFFFFFFFC);
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_CGGPE_CORE_WELL, LegacyGpioConfig.ResumeWellGPEEnable, 0xFFFFFFFC);
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_CGSMI_CORE_WELL, LegacyGpioConfig.ResumeWellSMIEnable, 0xFFFFFFFC);
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_CGEN_CORE_WELL, LegacyGpioConfig.CoreWellTriggerStatus, 0xFFFFFFFC);
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_CNMIEN_CORE_WELL, LegacyGpioConfig.ResumeWellNMIEnable, 0xFFFFFFFC);
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_RGEN_RESUME_WELL, LegacyGpioConfig.ResumeWellEnable, 0xFFFFFFC0);
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_RGIO_RESUME_WELL, LegacyGpioConfig.ResumeWellIoSelect, 0xFFFFFFC0);
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_RGLVL_RESUME_WELL, LegacyGpioConfig.ResumeWellLvlForInputOrOutput, 0xFFFFFFC0);
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_RGTPE_RESUME_WELL, LegacyGpioConfig.ResumeWellTriggerPositiveEdge, 0xFFFFFFC0);
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_RGTNE_RESUME_WELL, LegacyGpioConfig.ResumeWellTriggerNegativeEdge, 0xFFFFFFC0);
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_RGGPE_RESUME_WELL, LegacyGpioConfig.CoreWellGPEEnable, 0xFFFFFFC0);
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_RGSMI_RESUME_WELL, LegacyGpioConfig.CoreWellSMIEnable, 0xFFFFFFC0);
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_RGTS_RESUME_WELL, LegacyGpioConfig.ResumeWellTriggerStatus, 0xFFFFFFC0);
	 vGalileoLegacyGPIOPortRMW(LegacyGpioBase + R_QNC_GPIO_RNMIEN_RESUME_WELL, LegacyGpioConfig.CoreWellNMIEnable, 0xFFFFFFC0);
 }
 /*-----------------------------------------------------------*/

 void vGalileoInitializeGpioController(void)
 {
	 // Read Register Default Values into Structure
	 struct BOARD_GPIO_CONTROLLER_CONFIG BoardGpioControllerConfigTable[] =
	 { PLATFORM_GPIO_CONTROLLER_CONFIG_DEFINITION };

	 // BDF for I2C Controller (from the Quark Datasheet)
	 uint8_t Bus = IOH_I2C_GPIO_BUS_NUMBER;
	 uint8_t Device = IOH_I2C_GPIO_DEVICE_NUMBER;
	 uint8_t Func = IOH_I2C_GPIO_FUNCTION_NUMBER;

	 // Get PCI Configuration MMIO Address
	 uint32_t gpio_controller_base = MMIO_PCI_ADDRESS(Bus, Device, Func, 0);

	 // Get Vendor and Device IDs
	 uint16_t PciVid = mem_read(gpio_controller_base, PCI_REG_VID, 2);
	 uint16_t PciDid = mem_read(gpio_controller_base, PCI_REG_DID, 2);

	 // Check for valid VID and DID
	 if((PciVid == V_IOH_I2C_GPIO_VENDOR_ID) && (PciDid == V_IOH_I2C_GPIO_DEVICE_ID))
	 {
		 // Read PCICMD
		 uint8_t PciCmd = mem_read(gpio_controller_base, PCI_REG_PCICMD, 1);
		 // Enable Bus Master(Bit2), MMIO Space(Bit1) & I/O Space(Bit0)
		 mem_write(gpio_controller_base, PCI_REG_PCICMD, 1, (PciCmd | 0x7));
		 // Read MEM_BASE
		 IohGpioBase = mem_read(gpio_controller_base, R_IOH_GPIO_MEMBAR, 4);
		 // Setup Structure
		 GpioConfig = BoardGpioControllerConfigTable[0];
		 // IEN- Interrupt Enable Register
		 vGalileoGPIOWrite(GPIO_INTEN, GpioConfig.IntEn);
		 // ISTATUS- Interrupt Status Register
		 vGalileoGPIOWrite(GPIO_INTSTATUS, 0);
		 // GPIO SWPORTA Data Register - GPIO_SWPORTA_DR
		 vGalileoGPIOWrite(GPIO_SWPORTA_DR, GpioConfig.PortADR);
		 // GPIO SWPORTA Data Direction Register - GPIO_SWPORTA_DDR
		 vGalileoGPIOWrite(GPIO_SWPORTA_DDR, GpioConfig.PortADir);
		 // Interrupt Mask Register - GPIO_INTMASK
		 vGalileoGPIOWrite(GPIO_INTMASK, GpioConfig.IntMask);
		 // Interrupt Level Type Register - GPIO_INTTYPE_LEVEL
		 vGalileoGPIOWrite(GPIO_INTTYPE_LEVEL, GpioConfig.IntType);
		 // Interrupt Polarity Type Register - GPIO_INT_POLARITY
		 vGalileoGPIOWrite(GPIO_INT_POLARITY, GpioConfig.IntPolarity);
		 // Interrupt Debounce Type Register - GPIO_DEBOUNCE
		 vGalileoGPIOWrite(GPIO_DEBOUNCE, GpioConfig.Debounce);
		 // Interrupt Clock Synchronization Register - GPIO_LS_SYNC
		 vGalileoGPIOWrite(GPIO_LS_SYNC, GpioConfig.LsSync);
		 bGalileoGPIOInitialized = true;
	 }
 }
 /*-----------------------------------------------------------*/

 /*-----------------------------------------------------------------------
  * I/O direction and level setting functions
  *------------------------------------------------------------------------
  */
  void vGalileoSetGPIOBitDirection(uint32_t GPIONumber, uint32_t Direction)
  {
	  /* Check Range. */
	  if(GPIONumber <= 9)
	  {
		  /* setup gpio direction. */
		  if (bGalileoGPIOInitialized)
		  {
			  if(Direction == GPIO_OUTPUT)
				  GpioConfig.PortADir |= (1 << GPIONumber);
			  else
				  GpioConfig.PortADir &= ~(1 << GPIONumber);
			  vGalileoGPIOWrite(GPIO_SWPORTA_DDR, GpioConfig.PortADir);
		  }
	  }
  }
  /*-----------------------------------------------------------*/

  void vGalileoSetGPIOBitLevel(uint32_t GPIONumber, uint32_t Level)
  {
	  /* Check Range. */
	  if(GPIONumber <= 9)
	  {
		  /* Set the bit high or low. */
		  if (bGalileoGPIOInitialized)
		  {
			  // 1 for on, 0 for off.
			  if (Level == HIGH)
				  GpioConfig.PortADR |= (1 << GPIONumber);
			  else
				  GpioConfig.PortADR &= ~(1 << GPIONumber);
			  vGalileoGPIOWrite(GPIO_SWPORTA_DR, GpioConfig.PortADR);
		  }
	  }
  }
  /*-----------------------------------------------------------*/

  static void LegacyGpioSetLevel(uint32_t RegOffset, uint32_t GpioNum, uint8_t HighLevel)
  {
	  uint32_t RegValue;
	  uint32_t legacy_gpio_base;
	  uint32_t GpioNumMask;
	  uint8_t Bus = LEGACY_GPIO_BUS_NUMBER;
	  uint8_t Device = LEGACY_GPIO_DEVICE_NUMBER;
	  uint8_t Func = LEGACY_GPIO_FUNCTION_NUMBER;

	  // Get PCI Configuration IO Address
	  legacy_gpio_base =
	  uiGalileoLegacyGPIOPCIRead(IO_PCI_ADDRESS(Bus, Device, Func, R_QNC_LPC_GBA_BASE), B_QNC_LPC_GPA_BASE_MASK);

	  // Read register (Port I/O )
	  RegValue = inl(legacy_gpio_base + RegOffset);

	  // Set Data and mask
	  GpioNumMask = (1 << GpioNum);
	  if (HighLevel)
	   	  RegValue |= (GpioNumMask);
	  else
		  RegValue &= ~(GpioNumMask);

	  // Write the data (Port I/O )
	  outl((legacy_gpio_base + RegOffset), RegValue);
  }
  /*-----------------------------------------------------------*/

  void vGalileoLegacyGPIOInitializationForLED(void)
  {
	  // Setup multiplexers to route GPIO_SUS<5> to LED
	  vGalileoRouteLEDPins();

	  // Set GPIO_SUS<5> as output
	  LegacyGpioSetLevel (R_QNC_GPIO_RGIO_RESUME_WELL,
	  GALILEO_GEN2_FLASH_UPDATE_LED_RESUMEWELL_GPIO, GPIO_OUTPUT);

	  // Set GPIO_SUS<5> level to low
	  LegacyGpioSetLevel (R_QNC_GPIO_RGLVL_RESUME_WELL,
      GALILEO_GEN2_FLASH_UPDATE_LED_RESUMEWELL_GPIO, LOW);
  }
  /*-----------------------------------------------------------*/

  void vGalileoBlinkLEDUsingLegacyGPIO(uint32_t Level)
  {
	  LegacyGpioSetLevel (R_QNC_GPIO_RGLVL_RESUME_WELL,
	  GALILEO_GEN2_FLASH_UPDATE_LED_RESUMEWELL_GPIO, Level);
  }
  /*-----------------------------------------------------------*/

  /*-----------------------------------------------------------------------
   * I2C support functions
   *------------------------------------------------------------------------
   */
  static inline uint64_t rdtsc(void)
  {
      uint32_t lo, hi;
      uint64_t tsc;
      __asm__ __volatile__ ("rdtsc" : "=a" (lo), "=d" (hi));
      tsc = hi;
      tsc <<= 32;
      tsc |= lo;
      return tsc;
  }
  /*-----------------------------------------------------------*/

  void vMicroSecondDelay(uint32_t DelayTime)
  {
	  uint64_t diff_in_us = 0;
	  uint64_t cpufreq_in_mhz = 400;
	  uint64_t tsc_start = rdtsc();
	  uint64_t tsc_current = tsc_start;

	  do
	  {
	  	  diff_in_us = ((tsc_current - tsc_start) / cpufreq_in_mhz);
		  tsc_current = rdtsc();
	  }
	  while (diff_in_us < (uint64_t) DelayTime);
  }
  /*-----------------------------------------------------------*/

  void vMilliSecondDelay(uint32_t DelayTime)
  {
	  vMicroSecondDelay (DelayTime * 1000);
  }
  /*-----------------------------------------------------------*/

  static uintn_t GetI2CIoPortBaseAddress(void)
  {
	  uint8_t Bus = IOH_I2C_GPIO_BUS_NUMBER;
	  uint8_t Device = IOH_I2C_GPIO_DEVICE_NUMBER;
	  int8_t Func = IOH_I2C_GPIO_FUNCTION_NUMBER;
	  uint32_t I2C_controller_base = MMIO_PCI_ADDRESS(Bus, Device, Func, 0);
	  uintn_t I2CIoPortBaseAddress = mem_read(I2C_controller_base, R_IOH_I2C_MEMBAR, 4);
	  return I2CIoPortBaseAddress;
  }
  /*-----------------------------------------------------------*/

  static void EnableI2CMmioSpace(void)
  {
	  uint8_t Bus = IOH_I2C_GPIO_BUS_NUMBER;
	  uint8_t Device = IOH_I2C_GPIO_DEVICE_NUMBER;
	  uint8_t Func = IOH_I2C_GPIO_FUNCTION_NUMBER;
	  uint32_t I2C_controller_base = MMIO_PCI_ADDRESS(Bus, Device, Func, 0);
	  uint8_t PciCmd = mem_read(I2C_controller_base, PCI_REG_PCICMD, 1);
	  mem_write(I2C_controller_base, PCI_REG_PCICMD, 1, (PciCmd | 0x7));
  }
  /*-----------------------------------------------------------*/

  static void DisableI2CController(void)
  {
	  uintn_t       I2CIoPortBaseAddress;
	  uint32_t      Addr;
	  uint32_t      Data;
	  uint8_t       PollCount = 0;

	  // Get I2C Memory Mapped registers base address.
	  I2CIoPortBaseAddress = GetI2CIoPortBaseAddress ();

	  // Disable the I2C Controller by setting IC_ENABLE.ENABLE to zero
	  Addr = I2CIoPortBaseAddress + I2C_REG_ENABLE;
	  Data = *((volatile uint32_t *) (uintn_t)(Addr));
	  Data &= ~B_I2C_REG_ENABLE;
	  *((volatile uint32_t *) (uintn_t)(Addr)) = Data;

	  // Read the IC_ENABLE_STATUS.IC_EN Bit to check if Controller is disabled
	  Data = 0xFF;
	  Addr = I2CIoPortBaseAddress + I2C_REG_ENABLE_STATUS;
	  Data = *((volatile uint32_t *) (uintn_t)(Addr)) & I2C_REG_ENABLE_STATUS;
	  while (Data != 0)
	  {
		  // Poll the IC_ENABLE_STATUS.IC_EN Bit to check if Controller is disabled, until timeout (TI2C_POLL*MAX_T_POLL_COUNT).
		  if (++PollCount >= MAX_T_POLL_COUNT)
			  break;
		  vMicroSecondDelay(TI2C_POLL);
		  Data = *((volatile uint32_t *) (uintn_t)(Addr));
		  Data &= I2C_REG_ENABLE_STATUS;
	  }

	  // Read IC_CLR_INTR register to automatically clear the combined interrupt,
	  // all individual interrupts and the IC_TX_ABRT_SOURCE register.
	  if (PollCount < MAX_T_POLL_COUNT)
	  {
		  Addr = I2CIoPortBaseAddress + I2C_REG_CLR_INT;
		  Data = *((volatile uint32_t *) (uintn_t)(Addr));
	  }
  }
  /*-----------------------------------------------------------*/

  static void EnableI2CController(void)
  {
	  uintn_t   I2CIoPortBaseAddress;
	  uint32_t  Addr;
	  uint32_t  Data;

	  // Get I2C Memory Mapped registers base address.
	  I2CIoPortBaseAddress = GetI2CIoPortBaseAddress ();

	  // Enable the I2C Controller by setting IC_ENABLE.ENABLE to 1
	  Addr = I2CIoPortBaseAddress + I2C_REG_ENABLE;
	  Data = *((volatile uint32_t *) (uintn_t)(Addr));
	  Data |= B_I2C_REG_ENABLE;
	  *((volatile uint32_t *) (uintn_t)(Addr)) = Data;

	  // Clear overflow and abort error status bits before transactions.
	  Addr = I2CIoPortBaseAddress + I2C_REG_CLR_RX_OVER;
	  Data = *((volatile uint32_t *) (uintn_t)(Addr));
	  Addr = I2CIoPortBaseAddress + I2C_REG_CLR_TX_OVER;
	  Data = *((volatile uint32_t *) (uintn_t)(Addr));
	  Addr = I2CIoPortBaseAddress + I2C_REG_CLR_TX_ABRT;
	  Data = *((volatile uint32_t *) (uintn_t)(Addr));
  }
  /*-----------------------------------------------------------*/

  static uint32_t InitializeInternal(I2C_ADDR_MODE AddrMode)
  {
		uintn_t   I2CIoPortBaseAddress;
		uintn_t   Addr;
		uint32_t  Data;
		uint32_t  Status = 0;

		// Enable access to I2C Controller MMIO space.
		EnableI2CMmioSpace ();

		// Disable I2C Controller initially
		DisableI2CController ();

		// Get I2C Memory Mapped registers base address.
		 I2CIoPortBaseAddress = GetI2CIoPortBaseAddress ();

		// Clear START_DET
		Addr = I2CIoPortBaseAddress + I2C_REG_CLR_START_DET;
		Data = *((volatile uint32_t *) (uintn_t)(Addr));
		Data &= ~B_I2C_REG_CLR_START_DET;
		*((volatile uint32_t *) (uintn_t)(Addr)) = Data;

		// Clear STOP_DET
		Addr = I2CIoPortBaseAddress + I2C_REG_CLR_STOP_DET;
		Data = *((volatile uint32_t *) (uintn_t)(Addr));
		Data &= ~B_I2C_REG_CLR_STOP_DET;
		*((volatile uint32_t *) (uintn_t)(Addr)) = Data;

		// Set addressing mode to user defined (7 or 10 bit) and
		// speed mode to that defined by PCD (standard mode default).
		Addr = I2CIoPortBaseAddress + I2C_REG_CON;
		Data = *((volatile uint32_t *) (uintn_t)(Addr));

		// Set Addressing Mode
		if (AddrMode == EfiI2CSevenBitAddrMode)
			Data &= ~B_I2C_REG_CON_10BITADD_MASTER;
		else
			Data |= B_I2C_REG_CON_10BITADD_MASTER;

		// Set Speed Mode
		Data &= ~B_I2C_REG_CON_SPEED;

		// Default to slow mode
		Data |= BIT1;
		*((volatile uint32_t *) (uintn_t)(Addr)) = Data;
		Data = *((volatile uint32_t *) (uintn_t)(Addr));
		return Status;
  }
  /*-----------------------------------------------------------*/

  static void I2cEntry(uint16_t *SaveCmdPtr, uint32_t *SaveBar0Ptr)
  {
		uint8_t Bus = IOH_I2C_GPIO_BUS_NUMBER;
		uint8_t Device = IOH_I2C_GPIO_DEVICE_NUMBER;
		uint8_t Func = IOH_I2C_GPIO_FUNCTION_NUMBER;
		uint32_t I2C_controller_base = MMIO_PCI_ADDRESS(Bus, Device, Func, 0);

		I2CGpioBase = mem_read(I2C_controller_base, R_IOH_I2C_MEMBAR, 4);
		*SaveBar0Ptr = I2CGpioBase;
		if (((*SaveBar0Ptr) & B_IOH_I2C_GPIO_MEMBAR_ADDR_MASK) == 0)
		{
			mem_write(I2C_controller_base, R_IOH_I2C_MEMBAR, 4, IO_PCI_ADDRESS(Bus, Device, Func, 0));
			// also Save Cmd Register, Setup by InitializeInternal later during xfers.
			*SaveCmdPtr = mem_read(I2C_controller_base, PCI_REG_PCICMD, 1);
		}
  }
  /*-----------------------------------------------------------*/

  static void I2cExit(uint16_t SaveCmd, uint32_t SaveBar0)
  {
		if ((SaveBar0 & B_IOH_I2C_GPIO_MEMBAR_ADDR_MASK) == 0)
		{
			uint8_t Bus = IOH_I2C_GPIO_BUS_NUMBER;
			uint8_t Device = IOH_I2C_GPIO_DEVICE_NUMBER;
			uint8_t Func = IOH_I2C_GPIO_FUNCTION_NUMBER;
			uint32_t I2C_controller_base = MMIO_PCI_ADDRESS(Bus, Device, Func, 0);
			mem_write(I2C_controller_base, PCI_REG_PCICMD, 1, SaveCmd);
			mem_write(I2C_controller_base, R_IOH_I2C_MEMBAR, 4, SaveBar0);
		}
  }
  /*-----------------------------------------------------------*/

  static uint32_t WaitForStopDet(void)
  {
		uintn_t   I2CIoPortBaseAddress;
		uint32_t  Addr;
		uint32_t  Data;
		uint32_t  PollCount = 0;
		uint32_t  Status = 0;

		// Get I2C Memory Mapped registers base address.
		I2CIoPortBaseAddress = GetI2CIoPortBaseAddress ();

		// Wait for STOP Detect.
		Addr = I2CIoPortBaseAddress + I2C_REG_RAW_INTR_STAT;
		do
		{
			Data = *((volatile uint32_t *) (uintn_t)(Addr));
			if ((Data & I2C_REG_RAW_INTR_STAT_TX_ABRT) != 0)
			{
				Status = -1;
				break;
			}
			if ((Data & I2C_REG_RAW_INTR_STAT_TX_OVER) != 0)
			{
				Status = -1;
				break;
			}
			if ((Data & I2C_REG_RAW_INTR_STAT_RX_OVER) != 0)
			{
				Status = -1;
				break;
			}
			if ((Data & I2C_REG_RAW_INTR_STAT_STOP_DET) != 0)
			{
				  Status = 0;
				  break;
			}
			vMicroSecondDelay(TI2C_POLL);
			PollCount++;
			if (PollCount >= MAX_STOP_DET_POLL_COUNT)
			{
				  Status = -1;
				  break;
			}
		} while (TRUE);

		return Status;
  }
  /*-----------------------------------------------------------*/

  uint32_t WriteMultipleByte(uintn_t I2CAddress, uint8_t *WriteBuffer, uintn_t Length)
  {
		uintn_t   I2CIoPortBaseAddress;
		uintn_t   Index;
		uintn_t   Addr;
		uint32_t  Data;
		uint32_t  Status = 0;

		if (Length > I2C_FIFO_SIZE)
			return -1;  // Routine does not handle xfers > fifo size.

		I2CIoPortBaseAddress = GetI2CIoPortBaseAddress ();

		// Write to the IC_TAR register the address of the slave device to be addressed
		Addr = I2CIoPortBaseAddress + I2C_REG_TAR;
		Data = *((volatile uint32_t *) (uintn_t)(Addr));
		Data &= ~B_I2C_REG_TAR;
		Data |= I2CAddress;
		*((volatile uint32_t *) (uintn_t)(Addr)) = Data;

		// Enable the I2C Controller
		EnableI2CController ();

		// Write the data and transfer direction to the IC_DATA_CMD register.
		// Also specify that transfer should be terminated by STOP condition.
		Addr = I2CIoPortBaseAddress + I2C_REG_DATA_CMD;
		for (Index = 0; Index < Length; Index++)
		{
			  Data = *((volatile uint32_t *) (uintn_t)(Addr));
			  Data &= 0xFFFFFF00;
			  Data |= (uint8_t)WriteBuffer[Index];
			  Data &= ~B_I2C_REG_DATA_CMD_RW;
			  if (Index == (Length-1))
				  Data |= B_I2C_REG_DATA_CMD_STOP;
			  *((volatile uint32_t *) (uintn_t)(Addr)) = Data;
		}

		// Wait for transfer completion
		Status = WaitForStopDet ();

		// Ensure I2C Controller disabled.
		DisableI2CController ();

		return Status;
  }
  /*-----------------------------------------------------------*/

 static void I2CWriteMultipleBytes(I2C_DEVICE_ADDRESS  SlaveAddress,
 I2C_ADDR_MODE AddrMode, uintn_t *Length, void *Buffer)
 {
	  uintn_t  I2CAddress;
	  uint16_t SaveCmd;
	  uint32_t SaveBar0;

	  if (Buffer != NULL && Length != NULL)
	  {
		  SaveCmd = 0;
		  SaveBar0 = 0;
		  I2cEntry (&SaveCmd, &SaveBar0);
		  if (InitializeInternal(AddrMode) == 0)
		  {
			  I2CAddress = SlaveAddress.I2CDeviceAddress;
			  WriteMultipleByte(I2CAddress, Buffer, (*Length));
		  }
		  I2cExit (SaveCmd, SaveBar0);
	  }
 }
 /*-----------------------------------------------------------*/

  uint32_t ReadMultipleByte(uintn_t I2CAddress, uint8_t *Buffer,
  uintn_t WriteLength, uintn_t ReadLength)
  {
	  uintn_t   I2CIoPortBaseAddress;
	  uintn_t   Index;
	  uintn_t   Addr;
	  uint32_t  Data;
	  uint8_t   PollCount;
	  uint32_t  Status;

	  if (WriteLength > I2C_FIFO_SIZE || ReadLength > I2C_FIFO_SIZE)
		  return -1;  // Routine does not handle xfers > fifo size.

	  I2CIoPortBaseAddress = GetI2CIoPortBaseAddress ();

	  // Write to the IC_TAR register the address of the slave device to be addressed
	  Addr = I2CIoPortBaseAddress + I2C_REG_TAR;
	  Data = *((volatile uint32_t *) (uintn_t)(Addr));
	  Data &= ~B_I2C_REG_TAR;
	  Data |= I2CAddress;
	  *((volatile uint32_t *) (uintn_t)(Addr)) = Data;

	  // Enable the I2C Controller
	  EnableI2CController ();

	  // Write the data (sub-addresses) to the IC_DATA_CMD register.
	  Addr = I2CIoPortBaseAddress + I2C_REG_DATA_CMD;
	  for (Index = 0; Index < WriteLength; Index++)
	  {
		  Data = *((volatile uint32_t *) (uintn_t)(Addr));
      	  Data &= 0xFFFFFF00;
      	  Data |= (uint8_t)Buffer[Index];
      	  Data &= ~B_I2C_REG_DATA_CMD_RW;
      	  *((volatile uint32_t *) (uintn_t)(Addr)) = Data;
	  }

	  // Issue Read Transfers for each byte (Restart issued when write/read bit changed).
	  for (Index = 0; Index < ReadLength; Index++)
	  {
		  Data = *((volatile uint32_t *) (uintn_t)(Addr));
		  Data |= B_I2C_REG_DATA_CMD_RW;
		  // Issue a STOP for last read transfer.
		  if (Index == (ReadLength-1))
			  Data |= B_I2C_REG_DATA_CMD_STOP;
		  *((volatile uint32_t *) (uintn_t)(Addr)) = Data;
	  }

	  // Wait for STOP condition.
	  Status = WaitForStopDet();
	  if (Status != 0)
	  {
		  // Poll Receive FIFO Buffer Level register until valid (upto MAX_T_POLL_COUNT times).
		  Data = 0;
		  PollCount = 0;
		  Addr = I2CIoPortBaseAddress + I2C_REG_RXFLR;
		  Data = *((volatile uint32_t *) (uintn_t)(Addr));
		  while ((Data != ReadLength) && (PollCount < MAX_T_POLL_COUNT))
		  {
			  vMicroSecondDelay(TI2C_POLL);
			  PollCount++;
			  Data = *((volatile uint32_t *) (uintn_t)(Addr));
		  }

		  Addr = I2CIoPortBaseAddress + I2C_REG_RAW_INTR_STAT;
		  Data = *((volatile uint32_t *) (uintn_t)(Addr));

		  // If no timeout or device error then read rx data.
		  if (PollCount == MAX_T_POLL_COUNT)
		  {
			  Status = -1;
		  }
		  else if ((Data & I2C_REG_RAW_INTR_STAT_RX_OVER) != 0)
		  {
			  Status = -1;
		  }
		  else
		  {
			  // Clear RX underflow before reading IC_DATA_CMD.
			  Addr = I2CIoPortBaseAddress + I2C_REG_CLR_RX_UNDER;
			  Data = *((volatile uint32_t *) (uintn_t)(Addr));

			  // Read data.
			  Addr = I2CIoPortBaseAddress + I2C_REG_DATA_CMD;
			  for (Index = 0; Index < ReadLength; Index++)
			  {
				  Data = *((volatile uint32_t *) (uintn_t)(Addr));
				  Data &= 0x000000FF;
				  *(Buffer+Index) = (uint8_t)Data;
			  }
			  Addr = I2CIoPortBaseAddress + I2C_REG_RAW_INTR_STAT;
			  Data = *((volatile uint32_t *) (uintn_t)(Addr));
			  Data &= I2C_REG_RAW_INTR_STAT_RX_UNDER;
			  if (Data != 0)
			  {
				  Status = -1;
			  }
			  else
			  {
				  Status = 0;
			  }
		  }
	  }

	  // Ensure I2C Controller disabled.
	  DisableI2CController ();

	  return Status;
  }
  /*-----------------------------------------------------------*/

 static void I2CReadMultipleBytes(I2C_DEVICE_ADDRESS SlaveAddress, I2C_ADDR_MODE AddrMode,
 uintn_t *WriteLength, uintn_t *ReadLength, void *Buffer )
 {
	  uintn_t  I2CAddress;
	  uint16_t SaveCmd;
	  uint32_t SaveBar0;

	  if (Buffer != NULL && WriteLength != NULL && ReadLength != NULL)
	  {
		  SaveCmd = 0;
		  SaveBar0 = 0;
		  I2cEntry (&SaveCmd, &SaveBar0);
		  if (InitializeInternal(AddrMode) == 0)
		  {
			  I2CAddress = SlaveAddress.I2CDeviceAddress;
			  ReadMultipleByte(I2CAddress, Buffer, (*WriteLength), (*ReadLength));
		  }
		  I2cExit (SaveCmd, SaveBar0);
	  }
 }
 /*-----------------------------------------------------------*/

 /*-----------------------------------------------------------------------
  * Pcal9555 chips used on Galileo Gen 2 boards (see FAB-H schematic)
  *------------------------------------------------------------------------
  */
 static void Pcal9555SetPortRegBit(uint32_t Pcal9555SlaveAddr, uint32_t GpioNum, uint8_t RegBase, uint8_t LogicOne)
 {
	 uintn_t            ReadLength;
	 uintn_t            WriteLength;
	 uint8_t            Data[2];
	 uint8_t            *RegValuePtr;
	 uint8_t            GpioNumMask;
	 uint8_t            SubAddr;
	 I2C_DEVICE_ADDRESS I2cDeviceAddr;
	 I2C_ADDR_MODE      I2cAddrMode;

	 // Set I2C address and mode.
	 I2cDeviceAddr.I2CDeviceAddress = (uintn_t) Pcal9555SlaveAddr;
	 I2cAddrMode = EfiI2CSevenBitAddrMode;

	 // Set I2C subaddress and GPIO mask.
	 if (GpioNum < 8)
	 {
		 SubAddr = RegBase;
		 GpioNumMask = (uintn_t) (1 << GpioNum);
	 }
	 else
	 {
		 SubAddr = RegBase + 1;
		 GpioNumMask = (uintn_t) (1 << (GpioNum - 8));
	 }

	 // Output port value always at 2nd byte in Data variable.
	 RegValuePtr = &Data[1];

	 // On read entry - sub address at 2nd byte, on read exit - output
	 // port value in 2nd byte.
	 Data[1] = SubAddr;
	 WriteLength = 1;
	 ReadLength = 1;
	 I2CReadMultipleBytes(I2cDeviceAddr, I2cAddrMode, &WriteLength, &ReadLength,  &Data[1]);

	 // Adjust output port bit using mask value.
	 if (LogicOne)
		 *RegValuePtr = *RegValuePtr | GpioNumMask;
	 else
		 *RegValuePtr = *RegValuePtr & ~(GpioNumMask);

	 // Update register. Sub address at 1st byte, value at 2nd byte.
	 WriteLength = 2;
	 Data[0] = SubAddr;
	 I2CWriteMultipleBytes(I2cDeviceAddr,I2cAddrMode, &WriteLength, Data);
 }
 /*-----------------------------------------------------------*/

 static void PlatformPcal9555GpioPullup(uint32_t Pcal9555SlaveAddr, uint32_t GpioNum, uint32_t Enable)
 {
	  Pcal9555SetPortRegBit(Pcal9555SlaveAddr, GpioNum, PCAL9555_REG_PULL_EN_PORT0, Enable );
 }
 /*-----------------------------------------------------------*/

 static void PlatformPcal9555GpioSetDir(uint32_t Pcal9555SlaveAddr, uint32_t GpioNum, uint32_t CfgAsInput)
 {
	  Pcal9555SetPortRegBit(Pcal9555SlaveAddr, GpioNum, PCAL9555_REG_CFG_PORT0, CfgAsInput);
 }
 /*-----------------------------------------------------------*/

 static void PlatformPcal9555GpioSetLevel(uint32_t Pcal9555SlaveAddr, uint32_t GpioNum, uint32_t HighLevel )
 {
	  Pcal9555SetPortRegBit(Pcal9555SlaveAddr, GpioNum, PCAL9555_REG_OUT_PORT0, HighLevel );
 }
 /*-----------------------------------------------------------*/

 /*-----------------------------------------------------------------------
  * GPIO pin routing function
  *------------------------------------------------------------------------
  */
 static void vGalileoRouteLEDPins(void)
 {
	 // For GpioNums below values 0 to 7 are for Port0 IE. P0-0 - P0-7 and
	 // values 8 to 15 are for Port1 IE. P1-0 - P1-7.
	 // Disable Pull-ups / pull downs on EXP0 pin for LVL_B_PU7 signal.
	 PlatformPcal9555GpioPullup (
	 GALILEO_GEN2_IOEXP0_7BIT_SLAVE_ADDR,  // IO Expander 0.
     15,                                   // P1-7.
     FALSE
     );

     // Make LVL_B_OE7_N an output pin.
     PlatformPcal9555GpioSetDir (
     GALILEO_GEN2_IOEXP0_7BIT_SLAVE_ADDR,  // IO Expander 0.
     14,                                   // P1-6.
     FALSE);

     // Set level of LVL_B_OE7_N to low.
     PlatformPcal9555GpioSetLevel (
     GALILEO_GEN2_IOEXP0_7BIT_SLAVE_ADDR,
     14,
     FALSE);

     // Make MUX8_SEL an output pin.
     PlatformPcal9555GpioSetDir (
     GALILEO_GEN2_IOEXP1_7BIT_SLAVE_ADDR,  // IO Expander 1.
     14,                                   // P1-6.
     FALSE);

     // Set level of MUX8_SEL to low to route GPIO_SUS<5> to LED.
     PlatformPcal9555GpioSetLevel (
     GALILEO_GEN2_IOEXP1_7BIT_SLAVE_ADDR,  // IO Expander 1.
     14,                                   // P1-6.
     FALSE);
 }
 /*-----------------------------------------------------------*/
