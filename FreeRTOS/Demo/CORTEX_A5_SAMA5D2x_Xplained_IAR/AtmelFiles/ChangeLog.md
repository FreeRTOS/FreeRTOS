# Atmel SAMA5D2x Software Package


## Version 1.2 - 2015-12

### New drivers/examples

- USB Device examples and stack: CDC Serial, HID Keyboard, HID Mouse, Audio,
  Mass Storage and some composite examples.
- NAND flash driver and examples: supports MLC/SLC, up to 32-bit ECC.
- SDMMC/eMMC driver and example
- Low Power examples: power_consumption_pll, pmc_clock_switching,
  low_power_mode
- New storagemedia library to abstract storage devices (only supports RAM disk
  for now, but will support SDMMC/eMMC and NAND flash in later releases)

### Enhancements

- Several new functions in PMC driver, notably 'pmc_set_custom_pck_mck' that
  allow changing easily the main clock settings.
- IAR project generator now uses defines and include directories from
  CFLAGS_DEFS and CFLAGS_INC mkefile variables. It also generates projects with
  CMSIS-DAP debugger selected and proper optimization level.

### Fixes

- Fix CP15 driver to invalidate caches before enable. This fixes some lock-ups
  when caches were previously enabled and still contain stale data.



## Version 1.1 - 2015-10

### New drivers

- Class-D audio driver + example

### Enhancements

- Support for ISO7816 and LIN modes to UART driver + example
- Several functions added to PMC driver, mostly UPLL and AudioPLL support
- ISC/sensors: support for new capture modes / resolutions

### Fixes

- Several fixes to ADC driver and example
- Fixed MMU setup (some memory regions where not defined)



## Version 1.0 - 2015-09

### New drivers

- MCAN driver + example

### Changes

- sama5d2-xplained target adapted for final revA board

### Enhancements

- Clock initialization changed to be more reliable
- PMC driver now supports setting generated clocks on sama5d2
- Add support for new memory models to at25 driver (MX25L12835F, MX25L4005,
  N25Q032, S25FL127S)



## Version 0.3 -- 2015-08

### New drivers

- ACC driver
- ADC driver + example
- AES / TDES / SHA drivers + examples
- L2CC driver
- GMAC driver + examples (using ad-hoc / LWIP / UIP stacks)
- QT1070 driver
- SHDWC driver

### Enhancements

- FPU is now enabled in GCC startup (was already enabled for IAR)
- ISC example now demonstrates Auto White Balance / Auto Exposure
- SPID/TWID/USARTD drivers now switch the Flexcom mode when appropriate
- MMU is now has a non-cacheable DDR region (used by LCD and GMAC examples)

### Fixes

- RAM timings / configuration adjusted for sama5d2-xplained target
- Component headers in target/sama5d2/components updated to reflect latest
  datasheet updates
- PIO and TRNG callbacks now have a configurable user-defined argument
