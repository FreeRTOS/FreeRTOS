/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 * @file mss_io_config.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief MSS IO related code
 *
 */

#ifndef xUSER_CONFIG_MSS_DDRC_MSS_IO_CONFIG_H_
#define xUSER_CONFIG_MSS_DDRC_MSS_IO_CONFIG_H_


#ifdef __cplusplus
extern "C" {
#endif

/*
 * There are 38 general purpose IO pads, referred to as MSSIO, to support
 * peripheral devices. System registers will select which signals are connected
 * to the IO pads. These are in addition to the SGMII IO for the Ethernet MACs,
 * DDR I/O and two IOs to allow interfacing to an external 32kHz crystal. All
 * of these MSSIOs are bonded out to pins in all packages. The MSSIOs may be
 * configured as the IOs of any of the MSS peripherals listed in the table
 * below.
 */

/*
    - MUX -> PAD options set by Libero, register iomux1_cr to iomux5_cr
    | option        | value         | Info  |
    |:-------------:|:-------------:|:-----:|
    | SD_SDIO       | 0x0           |       |
    | EMMC          | 0x1           |       |
    | QSPI          | 0x2           |       |
    | SPI           | 0x3           |       |
    | USB           | 0x4           |       |
    | MMUART        | 0x5           |       |
    | I2C           | 0x6           |       |
    | CAN           | 0x7           |       |
    | MDIO          | 0x8           |       |
    | Miscellaneous | 0x9           |       |
    | Reservedx     | 0xA           |       |
    | GPIO_PAD      | 0xB           |       |
    | Fabric_test   | 0xC           |       |
    | Logic_0       | 0xD           |       |
    | Logic_1       | 0xE           |       |
    | Tristate      | 0xF           |Default|
 */

/**
 * \brief IOMUX configuration
 */
typedef struct IOMUX_CONFIG_ {
    __IO uint32_t iomux0_cr;     /* peripheral is connected to the Fabric or
                                    IOMUX structure */
    __IO uint32_t iomux1_cr;     /* BNK4 SDV PAD 0 to 7      */
    __IO uint32_t iomux2_cr;     /* BNK4 SDV PAD 8 to 13     */
    __IO uint32_t iomux3_cr;     /* BNK2 SDV PAD 14 to 21    */
    __IO uint32_t iomux4_cr;     /* BNK2 SDV PAD 22 to 29    */
    __IO uint32_t iomux5_cr;     /* BNK2 PAD 30 to 37        */
    __IO uint32_t iomux6_cr;     /* MMC/SD Voltage select lines are inverted on
                                    entry to the IOMUX structure */
} IOMUX_CONFIG;



/*
    pcode, ncode and drive strength for each bank is set using direct writes to
    the SCB registers

    The MSS IO pad configuration is provided by nineteen system registers
    each configuring two IO's using 15-bits per IO
    Theses registers are located in the MSS sysreg.

    - (mssio_bank*_io_cfg_*_*_cr).

   | mssio_bank*_io_cfg_*_*_cr | offset        | info |
   | field                     |               | info |
   |:-------------------------:|:-------------:|:-----|
   |      io_cfg_ibufmd_0      |0              |      |
   |      io_cfg_ibufmd_1      |1              |      |
   |      io_cfg_ibufmd_2      |2              |      |
   |      io_cfg_drv_0         |3              |      |
   |      Io_cfg_drv_1         |4              |      |
   |      Io_cfg_drv_2         |5              |      |
   |      io_cfg_drv_3         |6              |      |
   |      io_cfg_clamp         |7              |      |
   |      io_cfg_enhyst        |8              |      |
   |      io_cfg_lockdn_en     |9              |      |
   |      io_cfg_wpd           |10             |      |
   |      io_cfg_wpu           |11             |      |
   |      io_cfg_atp_en        |12             |      |
   |      io_cfg_lp_persist_en |13             |      |
   |      io_cfg_lp_bypass_en  |14             |      |

*/

/**
 * \brief Bank 2 and 4 voltage settings
 *
 */
typedef struct HSS_MSSIO_Bank_Config_ {
    __IO uint32_t mssio_bank4_pcode_ncode_vs;   /* bank 4- set pcode, ncode and
                                                   drive strength */
    __IO uint32_t mssio_bank2_pcode_ncode_vs;   /* bank 2- set pcode, ncode and
                                                   drive strength */
}MSSIO_BANK_CONFIG;

/**
 * \brief MSS IO Bank 4 configuration
 */
typedef struct MSSIO_Bank4_IO_Config_ {
    __IO uint32_t mssio_bank4_io_cfg_0_cr;   /* x_vddi Ratio Rx<0-2> == 001
                                                drv<3-6> == 1111
                                                7:clamp   == 0
                                                enhyst   == 0
                                                lockdn_en == 1
                                                10:wpd  == 0
                                                atp_en`== 0
                                                lpmd_ibuf  == 0
                                                lpmd_obuf == 0
                                                persist == 0
                                                */
    __IO uint32_t mssio_bank4_io_cfg_1_cr;
    __IO uint32_t mssio_bank4_io_cfg_2_cr;
    __IO uint32_t mssio_bank4_io_cfg_3_cr;
    __IO uint32_t mssio_bank4_io_cfg_4_cr;
    __IO uint32_t mssio_bank4_io_cfg_5_cr;
    __IO uint32_t mssio_bank4_io_cfg_6_cr;

}MSSIO_BANK4_CONFIG;

/**
 * \brief MSS IO Bank 2 configuration
 */
typedef struct MSSIO_Bank2_IO_Config_ {
    __IO uint32_t mssio_bank2_io_cfg_0_cr;   /* x_vddi Ratio Rx<0-2> == 001
                                                drv<3-6> == 1111
                                                7:clamp   == 0
                                                enhyst   == 0
                                                lockdn_en == 1
                                                10:wpd  == 0
                                                atp_en`== 0
                                                lpmd_ibuf  == 0
                                                lpmd_obuf == 0
                                                persist == 0
                                                */
    __IO uint32_t mssio_bank2_io_cfg_1_cr;
    __IO uint32_t mssio_bank2_io_cfg_2_cr;
    __IO uint32_t mssio_bank2_io_cfg_3_cr;
    __IO uint32_t mssio_bank2_io_cfg_4_cr;
    __IO uint32_t mssio_bank2_io_cfg_5_cr;
    __IO uint32_t mssio_bank2_io_cfg_6_cr;
    __IO uint32_t mssio_bank2_io_cfg_7_cr;
    __IO uint32_t mssio_bank2_io_cfg_8_cr;
    __IO uint32_t mssio_bank2_io_cfg_9_cr;
    __IO uint32_t mssio_bank2_io_cfg_10_cr;
    __IO uint32_t mssio_bank2_io_cfg_11_cr;
}MSSIO_BANK2_CONFIG;


/***************************************************************************//**
  The int32_t mssio_setup(void)()

  Setup the IOMUX and IO bank 2 and 4.
  The values used in this function are set by Libero.
  It configures the I/O mux, which detemines what peripherals are connected to
  what pins, and the electrical properties of each bank and each I/O.

  @return
    This function returns status, 0 => OK

  Example:
  @code

        error |= mssio_setup();

  @endcode

 */
uint8_t
mssio_setup
(
    void
);


/***************************************************************************//**
  The gpio_toggle_test(void)()

  Toggle a GPIO PIN on start-up

  @return
    This function returns status, 0 => OK

  Example:
  @code

        error |= mssio_setup();

  @endcode

 */
int32_t
gpio_toggle_test
(
    void
);

/***************************************************************************//**
  set_bank2_and_bank4_volts()
  Sets bank 2 and 4 voltages, with Values coming from Libero

  Example:

  @code

  set_bank2_and_bank4_volts();

  @endcode

 *
 */
void
set_bank2_and_bank4_volts
(
   void
);


#ifdef __cplusplus
}
#endif

#endif /* USER_CONFIG_MSS_DDRC_MSS_IO_CONFIG_H_ */
