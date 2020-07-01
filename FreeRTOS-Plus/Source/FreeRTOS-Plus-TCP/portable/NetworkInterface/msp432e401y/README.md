
## Usage

This driver require the following defines in `FreeRTOSIPConfig.h`

```c
/*in FreeRTOSIPConfig.h */
#define ipconfigUSE_LINKED_RX_MESSAGES 0
#define ipconfigZERO_COPY_TX_DRIVER 1
``` 

This driver can use the following defines in `FreeRTOSIPConfig.h`

```c
#define ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM 0
#define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM 0
``` 

The user must provide a global structure called `g_EMAC_DriverAttrs` containing a pointer to the macaddress and other driver configutaions. The file `MSP432E4_Networkinterface.h` sould be included.
```c
/* array containing macaddress as needed in freeRTOS+TCP */
uint8_t ucMACAddress[ 6 ] = { 0xff,0xff,0xff, 0xff, 0xff, 0xff};
/* EMAC configuration structure */
const EMACMSP432E4_DriverAttrs g_EMAC_DriverAttrs = {
    .intNum = INT_EMAC0,
    .intPriority = (~0),
    .led0Pin = EMACMSP432E4_PF0_EN0LED0,
    .led1Pin = EMACMSP432E4_PF4_EN0LED1,
    .macAddress = ucMACAddress
};
``` 

