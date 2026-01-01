/* freertos_acpica
 *
 * Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
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
 *
 */

#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "semphr.h"
#include <string.h>
#include "queue.h"
#define ACPI_SYSTEM_XFACE
#include "platform/aclinux.h"
#include "actypes.h"
#include "acexcep.h"
#include "acrestyp.h"
#include "actbl.h"
#include "stdio.h"
#include "console.h"
#include "io.h"
#include "ioapic.h"
#include "time.h"
#define ACPI_SIG_RSDP "RSD PTR "

#define ACPI_MADT_SIG          "APIC"

#define ACPI_DEVICE_HID_STRING_SIZE 9
#define ACPI_DEVICE_UID_STRING_SIZE 9

void *malloc(unsigned int);
void free(void *);

typedef struct support_devices_type {
    char name[8];
    uint32_t type;  
} support_devices_type;

/* Supported devices types */
#define MAX_SUPPORTED_DEVICE_TYPES 2
#define DEVICE_TYPE_UART_AMDI0020 0
#define DEVICE_TYPE_I2C_AMDI0010 1
#define DEVICE_TYPE_HPET_PNP0103 2
support_devices_type supported_devices[] = { {"AMDI0020", DEVICE_TYPE_UART_AMDI0020}, {"AMDI0010", DEVICE_TYPE_I2C_AMDI0010}};

typedef struct {
    char hid[ACPI_DEVICE_HID_STRING_SIZE];  // HID (Hardware ID)
#if defined(__x86_64__)
    int64_t uid;  // UID (Unique ID)
#else
    int32_t uid;  // UID (Unique ID)
#endif
    uint32_t dev_irq;
    uint32_t dev_base_address;
    uint32_t irq[16];                         // List of IRQs (up to 16)
    uint32_t exirq[16];                       // List of extended IRQs (up to 16)
    int irq_count;                            // Number of IRQs found
    uint32_t min_address[16];                 // Minimum memory address
    uint32_t max_address[16];                 // Maximum memory address
    uint32_t address_length[16];              // Address length
    uint32_t granularity[16];                 // Granularity

} DeviceData;


int AcpiEvaluateObject (
    ACPI_HANDLE             Object,
    ACPI_STRING             Pathname,
    ACPI_OBJECT_LIST        *ParameterObjects,
    ACPI_BUFFER             *ReturnObjectBuffer);

int AcpiGetCurrentResources (
    ACPI_HANDLE             Device,
    ACPI_BUFFER             *RetBuffer);

int AcpiInitializeSubsystem (
    void);

int AcpiInitializeTables (
    ACPI_TABLE_DESC         *InitialStorage,
    UINT32                  InitialTableCount,
    BOOLEAN                 AllowResize);

int AcpiLoadTables (
    void);
int AcpiInitializeObjects (
    UINT32                  Flags);
int AcpiGetHandle (
    ACPI_HANDLE             Parent,
    const char              *Pathname,
    ACPI_HANDLE             *RetHandle);

int AcpiGetNextObject (
    ACPI_OBJECT_TYPE        Type,
    ACPI_HANDLE             Parent,
    ACPI_HANDLE             Child,
    ACPI_HANDLE             *OutHandle);
int AcpiGetTable (
    char                    *Signature,
    UINT32                  Instance,
    ACPI_TABLE_HEADER       **OutTable);

/* This following store number of supported device found and their information */

/* Only first 2 UART and first 2 I2C devices are used. Remaining are found but ignored.*/
#define MAX_SUPPORTED_DEVICES 16
int num_device=0; /* Total Number of devices found */
DeviceData device_list[MAX_SUPPORTED_DEVICES];

/* UART device info */
#define MAX_UART_DEVICES 2
int num_uart_devices = 0;
DeviceData *uart_device_info[MAX_UART_DEVICES];

/* I2C device info */
#define MAX_I2C_DEVICES 2
int num_i2c_devices = 0;
DeviceData *i2c_device_info[MAX_I2C_DEVICES];

/* local apic address */
UINT32 local_apic_address = 0xFEE00000UL;
UINT32 facs_address = 0x0UL;

typedef struct acpi_madt_header {
    ACPI_TABLE_HEADER Header; // Standard ACPI table header
    UINT32             LocalApicAddress; // Address of the Local APIC
    UINT32            Flags; // Flags field (bitmask)
} ACPI_MADT_HEADER;

/* RSDP Table Header */
typedef struct {
    char signature[8];
    uint8_t checksum;
    char oem_id[6];
    uint8_t revision;
    uint32_t rsdt_address;  // 32-bit physical address of RSDT
} __attribute__((packed)) RSDPDescriptor;

/* Table Header of other ACPI tables */
typedef struct {
    char signature[4];
    uint32_t length;
    uint8_t revision;
    uint8_t checksum;
    char oem_id[6];
    char oem_table_id[8];
    uint32_t oem_revision;
    uint32_t creator_id;
    uint32_t creator_revision;
} __attribute__((packed)) ACPITableHeader;

// Function to compute checksum (used in ACPI tables)
uint8_t acpi_checksum(void *ptr, size_t len) {
    uint8_t *data = (uint8_t *)ptr;
    uint8_t sum = 0;
    for (size_t i = 0; i < len; i++) {
        sum += data[i];
    }
    return sum;
}

// read TSC
static inline uint64_t rdtsc(void) {
    unsigned int lo, hi;
    __asm__ volatile("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

// Function to find RSDP in memory
RSDPDescriptor *find_rsdp() {
    for (uintptr_t addr = (uintptr_t)0x000E0000; addr < (uintptr_t)0x00100000; addr += 16) {
        RSDPDescriptor *rsdp = (RSDPDescriptor *)addr;
        if (memcmp(rsdp->signature, ACPI_SIG_RSDP, 8) == 0 &&
            acpi_checksum(rsdp, sizeof(RSDPDescriptor)) == 0) {
            return rsdp;
        }
    }
    return NULL;
}


void AeTableOverride (
    ACPITableHeader       *ExistingTable,
    ACPITableHeader       **NewTable) {
    *NewTable = ExistingTable;
}

RSDPDescriptor *rsdp = NULL;
ACPI_TABLE_DESC table_store[128];

void *AcpiOsGetRootPointer ( void) {
    return rsdp;
}

void parse_resource_buffer(ACPI_BUFFER *buffer, DeviceData *data) {
    ACPI_RESOURCE *resource = (ACPI_RESOURCE *)buffer->Pointer;
    UINT8 *current = (UINT8 *)resource;
    UINT8 *end = current + buffer->Length;
    int mem_count =0;
    // Iterate over each resource in the buffer
    while (current < end) {
        resource = (ACPI_RESOURCE *)current;
        // Check the resource type and extract relevant data
        switch (resource->Type) {
            case ACPI_RESOURCE_TYPE_EXTENDED_IRQ: {
                ACPI_RESOURCE_EXTENDED_IRQ *exirq = &resource->Data.ExtendedIrq;
                for (int i = 0; i < exirq->InterruptCount; i++) {
                    data->dev_irq=exirq->Interrupts[i];
                }
                break;
	    }
            case ACPI_RESOURCE_TYPE_IRQ: {
                ACPI_RESOURCE_IRQ *irq = &resource->Data.Irq;
                for (int i = 0; i < irq->InterruptCount; i++) {
                    data->dev_irq=irq->Interrupts[i];
                }
                break;
            }
            case ACPI_RESOURCE_TYPE_ADDRESS64: {
                ACPI_RESOURCE_ADDRESS64 *address = &resource->Data.Address64;
                break;
            }
            case ACPI_RESOURCE_TYPE_ADDRESS32: {
                ACPI_RESOURCE_ADDRESS32 *address = &resource->Data.Address32;
		data->dev_base_address=address->Address.Minimum;                     // Minimum memory address
                data->min_address[mem_count]=address->Address.Minimum;                     // Minimum memory address
                data->max_address[mem_count]=address->Address.Maximum;                     // Maximum memory address
                data->address_length[mem_count]=address->Address.AddressLength;            // Address length
                data->granularity[mem_count]=address->Address.Granularity;
                mem_count++;
		break;
            }
	    case ACPI_RESOURCE_TYPE_FIXED_MEMORY32: {
                ACPI_RESOURCE_FIXED_MEMORY32 *fixed_mem = &resource->Data.FixedMemory32;
		data->dev_base_address=fixed_mem->Address;                     // Minimum memory address
                data->min_address[mem_count]=fixed_mem->Address;                     // Minimum memory address
                data->max_address[mem_count]=fixed_mem->Address + fixed_mem->AddressLength - 1;                     // Maximum memory address
                data->address_length[mem_count]=fixed_mem->AddressLength;            // Address length
                mem_count++;
                break;
            }				       
            default:
                // Handle other resource types if necessary
                 break;
        }
        // Move to the next resource descriptor
        current += resource->Length;
    }
}

void save_data(ACPI_HANDLE device_handle, DeviceData *data)
{
    int status;
    ACPI_BUFFER result;
    result.Length = ACPI_ALLOCATE_BUFFER; // ACPICA will allocate memory for us
    result.Pointer = NULL;
    //Find UID
    status = AcpiEvaluateObject(device_handle, "_UID", NULL, &result);
    if(ACPI_FAILURE(status)){
        return;
    }

    ACPI_OBJECT *object = (ACPI_OBJECT *)result.Pointer;
    data->uid= object->Integer.Value;
    free(result.Pointer);

    //Base Address finding
    ACPI_BUFFER crsBuffer;
    crsBuffer.Length = ACPI_ALLOCATE_BUFFER;
    crsBuffer.Pointer = NULL;
    status = AcpiGetCurrentResources(device_handle,&crsBuffer);
    if(ACPI_FAILURE(status)){
        return;
    }

    // Parse the resource buffer to extract IRQ and memory information
    parse_resource_buffer(&crsBuffer, data);
    free(crsBuffer.Pointer);
}

void get_device_hid_uid_memory(ACPI_HANDLE device_handle){
    int status;
    ACPI_BUFFER result;
    result.Length = ACPI_ALLOCATE_BUFFER;
    result.Pointer = NULL;
    //Find _HID :Device Name
    status = AcpiEvaluateObject(device_handle, "_HID", NULL, &result);
    if(ACPI_FAILURE(status)){
        return;
    }

    ACPI_OBJECT *object = (ACPI_OBJECT *)result.Pointer;
    if (object && object->Type == (ACPI_OBJECT *)ACPI_TYPE_STRING){
        int dev_info_parser= FALSE;
        uint32_t device_type = -1;
        //Find required device available or not
        for(int i=0;i<MAX_SUPPORTED_DEVICE_TYPES;i++){
            if(strncmp(object->String.Pointer,supported_devices[i].name,8)==0){
                dev_info_parser = TRUE;
                device_type = supported_devices[i].type;
                break;
            }
        }
        // If device matches, find device info
        if(dev_info_parser){
            if (num_device < MAX_SUPPORTED_DEVICES) {
                strncpy(device_list[num_device].hid, object->String.Pointer, ACPI_DEVICE_HID_STRING_SIZE);
                save_data(device_handle,&device_list[num_device]);
                if (device_type == (uint32_t)DEVICE_TYPE_UART_AMDI0020) {
                    if (num_uart_devices < MAX_UART_DEVICES) {
                        uart_device_info[num_uart_devices] = &device_list[num_device];
                        num_uart_devices++;
                    } else {
                        printk("WARNING: UART device ignored as already detected: %d UART devices\n",num_uart_devices);
                    }
                } else if (device_type == (uint32_t)DEVICE_TYPE_I2C_AMDI0010) {
                    if (num_i2c_devices < MAX_I2C_DEVICES) {
                        i2c_device_info[num_i2c_devices] = &device_list[num_device];
                        num_i2c_devices++;
                    } else {
                        printk("WARNING: I2C device ignored as already detected: %d I2C devices\n",num_i2c_devices);
                    }
                }
                num_device++;
            } else {
                printk("WARNING: Device ignored as already detected: %d supported devices\n",num_device);
            }
        }
    }
    free(result.Pointer);
}

void get_devices_info(ACPI_HANDLE parent ) {
    int status;
    ACPI_HANDLE child = NULL;
    while (ACPI_SUCCESS(status = (int)AcpiGetNextObject(ACPI_TYPE_DEVICE, parent, child, &child))) {
        get_device_hid_uid_memory(child);
        get_devices_info(child);
    }
}

extern ACPI_TABLE_FADT         AcpiGbl_FADT;
ACPI_TABLE_FACS *Facs;
#define SCI_STS 0x200
#define WAK_STS 0x100
void acpi_set_firmware_waking_vector(void *waking_vector)
{
     Facs->XFirmwareWakingVector = (uint32_t)0;
     Facs->FirmwareWakingVector = (uint32_t)waking_vector;
}
void enable_sci()
{
     uint16_t pm1a_en = inw(AcpiGbl_FADT.Pm1aEventBlock + 2);
     pm1a_en |= (SCI_STS|WAK_STS);
     outw(AcpiGbl_FADT.Pm1aEventBlock + 2, pm1a_en);
     uint16_t gpe_en = inw(AcpiGbl_FADT.Gpe0Block+2);
     gpe_en |= 0x6;
     outw(AcpiGbl_FADT.Gpe0Block,gpe_en);
     set_ioapic_irq_mask(9, 0);
}
void process_sci(void)
{
    static uint32_t is_sleeping = 0;
    uint64_t resume_start_time = rdtsc();
    uint64_t resume_complete_time; 
    extern uint32_t is_pvh;
    if (is_pvh == 1) {
        uint16_t pm1a_sts = inw(AcpiGbl_FADT.Pm1aEventBlock);
        if ((pm1a_sts == SCI_STS) && (is_sleeping == 0)) {
            pm1a_sts |= SCI_STS;
            outw(AcpiGbl_FADT.Pm1aEventBlock, pm1a_sts);
            fini_time();
            is_sleeping = 1;
            printk("Sleeping\n");
            vTaskSuspendAll();
        } else {
            pm1a_sts |= WAK_STS;
            outw(AcpiGbl_FADT.Pm1aEventBlock, pm1a_sts);
	    if (is_sleeping == 1) {
                init_time();
                is_sleeping = 0;
                xTaskResumeAll();
                resume_complete_time = rdtsc();
                printk("Resumed from Sleep. Time Take: %d cycles\n", resume_complete_time - resume_start_time);
	    }
        }
    } else {
    }
}
void get_facs_address()
{
    Facs = AcpiGbl_FADT.Facs;
}
void get_apiclocal_address()
{
    int status;
    ACPI_TABLE_HEADER *madt_table;
    ACPI_MADT_HEADER *madt_header;
    status = AcpiGetTable(ACPI_MADT_SIG, 0, &madt_table);
    if (ACPI_FAILURE(status)) {
        printk("MADT not found\n");
        return;
    }
    // Cast to the MADT header
    madt_header = (ACPI_MADT_HEADER *)madt_table;
    // Retrieve the Local APIC address
    local_apic_address = madt_header->LocalApicAddress;
}

void main_acpica( void )
{
    ACPI_HANDLE root_handle;
    if (rsdp == NULL){
        rsdp = find_rsdp();
    }
    // -------ACPICA Initialization------------------------------------------------------
    int status;
    status =AcpiInitializeSubsystem();
    if (ACPI_FAILURE(status)) {
        printk("ERROR AcpiInitializeSubsystem  status  %d\n",status);
        return;
    }
    status = AcpiInitializeTables(table_store,32,1);
    if (ACPI_FAILURE(status)) {
        printk("ERROR AcpiInitializeTable  status %d\n",status);
        return;
    }
    status = AcpiLoadTables();
    if (ACPI_FAILURE(status)) {
        printk("ERROR AcpiLoadTablestatus %d\n",status);
        return;
    }
    status = AcpiInitializeObjects(ACPI_FULL_INITIALIZATION);
    if (ACPI_FAILURE(status)) {
        printk("ERROR AcpiInitializeObjects  %d\n",status);
        return;
    }
    //------get localapic address------
    get_apiclocal_address();


    // -------Get device info----------
    status = AcpiGetHandle(NULL, "\\", &root_handle);
    if (ACPI_FAILURE(status)) {
        printk("ERROR AcpiGetHandle  %d\n",status);
        return;
    }

    get_devices_info(root_handle);
    get_facs_address(root_handle);

}

uint32_t get_uart_base_addr(uint32_t i) {
    if (i < (uint32_t)num_uart_devices) {
        return uart_device_info[i]->dev_base_address;
    }
    return 0;
}
uint32_t get_uart_irq(uint32_t i) {
    if (i < (uint32_t)num_uart_devices) {
        return uart_device_info[i]->dev_irq;
    }
    return 0;
}
uint32_t get_num_uart_devices(void) {
    return num_uart_devices;
}
uint32_t get_i2c_base_addr(uint32_t i) {
    if (i < (uint32_t)num_i2c_devices) {
        return i2c_device_info[i]->dev_base_address;
    }
    return 0;
}
uint32_t get_i2c_irq(uint32_t i) {
    if (i < (uint32_t)num_i2c_devices) {
        return i2c_device_info[i]->dev_irq;
    }
    return 0;
}
uint32_t get_num_i2c_devices(void) {
    return num_i2c_devices;
}

