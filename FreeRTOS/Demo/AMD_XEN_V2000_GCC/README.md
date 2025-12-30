# FreeRTOS port for Xen
This repository contains source for FreeRTOS port for xen.

# FreeRTOS port to Xen HVM

## Setup Build Environement

1. Build Host Operating System - Ubuntu 22.04
2. Install Dependencies
   
   `apt install -y build-essential grub-common mtools nasm xorriso gcc-multilib`


## Build FreeRTOS
1. Clone FreeRTOS repository

   `cd $HOME`
   
   `git clone https://github.com/FreeRTOS/FreeRTOS.git --recurse-submodules`

   `cd FreeRTOS/FreeRTOS/Source/`

   `git checkout V11.2.0`

   The above common will clone FreeRTOS resposity in the current working directoy, FreeRTOS kernel source will be cloned under FreeRTOS/FreeRTOS/Source.

2. Build 32-bit FreeRTOS port
   
   export FREERTOS_DIR=&lt;path containing Source folder from cloned FreeRTOS repository&gt;
   
   for example export FREERTOS_DIR=$HOME/FreeRTOS/FreeRTOS if git clone for FreeRTOS was done under home directory

   `export FREERTOS_DIR=$HOME/FreeRTOS/FreeRTOS`

    `cd $HOME`
   
   `git clone https://github.com/AMD-EMBAUTO/FreeRTOS/ FreeRTOS-X86`

   `cd FreeRTOS-X86`

   `git checkout v4.0`
   
   `cd port_32`
   
   `make clean`

   `make`

   Make will generate an image file in output/freertos-v4.0-x86_32.iso
3. Build 64-bit FreeRTOS port
   
   export FREERTOS_DIR=&lt;path containing Source folder from cloned FreeRTOS repository&gt;
   
   for example export FREERTOS_DIR=$HOME/FreeRTOS/FreeRTOS if git clone for FreeRTOS was done under home directory

   `export FREERTOS_DIR=$HOME/FreeRTOS/FreeRTOS`

    `cd $HOME`
   
   `git clone https://github.com/AMD-EMBAUTO/FreeRTOS/ FreeRTOS-X86`

   `cd FreeRTOS-X86`

   `git checkout v4.0`
   
   `cd port_64`
   
   `make clean`

   `make`

   Make will generate an image file in output/freertos-v4.0-x86_64.iso

## Create FreeRTOS xen HVM on Celadon board with Yocto

1. Copy HVM and ISO files to board

   use scp command to copy following files
   - freertos-v4.0-x86_32.iso
   - freertos32_v4.0.bin
   - freertos_x86_32.hvm
   - freertos_x86_32.pvh
   - freertos-v4.0-x86_64.iso
   - freertos64_v4.0.bin
   - freertos_x86_64.pvh
   - freertos_x86_64.hvm
   
2. Launch FreeRTOS xen HVM

   *32-bit*

   `xl create freertos_x86_32.hvm`

    *64-bit*

   `xl create freertos_x86_64.hvm` 

3. Launch FreeRTOS xen PVH 

   *32-bit*

   `xl create freertos_x86_32.pvh`

    *64-bit*

   `xl create freertos_x86_64.pvh` 

4. Check DomU created
   
   `xl list`
   
5. Connect to console using minicom debug port
   - find domain id using xl list
   - xenstore-read /local/domain/{domain_id}/console/tty
   - minicom -D <output_of_above_command>

6. Connect to xl console
   - xl console <domain_id|domain_name>

