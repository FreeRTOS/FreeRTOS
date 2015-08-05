#/******************************************************************************
#*
#* Copyright (C) 2015 Xilinx, Inc.  All rights reserved.
#*
#* Permission is hereby granted, free of charge, to any person obtaining a copy
#* of this software and associated documentation files (the "Software"), to deal
#* in the Software without restriction, including without limitation the rights
#* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
#* copies of the Software, and to permit persons to whom the Software is
#* furnished to do so, subject to the following conditions:
#*
#* The above copyright notice and this permission notice shall be included in
#* all copies or substantial portions of the Software.
#*
#* Use of the Software is limited solely to applications:
#* (a) running on a Xilinx device, or
#* (b) that interact with a Xilinx device through a bus or interconnect.
#*
#* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#* XILINX CONSORTIUM BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
#* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
#* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
#* SOFTWARE.
#*
#* Except as contained in this notice, the name of the Xilinx shall not be used
#* in advertising or otherwise to promote the sale, use or other dealings in
#* this Software without prior written authorization from Xilinx.
#*
#******************************************************************************/

proc swapp_get_name {} {
    return "FreeRTOS Hello World";
}

proc swapp_get_description {} {
    return " FreeRTOS Hello World application";
}

proc check_freertos_os {} {
    set oslist [get_os];

    if { [llength $oslist] != 1 } {
        return 0;
    }
    set os [lindex $oslist 0];

    if { $os != "freertos822_xilinx" } {
        error "This application is supported only on the freertos822_xilinx.";
    }
}

proc swapp_is_supported_sw {} {

    check_freertos_os

    return 1;
}

proc swapp_is_supported_hw {} {

    # check processor type
    set proc_instance [get_sw_processor];
    set hw_processor [common::get_property HW_INSTANCE $proc_instance]

    set proc_type [common::get_property IP_NAME [get_cells $hw_processor]];

    if { $proc_type != "ps7_cortexa9" && $proc_type != "microblaze" } {
                error "This application is supported only for ps7_cortexa9 and microblaze processors.";
    }

    return 1;
}


proc get_stdout {} {
    return;
}

proc check_stdout_hw {} {
    return;
}

proc swapp_generate {} {
    return;
}

proc swapp_get_linker_constraints {} {
    return "";
}
