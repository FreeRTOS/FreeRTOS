##############################################################################
#
# (c) Copyright 2011 Xilinx, Inc. All rights reserved.
#
# This file contains confidential and proprietary information of Xilinx, Inc.
# and is protected under U.S. and international copyright and other
# intellectual property laws.
#
# DISCLAIMER
# This disclaimer is not a license and does not grant any rights to the
# materials distributed herewith. Except as otherwise provided in a valid
# license issued to you by Xilinx, and to the maximum extent permitted by
# applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
# FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS,
# IMPLIED, OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF
# MERCHANTABILITY, NON-INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE;
# and (2) Xilinx shall not be liable (whether in contract or tort, including
# negligence, or under any other theory of liability) for any loss or damage
# of any kind or nature related to, arising under or in connection with these
# materials, including for any direct, or any indirect, special, incidental,
# or consequential loss or damage (including loss of data, profits, goodwill,
# or any type of loss or damage suffered as a result of any action brought by
# a third party) even if such damage or loss was reasonably foreseeable or
# Xilinx had been advised of the possibility of the same.
#
# CRITICAL APPLICATIONS
# Xilinx products are not designed or intended to be fail-safe, or for use in
# any application requiring fail-safe performance, such as life-support or
# safety devices or systems, Class III medical devices, nuclear facilities,
# applications related to the deployment of airbags, or any other applications
# that could lead to death, personal injury, or severe property or
# environmental damage (individually and collectively, "Critical
# Applications"). Customer assumes the sole risk and liability of any use of
# Xilinx products in Critical Applications, subject only to applicable laws
# and regulations governing limitations on product liability.
#
# THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE
# AT ALL TIMES.
#
# This file is part of FreeRTOS.
#
# $Id: freertos_v2_1_0.tcl,v 1.1.2.8 2010/12/10 07:27:08 svemula Exp $
###############################################################################

# standalone bsp version. set this to the latest "ACTIVE" version.
set standalone_version standalone_v3_01_a

proc kernel_drc {os_handle} {
    set sw_proc_handle [xget_libgen_proc_handle]
    set hw_proc_handle [xget_handle $sw_proc_handle "IPINST"]
    set proctype [xget_value $hw_proc_handle "OPTION" "IPNAME"]
    set compiler [xget_value $sw_proc_handle "PARAMETER" "COMPILER"]

    # check for valid compiler
    if { [string first "mb-gcc" $compiler] == 0 && [string first "mb-g++" $compiler] == 0} {
        error "Wrong compiler requested. FreeRTOS can be compiled only with the GNU compiler for MicroBlaze." "" "mdt_error"
    }

    # check for valid stdio parameters
    set stdin [xget_value $os_handle "PARAMETER" "STDIN"]
    set stdout [xget_value $os_handle "PARAMETER" "STDOUT"]
    if { $stdin == "none" || $stdout == "none" } {
        error "The STDIN/STDOUT parameters are not set. FreeRTOS requires stdin/stdout to be set." "" "mdt_error"
    }

    # check if the design has a intc
    set intr_port [xget_value $hw_proc_handle "PORT" "Interrupt"]
    if { [llength $intr_port] == 0 } {
        error "CPU has no connection to Interrupt controller." "" "mdt_error"
    }

    # support only AXI/PLB
    set interconnect [xget_value $hw_proc_handle "PARAMETER" "C_INTERCONNECT"]
    if { $interconnect == 1 } {
        set bus_name [xget_hw_busif_value $hw_proc_handle "DPLB"]
    } elseif { $interconnect == 2 } {
        set bus_name [xget_hw_busif_value $hw_proc_handle "M_AXI_DP"]
    } else {
        error "FreeRTOS supports Microblaze with only a AXI or PLB interconnect" "" "mdt_error"
    }

    # obtain handles to all the peripherals in the design
    set mhs_handle [xget_hw_parent_handle $hw_proc_handle]
    set slave_ifs [xget_hw_connected_busifs_handle $mhs_handle $bus_name "slave"]
    set timer_count 0
    set timer_has_intr 0

    # check for a valid timer
    foreach if $slave_ifs {
        set ip_handle [xget_hw_parent_handle $if]

        if {$ip_handle != $hw_proc_handle} {
            set type [xget_hw_value $ip_handle]
            if { $type == "xps_timer" || $type == "axi_timer" } {
                incr timer_count
                
                # check if the timer interrupts are enabled
                set intr_port [xget_value $ip_handle "PORT" "Interrupt"]
                if { [llength $intr_port] != 0 } {
                    set timer_has_intr 1
                }
            }
        }
    }

    if { $timer_count == 0 } {
        error "FreeRTOS for Microblaze requires an axi_timer or xps_timer. The HW platform doesn't have a valid timer." "" "mdt_error"
    }

    if { $timer_has_intr == 0 } {
        error "FreeRTOS for Microblaze requires interrupts enabled for a timer." "" "mdt_error"
    }

    set systmr_interval_ms [xget_value $os_handle "PARAMETER" "systmr_interval"]
    if { $systmr_interval_ms <= 0 } {
        error "Invalid value for parameter systmr_interval specified. Please specify a positive value." "" "mdt_error"
    }

    ### ToDo: Add DRC specific to FreeRTOS
}

proc generate {os_handle} {

    variable standalone_version

    set sw_proc_handle [xget_libgen_proc_handle]
    set hw_proc_handle [xget_handle $sw_proc_handle "IPINST"]
    set proctype [xget_value $hw_proc_handle "OPTION" "IPNAME"]
    set procver [xget_value $hw_proc_handle "PARAMETER" "HW_VER"]
    
    set need_config_file "false"

    # proctype should be "microblaze"
    set mbsrcdir  "../${standalone_version}/src/microblaze"
    set commondir   "../${standalone_version}/src/common"
    set datadir   "../${standalone_version}/data"

    foreach entry [glob -nocomplain [file join $commondir *]] {
        file copy -force $entry [file join ".." "${standalone_version}" "src"]
    }
    
    # proctype should be "microblaze"
    switch -regexp $proctype {
        "microblaze" { 

            foreach entry [glob -nocomplain [file join $mbsrcdir *]] {
                if { [string first "microblaze_interrupt_handler" $entry] == -1 } { ;# Do not copy over the Standalone BSP exception handler
                    file copy -force $entry [file join ".." "${standalone_version}" "src"]
                }
            }
            set need_config_file "true"
        }
        "default" {puts "unknown processor type $proctype\n"}
    }

    # Write the config.make file
    set makeconfig [open "../standalone_v3_01_a/src/config.make" w]  
    xprint_generated_header_tcl $makeconfig "Configuration parameters for Standalone Makefile"

    if { $proctype == "microblaze" } {
        if { [mb_has_exceptions $hw_proc_handle] } {
            puts $makeconfig "LIBSOURCES = *.s *.c *.S"
        } else {
            puts $makeconfig "LIBSOURCES = *.s *.c"
        }
    }

    puts $makeconfig "LIBS = standalone_libs"
    close $makeconfig

    # Remove microblaze directories...
    file delete -force $mbsrcdir

    # copy required files to the main src directory
    file copy -force [file join src Source tasks.c] src
    file copy -force [file join src Source queue.c] src
    file copy -force [file join src Source list.c] src
    file copy -force [file join src Source timers.c] src
    file copy -force [file join src Source portable MemMang heap_3.c] src
    file copy -force [file join src Source portable GCC MicroBlazeV8 port.c] src
    file copy -force [file join src Source portable GCC MicroBlazeV8 port_exceptions.c] src
    file copy -force [file join src Source portable GCC MicroBlazeV8 portasm.S] src
    file copy -force [file join src Source portable GCC MicroBlazeV8 portmacro.h] src
    set headers [glob -join ./src/Source/include *.\[h\]]
    foreach header $headers {
        file copy -force $header src
    }

    file delete -force [file join src Source]
    file delete -force [file join src Source]

    # Handle stdin and stdout
    xhandle_stdin $os_handle
    xhandle_stdout $os_handle

    # Create config file for microblaze interrupt handling
    if {[string compare -nocase $need_config_file "true"] == 0} {
        xhandle_mb_interrupts
    }

    # Create config files for Microblaze exception handling
    if { $proctype == "microblaze" && [mb_has_exceptions $hw_proc_handle] } {
        xcreate_mb_exc_config_file 
    }

    # Create bspconfig file
    set bspcfg_fn [file join ".." "${standalone_version}" "src"  "bspconfig.h"] 
    file delete $bspcfg_fn
    set bspcfg_fh [open $bspcfg_fn w]
    xprint_generated_header $bspcfg_fh "Configurations for Standalone BSP"

    if { $proctype == "microblaze" && [mb_has_pvr $hw_proc_handle] } {
        
        set pvr [xget_value $hw_proc_handle "PARAMETER" "C_PVR"]
        
        switch $pvr {
            "0" {
                puts $bspcfg_fh "#define MICROBLAZE_PVR_NONE"
            }
            "1" {
                puts $bspcfg_fh "#define MICROBLAZE_PVR_BASIC"
            }
            "2" {
                puts $bspcfg_fh "#define MICROBLAZE_PVR_FULL"
            }
            "default" {
                puts $bspcfg_fh "#define MICROBLAZE_PVR_NONE"
            }
        }    
    }

    close $bspcfg_fh

# ToDO: FreeRTOS does not handle the following, refer xilkernel TCL script
# - MPU settings

    set config_file [xopen_new_include_file "./src/FreeRTOSConfig.h" "FreeRTOS Configuration parameters"]
    puts $config_file "\#include \"xparameters.h\" \n"

    set val [xget_value $os_handle "PARAMETER" "use_preemption"]
    if {$val == "false"} {
        xput_define $config_file "configUSE_PREEMPTION" "0"
    } else {
        xput_define $config_file "configUSE_PREEMPTION" "1"
    }

    set val [xget_value $os_handle "PARAMETER" "use_mutexes"]
    if {$val == "false"} {
        xput_define $config_file "configUSE_MUTEXES" "0"
    } else {
        xput_define $config_file "configUSE_MUTEXES" "1"
    }
    
    set val [xget_value $os_handle "PARAMETER" "use_recursive_mutexes"]
    if {$val == "false"} {
        xput_define $config_file "configUSE_RECURSIVE_MUTEXES" "0"
    } else {
        xput_define $config_file "configUSE_RECURSIVE_MUTEXES" "1"
    }

    set val [xget_value $os_handle "PARAMETER" "use_counting_semaphores"]
    if {$val == "false"} {
        xput_define $config_file "configUSE_COUNTING_SEMAPHORES" "0"
    } else {
        xput_define $config_file "configUSE_COUNTING_SEMAPHORES" "1"
    }

    set val [xget_value $os_handle "PARAMETER" "use_timers"]
    if {$val == "false"} {
        xput_define $config_file "configUSE_TIMERS" "0"
    } else {
        xput_define $config_file "configUSE_TIMERS" "1"
    }

    set val [xget_value $os_handle "PARAMETER" "use_idle_hook"]
    if {$val == "false"} {
        xput_define $config_file "configUSE_IDLE_HOOK"    "0"
    } else {
        xput_define $config_file "configUSE_IDLE_HOOK"    "1"
    }

    set val [xget_value $os_handle "PARAMETER" "use_tick_hook"]
    if {$val == "false"} {
        xput_define $config_file "configUSE_TICK_HOOK"    "0"
    } else {
        xput_define $config_file "configUSE_TICK_HOOK"    "1"
    }

    set val [xget_value $os_handle "PARAMETER" "use_malloc_failed_hook"]
    if {$val == "false"} {
        xput_define $config_file "configUSE_MALLOC_FAILED_HOOK"    "0"
    } else {
        xput_define $config_file "configUSE_MALLOC_FAILED_HOOK"    "1"
    }

    set val [xget_value $os_handle "PARAMETER" "use_trace_facility"]
    if {$val == "false"} {
        xput_define $config_file "configUSE_TRACE_FACILITY" "0"
    } else {
        xput_define $config_file "configUSE_TRACE_FACILITY" "1"
    }

    xput_define $config_file "configUSE_16_BIT_TICKS"   "0"
    xput_define $config_file "configUSE_APPLICATION_TASK_TAG"   "0"
    xput_define $config_file "configUSE_CO_ROUTINES"    "0"

    # System timer tick rate (Microblaze only. kernel DRC ensures this)
    set systmr_interval [xget_value $os_handle "PARAMETER" "systmr_interval"]
    xput_define $config_file "configTICK_RATE_HZ"     $systmr_interval

    set max_priorities [xget_value $os_handle "PARAMETER" "max_priorities"]
    xput_define $config_file "configMAX_PRIORITIES"   $max_priorities
    xput_define $config_file "configMAX_CO_ROUTINE_PRIORITIES" "2"
    
    set min_stack [xget_value $os_handle "PARAMETER" "minimal_stack_size"]
    set min_stack [expr [expr $min_stack + 3] & 0xFFFFFFFC]
    xput_define $config_file "configMINIMAL_STACK_SIZE" $min_stack

    set total_heap_size [xget_value $os_handle "PARAMETER" "total_heap_size"]
    set total_heap_size [expr [expr $total_heap_size + 3] & 0xFFFFFFFC]
    xput_define $config_file "configTOTAL_HEAP_SIZE"  $total_heap_size

    set max_task_name_len [xget_value $os_handle "PARAMETER" "max_task_name_len"]
    xput_define $config_file "configMAX_TASK_NAME_LEN"  $max_task_name_len
    
    set val [xget_value $os_handle "PARAMETER" "idle_yield"]
    if {$val == "false"} {
        xput_define $config_file "configIDLE_SHOULD_YIELD"  "0"
    } else {
        xput_define $config_file "configIDLE_SHOULD_YIELD"  "1"
    }

    set val [xget_value $os_handle "PARAMETER" "check_for_stack_overflow"]
    if {$val == "false"} {
        xput_define $config_file "configCHECK_FOR_STACK_OVERFLOW"  "0"
    } else {
        xput_define $config_file "configCHECK_FOR_STACK_OVERFLOW"  "2"
    }
    
    set val [xget_value $os_handle "PARAMETER" "queue_registry_size"]
    if {$val == "false"} {
        xput_define $config_file "configQUEUE_REGISTRY_SIZE"  "0"
    } else {
        xput_define $config_file "configQUEUE_REGISTRY_SIZE"  "10"
    }

    xput_define $config_file "configGENERATE_RUN_TIME_STATS"    "0"

    set val [xget_value $os_handle "PARAMETER" "timer_task_priority"]
    if {$val == "false"} {
        xput_define $config_file "configTIMER_TASK_PRIORITY"  "0"
    } else {
        xput_define $config_file "configTIMER_TASK_PRIORITY"  "10"
    }

    set val [xget_value $os_handle "PARAMETER" "timer_command_queue_length"]
    if {$val == "false"} {
        xput_define $config_file "configTIMER_QUEUE_LENGTH"  "0"
    } else {
        xput_define $config_file "configTIMER_QUEUE_LENGTH"  "10"
    }

    set val [xget_value $os_handle "PARAMETER" "timer_task_stack_depth"]
    if {$val == "false"} {
        xput_define $config_file "configTIMER_TASK_STACK_DEPTH"  "0"
    } else {
        xput_define $config_file "configTIMER_TASK_STACK_DEPTH"  $min_stack
    }

    if { [mb_has_exceptions $hw_proc_handle] } {    
        xput_define $config_file "configINSTALL_EXCEPTION_HANDLERS"  "1"
    } else {
        xput_define $config_file "configINSTALL_EXCEPTION_HANDLERS"  "0"
    }

    xput_define $config_file "configINTERRUPT_CONTROLLER_TO_USE"  "XPAR_INTC_SINGLE_DEVICE_ID"

    xput_define $config_file "INCLUDE_vTaskCleanUpResources" "0"
    xput_define $config_file "INCLUDE_vTaskDelay"        "1"
    xput_define $config_file "INCLUDE_vTaskDelayUntil"   "1"
    xput_define $config_file "INCLUDE_vTaskDelete"       "1"
    xput_define $config_file "INCLUDE_xTaskGetCurrentTaskHandle"   "1"
    xput_define $config_file "INCLUDE_xTaskGetIdleTaskHandle"      "1"
    xput_define $config_file "INCLUDE_xTaskGetSchedulerState"  "1"
    xput_define $config_file "INCLUDE_xTimerGetTimerTaskHandle"    "1"
    xput_define $config_file "INCLUDE_uxTaskGetStackHighWaterMark"  "1"
    xput_define $config_file "INCLUDE_uxTaskPriorityGet" "1"
    xput_define $config_file "INCLUDE_vTaskPrioritySet"  "1"
    xput_define $config_file "INCLUDE_xTaskResumeFromISR"  "1"
    xput_define $config_file "INCLUDE_vTaskSuspend"      "1"
    xput_define $config_file "INCLUDE_pcTaskNameGet"      "1"
    xput_define $config_file "INCLUDE_xTaskIdleTaskHandleGet"      "1"
    xput_define $config_file "INCLUDE_xTimerDaemonTaskHandleGet"      "1"

    # complete the header protectors
    puts $config_file "\#endif"
    close $config_file
}

proc xopen_new_include_file { filename description } {
    set inc_file [open $filename w]
    xprint_generated_header $inc_file $description
    set newfname [string map {. _} [lindex [split $filename {\/}] end]]
    puts $inc_file "\#ifndef _[string toupper $newfname]"
    puts $inc_file "\#define _[string toupper $newfname]\n\n"
    return $inc_file
}

proc xadd_define { config_file os_handle parameter } {
    set param_value [xget_value $os_handle "PARAMETER" $parameter]
    puts $config_file "#define [string toupper $parameter] $param_value\n"

    # puts "creating #define [string toupper $parameter] $param_value\n"
}

proc xput_define { config_file parameter param_value } {
    puts $config_file "#define $parameter $param_value\n"

    # puts "creating #define [string toupper $parameter] $param_value\n"
}

# args field of the array
proc xadd_extern_fname {initfile oshandle arrayname arg} { 

    set arrhandle [xget_handle $oshandle "ARRAY" $arrayname]
    set elements [xget_handle $arrhandle "ELEMENTS" "*"]
    set count 0
    set max_count [llength $elements]

    foreach ele $elements {
        incr count
        set arg_value [xget_value $ele "PARAMETER" $arg]
        puts $initfile "extern void $arg_value\(\)\;"
    }
    puts $initfile ""
}

# args is variable no - fields of the array
proc xadd_struct {initfile oshandle structtype structname arrayname args} { 

    set arrhandle [xget_handle $oshandle "ARRAY" $arrayname]
    set elements [xget_handle $arrhandle "ELEMENTS" "*"]
    set count 0
    set max_count [llength $elements]
    puts $initfile "struct $structtype $structname\[$max_count\] = \{"

    foreach ele $elements {
	incr count
	puts -nonewline $initfile "\t\{"
	foreach field $args {
	    set field_value [xget_value $ele "PARAMETER" $field]
	    # puts "$arrayname ( $count )->$field is $field_value"
	    puts -nonewline $initfile "$field_value"
	    if { $field != [lindex $args end] } {
		puts -nonewline $initfile ","
	    }
	}
	if {$count < $max_count} {
	    puts $initfile "\},"
	} else {
	    puts $initfile "\}"
	}
    }
    puts $initfile "\}\;"
}

# return the sum of all the arg field values in arrayname
proc get_field_sum {oshandle arrayname arg} { 

    set arrhandle [xget_handle $oshandle "ARRAY" $arrayname]
    set elements [xget_handle $arrhandle "ELEMENTS" "*"]
    set count 0
    set max_count [llength $elements]
  
    foreach ele $elements {
	set field_value [xget_value $ele "PARAMETER" $arg]
	set count [expr $field_value+$count]
    }
    return $count
}

# return the sum of the product of field values in arrayname
proc get_field_product_sum {oshandle arrayname field1 field2} { 

    set arrhandle [xget_handle $oshandle "ARRAY" $arrayname]
    set elements [xget_handle $arrhandle "ELEMENTS" "*"]
    set count 0
    set max_count [llength $elements]

    foreach ele $elements {
        set field1_value [xget_value $ele "PARAMETER" $field1]
        set field2_value [xget_value $ele "PARAMETER" $field2]
        set incr_value [expr $field1_value*$field2_value]
        set count [expr $count+$incr_value]
    }
    return $count
}

proc xhandle_mb_interrupts {} {

    set default_interrupt_handler "XNullHandler"
    set default_arg "XNULL"

    set source_interrupt_handler $default_interrupt_handler
    set source_handler_arg $default_arg
    
    # Handle the interrupt pin
    set sw_proc_handle [xget_libgen_proc_handle] 
    set periph [xget_handle $sw_proc_handle "IPINST"]
    set source_ports [xget_interrupt_sources $periph]
    if {[llength $source_ports] > 1} {
        error "Too many interrupting ports on the MicroBlaze.  Should only find 1" "" "libgen_error"
        return
    }
    
    if {[llength $source_ports] == 1} {
	set source_port [lindex $source_ports 0]
	if {[llength $source_port] != 0} {
	    set source_port_name [xget_value $source_port "VALUE"]	
	    set source_periph [xget_handle $source_port "PARENT"]
	    set source_name [xget_value $source_periph "NAME"]
	    set source_driver [xget_sw_driver_handle_for_ipinst $sw_proc_handle $source_name]

	    if {[string compare -nocase $source_driver ""] != 0} {
		set int_array [xget_handle $source_driver "ARRAY" "interrupt_handler"]
		if {[llength $int_array] != 0} {
		    set int_array_elems [xget_handle $int_array "ELEMENTS" "*"]
		    if {[llength $int_array_elems] != 0} {
			foreach int_array_elem $int_array_elems {
			    set int_port [xget_value $int_array_elem "PARAMETER" "int_port"]
			    if {[llength $int_port] != 0} {
				if {[string compare -nocase $int_port $source_port_name] == 0 } {
				    set source_interrupt_handler [xget_value $int_array_elem "PARAMETER" "int_handler"]
				    set source_handler_arg [xget_value $int_array_elem "PARAMETER" "int_handler_arg"]
				    if {[string compare -nocase $source_handler_arg DEVICE_ID] == 0 } {
					set source_handler_arg [xget_name $source_periph "DEVICE_ID"]
				    } else {
					if {[string compare -nocase "global" [xget_port_type $source_port]] == 0} {
					    set source_handler_arg $default_arg
					} else {
					    set source_handler_arg [xget_name $source_periph "C_BASEADDR"]
					}
				    }
				    break
				}
			    }
			}
		    }
		}
	    }
	}
    }
    
    # Generate microblaze_interrupts_g.c file...
    xcreate_mb_intr_config_file $source_interrupt_handler $source_handler_arg
    
}


proc xcreate_mb_intr_config_file {handler arg} {
    
    set mb_table "MB_InterruptVectorTable"

    set filename [file join "../standalone_v3_01_a/src" "microblaze_interrupts_g.c"] 
    file delete $filename
    set config_file [open $filename w]

    xprint_generated_header $config_file "Interrupt Handler Table for MicroBlaze Processor"
    
    puts $config_file "#include \"microblaze_interrupts_i.h\""
    puts $config_file "#include \"xparameters.h\""
    puts $config_file "\n"
    puts $config_file [format "extern void %s (void *);" $handler]
    puts $config_file "\n/*"
    puts $config_file "* The interrupt handler table for microblaze processor"
    puts $config_file "*/\n"
    puts $config_file [format "%sEntry %s\[\] =" $mb_table $mb_table]
    puts $config_file "\{"
    puts -nonewline $config_file [format "\{\t%s" $handler]
    puts -nonewline $config_file [format ",\n\t(void*) %s\}" $arg]
    puts -nonewline $config_file "\n\};"
    puts $config_file "\n"
    close $config_file
}


# -------------------------------------------
# Tcl procedure xcreate_mb_exc_config file
# -------------------------------------------
proc xcreate_mb_exc_config_file { } {
    
    set hfilename [file join "src" "microblaze_exceptions_g.h"] 
    file delete $hfilename
    set hconfig_file [open $hfilename w]

    xprint_generated_header $hconfig_file "Exception Handling Header for MicroBlaze Processor"
    
    puts $hconfig_file "\n"

    set sw_proc_handle [xget_libgen_proc_handle]
    set hw_proc_handle [xget_handle $sw_proc_handle "IPINST"]
    set procver [xget_value $hw_proc_handle "PARAMETER" "HW_VER"]

    if { ![mb_has_exceptions $hw_proc_handle]} { ;# NO exceptions are enabled
        close $hconfig_file              ;# Do not generate any info in either the header or the C file
        return
    }
    
    puts $hconfig_file "\#define MICROBLAZE_EXCEPTIONS_ENABLED 1"
    if { [mb_can_handle_exceptions_in_delay_slots $procver] } {
        puts $hconfig_file "#define MICROBLAZE_CAN_HANDLE_EXCEPTIONS_IN_DELAY_SLOTS"
    }

    close $hconfig_file
}

# --------------------------------------
# Tcl procedure post_generate
# This proc removes from libxil.a the basic 
# and standalone BSP versions of 
# _interrupt_handler and _hw_exception_handler
# routines
# --------------------------------------
proc post_generate {os_handle} {
    set sw_proc_handle [xget_libgen_proc_handle]
    set hw_proc_handle [xget_handle $sw_proc_handle "IPINST"]
    set proctype [xget_value $hw_proc_handle "OPTION" "IPNAME"]
    set procname [xget_value $hw_proc_handle "NAME"]

    set procdrv [xget_sw_driver_handle_for_ipinst $sw_proc_handle $procname]
    set archiver [xget_value $procdrv "PARAMETER" "archiver"]

    if {[string compare -nocase $proctype "microblaze"] == 0 } {
        # Remove _interrupt_handler.o from libxil.a for FreeRTOS
		set libxil_a [file join .. .. lib libxil.a]
        exec $archiver -d $libxil_a   _interrupt_handler.o

        # We have linkage problems due to how these platforms are defined. Can't do this right now.  
        # # Remove _exception_handler.o from libxil.a for FreeRTOS
        # exec bash -c "$archiver -d ../../lib/libxil.a _exception_handler.o"
        
        # Remove _hw_exception_handler.o from libxil.a for microblaze cores with exception support
        if {[mb_has_exceptions $hw_proc_handle]} {
            exec $archiver -d ../../lib/libxil.a _hw_exception_handler.o
        }
    }
}

# --------------------------------------
# Tcl procedure execs_generate
# This proc removes from libxil.a all 
# the stuff that we are overriding
# with xilkernel
# We currently override,
#  MicroBlaze
#   - Dummy _interrupt_hander and _hw_exception_handler 
#     (in post_generate)
#  PPC
#   - xvectors.o; sleep.o (IF config_time is true)
#  Common to all processors
#    - errno.o
# --------------------------------------
proc execs_generate {os_handle} {
    set sw_proc_handle [xget_libgen_proc_handle]
    set hw_proc_handle [xget_handle $sw_proc_handle "IPINST"]
    set proctype [xget_value $hw_proc_handle "OPTION" "IPNAME"]
    set procname [xget_value $hw_proc_handle "NAME"]

    set procdrv [xget_sw_driver_handle_for_ipinst $sw_proc_handle $procname]
    # Remove _interrupt_handler.o from libxil.a for mb-gcc
    set archiver [xget_value $procdrv "PARAMETER" "archiver"]

    set libxil_a [file join .. .. lib libxil.a]
#    exec $archiver -d $libxil_a  errno.o

    # We have linkage problems due to how these platforms are defined. Can't do this right now.  
    # exec "$archiver -d $libxil_a microblaze_interrupt_handler.o"
}

# --------------------------------------
# Return true if this MB has 
# exception handling support
# --------------------------------------
proc mb_has_exceptions { hw_proc_handle } {
   
    # Check if the following parameters exist on this MicroBlaze's MPD
    set ee [xget_value $hw_proc_handle "PARAMETER" "C_UNALIGNED_EXCEPTIONS"]
    if { $ee != "" } {
        return true
    }

    set ee [xget_value $hw_proc_handle "PARAMETER" "C_ILL_OPCODE_EXCEPTION"]
    if { $ee != "" } {
        return true
    }

    set ee [xget_value $hw_proc_handle "PARAMETER" "C_IOPB_BUS_EXCEPTION"]
    if { $ee != "" } {
        return true
    }

    set ee [xget_value $hw_proc_handle "PARAMETER" "C_DOPB_BUS_EXCEPTION"]
    if { $ee != "" } {
        return true
    }

    set ee [xget_value $hw_proc_handle "PARAMETER" "C_DIV_BY_ZERO_EXCEPTION"]
    if { $ee != "" } {
        return true
    } 

    set ee [xget_value $hw_proc_handle "PARAMETER" "C_DIV_ZERO_EXCEPTION"]
    if { $ee != "" } {
        return true
    } 

    set ee [xget_value $hw_proc_handle "PARAMETER" "C_FPU_EXCEPTION"]
    if { $ee != "" } {
        return true
    } 

    set ee [xget_value $hw_proc_handle "PARAMETER" "C_USE_MMU"]
    if { $ee != "" && $ee != 0 } {
        return true
    } 

    return false
}

# --------------------------------------
# Return true if this MB has 
# FPU exception handling support
# --------------------------------------
proc mb_has_fpu_exceptions { hw_proc_handle } {
    
    # Check if the following parameters exist on this MicroBlaze's MPD
    set ee [xget_value $hw_proc_handle "PARAMETER" "C_FPU_EXCEPTION"]
    if { $ee != "" } {
        return true
    }

    return false
}

# --------------------------------------
# Return true if this MB has PVR support
# --------------------------------------
proc mb_has_pvr { hw_proc_handle } {
    
    # Check if the following parameters exist on this MicroBlaze's MPD
    set pvr [xget_value $hw_proc_handle "PARAMETER" "C_PVR"]
    if { $pvr != "" } {
        return true
    } 

    return false
}

# --------------------------------------
# Return true if MB ver 'procver' has 
# support for handling exceptions in 
# delay slots
# --------------------------------------
proc mb_can_handle_exceptions_in_delay_slots { procver } {
    
    if { [string compare -nocase $procver "5.00.a"] >= 0 } {
        return true
    } else {
        return false
    }
}

# --------------------------------------------------------------------------
# Gets all the handles that are memory controller cores.
# --------------------------------------------------------------------------
proc xget_memory_controller_handles { mhs } {
   set ret_list ""

   # Gets all MhsInsts in the system
   set mhsinsts [xget_hw_ipinst_handle $mhs "*"]

   # Loop thru each MhsInst and determine if have "ADDR_TYPE = MEMORY" in
   # the parameters.
   foreach mhsinst $mhsinsts {
      # Gets all parameters of the component
      set params [xget_hw_parameter_handle $mhsinst "*"]

      # Loop thru each param and find tag "ADDR_TYPE = MEMORY"
      foreach param $params {
         if {$param == 0} {
            continue
         } elseif {$param == ""} {
            continue
         }
         set addrTypeValue [ xget_hw_subproperty_value $param "ADDR_TYPE" ]

         # Found tag! Add MhsInst to list and break to go to next MhsInst
         if {[string compare -nocase $addrTypeValue "MEMORY"] == 0} {
            lappend ret_list $mhsinst
            break
         }
      }
   }

   return $ret_list
}
