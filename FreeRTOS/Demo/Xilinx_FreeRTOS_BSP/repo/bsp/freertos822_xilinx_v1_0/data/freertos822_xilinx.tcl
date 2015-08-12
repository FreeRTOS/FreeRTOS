#
# Copyright (C) 2015 Xilinx, Inc.
#
# This file is part of the FreeRTOS port.
#
# FreeRTOS is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License (version 2) as published by the
# Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.
#
# NOTE: The modification to the GPL is included to allow you to distribute a
# combined work that includes FreeRTOS without being obliged to provide the
# source code for proprietary components outside of the FreeRTOS kernel.
#
# FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
# WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE.  Full license text is available on the following
# link: http://www.freertos.org/a00114.html
#


# standalone bsp version. set this to the latest "ACTIVE" version.
set standalone_version standalone_v5_0

proc FreeRTOS_drc {os_handle} {

	global env

	set sw_proc_handle [hsi::get_sw_processor]
	set hw_proc_handle [hsi::get_cells [common::get_property HW_INSTANCE $sw_proc_handle] ]
	set proctype [common::get_property IPNAME $hw_proc_handle]

	if { $proctype == "microblaze" } {
		mb_drc_checks
	}
}

proc generate {os_handle} {

	variable standalone_version
	set have_tick_timer 0
	set sw_proc_handle [hsi::get_sw_processor]
	set hw_proc_handle [hsi::get_cells [common::get_property HW_INSTANCE $sw_proc_handle] ]
	set proctype [common::get_property IP_NAME $hw_proc_handle]
	set need_config_file "false"

	set commonsrcdir "../${standalone_version}/src/common"
	set mbsrcdir "../${standalone_version}/src/microblaze"
	set arma9srcdir "../${standalone_version}/src/cortexa9"
	set arma9gccdir "../${standalone_version}/src/cortexa9/gcc"
	set arma9armccdir "../${standalone_version}/src/cortexa9/armcc"
	set arma9iarccdir "../${standalone_version}/src/cortexa9/iarcc"

	foreach entry [glob -nocomplain [file join $commonsrcdir *]] {
		file copy -force $entry [file join ".." "${standalone_version}" "src"]
	}

	switch $proctype {

		"ps7_cortexa9"  {
				puts "In start copy ps7_cortexa9"
				file copy -force "./src/Makefile_ps7_cortexa9" "./src/Makefile"
				file copy -force "./src/Makefile" "./src/Makefile_dep"

				foreach entry [glob -nocomplain [file join $arma9srcdir *]] {
					file copy -force $entry [file join ".." "${standalone_version}" "src"]
				}

				foreach entry [glob -nocomplain [file join $arma9gccdir *]] {
					file copy -force $entry [file join ".." "${standalone_version}" "src"]
				}

				file delete -force "../${standalone_version}/src/gcc"

				set need_config_file "true"

				set file_handle [::hsi::utils::open_include_file "xparameters.h"]
				puts $file_handle "#include \"xparameters_ps.h\""
				puts $file_handle ""
				close $file_handle
			}

		"microblaze"  {
				puts "In start copy microblaze"
				file copy -force "./src/Makefile_microblaze" "./src/Makefile"
				file copy -force "./src/Makefile" "./src/Makefile_dep"

				foreach entry [glob -nocomplain [file join $mbsrcdir *]] {
					if { [string first "microblaze_interrupt_handler" $entry] == -1 } { ;# Do not copy over the Standalone BSP exception handler
						file copy -force $entry [file join ".." "${standalone_version}" "src"]
					}
				}

				set need_config_file "true"
			}

		"default" {
			puts "processor type $proctype not supported\n"
		}
	}

	# Write the Config.make file
	set makeconfig [open "../${standalone_version}/src/config.make" w]
	file rename -force -- "../${standalone_version}/src/Makefile" "../${standalone_version}/src/Makefile_depends"

	if { $proctype == "ps7_cortexa9" || $proctype == "microblaze" } {
		puts $makeconfig "LIBSOURCES = *.c *.S"
		puts $makeconfig "LIBS = standalone_libs"
	}

	close $makeconfig

	# Remove arm directory...
	file delete -force $arma9srcdir
	file delete -force $mbsrcdir

	# Copy core kernel files to the main src directory
	file copy -force [file join src Source tasks.c] ./src
	file copy -force [file join src Source queue.c] ./src
	file copy -force [file join src Source list.c] ./src
	file copy -force [file join src Source timers.c] ./src
	file copy -force [file join src Source event_groups.c] ./src
	file copy -force [file join src Source portable MemMang heap_4.c] ./src

	if { $proctype == "ps7_cortexa9" } {
		file copy -force [file join src Source portable GCC ARM_CA9 port.c] ./src
		file copy -force [file join src Source portable GCC ARM_CA9 portASM.S] ./src
		file copy -force [file join src Source portable GCC ARM_CA9 port_asm_vectors.S] ./src
		file copy -force [file join src Source portable GCC ARM_CA9 portmacro.h] ./src
		file copy -force [file join src Source portable GCC ARM_CA9 portZynq7000.c] ./src
	}

	if { $proctype == "microblaze" } {
		file copy -force [file join src Source portable GCC MicroBlazeV8 port.c] ./src
		file copy -force [file join src Source portable GCC MicroBlazeV8 port_exceptions.c] ./src
		file copy -force [file join src Source portable GCC MicroBlazeV8 portasm.S] ./src
		file copy -force [file join src Source portable GCC MicroBlazeV8 portmacro.h] ./src
		file copy -force [file join src Source portable GCC MicroBlazeV8 portmicroblaze.c] ./src

		# Create config file for microblaze interrupt handling
		if {[string compare -nocase $need_config_file "true"] == 0} {
			xhandle_mb_interrupts
		}

		# Create config files for Microblaze exception handling
		if { [mb_has_exceptions $hw_proc_handle] } {
			xcreate_mb_exc_config_file
		}

		# Create bspconfig file
		set bspcfg_fn [file join ".." "${standalone_version}" "src"  "bspconfig.h"]
		file delete $bspcfg_fn
		set bspcfg_fh [open $bspcfg_fn w]
		xprint_generated_header $bspcfg_fh "Configurations for Standalone BSP"

		if { [mb_has_pvr $hw_proc_handle] } {

			set pvr [get_property CONFIG.C_PVR $hw_proc_handle]

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
	}

	set headers [glob -join ./src/Source/include *.\[h\]]
	foreach header $headers {
		file copy -force $header src
	}

	file delete -force [file join src Source]

	# Remove microblaze, cortexa9 and common directories...
	file delete -force $mbsrcdir
	file delete -force $commonsrcdir
	file delete -force $arma9srcdir
	file delete -force $arma9gccdir
	file delete -force $arma9armccdir
	file delete -force $arma9iarccdir

	# Handle stdin and stdout
	::hsi::utils::handle_stdin $os_handle
	::hsi::utils::handle_stdout $os_handle

	file copy -force "./src/outbyte.c" "../${standalone_version}/src/"
	file copy -force "./src/inbyte.c" "../${standalone_version}/src/"

	set file_handle [::hsi::utils::open_include_file "xparameters.h"]
	puts $file_handle "\n/******************************************************************/\n"
    	close $file_handle

	############################################################################
	## Add constants common to all architectures to the configuration file.
	############################################################################

	set config_file [xopen_new_include_file "./src/FreeRTOSConfig.h" "FreeRTOS Configuration parameters"]
	puts $config_file "\#include \"xparameters.h\" \n"

	set val [common::get_property CONFIG.use_preemption $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configUSE_PREEMPTION" "0"
	} else {
		xput_define $config_file "configUSE_PREEMPTION" "1"
	}

	set val [common::get_property CONFIG.use_mutexes $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configUSE_MUTEXES" "0"
	} else {
		xput_define $config_file "configUSE_MUTEXES" "1"
	}

	set val [common::get_property CONFIG.use_recursive_mutexes $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configUSE_RECURSIVE_MUTEXES" "0"
	} else {
		xput_define $config_file "configUSE_RECURSIVE_MUTEXES" "1"
	}

	set val [common::get_property CONFIG.use_counting_semaphores $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configUSE_COUNTING_SEMAPHORES" "0"
	} else {
		xput_define $config_file "configUSE_COUNTING_SEMAPHORES" "1"
	}

	set val [common::get_property CONFIG.use_timers $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configUSE_TIMERS" "0"
	} else {
		xput_define $config_file "configUSE_TIMERS" "1"
	}

	set val [common::get_property CONFIG.use_idle_hook $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configUSE_IDLE_HOOK"	"0"
	} else {
		xput_define $config_file "configUSE_IDLE_HOOK"	"1"
	}

	set val [common::get_property CONFIG.use_tick_hook $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configUSE_TICK_HOOK"	"0"
	} else {
		xput_define $config_file "configUSE_TICK_HOOK"	"1"
	}

	set val [common::get_property CONFIG.use_malloc_failed_hook $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configUSE_MALLOC_FAILED_HOOK"	"0"
	} else {
		xput_define $config_file "configUSE_MALLOC_FAILED_HOOK"	"1"
	}

	set val [common::get_property CONFIG.use_trace_facility $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configUSE_TRACE_FACILITY" "0"
	} else {
		xput_define $config_file "configUSE_TRACE_FACILITY" "1"
	}

	set val [common::get_property CONFIG.use_task_notifications $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configUSE_TASK_NOTIFICATIONS" "0"
	} else {
		xput_define $config_file "configUSE_TASK_NOTIFICATIONS" "1"
	}

	xput_define $config_file "configUSE_16_BIT_TICKS"		   "0"
	xput_define $config_file "configUSE_APPLICATION_TASK_TAG"   "0"
	xput_define $config_file "configUSE_CO_ROUTINES"			"0"

	set tick_rate [common::get_property CONFIG.tick_rate $os_handle]
	xput_define $config_file "configTICK_RATE_HZ"	 "($tick_rate)"

	set max_priorities [common::get_property CONFIG.max_priorities $os_handle]
	xput_define $config_file "configMAX_PRIORITIES"   "($max_priorities)"
	xput_define $config_file "configMAX_CO_ROUTINE_PRIORITIES" "2"

	set min_stack [common::get_property CONFIG.minimal_stack_size $os_handle]
	set min_stack [expr [expr $min_stack + 3] & 0xFFFFFFFC]
	xput_define $config_file "configMINIMAL_STACK_SIZE" "( ( unsigned short ) $min_stack)"

	set total_heap_size [common::get_property CONFIG.total_heap_size $os_handle]
	xput_define $config_file "configTOTAL_HEAP_SIZE"  "( ( size_t ) ( $total_heap_size ) )"

	set max_task_name_len [common::get_property CONFIG.max_task_name_len $os_handle]
	xput_define $config_file "configMAX_TASK_NAME_LEN"  $max_task_name_len

	set val [common::get_property CONFIG.idle_yield $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configIDLE_SHOULD_YIELD"  "0"
	} else {
		xput_define $config_file "configIDLE_SHOULD_YIELD"  "1"
	}

	set val [common::get_property CONFIG.timer_task_priority $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configTIMER_TASK_PRIORITY"  "0"
	} else {
		xput_define $config_file "configTIMER_TASK_PRIORITY"  "1"
	}

	set val [common::get_property CONFIG.timer_command_queue_length $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configTIMER_QUEUE_LENGTH"  "0"
	} else {
		xput_define $config_file "configTIMER_QUEUE_LENGTH"  "10"
	}

	set val [common::get_property CONFIG.timer_task_stack_depth $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configTIMER_TASK_STACK_DEPTH"  "0"
	} else {
		xput_define $config_file "configTIMER_TASK_STACK_DEPTH"  $min_stack
	}

	set val [common::get_property CONFIG.use_newlib_reent $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configUSE_NEWLIB_REENTRANT"  "0"
	} else {
		xput_define $config_file "configUSE_NEWLIB_REENTRANT"  "1"
	}

	set val [common::get_property CONFIG.use_timeslicing $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configUSE_TIME_SLICING"  "0"
	} else {
		xput_define $config_file "configUSE_TIME_SLICING"  "1"
	}

	set val [get_property CONFIG.use_freertos_asserts $os_handle]
	if {$val == "true"} {
		puts $config_file "#define configASSERT( x ) if( ( x ) == 0 ) vApplicationAssert( __FILE__, __LINE__ )\n"
	}

	set val [common::get_property CONFIG.use_queue_sets $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configUSE_QUEUE_SETS"  "0"
	} else {
		xput_define $config_file "configUSE_QUEUE_SETS"  "1"
	}

	set val [common::get_property CONFIG.check_for_stack_overflow $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configCHECK_FOR_STACK_OVERFLOW"  "0"
	} else {
		if { $val > 2 } {
			error "ERROR: check_for_stack_overflow must be between 0 and 2"
		} else {
			xput_define $config_file "configCHECK_FOR_STACK_OVERFLOW"  $val
		}
	}


	set val [common::get_property CONFIG.queue_registry_size $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configQUEUE_REGISTRY_SIZE"  "0"
	} else {
		xput_define $config_file "configQUEUE_REGISTRY_SIZE"  $val
	}


	set val [common::get_property CONFIG.use_stats_formatting_functions  $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configUSE_STATS_FORMATTING_FUNCTIONS"  "0"
	} else {
		xput_define $config_file "configUSE_STATS_FORMATTING_FUNCTIONS"  "1"
	}

	set val [common::get_property CONFIG.num_thread_local_storage_pointers $os_handle]
	if {$val == "false"} {
		xput_define $config_file "configNUM_THREAD_LOCAL_STORAGE_POINTERS"  "0"
	} else {
		xput_define $config_file "configNUM_THREAD_LOCAL_STORAGE_POINTERS"  $val
	}

	puts $config_file "#define configTASK_RETURN_ADDRESS    NULL"

	puts $config_file "#define INCLUDE_vTaskPrioritySet             1"
	puts $config_file "#define INCLUDE_uxTaskPriorityGet            1"
	puts $config_file "#define INCLUDE_vTaskDelete                  1"
	puts $config_file "#define INCLUDE_vTaskCleanUpResources        0"
	puts $config_file "#define INCLUDE_vTaskSuspend                 1"
	puts $config_file "#define INCLUDE_vTaskDelayUntil              1"
	puts $config_file "#define INCLUDE_vTaskDelay                   1"
	puts $config_file "#define INCLUDE_uxTaskGetStackHighWaterMark  1"
	puts $config_file "#define INCLUDE_xTaskGetSchedulerState       1"
	puts $config_file "#define INCLUDE_xTimerGetTimerTaskHandle     1"
	puts $config_file "#define INCLUDE_xTaskGetIdleTaskHandle       1"
	puts $config_file "#define INCLUDE_xQueueGetMutexHolder         1"
	puts $config_file "#define INCLUDE_eTaskGetState                1"
	puts $config_file "#define INCLUDE_xEventGroupSetBitFromISR     1"
	puts $config_file "#define INCLUDE_xTimerPendFunctionCall       1"
	puts $config_file "#define INCLUDE_pcTaskGetTaskName            1"
	puts $config_file "#define INCLUDE_xTaskResumeFromISR           1"
	puts $config_file "#define INCLUDE_xTaskGetCurrentTaskHandle    1"
	puts $config_file "#define INCLUDE_xSemaphoreGetMutexHolder     1"


	############################################################################
	## Add constants specific to the ps7_cortexa9
	############################################################################
	if { $proctype == "ps7_cortexa9" } {
		set max_api_call_interrupt_priority [common::get_property CONFIG.max_api_call_interrupt_priority $os_handle]
		xput_define $config_file "configMAX_API_CALL_INTERRUPT_PRIORITY"   "($max_api_call_interrupt_priority)"

		set val [common::get_property CONFIG.use_port_optimized_task_selection $os_handle]
		if {$val == "false"} {
			xput_define $config_file "configUSE_PORT_OPTIMISED_TASK_SELECTION"  "0"
		} else {
			xput_define $config_file "configUSE_PORT_OPTIMISED_TASK_SELECTION"  "1"
		}

		puts $config_file "#define configINTERRUPT_CONTROLLER_BASE_ADDRESS         ( XPAR_PS7_SCUGIC_0_DIST_BASEADDR )"
		puts $config_file "#define configINTERRUPT_CONTROLLER_CPU_INTERFACE_OFFSET ( -0xf00 )"
		puts $config_file "#define configUNIQUE_INTERRUPT_PRIORITIES                32"

		# Function prototypes cannot be in the common code as some compilers or
		# ports require pre-processor guards to ensure they are not visible from
		# assembly files.
		puts $config_file "void vApplicationAssert( const char *pcFile, uint32_t ulLine );"
		puts $config_file "void FreeRTOS_SetupTickInterrupt( void );"
		puts $config_file "#define configSETUP_TICK_INTERRUPT() FreeRTOS_SetupTickInterrupt()\n"
		puts $config_file "void FreeRTOS_ClearTickInterrupt( void );"
		puts $config_file "#define configCLEAR_TICK_INTERRUPT()	FreeRTOS_ClearTickInterrupt()\n"
	}
	# end of if $proctype == "ps7_cortexa9"



	############################################################################
	## Add constants specific to the microblaze
	############################################################################
	if { $proctype == "microblaze" } {
		# Interrupt controller setting assumes only one is in use.
		puts $config_file "#define configINTERRUPT_CONTROLLER_TO_USE XPAR_INTC_SINGLE_DEVICE_ID"
		puts $config_file "#define configINSTALL_EXCEPTION_HANDLERS 1"

		# Avoid non #define statements getting included in assembly files.
		puts $config_file "#ifndef __ASSEMBLER__"
		puts $config_file "void vApplicationAssert( const char *pcFile, uint32_t ulLine );"
		puts $config_file "#endif"
	}
	# end of if $proctype == "microblaze"


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

proc xput_define { config_file parameter param_value } {
	puts $config_file "#define $parameter $param_value\n"
}

proc xhandle_mb_interrupts {} {

	set default_interrupt_handler "XNullHandler"
	set default_arg "XNULL"

	set source_interrupt_handler $default_interrupt_handler
	set source_handler_arg $default_arg

	# Handle the interrupt pin
	set sw_proc_handle [get_sw_processor]
	set periph [get_cells $sw_proc_handle]
	set source_ports [xget_interrupt_sources $periph]
	if {[llength $source_ports] > 1} {
		error "Too many interrupting ports on the MicroBlaze.  Should only find 1" "" "error"
		return
	}

	if {[llength $source_ports] == 1} {
		set source_port [lindex $source_ports 0]
		if {[llength $source_port] != 0} {
			set source_port_name [get_property NAME $source_port]
			set source_periph [get_cells -of_objects $source_port]
			set source_name [get_property NAME $source_periph]
			set source_driver [get_drivers $source_name]

			if {[string compare -nocase $source_driver ""] != 0} {
				set int_array [get_arrays -of_objects $source_driver]
				if {[llength $int_array] != 0} {
					set size [get_property PROPERTY.size $int_array]
					for {set i 0 } { $i < $size } { incr $i } {
						set int_port [lindex [get_property PARAM.int_port $int_array] $i]
						if {[llength $int_port] != 0} {
							if {[string compare -nocase $int_port $source_port_name] == 0 } {
								set source_interrupt_handler [lindex [get_property PARAM.int_handler $int_array] $i ]
								set source_handler_arg [lindex [get_property PARAM.int_handler_arg $int_array] $i ]
								if {[string compare -nocase $source_handler_arg DEVICE_ID] == 0 } {
									set source_handler_arg [xget_name $source_periph "DEVICE_ID"]
								} else {
									if {[llength $source_periph] == 0} {
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

    # Generate microblaze_interrupts_g.c file...
    xcreate_mb_intr_config_file $source_interrupt_handler $source_handler_arg
}

proc xcreate_mb_intr_config_file {handler arg} {

    set mb_table "MB_InterruptVectorTable"
	variable standalone_version

	set filename [file join ".." "${standalone_version}" "src" "microblaze_interrupts_g.c"]
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

# --------------------------------------
# Return true if this MB has
# exception handling support
# --------------------------------------
proc mb_has_exceptions { hw_proc_handle } {

    # Check if the following parameters exist on this MicroBlaze's MPD
    set ee [get_property CONFIG.C_UNALIGNED_EXCEPTIONS $hw_proc_handle]
    if { $ee != "" } {
        return true
    }

    set ee [get_property CONFIG.C_ILL_OPCODE_EXCEPTION $hw_proc_handle]
    if { $ee != "" } {
        return true
    }
    set ee [get_property CONFIG.C_IOPB_BUS_EXCEPTION  $hw_proc_handle]
    if { $ee != "" } {
        return true
    }
    set ee [get_property CONFIG.C_DOPB_BUS_EXCEPTION  $hw_proc_handle]
    if { $ee != "" } {
        return true
    }
    set ee [get_property CONFIG.C_DIV_BY_ZERO_EXCEPTION $hw_proc_handle]
    if { $ee != "" } {
        return true
    }
    set ee [get_property CONFIG.C_DIV_ZERO_EXCEPTION $hw_proc_handle]
    if { $ee != "" } {
        return true
    }
    set ee [get_property CONFIG.C_FPU_EXCEPTION   $hw_proc_handle]
    if { $ee != "" } {
        return true
    }
    set ee [get_property CONFIG.C_USE_MMU    $hw_proc_handle]
    if { $ee != "" } {
        return true
    }
    return false
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

    set sw_proc_handle [get_sw_processor]
    set hw_proc_handle [get_cells [get_property HW_INSTANCE $sw_proc_handle] ]
    set proctype [get_property IP_NAME $hw_proc_handle]
    set procver [get_ip_version $hw_proc_handle]

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

# --------------------------------------
# Return true if this MB has PVR support
# --------------------------------------
proc mb_has_pvr { hw_proc_handle } {

    # Check if the following parameters exist on this MicroBlaze's MPD
    set pvr [get_property CONFIG.C_PVR $hw_proc_handle]
    if { $pvr != "" } {
        return true
    }

    return false
}

# --------------------------------------
# Microblaze config checks
# --------------------------------------
proc mb_drc_checks { } {
	set compiler [common::get_property CONFIG.compiler $sw_proc_handle]

	# check for valid compiler
	if { [string first "mb-gcc" $compiler] == 0 && [string first "mb-g++" $compiler] == 0} {
		error "Wrong compiler requested. FreeRTOS can be compiled only with the GNU compiler for MicroBlaze." "" "mdt_error"
	}

	# check for valid stdio parameters
	set stdin  [common::get_property CONFIG.stdin  $os_handle]
	set stdout [common::get_property CONFIG.stdout $os_handle]
	if { $stdin == "none" || $stdout == "none" } {
		error "The STDIN/STDOUT parameters are not set. FreeRTOS requires stdin/stdout to be set." "" "mdt_error"
	}

	# check if the design has a intc
	set intr_port [hsi::get_pins -of_objects $hw_proc_handle Interrupt]
	set intr_flag 1
	if { [llength $intr_port] == 0 } {
		set intr_flag 0
	} else {
		set intr_net [hsi::get_nets -of_objects $intr_port]
		if  { [llength $intr_port] == 0 }  {
			set intr_flag 0
		}
	}

	if {$intr_flag == 0 } {
		error "CPU has no connection to Interrupt controller." "" "mdt_error"
	}

	# support only AXI/PLB
	set bus_name ""
	set interconnect [common::get_property CONFIG.C_INTERCONNECT $hw_proc_handle]
	puts [format "hw_proc_handle is %s" $hw_proc_handle]
	if { $interconnect == 2 } {
		set intf_pin [hsi::get_intf_pins -of_objects $hw_proc_handle "M_AXI_DP"]
		if { [llength $intf_pin] } {
			set bus_name [hsi::get_intf_nets -of_objects $intf_pin]
		}
	} else {
		error "FreeRTOS supports Microblaze with only a AXI interconnect" "" "mdt_error"
	}

	if { [llength $bus_name] == 0 } {
		error "Microblaze M_AXI_DP is not connected to slave peripherals"
	}

	# obtain handles to all the peripherals in the design
	set slave_ifs [hsi::get_intf_pins -of_objects $bus_name -filter "TYPE==SLAVE"]
	puts [format "slave_ifs %s bus_name %s" $slave_ifs $bus_name]
	set timer_count 0
	set timer_has_intr 0

	# check for a valid timer
	foreach if $slave_ifs {
		set ip_handle [hsi::get_cells -of_objects $if]

		if {$ip_handle != $hw_proc_handle} {
			set type [common::get_property IP_NAME $ip_handle]
			if { $type == "axi_timer" } {
				incr timer_count

				# check if the timer interrupts are enabled
				set intr_port [hsi::get_pins -of_objects $ip_handle interrupt]
				if { [llength $intr_port] != 0 } {
					set intr_net [hsi::get_nets -of_objects $intr_port]
					if { [llength $intr_net] !=  0 } {
						set timer_has_intr 1
					}
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

	set systmr_interval_ms [common::get_property CONFIG.systmr_interval $os_handle]
	if { $systmr_interval_ms <= 0 } {
		error "Invalid value for parameter systmr_interval specified. Please specify a positive value." "" "mdt_error"
	}
}












