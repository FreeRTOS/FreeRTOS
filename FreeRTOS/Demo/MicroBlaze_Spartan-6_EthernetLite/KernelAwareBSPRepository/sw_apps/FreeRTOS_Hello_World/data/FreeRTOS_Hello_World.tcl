proc swapp_get_name {} {
    return "FreeRTOS Hello World";
}

proc swapp_get_description {} {
    return "Let's say 'Hello World' in FreeRTOS.";
}

proc get_os {} {
    set oslist [xget_sw_modules "type" "os"];
    set os [lindex $oslist 0];

    if { $os == "" } {
        error "No Operating System specified in the Board Support Package.";
    }

    return $os;
}

proc get_stdout {} {
    set os [get_os];
    set stdout [xget_sw_module_parameter $os "STDOUT"];
    return $stdout;
}

proc check_stdout_hw {} {
    set uartlites [xget_ips "type" "uartlite"];
    set uart16550s [xget_ips "type" "uart16550"];
    if { ([llength $uartlites] == 0) && ([llength $uart16550s] == 0) } {
        # Check for MDM-Uart peripheral. The MDM would be listed as a peripheral
        # only if it has a UART interface. So no further check is required
        set mdmlist [xget_ips "type" "mdm"]
        if { [llength $mdmlist] == 0 } {
	    error "This application requires a Uart IP in the hardware."
        }
    }
}

proc check_stdout_sw {} {
    set stdout [get_stdout];
    if { $stdout == "none" } {
        error "The STDOUT parameter is not set on the OS. Hello World requires stdout to be set."
    }
}

proc get_mem_size { memlist } {
    return [lindex $memlist 4];
}

proc require_memory {memsize} {
    set imemlist [xget_memory_ranges "access_type" "I"];
    set idmemlist [xget_memory_ranges "access_type" "ID"];
    set dmemlist [xget_memory_ranges "access_type" "D"];

    set memlist [concat $imemlist $idmemlist $dmemlist];

    while { [llength $memlist] > 3 } {
        set mem [lrange $memlist 0 4];
        set memlist [lreplace $memlist 0 4];

        if { [get_mem_size $mem] >= $memsize } {
            return 1;
        }
    }

    error "This application requires atleast $memsize bytes of memory.";
}

proc swapp_is_supported_hw {} {
    # check for uart peripheral
    check_stdout_hw;

    # require about 1M of memory
    require_memory "1000000";

    return 1;
}

proc swapp_is_supported_sw {} {
    # check for stdout being set
    check_stdout_sw;

    return 1;
}

proc generate_stdout_config { fid } {
    set stdout [get_stdout];

    # if stdout is uartlite, we don't have to generate anything
    set stdout_type [xget_ip_attribute "type" $stdout];

    if { [regexp -nocase "uartlite" $stdout_type] || [string match -nocase "mdm" $stdout_type] } {
        return;
    } elseif { [regexp -nocase "uart16550" $stdout_type] } {
	# mention that we have a 16550
        puts $fid "#define STDOUT_IS_16550";

        # and note down its base address
	set prefix "XPAR_";
	set postfix "_BASEADDR";
	set stdout_baseaddr_macro $prefix$stdout$postfix;
	set stdout_baseaddr_macro [string toupper $stdout_baseaddr_macro];
	puts $fid "#define STDOUT_BASEADDR $stdout_baseaddr_macro";
    }
}

# depending on the type of os (standalone|xilkernel), choose
# the correct source files
proc swapp_generate {} {

    # cleanup this file for writing
    set fid [open "platform_config.h" "w+"];
    puts $fid "#ifndef __PLATFORM_CONFIG_H_";
    puts $fid "#define __PLATFORM_CONFIG_H_\n";

    # if we have a uart16550 as stdout, then generate some config for that
    generate_stdout_config $fid;

    puts $fid "#endif";
    close $fid;
}

proc swapp_get_linker_constraints {} {

    # we need a 4k heap
    return "stack 40k heap 40k";
}
