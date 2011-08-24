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
    set p7_uarts [xget_ips "type" "ps7_uart"];
    set uartlites [xget_ips "type" "uartlite"];
    set uart16550s [xget_ips "type" "uart16550"];
    if { ([llength $p7_uarts] == 0) && ([llength $uartlites] == 0) &&
	 ([llength $uart16550s] == 0) } {
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

proc swapp_is_supported_hw {} {
    # check for uart peripheral
    check_stdout_hw;

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

    if { [regexp -nocase "uartlite" $stdout_type] || [string match -nocase "mdm" $stdout_type] ||
	 [regexp -nocase "ps7_uart" $stdout_type]} {
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

proc generate_cache_mask { fid } {
    set mask [format "0x%x" [xget_ppc_cache_mask]]
    puts $fid "#ifdef __PPC__"
    puts $fid "#define CACHEABLE_REGION_MASK $mask"
    puts $fid "#endif\n"
}

# depending on the type of os (standalone|xilkernel), choose
# the correct source files
proc swapp_generate {} {
    set os [get_os];

    if { $os == "xilkernel" } {
        file rename -force "helloworld_xmk.c" "helloworld.c"
    } else {
        file delete -force "helloworld_xmk.c"
    }

    # cleanup this file for writing
    set fid [open "platform_config.h" "w+"];
    puts $fid "#ifndef __PLATFORM_CONFIG_H_";
    puts $fid "#define __PLATFORM_CONFIG_H_\n";

    # if we have a uart16550 as stdout, then generate some config for that
    generate_stdout_config $fid;

    # for ppc, generate cache mask string
    generate_cache_mask $fid;

    puts $fid "#endif";
    close $fid;
}

proc swapp_get_linker_constraints {} {
    # this app does not require a .vectors section if it is being run w/ the standalone OS on PPC
    set os [get_os];

    if { $os == "standalone" } {
        return "vector_section no";
    }

    return "";
}
