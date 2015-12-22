
################################################################
# This is a generated script based on design: design_1
#
# Though there are limitations about the generated script,
# the main purpose of this utility is to make learning
# IP Integrator Tcl commands easier.
################################################################

################################################################
# Check if script is running in correct Vivado version.
################################################################
set scripts_vivado_version 2015.1
set current_vivado_version [version -short]

if { [string first $scripts_vivado_version $current_vivado_version] == -1 } {
   puts ""
   puts "ERROR: This script was generated using Vivado <$scripts_vivado_version> and is being run in <$current_vivado_version> of Vivado. Please run the script in Vivado <$scripts_vivado_version> then open the design in Vivado <$current_vivado_version>. Upgrade the design by running \"Tools => Report => Report IP Status...\", then run write_bd_tcl to create an updated script."

   return 1
}

################################################################
# START
################################################################

# To test this script, run the following commands from Vivado Tcl console:
# source design_1_script.tcl

# If you do not already have a project created,
# you can create a project using the following command:
#    create_project project_1 myproj -part xc7vx485tffg1761-2
#    set_property BOARD_PART xilinx.com:vc707:part0:1.2 [current_project]

# CHECKING IF PROJECT EXISTS
if { [get_projects -quiet] eq "" } {
   puts "ERROR: Please open or create a project!"
   return 1
}



# CHANGE DESIGN NAME HERE
set design_name design_1

# If you do not already have an existing IP Integrator design open,
# you can create a design using the following command:
#    create_bd_design $design_name

# Creating design if needed
set errMsg ""
set nRet 0

set cur_design [current_bd_design -quiet]
set list_cells [get_bd_cells -quiet]

if { ${design_name} eq "" } {
   # USE CASES:
   #    1) Design_name not set

   set errMsg "ERROR: Please set the variable <design_name> to a non-empty value."
   set nRet 1

} elseif { ${cur_design} ne "" && ${list_cells} eq "" } {
   # USE CASES:
   #    2): Current design opened AND is empty AND names same.
   #    3): Current design opened AND is empty AND names diff; design_name NOT in project.
   #    4): Current design opened AND is empty AND names diff; design_name exists in project.

   if { $cur_design ne $design_name } {
      puts "INFO: Changing value of <design_name> from <$design_name> to <$cur_design> since current design is empty."
      set design_name [get_property NAME $cur_design]
   }
   puts "INFO: Constructing design in IPI design <$cur_design>..."

} elseif { ${cur_design} ne "" && $list_cells ne "" && $cur_design eq $design_name } {
   # USE CASES:
   #    5) Current design opened AND has components AND same names.

   set errMsg "ERROR: Design <$design_name> already exists in your project, please set the variable <design_name> to another value."
   set nRet 1
} elseif { [get_files -quiet ${design_name}.bd] ne "" } {
   # USE CASES: 
   #    6) Current opened design, has components, but diff names, design_name exists in project.
   #    7) No opened design, design_name exists in project.

   set errMsg "ERROR: Design <$design_name> already exists in your project, please set the variable <design_name> to another value."
   set nRet 2

} else {
   # USE CASES:
   #    8) No opened design, design_name not in project.
   #    9) Current opened design, has components, but diff names, design_name not in project.

   puts "INFO: Currently there is no design <$design_name> in project, so creating one..."

   create_bd_design $design_name

   puts "INFO: Making design <$design_name> as current_bd_design."
   current_bd_design $design_name

}

puts "INFO: Currently the variable <design_name> is equal to \"$design_name\"."

if { $nRet != 0 } {
   puts $errMsg
   return $nRet
}

##################################################################
# DESIGN PROCs
##################################################################



# Procedure to create entire design; Provide argument to make
# procedure reusable. If parentCell is "", will use root.
proc create_root_design { parentCell } {

  if { $parentCell eq "" } {
     set parentCell [get_bd_cells /]
  }

  # Get object for parentCell
  set parentObj [get_bd_cells $parentCell]
  if { $parentObj == "" } {
     puts "ERROR: Unable to find parent cell <$parentCell>!"
     return
  }

  # Make sure parentObj is hier blk
  set parentType [get_property TYPE $parentObj]
  if { $parentType ne "hier" } {
     puts "ERROR: Parent <$parentObj> has TYPE = <$parentType>. Expected to be <hier>."
     return
  }

  # Save current instance; Restore later
  set oldCurInst [current_bd_instance .]

  # Set parent object as current
  current_bd_instance $parentObj


  # Create interface ports
  set MAXIGP0 [ create_bd_intf_port -mode Master -vlnv xilinx.com:interface:aximm_rtl:1.0 MAXIGP0 ]
  set_property -dict [ list CONFIG.ADDR_WIDTH {40} CONFIG.DATA_WIDTH {128} CONFIG.NUM_READ_OUTSTANDING {8} CONFIG.NUM_WRITE_OUTSTANDING {8} CONFIG.PROTOCOL {AXI4}  ] $MAXIGP0

  # Create ports
  set maxigp0_aclk [ create_bd_port -dir I -type clk maxigp0_aclk ]

  # Create instance: processing_system8_0, and set properties
  set processing_system8_0 [ create_bd_cell -type ip -vlnv xilinx.com:ip:processing_system8:1.0 processing_system8_0 ]
  set_property -dict [ list CONFIG.preset {Remus}  ] $processing_system8_0

  # Create interface connections
  connect_bd_intf_net -intf_net processing_system8_0_MAXIGP0 [get_bd_intf_ports MAXIGP0] [get_bd_intf_pins processing_system8_0/MAXIGP0]

  # Create port connections
  connect_bd_net -net maxigp0_aclk_1 [get_bd_ports maxigp0_aclk] [get_bd_pins processing_system8_0/config_loop_in] [get_bd_pins processing_system8_0/dp_s_axis_audio_clk] [get_bd_pins processing_system8_0/maxigp0_aclk] [get_bd_pins processing_system8_0/maxigp1_aclk] [get_bd_pins processing_system8_0/ref_clk_in_n] [get_bd_pins processing_system8_0/ref_clk_in_p] [get_bd_pins processing_system8_0/rx_clk_iou17_user_13_n] [get_bd_pins processing_system8_0/rx_clk_iou17_user_13_p] [get_bd_pins processing_system8_0/sacefpd_aclk] [get_bd_pins processing_system8_0/saxiacp_aclk] [get_bd_pins processing_system8_0/saxigp0_rclk] [get_bd_pins processing_system8_0/saxigp0_wclk] [get_bd_pins processing_system8_0/saxigp1_rclk] [get_bd_pins processing_system8_0/saxigp1_wclk] [get_bd_pins processing_system8_0/saxigp2_rclk] [get_bd_pins processing_system8_0/saxigp2_wclk] [get_bd_pins processing_system8_0/saxigp3_rclk] [get_bd_pins processing_system8_0/saxigp3_wclk] [get_bd_pins processing_system8_0/saxigp4_rclk] [get_bd_pins processing_system8_0/saxigp4_wclk] [get_bd_pins processing_system8_0/saxigp5_rclk] [get_bd_pins processing_system8_0/saxigp5_wclk] [get_bd_pins processing_system8_0/saxigp6_rclk] [get_bd_pins processing_system8_0/saxigp6_wclk] [get_bd_pins processing_system8_0/serdes_clk_in_n] [get_bd_pins processing_system8_0/serdes_clk_in_p] [get_bd_pins processing_system8_0/sys_1x_clk_in_n] [get_bd_pins processing_system8_0/sys_1x_clk_in_p] [get_bd_pins processing_system8_0/sys_2x_clk_in_n] [get_bd_pins processing_system8_0/sys_2x_clk_in_p]

  # Create address segments
  

  # Restore current instance
  current_bd_instance $oldCurInst

  save_bd_design
}
# End of create_root_design()


##################################################################
# MAIN FLOW
##################################################################

create_root_design ""


