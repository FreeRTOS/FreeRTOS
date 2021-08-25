#-------------------------------------------------------------------------------
# This script takes an xml file which describes hardware options and produces
# header files in the target directory which are used by the embedded
# software. 
#-------------------------------------------------------------------------------

import datetime
import os
import os.path
import xml.etree.ElementTree as ET
import sys
from pathlib import Path


# --------------------------------------------------------------------------------------------
# mpfs_configuration_generator.py version
#
# 0.6.3 bug fix related to multiple xml file selection. and added libero design information 
# constants in fpga_design_config.h/ removed date,version and design information from all the files
# except fpga_design_config.h
#
# 0.6.2 added support for multiple xml file found in input folder
#       /empty xml file check/ xml filename arg in current folder/
#       if multiple files are there then the file with the latest time stamp will 
#       be selected. 
# 0.6.1 changed target folder name from soc_config to fpga_design_config
#
# 0.5.2 Aries Embedded Feedback: remove trailing spaces.
# 0.5.1 Added check that the source XML document is more recent than content of already existing
# SoC configuration files.
#
# 0.4.2 Allowed to only specify the folder where the input XML 
#       file is located. Use file ending with _mss_cfg.xml if one exists, any other .xml file in
#        the input folder otherwise.
#
# 0.4.1 Modified the arguments to allow specifying 
#       the folder where the soc_config folder should be generated.
#
# 0.3.4 fixed comment formatting bug in hw_memory.h generation
# 0.3.3 updated copyright format
# 0.3.2 removed leading zeros from decimal values ( clock rates)
# -------------------------------------------------------------------------------------------------------   
def get_script_ver():
    '''
    This changes anytime anytime the mpfs_configuration_generator.py script
    changes. This does not necessarily mean the xml format has been updated in
    get_xml_ver()
    :return: script version
    '''
    return "0.6.3"




# -----------------------------------------------------------------------------
# xml file to parse
# Also an xml files listing tags used for reference
# -----------------------------------------------------------------------------
reference_xml_file = \
    ('hardware_des_xml,src_example,mpfs_hw_ref_defaults.xml,default',
     'hardware_des_xml,src_example,mpfs_hw_ref_ddr3_100Mhz_ext_clk.xml,ddr3_100Mhz_ref')

xml_tag_file = 'hardware_des_xml,src_example,mpfs_hw_tag_reference.xml'


# -----------------------------------------------------------------------------
# xml tags, the structure here should follow the readme.md description
# contained in the root folder for tags
# Please note: The tag in the first column ( mss_xxx) is the same as the
# directory name (/fpga_design_config/mss_xxx)
# the fourth item lets program know how to format info in header file
# the six item lets program know how to format value, decimal or hex
# -----------------------------------------------------------------------------
xml_tags = ('mss_memory_map,map,mem_elements,fm_define,none,hex',
            'mss_memory_map,apb_split,registers,fm_struct,none,hex',
            'mss_memory_map,cache,registers,fm_struct,none,hex',
            'mss_memory_map,pmp_h0,registers,fm_struct,HART0_,hex64',
            'mss_memory_map,pmp_h1,registers,fm_struct,HART1_,hex64',
            'mss_memory_map,pmp_h2,registers,fm_struct,HART2_,hex64',
            'mss_memory_map,pmp_h3,registers,fm_struct,HART3_,hex64',
            'mss_memory_map,pmp_h4,registers,fm_struct,HART4_,hex64',
            'mss_memory_map,mpu_fic0,registers,fm_struct,FIC0_,hex64',
            'mss_memory_map,mpu_fic1,registers,fm_struct,FIC1_,hex64',
            'mss_memory_map,mpu_fic2,registers,fm_struct,FIC2_,hex64',
            'mss_memory_map,mpu_crypto,registers,fm_struct,CRYPTO_,hex64',
            'mss_memory_map,mpu_gem0,registers,fm_struct,GEM0_,hex64',
            'mss_memory_map,mpu_gem1,registers,fm_struct,GEM1_,hex64',
            'mss_memory_map,mpu_usb,registers,fm_struct,USB_,hex64',
            'mss_memory_map,mpu_mmc,registers,fm_struct,MMC_,hex64',
            'mss_memory_map,mpu_scb,registers,fm_struct,SCB_,hex64',
            'mss_memory_map,mpu_trace,registers,fm_struct,TRACE_,hex64',
            'mss_io,io_mux,registers,fm_reg,none,hex',
            'mss_io,hsio,registers,fm_reg,none,hex',
            'mss_sgmii,tip,registers,fm_reg,none,hex',
            'mss_ddr,options,registers,fm_reg,none,hex',
            'mss_ddr,io_bank,registers,fm_reg,none,hex',
            'mss_ddr,mode,registers,fm_reg,none,hex',
            'mss_ddr,off_mode,registers,fm_reg,none,hex',
            'mss_ddr,segs,registers,fm_reg,none,hex',
            'mss_ddr,ddrc,registers,fm_reg,none,hex',
            'mss_clocks,clocks,registers,fm_define,none,decimal',
            'mss_clocks,mss_sys,registers,fm_define,MSS_,hex',
            'mss_clocks,mss_pll,registers,fm_define,MSS_,hex',
            'mss_clocks,sgmii_pll,registers,fm_reg,SGMII_,hex',
            'mss_clocks,ddr_pll,registers,fm_reg,DDR_,hex',
            'mss_clocks,mss_cfm,registers,fm_reg,MSS_,hex',
            'mss_clocks,sgmii_cfm,registers,fm_reg,SGMII_,hex',
            'mss_general,mss_peripherals,registers,fm_reg,none,hex',)


# -----------------------------------------------------------------------------
#  Header files to generate
# -----------------------------------------------------------------------------
header_files = ('fpga_design_config,memory_map,hw_memory.h',
                'fpga_design_config,memory_map,hw_apb_split.h',
                'fpga_design_config,memory_map,hw_cache.h',
                'fpga_design_config,memory_map,hw_pmp_hart0.h',
                'fpga_design_config,memory_map,hw_pmp_hart1.h',
                'fpga_design_config,memory_map,hw_pmp_hart2.h',
                'fpga_design_config,memory_map,hw_pmp_hart3.h',
                'fpga_design_config,memory_map,hw_pmp_hart4.h',
                'fpga_design_config,memory_map,hw_mpu_fic0.h',
                'fpga_design_config,memory_map,hw_mpu_fic1.h',
                'fpga_design_config,memory_map,hw_mpu_fic2.h',
                'fpga_design_config,memory_map,hw_mpu_crypto.h',
                'fpga_design_config,memory_map,hw_mpu_gem0.h',
                'fpga_design_config,memory_map,hw_mpu_gem1.h',
                'fpga_design_config,memory_map,hw_mpu_usb.h',
                'fpga_design_config,memory_map,hw_mpu_mmc.h',
                'fpga_design_config,memory_map,hw_mpu_scb.h',
                'fpga_design_config,memory_map,hw_mpu_trace.h',
                'fpga_design_config,io,hw_mssio_mux.h',
                'fpga_design_config,io,hw_hsio_mux.h',
                'fpga_design_config,sgmii,hw_sgmii_tip.h',
                'fpga_design_config,ddr,hw_ddr_options.h',
                'fpga_design_config,ddr,hw_ddr_io_bank.h',
                'fpga_design_config,ddr,hw_ddr_mode.h',
                'fpga_design_config,ddr,hw_ddr_off_mode.h',
                'fpga_design_config,ddr,hw_ddr_segs.h',
                'fpga_design_config,ddr,hw_ddrc.h',
                'fpga_design_config,clocks,hw_mss_clks.h',
                'fpga_design_config,clocks,hw_clk_sysreg.h',
                'fpga_design_config,clocks,hw_clk_mss_pll.h',
                'fpga_design_config,clocks,hw_clk_sgmii_pll.h',
                'fpga_design_config,clocks,hw_clk_ddr_pll.h',
                'fpga_design_config,clocks,hw_clk_mss_cfm.h',
                'fpga_design_config,clocks,hw_clk_sgmii_cfm.h',
                'fpga_design_config,general,hw_gen_peripherals.h')

MAX_LINE_WIDTH = 80


# -----------------------------------------------------------------------------
# Read the xml file into ET
# -----------------------------------------------------------------------------
def read_xml_file(s):
    file_dir = os.path.join(*s)
    tree = ET.parse(file_dir.strip())
    root = tree.getroot()  # type: object
    return root


# -----------------------------------------------------------------------------
#  Routine to make a folder
# -----------------------------------------------------------------------------
def safe_make_folder(i):
    '''Makes a folder (and its parents) if not present'''
    try:
        os.makedirs(i)
    except:
        pass


# -----------------------------------------------------------------------------
# Create the directory structure
# -----------------------------------------------------------------------------
def create_hw_dir_struct(root_folder, TOP):
    '''Creates directory structure off root, subdirectories passed in a tupple'''
    for folder in TOP:
        safe_make_folder(root_folder + '/' + folder)


# -----------------------------------------------------------------------------
#  Generate the copyright notice at the top of the header file
# -----------------------------------------------------------------------------
def WriteCopyright(root, theFile, filename, creator):
    '''
    generate copyright notice based on the following:
    #/*******************************************************************************
    # * Copyright 2019-2020 Microchip FPGA Embedded Systems Solutions.
    # *
    # * SPDX-License-Identifier: MIT
    # *
    # * MPFS HAL Embedded Software
    # *
    # */
    :param root:
    :param theFile:
    :param filename:
    :param creator:
    :return:
    '''
    theFile.write('/**********************************************************'
                  '*********************\n')
    theFile.write(" * Copyright 2019-" + str(datetime.datetime.now().year) + " Microchip FPGA Embedded Systems Solutions.\n")
    theFile.write(' *\n')
    theFile.write(' * SPDX-License-Identifier: MIT\n')
    theFile.write(' *\n')
    theFile.write(" * @file " + filename + "\n")
    theFile.write(" * @author " + creator + "\n")
    theFile.write(' *\n')
    if theFile.name == "fpga_design_config\fpga_design_config.h":
        for child in root:
            if child.tag == "design_information":
                for child1 in child:
                    if child1.tag == "design_name":
                        theFile.write(' * Libero design name: ' + child1.text.strip() + "\n")
                    if child1.tag == "libero_version":
                        theFile.write(' * Generated using Libero version: ' + child1.text.strip() + "\n")
                    if child1.tag == "mpfs_part_no":
                        theFile.write(' * MPFS part number used in design: ' + child1.text.strip() + "\n")
                    if child1.tag == "creation_date_time":
                        theFile.write(' * Date generated by Libero: ' + child1.text.strip() + "\n")
                    if child1.tag == "xml_format_version":
                        theFile.write(' * Format version of XML description: ' + child1.text.strip() + "\n")
        theFile.write(' * PolarFire SoC Configuration Generator version: ' + get_script_ver() + "\n")

    strings = ('', ' Note 1: This file should not be edited. If you need to modify a parameter',\
  ' without going through regenerating using the MSS Configurator Libero flow ' ,' or editing the associated xml file',\
  ' the following method is recommended: \n',\
  ' 1. edit the following file ',' boards/your_board/platform_config/mpfs_hal_config/mss_sw_config.h\n',\
  ' 2. define the value you want to override there.',' (Note: There is a commented example in the platform directory)\n',\
  ' Note 2: The definition in mss_sw_config.h takes precedence, as',\
  ' mss_sw_config.h is included prior to the generated header files located in', ' boards/your_board/fpga_design_config'\
           )
    for string in strings:
        theFile.write(' *' + string + "\n")
    theFile.write(' *\n */\n')


# -----------------------------------------------------------------------------
#  the header start define
# -----------------------------------------------------------------------------
def start_define(theFile, filename):
    filename = filename[:-2]  # remove .h from file name
    theFile.write('\n#ifndef ' + filename.upper() + '_H_')
    theFile.write('\n#define ' + filename.upper() + '_H_\n\n')


# -----------------------------------------------------------------------------
#  start c plus define
# -----------------------------------------------------------------------------
def start_cplus(theFile, filename):
    theFile.write('\n#ifdef __cplusplus\n')
    theFile.write('extern ' + ' \"C\"' + ' {\n')
    theFile.write('#endif\n\n')


# -----------------------------------------------------------------------------
#  end define associated with header start define
# -----------------------------------------------------------------------------
def end_define(theFile, filename):
    filename = filename[:-2]  # remove .h from file name
    theFile.write('\n#endif /*' + ' #ifdef ' + filename.upper() + '_H_ */\n\n')


# -----------------------------------------------------------------------------
#  end c++ define
# -----------------------------------------------------------------------------
def end_cplus(theFile, filename):
    theFile.write('\n#ifdef __cplusplus\n}\n#endif\n\n')


# -----------------------------------------------------------------------------
#  write line, break into chunks
# -----------------------------------------------------------------------------
def write_line(headerFile , reg_description):
    ''' write line, break into chunks '''
    word_list = reg_description.split()  # list of words
    sentence = word_list[0] + ' '
    word_list.pop(0)
    for word in word_list:
        if (len(sentence + word + ' ') > MAX_LINE_WIDTH):
            headerFile.write(sentence.rstrip() + '\n')
            sentence = word + ' '
        else:
            sentence = sentence + word + ' '
    if len(sentence) > 0:
        headerFile.write(sentence.rstrip() + '\n')


# -----------------------------------------------------------------------------
# Iterate through registers and produce header file output
# -----------------------------------------------------------------------------
def generate_register(headerFile, registers, tags):
    '''
    Parse registers tag for register tags and print to header file
    :param headerFile: header file to print to
    :param registers: registers in a tag
    :param tags: Some tags used to determine print format
    :return:
    '''
    for register in registers:
        # if tag 4 is set, pre-append register name with tag[4] value
        if tags[4] != 'none':
            pre_append = tags[4]
            name = 'LIBERO_SETTING_' + pre_append + register.get('name')
        else:
            name = 'LIBERO_SETTING_' + register.get('name')
        name_of_reg = name
        description = register.get('description')
        name_gap = 15
        if len(name) > 15:
            name_gap = len(name)
        s = '#define' + ' ' + name.ljust(name_gap, ' ')
        name = register.get('name') + "_OFF_MODE"
        name_gap = 15
        if len(name) > 15:
            name_gap = len(name)
        stest1 = '#define' + ' ' + name.ljust(name_gap, ' ')
        field_list = []
        reg_value = 0
        reg_value_default = 0
        for field in register:
            if field.tag == "field":
                gap = 30
                if len(field.get('name')) > gap:
                    gap = len(field.get('name')) + 4
                sfield = '    /* ' + field.get('name').ljust(gap, ' ')
                stemp = '    [' + field.get('offset') + ':' + field.get('width') + ']'
                stemp = stemp.ljust(12, ' ')
                sfield += stemp
                sfield += field.get('Type')
                if (field.get('Type') == 'RW'):
                    sfield += ' value= ' + field.text.strip()
                    temp_val = ((int(field.text.strip(), 16)) << int(field.get('offset')))
                    reg_value += temp_val
                sfield += ' */\n'
                # add the field to list of fields
                field_list.extend([sfield])
        if tags[5] == 'decimal':
            value = format(reg_value, '01X')
            default_value = format(reg_value_default, '08X')
        elif tags[5] == 'hex64':
            value = '0x' + format(reg_value, '016X')  + 'ULL'
            default_value = '0x' + format(reg_value_default, '08X')
        else :
            value = '0x' + format(reg_value, '08X')  + 'UL'
            default_value = '0x' + format(reg_value_default, '08X')
        name_gap = 4
        if len(s) >= name_gap:
            name_gap = len(s) + 4
        s = s.ljust(name_gap, ' ') + value + '\n'
        reg_description = '/*' + description + ' */\n'
        headerFile.write('#if !defined ' + '(' + name_of_reg + ')\n')
        # Write out the register description, max chars per line 80
        write_line(headerFile , reg_description)
        headerFile.write(s)
        for x in range(len(field_list)):
            headerFile.write(field_list[x])
        headerFile.write('#endif\n')


# -----------------------------------------------------------------------------
# Iterate through tag mem_elements looking for mem elements produce header file
# output
# -----------------------------------------------------------------------------
def generate_mem_elements(headerFile, mem_elements, tags):
    '''
    Parse registers tag for mem tags and print to header file
    :param headerFile:
    :param registers:
    :return:
    '''
    for mem in mem_elements:
        name = 'LIBERO_SETTING_' + mem.get('name')
        name_of_reg = name
        name_size = name + '_SIZE'
        description = mem.get('description')
        name_gap = 15
        if len(name) > 15:
            name_gap = len(name)
        s = '#define' + ' ' + name.ljust(name_gap, ' ')
        s1 = '#define' + ' ' + name_size.ljust(name_gap, ' ')
        # get the values
        mem_value = mem.text.strip()
        mem_size = mem.get('size')
        # make sure space between name and value 4 spaces
        name_gap = 4
        if len(s) >= name_gap:
            name_gap = len(s) + 4
        # make sure space between name and value 4 spaces
        name_size_gap = 4
        if len(s1) >= name_size_gap:
            name_size_gap = len(s1) + 4
        # create the strings for writing
        s = s.ljust(name_gap, ' ') + mem_value +  '\n'
        reg_description = '/*' + description + ' */\n'
        s1 = s1.ljust(name_size_gap, ' ') + mem_size \
             + '    /* Length of memory block*/ \n'
        headerFile.write('#if !defined ' + '(' + name_of_reg + ')\n')
        headerFile.write(reg_description)
        headerFile.write(s)
        headerFile.write(s1)
        headerFile.write('#endif\n')


# -----------------------------------------------------------------------------
# generate a header file
# -----------------------------------------------------------------------------
def generate_header( file, real_root, root, file_name, tags):
    creator = "Microchip-FPGA Embedded Systems Solutions"
    with open(file, 'w+') as headerFile:
        # write the copyright header
        WriteCopyright(real_root, headerFile, file_name, creator)
        start_define(headerFile, file_name)
        start_cplus(headerFile, file_name)
        for child in root:
            if child.tag == "registers":
                generate_register(headerFile, child, tags)
            if child.tag == "mem_elements":
                generate_mem_elements(headerFile, child, tags)
            for child2 in child:
                if child2.tag == "registers":
                    generate_register(headerFile, child2, tags)
        end_cplus(headerFile, file_name)
        end_define(headerFile, file_name)


# -----------------------------------------------------------------------------
# fpga_design_config.h header file generation. 
# -----------------------------------------------------------------------------

def write_libero_config_info(root,theFile):
    script_version = get_script_ver().split('.')
    tags_dic = {"design_name":"LIBERO_SETTING_DESIGN_NAME","libero_version":"LIBERO_SETTING_MSS_CONFIGURATOR_VERSION","mpfs_part_no" :"LIBERO_SETTING_MPFS_PART "\
        ,"creation_date_time":"LIBERO_SETTING_GENERATION_DATE","xml_format_version":"LIBERO_SETTING_XML_VERSION"}
    
    #max constant name size + some extra buffer space  
    max_gap = max([len(v) for k,v in tags_dic.items()]) + 8

    fixed_gap = 12 
    xml_version = []
    for child in root:
            if child.tag == "design_information":
                for child1 in child:
                    if child1.tag in tags_dic:
                        gap = max_gap - (len(tags_dic[child1.tag]))
                        theFile.write('#define  '+ tags_dic[child1.tag].ljust(4,' ') + " "*(gap + fixed_gap)  + "\"" + child1.text.strip() + "\"" + "\n")  
                        if child1.tag == "xml_format_version":
                            xml_version = child1.text.strip().split('.')
    
    const = {"LIBERO_SETTING_XML_VERSION_MAJOR": xml_version[0],"LIBERO_SETTING_XML_VERSION_MINOR":xml_version[1],"LIBERO_SETTING_XML_VERSION_PATCH":xml_version[2], "LIBERO_SETTING_HEADER_GENERATOR_VERSION":'.'.join(script_version),"LIBERO_SETTING_HEADER_GENERATOR_VERSION_MAJOR":script_version[0],"LIBERO_SETTING_HEADER_GENERATOR_VERSION_MINOR":script_version[1],"LIBERO_SETTING_HEADER_GENERATOR_VERSION_PATCH":script_version[2]}
    
    # write hard coded constants in the fpga_design_config.h file.
    for k,v in const.items(): 
        gap = max_gap - len(k)
        if k == "LIBERO_SETTING_HEADER_GENERATOR_VERSION":
            theFile.write('#define  '+ k.ljust(4,' ') + " "*(gap + fixed_gap)  + "\"" + v + "\"" + "\n")  
        else:
            theFile.write('#define  '+ k + " "*(gap + fixed_gap)  + v  + "\n")  
    #new line 
    theFile.write("\n")


def generate_reference_header_file(ref_header_file, root, header_files):
    creator = "Embedded Software"
    # itemName ="io_mux configuration"
    s = ref_header_file.split(',')
    file = os.path.join(*s)
    file_name = s[-1]
    with open(file, 'w+') as headerFile:
        # write the copyright header

        WriteCopyright(root, headerFile, file_name, creator)
        # add exclusive define
        start_define(headerFile, file_name)
        # include all the headers

        #define Libero design information constants 
        write_libero_config_info(root,headerFile)
        index = 0
        for child in header_files:
            c = header_files[index].split(',')
            c.remove('fpga_design_config')
            # include_file = os.path.join(*c)
            # as we need formatting correct for linux and windows
            include_file = c[0] + '/' + c[1]
            headerFile.write('#include \"' + include_file + '\"\n')
            index += 1
        # add the c++ define
        start_cplus(headerFile, file_name)
        # no content in this case
        comment = '/* No content in this file, used for referencing header */\n'
        headerFile.write(comment)
        # end the c++ define
        end_cplus(headerFile, file_name)
        end_define(headerFile, file_name)


# -----------------------------------------------------------------------------
#  Generate all the header files, passed in output_header_files
# -----------------------------------------------------------------------------
def generate_header_files(output_header_files, input_xml_file, input_xml_tags):
    # read in an xml file
    s = input_xml_file.split(',')

    root = read_xml_file(s)
    index = 0
    while index < len(input_xml_tags):
        ref_tags = input_xml_tags[index].split(',')
        s = output_header_files[index].split(',')
        file_name = s[-1]
        dir_name = s[-2]
        file_dir = os.path.join(*s)
        found_match = 0
        for child in root:
            if child.tag == 'mss_' + dir_name:
                for child1 in child:
                    if child1.tag == ref_tags[1]:
                        found_match = 1
                        break
        #
        # Next, create file based on xml content
        #
        if found_match == 1:
            generate_header(file_dir, root, child1, file_name, ref_tags)
        index += 1

    '''
    generate a header which references all the generated headers
    '''
    file_name = 'fpga_design_config,fpga_design_config.h'
    generate_reference_header_file(file_name, root, output_header_files)


# -----------------------------------------------------------------------------
# Return absolute path created from working directory location and relative
# path passed as argument. Handles path to an XML file and path to a folder.
# -----------------------------------------------------------------------------
def get_full_path(in_path):
    print(in_path)
    cwd = os.getcwd()
    print(cwd)
    filename = ''
    temp = in_path
    if in_path.endswith('.xml'):
        path_comp = in_path.split('/')
        last = len(path_comp) - 1
        filename = path_comp[last]
        
        in_path = in_path.replace(filename, '')
        print(in_path)
    if in_path == '':
        filename = temp 
        in_path = os.getcwd()
        print(in_path)
    else:
        xml_list = [] 
        dir_entries = os.listdir(in_path)
        for dir_entry in dir_entries:

            if dir_entry.endswith('.xml'):
                xml_list.append(dir_entry)
            else:
                if dir_entry.endswith('_mss_cfg.xml'):
                    xml_list.append(dir_entry) 
                    break
       #This section  will sort the xml file by the latest timestamp  
        if len(xml_list) > 1:

            xml_list = sort_by_timestamp(xml_list,in_path)
            filename = xml_list[-1]
            #prompt the selected filename 
            print("selected xml file is : {}".format(filename))
        else:
            if len(xml_list) != 0:
                filename = xml_list[0]

        print(in_path)
        
    try:
        print("trying to change directory")
        os.chdir(in_path)
        full_path = os.getcwd()
    except IOError:
        print("caught IO error ")
        sys.exit()

    os.chdir(cwd)
    full_path = full_path + '/' + filename
    if is_empty_file(full_path):
        print("\nxml File is empty")
        sys.exit()
    else:
        return full_path


# -------------------------------------------------------
# check is fpath is a file and empty 
# -------------------------------------------------------
def is_empty_file(fpath):  
    return os.path.isfile(fpath) and os.path.getsize(fpath) == 0

# -------------------------------------------------------
# sort file names on the basis of time stamp 
# -------------------------------------------------------
def sort_by_timestamp(file_name,file_path):
    cwd = os.getcwd()
    try :
        os.chdir(file_path)
        path = os.getcwd()
    except IOError : 
        print("not a valid folder name--------------")
        sys.exit()


    Files = [path + '/' + file_name[i] for i in range(len(file_name))]
    Files.sort(key=os.path.getmtime)
    s_file_name = []
    for i in range(len(Files)):
        s_file_name.append(Files[i].split('/')[-1])
    
    print("sorted list of files\n",s_file_name)
    os.chdir(cwd)
    return s_file_name

# -----------------------------------------------------------------------------
# helper for showing help information
# -----------------------------------------------------------------------------
def show_help():
    print ('no of args you entered = ' + str(len(sys.argv) - 1))
    print ('mpfs_configuration_generator.py :')
    print (' This program reads xml hardware definition, outputs: header files')
    print \
        (' Usage: python3 mpfs_configuration_generator.py [xml file path] [output folder path] ')
    print('path can be absolute as well as relative \n')
    input(' Please run again with correct arguments')


# -----------------------------------------------------------------------------
#    main function
#    todo: add options from the command line
# -----------------------------------------------------------------------------
def main_config_generator():
    '''
    This script takes an xml file which describes hardware options and produces
    header files in the target directory which are used by the embedded
    software.
    Currently there are Two command line arguments
    arg0: path to the folder containing xml file. 
    arg1: path of the folder where the fpga_design_config will be generated.
    Note - If multiple xml files are present then the one with the latest time stamp 
    will be selected. 

    '''

    #
    #  check/parse  arguments
    #
    nb_arguments = len(sys.argv) - 1
    if nb_arguments < 2:
        show_help()
        sys.exit()
    fullCmdArguments = sys.argv
    # - further arguments
    argumentList = fullCmdArguments[1:]
    input_xml_file = argumentList[0]
    input_xml_file = get_full_path(input_xml_file)

    if nb_arguments >= 2:
        output_folder_name = argumentList[1]
        output_folder_name = get_full_path(output_folder_name)
        os.chdir(output_folder_name)

    debug_reg_csv = False
    if nb_arguments >= 4:
        if argumentList[3] == 'debug_regs':
            debug_reg_csv = True
    if nb_arguments >= 3:
        if argumentList[2] == 'generate_refernce_xml':
            gen_xml = True
        else:
            gen_xml = False
    #
    # Check version of python interpreter, helps debugging
    # Currently runs on python version 2 and 3
    #
    print ('python interpreter details:',sys.version_info)
    if sys.version_info > (3, 0):
    #    # Python 3 code in this block
        print ('python interpreter running is version 3')
    else:
    #    # Python 2 code in this block
        print ('python interpreter running is version 2')
    
    # Create directory structure for the header files
    #
    root_folder = 'fpga_design_config'
    TOP = ['clocks', 'ddr', 'io', 'memory_map', 'sgmii', 'general']
    create_hw_dir_struct(root_folder, TOP)
    #
    # Next, read in XML content and create header files
    #
    generate_header_files(header_files, input_xml_file, xml_tags)
    print('Hardware configuration header files created in directory:', os.path.join(output_folder_name, 'fpga_design_config'))

if __name__ == "__main__":
    main_config_generator()


