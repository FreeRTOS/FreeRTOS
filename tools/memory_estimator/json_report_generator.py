import os
import copy
from operator import truediv


# Some of the file names are customized when diplaying on the website. This dict
# contains the mappings of original file name to customized name with additional
# information.
__FILE_NAME_TO_DISPLAY_NAME__ = {
        "http_parser.c": "http_parser.c (third-party utility)"
    }


def convert_size_to_kb(byte_size):
    kb_size = round(truediv(int(byte_size),1024),1)
    if (kb_size == 0.0):
        return 0.1
    else:
        return kb_size


def parse_sizes(sizes):
    '''
    It assumes the Berkley output format:
    text       data     bss     dec     hex filename

    Returns a dict of the following format:
    {
        'file_name':'size',
        'file_name':'size'
    }
    '''
    filename_to_size_dict = {}

    # The first line is the size tool command and the second line is the
    # header. Therefore, we start from third line which contains actual sizes.
    for size in sizes[2:]:
        parts = size.split()

        filename = os.path.basename(parts[5])
        c_filename = str(filename.replace('.o','.c').strip())

        text_size = parts[0].strip()
        text_size_in_kb = convert_size_to_kb(text_size)

        filename_to_size_dict[c_filename] = text_size_in_kb

    return filename_to_size_dict


def update_json_report(lib_name, o1_sizes, os_sizes, size_description, lib_report_template, generated_json_report):
    filename_to_o1_size_dict = parse_sizes(o1_sizes)
    filename_to_os_size_dict = parse_sizes(os_sizes)

    # Make a copy of the template.
    lib_report = copy.deepcopy(lib_report_template)

    # Populate files in the library report.
    for filename in filename_to_o1_size_dict:
        file_report = {}
        file_report['file_name'] = __FILE_NAME_TO_DISPLAY_NAME__.get(filename, filename)
        file_report['o1_size'] = '{:.1f}K'.format(filename_to_o1_size_dict[filename])
        file_report['os_size']= '{:.1f}K'.format(filename_to_os_size_dict[filename])
        lib_report['files'].append(file_report)

    # Update total size of the library.
    lib_report['total']['total_o1'] = '{:.1f}K'.format(sum(filename_to_o1_size_dict.values()))
    lib_report['total']['total_os'] = '{:.1f}K'.format(sum(filename_to_os_size_dict.values()))

    # Add the size description.
    lib_report['table_header'] = size_description

    # Add the library report to the report.
    generated_json_report[lib_name] = lib_report

