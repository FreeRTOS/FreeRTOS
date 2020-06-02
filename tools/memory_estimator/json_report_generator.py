import os
import json
from operator import truediv


# Some of the file names are modified when diplaying on the website. This dict
# contains the mappings from file name to display name for those files.
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

    for size in sizes[2:]:
        parts = size.split()

        filename = os.path.basename(parts[5])
        c_filename = str(filename.replace('.o','.c').strip())

        text_size = parts[0].strip()
        text_size_in_kb = convert_size_to_kb(text_size)

        filename_to_size_dict[c_filename] = text_size_in_kb

    return filename_to_size_dict


def update_json_report(lib_name, o1_sizes, os_sizes, report_json_file):
    filename_to_o1_size_dict = parse_sizes(o1_sizes)
    filename_to_os_size_dict = parse_sizes(os_sizes)

    with open(report_json_file) as report_json_file_handle:
        report_json_data = json.load(report_json_file_handle)

    lib_report = report_json_data[lib_name]

    # Populate files in the library report.
    for filename in filename_to_o1_size_dict:
        file_report = {}
        file_report['file_name'] = __FILE_NAME_TO_DISPLAY_NAME__.get(filename, filename)
        file_report['o1_size'] = str(filename_to_o1_size_dict[filename]) + 'K'
        file_report['os_size']= str(filename_to_os_size_dict[filename]) + 'K'
        lib_report['files'].append(file_report)

    # Update total size of the library.
    lib_report['total']['total_o1'] = str(round(sum(filename_to_o1_size_dict.values()), 1)) + 'K'
    lib_report['total']['total_os'] = str(round(sum(filename_to_os_size_dict.values()), 1)) + 'K'

    # Update the library report in the json report.
    report_json_data[lib_name] = lib_report

    with open(report_json_file, 'w') as report_json_file_handle:
        report_json_file_handle.write(json.dumps(report_json_data, indent=4, sort_keys=True))
