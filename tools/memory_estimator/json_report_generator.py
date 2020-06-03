import os
import json
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

    for size in sizes[2:]:
        parts = size.split()

        filename = os.path.basename(parts[5])
        c_filename = str(filename.replace('.o','.c').strip())

        text_size = parts[0].strip()
        text_size_in_kb = convert_size_to_kb(text_size)

        filename_to_size_dict[c_filename] = text_size_in_kb

    return filename_to_size_dict


def update_json_report(lib_name, o1_sizes, os_sizes, size_description, json_report_template, generated_json_report):
    filename_to_o1_size_dict = parse_sizes(o1_sizes)
    filename_to_os_size_dict = parse_sizes(os_sizes)

    # Read the template to obtain the library report format.
    with open(json_report_template) as json_report_template_handle:
        json_report_template_data = json.load(json_report_template_handle)

    lib_report = json_report_template_data['lib']

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

    # Add the size description.
    lib_report['table_header'] = size_description

    # Get the generated report so far.
    with open(generated_json_report) as generated_json_report_handle:
        generated_report_json_data = json.load(generated_json_report_handle)

    # Add the library report to the report.
    generated_report_json_data[lib_name] = lib_report

    # Write the updated report back to the report file.
    with open(generated_json_report, 'w') as generated_json_report_handle:
        generated_json_report_handle.write(json.dumps(generated_report_json_data, indent=4, sort_keys=True))
