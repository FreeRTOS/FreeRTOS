

def generate_makefile_from_template(source_files, include_dirs, optimization, template_file, output_file):
    '''
    source_files - A list containing all source files.
    include_dirs - A list containing all include directories.
    optimization - Compiler optimization (O0, Os etc.).
    template_file - Makefile template to use.
    output_file - Generated Makefile path.
    '''
    formatted_source_files = 'SRCS=' + ' \\\n'.join(source_files)
    formatted_source_files += '\n'

    formatted_include_dirs=''
    for include_dir in include_dirs:
        formatted_include_dirs += 'INCLUDE_DIRS+=-I ' + include_dir + '\n'
    formatted_include_dirs += '\n'

    with open(template_file, 'r') as f:
        makefile_content = f.read()

    makefile_content = makefile_content.replace('SOURCE_FILES', formatted_source_files)
    makefile_content = makefile_content.replace('INCLUDE_DIRECTORIES', formatted_include_dirs)
    makefile_content = makefile_content.replace('OPTIMIZATION', optimization)

    with open(output_file, 'w') as f:
        f.write(makefile_content)
