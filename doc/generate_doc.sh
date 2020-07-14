#!/bin/sh

# Check arguments.
if [ $# -ne 1 ]; then
    echo "Usage: ./generate_doc.sh sdk_root_directory"
    exit 1
fi

# Change to SDK root directory.
cd $1

# Check for doxygen.
command -v doxygen > /dev/null || { echo "Doxygen not found. Exiting."; exit 1; }

# Doxygen must be run twice: once to generate tags and once more to link tags.
i=0; while [ $i -le 1 ]; do
    # Run for each library config file.
    for file in doc/config/*; do
        # Ignore directories.
        if [ -d $file ]; then
            continue
        fi

        # Ignore xml files.
        if [ ${file##*.} = "xml" ]; then
            continue
        fi

        # Ignore the common configuration file.
        if [ $file = "doc/config/common" ]; then
            continue
        fi

        # Generate Doxygen tags first. Once tags are generated, generate documentation.
        if [ $i -eq 0 ]; then
            echo "Generating Doxygen tags for $file..."
            doxygen $file 2> /dev/null
        else
            echo "Generating documentation for $file..."

            # Redirect errors to file when running under Travis CI.
            doxygen $file 2>>doxygen_warnings.txt
        fi
    done

    i=$(($i+1));
done

echo "Documentation written to doc/output"

# Print any doxygen errors or warnings and exit with a nonzero value.
if [ -s doxygen_warnings.txt ]; then
    cat doxygen_warnings.txt
    exit 1
fi
