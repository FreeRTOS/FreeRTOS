# Instructions for adding new library doxygen docs to FreeRTOS.org

## Pre-requisites:
- Library is imported into <Root>/FreeRTOS-Plus/Source/FreeRTOS-IoT-Libraries-LTS-Beta1.
- Demos are complete in <Root>/FreeRTOS-Plus/Source/FreeRTOS-IoT-Libraries-LTS-Beta1.
- Install the latest Doxygen.

## Instructions
1. Create a layout file under **doc/config/**. Please name it "**layout_*libraryname***". Please replace *libraryname* with the same name as the library's folder name, for consistency.
   Please see **doc/config/layout_mqtt.xml** for an example layout file.
1. Create a configuration file under **doc/config/**. Please name it the same name as the library's folder name, for consistency.  
   Please see **doc/config/mqtt** for an example configuration file.
1. Create/import supporting doxygen documentation under *doc/lib/*. Please name the file the same as the library's folder name, for consistency.
   Please see **doc/lib/mqtt.txt** for an example supporting documentation file.   
1. Run doc/generate_doc.sh to generate all docs for all libraries (the command below is from the root of this repo).
   ```
   $ ./doc/generate_doc.sh .
   ```
1. Verify your library's generated pages by opening **doc/output/*libraryname*/index.html**. 