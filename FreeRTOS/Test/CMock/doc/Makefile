DOXY_ARGS := "INPUT=../ \n FILE_PATTERNS=*.c *.h\n RECURSIVE=YES\n"
DOXY_ARGS += "EXCLUDE=../CMock/ ../config/ ../scripts/ ../build/\n"
DOXY_ARGS += "PROJECT_NAME=FreeRTOS Unit Tests\nGENERATE_LATEX=NO\n"
DOXY_ARGS += "OUTPUT_DIRECTORY=$(DOC_DIR)"

all:
	echo -e $(DOXY_ARGS) | doxygen -
