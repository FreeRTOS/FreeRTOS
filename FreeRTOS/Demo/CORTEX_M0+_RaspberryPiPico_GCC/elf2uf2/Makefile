HOSTCXX = g++
HOSTCXXFLAGS = -std=c++14

include ../common.mk
ELF2_UF2_SOURCES += main.cpp

$(BUILD_DIR)/elf2uf2/elf2uf2: $(ELF2_UF2_SOURCES)
	mkdir -p $(@D)
	$(HOSTCXX) $(HOSTCXXFLAGS) $(ELF2_UF2_INCLUDE_DIRS) $< -o $@

clean:
	-rm -rf build