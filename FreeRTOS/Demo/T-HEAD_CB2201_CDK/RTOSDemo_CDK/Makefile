.PHONY: clean All

All:
	@echo "----------Building project:[ RTOSDemo - BuildSet ]----------"
	@
	@cd "RTOSDemo" && make -f "RTOSDemo.mk" MakeIntermediateDirs && make -f "RTOSDemo.mk" -j 8
clean:
	@echo "----------Cleaning project:[ RTOSDemo - BuildSet ]----------"
	@cd "RTOSDemo" && make -f  "RTOSDemo.mk" clean
