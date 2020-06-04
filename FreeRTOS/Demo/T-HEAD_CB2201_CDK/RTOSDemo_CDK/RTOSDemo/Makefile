.PHONY: clean All

All:
	@echo "----------Building project:[ RTOSDemo - BuildSet ]----------"
	@
	@make -f "RTOSDemo.mk" MakeIntermediateDirs && make -f "RTOSDemo.mk" -j 8
clean:
	@echo "----------Cleaning project:[ RTOSDemo - BuildSet ]----------"
	@make -f  "RTOSDemo.mk" clean
