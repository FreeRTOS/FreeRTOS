# Copyright (c) 2019 SiFive Inc.
#
# Documentation Build

.PHONY: all
all: html pdf

.PHONY: clean
clean: clean-pdf clean-html clean-xml

##########################
# Build PDF Documentation
##########################

.PHONY: pdf
pdf: latex/FreedomMetal.pdf

latex/FreedomMetal.pdf: latex/FreedomMetal.tex
	$(MAKE) -C latex

latex/FreedomMetal.tex: xml/index.xml sphinx/*
	sphinx-build -b latex sphinx latex

.PHONY: clean-pdf
clean-pdf:
	rm -rf latex

###########################
# Build HTML Documentation
###########################

.PHONY: html
html: html/index.html

# Use Sphinx to build HTML from Doxygen XML
html/index.html: xml/index.xml sphinx/*
	sphinx-build -b html sphinx html

.PHONY: clean-html
clean-html:
	rm -rf html/* html/.buildinfo html/.doctrees

##########################
# Build XML Documentation
##########################

xml/index.xml: ../metal/*.h
	cd .. && doxygen

.PHONY: clean-xml
clean-xml:
	rm -rf xml
