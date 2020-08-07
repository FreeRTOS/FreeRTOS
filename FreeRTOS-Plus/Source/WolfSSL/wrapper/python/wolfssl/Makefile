# Makefile
#
# Copyright (C) 2006-2020 wolfSSL Inc.
#
# This file is part of wolfSSL.
#
# wolfSSL is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# wolfSSL is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
#/

.PHONY : all clean clean-test clean-build clean-pyc install test check upload

# builds the module
all :
	python ./setup.py build

#builds and installs the module
install : all
	python ./setup.py install

## removes all build, test, coverage and Python artifacts
clean : clean-test clean-build clean-pyc

## removes test and coverage artifacts
clean-test :
	rm -rf .coverage .tox/ htmlcov/

## removes build artifacts
clean-build :
	rm -rf build/ dist/ .eggs/
	find . -name '*.egg-info' -exec rm -rf {} +
	find . -name '*.egg' -exec rm -v {} +

## removes Python file artifacts
clean-pyc :
	find src test -name '__pycache__' -exec rm -rf {} +
	find src test -name '*.pyc' -exec rm -f {} +
	find src test -name '*.pyo' -exec rm -f {} +

# runs unit tests
check : test

test : clean-pyc
	tox

# publishes module at pypi
upload : test
	python ./setup.py sdist upload
