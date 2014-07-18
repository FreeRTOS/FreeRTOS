# includes append to these:
SUFFIXES =
TESTS =
CLEANFILES =
DISTCLEANFILES =
bin_PROGRAMS =
noinst_HEADERS =
lib_LTLIBRARIES =
man_MANS =
noinst_LTLIBRARIES =
noinst_PROGRAMS =
include_HEADERS =
nobase_include_HEADERS =
check_PROGRAMS =
EXTRA_HEADERS =
BUILT_SOURCES=
EXTRA_DIST=
dist_doc_DATA=

#includes additional rules from aminclude.am
@INC_AMINCLUDE@
DISTCLEANFILES+= aminclude.am

CLEANFILES+= cert.der \
             cert.pem \
             certecc.der \
             certecc.pem \
             certreq.der \
             certreq.pem \
             key.der \
             key.pem \
             ntru-cert.der \
             ntru-cert.pem \
             ntru-key.raw \
             othercert.der \
             othercert.pem \
             pkcs7cert.der \
             pkcs7envelopedData.der \
             pkcs7signedData.der

exampledir = $(docdir)/example
dist_example_DATA=

ACLOCAL_AMFLAGS= -I m4

EXTRA_DIST+= lib/dummy

EXTRA_DIST+= cyassl-ntru.vcproj
EXTRA_DIST+= cyassl.vcproj
EXTRA_DIST+= cyassl.vcxproj
EXTRA_DIST+= cyassl-iphone.xcodeproj/project.pbxproj
EXTRA_DIST+= cyassl-ios.xcodeproj/project.pbxproj
EXTRA_DIST+= cyassl-ntru.sln
EXTRA_DIST+= cyassl.sln
EXTRA_DIST+= cyassl64.sln
EXTRA_DIST+= valgrind-error.sh
EXTRA_DIST+= gencertbuf.pl
EXTRA_DIST+= IDE 

include cyassl/include.am
include certs/include.am
include certs/1024/include.am
include certs/crl/include.am
include doc/include.am
include swig/include.am

include src/include.am
include support/include.am
include ctaocrypt/benchmark/include.am
include ctaocrypt/src/include.am
include ctaocrypt/test/include.am
include examples/client/include.am
include examples/server/include.am
include examples/echoclient/include.am
include examples/echoserver/include.am
include testsuite/include.am
include tests/include.am
include sslSniffer/sslSnifferTest/include.am
include rpm/include.am
include mqx/ctaocrypt_test/Sources/include.am
include mqx/cyassl/include.am
include mqx/cyassl_client/Sources/include.am
include mqx/util_lib/Sources/include.am
include mplabx/include.am
include mplabx/ctaocrypt_benchmark.X/nbproject/include.am
include mplabx/ctaocrypt_test.X/nbproject/include.am
include mplabx/cyassl.X/nbproject/include.am
include mcapi/include.am
include mcapi/ctaocrypt_mcapi.X/nbproject/include.am
include mcapi/ctaocrypt_test.X/nbproject/include.am
include mcapi/cyassl.X/nbproject/include.am
include mcapi/zlib.X/nbproject/include.am

if USE_VALGRIND
TESTS_ENVIRONMENT=./valgrind-error.sh
endif

TEST_EXTENSIONS=.test
TESTS += $(check_PROGRAMS)
test: check
tests/unit.log: testsuite/testsuite.log

DISTCLEANFILES+= cyassl-config
# fips files shouldn't be left after make distclean
DISTCLEANFILES+= ctaocrypt/src/fips.c
DISTCLEANFILES+= ctaocrypt/src/fips_test.c

maintainer-clean-local:
	-rm Makefile.in
	-rm aclocal.m4
	-rm build-aux/compile
	-rm build-aux/config.guess
	-rm build-aux/config.sub
	-rm build-aux/depcomp
	-rm build-aux/install-sh
	-rm build-aux/ltmain.sh
	-rm build-aux/missing
	-rm cyassl-config
	-rmdir build-aux
	-rm configure
	-rm config.log
	-rm config.status
	-rm config.in
	-rm m4/libtool.m4
	-rm m4/ltoptions.m4
	-rm m4/ltsugar.m4
	-rm m4/ltversion.m4
	-rm m4/lt~obsolete.m4
	-rm support/cyassl.pc
	find . -type f -name '*~' -exec rm -f '{}' \;
	-rm -f @PACKAGE@-*.tar.gz
	-rm -f @PACKAGE@-*.rpm

# !!!! first line of rule has to start with a hard (real) tab, not spaces
egs:
	$(MAKE) examples/client/client; \
	$(MAKE) examples/echoclient/echoclient;\
	$(MAKE) examples/server/server; \
	$(MAKE) examples/echoserver/echoserver;

ctc:
	$(MAKE) ctaocrypt/test/testctaocrypt; \
	$(MAKE) ctaocrypt/benchmark/benchmark; 

install-exec-local:	install-generic-config

install-generic-config:
	$(mkinstalldirs) $(DESTDIR)$(bindir)
	$(INSTALL_SCRIPT) @GENERIC_CONFIG@ $(DESTDIR)$(bindir)

uninstall-local:
	-rm -f $(DESTDIR)$(bindir)/@GENERIC_CONFIG@

merge-clean:
	@find ./ | $(GREP) \.gcda | xargs rm -f
	@find ./ | $(GREP) \.gcno | xargs rm -f
	@find ./ | $(GREP) \.gz | xargs rm -f
	@find ./ | $(GREP) \.orig | xargs rm -f
	@find ./ | $(GREP) \.rej | xargs rm -f
	@find ./ | $(GREP) \.rpm | xargs rm -f
	@find ./ | $(GREP) \.THIS | xargs rm -f
	@find ./ | $(GREP) \.OTHER | xargs rm -f
	@find ./ | $(GREP) \.BASE | xargs rm -f
	@find ./ | $(GREP) \~$$ | xargs rm -f
