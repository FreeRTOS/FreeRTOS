# abbu

ASLMODADD=	MAIN_ASLTS
AMLMOD= extra extra_aslts
COLL= ../..

ADD_ASLFLAGS=-vx 6142 #illegal forward reference
ADD_ASLFLAGS+=-vx 6152 #recursive method call
ADD_ASLFLAGS+=-vx 6163 #illegal reference in method

TOP= $(COLL)/../../..
include $(COLL)/Makefile.install
