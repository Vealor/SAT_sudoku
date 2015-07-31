# This script is in sh
SHELL = /bin/sh

# The script cputype must be executable, and should return
# one of sparc, mips, or mips.sgi, or mips.irix5

ARCH = `cputype`

# Stuff to allow compilation on Mips.  Problems:
# (1) The bsd43 includes are incomplete, missing e.g. malloc.h,
#       and sysV includes are missing things such as resource.h,
#       which defines getrusage.
#     Therefore, we include both libraries, with bsd43 higher
#	priority.
# (2) The type size_t is not defined.  This is usually an 
#       unsigned int, so we pass that definition to the compiler.
# (3) The C++ libraries on the Mips are a mess as well, missing
#       various bsd43 functions, such as the resource functions.
MIPSFLAGS = -I/bsd43/usr/include -I/usr/include -Dsize_t=unsigned -DMips=1 -O2

# Stuff to allow compilation on SGI (Silicon Graphics).  Problems:
# (1) Function usleep not defined
# (2) Can't use -non_shared option with X libraries
#SGIFLAGS = -DNO_USLEEP -O3 -non_shared
SGIFLAGS = -DNO_USLEEP
SGIXFLAGS = -O2 -DNO_USLEEP

# Stuff to allow compilation on Sparc
SPARCFLAGS = -O2

# Stuff for compilation on other machines
OTHERCFLAGS = -02

############## end of machine specific flags ########################

# Options:
CFLAGS =
#   Profile code:
# CFLAGS = -p
#   Don't include self-checks in code:
# CFLAGS = -DNOCHECK
#   Don't include walk option:
# CFLAGS = -DNOWALK

############## end of general options ###############################

LIB    =   -lm
XLIB   =   -lXaw -lXmu -lXt -lXext -lX11

XSOURCES = xgsat.c
XHEADERS = xgsat.h
SOURCES = gsat.c anneal.c urand.c  utils.c globals.c
HEADERS = gsat.h anneal.h urand.h utils.h proto.h adjust_bucket.h
OBJECTS = urand.o gsat.o globals.o anneal.o utils.o
AUX = Makefile GSAT_USERS_GUIDE cputype interp gsat.1 ex.in ex.wff agsat Gsat


gsat: $(SOURCES) $(HEADERS)
	case $(ARCH) in \
	mips) cc $(CFLAGS) $(MIPSFLAGS) $(SOURCES)  $(LIB) -o gsat;; \
	SGI | mips.sgi | mips.irix5 ) cc $(CFLAGS) $(SGIFLAGS) $(SOURCES) $(LIB) -o gsat;; \
	sparc) cc $(CFLAGS) $(SPARCFLAGS) $(SOURCES) $(LIB) -o gsat;; \
	*) cc $(CFLAGS) $(SOURCES) $(LIB) -o gsat;; \
	esac

xgsat: $(SOURCES) $(HEADERS) $(XSOURCES) $(XHEADERS)
	case $(ARCH) in \
	mips) cc $(CFLAGS) $(MIPSFLAGS) -DXGSAT $(SOURCES) $(XSOURCES) $(LIB) $(XLIB) -o xgsat;; \
	SGI | mips.sgi | mips.irix5 ) cc $(CFLAGS) $(SGIXFLAGS) -DXGSAT $(SOURCES) $(XSOURCES) $(LIB) $(XLIB) -o xgsat;; \
	sparc) cc $(CFLAGS) $(SPARCFLAGS) -DXGSAT $(SOURCES) $(XSOURCES) $(LIB) $(XLIB) -o xgsat;; \
	*) cc $(CFLAGS) -DXGSAT $(SOURCES) $(XSOURCES) $(LIB) $(XLIB) -o xgsat;; \
	esac

fact2sat: fact2sat.c
	cc fact2sat.c -o fact2sat

clean:
	'rm' -f gsat xgsat *.o listing.ps

install: gsat
	strip gsat
	cp gsat ${HOME}/bin/${ARCH}/gsat

shar:
	'rm' -f gsat.shar
	shar gsat.shar $(SOURCES) $(HEADERS) $(AUX) $(XSOURCES) $(XHEADERS)

tar:
	'rm' -f gsat.tar.Z*
	tar cevof gsat.tar $(SOURCES) $(HEADERS) $(AUX) $(XSOURCES) $(XHEADERS)
	compress gsat.tar
	uuencode gsat.tar.Z gsat.tar.Z > gsat.tar.Z.uu

listing:
	cpr -o -n $(HEADERS) $(XHEADERS) $(SOURCES) $(XSOURCES) | postcpr -pland > listing.ps

