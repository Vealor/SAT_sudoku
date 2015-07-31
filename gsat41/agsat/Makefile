# This script is in sh
SHELL = /bin/sh

# Compiler for sparc is C++
CC = CC

# Crap to allow compilation on Mips.  Problems:
# (1) The bsd43 includes are incomplete, missing e.g. malloc.h,
#       and sysV includes are missing things such as resource.h,
#       which defines getrusage.
#     Therefore, we include both libraries, with bsd43 higher
#	priority.
# (2) The type size_t is not defined.  This is usually an 
#       unsigned int, so we pass that definition to the compiler.
# (3) The C++ libraries on the Mips are a mess as well, missing
#       various bsd43 functions, such as the resource functions.
#       For now, we always use cc and not CC on the Mips.

MIPSFLAGS = -I/bsd43/usr/include -I/usr/include -Dsize_t=unsigned

# Crap to allow compilation on Iris (Silicon Graphics).  Problems:
# (1) Function usleep not defined.
# (2) C++ not installed.

IRISFLAGS = -DNO_SYSTEM

ARCH = `cputype`

SOURCES = eqn2clause.c ampl2eqn.c gsat2sol.c
HEADERS = proto.h xv_c_types.h
BINARIES = eqn2clause ampl2eqn gsat2sol
SCRIPTS = agsat
AUX = Makefile README cputype

all: eqn2clause ampl2eqn gsat2sol

eqn2clause: eqn2clause.o
	case $(ARCH) in \
	sparc) $(CC) $(CFLAGS) eqn2clause.o -lm -o eqn2clause;; \
	*) cc $(CFLAGS) eqn2clause.o -lm -o eqn2clause;; \
	esac

ampl2eqn: ampl2eqn.o
	case $(ARCH) in \
	sparc) $(CC) $(CFLAGS) ampl2eqn.o -lm -o ampl2eqn;; \
	*) cc $(CFLAGS) ampl2eqn.o -lm -o ampl2eqn;; \
	esac

gsat2sol: gsat2sol.o
	case $(ARCH) in \
	sparc) $(CC) $(CFLAGS) gsat2sol.o -lm -o gsat2sol;; \
	*) cc $(CFLAGS) gsat2sol.o -lm -o gsat2sol;; \
	esac

cc:
	make all 'CC=cc'

.c.o: $(HEADERS)
	case $(ARCH) in \
	mips) cc $(CFLAGS) $(MIPSFLAGS) -c $*.c -O ;; \
	iris) cc $(CFLAGS) $(IRISFLAGS) -c $*.c -O ;; \
	sparc) $(CC) $(CFLAGS) -c $*.c -O ;; \
	*) cc $(CFLAGS) -c $*.c -O ;; \
	esac

lint:	$(SOURCES)
	lint $(SOURCES) -lm -I/usr/include/bsd

clean:
	'rm' -f *.o listing.ps  $(BINARIES)

install: $(SCRIPTS) $(BINARIES)
	strip $(BINARIES)
	cp $(BINARIES) ${HOME}/bin/${ARCH}
	cp $(SCRIPTS) ${HOME}/bin

shar:
	'rm' -f agsat.shar
	shar agsat.shar $(SOURCES) $(HEADERS) $(AUX) $(SCRIPTS) Makefile

listing:
	cpr -o -n $(HEADERS) $(SOURCES) $(SCRIPTS) | postcpr -pland > listing.ps

portrait:
	cpr -o -n -w 85 $(HEADERS) $(SOURCES) $(SCRIPTS) | postcpr > listing.ps
