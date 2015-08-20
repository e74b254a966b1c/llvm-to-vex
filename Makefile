LEVEL = ../../..
CPPFLAGS += -I/home/andrei/projects/fac/licenta/valgrind-3.10.1/VEX/pub/ -I/home/andrei/projects/fac/licenta/valgrind-3.10.1/VEX/priv/
LIBRARYNAME = LLVMtoVEX
LOADABLE_MODULE = 1
USEDLIBS = vex-amd64-linux.a


include $(LEVEL)/Makefile.common
