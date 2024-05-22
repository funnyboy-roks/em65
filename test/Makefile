# Commands taken from https://github.com/therealjacinto/6502-ben-computer/blob/master/scripts/buildmanually.sh

build/test: build build/test.o build/startup.o vlink.cmd
	vlink -b rawbin1 -Cvbcc -Tvlink.cmd build/startup.o build/test.o -o build/test

build/startup.o: build startup.s
	vasm6502_oldstyle startup.s -o build/startup.o -Fvobj -quiet -nowarn=62

build/test.o: build build/test.s
	vasm6502_oldstyle build/test.s -o build/test.o -Fvobj -quiet -nowarn=62 -opt-branch

build/test.s: test.c
	vbcc6502 test.c -o=build/test.s -c99 -quiet -avoid-bank-switch -O=7615

build:
	mkdir build/

