CPP=gcc
CXX=g++
CFLAGS = -O3 -Wno-nullability-completeness	
CXFLAGS = $(CFLAGS) -std=c++20

BUDDY = ~/pb-benchmarking/proof-checkers/tbuddy/buddy
INC = -I $(BUDDY)/include
LIB = $(BUDDY)/lib/tbuddy.a

all: report.o ipbip-hints pbip-check

ipbip-hints:
	$(CXX) $(CXFLAGS) ipbip_hints.cpp report.o -o ./ipbip_hints

report.o: report.c report.h
	$(CPP) $(CFLAGS) -c report.c

pbip-check: pbip-check.cpp report.o
	$(CXX) $(CXFLAGS) $(INC) -o pbip-check pbip-check.cpp report.o $(LIB)

main:
	ipbip-hints

clean:
	rm -f *~
	rm -f ipbip_hints pbip-check
