#!/usr/bin/python3

import sys


# Generate contradictory formula using majority constraint

n = 5
m = 3

def gen_conflict(outfile):
    outfile.write("* PBIP Declaration that n=%d inputs sum to value >= m=%d\n" % (n,m))
    outfile.write("i ")
    for i in range(1,n+1):
        outfile.write("1 x%d " % i)
    outfile.write(">= %d ;\n" % m)
    outfile.write("* PBIP Declaration that n=%d inputs sum to value <  m=%d\n" % (n,m))
    outfile.write("i ")
    for i in range(1,n+1):
        outfile.write("1 x%d " % i)
    outfile.write("<  %d ;\n" % m)
    outfile.write("* Prove conflict\n")
    outfile.write("a >= 1; 1 2\n")

def run(name, args):
    global n, m
    if len(args) < 1 or len(args) > 2:
        sys.stderr.write("Usage: %s n [m]\n" % name)
        sys.exit(1)
    n = int(args[0])
    if len(args) == 2:
        m = int(args[1])
    else:
        m = (n//2)+1
    gen_conflict(sys.stdout)
           
                   
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
            
