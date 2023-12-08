#!/usr/local/bin/python3

from pysat import card
import sys
import getopt


# Generate contradictory formula using majority constraint

def usage(name):
    print("Usage: %s [-h] -n NVAR [-m THRESH] [-e ENC] -p PFILE -c CFILE" % name)
    print("  -h        Print this message")
    print("  -n NVAR   Set number of variables")
    print("  -m THRESH Set threshold (default = n//2+1)")
    print("  -e ENC    Specify encoding method.  Choices:")
    print("              seqcounter, sortnetwrk, cardnetwrk")
    print("              totalizer, mtotalizer, kmtotalizer")
    print("  -p PFILE  Specify output PBIP file")
    print("  -c CFILE  Specify output CNF file")
    

encodings = { 
    "seqcounter" : card.EncType.seqcounter,
    "sortnetwrk"  : card.EncType.sortnetwrk,
    "cardnetwrk"  : card.EncType.cardnetwrk,
    "totalizer"    : card.EncType.totalizer,
    "mtotalizer"    : card.EncType.mtotalizer,
    "kmtotalizer"    : card.EncType.kmtotalizer,
}

def gen_conflict(n, m, encoding, pbipFile, cnfFile):
    maxvar = n
    clauses = []
    vars = list(range(1,n+1))
    cnf = card.CardEnc.atleast(vars, bound = m, top_id = maxvar+1, encoding = encoding)
    clauses = cnf.clauses
    startClause = 1
    for clause in cnf.clauses:
        for lit in clause:
            var = abs(lit)
        if var > maxvar:
            maxvar = var
    pbipFile.write("* PBIP Declaration that %d inputs sum to value >= %d\n" % (n,m))
    pbipFile.write("i ")
    for i in vars:
        pbipFile.write("1 x%d " % i)
    pbipFile.write(">= %d ;" % m)
    for h in range(startClause, len(clauses)+1):
         pbipFile.write(" %d" % h)
    pbipFile.write("\n")
         
    startClause = len(clauses)+1
    cnf = card.CardEnc.atmost(vars, bound = m-1, top_id = maxvar+1, encoding = encoding)
    clauses = clauses + cnf.clauses
    pbipFile.write("* PBIP Declaration that %d inputs sum to value <= %d\n" % (n,m-1))
    pbipFile.write("i ")
    for i in range(1,n+1):
        pbipFile.write("1 x%d " % i)
    pbipFile.write("<=  %d ;" % (m-1))
    for h in range(startClause, len(clauses)+1):
        pbipFile.write(" %d " % h)
    pbipFile.write("\n")
    pbipFile.write("* Prove conflict\n")
    pbipFile.write("a >= 1; 1 2\n")
    for clause in cnf.clauses:
        for lit in clause:
            var = abs(lit)
        if var > maxvar:
            maxvar = var
    cnfFile.write("c Conflicting constraints for n=%d, m= %d\n" % (m,n))
    cnfFile.write("p cnf %d %d\n" % (maxvar, len(clauses)))
    for clause in clauses:
        ilits = [str(lit) for lit in clause]
        cnfFile.write("%s 0\n" % " ".join(ilits))
    pbipFile.close()
    cnfFile.close()
    print("Wrote CNF file with %d variables and %d clauses" % (maxvar, len(clauses)))

def run(name, argList):
    n = None
    m = None
    encoding = encodings["seqcounter"]
    pbipName = None
    cnfName = None
    optlist, args = getopt.getopt(argList, "hn:m:e:p:c:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-n':
            n = int(val)
        elif opt == '-m':
            m = int(val)
        elif opt == '-e':
            if val not in encodings:
                print("Unknown encoding type '%s'" % val)
                usage(name)
                return
            encoding = encodings[val]
        elif opt == '-p':
            pbipName = val
        elif opt == '-c':
            cnfName = val
        else:
            print("Unknown option '%s'" % opt)
            usage(name)
            return
    if n is None:
        print("Need value for number of variables")
        usage(name)
        return
    if m is None:
        m = n//2+1
    if pbipName is None:
        print("Require PBIP file name")
        usage(name)
        return
    try:
        pfile = open(pbipName, "w")
    except:
        print("Couldn't open PBIP file '%s'" % pbipName)
        return
    try:
        cfile = open(cnfName, "w")
    except:
        print("Couldn't open CNF file '%s'" % cnfName)
        return
    gen_conflict(n, m, encoding, pfile, cfile)
           
                   
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
            
