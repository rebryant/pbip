#!/usr/bin/python3

import sys
import getopt
import datetime
import writer

# Generate PBIP proof of PHP without CNF input

def usage(name):
    print("%s [-h] [-v VERB] [-e] -n N -o OUTFILE.{pbip,opb}" % name)
    print("  -h          Print this message")
    print("  -e          Use equations rather than ordering constraints")
    print("  -v VERB     Set verbosity level")
    print("  -n N        Set number of holes (pigeons = N+1)")
    print("  -o OUT.pbip Set output file (PBIP or OPB format)")

verbLevel = 1
holeCount = 8
pigeonCount = 9
pwriter = None
pigeonIds = []
holeIds = []
constraints = []
inputCount = 0
assertionCount = 0
useEquations = False
opbOnly = False

# Identify variable for hole i, pigeon j (both numbered from 1)
def pij(i,j):
    return (i-1)*pigeonCount + j

def addPigeon(j):
    global pigeonIds, constraints, inputCount
    vars = [pij(i,j) for i in range(1, holeCount+1)]
    if useEquations:
        con = writer.genExactlyOne(vars)
        cname = "Exactly1"
    else:
        con = writer.genAlo(vars)
        cname = "ALO"
    constraints.append(con)
    cid = len(constraints)
    pigeonIds.append(cid)
    pwriter.doComment("Constraint #%d.  %s constraint for pigeon %d" % (cid,cname,j))
    pwriter.doInput(con.genOpb(), [])
    inputCount += 1

def addHole(i):
    global holeIds, constraints, inputCount
    vars = [pij(i,j) for j in range(1, pigeonCount+1)]
    if useEquations:
        con = writer.genExactlyOne(vars)
        cname = "Exactly1"
    else:
        con = writer.genAmo(vars)
        cname = "AMO"
    constraints.append(con)
    cid = len(constraints)
    holeIds.append(cid)
    pwriter.doComment("Constraint #%d.  %s constraint for hole %d" % (cid, cname, i))
    pwriter.doInput(con.genOpb(), [])
    inputCount+= 1

def mergePigeons():
    global constraints, pigeonIds, assertionCount
    while len(pigeonIds) > 1:
        id1 = pigeonIds[0]
        id2 = pigeonIds[1]
        pigeonIds = pigeonIds[2:]
        con1 = constraints[id1-1]
        con2 = constraints[id2-1]
        ncon = con1.add(con2)
        constraints.append(ncon)
        nid = len(constraints)
        pigeonIds.append(nid)
        pwriter.doComment("Constraint #%d.  Combine pigeon constraints %d & %d" % (nid, id1, id2))
        pwriter.doAssert(ncon.genOpb(), [id1, id2])
        assertionCount += 1
    return pigeonIds[-1]

def mergeHoles():
    global constraints, holeIds, assertionCount
    while len(holeIds) > 1:
        id1 = holeIds[0]
        id2 = holeIds[1]
        holeIds = holeIds[2:]
        con1 = constraints[id1-1]
        con2 = constraints[id2-1]
        ncon = con1.add(con2)
        constraints.append(ncon)
        nid = len(constraints)
        holeIds.append(nid)
        pwriter.doComment("Constraint #%d.  Combine hole constraints %d & %d" % (nid, id1, id2))
        pwriter.doAssert(ncon.genOpb(), [id1, id2])
        assertionCount += 1
    return holeIds[-1]

        
def build(n):
    global holeCount, pigeonCount, assertionCount
    holeCount = n
    pigeonCount = n+1
    rep = "Equational" if useEquations else "Constraint"
    pwriter.doComment("Pigeonhole problem.  %s representation. %d pigeons, %d holes" % (rep, pigeonCount, holeCount))
    for j in range(1, pigeonCount+1):
        addPigeon(j)
    for i in range(1, holeCount+1):
        addHole(i)
    if opbOnly:
        if verbLevel >= 1:
            print("PIGEON: Pseudo-Boolean encoding of PHP.  %s representation" % rep)
            print("%d pigeons, %d holes, %d constraints" % (pigeonCount, holeCount, inputCount))
        return
    pid = mergePigeons()
    hid = mergeHoles()
    pcon = constraints[pid-1]
    hcon = constraints[hid-1]
    lcon = pcon.add(hcon)
    pwriter.doComment("Combine pigeon and hole constraints to get conflict")
    pwriter.doAssert(lcon.genOpb(), [pid, hid])
    assertionCount += 1
    if verbLevel >= 1:
        print("PIGEON: Pseudo-Boolean encoding of PHP UNSAT proof. %s representation" % rep)
        print("PIGEON: %d pigeons, %d holes, %d input steps %d assertion steps" 
              % (pigeonCount, holeCount, inputCount, assertionCount))


    
def run(name, argList):
    global pwriter
    global verbLevel
    global useEquations
    global opbOnly
    outName = None
    n = None
    optlist, args = getopt.getopt(argList, "hv:en:o:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbLevel = int(val)
        elif opt == '-e':
            useEquations = True
        elif opt == '-n':
            n = int(val)
        elif opt == '-o':
            outName = val

    if outName is None:
        print("ERROR: Must provide output file name")
        usage(name)
        return

    fields = outName.split('.')
    opbOnly = fields[-1] == 'opb'

    if n is None:
        print("ERROR: Must provide value of n")
        usage(name)
        return

    pwriter = writer.PbipWriter(outName, verbLevel, opbOnly)
    build(n)
    pwriter.finish()

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    
