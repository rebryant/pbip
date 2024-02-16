#!/usr/bin/python3

import sys
import getopt
import datetime
import writer

# Generate PBIP proof of PHP without CNF input

def usage(name):
    print("%s [-h] [-v VERB] [-e] [-m p|s|c] -n N -o OUTFILE.{pbip,opb}" % name)
    print("  -h           Print this message")
    print("  -e           Use equations rather than ordering constraints")
    print("  -m           Summation mode: pairwise (p), separate pos & neg (s), combined pos & neg (c)")
    print("  -v VERB      Set verbosity level")
    print("  -n N         Set number of holes (pigeons = N+1)")
    print("  -o OUT.ipbip Set output file (PBIP or OPB format)")

verbLevel = 1
holeCount = 8
pigeonCount = 9
pwriter = None
pigeonIds = []
holeIds = []
constraints = []
inputCount = 0
assertionCount = 0
summationCount = 0
useEquations = False
opbOnly = False
sumMode = 'p'

sumModeNames = { 'p' : "pairwise", 's' : "holes/pigeons" , 'c' : "holes+pigeons" }

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

def sum(ids):
    global constraints, summationCount
    con = constraints[ids[0]-1]
    for id in ids[1:]:
        acon = constraints[id-1]
        con = con.add(acon)
    constraints.append(con)
    nid = len(constraints)
    sids = [str(id) for id in ids]
    pwriter.doComment("Constraint #%d.  Sum constraints %s" % (nid, " ".join(sids)))
    pwriter.doSum(con.genOpb(), ids)
    summationCount += 1
    return nid

        
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
    newIds = []
    if sumMode in ['p', 's']:
        if sumMode == 'p':
            pid = mergePigeons()
            hid = mergeHoles()
        else:
            pid = sum(pigeonIds)
            hid = sum(holeIds)
        pcon = constraints[pid-1]
        hcon = constraints[hid-1]
        pwriter.doComment("Combine pigeon and hole constraints to get conflict")
        pwriter.doConflict([pid, hid])
        assertionCount += 1
    elif sumMode == 'c':
        pwriter.doComment("Sum all constraints to get conflict")
        nid = sum(pigeonIds + holeIds)
        if useEquations:
            pwriter.doConflict([nid])
            
    else:
        print("ERROR: Unknown summation mode '%s'" % sumMode)
        sys.exit(1)
    if verbLevel >= 1:
        print("PIGEON: Pseudo-Boolean encoding of PHP UNSAT proof. %s representation.  %s summation" % (rep, sumModeNames[sumMode]))
        print("PIGEON: %d pigeons, %d holes, %d input steps %d assertion steps %d summation steps" 
              % (pigeonCount, holeCount, inputCount, assertionCount, summationCount))


    
def run(name, argList):
    global pwriter
    global verbLevel
    global useEquations
    global opbOnly
    global sumMode
    outName = None
    n = None
    optlist, args = getopt.getopt(argList, "hv:m:en:o:")
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
        elif opt == '-m':
            if val not in ['p', 's', 'c']:
                print("ERROR: Uknown mode '%s'" % val)
                usage(name)
                return
            sumMode = val
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
    
