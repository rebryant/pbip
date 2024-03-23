#!/usr/bin/python3

import sys
import getopt
import datetime

import bdd
import solver
import pbip

def usage(name):
    print("Usage %s: [-h] [-v VERB] [-b] [-r] -i INFILE.ipbip -c OUTFILE.cnf -o OUTFILE.pbib")
    print("  -h              Print this message")
    print("  -v VERB         Set verbosity level")
    print("  -b              Pure BDD mode.  Don't make use of clausal representations")
    print("  -r              Rename variables to improve variable ordering")
    print("  -i INFILE.ipbip Input PBIP file (with unhinted inputs)")
    print("  -o OUTFILE.pbip Output PBIP file (with hints)")
    print("  -c OUTFILE.cnf  Output CNF file")


# Code for generating CNF, order, and schedule files
class WriterException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Writer Exception: " + str(self.value)


# Generic writer
class Writer:
    outfile = None
    suffix = None
    verbLevel = 1
    variableCount = 0
    isNull = False

    def __init__(self, fname, verbLevel = 1, isNull = False):
        self.variableCount = 0
        self.verbLevel = verbLevel
        self.isNull = isNull
        if isNull:
            return
        try:
            self.outfile = open(fname, 'w')
        except:
            print("Couldn't open file '%s'. Aborting" % fname)
            sys.exit(1)

    def trim(self, line):
        while len(line) > 0 and line[-1] == '\n':
            line = line[:-1]
        return line

    def show(self, line):
        if self.isNull:
            return
        line = self.trim(line)
        if self.verbLevel >= 3:
            print(line)
        if self.outfile is not None:
            self.outfile.write(line + '\n')

    def finish(self):
        if self.isNull:
            return
        if self.outfile is None:
            return
        self.outfile.close()
        self.outfile = None

# Creating CNF
class CnfWriter(Writer):
    clauseCount = 0
    # Set of tuples (T/F, item)
    # Boolean T for clause F for comment
    # item: list of literals for clause, string for comment
    items = []

    def __init__(self, fname, verbLevel = 1):
        Writer.__init__(self, fname, verbLevel = verbLevel)
        self.clauseCount = 0
        self.items = []

    # With CNF, must accumulate all of the clauses, since the file header
    # requires providing the number of clauses.

    def doComment(self, line):
        self.items.append((False, line))

    def doClause(self, literals):
        for lit in literals:
            var = abs(lit)
            self.variableCount = max(var, self.variableCount)
        sliterals = sorted(literals, key = lambda lit : abs(lit))
        self.items.append((True, sliterals))
        self.clauseCount += 1
        return self.clauseCount

    # Rename variables to order them according to least variable in each clause
    def remapVariables(self, inputCount):
        # Associate each non-input variable with the lowest-numbered variable for which both occur in some clause
        varBucket = {}
        inputSet = set(range(1,inputCount+1))
        for (isClause, element) in self.items:
            if not isClause:
                continue
            vars = [abs(lit) for lit in element]
            mvar = min(vars)
            for var in vars:
                if var in inputSet:
                    continue
                elif var in varBucket:
                    varBucket[var] = min(mvar, varBucket[var])
                else:
                    varBucket[var] = mvar
        # Generate list of variables associated with each minimum variable
        mvarMap = { mvar : [] for mvar in inputSet } 
        for (var, mvar) in varBucket.items():
            mvarMap[mvar].append(var)
        # Renumber variables according to positions
        remap = { mvar : mvar for mvar in inputSet }
        nextVar = len(inputSet) + 1
        for mvar in sorted(inputSet):
            for var in sorted(mvarMap[mvar]):
                remap[var] = nextVar
                nextVar += 1
        # Rewrite the clauses
        nitems = []
        for (isClause, element) in self.items:
            if not isClause:
                nitems.append((isClause,element))
                continue
            nclause = [remap[abs(lit)] * (-1 if lit < 0 else 1) for lit in element]
            nitems.append((True, nclause))
        self.items = nitems

    def finish(self):
        if self.isNull:
            return
        if self.outfile is None:
            return
        self.show("p cnf %d %d" % (self.variableCount, self.clauseCount))
        for (isClause,element) in self.items:
            if isClause:
                slist = [str(lit) for lit in element] + ["0"]
                line = " ".join(slist)
            else:
                line = "c " + element
            self.show(line)
        self.outfile.close()
        self.outfile = None

# Creating PBIP
class PbipWriter(Writer):
    commandCount = 0
    
    def __init__(self, fname, verbLevel = False):
        Writer.__init__(self, fname, verbLevel=verbLevel)
        self.commandCount = 0

    def doComment(self, line):
        self.show("* " + line)

    def doCommand(self, cmd, opbstring, hints):
        shints = []
        for hint in hints:
            if type(hint) == type([0]):
                slist = [str(h) for h in hint]
                if len(hint) == 2:
                    h = hint[1]
                    slist[1] = ("x" + slist[1]) if h >= 0 else ("~x" + slist[1][1:])
                shint = '[' + " ".join(slist) + ']'
            else:
                shint = str(hint)
            shints.append(shint)
        self.show("%s %s ; %s" % (cmd, opbstring, " ".join(shints)))

    def doInput(self, opbstring, hints):
        self.doCommand('i', opbstring, hints)

class CnfGenerator:
    verbLevel = 1
    bddOnly = False
    rename = True
    cwriter = None
    preader = None
    # Information from PBIP file
    commandList = []
    constraintList = []
    hintList = []
    commentsList = []
    prover = None
    manager = None
    inputVariableCount = 0
    # Map from tuple representation of clause to its ID
    clauseMap = {}
    
    def __init__(self, cnfName, inPbipName, outPbipName, verbLevel, bddOnly, rename):
        self.verbLevel = verbLevel
        self.bddOnly = bddOnly
        self.rename = rename
        self.cwriter = CnfWriter(cnfName, verbLevel)
        self.preader = pbip.PbipReader(inPbipName, verbLevel)
        self.pwriter = PbipWriter(outPbipName, verbLevel)
        self.inputVariableCount = 0
        self.commandList = []
        self.constraintList = []
        self.hintList = []
        self.clauseMap = {}
        while True:
            cmd, clist, hints, comments = self.preader.readLine()
            if cmd == "":
                break
            self.commandList.append(cmd)
            self.constraintList.append(clist)
            self.hintList.append(hints)
            self.commentsList.append(comments)
            for con in clist:
                if len(con.nz) > 0:
                    mvar = max(con.nz.keys())
                    self.inputVariableCount = max(self.inputVariableCount, mvar)
        if self.verbLevel >= 1:
            print("CNFGEN: Read %d constraints.  Found %d input variables" % (len(self.commandList), self.inputVariableCount))
        # Set up prover, but disable LRAT output
        self.prover = solver.Prover(fname="", writer = solver.StdOutWriter(), verbLevel = verbLevel, doLrat = False)
        self.manager = bdd.Manager(prover = self.prover, nextNodeId = self.inputVariableCount+1, verbLevel = verbLevel)
        for id in range(1, self.inputVariableCount+1):
            var = self.manager.newVariable(name = "V%d" % id)
        self.varMap = { var.id : var for var in self.manager.variables }
        self.levelMap = { var.id : var.level for var in self.manager.variables }
    
    def run(self):
        for cid in range(1, len(self.commandList)+1):
            self.processCommand(cid)
        if self.verbLevel >= 1:
            print("CNFGEN: Problem variables = %d" % self.inputVariableCount)
            print("CNFGEN: CNF variables = %d CNF Clauses = %d" %(self.cwriter.variableCount, self.cwriter.clauseCount))
            
        if self.rename:
            self.cwriter.remapVariables(self.inputVariableCount)
        self.cwriter.finish()
        self.preader.finish()
        self.pwriter.finish()


    def processCommand(self, cid):
        cmd = self.commandList[cid-1]
        clist = self.constraintList[cid-1]
        hlist = self.hintList[cid-1]
        comments = self.commentsList[cid-1]
        if len(clist) == 1:
            opbstring = clist[0].opbString(coefficientNormalized = True)
        else:
            opbstring = clist[0].opbString(forceEquality = True, coefficientNormalized = True)
        for com in comments:
            self.pwriter.doComment(com)
        self.pwriter.doComment("Constraint #%d" % cid)
        if cmd == 'i':
            self.cwriter.doComment("Clauses for input constraint #%d: %s" % (cid, opbstring))
            clauses = None
            if not self.bddOnly and len(clist) == 1:
                tclause = clist[0].getClause()
                if tclause is not None:
                    clauses = [tclause]
            if clauses is None:
                for con in clist:
                    con.buildBdd(self)
                if len(clist) == 1:
                    root = clist[0].root
                else:
                    root = self.manager.applyAnd(clist[0].root, clist[1].root)
                clauses = self.manager.generateClauses(root, up=False)
            hlist = []
            for clause in clauses:
                tclause = tuple(clause)
                if tclause in self.clauseMap:
                    id = self.clauseMap[tclause]
                else:
                    id = self.cwriter.doClause(clause)
                    self.clauseMap[tclause] = id
                hlist.append(id)
            self.pwriter.doInput(opbstring, hlist)
        else:
            if cmd == 'k':
                cmd = 'u'
            self.pwriter.doCommand(cmd, opbstring, hlist)

def run(name, argList):
    verbLevel = 1
    bddOnly = False
    rename = False
    cnfName = ""
    inPbipName = ""
    outPbipName = ""

    optlist, args = getopt.getopt(argList, "hbrv:c:i:o:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-b':
            bddOnly = True
        elif opt == '-r':
            rename = True
        elif opt == '-v':
            verbLevel = int(val)
        elif opt == '-i':
            inPbipName = val
        elif opt == '-c':
            cnfName = val
        elif opt == '-o':
            outPbipName = val
        else:
            print("Unknown option '%s'" % opt)
            usage(name)
            return
    if cnfName == "":
        print("ERROR: Must give name of CNF file")
        usage(name)
        return
    if inPbipName == "":
        print("ERROR: Must give name of input PBIP file")
        usage(name)
        return
    if outPbipName == "":
        print("ERROR: Must give name of output PBIP file")
        usage(name)
        return

    start = datetime.datetime.now()
    generator = CnfGenerator(cnfName, inPbipName, outPbipName, verbLevel, bddOnly, rename)
    generator.run()
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    if verbLevel > 0:
        print("CNFGEN: Generation of CNF constraints from PBIP elapsed seconds: %.2f" % (seconds))


if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
            

        

        
