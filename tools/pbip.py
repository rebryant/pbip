# Tools for working with PBIP proofs.
# PBIP that a set of Pseudo-Boolean (PB) constraints is unsatisfiable
# via a sequence of implication steps
# The tool pbip_check.py converts a PBIP proof into a clausal proof in LRAT format
# The tool pbip_cnf.py generates a CNF file containing clausal representation of the input PB constraints
# The tool pbip_order.py generates a permutation of the CNF file to ensure that all
# problem variables occur first in the file.


import solver
import bdd
import pseudoboolean
import resolver


def trim(s):
    while len(s) > 0 and s[0] in ' \t':
        s = s[1:]
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s

def uncomment(s):
    while s[0] in "* ":
        s = s[1:]
    return s

# Return list of constraints from line of OPB
class PbipException(Exception):
    form = ""
    line = ""

    def __init__(self, line, msg):
        self.form = "PBIP error"
        if line == "":
            self.msg = msg
        else:
            self.msg = "line = '%s', %s" % (line, msg)

    def __str__(self):
        m = self.form
        if self.msg != "":
            m += " (" + self.msg + ")"
        return m

# Read string representation of OPB constraint
# Return list of Constraint objects
# List contains one constraint for operations <, <=, >, >=
# and a pair of constraints for =
def parseOpb(line):
    fields = line.split()
    # Get rid of trailing semicolon
    if len(fields) == 0:
        raise PbipException(line, "Empty")
    if fields[-1] == ';':
        fields = fields[:-1]
    elif fields[-1][-1] == ';':
        fields[-1] = fields[-1][:-1]
    if len(fields) < 2 or len(fields) % 2 != 0:
        raise PbipException(line, "Invalid number of fields")
    try:
        cval = int(fields[-1])
    except:
        raise PbipException(line, "Invalid constant %s" % fields[-1])
    rel = fields[-2]
    if rel not in ['<', '<=', '=', '>=', '>']:
        raise PbipException(line, "Invalid relation %s" % rel)
    cfields = fields[:-2]
    coeffs = []
    vars = []
    for i in range(len(cfields)//2):
        scoeff = cfields[2*i]
        try:
            coeff = int(scoeff)
        except:
            raise PbipException(line, "Invalid coefficient %s" % scoeff)
        svar = cfields[2*i+1]
        if svar[0] in '!~':
            cval -= coeff
            coeff = -coeff
            svar = svar[1:]
        if svar[0] == 'x':
            try:
                var = int(svar[1:])
            except:
                raise PbipException(line, "Invalid term %s" % svar)
        else:
            raise PbipException(line, "Invalid term %s" % svar)
        coeffs.append(coeff)
        vars.append(var)
    # Normalize
    if rel == '<':
        rel = '<='
        cval -= 1
    if rel == '>':
        rel = '>='
        cval += 1
    if rel == '<=':
        rel = '>='
        cval = -cval
        coeffs = [-c for c in coeffs]
    nz = { v : c for v,c in zip(vars,coeffs) }
    con1 = pseudoboolean.Constraint(len(nz), cval)
    con1.setNz(nz)
    if rel == '>=':
        return (con1,)
    else:
        cval = -cval
        coeffs = [-c for c in coeffs]
        nz = { v : c for v,c in zip(vars,coeffs) }
        con2 = pseudoboolean.Constraint(len(nz), cval)
        con2.setNz(nz)
        return (con1, con2)
    
class PbipReader:
    fname = ""
    lineCount = 0
    infile = None
    verbLevel = 1
    
    def __init__(self, fname, verbLevel):
        try:
            self.fname = fname
            self.infile = open(fname, 'r')
        except:
            print("Can't open input file %s" % fname)
            raise PbipException("", "Invalid input file")
        self.lineCount = 0
        self.verbLevel = verbLevel

    def finish(self):
        if self.infile is not None:
            self.infile.close()
            self.infile = None
        

    # Return (command, list of PB constraints, list of hints, list of preceding comments)
    def readLine(self):
        command = ""
        clist = []
        hlist = []
        comlist = []
        for line in self.infile:
            self.lineCount += 1
            line = trim(line)
            if len(line) == 0:
                continue
            if line[0] == '*':
                comlist.append(uncomment(line))
                continue
            command = line[0]
            if command not in ['i', 'a', 'k', 'A']:
                raise PbipException("", "File %s Line %d: Invalid command '%s'" % (self.fname, self.lineCount, command))
            cline  = trim(line[1:])
            pos = cline.find(';')
            if pos < 0:
                raise PbipException("", "File %s Line %d: No semicolon found" % (self.fname, self.lineCount))
            cstring = cline[:pos]
            hstring = cline[pos+1:]
            try:
                clist = parseOpb(cstring)
            except PbipException as ex:
                raise PbipException("", "File %s Line %d: %s" % (self.fname, self.lineCount, str(ex)))
            hfields = hstring.split()
            try:
                hlist = [int(f) for f in hfields]
            except:
                raise PbipException("", "File %s Line %d: Couldn't parse hint list '%s'" % (self.fname, self.lineCount, hstring))
            break
        if self.verbLevel >= 3:
            print("PBIP: Read PBIP line #%d.  Command = %s" % (self.lineCount, command))
            print("PBIP:  Constraints:")
            for con in clist:
                print("PBIP:     %s" % str(con))
            if len(hlist) > 0:
                print("PBIP:   Hints: %s" % str(hlist))
        return (command, clist, hlist, comlist)

class StepType:
    input, assertion, oldCF, currentCF, currentTarget = range(5)

    def implicationOK(self, st):
        return st in [self.input, self.assertion]

    def cfImplicationOK(self, st):
        return st in [self.input, self.assertion, self.currentCF]

class Pbip:
    verbLevel = 1
    valid = True
    creader = None
    preader = None
    permuter = None
    # Set of constraints
    cset = None
    # Array mapping from PBIP file constraints to cset constraints (offset by 1)
    # Each is a list containing Ids of 1 or 2 constraints
    constraintList = []
    # Trusted BDD representations of constraints
    # Each TBDD is pair (root, validation)

    # BDDs for counterfactual assertions are for negation of constraint
    # and their validation is of the form u ==> u_T, were u_T is the
    # extension variable for the target constraint
    tbddList = []
    # Each constraint carries a type that determines how it can be used as a hint
    stepTypeList = []
    # Verifier can work in either implication or counterfactual mode
    counterfactualMode = False
    # When in counterfactual mode, keep track of target root
    targetId = None

    # Enable use as constraint system
    prover = None
    manager = None
    litMap = {}
    varMap = {}
    levelMap = {}
    
    def __init__(self, cnfName, pbipName, lratName, verbLevel):
        self.verbLevel = verbLevel
        self.valid = True
        self.creader = solver.CnfReader(cnfName, verbLevel)
        self.preader = PbipReader(pbipName, verbLevel)
        self.cset = pseudoboolean.ConstraintSet()
        self.constraintList = []
        self.tbddList = []
        self.stepTypeList = []
        self.counterfactualMode = False
        self.targetId = None
        lratName = None if lratName == "" else lratName
        self.prover = solver.Prover(fname=lratName, writer = solver.StdOutWriter(), verbLevel = verbLevel, doLrat = True)
        # Print input clauses
        clauseCount = 0
        for clause in self.creader.clauses:
            clauseCount += 1
            self.prover.createClause(clause, [], "Input clause %d" % clauseCount, isInput = True)
        self.prover.inputDone()
        self.manager = bdd.Manager(prover = self.prover, nextNodeId = self.creader.nvar+1, verbLevel = verbLevel)
        self.litMap = {}
        for level in range(1, self.creader.nvar+1):
            inputId = level
            var = self.manager.newVariable(name = "V%d" % inputId, id = inputId)
            t = self.manager.literal(var, 1)
            self.litMap[ inputId] = t
            e = self.manager.literal(var, 0)
            self.litMap[-inputId] = e
        self.varMap = { var.id : var for var in self.manager.variables }
        self.levelMap = { var.id : var.level for var in self.manager.variables }

    def doStep(self):
        command, clist, hlist, comlist = self.preader.readLine()
        if command == '':
            return True
        st = None
        nclist = clist
        negated = False

        # Little hack.  Dynamically change command from 'A' to 'a' if all hints are acceptable as implication mode hints
        if command == 'A' and self.assertionHintsOk(hlist):
            command = 'a'
            if (self.verbLevel >= 1):
                pid = len(self.constraintList) + 1
                print("WARNING: Converting command type of #%d from 'A' to 'a'" % pid)

        if command in ['a', 'i']:
## NEW: Allow implication assertions in CF mode
#            if self.counterfactualMode:
#                raise PbipException("", "Can't have command of type '%s' while in counterfactual mode" % command)
            for con in clist:
                con.buildBdd(self)
            st = StepType.assertion if command == 'a' else StepType.input
        elif command == 'k':
            if self.counterfactualMode:
                raise PbipException("", "Can't have command of type '%s' while already in counterfactual mode" % command)
            for con in clist:
                con.buildBdd(self)
            st = StepType.currentTarget
        elif command == 'A':
            if not self.counterfactualMode:
                raise PbipException("", "Can't have command of type '%s' when in implication mode" % command)
            nclist = [con.negate() for con in clist]
            for ncon in nclist:
                ncon.buildBdd(self)
            negated = True
            st = StepType.currentCF
        self.constraintList.append(nclist)
        self.stepTypeList.append(st)
        if len(nclist) == 2:
            nroot = self.manager.applyOr(nclist[0].root, nclist[1].root) if negated else self.manager.applyAnd(nclist[0].root, nclist[1].root)
        else:
            nroot = nclist[0].root
        self.tbddList.append((nroot,None))
        pid = len(self.constraintList)
        done = False
        for com in comlist:
            self.prover.comment(com)
        if command == 'i':
            self.doInput(pid, hlist)
            done = nroot == self.manager.leaf0
        elif command == 'a':
            self.doAssertion(pid, hlist)
            done = nroot == self.manager.leaf0
        elif command == 'k':
            self.doTarget(pid, hlist)
        elif command == 'A':
            self.doCfAssertion(pid, hlist)
        else:
            raise PbipException("", "Unexpected command '%s'" % command)
        return done
        
    def placeInBucket(self, buckets, root, validation):
        supportIds = self.manager.getSupportIds(root)
        for id in supportIds:
            if id in buckets:
                buckets[id].append((root, validation))
                return
        buckets[0].append((root, validation))

    def conjunctTerms(self, r1, v1, r2, v2):
        nroot, implication = self.manager.applyAndJustify(r1, r2)
        validation = None
        antecedents = [v1, v2]
        if nroot == self.manager.leaf0:
            comment = "Validation of empty clause from %s & %s" % (r1.label(), r2.label())
        else:
            comment = "Validation of %s & %s --> %s" % (r1.label(), r2.label(), nroot.label())
        if implication == resolver.tautologyId:
            if nroot == r1:
                validation = v1
            elif nroot == r2:
                validation = v2
        else:
            antecedents += [implication]
        if validation is None:
            validation = self.manager.prover.createClause([nroot.id], antecedents, comment)
        return nroot, validation

    def quantifyRoot(self, root, validation, id):
        antecedents = [validation]
        vfun = self.litMap[id]
        nroot = self.manager.equant(root, vfun)
        ok, implication = self.manager.justifyImply(root, nroot)
        if not ok:
            raise PbipException("", "Implication failed during quantification of %s" % (root.label()))
        if implication != resolver.tautologyId:
            antecedents += [implication]
        comment = "Quantification of node %s by variable %s --> node %s" % (root.label(), str(vfun.variable), nroot.label())
        validation = self.manager.prover.createClause([nroot.id], antecedents, comment)
        return nroot, validation

    # Bucket reduction assumes all external variables come first in variable ordering
    def bucketReduce(self, buckets):
        ids = sorted(list(buckets.keys()))
        if ids[0] == 0:
            ids = ids[1:] + [0]
        for id in ids:
            if self.verbLevel >= 4:
                print("PBIP: Processing bucket #%d.  Size = %d" % (id, len(buckets[id])))
            while len(buckets[id]) > 1:
                (r1,v1) = buckets[id][0]
                (r2,v2) = buckets[id][1]
                buckets[id] = buckets[id][2:]
                nroot,validation = self.conjunctTerms(r1, v1, r2, v2)
                self.placeInBucket(buckets, nroot, validation)
            if len(buckets[id]) == 1:
                root, validation = buckets[id][0]
                if id == 0:
                    return (root, validation)
                nroot, nvalidation = self.quantifyRoot(root, validation, id)
                if self.verbLevel >= 4:
                    print("PBIP: Processed bucket #%d.  Root = %s" % (id, root.label()))
                self.placeInBucket(buckets, nroot, nvalidation)
        raise PbipException("", "Unexpected exit from bucketReduce.  buckets = %s" % str(buckets))


    def doInput(self, pid, hlist):
        clist= self.constraintList[pid-1]
        externalIdSet = set([])
        internalIdSet = set([])
        for con in clist:
            for ivar in con.nz.keys():
                id = self.manager.variables[ivar-1].id
                externalIdSet.add(id)
        # Set up buckets containing trusted BDD representations of clauses
        # Each tbdd is pair (root, validation)
        # Indexed by variable id
        # Special bucket 0 for terms that depend only on external variables
        buckets = { 0 : []}

        if self.verbLevel >= 2:
            self.prover.comment("Processing PBIP Input #%d.  Input clauses %s" % (pid, str(hlist)))
        for hid in hlist:
            iclause = self.creader.clauses[hid-1]
            clause = [self.litMap[lit] for lit in iclause]
            root, validation = self.manager.constructClause(hid, clause)
            if self.verbLevel >= 4:
                print("PBIP: Created BDD with root %s, validation %s for input clause #%d" % (root.label(), str(validation), hid))
            for lit in iclause:
                ivar = abs(lit)
                id = self.manager.variables[ivar-1].id
                if id not in externalIdSet and id not in internalIdSet:
                    internalIdSet.add(id)
                    buckets[id] = []
            self.placeInBucket(buckets, root, validation)
        (broot, bvalidation) = self.bucketReduce(buckets)
        root = self.tbddList[pid-1][0]
        if root == broot:
            cid = bvalidation
        else:
            if self.verbLevel >= 3:
                print("PBIP: Testing %s ==> %s" % (str(broot), str(root)))
            (ok, implication) = self.manager.justifyImply(broot, root)
            if not ok:
                print("PBIP ERROR: Couldn't justify step #%d.  Input not implied" % (pid))
                self.valid = False
                antecedents = []
            else:
                antecedents = [cid for cid in [implication, bvalidation] if cid != resolver.tautologyId]
            comment = "Justification of input constraint #%d" % pid
            cid = self.prover.createClause([root.id], antecedents, comment=comment)
        self.tbddList[pid-1] = (root, cid)
        if self.verbLevel >= 2:
            if root.id == -resolver.tautologyId:
                print("PBIP: Processed PBIP input #%d.  Constraint root = %s, Generated root = %s Empty clause #%d" % (pid, broot.label(), root.label(), cid))
                self.prover.comment("Processed PBIP input #%d.  Constraint root = %s, Generated root = %s Empty clause #%d" % (pid, broot.label(), root.label(), cid))
            else:
                print("PBIP: Processed PBIP input #%d.  Constraint root = %s, Generated root = %s Unit clause #%d [%d]" % (pid, broot.label(), root.label(), cid, root.id))
                self.prover.comment("Processed PBIP input #%d.  Constraint root = %s, Generated root = %s Unit clause #%d [%d]" % (pid, broot.label(), root.label(), cid, root.id))

      
    def assertionHintsOk(self, hlist):
        for hid in hlist:
            if hid < 1 or hid > len(self.tbddList):
                return False
            ht = self.stepTypeList[hid-1]
            if not StepType().implicationOK(ht):
                return False
        return True


    def doAssertion(self, pid, hlist):
        root = self.tbddList[pid-1][0]
        if self.verbLevel >= 2:
            self.prover.comment("Processing PBIP assertion #%d.  Hints = %s" % (pid, str(hlist)))
        antecedents = []
        hok = True
        if len(hlist) not in [1,2]:
            print("PBIP ERROR: Step #%d.  Assertion must have one or two hints" % pid)
            hok = False
        else:
            for hid in hlist:
                if hid < 1 or hid > len(self.tbddList):
                    print("PBIP ERROR: Step #%d.  Hint %d out of range" % (pid, hid))
                    hok = False
                ht = self.stepTypeList[hid-1]
                if not StepType().implicationOK(ht):
                    print("PBIP ERROR: Step #%d.  Hint %d cannot be used for implication-mode assertion" % (pid, hid))
                    hok = False
        if not hok:
            self.valid = False
        elif len(hlist) == 1:
            (r1,v1) = self.tbddList[hlist[0]-1]
            (ok, implication) = self.manager.justifyImply(r1, root)
            if not ok:
                print("PBIP ERROR: Couldn't justify Step #%d.  Not implied by Step #%d" % (pid, hlist[0]))
                self.valid = False
            else:
                antecedents = [cid for cid in [v1, implication] if cid != resolver.tautologyId]
        else:
            (r1,v1) = self.tbddList[hlist[0]-1]
            (r2,v2) = self.tbddList[hlist[1]-1]
            (ok, implication) = self.manager.applyAndJustifyImply(r1, r2, root)
            if not ok:
                print("PBIP ERROR: Couldn't justify Step #%d.  Not implied by Steps #%d and #%d" % (pid, hlist[0], hlist[1]))
                self.valid = False
            else:
                antecedents = [cid for cid in [v1, v2, implication] if cid != resolver.tautologyId]
        comment = "Justification of assertion #%d" % pid
        cid = self.prover.createClause([root.id], antecedents, comment)
        self.tbddList[pid-1] = (root, cid)
        if self.verbLevel >= 2:
            if root.id == -resolver.tautologyId:
                print("PBIP: Processed PBIP assertion #%d.  Root %s Empty clause #%d" % (pid, root.label(), cid))
                self.prover.comment("Processed PBIP assertion #%d.  Root %s Empty clause #%d" % (pid, root.label(), cid))
            else:
                print("PBIP: Processed PBIP assertion #%d.  Root %s Unit clause #%d [%d]" % (pid, root.label(), cid, root.id))
                self.prover.comment("Processed PBIP assertion #%d.  Root %s Unit clause #%d [%d]" % (pid, root.label(), cid, root.id))

    def doTarget(self, pid, hlist):
        if len(hlist) > 0:
            print("PBIP ERROR: Step #%d.  Cannot have hints with target declaration" % (pid))
        self.counterfactualMode = True
        self.targetId = pid
        # Temporary validation is tautology
        root = self.tbddList[pid-1][0]
        self.tbddList[pid-1] = (root, resolver.tautologyId)
        if self.verbLevel >= 2:
            self.prover.comment("PBIP: Processed PBIP target declaration #%d.  Root %s" % (pid, root.label()))
            print("PBIP: Processed PBIP target declaration #%d.  Root %s" % (pid, root.label()))

    def doCfAssertion(self, pid, hlist):
        # Mark which hints are implications and which are counterfactual
        isImplication = []
        root = self.tbddList[pid-1][0]
        if self.verbLevel >= 2:
            self.prover.comment("Processing PBIP counterfactual assertion #%d.  Hints = %s" % (pid, str(hlist)))
        antecedents = []
        hok = True
        if len(hlist) not in [1,2]:
            print("PBIP ERROR: Step #%d.  Counterfactual assertion must have one or two hints" % pid)
            hok = False
        else:
            for hid in hlist:
                if hid < 0:
                    hid = abs(hid)
                    if hid > len(self.tbddList):
                        print("PBIP ERROR: Step #%d.  Hint %d out of range" % (pid, hid))
                        hok = False
                    else:
                        ht = self.stepTypeList[hid-1]
                        if ht != StepType().currentTarget:
                            print("PBIP ERROR: Step #%d.  Negated hint -%d must be for current target" % (pid, hid))
                            hok = False
                    isImplication.append(False)
                elif hid < 1 or hid > len(self.tbddList):
                    print("PBIP ERROR: Step #%d.  Hint %d out of range" % (pid, hid))
                    hok = False
                else:
                    ht = self.stepTypeList[hid-1]
                    if not StepType().cfImplicationOK(ht):
                        print("PBIP ERROR: Step #%d.  Hint %d cannot be used for counterfactual-mode assertion" % (pid, hid))
                        hok = False
                    isImplication.append(StepType().implicationOK(ht))
        if not hok:
            self.valid = False
        elif len(hlist) == 1:
            if isImplication[0]:
                print("PBIP ERROR: Step #%d.  Cannot have implication assertion %d as only hint for counterfactual assertion" % (pid, hlist[0]))
                self.valid = False
            else:
                (r1,v1) = self.tbddList[abs(hlist[0])-1]
                (ok, implication) = self.manager.justifyImply(root, r1)
                if not ok:
                    print("PBIP ERROR: Couldn't justify Step #%d.  Not implied by Step #%d" % (pid, hlist[0]))
                    self.valid = False
                else:
                    antecedents = [cid for cid in [v1, implication] if cid != resolver.tautologyId]
        else:
            (r1,v1) = self.tbddList[abs(hlist[0])-1]
            (r2,v2) = self.tbddList[abs(hlist[1])-1]
            if isImplication[0]:
                if isImplication[1]:
                    print("PBIP ERROR.  Step #%d.  Cannot have both hints be implication assertions" % pid)
                    self.valid = False
                else:
                    (ok, implication) = self.manager.applyAndJustifyImply(r1, root, r2)
                    if not ok:
                        print("PBIP ERROR: Couldn't justify Step #%d.  Not implied by Steps #%d (implication) and #%d (counterfactual)" % (pid, hlist[0], hlist[1]))
                        self.valid = False
                    else:
                        antecedents = [cid for cid in [v1, v2, implication] if cid != resolver.tautologyId]
            else:
                if isImplication[1]:
                    (ok, implication) = self.manager.applyAndJustifyImply(r2, root, r1)
                    if not ok:
                        print("PBIP ERROR: Couldn't justify Step #%d.  Not implied by Steps #%d (counterfactual) and #%d (implication)" % (pid, hlist[0], hlist[1]))
                        self.valid = False
                    else:
                        antecedents = [cid for cid in [v1, v2, implication] if cid != resolver.tautologyId]
                else:
                    (orRoot, orImplication) = self.manager.applyOrJustify(r1, r2)
                    if orImplication is None:
                        orImplication = resolver.tautologyId
                        implication = resolver.tautologyId
                    else:
                        (ok, implication) = self.manager.justifyImply(root, orRoot)
                        if not ok:
                            print("PBIP ERROR: Couldn't justify Step #%d.  Not implied by Steps #%d (counterfactual) and #%d (counterfactual)" % (pid, hlist[0], hlist[1]))
                            self.valid = False
                        else:
                            antecedents = [cid for cid in [v1, v2, orImplication, implication] if cid != resolver.tautologyId]
        
        if not self.valid:
            return
        comment = "Justification of counterfactual assertion #%d" % pid
        targetRoot = self.tbddList[self.targetId-1][0]
        if root == self.manager.leaf1:
            pclause = [targetRoot.id]
        else:
            pclause = [-root.id, targetRoot.id]
        cid = self.prover.createClause(pclause, antecedents, comment)
        self.tbddList[pid-1] = (root, cid)
        if self.verbLevel >= 2:
            if root == self.manager.leaf1:
                print("PBIP: Processed PBIP counterfactual assertion #%d.  Completed proof by contradiction" % pid)
                self.prover.comment("Processed PBIP counterfactual assertion #%d.  Completed proof by contradiction" % pid)
            else:
                print("PBIP: Processed PBIP counterfactual assertion #%d.  Root %s Implication #%d [-%d %d]" % (pid, root.label(), cid, root.id, targetRoot.id))
                self.prover.comment("Processed PBIP counterfactual assertion #%d.  Root %s Implication #%d [-%d %d]" % (pid, root.label(), cid, root.id, targetRoot.id))
        if root == self.manager.leaf1:
            # Counterfactual proof completed.
            # Relabel step types
            rpid = pid
            while rpid > self.targetId:
                self.stepTypeList[rpid-1] = StepType().oldCF
                rpid -= 1
            self.stepTypeList[self.targetId-1] = StepType().assertion
            self.tbddList[self.targetId-1] = (targetRoot, cid)
            self.targetId = None
            self.counterfactualMode = False
            
    def run(self):
        while not self.doStep():
            pass
        decided = False
        if not self.valid:
            print("PBIP INVALID")
            decided = True
        elif len(self.constraintList) > 0:
            lastBdd = self.tbddList[-1][0] if len(self.tbddList) > 0 else self.manager.leaf1
            if lastBdd == self.manager.leaf0:
                decided = True
                print("PBIP UNSAT")
        if not decided:
            print("PBIP Final status unknown")
        self.manager.summarize()


