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

# Divide string into tokens, where open and close brackets are separate tokens
def tokenize(s):
    result = []
    tok = ""
    for c in s:
        if c in " \t":
            if tok != "":
                result.append(tok)
                tok = ""
        elif c in "[]":
            if tok != "":
                result.append(tok)
                tok = ""
            result.append(c)
        else:
            tok += c
    if tok != "":
        result.append(tok)
    return result
        
  

# Convert string of tokens into nested list of integers based on bracket structure
def listify(s, maxdepth = None, mindepth = None):
    tokens = tokenize(s)
    active = [[]]
    for tok in tokens:
        if tok == '[':
            if maxdepth is not None and len(active) >= maxdepth:
                msg = "Nesting is too deep"
                return (msg, None)
            active.append([])
        elif tok == ']':
            if len(active) < 2:
                msg = "Mismatched brackets.  Unexpected ']'"
                return (msg, None)
            active[-2].append(active[-1])
            active = active[:-1]
        elif mindepth is not None and len(active) < mindepth:
            msg = "Trying to append token '%s' at invalid depth" % tok
            return (msg, None)
        else:
            ptok = tok
            negate = False
            if ptok[0] == '~':
                negate = True
                ptok = ptok[1:]
            if ptok[0] == 'x':
                ptok = ptok[1:]
            try:
                val = int(ptok)
                if negate:
                    val = -val
            except:
                msg = "Couldn't extract integer from token %s" % tok
                return (msg, None)
            active[-1].append(val)
    if len(active) > 1:
        msg = "Mismatched brackets.  Not enough ']' brackets"
        return (msg, None)
    return ("", active[0])
        
def pairlists(s):
    msg, ols = listify(s, 2, 2)
    if ols is None:
        return msg, ols
    # Split multiple-literal sublists into singles
    ls = []
    for sls in ols:
        if len(sls) <= 2:
            ls.append(sls)
        else:
            head = sls[0]
            for lit in sls[1:]:
                ls.append([head, lit])
    return msg, ls

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
    tups = [(v,c) for v,c in zip(vars, coeffs)]
    tups.sort(key = lambda t : abs(t[0]))
    nz = { v : c for v,c in tups }
    con1 = pseudoboolean.Constraint(len(nz), cval)
    con1.setNz(nz)
    if rel == '>=':
        return (con1,)
    else:
        cval = -cval
        tups = [(t[0],-t[1]) for t in tups]
        nz = { v : c for v,c in tups }
        con2 = pseudoboolean.Constraint(len(nz), cval)
        con2.setNz(nz)
        return (con1, con2)
    
class PbipReader:
    fname = ""
    lineCount = 0
    infile = None
    verbLevel = 1
    
    def __init__(self, fname, verbLevel):
        self.fname = fname
        self.start()
        self.verbLevel = verbLevel

    def start(self):
        try:
            self.infile = open(self.fname, 'r')            
        except:
            print("Can't open input file %s" % self.fname)
            raise PbipException("", "Invalid input file")
        self.lineCount = 0

    def finish(self):
        if self.infile is not None:
            self.infile.close()
            self.infile = None
        
    def findMaximum(self):
        maximum = 0
        while True:
            nextMaximum = self.maximumLine()
            if nextMaximum is None:
                break
            if nextMaximum > maximum:
                maximum = nextMaximum
        ## reset
        self.finish()
        self.start()
        return maximum

    def maximumLine(self):
        eof = True
        maximum = 0
        for line in self.infile:
            eof = False
            self.lineCount += 1
            line = trim(line)
            if len(line) == 0:
                continue
            if line[0] == '*':
                continue
            command = line[0]
            if command != 'i':
                continue
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
            for con in clist:
                for var in con.nz.keys():
                    maximum = max(maximum, var)
        if eof:
            return None
        else:
            return maximum

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
            if command not in "iauk":
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
            if command in ['i', 'a']:
                hfields = hstring.split()
                try:
                    hlist = [int(f) for f in hfields]
                except:
                    raise PbipException("", "File %s Line %d: Couldn't parse hint list '%s'" % (self.fname, self.lineCount, hstring))
                break
            else:
                msg, hlist = pairlists(hstring)
                if hlist is None:
                    raise PbipException("", "File %s Line %d: Couldn't parse hint list '%s' (%s)" % (self.fname, self.lineCount, hstring, msg))
                break
        if self.verbLevel >= 3:
            print("PBIP: Read PBIP line #%d.  Command = %s" % (self.lineCount, command))
            print("PBIP:  Constraints:")
            for con in clist:
                print("PBIP:     %s" % str(con))
            if len(hlist) > 0:
                print("PBIP:   Hints: %s" % str(hlist))
        return (command, clist, hlist, comlist)

#### Support for Symbolic Davis-Putnam (SDP) reduction
class BucketException(Exception):
    valid = None

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "BUCKET Exception: " + str(self.value)


# Class for performing bucket reduction
class BucketReducer:

    parent = None
    buckets = {0 : []}

    def __init__(self, parent):
        self.parent = parent
        self.buckets = {0 : []}

    def placeInBucket(self, root, validation):
        supportLevels = self.parent.manager.getSupportLevels(root)
        supportLevels.reverse()
        for level in supportLevels:
            if level in self.buckets:
                self.buckets[level].append((root, validation))
                return
        # Support set only has data variables
        self.buckets[0].append((root, validation))
    
    # Bucket reduction based on variable levels
    def reduce(self):
        levels = sorted(list(self.buckets.keys()))
        levels.reverse()
        if levels[0] == 0:
            levels = levels[1:]
        if len(levels) == 0  or levels[-1] != 0:
            levels = levels + [0]
        for level in levels:
            id = self.parent.idMap[level]
            if self.parent.verbLevel >= 4:
                var = self.parent.varMap[id] if id > 0 else "TOP"
                print("BREDUCE: Processing bucket #%d (variable %s).  Size = %d" % (level, str(var), len(self.buckets[level])))
            while len(self.buckets[level]) > 1:
                (r1,v1) = self.buckets[level][0]
                (r2,v2) = self.buckets[level][1]
                self.buckets[level] = self.buckets[level][2:]
                nroot,validation = self.parent.conjunctTerms(r1, v1, r2, v2)
                self.placeInBucket(nroot, validation)
            if len(self.buckets[level]) == 1:
                root, validation = self.buckets[level][0]
                if level == 0:
                    return (root, validation)
                nroot, nvalidation = self.parent.quantifyRoot(root, validation, id)
                if self.parent.verbLevel >= 4:
                    print("BREDUCE: Processed bucket #%d.  Root = %s" % (level, root.label()))
                self.placeInBucket(nroot, nvalidation)
        raise BucketException("", "Unexpected exit from reduce.  buckets = %s" % str(self.buckets))

    def performReduction(self, hlist, inputIdSet):
        # Set up buckets containing trusted BDD representations of clauses
        # Each tbdd is pair (root, validation)
        # Indexed by variable level
        # Special bucket 0 for terms that depend only on external variables
        self.buckets = { 0 : []}
        internalIdSet = set([])
        for hid in hlist:
            iclause = self.parent.creader.clauses[hid-1]
            root, validation = self.parent.getInputClauseBdd(hid)
            for lit in iclause:
                ivar = abs(lit)
                id = ivar
                if id not in inputIdSet and id not in internalIdSet:
                    internalIdSet.add(id)
                    bddVar = self.parent.varMap[id]
                    level = bddVar.level
                    self.buckets[level] = []
            self.placeInBucket(root, validation)
        (root, validation) = self.reduce()
        return (root, validation)

#### Support for Symbolic Davis-Putnam (SDP) reduction
class SdpException(Exception):
    valid = None

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "SDP Exception: " + str(self.value)

    

# Term for use in converting CNF into BDDs via
# symbolic Davis-Putnam reduction
class SdpTerm:
    parent = None # Pointer to PBIP information
    head = tuple([])   # Head clause (list of integers).  Must be tuple.  Ascending order by variable
    literal = 0  # Splitting literal (integer) (0 indicates no literal and must have empty head)
    tail = None # BDD representation of conjoined terms
    validation = None # Clause Id for head + [var] + [tail.validation]

    def __init__(self, parent, head = tuple([]), literal = 0, tail = None, validation = None):
        self.parent = parent
        self.head = head
        self.literal = literal
        self.tail = self.parent.manager.leaf0 if tail is None else tail
        self.validation = 0 if validation is None else validation

    def __str__(self):
        return "T<%s, %d, %s, %d>" % (str(list(self.head)), self.literal, self.tail.label(), self.validation)

    def litLevel(self, ilit):
        return self.parent.idToLevel(abs(ilit))

    def orderLiterals(self, literals):
        return tuple(sorted(literals, key = lambda lit: self.litLevel(lit)))

    def newHead(self, literals):
        if len(literals) == 0:
            return literals, 0
        else:
            return tuple(literals[:-1]), literals[-1]

    def fromInputClause(self, literals, id):
        tup = self.orderLiterals(literals)
        self.head, self.literal = self.newHead(tup)
        self.tail = self.parent.manager.leaf0
        self.validation = id
        return self

    # Merge terms having identical heads and literals
    def tailMerge(self, other):
        ## Must have identical head and literal
        if self.head != other.head:
            raise SdpException("Cannot merge tuples %s and %s.  Heads differ" % (str(self), str(other)))
        if self.literal != other.literal:
            raise SdpException("Cannot merge tuples %s and %s.  Literals differ" % (str(self), str(other)))
        if self.tail == self.parent.manager.leaf0:
            nroot, validation = self.tail, self.validation
        elif other.tail == self.parent.manager.leaf0:
            nroot, validation = other.tail, other.validation
        elif self.tail == self.parent.manager.leaf1:
            nroot, validation = other.tail, other.validation
        elif other.tail == self.parent.manager.leaf1:
            nroot, validation = self.tail, self.validation            
        elif self.tail == other.tail:
            nroot, validation = self.tail, self.validation
        else:
            nroot, jclause = self.parent.manager.applyAndJustify(self.tail, other.tail)
            if self.literal == 0:
                vclause = list(self.head) + [nroot.id]
            else:
                vclause = list(self.head) + [self.literal, nroot.id]
            comment = "Tail merge.  Head = %s. Literal = %d" % (str(self.head), self.literal)
            antecedents = [self.validation, other.validation, jclause]
            validation = self.parent.manager.prover.createClause(vclause, antecedents, comment)
        return SdpTerm(self.parent, self.head, self.literal, nroot, validation)
        
    # Combine two SDP terms have matching heads and opposite literals of data variable
    def join(self, other):
        if self.literal != -other.literal:
            raise SdpException("Cannot combine terms %s and %s.  Incompatible literals %d and %d" % (str(self), str(other), self.literal, other.literal))
        if self.head != other.head:
            raise SdpException("Cannot combine terms %s and %s.  Non-matching heads" % (str(self), str(other)))
        nhead, nliteral = self.newHead(self.head)
        ivar = abs(self.literal)
        var = self.parent.varMap[ivar]
        if self.literal < 0:
            tchild = self.tail
            echild = other.tail
            tvalidation = self.validation
            evalidation = other.validation
        else:
            tchild = other.tail
            echild = self.tail
            tvalidation = other.validation
            evalidation = self.validation
        ntail = self.parent.manager.findOrMake(var, tchild, echild)
        vclause = list(self.head) + [ntail.id]
        hints = {}
        hints["WHU"] = (ntail.idHU(), resolver.cleanClause(list(nhead) + [-ivar, -tchild.id, ntail.id]))
        hints["WLU"] = (ntail.idLU(), resolver.cleanClause(list(nhead) + [ ivar, -echild.id, ntail.id]))
        hints["OPH"] = (tvalidation,  resolver.cleanClause(list(nhead) + [-ivar, tchild.id]))
        hints["OPL"] = (evalidation,  resolver.cleanClause(list(nhead) + [ ivar, echild.id]))
        comment = "Join of terms %s and %s with root variable %d" % (str(self), str(other), ivar)
        validation = self.parent.manager.vresolver.run(vclause, ivar, hints, comment)
        return SdpTerm(self.parent, nhead, nliteral, ntail, validation)

    # Transfer literal from head to tail
    def processLiteral(self):
        ivar = abs(self.literal)
        var = self.parent.varMap[ivar]
        nhead, nliteral = self.newHead(self.head)
        if self.literal > 0:
            ntail = self.parent.manager.findOrMake(var, self.parent.manager.leaf1, self.tail)
            antecedents = resolver.cleanHint([ntail.idHU(), self.validation, ntail.idLU()])
        else:
            ntail = self.parent.manager.findOrMake(var, self.tail, self.parent.manager.leaf1)
            antecedents = resolver.cleanHint([ntail.idLU(), self.validation, ntail.idHU()])
        vclause = list(self.head) + [ntail.id]
        comment = "Transfer literal %d from head to tail for term %s" % (self.literal, str(self))
        validation = self.parent.manager.prover.createClause(vclause, antecedents, comment)
        return SdpTerm(self.parent, nhead, nliteral, ntail, validation)

    # Combine head of one term with tail of other
    def resolve(self, other):
        if self.literal != -other.literal:
            raise SdpException("Cannot resolve terms %s and %s.  Incompatible literals %d and %d" % (str(self), str(other), self.literal, other.literal))
        rhead = resolver.cleanClause(list(self.head) + list(other.head))
        if rhead == resolver.tautologyId:
            return None
        rhead = self.orderLiterals(rhead)
        nhead, nliteral,  = self.newHead(rhead)
        if self.tail == self.parent.manager.leaf0:
            ntail = other.tail
            vclause = list(rhead) + [ntail.id]
            antecedents = [self.validation, other.validation]
        elif other.tail == self.parent.manager.leaf0:
            ntail = self.tail
            vclause = list(rhead) + [ntail.id]
            antecedents = [self.validation, other.validation]
        else:
            ntail = self.parent.manager.applyOr(self.tail, other.tail)
            if ntail == self.parent.manager.leaf1:
                return None
            vclause = list(rhead) + [ntail.id]
            sid = self.parent.manager.justifyImply(self.tail, ntail)
            oid = self.parent.manager.justifyImply(other.tail, ntail)
            antecedents = [sid, oid, self.validation, other.validation]
        comment = "Resolve terms terms %s and %s" % (str(self), str(other))
        validation = self.parent.manager.prover.createClause(vclause, antecedents, comment)
        return SdpTerm(self.parent, nhead, nliteral, ntail, validation)

class SdpReducer:

    parent = None
    buckets = { 0 : [] }

    def __init__(self, parent):
        self.parent = parent
        self.buckets = { 0 :[] }

        
    def placeInBucket(self, lterm):
        var = abs(lterm.literal)
        level = self.parent.idToLevel(var)
        if level not in self.buckets:
            self.buckets[level] = [lterm]
        else:
            self.buckets[level].append(lterm)
        if self.parent.verbLevel >= 4:
            print("   Placed term %s in bucket %d (var %d)" % (str(lterm), level, var))

    def sdpBucketReduce(self, inputIdSet):
        # Process from largest level to smallest
        bucketItems = []
        while len(self.buckets) > 0:
            level = max(self.buckets.keys())
            bucketItems = self.buckets[level]
            del self.buckets[level]
            if level == 0:
                break
            ivar = self.parent.levelToId(level)
            if self.parent.verbLevel >= 3:
                tstring = "I" if ivar in inputIdSet else "Z"
                print("Processing bucket %d (Variable %s%d).  %d terms" % (level, tstring, ivar, len(bucketItems)))
                if self.parent.verbLevel >= 4:
                    for t in bucketItems:
                        print("  %s" % str(t))
            # Merge terms with matching heads and literals.
            # Mapping of head to separate lists for positive and negative terms
            headDict = {}
            for lt in bucketItems:
                if lt.head not in headDict:
                    headDict[lt.head] = [[],[]]
                phase = 1 if lt.literal > 0 else 0 
                headDict[lt.head][phase].append(lt)
            for head in headDict:
                # Tail reduction to have at most one term with each phase
                for phase in range(2):
                    while len(headDict[head][phase]) > 1:
                        # Merge
                        lt1 = headDict[head][phase][0]
                        lt2 = headDict[head][phase][1]
                        headDict[head][phase] = headDict[head][phase][2:]
                        nlt = lt1.tailMerge(lt2)
                        headDict[head][phase].append(nlt)
                        if self.parent.verbLevel >= 5:
                            print("   Tail merged %s and %s to get %s" % (str(lt1), str(lt2), str(nlt)))

            # Process by head.  At most two terms
            for head in headDict:
                if ivar in inputIdSet:
                    if len(headDict[head][0]) == 0:
                        nterm = headDict[head][1][0].processLiteral()
                    elif len(headDict[head][1]) == 0:
                        nterm = headDict[head][0][0].processLiteral()
                    else:
                        nterm = headDict[head][0][0].join(headDict[head][1][0])
                    if self.parent.verbLevel >= 4:
                        print("  Generated data term %s" % str(nterm))
                    self.placeInBucket(nterm)
                else:
                    if len(headDict[head][0]) == 0:
                        continue
                    for ohead in headDict:
                        if len(headDict[ohead][1]) == 0:
                            continue
                        nterm = headDict[head][0][0].resolve(headDict[ohead][1][0])
                        if nterm is None:
                            continue
                        if self.parent.verbLevel >= 4:
                            print("  Generated resolution term %s" % str(nterm))
                        self.placeInBucket(nterm)                    

        # Process top-level bucket
        while len(bucketItems) > 1:
            lt1 = bucketItems[0]
            lt2 = bucketItems[1]
            bucketItems = bucketItems[2:]
            nterm = lt1.tailMerge(lt2)
            bucketItems.append(nterm)
        if len(bucketItems) < 1:
            raise SdpException("SPD reduction failed.  Bucket 0 empty")
        rt = bucketItems[0]
        return rt.tail, rt.validation

    def performReduction(self, hlist, inputIdSet):
        # Set up buckets containing SDP terms
        # Special bucket 0 for terms that depend only on external variables
        self.buckets = { 0 : []}
        for hid in hlist:
            iclause = self.parent.creader.clauses[hid-1]
            lterm = SdpTerm(self.parent).fromInputClause(iclause, hid)
            self.placeInBucket(lterm)
        (root, validation) = self.sdpBucketReduce(inputIdSet)
        return (root, validation)


class Pbip:
    verbLevel = 1
    bddOnly = False
    sdpReduce = False
    valid = True
    creader = None
    preader = None
    permuter = None
    # Set of constraints
    # Array mapping from PBIP file constraints to cset constraints (offset by 1)
    # Each is a list containing Ids of 1 or 2 constraints
    constraintList = []
    # Trusted BDD representations of constraints
    # Each TBDD is pair (root, validation)
    tbddList = []
    # Clausal representations of constratints (when they exist).
    # Pair of form.  Can be of form:
    # (clause, cid).  Clause is present in input or proof file with specified ID
    # (clause, None). Constraint has clausal form, but hasn't been validated
    # (None, None).   Running bddOnly mode or constraint is not clausal
    tclauseList = []
    maxBddSize = 0
    maxConstant = 0
    lastClauseCount = 0

    # Enable use as constraint system
    prover = None
    manager = None
    litMap = {}
    varMap = {}
    levelMap = {}
    idMap = {}

    def __init__(self, cnfName, pbipName, lratName, verbLevel, bddOnly, reorder, sdpReduce):
        self.verbLevel = verbLevel
        self.bddOnly = bddOnly
        self.sdpReduce = sdpReduce
        self.valid = True
        self.creader = solver.CnfReader(cnfName, verbLevel)
        self.preader = PbipReader(pbipName, verbLevel)
        self.constraintList = []
        self.tbddList = []
        lratName = None if lratName == "" else lratName
        self.prover = solver.Prover(fname=lratName, writer = solver.StdOutWriter(), verbLevel = verbLevel, doLrat = True)
        # Print input clauses
        clauseCount = 0
        for clause in self.creader.clauses:
            clauseCount += 1
            self.prover.createClause(clause, [], "Input clause %d" % clauseCount, isInput = True)
        self.prover.inputDone()
        inputCount = self.preader.findMaximum()
        varOrder = list(range(1, self.creader.nvar+1))
        if reorder:
            varOrder = self.creader.orderVariables(inputCount)
        self.manager = bdd.Manager(prover = self.prover, rootGenerator = self.rootGenerator, nextNodeId = self.creader.nvar+1, verbLevel = verbLevel)
        self.litMap = {}
        for id in varOrder:
            var = self.manager.newVariable(name = "V%d" % id, id = id)
            self.litMap[ id] = None
            self.litMap[-id] = None
        self.varMap = { var.id : var for var in self.manager.variables }
        self.levelMap = { var.id : var.level for var in self.manager.variables }
        self.idMap = { var.level : var.id for var in self.manager.variables }
        self.idMap[0] = 0
        self.maxBddSize = 0
        self.maxConstant = 0
        self.deltaClauses()

    def idToLevel(self, id):
        if id == 0:
            return 0
        return self.levelMap[id]

    def levelToId(self, level):
        if level == 0:
            return 0
        return self.idMap[level]

    def getLiteralBdd(self, lit):
        if self.litMap[lit] is None:
            var = self.varMap[abs(lit)]
            phase = 1 if lit > 0 else 0
            self.litMap[lit] = self.manager.literal(var, phase)
        return self.litMap[lit]

    def deltaClauses(self):
        occ = self.lastClauseCount
        self.lastClauseCount = self.prover.clauseCount
        return self.lastClauseCount - occ

    def doStep(self):
        command, clist, hlist, comlist = self.preader.readLine()
        if command == '':
            return True
        # Special handling of input constraints represented by single clauses
        tclause = None
        tcid = None
        clauseOnly = False
        if not self.bddOnly and len(clist) == 1:
            tclause = clist[0].getClause()
            if tclause is not None and command == 'i' and len(hlist) == 1:
                # Won't generate BDD representation until needed
                tcid = hlist[0]
                clauseOnly = True
            elif tclause is not None and command in "uk":
                # Allow setting of target clause
                pass
#                clauseOnly = True
            else:
                tclause = None
        self.tclauseList.append((tclause, tcid))
        for con in clist:
            self.maxConstant = max(self.maxConstant, abs(con.variableNormalizedCval()))
        if not clauseOnly:
            for con in clist:
                con.buildBdd(self)
        self.constraintList.append(clist)
        if len(clist) == 2:
            nroot = self.manager.applyAnd(nclist[0].root, nclist[1].root)
        elif clauseOnly:
            nroot = None
        else:
            nroot = clist[0].root
        self.tbddList.append((nroot,None))
        if nroot is not None:
            self.maxBddSize = max(self.maxBddSize, self.manager.getSize(nroot))
        startCount = len(self.manager.uniqueTable)
        pid = len(self.constraintList)
        done = False
        for com in comlist:
            self.prover.comment(com)
        if command == 'i':
            self.doInput(pid, hlist)
            done = len(tclause) == 0 if clauseOnly else nroot == self.manager.leaf0
        elif command == 'a':
            self.doAssertion(pid, hlist)
            done = nroot == self.manager.leaf0
        elif command in "uk":
            self.doRup(pid, hlist)
            done = len(tclause) == 0 if clauseOnly else nroot == self.manager.leaf0
        else:
            raise PbipException("", "Unexpected command '%s'" % command)
        deltaCount = len(self.manager.uniqueTable) - startCount
        if deltaCount > 0:
            self.manager.checkGC(deltaCount)
        return done
        
    def needTbdd(self, pid):
        (root, validation) = self.tbddList[pid-1]
        if validation is None:
            clause, cid = self.tclauseList[pid-1]
            if cid is not None:
                lits = [self.getLiteralBdd(lit) for lit in clause]
                root, validation = self.manager.constructClauseBdd(cid, lits)
            else:
                raise PbipException("Can't generate TBDD representation of constraint %d" % pid)
            self.tbddList[pid-1] = (root, validation)            

    def needClauseValidation(self, pid):
        clause, cid = self.tclauseList[pid-1]
        if cid is not None:
            return
        if clause is None:
            raise PbipException("Can't generate clausal representation of constraint %d" % pid)
        (root, validation) = self.tbddList[pid-1]
        if root is not None:
            oroot, ovalidation = self.manager.constructOr(clause, self.getLiteralBdd)
            comment = "Generate validated clause from TBDD %s" % root.label()
            cvalidation = self.manager.prover.createClause(clause, [validation, ovalidation], comment)
            self.tclauseList[pid-1] = (clause, cvalidation) 
        else:
            raise PbipException("Can't generate validated clausal representation of constraint #%d" % pid)

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
        vfun = self.getLiteralBdd(id)
        nroot = self.manager.equant(root, vfun)
        ok, implication = self.manager.justifyImply(root, nroot)
        if not ok:
            raise PbipException("", "Implication failed during quantification of %s" % (root.label()))
        if implication != resolver.tautologyId:
            antecedents += [implication]
        comment = "Quantification of node %s by variable %s --> node %s" % (root.label(), str(vfun.variable), nroot.label())
        validation = self.manager.prover.createClause([nroot.id], antecedents, comment)
        return nroot, validation

    def getInputClauseBdd(self, id):
        iclause = self.creader.clauses[id-1]
        clause = [self.getLiteralBdd(lit) for lit in iclause]
        root, validation = self.manager.constructClauseBdd(id, clause)
        if self.verbLevel >= 4:
            print("PBIP: Created BDD with root %s, validation %s for input clause #%d" % (root.label(), str(validation), id))
        return (root, validation)

    def doInput(self, pid, hlist):
        clist= self.constraintList[pid-1]
        if not self.bddOnly and len(hlist) == 1 and self.tclauseList[pid-1][0] is not None:
            self.tclauseList[pid-1] = (self.tclauseList[pid-1][0], hlist[0])
            if self.verbLevel >= 2:
                print("PBIP: Processed PBIP input #%d.  Represented by input clause #%d" % (pid, hlist[0]))
            return

        inputIdSet = set([])
        for con in clist:
            for ivar in con.nz.keys():
                id = ivar
                inputIdSet.add(id)

        if self.verbLevel >= 2:
            self.prover.comment("Processing PBIP Input #%d.  Input clauses %s" % (pid, str(hlist)))
        if self.sdpReduce:
            reducer = SdpReducer(self)
        else:
            reducer = BucketReducer(self)
        (broot, bvalidation) = reducer.performReduction(hlist, inputIdSet)

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
                print("PBIP: Processed PBIP input #%d.  Empty clause #%d.  Added %d clauses" % (pid, cid.  self.deltaClauses()))
                self.prover.comment("Processed PBIP input #%d.  Constraint root = %s, Generated root = %s Empty clause #%d" % (pid, broot.label(), root.label(), cid))
            else:
                print("PBIP: Processed PBIP input #%d. Added %d clauses" % (pid, self.deltaClauses()))
                self.prover.comment("Processed PBIP input #%d.  Constraint root = %s, Generated root = %s Unit clause #%d [%d]" % (pid, broot.label(), root.label(), cid, root.id))


    def doAssertion(self, pid, hlist):
        root = self.tbddList[pid-1][0]
        if self.verbLevel >= 2:
            self.prover.comment("Processing PBIP assertion #%d.  Hints = %s" % (pid, str(hlist)))
        unitLterals = []
        hok = True
        if len(hlist) == 0:
            print("PBIP ERROR: Step #%d.  Must have at least one hint" % pid)
            hok = False
        else:
            for hid in hlist:
                if hid < 1 or hid > len(self.tbddList):
                    print("PBIP ERROR: Step #%d.  Hint %d out of range" % (pid, hid))
                    hok = False
        if not hok:
            self.valid = False
        elif len(hlist) == 1:
            hid = hlist[0]
            self.needTbdd(hid)
            (r1,v1) = self.tbddList[hid-1]
            (ok, implication) = self.manager.justifyImply(r1, root)
            if not ok:
                print("PBIP ERROR: Couldn't justify Step #%d.  Not implied by Step #%d" % (pid, hid))
                self.valid = False
            else:
                antecedents = [cid for cid in [v1, implication] if cid != resolver.tautologyId]
        else:
            hid1, hid2 = hlist
            self.needTbdd(hid1)
            (r1,v1) = self.tbddList[hid1-1]
            self.needTbdd(hid2)
            (r2,v2) = self.tbddList[hid2-1]
            (ok, implication) = self.manager.applyAndJustifyImply(r1, r2, root)
            if not ok:
                print("PBIP ERROR: Couldn't justify Step #%d.  Not implied by Steps #%d and #%d" % (pid, hid1, hid2))
                self.valid = False
            else:
                antecedents = [cid for cid in [v1, v2, implication] if cid != resolver.tautologyId]
        comment = "Justification of assertion #%d" % pid
        cid = self.prover.createClause([root.id], antecedents, comment)
        self.tbddList[pid-1] = (root, cid)
        if self.verbLevel >= 2:
            if root.id == -resolver.tautologyId:
                print("PBIP: Processed PBIP assertion #%d.  Empty clause #%d.  Added %d clauses" % (pid, cid, self.deltaClauses()))
                self.prover.comment("Processed PBIP assertion #%d.  Root %s Empty clause #%d" % (pid, root.label(), cid))
            else:
                print("PBIP: Processed PBIP assertion #%d.  Added %d clauses" % (pid, self.deltaClauses()))
                self.prover.comment("Processed PBIP assertion #%d.  Root %s Unit clause #%d [%d]" % (pid, root.label(), cid, root.id))

    def doRup(self, pid, hlist):
        root, validation = self.tbddList[pid-1]
        targetClause, cid = self.tclauseList[pid-1]
        bddTarget = targetClause is None
        if bddTarget:
            if root is None:
                raise PbipException("", "Have neither clausal nor BDD representation of constraint %d" % pid)
            targetClause = [root.id] if root != self.manager.leaf0 else []
        if self.verbLevel >= 2:
            self.prover.comment("Processing PBIP rup line #%d.  Hints = %s" % (pid, str(hlist)))
        if self.verbLevel >= 3:
            print("PBIP: Processing RUP line #%d.  Root = %s.  Hints = %s" % (pid, root.label(), str(hlist)))
        # Build up antecedents for final RUP addition
        finalAntecedents = []
        litList = []
        for hint in hlist:
            clauseUsed = False
            aid = abs(hint[0])
            alit = hint[1] if len(hint) == 2 else None
            stepAntecedents = []
            stepClause = []
            if aid < pid:
                propArgs = [-lit for lit in litList]
                if alit is not None:
                    propArgs += [alit]
                stepClause = propArgs
                (tclause, tcid) = self.tclauseList[aid-1]
                if tcid is not None:
                    # Use the clausal representation for unit propagation
                    clauseUsed = True
                    stepAntecedents = [tcid]
                else:
                    (ar,av) = self.tbddList[aid-1]
                    (vroot,vid) = self.manager.constructOr(propArgs, self.getLiteralBdd)
                    stepAntecedents = [av, vid]
                    (uroot,uid) = self.manager.justifyImply(ar,vroot)
                    if uid != resolver.tautologyId:
                        stepAntecedents.append(uid)
            elif bddTarget:
                propArgs = list(litList)
                if alit is not None:
                    propArgs += [-alit]
                (vroot,vid) = self.manager.constructAnd(propArgs, self.getLiteralBdd)
                stepAntecedents = [vid]
                (uroot,uid) = self.manager.justifyImply(vroot,root)
                if uid != resolver.tautologyId:
                    stepAntecedents.append(uid)
                stepClause = [-lit for lit in propArgs] + targetClause
            else:
                # Can unit propagate directly off target clause
                litList += [-lit for lit in targetClause]
                continue
            # Generate proof for step
            used = "clause" if clauseUsed else "BDDs"
            comment = "Justification of step in RUP addition #%d (%s used).  Hint = %s" % (pid, used, str(hint))
            scid = self.prover.createClause(stepClause, stepAntecedents, comment)
            if scid != resolver.tautologyId:
                finalAntecedents.append(scid)
            if alit is not None:
                litList.append(alit)
            if self.verbLevel >= 3:
                print("PBIP: Processing RUP addition #%d step (%s used). Hint = %s.  Generated clause #%d" % (pid, used, str(hint), scid))

        comment = "Justification of RUP addition #%d" % pid
        cid = self.prover.createClause(targetClause, finalAntecedents, comment)
        if bddTarget:
            self.tbddList[pid-1] = (root, cid)
        else:
            self.tclauseList[pid-1] = (targetClause, cid)
        if self.verbLevel >= 2:
            if len(targetClause) == 0:
                print("PBIP: Processed PBIP RUP addition #%d.  Empty clause #%d.  Added %d clauses" % (pid, cid, self.deltaClauses()))
                self.prover.comment("Processed PBIP RUP addition #%d.  Empty clause #%d" % (pid, cid))
            else:
                print("PBIP: Processed PBIP RUP addition #%d.  Added %d clauses" % (pid, self.deltaClauses()))
                self.prover.comment("Processed PBIP RUP addition #%d.  Target clause %s #%d" % (pid, targetClause, cid))
            
    def rootGenerator(self):
        return [root for root,validation in self.tbddList if root is not None]
            

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
        print("PBIP Results:")
        print("  Maximum Constraint RHS = %d" % self.maxConstant)
        print("  Maximum BDD size = %d" % self.maxBddSize)
        print("BDD Results:")
        self.manager.summarize()

