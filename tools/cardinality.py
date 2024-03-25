# Maintiain set of cardinality constraints
# Generate clausal form

class CardinalityException(Exception):
    form = ""
    msg = ""

    def __str__(self):
        m = self.form
        if self.msg != "":
            m += " (" + self.msg + ")"
        return m

def absSort(ilist):
    return sorted(ilist, key = lambda x : abs(x))


class Constraint:
    literals = tuple([])
    constant = 0
    xvar = 0
    low = None
    high = None
    clauseIds = []

    def __init__(self, literals, constant, xvar):
        self.literals = tuple(literals)
        self.constant = constant
        self.xvar = xvar
        self.low = None
        self.high = None
        self.clauseIds = []

    def clausify(self, cwriter):
        if len(self.clauseIds) > 0:
            return
        if cwriter.verbLevel >= 3:
            cwriter.doComment("Local clauses for constraint %s" % str(self))
        if self.constant == 1:
            self.clauseIds.append(cwriter.doClause([-self.xvar] + list(self.literals)))
            return
        lit = self.literals[0]
        if self.high is not None:
            self.clauseIds.append(cwriter.doClause([-self.xvar, -lit, self.high.xvar]))
        if self.low is None:
            self.clauseIds.append(cwriter.doClause([-self.xvar, lit]))
        else:
            self.clauseIds.append(cwriter.doClause([-self.xvar, lit, self.low.xvar]))

    def addDescendantXvars(self, xvarSet):
        if self.xvar in xvarSet:
            return
        xvarSet.add(self.xvar)
        if self.low is not None:
            self.low.addDescendantXvars(xvarSet)
        if self.high is not None:
            self.high.addDescendantXvars(xvarSet)

    def __str__(self):
        slist = ["x" + str(lit) if lit >= 0 else "~x" + str(-lit) for lit in self.literals]
        return "%d:%s >= %d" % (self.xvar, " + ".join(slist), self.constant)

class Manager:

    startXvar = 0
    # Clause writer
    cwriter = None
    # List of constraints in ascending order of xvar
    constraintList = []
    # Dictionary of constraints 
    constraintDict = {}

    def __init__(self, startXvar, cwriter):
        self.startXvar = startXvar
        self.constraintList = []
        self.constraintDict = {}
        self.cwriter = cwriter

    def nextXvar(self):
        return self.startXvar + len(self.constraintList)

    def build(self, literals, constant):
        s = self.format(literals, constant)
        self.cwriter.doComment("Added clauses for constraint %s" % s)
        if constant == 1:
            id = self.cwriter.doClause(literals)
            return [id]
        lit = literals[0]
        rlits = literals[1:]
        high = self.find(rlits, constant-1)
        low = self.find(rlits, constant)
        clauseIds = self.getClauseIds([low,high])
        clauseIds.append(self.cwriter.doClause([-lit, high.xvar]))
        clauseIds.append(self.cwriter.doClause([lit, low.xvar]))
        return clauseIds

    def format(self, literals, constant):
        slist = ["x" + str(lit) if lit >= 0 else "~x" + str(-lit) for lit in literals]
        return "%s >= %d" % (" + ".join(slist), constant)


    # Reuse or create new constraint
    def find(self, literals, constant):
        key = tuple(literals + [constant])
        if key in self.constraintDict:
            return self.constraintDict[key]
        xvar = self.nextXvar()
        con = Constraint(literals, constant, xvar)
        self.constraintList.append(con)
        self.constraintDict[key] = con
        if constant > 1:
            con.high = self.find(literals[1:], constant-1)
            if len(literals) > constant:
                con.low = self.find(literals[1:], constant)
        con.clausify(self.cwriter)
        return con

    def getConstraint(self, xvar):
        return self.constraintList[xvar-self.startXvar]

    def getDescendants(self, conList):
        xvarSet = set([])
        for con in conList:
            con.addDescendantXvars(xvarSet)
        return [self.getConstraint(xvar) for xvar in xvarSet]

    def getClauseIds(self, conList):
        clist = self.getDescendants(conList)
        idList = []
        for con in clist:
            idList = idList + con.clauseIds
        return sorted(idList)

class TWriter:

    clauseCount = 0
    verbLevel = 1

    def __init__(self, verbLevel = 1):
        self.clauseCount = 0
        self.verbLevel = verbLevel

    def doComment(self, line):
        if self.verbLevel >= 2:
            print("c " + line)

    def doClause(self, literals):
        slist = [str(lit) for lit in literals]
        self.clauseCount += 1
        print("  %d: " % self.clauseCount + " ".join(slist) + " 0")

        return self.clauseCount

cm = Manager(100, TWriter())        

