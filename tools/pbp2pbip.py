# This file transforms pseudoboolean proofs generated by VeriPB (Gocht 2022)
# into pseudoboolean proofs in the PBIP (Pseudoboolean Implication Proof) format
# introduced by Bryant (2022).

# Author: Karthik Nukala (kvn@andrew.cmu.edu)

# The tool takes in two files:
# - the input pseudoboolean constraints in .opb format
# - the pseudoboolean proof file in .pbp/.veripb formats
# The output is a .pbip file.

# ******************************************************************************
# import statements

import sys
import math
import getopt

# ******************************************************************************
# classes used

# mimicking CnfException from the same CNF-parsing file in the tbuddy repo
class PbpException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "PBP Exception: " + str(self.value)


# stack interface used for polish notation processing
class Stack:
    def __init__(self):
        self.elems = []

    def is_empty(self):
        return self.elems == []

    def push(self, elem):
        self.elems.append(elem)

    def pop(self):
        return self.elems.pop()

    def __str__(self):
        return str(self.elems)

# ******************************************************************************
# global structures and variables


# store clause i as dict pair {i : [b | c1, c2, ..., cn]}
clauses = dict()

nInitclauses = 0 # stores the number of init clauses (used only for final_print())

nclause = 0

# since creating new clauses results in a mismatched numbering,
# map original clause numbers to updated clause numbers
clause_maps = dict()
prev_nclause = 0


# mapping clause IDs to their dependencies
deps = dict()


orig_stdout = sys.stdout

# ******************************************************************************
# miscellaneous print functions

def shell_print(st):
    temp = sys.stdout
    global orig_stdout
    sys.stdout = orig_stdout
    print(st)
    sys.stdout = temp
    

def print_clauses():
    for clause in clauses:
        print(clause, end=": ")
        print(clauses[clause])

def print_deps():
    for dep in deps:
        print(dep, end=": ")
        print(deps[dep])

def print_all():
    for idx in clauses:
        print(idx, end=": ")
        print(clauses[idx], end=" ; ")
        try:
            print(deps[idx])
        except KeyError:
            print("none")

def final_print():
    for idx in clauses:
        clause = clauses[idx]
        if idx <= nInitclauses:
            print("i ", end=" ")
        else:
            print("a ", end=" ")
        for i in range(1, len(clause)):
            if (clause[i] == 0):
                continue
            else:
                print(str(clause[i]) + " " + "x" + str(i), end=" ")

        print(">= " + str(clause[0]), end="; ")
        try:
            d = deps[idx]
            if len(d) == 2:
                print(str(d[0]) + " " + str(d[1]))
            else:
                print(str(d[0]))
        except KeyError:
# REB: Don't add hints after input clauses
            print("")
#            print(idx)


# ******************************************************************************
# helper/misc methods

# taken from a CNF-parsing file in the tbuddy repo
def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s

def test():
    readPbp("./VeriPB-master/tests/integration_tests/correct/miniProof_polishnotation_1.pbp", "./VeriPB-master/tests/integration_tests/correct/miniProof_polishnotation_1.opb")
#    readPbp("./VeriPB-master/tests/integration_tests/correct/all_diff.pbp", "./VeriPB-master/tests/integration_tests/correct/all_diff.opb")

# ******************************************************************************
# file parsing


# since .opb files allow constants that either look like
# +x or -x or just simply x
def is_num(lit):
    if lit.isdigit(): # just x
        return (True, int(lit))
    elif lit[0] == '+' and lit[1:].isdigit(): # +x
        return (True, int(lit[1:]))
    elif lit[0] == '-' and lit[1:].isdigit(): # -x
        return (True, -int(lit[1:]))
    else: # variable looking like [char][num], return the num as well
        return (False, int(lit[1:]))


# called upon seeing the "f" rule
# loads the initial starting clauses in the .opb file
# we treat all <= constraints as negated >= constraints
def load_clauses(opb_file_name):
    opb_file = open(opb_file_name, "r")
    nvars = 0
    clause_idx = 1
    for line in opb_file:
        if (line[0] == '*'): # comment line
            line = line.split()
            nvars = int(line[2]) # relies on .opb file having '#variables= [nvars]' in header
            continue
        else: # non-comment
            line = trim(line)[:-1] #removes newlines, semicolon
            lits = line.split()

            list = [0] * (nvars + 1) # initialize clause to all 0s

            # find the operator index
            try:
                v1 = lits.index(">=")
            except ValueError:
                v1 = -1

            try:
                v2 = lits.index("<=")
            except ValueError:
                v2 = -1

            op_idx = max(v1, v2)

            if (op_idx < 0): # neither >= or <=
                raise PbpException("formula has neither >= nor <=")
                

            if (v2 > 0): # you have a <=
                list[0] = -int(lits[op_idx + 1]) # choosing >= as default, so have to negate
            else:
                list[0] = int(lits[op_idx + 1])

            cv = lits[:op_idx]
            for i in range(len(cv)):
                lit = cv[i]
                (b, idx) = is_num(lit)
                if b: # parsed element is a coefficient
                    v = cv[i + 1] # get the var associated with coeff
                    (b2, idx2) = is_num(v) # get the underlying var idx
                    if (v2 > 0): # you have a <=
                        list[idx2] = -idx
                    else:
                        list[idx2] = idx
                        
            clauses[clause_idx] = list
            clause_maps[clause_idx] = clause_idx # instantiate clause maps as identity
            clause_idx += 1

    shell_print("Done loading clauses from {0}".format(opb_file_name))
    return

# ******************************************************************************
# polish arithmetic processing

def multiply(arg1, arg2):
    clause = clauses[arg1]
    newclause = [0] * len(clause)
    for i in range(len(clause)):
        newclause[i] = clause[i] * arg2

    return (newclause, [])
    
def sum(arg1, arg2):
    clause1 = clauses[arg1]
    clause2 = clauses[arg2]
    newclause = [0] * len(clause1)
    for i in range(len(clause1)):
        newclause[i] = clause1[i] + clause2[i]

    return (newclause, [arg1, arg2])

def divide(arg1, arg2):
    clause = clauses[arg1]
    newclause = [0] * len(clause)
    for i in range(len(clause)):
        newclause[i] = int(math.ceil(clause[i] / arg2))

    return (newclause, [arg1])

def saturate(arg):
    clause = clauses[arg]
    newclause = [0] * len(clause)
    for i in range(len(clause)):
        d = math.gcd(*[n for n in clause[1:] if n])
        newclause[i] = int(math.ceil(clause[i] / d))

    return (newclause, [])


def calculate(op, arg1, arg2):
    if op == "+":
        return sum(arg1, arg2)
    elif op == "*":
        return multiply(arg1, arg2)
    elif op == "d":
        return divide(arg1, arg2)
    elif op == "s":
        return saturate(arg1)
    else:
        raise PbpException("invalid operation: %s" % op)
    
# performs operation (adding new clause) and tracking new clause's dependencies
def polish(line):
    
    dops = ["+", "*", "d"]
    sops = ["s"]
    numstack = Stack()
    lits = line.split()
    for lit in lits:
        if lit in dops: # we found an operator
            arg2 = numstack.pop()
            arg1 = numstack.pop()
            shell_print("c Calling {0} on {1} and {2}".format(lit, arg1, arg2))

            (newclause, d) = calculate(lit, arg1, arg2)
#           shell_print("new clause %s" % arg1 + ": " + str(newclause))
            if d == []:
                # multiplication
                numstack.push(arg1)
            else:
                e = [key for (key, value) in deps.items() if value == d]
                if (len(e) > 0):
                    existing_dep = e[0]
                    numstack.push(existing_dep)
                    continue
                
                global nclause
                nclause += 1

                clauses[nclause] = newclause

                try:
                    deps[nclause]
                except KeyError:
                    deps[nclause] = d
                    shell_print("c Assigned {0} dependency {1}".format(nclause, d))

                numstack.push(nclause)

        elif lit in sops:
            arg = numstack.pop()
            (newclause, dep) = calculate(lit, arg, None)
            clauses[arg] = newclause
        else:
            numstack.push(clause_maps[int(lit)])

    global prev_nclause
    prev_nclause += 1
    clause_maps[prev_nclause] = nclause


# ******************************************************************************
# parsing pbp/opb files, dispatching on load/polish, final output

def readPbp(pbp_file_name, opb_file_name):
    pbp_file = open(pbp_file_name, "r")
    
    lineNumber = 0
    clauseCount = 0
    
    for line in pbp_file:
        lineNumber += 1
        if lineNumber == 1:
            continue
        else:
            line = trim(line)
        if len(line) == 0:
            continue
        fields = line.split()
        if len(fields) == 0:
            continue
        elif line[0] == '*': # comment line - don't care
            continue
        elif line[0] == 'f': # load original constraints from opb file
            load_clauses(opb_file_name)
            n = int(line[2])
            global nInitclauses
            nInitclauses += n
            global nclause
            nclause += n
            global prev_nclause
            prev_nclause += n
        elif line[0] == 'p': # polish rule: do the actual math
            polish(line[1:])
        elif line[0] == 'e': # equality rule: e [id] [c] | check if [id] equals the clause [c]
            # [fill in] - optional, continuing for now
            continue
        elif line[0] == 'i': # implication rule: i [id] [new] | [id] ==> [new]
            # [fill in] - optional, continuing for now
            continue
        elif line[0] == 'j': # (other) implication rule: j [id] [new] | [id] ==> [new]
            # [fill in] - optional, continuing for now
            continue        
        elif line[0] == 'c': # contradiction: c [id] | check if clause [id] is a contradiction
            final_print()
            # print_all()
            break
        else:
            raise PbpException("Unsupported proof rule {0} at line {1} - Occurs in context {2} in file {3}".format(line[0], lineNumber, line, pbp_file_name))
                
    shell_print("Done parsing proof file {0}".format(pbp_file_name))
        
def run(argv):
    shell_print("---------------------------")
    shell_print("Pbp2PBIP: VeriPB --> Pseudo-Boolean Implication Proof format conversion")
    shell_print("updated 10/18/2022")
    shell_print("Author: Karthik Nukala")
    shell_print("Affiliation: Carnegie Mellon University")
    shell_print("---------------------------")
    pbp_file = ""
    opb_file = ""
    output_file = ""
    global verbosity
    arg_help = argv[0] + " --pbp_file [path to .pbp/.veripb file] --opb_file [path to .opb file] --output_file [path to output file] --help"

    try:
        opts, args = getopt.getopt(argv[1:], "", longopts=["pbp_file=", "opb_file=", "output_file=", "help"])
    except getopt.GetoptError as err:
        shell_print(err)
        shell_print(arg_help)
        sys.exit(2)

    for o, a in opts:
        if o in ("--help"):
            shell_print(arg_help)
            sys.exit()
        elif o in ("--output_file"):
            output_file = a
            f = open(output_file, 'w+')
            sys.stdout = f
        elif o in ("--pbp_file"):
            pbp_file = a
        elif o in ("--opb_file"):
            opb_file = a
        else:
            shell_print(arg_help)
            sys.exit()

    readPbp(pbp_file, opb_file)

    if output_file != "":
        shell_print("Output printed to {0}".format(output_file))


if __name__ == "__main__":
     run(sys.argv)
