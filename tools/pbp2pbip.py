import sys
import argparse

from PBConstraint import PBConstraint
from DeriveClause import get_clause
from NumberRetriever import NumberRetriever
from RPN import rpn

constraints = []
hints = []

obj_constraints = set()

nvars = 0

obj_fn = []

clause_expansions = []

nclauses = 0

ninputs = 0

nr = NumberRetriever()

def isVar(tok):
    flag = False
    for i in range(len(tok)):
        if flag:
            if (len(tok[i:]) == 0):
                return True
            return tok[i:].isdigit()
        if tok[i].isalpha():
            continue
        else:
            flag = True

    return True

def isVarNeg(tok):
    if(tok[0] == '~'):
        return isVar(tok[1:])

def str_to_constraint(line):
    term_list = []
    toks = line.split(" ")
    for i in range(0, len(toks), 2):
        if (toks[i] in ['>=', '<=', '>', '<', '=']):
            constraint_type = toks[i]
            rhs_constant = int(toks[i + 1])
            c = PBConstraint(term_list, rhs_constant, constraint_type)
            return c

                
        c = toks[i]
        v = toks[i + 1]
                
        try:
            n = int(toks[i])
        except:
            print("Error! expected coeff but got " + toks[i])
            break
        
        if (isVar(v) or isVarNeg(v)):
            term_list.append((v, n))
        else:
            print("Error! expected variable but got % " + v)
            break
    

# creates overall PBFormula having read in starting constraints
# from opb_file
def loadFile(opb_file):
    f = open(opb_file, "r")

    clause_idx = 0
    for line in f:
        term_list = []
        toks = line.split(" ")
        if toks[0] == '*':
            global nvars
            nvars = int(toks[2])
        elif toks[0] == 'min:':
            global obj_fn
            obj_fn = [0] * (nvars + 1)
            tok_idx = 1
            for i in range(1, nvars + 1):
                obj_fn[i] = toks[tok_idx]
                tok_idx += 2
        else:
            clause_idx += 1
            c = str_to_constraint(line)
            constraints.append(c)
            hints.append(";")
            
            global nr
            nr.process_line(clause_idx, 1)
            
            clause_expansions.append((clause_idx, 1))

    global nclauses
    nclauses = clause_idx

    
    global ninputs
    ninputs = clause_idx
    
    
    '''for i in range(len(constraints)):
        print("Constraint " + str(i + 1) + ": " + str(constraints[i]))'''
                    
                    

# parses a "p" rule, corresponding to the polish notation arithmetic
# can do this with a simple stack machine?
def parseP(line):
    # for each clause we add, create a mapping between old clause ids
    # and new clause ids

    global nclauses
    global clause_expansions
    nclauses += 1
    total = 0
    #print("COUNTING: " + str(line))
    for tok in line:
        if tok == '+':
            total += 1
        elif tok == 'd':
            total += 1
            
    clause_expansions.append((nclauses, total))
    global nr
    nr.process_line(nclauses, total)

    global constraints
    new_clauses = rpn(line, constraints, nr.get_reference, len(constraints) + 1)

    for (clauses, hint) in new_clauses:
        constraints.append(clauses)
        hints.append(hint)
    
    return

# parses an "o" rule, corresponding to the reverse unit propagation
def parseU(constraint):

    global nclauses
    global clause_expansions
    global nr

    (status, new_clauses) = get_clause(constraints, constraint)

    l = len(new_clauses)
    nclauses += 1
    #print(get_clause(constraints, constraint))


    c = []
    if status:
        clause_expansions.append((nclauses, l))

        for (clause, hint) in new_clauses:
            c.append(clause)
            #print("                             C: ", clause, hint)
            constraints.append(clause)
            hints.append(hint)
            

        nr.process_line(nclauses, l)
        
    return


# the main "driver function"
# reads each line of the proof and dispatches to relevant helpers
#
# main helpers are
# - parseP(line): polish notation arithmetic
# - parseU(line): reverse unit propagation
# all others (w, o, etc) should be dealt with here
def parseProof(veripb_file):
    f = open(veripb_file, "r")
    linenum = 1
    for line in f:
        if linenum == 1:
            linenum += 1
            continue
        else:
            linenum += 1
            toks = line.rstrip().split(" ")
            command = toks[0]
            
            if command == '#': # comment
                #print("comment")
                continue
            elif command == 'f': # load clauses from file
                #print("load")
                continue # dealt with in main
            elif command == 'o': # optimization rule (pre-processing)
                #print("o - adding new optimization constraint")
                assn = toks[1:]

                found_size = 0
                term_list = []
                for a in assn:
                    if a[0] == '~':
                        term_list.append((a[1:].rstrip(), 1))
                        continue
                    else:
                        term_list.append((a.rstrip(), 1))
                        found_size += 1

                new_rhs = found_size + 1

                global constraints
                    
                c = PBConstraint(term_list, new_rhs, ">=")
                #print("new constraint: " + str(c))
                constraints.append(c)
                global obj_constraints
                obj_constraints.add(len(constraints) - 1)
                hints.append(";")
                
                global nr
                global nclauses
                nclauses += 1
                nr.process_line(nclauses, 1)
                continue
            elif command == 'u': # rup
                c = str_to_constraint(line[2:-2])
                #print("RUP: " + str(c))
                parseU(c)
            elif command == 'w': # clear, don't care
                #print("clear")
                continue
            elif command == 'p': # polish notation arithmetic
                #print("arithmetic: " + str(toks))
                parseP(toks[1:])
            elif command == 'c':
                #print("done")
                break
    return
        

# after parsing and processing, prints out the proof augmented with
# the necessary hints
def printHints(output_file):
    return


def main():
    parser = argparse.ArgumentParser()

    parser.add_argument('--opb', type=str, required=True)
    parser.add_argument('--pbp', type=str, required=True)
    parser.add_argument('--o', type=str, required=True)

    args = parser.parse_args()

    print("Opening " + args.opb)
    loadFile(args.opb)
    print("Loaded " + str(len(constraints)) + " constraints from " + args.opb)
    print("Number of variables: " + str(nvars))
    print("Number of input clauses: " + str(nclauses))
    # print("Objective: " + str(obj_fn))

    parseProof(args.pbp)

    n = len(constraints)

    with open(args.o, 'x') as f:
        for i in range(n):
            # constraints[i].var_normalised().pbip_output_format()
            global ninputs
            if i < ninputs or i in obj_constraints:
                print("i", end=' ', file=f)
            else:
                print("a", end=' ', file=f)
            # constraints[i].var_normalised().pbip_output_format()
            print(constraints[i].pbip_output_format(), end='; ', file=f)
            if type(hints[i]) == type([4, 5]) or type(hints[i]) == type((4, 5, 5)):
                for hint in hints[i]:
                    if hint == "prev":
                        # print("prev", end=' ', file=f)
                        print(i, end=' ', file=f)
                    else:
                        print(hint, end=' ', file=f)
            elif type(hints[i]) == type(5):
                print(hints[i], end=' ', file=f)
            print("", file=f)

    #print(clause_expansions)
#    printHints(args.o)
    

if __name__ == "__main__":
    main()

