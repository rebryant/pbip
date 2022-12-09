
from PBConstraint import *

def get_clause(clause_history, target_clause):
    negated_target = target_clause.negated().constraint_normalised().coeff_normalised()

    up_sequence = PBConstraint([], 0, ">=")

    '''print("HISTORY:")
    for x in clause_history:
        print(x)
    print("END HISTORY")'''

    considered_clauses = []
    for clause in clause_history:
        considered_clauses.append(clause.constraint_normalised().coeff_normalised().copy())
    considered_clauses.append(negated_target)
    #print(negated_target)
    #print("END LIST")

    partial_ups = []
    up_source = []

    while True:

        idx = 0

        for clause in considered_clauses:
            if clause.unsat():
                # print("upseq: ", partial_ups)
                # print("upsrc: ", up_source)
                # print("unsat clause: ", clause)
                # print("unsat clause idx: ", idx)

                resulting_additions = []

                ulen = len(partial_ups)

                first = True

                for x in range(ulen-1, -1, -1):
                    wherefrom = []
                    if first:
                        wherefrom = [idx + 1]
                        first = False
                    else:
                        wherefrom = [up_source[x+1][1], "prev"]
                    resulting_additions.append((partial_ups[x].negated().constraint_normalised().coeff_normalised(), wherefrom))

                resulting_additions.append((target_clause, ["prev"]))

                '''for x in resulting_additions:
                    print(x)'''

                return (True, resulting_additions)
            up_able = clause.get_up_able()
            if len(up_able) != 0:
                new_known = up_able[0]
                new_up_sequence = up_sequence.copy()
                new_up_sequence.add_to_rhs(1)
                new_up_sequence.add_variable(new_known, 1)
                up_sequence = new_up_sequence
                partial_ups.append(new_up_sequence)
                up_source.append((new_known, idx))

                for i in range(len(considered_clauses)):
                    considered_clauses[i] = considered_clauses[i].subs(new_known, 1)

                break
            idx += 1

        if idx == len(considered_clauses):
            return (False, [])
    return (False, [])

    

clause_1 = PBConstraint([("x1", 1), ("x2", 2), ("~x3", 1)], 2, '>=')
clause_2 = PBConstraint([("~x1", 1), ("~x2", 1), ("x3", 2)], 2, '>=')
clause_3 = PBConstraint([("x1", 1), ("~x2", 2), ("x3", 2)], 3, '>=')

target_clause = PBConstraint([("x1", 2), ("x2", 1), ("x3", 1)], 2, '>=')
'''
print("t: ", target_clause)
print("Negating:")
print("n: ", target_clause.negated())
print("c: ", target_clause.negated().constraint_normalised())
print("nc: ", target_clause.negated().constraint_normalised().coeff_normalised())
'''

'''
#print(get_clause(
    [clause_1, clause_2, clause_3],
    target_clause
))
'''

'''

final failing assignment | final conflicting clause for the assignment
previous partial assignments (#k) | (previous clause), (what clause caused UP from this to previous assignment?)
... (#(k-1))
...
target clause | previous clause only

'''
