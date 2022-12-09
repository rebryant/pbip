import copy

neg_token = '~'

def is_negated(literal):
    assert(len(literal) > 0)
    if literal[0] == neg_token:
        return True
    return False

def negate_literal(literal):
    assert(len(literal) > 0)
    if is_negated(literal):
        return literal[1:]
    return neg_token + literal

def negate_constraint(constraint):
    if constraint == '<':
        return '>='
    if constraint == '>':
        return '<='
    if constraint == '<=':
        return '>'
    if constraint == '>=':
        return '<'
    assert(False) # constraint is =, which our representation does not allow for.

def coefficient_format(x):
    if x < 0:
        return str(x)
    assert(x != 0)
    return '+' + str(x)

class PBConstraint():

    def _setup_constraint(self, term_list, rhs_value, constraint_type):
        self.coefficients = {}
        for (term, coeff) in term_list:
            self.coefficients[term] = coeff
        self.constraint = constraint_type
        self.rhs = rhs_value

    def __init__(self, term_list, rhs_value, constraint_type):
        self._setup_constraint(term_list, rhs_value, constraint_type)

    def to_basic_rep(self):
        term_list = []
        for (term, coeff) in self.coefficients.items():
            term_list.append((term, coeff))
        return (term_list, self.rhs, self.constraint)

    def get_coeff(self, var):
        if var in self.coefficients:
            return self.coefficients[var]
        return 0
    
    def __repr__(self):
        coeffs = list(self.coefficients.items())
        s = ""
        if (len(coeffs) == 0):
            s = "<Nothing>"
        for i in range(len(coeffs)):
            var, coeff = coeffs[i]
            s += str(coeff) + "*(" + str(var) + ")"
            if i + 1 != len(coeffs):
                s += " + "
        s += " " + self.constraint + " "
        s += str(self.rhs)
        return s

    def __str__(self):
        return self.__repr__()

    def set_rhs_value(self, value):
        self.rhs = value

    def add_to_rhs(self, value):
        self.rhs += value

    def normalise(self, var):
        mvar = negate_literal(var)
        if var in self.coefficients:
            if self.coefficients[var] == 0:
                self.coefficients.pop(var, None)
        if mvar in self.coefficients:
            if self.coefficients[mvar] == 0:
                self.coefficients.pop(mvar, None)
        if var not in self.coefficients:
            return
        if mvar not in self.coefficients:
            return
        lesser = min(self.coefficients[var], self.coefficients[mvar])
        self.coefficients[var] -= lesser
        self.coefficients[mvar] -= lesser
        self.add_to_rhs(-lesser)
        if self.coefficients[var] == 0:
            self.coefficients.pop(var, None)
        if self.coefficients[mvar] == 0:
            self.coefficients.pop(mvar, None)

    def add_variable(self, var, coeff):
        if var in self.coefficients:
            self.coefficients[var] += coeff
        else:
            self.coefficients[var] = coeff
        self.normalise(var)

    def set_coeff(self, var, new_coeff):
        self.coefficients[var] = new_coeff
        self.normalise(var)
            
    def coeff_normalised(self): # all coeffs should be positive, even if the vars themselves are negative
        vars = []
        for (var, coeff) in self.coefficients.items():
            vars.append(var)
        for var in vars:
            self.normalise(var)
        var_list = []
        new_rhs = self.rhs
        new_constraint = self.constraint
        for (var, coeff) in self.coefficients.items():
            if coeff == 0:
                pass
            if coeff > 0:
                var_list.append((var, coeff))
            else:
                var_list.append((negate_literal(var), -coeff))
                new_rhs -= coeff
        return PBConstraint(var_list, new_rhs, new_constraint)

    def variable_normalised(self):
        for (var, coeff) in self.coefficients.items():
            self.normalise(var)
        var_list = []
        new_rhs = self.rhs
        new_constraint = self.constraint
        for (var, coeff) in self.coefficients.items():
            if coeff == 0:
                pass
            if not is_negated(var):
                var_list.append((var, coeff))
            else:
                var_list.append((negate_literal(var), -coeff))
                new_rhs -= coeff
        return PBConstraint(var_list, new_rhs, new_constraint)

    def constraint_normalised(self):
        if self.constraint == '>=':
            term_list, rhs, constraint = self.to_basic_rep()
            return PBConstraint(term_list, rhs, '>=')
        if self.constraint == '<=':
            term_list, rhs, constraint = self.to_basic_rep()
            new_term_list = []
            for (var, coeff) in term_list:
                new_term_list.append((var, -coeff))
            rhs *= -1
            return PBConstraint(new_term_list, rhs, '>=')
        if self.constraint == '>':
            term_list, rhs, constraint = self.to_basic_rep()
            rhs += 1
            return PBConstraint(term_list, rhs, '>=')
        if self.constraint == '<':
            term_list, rhs, constraint = self.to_basic_rep()
            new_term_list = []
            for (var, coeff) in term_list:
                new_term_list.append((var, -coeff))
            rhs *= -1
            rhs += 1
            return PBConstraint(new_term_list, rhs, '>=')
        assert(False)

    def get_constraint(self):
        return self.constraint

    def negated(self):
        (term_list, rhs, constraint) = self.to_basic_rep()
        new_constraint = negate_constraint(constraint)
        return PBConstraint(term_list, rhs, new_constraint)

    def subs(self, var, val):
        nvar = negate_literal(var)
        rhs_delta = 0
        coeffs = copy.deepcopy(self.coefficients)
        if var in coeffs:
            coeff = coeffs[var]
            sum_contribution = coeff * val
            rhs_delta -= sum_contribution
            coeffs.pop(var, None)
        if nvar in coeffs:
            coeff = coeffs[nvar]
            sum_contribution = coeff * (1 - val)
            rhs_delta -= sum_contribution
            coeffs.pop(nvar, None)
        (xl, rhs, constraint) = self.to_basic_rep()
        rhs += rhs_delta
        terms = []
        for (var, coeff) in coeffs.items():
            terms.append((var, coeff))
        return PBConstraint(terms, rhs, constraint)

    def get_up_able(self):
        # Assumes that we are in coefficient normalised form.
        sum_coeffs = 0
        up_able = []
        for (var, coeff) in self.coefficients.items():
            sum_coeffs += coeff
        for (var, coeff) in self.coefficients.items():
            if sum_coeffs - coeff < self.rhs:
                up_able.append(var)
        return up_able

    def __add__(self, other):
        def add_constraints(constraint_a, constraint_b):
            if constraint_a.get_constraint() != constraint_b.get_constraint():
                raise ValueError("Mismatched constraint types")
            (term_list, rhs, constraint) = constraint_a.to_basic_rep()
            new_constraint = PBConstraint(term_list, rhs, constraint)
            (term_list, rhs, constraint) = constraint_b.to_basic_rep()
            new_constraint.add_to_rhs(rhs)
            for (var, coeff) in term_list:
                new_constraint.add_variable(var, coeff)
            return new_constraint
        return add_constraints(self, other)

    def multiply(self, constant):
        f = self.to_basic_rep()
        term_list, rhs_value, constraint_type = f
        new_term_list = []
        rhs_value *= constant
        for (term, coeff) in term_list:
            new_term_list.append((term, coeff * constant))
        return PBConstraint(new_term_list, rhs_value, constraint_type)

    def divide(self, constant):
        f = self.to_basic_rep()
        new_term_list = []
        term_list, rhs_value, constraint_type = f
        rhs_value = (rhs_value + constant - 1) // constant
        for (term, coeff) in term_list:
            new_term_list.append((term, coeff // constant))
        return PBConstraint(new_term_list, rhs_value, constraint_type)

    def saturate(self):
        f = self.to_basic_rep()
        new_term_list = []
        term_list, rhs_value, constraint_type = f
        for (term, coeff) in term_list:
            new_term_list.append((term, min(coeff, rhs_value)))
        return PBConstraint(new_term_list, rhs_value, constraint_type)

    def unsat(self):
        sum_coeffs = 0
        for (v, c) in self.coefficients.items():
            sum_coeffs += c
        return sum_coeffs < self.rhs

    def copy(self):
        (li, rhs, co) = self.to_basic_rep()
        return PBConstraint(li, rhs, co)

    def pbip_output_format(self):
        st = ""
        (term_list, rhs_value, cons) = self.to_basic_rep()
        for (term, coeff) in term_list:
            st += coefficient_format(coeff)
            st += ' '
            st += term
            st += ' '
        st += cons
        st += ' '
        st += str(rhs_value)
        st += ' '
        return st
    
