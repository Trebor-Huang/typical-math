from unification.basics import *


class Constraint:
    def __init__(self, lhs, rhs=None):
        if rhs is None:
            lhs, rhs = lhs
        self.eq = (lhs, rhs)
        self.lhs = lhs
        self.rhs = rhs

    def __getitem__(self, i):
        return self.eq[i]

    def __repr__(self):
        return str(self[0]) + " == " + str(self[1])


class UnificationException(Exception):
    pass


class OccursCheckException(UnificationException):
    def __init__(self, equation):
        self.equation = equation

    def __str__(self):
        return "Occurs Check failed: " + str(self.equation)


class ConflictException(UnificationException):
    def __init__(self, equation):
        self.equation = equation

    def __str__(self):
        return "Conflicting equation: " + str(self.equation)


def substitute(constraints, var, subs):
    return [Constraint(l.substitute(var, subs), r.substitute(var, subs)) for l, r in constraints]


def unify(constraints, verbose=False):
    # This algorithm comes from
    # https://en.wikipedia.org/wiki/Unification_(computer_science)#A_unification_algorithm
    solutions = []
    while constraints:
        c = constraints.pop()
        if verbose:
            print("Current Equations State:\n" + "\n".join([str(e) for e in constraints])
                  + "\n+++++++++++++++++++\n" + str(c) + "\n")
        if c[0] == c[1]:  # DELETE
            continue
        elif isinstance(c[0], Function) and isinstance(c[1], Function):
            if c[0].constructor == c[1].constructor:  # DECOMPOSE
                constraints.extend(map(Constraint, zip(c[0].args, c[1].args)))
            else:  # CONFLICT
                return ConflictException(c)
        elif isinstance(c[0], Function) and isinstance(c[1], Variable):  # SWAP
            constraints.append(Constraint(c[1], c[0]))
        elif isinstance(c[1], Expression) and isinstance(c[0], Variable):
            if c[0] not in c[1].variables():  # ELIMINATE
                constraints = substitute(constraints, c[0], c[1])
                solutions = substitute(solutions, c[0], c[1])
                # constraints.insert(0, c)
                solutions.append(c)
            else:  # OCCURS CHECK
                raise OccursCheckException(c)
    return solutions


def constr(name, arity):
    return Constructor(name, arity)


def vriabl(name):
    return Variable(name)


if __name__ == "__main__":
    f = constr("f", 1)
    c = constr("c", 0)
    g = constr("g", 2)
    x = vriabl("x")
    y = vriabl("y")
    z = vriabl("z")

    expr = g(f(x), g(c(), y))
    eqs = [Constraint(expr, z), Constraint(f(y), f(g(x, c())))]
    sl = unify(eqs, True)
    print(sl)
    input("Paused...")

    eqs = [Constraint(x, y), Constraint(y, f(x))]
    try:
        sl = unify(eqs, True)
    except OccursCheckException as e:
        print(e)

    eqs = [Constraint(x, y), Constraint(y, z)]
    print(unify(eqs, True))
