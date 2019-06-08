from abt import *


def _merge_dicts(*dicts):
    return {k:v for d in dicts for k,v in d.items()}


class MetaVariable(ABT):
    def __init__(self, name, sort):
        self.name = str(name)
        self.sort = sort
        self._hash = hash(self.name) ^ hash(self.sort)

    def __repr__(self):
        return self.name

    def __hash__(self):
        return self._hash

    def FV(self):
        return set()


def match(expr: ABT, pattern: ABT):
    if expr.sort != pattern.sort:
        raise ValueError("Sort mismatch.")
    elif isinstance(pattern, MetaVariable):
        return {pattern: expr}
    elif type(expr) == type(pattern) == Variable:
        return dict()
    elif type(expr) == type(pattern) == AST:
        if expr.node == pattern.node:
            return _merge_dicts(*map(match, expr.args, pattern.args))
        else:
            raise ValueError("Node mismatch.")
    elif type(expr) == type(pattern) == Bind:
        return match(expr.expr.substitute(expr.bv, pattern.bv), pattern.expr)
    else:
        raise ValueError("Node type mismatch.")
    

if __name__ == "__main__":
    wff = PrimitiveSort("wff")
    term = PrimitiveSort("term")

    zero = Node("0", term, ())
    plus = Node("+", term, (term, term))
    eq = Node("=", wff, (term, term))
    impl = Node("->", wff, (wff, wff))

    x = Variable("x", term)
    y = Variable("y", term)
    phi = MetaVariable("phi", wff)
    T = MetaVariable("T", term)

    OpOeO = eq(plus(zero(), zero()))
    xe0_i_xp0e0 = Bind(x, impl(eq(x, zero()), eq(plus(x, zero()), zero())))

    phi_i_Tp0e0 = Bind(y, impl(phi, eq(plus(T, zero()), zero())))
    print(xe0_i_xp0e0.sort, phi_i_Tp0e0.sort)

    print(match(xe0_i_xp0e0, phi_i_Tp0e0))

