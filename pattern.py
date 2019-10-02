from abt import *


def merge_dicts(*res):
    """Merges two dictionaries and check if they are consistent."""
    ans = dict()  # TODO: maybe more elegant?
    for r in res:
        for k in r:
            if k in ans and ans[k] != r[k]:
                raise ValueError("Inconsistent substitution.")
            ans[k] = r[k]
    return ans


class MetaVariable(ABT):
    def __init__(self, name, sort):
        self.name = str(name)
        self.sort = sort
        self._hash = hash(self.name) ^ hash(self.sort) ^ id(self)

    def __repr__(self):
        return self.name

    def __hash__(self):
        return self._hash

    def FV(self):
        return set()

    def substitute(self, var, expr):
        if self is var:
            return expr
        return self


def match(expr: ABT, pattern: ABT):
    try:
        if expr.sort != pattern.sort:
            raise ValueError("Sort mismatch.")
        elif isinstance(pattern, MetaVariable):
            return {pattern: expr}
        elif type(expr) == type(pattern) == Variable:
            return dict()
        elif type(expr) == type(pattern) == AST:
            if expr.node == pattern.node:
                return merge_dicts(*map(match, expr.args, pattern.args))
            else:
                raise ValueError("Node mismatch.")
        elif type(expr) == type(pattern) == Bind:
            return match(expr.expr.substitute(expr.bv, pattern.bv), pattern.expr)
        else:
            raise ValueError("Node type mismatch.")
    except ValueError as e:
        raise ValueError("Match failed: inconsistent.")


def unify(constraints, verbose=False):
    """Unification of metavariables."""
    print("[UNIFY]", constraints)
    solutions = []
    while constraints:
        c = constraints.pop()
        if verbose:
            print("Current Equations State:\n" + "\n".join([str(e) for e in constraints])
                  + "\n+++++++++++++++++++\n" + str(c) + "\n")
        if c[0] == c[1]:  # DELETE
            pass
        elif isinstance(c[0], AST) and isinstance(c[1], AST):
            if c[0].node == c[1].node:  # DECOMPOSE
                constraints.extend(zip(c[0].args, c[1].args))
            else:  # CONFLICT
                raise ValueError("Unification failed: conflict.")
        elif isinstance(c[0], Bind) and isinstance(c[1], Bind):  # DECOMPOSE-Alt
            constraints.append((c[0].expr, c[1].expr.substitute(c[1].bv, c[0].bv)))
        elif isinstance(c[0], ABT) and isinstance(c[1], MetaVariable) and not isinstance(c[0], MetaVariable):  # SWAP
            constraints.insert(0, (c[1], c[0]))
        elif isinstance(c[1], ABT) and isinstance(c[0], MetaVariable):
            if c[0] not in get_metavariables(c[1]):  # ELIMINATE
                constraints = [(subs_metavariables(cnl, {c[0]: c[1]}),
                                subs_metavariables(cnr, {c[0]: c[1]})) for cnl, cnr in constraints]
                solutions = [(subs_metavariables(sll, {c[0]: c[1]}),
                              subs_metavariables(slr, {c[0]: c[1]})) for sll, slr in solutions]
                # constraints.insert(0, c)
                solutions.append(c)
            else:  # OCCURS CHECK
                raise ValueError("Unification failed: occurs check.")
        else:  # OTHER, must be conflict since c[0] != c[1]
            raise ValueError("Unification failed: conflict.")
    return {p: q for p, q in solutions}


def get_metavariables(expr: ABT):
    if isinstance(expr, MetaVariable):
        return {expr: expr.sort}
    elif isinstance(expr, AST):
        return merge_dicts(*(get_metavariables(c) for c in expr.args))
    elif isinstance(expr, Bind):
        return get_metavariables(expr.expr)
    else:
        return dict()


def subs_metavariables(expr:ABT, ass:dict):
    if isinstance(expr, MetaVariable) and expr in ass:
        return ass[expr]
    elif isinstance(expr, AST):
        return expr.node(*(subs_metavariables(a, ass) for a in expr.args))
    elif isinstance(expr, Bind):
        return Bind(expr.bv, subs_metavariables(expr.expr, ass))
    else:
        return expr


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

    OpOeO = eq(plus(zero(), zero()), zero())
    xe0_i_xp0e0 = Bind(x, impl(eq(x, zero()), eq(plus(x, zero()), zero())))

    phi_i_Tp0e0 = Bind(y, impl(phi, eq(plus(T, zero()), zero())))
    phi_i_TpTe0 = Bind(y, impl(phi, eq(plus(T, T), zero())))
    print(xe0_i_xp0e0.sort, phi_i_Tp0e0.sort)

    print(match(xe0_i_xp0e0, phi_i_Tp0e0))
    print(unify([(xe0_i_xp0e0, phi_i_Tp0e0)]))
    try:
        print(unify([(xe0_i_xp0e0, phi_i_TpTe0)], True))
    except ValueError as v:
        print("Failed!")

    print(get_metavariables(phi_i_Tp0e0))

