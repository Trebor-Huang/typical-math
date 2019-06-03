# For abstract syntax trees and abstract binding trees.
# from functools import lru_cache


class Sort:
    def __repr__(self):
        return "Sort"

    def __hash__(self):
        return 0

    def __eq__(self, other):
        return self is other


class PrimitiveSort(Sort):
    def __init__(self, name: str):
        self.name = name
        self._hash = hash(name)
        self._repr = name

    def __hash__(self):
        return self._hash

    def __eq__(self, other):
        return isinstance(other, PrimitiveSort) and self.name == other.name

    def __repr__(self):
        return self._repr


class BindingSort(Sort):
    def __init__(self, var_sort, body_sort):
        self.var_sort = var_sort
        self.body_sort = body_sort
        self._hash = hash(var_sort) ^ hash(body_sort)
        self._repr = f"({repr(var_sort)}).{repr(body_sort)}"

    def __hash__(self):
        return self._hash

    def __eq__(self, other):
        return isinstance(other, BindingSort) and self.var_sort == other.var_sort and self.body_sort == other.body_sort

    def __repr__(self):
        return self._repr


class ABT:
    def __init__(self):  # For sub-typing hints
        self.sort = Sort()
        raise ValueError("ABT is an abstract class")

    def __repr__(self):
        return "ABT"

    def __hash__(self):
        return 0

    def substitute(self, var, expr):
        return self

    def __eq__(self, other):
        return self is other

    def FV(self):
        return set()


class Node:
    def __init__(self, name, sort, args):
        self.sort = sort
        self.name = name
        self.args = args  # A tuple of sorts
        self._hash = hash(self.sort) ^ hash(self.name) ^ hash(self.args)

    def __hash__(self):
        return self._hash

    def __call__(self, *args):
        return AST(self, args)


class AST(ABT):
    """An AST Node."""
    def __init__(self, node: Node, args: tuple):
        assert isinstance(node, Node)
        self.node = node
        self.sort = node.sort
        if not all(map(lambda t: t[0].sort == t[1], zip(args, node.args))):
            raise ValueError("Sort mismatch.")
        self.args = args
        self._repr = f"{self.node.name}({', '.join(map(str, self.args))})"
        self._hash = hash(self.node) ^ hash(self.args)
        self._FV = set.union(*(e.FV() for e in self.args), set())

    def __repr__(self):  # TODO: leave room for syntax output sugars
        return self._repr

    def __hash__(self):
        return self._hash

    def substitute(self, var, expr):
        return self.node(*(e.substitute(var, expr) for e in self.args))

    def __eq__(self, other):
        return isinstance(other, AST) and self.node == other.node and self.args == other.args

    def FV(self):
        return self._FV


class Variable(ABT):
    def __init__(self, ident, sort, name=None):
        self.sort = sort
        self.ident = ident
        self.name = str(ident) if name is None else str(name)
        self._hash = hash(self.sort) ^ hash(self.ident) ^ hash(self.name)

    def __repr__(self):
        return self.name

    def __hash__(self):
        return self._hash

    def substitute(self, var, expr):
        return self if var != self else expr

    def __eq__(self, other):
        return isinstance(other, Variable) and self.sort == other.sort and self.ident == other.ident \
               and self.name == other.name

    def FV(self):
        return {self}


class Bind(ABT):
    def __init__(self, var, expr: ABT):
        self._hash = 0
        self.bv = Variable(self, var.sort, var.name)
        self.expr = expr.substitute(var, self.bv)
        self.sort = BindingSort(var.sort, expr.sort)
        self._FV = self.expr.FV() - {self.bv}
        self._hash = hash(self.expr)  # TODO: Might this actually *be* alpha-invariant? Test!
        self._repr = "(" + repr(self.bv) + ")." + repr(self.expr)

    def __repr__(self):
        return self._repr

    def __hash__(self):
        return self._hash

    def substitute(self, var, expr):
        if var == self.bv:
            raise ValueError("Name collision (normally will not happen unless you jinx stuff).")
        return Bind(self.bv, expr.substitute(var, expr))

    def __eq__(self, other):
        return isinstance(other, Bind) and self.expr == other.expr.substitute(other.bv, self.bv)

    def FV(self):
        return self._FV


if __name__ == "__main__":
    # The formal system of addition of zeroes in Metamath
    wff = PrimitiveSort("wff")
    term = PrimitiveSort("term")

    zero = Node("0", term, ())
    plus = Node("+", term, (term, term))
    eq = Node("=", wff, (term, term))
    impl = Node("->", wff, (wff, wff))

    x = Variable("x", term)
    phi = Variable("phi", wff)

    OpOeO = eq(plus(zero(), zero()))
    print(OpOeO)
    xe0_i_xp0e0 = Bind(x, impl(eq(x, zero()), eq(plus(x, zero()), zero())))
    print(xe0_i_xp0e0)
    print(xe0_i_xp0e0.sort)

