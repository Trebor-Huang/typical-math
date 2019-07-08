# For abstract syntax trees and abstract binding trees.
# from functools import lru_cache
# TODO unification


def substitute(expr, subs: dict):
    for key in subs:
        expr = expr.substitute(key, subs[key])
    return expr


class Sort:
    def __setattr__(self, key, value):
        if not hasattr(self, key):
            super().__setattr__(key, value)
        else:
            raise RuntimeError("Can't modify immutable object's attribute: {}".format(key))

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
    def __init__(self, sort):  # TODO refactoring so that this method assigns common attributes
        self.sort = sort

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

    def __setattr__(self, key, value):
        if not hasattr(self, key):
            super().__setattr__(key, value)
        else:
            raise RuntimeError("Can't modify immutable object's attribute: {}".format(key))


class Node:
    def __init__(self, name, sort, args, repr=None):
        self.sort = sort
        self.name = name
        self.args = tuple(args)  # A tuple of sorts
        self._repr = (lambda t: repr % t) if isinstance(repr, str) else repr
        self._hash = hash(self.sort) ^ hash(self.name) ^ hash(self.args)

    def __hash__(self):
        return self._hash

    def __call__(self, *args):
        return AST(self, tuple(args))

    def __setattr__(self, key, value):
        if not hasattr(self, key):
            super().__setattr__(key, value)
        else:
            raise RuntimeError("Can't modify immutable object's attribute: {}".format(key))


class AST(ABT):
    """An AST Node."""

    def __init__(self, node: Node, args: tuple):
        if not isinstance(node, Node):
            raise TypeError("node is not of type Node.")
        super().__init__(node.sort)
        self.node = node
        if len(args) != len(node.args):
            raise ValueError("Incorrect number of arguments.")
        if not all(map(lambda t: t[0].sort == t[1], zip(args, node.args))):
            raise ValueError("Sort mismatch.")
        self.args = args
        self._repr = f"{self.node.name}({', '.join(map(str, self.args))})" if node._repr is None \
            else node._repr((self.node.name, *map(str, self.args)))
        self._hash = hash(self.node) ^ hash(self.args)
        self._FV = set.union(*(e.FV() for e in self.args), set())

    def __repr__(self):
        """To customize output, pass `repr` parameter for Node.
        It will be formatted as `repr % (self.node.name, *map(str, self.args))`"""
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
        super().__init__(sort)
        self.ident = ident
        self.name = str(ident) if name is None else str(name)
        self._hash = hash(self.sort) ^ hash(self.ident)

    def __repr__(self):
        return self.name

    def __hash__(self):
        return self._hash

    def substitute(self, var, expr):
        return self if var != self else expr

    def __eq__(self, other):
        return isinstance(other, Variable) and self.sort == other.sort and self.ident is other.ident \
               and self.name == other.name

    def FV(self):
        return {self}


class Bind(ABT):
    def __init__(self, var, expr: ABT):
        self._hash = 0
        super().__init__(BindingSort(var.sort, expr.sort))
        self.bv = Variable(self, var.sort, var.name)
        self.expr = expr.substitute(var, self.bv)
        self._FV = self.expr.FV() - {self.bv}
        object.__setattr__(self, "_hash", hash(self.expr))  # TODO: Might this actually *be* alpha-invariant? Test!
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

    zero = Node("0", term, (), lambda _: "0")
    plus = Node("+", term, (term, term), lambda t: "( %s + %s )" % t[1:])
    eq = Node("=", wff, (term, term), lambda t: "( %s = %s )" % t[1:])
    impl = Node("->", wff, (wff, wff), lambda t: "( %s -> %s )" % t[1:])

    x = Variable("x", term)
    y = Variable("y", term)
    phi = Variable("phi", wff)

    OpOeO = eq(plus(zero(), zero()), zero())
    print(OpOeO)
    xe0_i_xp0e0 = Bind(x, impl(eq(x, zero()), eq(plus(x, zero()), zero())))
    print(xe0_i_xp0e0)
    print(xe0_i_xp0e0.sort)
    print(hash(xe0_i_xp0e0))
    xty = Bind(y, xe0_i_xp0e0.expr.substitute(xe0_i_xp0e0.bv, y))
    print(xty, hash(xty))
