class Expression:
    def __eq__(self, other):
        return self is other

    def __repr__(self):
        return "Expression"

    def substitute(self, var, sub):
        return self

    def variables(self):
        return set()

    def __hash__(self):
        return 0


class Variable(Expression):
    def __init__(self, name):  # ident may not be str
        self.name = name

    def __eq__(self, other):
        return isinstance(other, Variable) and self.name == other.name

    def __repr__(self):
        return str(self.name)

    def substitute(self, var, sub):
        if self == var:
            return sub
        else:
            return self

    def variables(self):
        return {self}

    def __hash__(self):
        return hash(self.name)


class Constructor:
    def __init__(self, name, arity=0):
        self.name = name
        self.arity = arity

    def __eq__(self, other):
        return isinstance(other, Constructor) and self.name == other.name and self.arity == other.arity

    def __repr__(self):
        return self.name + "\\" + str(self.arity)

    def __call__(self, *variables):
        if len(variables) == 1 and isinstance(variables[0], tuple):
            variables = variables[0]
        if len(variables) != self.arity:
            raise ValueError("Incorrect arity for "+str(self)+".")
        return Function(self, variables)

    def __hash__(self):
        return hash(self.name)


class Function(Expression):
    def __init__(self, cons, variables):
        self.constructor = cons
        self.args = tuple(variables)

    def __eq__(self, other):
        return isinstance(other, Function) and self.constructor == other.constructor and self.args == other.args

    def __repr__(self):
        return f"{self.constructor.name}({', '.join([str(v) for v in self.args])})"

    def substitute(self, var, sub):
        return self.constructor(tuple([v.substitute(var, sub) for v in self.args]))

    def variables(self):
        return set.union(set(), *[v.variables() for v in self.args])  # Empty set() to avoid empty unions

    def __hash__(self):
        return hash(self.name)


if __name__ == "__main__":
    f = Constructor("f", 1)
    c = Constructor("c", 0)
    g = Constructor("g", 2)
    x = Variable("x")
    y = Variable("y")

    expr = g(f(x), g(c(), y))

    print(expr)
    print(expr.variables())

    expr1 = expr.substitute(x, g(y, f(c())))

    print(expr1)
    print(expr1.variables())
