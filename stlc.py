class Type:
    def substitute(self, tvar, tp):
        return self

    def __eq__(self, other):
        return self is other

    def __repr__(self):
        return "Type"

    def __hash__(self):
        return 0

    def __sub__(self, other):
        return FuncType(self, other)

    def FV(self):
        return set()


class TypeVar(Type):
    def __init__(self, name=""):
        self.name = name
        self._h = hash(id(self))

    def substitute(self, tvar, tp):
        return self if self != tvar else tp

    def __repr__(self):
        return self.name

    def FV(self):
        return {self}

    def __hash__(self):
        return self._h


class FuncType(Type):
    def __init__(self, domain, codomain):
        self.dom = domain
        self.cod = codomain
        self._h = hash(domain) ^ hash(codomain) ^ 0x1353123

    def substitute(self, tvar, tp):
        return self if self != tvar else tp

    def __repr__(self):
        return f"({repr(self.dom)} -> {repr(self.cod)})"

    def FV(self):
        return set.union(self.dom.FV(), self.cod.FV())

    def __hash__(self):
        return self._h


class Expression:
    def substitute(self, var, subs):
        return self

    def __eq__(self, other):
        return self is other

    def __repr__(self):
        return "Expression"

    def reduction(self):
        return self

    def FV(self):
        return set()

    def __call__(self, arg):
        return Application(self, arg)

    def __hash__(self):
        return 0


class Variable(Expression):
    def __init__(self, name=""):
        self.name = name
        self._h = hash(id(self))

    def __repr__(self):
        return self.name

    def substitute(self, var, subs):
        if self == var:
            return subs
        else:
            return self

    def reduction(self):
        return self

    def FV(self):
        return {self}

    def __sub__(self, body):
        return Abstraction(self, body)

    def __hash__(self):
        return self._h


class Abstraction(Expression):
    def __init__(self, var, body):
        self.bv = Variable(var.name)
        self.body = body.substitute(var, self.bv)
        self._h = hash(self.bv) ^ hash(self.body) ^ 0x123456

    def __eq__(self, other):
        return isinstance(other, Abstraction) and \
               self.body == other.body.substitute(other.bv, self.bv)

    def __repr__(self):
        return "(\\" + repr(self.bv) + "." + repr(self.body) + ")"

    def substitute(self, var, subs):
        if var == self.bv:
            raise ValueError("Bound variable leakage.")
        else:
            return Abstraction(self.bv, self.body.substitute(var, subs))

    def reduction(self):
        if isinstance(self.body, Application) and \
                self.body.body == self.bv and self.bv not in self.body.head.FV():
            return self.body.head.reduction()  # eta-reduction
        else:
            return Abstraction(self.bv, self.body.reduction())

    def FV(self):
        # print('[DEBUG]'+str(self.body)+" - "+str(self.body.FV()))
        return self.body.FV() - {self.bv}

    def __hash__(self):
        return self._h


class Application(Expression):
    def __init__(self, head, body):
        self.head = head
        self.body = body
        self._h = hash(self.head) ^ hash(self.body) ^ 0xABCDEF

    def __eq__(self, other):
        return isinstance(other, Application) and \
               other.head == self.head and other.body == self.body

    def __repr__(self):
        return '(' + repr(self.head) + " " + repr(self.body) + ")"

    def substitute(self, var, subs):
        return Application(self.head.substitute(var, subs),
                           self.body.substitute(var, subs))

    def reduction(self):
        hr = self.head.reduction()
        if isinstance(hr, Abstraction):
            # print('[Debug]',hr.body.substitute(hr.bv, self.body))
            return hr.body.substitute(hr.bv, self.body).reduction()
        else:
            return Application(hr,
                               self.body.reduction())

    def FV(self):
        return set.union(self.head.FV(), self.body.FV())

    def __hash__(self):
        return self._h


class Constraint:  # Wrapper class for constraint equations
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self):
        return repr(self.lhs) + " == " + repr(self.rhs)


#
