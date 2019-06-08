from Misc.unification.basics import Expression as uExp, Variable as uVar, Constructor as uCons, Function as uFunc
from Misc.unification.unify import Constraint, unify, UnificationException


class Type(uExp):
    def __eq__(self, other):
        return self is other

    def __repr__(self):
        return "Type"

    def __sub__(self, other):
        return FuncType(self, other)


class TypeVar(uVar, Type):
    uuid_cur = 0

    def __init__(self, name):
        super().__init__(name)
        self.uuid = TypeVar.uuid_cur
        TypeVar.uuid_cur += 1

    def __repr__(self):
        return f"T{str(self.uuid)}"  # f"TYPE<{repr(self.ident)}>"


class Arrow(uCons):
    def __init__(self):
        super().__init__('Arrow', 2)

    def __eq__(self, other):
        return isinstance(other, Arrow)

    def __repr__(self):
        return '->'

    def __call__(self, dom, cod):
        return FuncType(dom, cod)

    def __hash__(self):
        return 0


To = Arrow()


class FuncType(Type, uFunc):
    def __init__(self, domain, codomain):
        super().__init__(To, (domain, codomain))
        self.dom = domain
        self.cod = codomain

    def __repr__(self):
        return f"({repr(self.dom)} -> {repr(self.cod)})"

    def substitute(self, var, sub):
        return FuncType(self.dom.substitute(var, sub), self.cod.substitute(var, sub))

    def __eq__(self, other):
        return isinstance(other, FuncType) and self.dom == other.dom and self.cod == other.cod


class ConstantType(Type, uExp):
    def __init__(self, name):
        self.name = name

    def __eq__(self, other):
        return isinstance(other, ConstantType) and self.name == other.name

    def __repr__(self):
        return self.name

    def __hash__(self):
        return hash(self.name)


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

    def __rsub__(self, vart):
        return Abstraction(*vart, self) if isinstance(vart, tuple) else Abstraction(vart, None, self)

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

    def __hash__(self):
        return self._h

    def __sub__(self, expr):
        return Abstraction(self, None, expr)


class Abstraction(Expression):
    def __init__(self, var, vtype, body):
        self.bv = Variable(var.name)
        self.vtype = vtype  # Type annotation
        self.body = body.substitute(var, self.bv)
        self._h = hash(self.bv) ^ hash(self.body) ^ 0x123456

    def __eq__(self, other):
        return isinstance(other, Abstraction) and self.vtype == other.vtype and \
               self.body == other.body.substitute(other.bv, self.bv)

    def __repr__(self):
        return "(\\" + repr(self.bv) + (":" + repr(self.vtype) if self.vtype is not None else '') + "." + repr(self.body) + ")"

    def substitute(self, var, subs):
        if var == self.bv:
            raise ValueError("Bound variable leakage.")
        else:
            return Abstraction(self.bv, self.vtype, self.body.substitute(var, subs))

    def reduction(self):
        if isinstance(self.body, Application) and \
                self.body.body == self.bv and self.bv not in self.body.head.FV():
            return self.body.head.reduction()  # eta-reduction
        else:
            return Abstraction(self.bv, self.vtype, self.body.reduction())

    def FV(self):
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


class Constant(Expression):
    def __init__(self, name, tp: ConstantType):
        self.name = name
        self.tp = tp
        self._h = hash(self.name)

    def __eq__(self, other):
        return self.name == other.name and self.tp == other.tp

    def __repr__(self):
        return self.name

    def reduction(self):
        return self

    def FV(self):
        return set()

    def __hash__(self):
        return self._h


# TODO: atomic operations on constants, as a subclass of Abstraction


def variables(expr: Expression):  # This is used only for inference, so it is not incorporated into the classes
    if isinstance(expr, Variable):
        return {expr}
    elif isinstance(expr, Abstraction):
        return {expr.bv}.union(variables(expr.body))
    elif isinstance(expr, Application):
        return set.union(variables(expr.head), variables(expr.body))


def traverse(expr: Expression):
    if isinstance(expr, Variable):
        return [(expr,)]
    elif isinstance(expr, Abstraction):
        return [(expr.bv, expr)] + [l+(expr,) for l in traverse(expr.body)] + [(expr,)]
    elif isinstance(expr, Application):
        return [l+(expr,) for l in traverse(expr.head)] + [l+(expr,) for l in traverse(expr.body)] + [(expr,)]


def _infer(expr):
    # --- I. instantiate type variables ---
    # Each variable x gets a type variable u(x)
    # Each occurrence of an expression E gets a type var v(E)
    vrs = variables(expr)
    trs = traverse(expr)
    u = {x: TypeVar(x) for x in vrs}
    v = {r: TypeVar(r) for r in trs}
    # --- II. generate constraints ---
    # u(x) = v(x) for each occurrence of a variable x
    # v(e1) = v(e2) -> v((e1 e2)) for each occurrence of a subexpression (e1 e2)
    # v(\x:None.e) = v(x) -> v(e) for each occurrence of a subexpression \x:None.e
    # u(x) = T for each occurence of a subexpression \x:T.e
    constraints = []  # can be merged
    constraints.extend(Constraint(v[r], u[r[0]]) for r in trs if isinstance(r[0], Variable))
    constraints.extend(Constraint(v[(e[0].head,)+e], FuncType(v[(e[0].body,)+e], v[e]))
                       for e in trs if isinstance(e[0], Application))
    constraints.extend(Constraint(v[e], FuncType(v[(e[0].bv,)+e], v[(e[0].body,)+e]))
                       for e in trs if isinstance(e[0], Abstraction))
    constraints.extend(Constraint(u[e[0].bv], e[0].vtype)
                       for e in trs if isinstance(e[0], Abstraction) and e[0].vtype is not None)
    # --- III. UNIFY!!! ---
    return unify(constraints)


def infer(expr):
    rs = _infer(expr)
    t = [c.rhs for c in rs if isinstance(c.lhs.name, tuple) and c.lhs.name[0] == expr]
    assert len(t) == 1
    return t[0]


if __name__ == '__main__':
    x = Variable('x')
    y = Variable('y')
    z = Variable('z')
    u = Variable('u')
    T = ConstantType("A")
    S = (x, None) - ((y, None) - ((z, None) - (x(z)(y(z)))))
    print("$$$ Traversal of S $$$")
    print(*traverse(S), sep='\n')
    print("\n$$$ Inference result $$$")
    print(*_infer(S), sep='\n')
    print("\nSo there...")
    print(infer(S))
    print()

    omega = (x, None) - x(x)
    print("For omega:")
    try:
        print(infer(omega))
    except UnificationException as ue:
        print(ue)
    print()

    zero = (y, FuncType(T, T)) - (x - x)
    succ = x - (y - (z - y(x(y)(z))))

    print(infer(zero), sep='\n')
    print(infer(succ))
