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
        return hash(id(self))


class Abstraction(Expression):
    def __init__(self, var, body):
        self.bv = Variable(var.name)
        self.body = body.substitute(var, self.bv)

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
        return hash(self.bv) ^ hash(self.body) ^ 0x123456


class Application(Expression):
    def __init__(self, head, body):
        self.head = head
        self.body = body

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
        return hash(self.head) ^ hash(self.body) ^ 0xABCDEF


if __name__ == '__main__':
    # -----      Variable Definition     -----
    x = Variable('x')
    y = Variable('y')
    z = Variable('z')
    # -----        The SKI Basis         -----
    #    S, K and Id defined below can produce
    # all lambda expressions up to alpha/beta/
    # eta conversions.
    Id = Abstraction(x, x)  # Alternatively I
    K = Abstraction(x, Abstraction(y, x))
    print("K =", K)
    KI = K(Id).reduction()
    print("K I =",KI)
    print("KI(x).reduction() == Id :",KI(x).reduction() == Id)
    S = (x - (y - (z - ((x(z))(y(z))))))
    print("S =",S)
    SKK = S(K)(K)
    print("SKK =", SKK.reduction())
    # -----         The X Basis          -----
    #    Surprisingly, X alone can represent
    # all lambda terms. There are many more of
    # this kind.
    X = (x - (x(S)(K)))
    print("X (X (X X)) =", (X(X(X(X)))).reduction())
    print("X (X (X (X X))) =", (X(X(X(X(X))))).reduction())
    # -----          The Omega           -----
    omega = (x - (x(x)))
    Omega = omega(omega)
    print("Omega =", Omega)
    try:
        print(Omega.reduction())
    except RuntimeError as e:
        print('Omega has no normal form.')
    Y = (y - ((x - (y(x)(x)))(x - (y(x)(x)))))
    # -----   The Fixpoint combinator Y  -----
    print("Fixpoint combinator Y =", Y.reduction())
    print("Y(KI) =", Y(KI).reduction())  # Should be exactly Id.
