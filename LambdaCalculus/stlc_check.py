from LambdaCalculus.stlc import Variable, Abstraction, Application, Type, Constant, FuncType, ConstantType


"""
Judgments:
G |- check x : A   [G is a context, A is a type]
G |- x synth ~> A  [G is a context]
G |- x lookup ~> A [G is a context]
"""


def ctx2str(ctx) -> str:
    s = ', '.join(f"{repr(i)}:{repr(t)}" for i, t in ctx)
    if len(s) > 40:
        return "G..."
    elif len(s) == 0:
        return '*'
    else:
        return s


class Judgment:
    def __repr__(self):
        return "Judgment"  # TODO


"""
Typing Rules:
###### Context ###### (implemented as lists of tuples)

(Context validity is automatic)
"""


class Lookup(Judgment):
    """
    Judgments for lookup:

    -------------------------STOP
     G, x:A |- x lookup ~> A

        G |- x lookup ~> A
    -------------------------POP (x!=y)
     G, y:B |- x lookup ~> A
    """
    def __init__(self, ctx, var):
        self.ctx = ctx
        self.term = var
        if len(ctx) == 0:
            raise ValueError("Judgment not derivable.")
        if ctx[-1][0] == self.term:
            self.out = ctx[-1][1]
            self.derivation = ()
        else:
            pop = Lookup(ctx[:-1], var)
            self.derivation = (pop,)
            self.out = pop.out

    def __repr__(self):
        return ctx2str(self.ctx) + " |- " + str(self.term) + " lookup ~> " + str(self.out)


"""
###### Type ######

(Automatic: non-types cannot be expressed at all)

###### Typing ######
"""

"""
 G |- x lookup ~> A      G |- x lookup ~> A
--------------------VC  --------------------VS
  G |- check x : A        G |- x synth ~> A

 G |- E1 synth ~> A->B; G |- check E2 : A
------------------------------------------AS
         G |- (E1 E2) synth ~> B

 G |- E2 synth ~> A; G |- check E1 : A->B
------------------------------------------AC
         G |- check (E1 E2) : B

  G, x:A |- E synth ~> B         G, x:A |- check E : B
--------------------------LS  --------------------------LC
 G |- ^x:A.E synth ~> A->B     G |- check ^x:A.E : A->B
 """


class Synth(Judgment):  # The structure is strange here. We need to automate this.
    def __init__(self, ctx, expr):
        self.ctx = ctx
        self.expr = expr
        if isinstance(expr, Variable):
            vs = Lookup(ctx, expr)
            self.out = vs.out
            self.derivation = (vs,)
        elif isinstance(expr, Application):
            as1 = Synth(ctx, expr.head)
            assert isinstance(as1.out, FuncType)
            as2 = Check(ctx, expr.body, as1.out.dom)
            self.out = as1.out.cod
            self.derivation = (as1, as2)
        elif isinstance(expr, Abstraction):
            ls = Synth(ctx + [(expr.bv, expr.vtype)], expr.body)
            self.out = FuncType(expr.vtype, ls.out)
            self.derivation = (ls,)

    def __repr__(self):
        return ctx2str(self.ctx) + " |- " + str(self.expr) + " synth ~> " + str(self.out)


class Check(Judgment):
    def __init__(self, ctx, expr, check: Type):
        self.ctx = ctx
        self.expr = expr
        self.check = check
        if isinstance(expr, Variable):
            vc = Lookup(ctx, expr)
            if check != vc.out:
                raise ValueError("Judgment not derivable.")
            self.derivation = (vc,)
        elif isinstance(expr, Application):
            ac1 = Synth(ctx, expr.body)
            ac2 = Check(ctx, expr.head, FuncType(ac1.out, check))
            self.derivation = (ac1, ac2)
        elif isinstance(expr, Abstraction):
            if not isinstance(check, FuncType) or expr.vtype != check.dom:
                raise ValueError("Judgment not derivable.")
            lc = Check(ctx + [(expr.bv, expr.vtype)], expr.body, check.cod)
            self.derivation = (lc,)

    def __repr__(self):
        return ctx2str(self.ctx) + " |- check " + str(self.expr) + " : " + str(self.check)


def deriv2array(j: Judgment):
    if len(j.derivation) == 0:
        a = ['']
        width = 0
    else:
        derivstrs = list(map(deriv2array, j.derivation))
        derivlens = list(map(lambda l:len(l[0]), derivstrs))
        a = []
        while not all(len(i) == 0 for i in derivstrs):
            a.insert(0, '  '.join(i.pop() if len(i) != 0 else " " * derivlens[n]
                                  for n, i in enumerate(derivstrs)))
        width = len(a[-1])
    concl = str(j)
    wc = len(str(j))
    total_width = max(width, wc) + 2
    return [ai.center(total_width, ' ') for ai in a] +\
           ['-' * total_width] + [concl.center(total_width, ' ')]


if __name__ == "__main__":
    A, B, C = map(ConstantType, "A B C".split())
    x, y, z = map(Variable, "x y z".split())
    AtB = FuncType(A, B)
    AtBtC = FuncType(A, FuncType(B, C))
    S = (x, AtBtC) - ((y, AtB) - ((z, A) - (x(z)(y(z)))))
    print(S)
    SynthS = Synth([], S)
    print(SynthS)
    print("Synthesized: S is of type %s" % str(SynthS.out))
    print('\n'.join(deriv2array(SynthS)))
    CheckS = Check([], S, SynthS.out)
    print(CheckS)
    print("Checked: S is indeed of type %s" % str(CheckS.check))
