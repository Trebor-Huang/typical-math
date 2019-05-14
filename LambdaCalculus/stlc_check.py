def merge_dicts(*dicts):
    if len(dicts) == 0:
        return dict()
    else:
        return {**dicts[0], **merge_dicts(dicts[1:])}


class AST:
    def __init__(self, name, args):
        self.name = name.replace('_', '%s')
        self.arity = name.count('_')
        self.args = args

    def __repr__(self):
        return self.name % self.args


class ASTVar(AST):
    def __init__(self, name):
        super().__init__(name, ())



"""
Judgments:
G ctx
G |- check x : A   [G is a context, A is a type]
G |- x synth ~> A  [G is a context]
G |- x lookup ~> A [G is a context]
"""


def ctx2str(ctx) -> str:
    s = ', '.join(f"{repr(i)}:{repr(t)}" for i, t in ctx)
    if len(s) > 15:
        return "G..."
    else:
        return s


class Judgment:
    def __repr__(self):
        return "Judgment"


class CtxJudgment(Judgment):
    def __init__(self, ctx):
        self.ctx = ctx

    def __repr__(self):
        return ctx2str(self.ctx) + ' ctx'


class CheckJudgment(Judgment):
    def __init__(self, ctx, term, typ):
        self.term = term
        self.type = typ
        self.ctx = ctx

    def __repr__(self):
        return f"{ctx2str(self.ctx)} |- check {repr(self.term)} : {repr(self.type)}"


class SynthJudgment(Judgment):
    def __init__(self, ctx, term, typ):
        self.term = term
        self.type = typ
        self.ctx = ctx

    def __repr__(self):
        return f"{ctx2str(self.ctx)} |- {repr(self.term)} synth ~> {repr(self.type)}"


class LookupJudgment(Judgment):
    def __init__(self, ctx, var, typ):
        self.ctx = ctx
        self.var = var
        self.type = typ

    def __repr__(self):
        return f"{ctx2str(self.ctx)} |- {repr(self.var)} lookup ~> {repr(self.type)}"


def pattern(pat: AST, expr: AST):
    if isinstance(pat, ASTVar):
        return {pat.name: expr}
    if pat.name == expr.name:
        return merge_dicts(*map(lambda t: pattern(*t), zip(pat.args, expr.args)))
    raise ValueError("Pattern does not match expression.")


"""
Typing Rules:
###### Context ###### (implemented as lists of tuples)
                   G ctx
-------EMPTY   ------------EXT
 * ctx          G, x:A ctx


-------------------------STOP
 G, x:A |- x lookup ~> A

    G |- x lookup ~> A
-------------------------POP (x!=y)
 G, y:B |- x lookup ~> A

###### Type ######

(Automatic: non-types cannot be expressed at all)

###### Typing ######
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

# TODO
