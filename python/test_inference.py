from python.judgment import *

print("##### TEST I #####")
expr = PrimitiveSort("expr")
Zero = Node("0", expr, (), lambda _: "0")()
Succ = Node("S", expr, (expr,))
isNat = JudgmentForm("NAT", (expr,), lambda m: f"{str(m[1])} nat")

n = MetaVariable("n", expr)

Onat = InferenceRule("Onat", (), isNat(Zero))
Snat = InferenceRule("Snat", (isNat(n),), isNat(Succ(n)))
# We build derivation trees by hand.
ZeroIsNat = Derivation(Onat, (), isNat(Zero))
OneIsNat = Derivation(Snat, (ZeroIsNat,), isNat(Succ(Zero)))

print(OneIsNat.pretty())

OneIsNat_auto, assignments = infer(isNat(Succ(Zero)), [Onat, Snat])

print(OneIsNat_auto.pretty())

print()
print("##### TEST II #####")
# We redo the stlc system, systematically.
# Forgive reuse of expr, because it's basically the same

A = MetaVariable("A", expr)
B = MetaVariable("B", expr)
C = MetaVariable("C", expr)
E = MetaVariable("E", expr)
M = MetaVariable("M", expr)
N = MetaVariable("N", expr)

TA = Node("A", expr, (), lambda _: "TA")()
TB = Node("B", expr, (), lambda _: "TB")()
TC = Node("C", expr, (), lambda _: "TC")()

OneType = Node("1", expr, (), lambda _: "1")()
ZeroType = Node("0", expr, (), lambda _: "0")()
Lambda = Node("lambda", expr, (BindingSort(expr, expr), expr),
              lambda t: "\\" + t[1].split(".")[0] + ":" + t[2] + "." + ".".join(t[1].split(".")[1:]))

def L(x, A, E):  # a more natural way of stating lambda
    return Lambda(Bind(x, E), A)

App = Node("@", expr, (expr, expr), lambda t: "(%s %s)" % t[1:])
To = Node("->", expr, (expr, expr), lambda t: "(%s -> %s)" % t[1:])

# Trivial = Node("*", expr, ())()
type_stmt = PrimitiveSort("type_stmt")
x = MetaVariable("x", expr)  # a fatal error: when metavariables become bound, they can no longer be matched!!!
y = MetaVariable("y", expr)  # solution: substitution should get stuck on metavariables!!!
z = MetaVariable("z", expr)  # this is mentioned in the little typer book as CLOSURES!!!!!!! How could I've missed it?
a = Variable("a", expr)
b = Variable("b", expr)
c = Variable("c", expr)

S_combinator = L(a, To(TA, To(TB, TC)), L(b, To(TA, TB), L(c, TA, App(App(a, c), App(b, c)))))
print(S_combinator)  # This is becoming Lisp....

colon = Node(":", type_stmt, (expr, expr), lambda t: t[1] + ":" + t[2])

# -- Contexts
ctx_sort = PrimitiveSort("ctx")
Gamma = MetaVariable("Gamma", ctx_sort)
epsilon = Node("*", ctx_sort, (), lambda _: "*")()  # Empty context
cons = Node("::", ctx_sort, (ctx_sort, type_stmt), lambda t: t[1] + ", " + t[2])  # reverse cons

# -- lookup
lookup = JudgmentForm("lookup", (ctx_sort, expr, expr), lambda t: t[1] + " |- " + t[2] + " lookup ~> " + t[3])  # lookup
lookup_pop = InferenceRule("POP", (), lookup(cons(Gamma, colon(x, A)), x, A))
lookup_next = InferenceRule("NEXT", (lookup(Gamma, x, A),), lookup(cons(Gamma, colon(y, B)), x, A),
                            lambda d: d[y] != d[x])

inference_rules = [lookup_pop, lookup_next]
simple_lookup = lookup(cons(cons(epsilon, colon(a, OneType)), colon(b, ZeroType)), a, OneType)
print(infer(simple_lookup, inference_rules)[0].pretty())

# -- synth and check
synth = JudgmentForm("synth", (ctx_sort, expr, expr), lambda t: t[1] + " |- " + t[2] + " synth ~> " + t[3])
check = JudgmentForm("check", (ctx_sort, expr, expr), lambda t: t[1] + " |- check " + t[2] + " : " + t[3])

SV = InferenceRule("SV", (lookup(Gamma, x, A),), synth(Gamma, x, A), lambda d: isinstance(d[x], Variable))
SL = InferenceRule("SL", (synth(cons(Gamma, colon(x, A)), E, B),), synth(Gamma, L(x, A, E), To(A, B)),
                   lambda d: isinstance(d[x], Variable))
SA = InferenceRule("SA", (synth(Gamma, M, To(A, B)), check(Gamma, N, A)), synth(Gamma, App(M, N), B),
                   lambda d: isinstance(d[x], Variable))

CV = InferenceRule("CV", (lookup(Gamma, x, A),), check(Gamma, x, A),
                   lambda d: isinstance(d[x], Variable))
CL = InferenceRule("CL", (check(cons(Gamma, colon(x, A)), E, B),), check(Gamma, L(x, A, E), To(A, B)),
                   lambda d: isinstance(d[x], Variable))
CA = InferenceRule("CA", (synth(Gamma, N, A), check(Gamma, M, To(A, B))), check(Gamma, App(M, N), B),
                   lambda d: isinstance(d[x], Variable))

inference_rules.extend([SV, SL, SA, CV, CL, CA])
print(infer(synth(epsilon, S_combinator, M), inference_rules)[0].pretty())
