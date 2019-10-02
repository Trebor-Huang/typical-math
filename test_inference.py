from judgment import *

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
OneType = Node("1", expr, ())()
ZeroType = Node("0", expr, ())()
# Trivial = Node("*", expr, ())()
type_stmt = PrimitiveSort("type_stmt")
var = PrimitiveSort("var")
x = MetaVariable("x", var)
y = MetaVariable("y", var)
a = Node("a", var, ())()
b = Node("b", var, ())()
colon = Node(":", type_stmt, (var, expr), lambda t: t[1] + ":" + t[2])
ctx_sort = PrimitiveSort("ctx")
Gamma = MetaVariable("Gamma", ctx_sort)
epsilon = Node("*", ctx_sort, (), lambda _: "*")()  # Empty context
cons = Node("::", ctx_sort, (ctx_sort, type_stmt), lambda t: t[1] + ", " + t[2])  # reverse cons
lookup = JudgmentForm("lookup", (ctx_sort, var, expr), lambda t: t[1] + " |- " + t[2] + " lookup ~> " + t[3])  # lookup
lookup_pop = InferenceRule("POP", (), lookup(cons(Gamma, colon(x, A)), x, A))
lookup_next = InferenceRule("NEXT", (lookup(Gamma, x, A),), lookup(cons(Gamma, colon(y, B)), x, A),
                            lambda d: d[y] != d[x])

inference_rules = [lookup_pop, lookup_next]
simple_lookup = lookup(cons(cons(epsilon, colon(a, OneType)), colon(b, ZeroType)), a, OneType)
print(infer(simple_lookup, inference_rules)[0].pretty())

# TODO: further develop this
