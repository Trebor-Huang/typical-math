from judgment import *

print("----- TEST I -----")
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
print("----- TEST II -----")
# We redo the stlc system, systematically.


