from abt import *
from pattern import *

judgmentSort = PrimitiveSort("judgment")


class JudgmentForm(Node):
    def __init__(self, name, args, repr=None):
        super().__init__(name, judgmentSort, args, repr)


class InferenceRule:
    def __init__(self, name, premises, conclusion):
        self.name = name
        self.premises = tuple(premises)
        self.conclusion = conclusion

    def __call__(self, pr, concl):
        return Derivation(self, pr, concl)


class Derivation:
    def __init__(self, rule: InferenceRule, prem, concl: ABT):
        self.rule = rule
        try:
            prem_match = merge_dicts(*map(match, (p.conclusion for p in prem), rule.premises))
            res_match = match(concl, rule.conclusion)
            subs = merge_dicts(prem_match, res_match)
        except ValueError as e:
            raise ValueError("Inconsistent assignment of metavariables.")
        self.premises = prem
        self.conclusion = concl
        self.assigment = subs


class BidirectionalRule(InferenceRule):
    pass


if __name__ == "__main__":
    expr = PrimitiveSort("expr")
    Zero = Node("0", expr, (), lambda _: "0")()
    Succ = Node("S", expr, (expr,))
    isNat = JudgmentForm("NAT", (expr,), lambda m: f"{str(m[1])} nat")

    n = MetaVariable("n", expr)

    Onat = InferenceRule("Onat", (), isNat(Zero))
    Snat = InferenceRule("Snat", (isNat(n),), isNat(Succ(n)))

    ZeroIsNat = Derivation(Onat, (), isNat(Zero))
    OneIsNat = Derivation(Snat, (ZeroIsNat,), isNat(Succ(Zero)))
