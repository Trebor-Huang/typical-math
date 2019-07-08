from abt import *
from pattern import *


class JudgmentForm(Node):
    judgmentSort = PrimitiveSort("judgment")

    def __init__(self, name, args, repr=None):
        super().__init__(name, self.judgmentSort, args, repr)


class InferenceRule:
    def __init__(self, name, premises, conclusion):
        self.name = name
        self.premises = tuple(premises)
        self.conclusion = conclusion

    def __call__(self, pr, concl):
        return Derivation(self, pr, concl)

    def __setattr__(self, key, value):
        if not hasattr(self, key):
            super().__setattr__(key, value)
        else:
            raise RuntimeError("Can't modify immutable object's attribute: {}".format(key))


class Derivation:
    def __init__(self, rule: InferenceRule, prem, concl: ABT):
        self.rule = rule
        assert all(map(lambda x: isinstance(x, Derivation), prem))
        try:
            prem_match = merge_dicts(*map(match, (p.conclusion for p in prem), rule.premises))
            res_match = match(concl, rule.conclusion)
            subs = merge_dicts(prem_match, res_match)
        except ValueError as e:
            raise ValueError("Inconsistent assignment of metavariables.")
        self.premises = prem
        self.conclusion = concl
        self.assignment = subs

    def __setattr__(self, key, value):
        if not hasattr(self, key):
            super().__setattr__(key, value)
        else:
            raise RuntimeError("Can't modify immutable object's attribute: {}".format(key))


class BidirectionalRule(InferenceRule):
    def __init__(self, name, premises, conclusion_in, conclusion_out, io_node):
        # io_node is a Node with conclusion_in and conclusion_out as arguments.
        # the conclusion_in's will be used as pattern to match against actual expressions
        # when type checking, and the matched results substituted into premises'
        # meta-variables, recursively generating the output.

        # premises should be a list of bidirectional rules (check!)
        self.conclusion_in = conclusion_in
        self.conclusion_out = conclusion_out
        super().__init__(name, premises, io_node(*conclusion_in, conclusion_out))

    def generate(self, conclusion_in):
        res = match(conclusion_in, self.conclusion_in)
        # TODO


    def __setattr__(self, key, value):
        if not hasattr(self, key):
            super().__setattr__(key, value)
        else:
            raise RuntimeError("Can't modify immutable object's attribute: {}".format(key))


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
