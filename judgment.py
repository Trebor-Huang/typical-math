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
        assert all(map(lambda x: isinstance(x, Derivation), prem))
        try:
            map(match, prem + [concl], rule.premises + [rule.conclusion])
        except ValueError as e:
            raise ValueError("Variables does not match.")

    def __repr__(self):
        return "???"  # TODO


class BidirectionalRule(InferenceRule):
    def __init__(self, name, premises, conclusion, auto):  # TODO
        """auto(...?)"""
        super().__init__(name, premises, conclusion)
        self.auto = auto


if __name__ == "__main__":
    # miu
    pass
