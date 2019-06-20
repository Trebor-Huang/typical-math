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
            map(match, prem, rule.premises)
        except ValueError as e:
            pass



class BidirectionalRule(InferenceRule):
    pass
