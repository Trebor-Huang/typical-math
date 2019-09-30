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


    # TODO: inference rules
    # ##### How automatic inference works ##### #
    # We take the known parts in the judgment,
    # and by unification with each inference rules
    # we pick out the ones that result in a
    # consistent unification, and, one-by-one, try
    # to recursively find the expression to fill
    # in the metavariables in the premises. We
    # take the first successful one, and fill in
    # the unknown parts of the conclusion with the
    # now-known knowledge.

    # We do *NOT* need explicit marking of inputs and outputs.


if __name__ == "__main__":
    pass
