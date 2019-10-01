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
        self.variables = merge_dicts(get_metavariables(conclusion), *map(get_metavariables, premises))

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
        self.premises = tuple(prem)
        self.conclusion = concl
        self.assignment = subs

    """
    def __setattr__(self, key, value):
        if not hasattr(self, key):
            super().__setattr__(key, value)
        else:
            raise RuntimeError("Can't modify immutable object's attribute: {}".format(key))
    """

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


def infer(judgment, rules):
    for rule in rules:  # try each rule
        try:
            assignment = unify([(judgment, rule.conclusion)])  # if one rule matches
            prem_deriv = [infer(subs_metavariables(p, assignment), rules) for p in rule.premises]  # fulfill premises
            if None in prem_deriv:  # fails
                continue
            # Succeeded. We collect the derivation tree and assignments
            try:
                full_assignment = merge_dicts(assignment, *(a for d, a in prem_deriv))
            except ValueError as v:
                # print("[INFER] Merge conflict.")  # Debug; need to remove this
                continue  # merge conflict
            conclusion = subs_metavariables(judgment, full_assignment)
            if get_metavariables(conclusion) != dict():
                # or this?? : any(isinstance(e, MetaVariable) for e in full_assignment.items()):
                print(conclusion)
                # print("[INFER] Unable to fully infer all unknowns.")
                continue
            return rule(tuple(p for p, a in prem_deriv), conclusion), \
                   {k: full_assignment[k] for k in get_metavariables(judgment)}
        except ValueError as v:
            continue
    # by now no rules apply, so fail
    return None


if __name__ == "__main__":
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

    OneIsNat_auto = infer(isNat(Succ(Zero)), [Onat, Snat])
