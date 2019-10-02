from abt import *
from pattern import *


class JudgmentForm(Node):
    judgmentSort = PrimitiveSort("judgment")

    def __init__(self, name, args, repr=None):
        super().__init__(name, self.judgmentSort, args, repr)


class InferenceRule:
    def __init__(self, name, premises, conclusion, condition=None):
        # condition is additional conditions that may be present.
        # This should be a function accepting a dict
        self.name = name
        self.premises = tuple(premises)
        self.conclusion = conclusion
        self.variables = merge_dicts(get_metavariables(conclusion), *map(get_metavariables, premises))
        self.condition = condition \
            if condition is not None else lambda *_: True

    def __call__(self, pr, concl):
        return Derivation(self, pr, concl)

    def __repr__(self):
        return self.name


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

    def __repr__(self):
        return "Derivation of %s" % repr(self.conclusion)

    def _pretty(self):
        if len(self.premises) == 0:
            a = ['']
            width = 0
        else:
            derivstrs = [p._pretty() for p in self.premises]
            derivlens = list(map(lambda l: len(l[0]), derivstrs))
            a = []
            while not all(len(i) == 0 for i in derivstrs):
                a.insert(0, '  '.join(i.pop() if len(i) != 0 else " " * derivlens[n]
                                      for n, i in enumerate(derivstrs)))
            width = len(a[-1])
        concl = repr(self.conclusion)
        wc = len(concl)
        total_width = max(width, wc) + 2
        return [ai.center(total_width, ' ') for ai in a] + \
               ['-' * total_width] + [concl.center(total_width, ' ')]

    def pretty(self):
        return '\n'.join(self._pretty())

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
            # at last.. check the additional conditions
            if not rule.condition({v : full_assignment[v] for v in rule.variables}):
                continue
            return rule(tuple(p for p, a in prem_deriv), conclusion), \
                   {k: full_assignment[k] for k in get_metavariables(judgment)}
        except ValueError as v:
            continue
    # by now no rules apply, so fail
    return None
