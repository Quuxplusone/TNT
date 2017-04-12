# -*- coding: utf-8 -*-

import contextlib
import re

import wff_quick as wff
from wff import U, is_term, is_variable

class InvalidStep:
    pass

class Derivation:
    def __init__(self, fantasy_setup=None):
        self.handwaving = False
        if fantasy_setup is None:
            self.premise = None
            self.theorems = set([
                u'∀a:~Sa=0',
                u'∀a:(a+0)=a',
                u'∀a:∀b:(a+Sb)=S(a+b)',
                u'∀a:(a⋅0)=0',
                u'∀a:∀b:(a⋅Sb)=((a⋅b)+a)',
            ])
            self.conclusion = None
        else:
            self.premise, self.theorems = fantasy_setup
            self.theorems.add(self.premise)
            self.conclusion = self.premise

    def is_valid_by_joining(self, s):
        s = U(s)
        if s[0] == '<' and s[-1] == '>':
            for i in range(len(s)):
                if s[i] == u'∧':
                    first, second = s[1:i], s[i+1:-1]
                    if set([first, second]) <= self.theorems:
                        return True
        return False

    def is_valid_by_separation(self, s):
        s = U(s)
        if not wff.is_well_formed_formula(s):
            return False
        for theorem in self.theorems:
            if theorem[0] == '<' and theorem[-1] == '>':
                if theorem.startswith(u'<%s∧' % s):
                    return True
                if theorem.endswith(u'∧%s>' % s):
                    return True
        return False

    def is_removal_of_double_tilde(self, shorter, longer):
        if len(shorter)+2 == len(longer):
            if sorted(shorter + u'~~') == sorted(longer):
                for i in range(len(shorter)):
                    if longer == shorter[:i] + '~~' + shorter[i:]:
                        return True
        return False

    def is_valid_by_double_tilde(self, s):
        s = U(s)
        if not wff.is_well_formed_formula(s):
            return False

        for theorem in self.theorems:
            if self.is_removal_of_double_tilde(s, theorem) or self.is_removal_of_double_tilde(theorem, s):
                return True
        return False

    def is_valid_by_detachment(self, s):
        s = U(s)
        for theorem in self.theorems:
            implication = u'<%s⊃%s>' % (theorem, s)
            if implication in self.theorems:
                return True  # because of the implication
        return False

    def _is_valid_by_substituting(self, s, a, b):
        s = U(s)
        for xi in range(0, len(s)):
            for xj in range(xi+1, len(s)):
                x = s[xi:xj]
                if wff.is_well_formed_formula(x):
                    for yi in range(0, len(s)):
                        for yj in range(yi+1, len(s)):
                            y = s[yi:yj]
                            if wff.is_well_formed_formula(y):
                                first = a.replace('X', x).replace('Y', y)
                                if len(first) > len(s):
                                    continue
                                second = b.replace('X', x).replace('Y', y)
                                i = s.find(first)
                                while i != -1:
                                    substituted_s = s[:i] + second + s[i+len(first):]
                                    if substituted_s in self.theorems:
                                        return True
                                    i = s.find(first, i+1)
        return False

    def _is_valid_by_interchanging(self, s, a, b):
        return self._is_valid_by_substituting(s, a, b) or self._is_valid_by_substituting(s, b, a)

    def is_valid_by_contrapositive(self, s):
        return self._is_valid_by_interchanging(s, u'<X⊃Y>', u'<~Y⊃~X>')

    def is_valid_by_de_morgans(self, s):
        return self._is_valid_by_interchanging(s, u'<~X∧~Y>', u'~<X∨Y>')

    def is_valid_by_switcheroo(self, s):
        return self._is_valid_by_interchanging(s, u'<X∨Y>', u'<~X⊃Y>')

    def _is_substitution_of_some_term_for_variable(self, u, a, b):
        if a == b:
            return True
        us_in_a = a.count(u)
        length_of_a_without_us = len(a) - (us_in_a * len(u))
        if len(b) < length_of_a_without_us:
            return False
        if (len(b) - length_of_a_without_us) % us_in_a != 0:
            return False
        length_of_replacement = (len(b) - length_of_a_without_us) / us_in_a
        first_u_in_a = a.find(u)
        if not b.startswith(a[:first_u_in_a]):
            return False
        replacement = b[first_u_in_a:first_u_in_a + length_of_replacement]
        if not is_term(replacement):
            return False
        if wff.get_free_variables_in_term(replacement) & wff.get_quantified_variables(a):
            return False
        return (b == a.replace(u, replacement))

    def is_valid_by_specification(self, s):
        s = U(s)
        for theorem in self.theorems:
            if theorem.startswith(u'∀'):
                colon = theorem.find(':')
                if colon >= 0:
                    u, x = theorem[1:colon], theorem[colon+1:]
                    assert is_variable(u)
                    if self._is_substitution_of_some_term_for_variable(u, x, s):
                        return True
        return False

    def is_valid_by_generalization(self, s):
        s = U(s)
        if s.startswith(u'∀'):
            colon = s.find(':')
            if colon >= 0:
                u, x = s[1:colon], s[colon+1:]
                if wff.is_variable(u) and u in wff.get_free_variables(x):
                    if self.premise is not None and u in wff.get_free_variables(self.premise):
                        return False
                    if x in self.theorems:
                        return True
        return False

    def is_valid_by_interchange(self, s):
        s = U(s)
        for theorem in self.theorems:
            if len(theorem) == len(s):
                a = theorem.find(u'∀')
                while a >= 0 and s[:a] == theorem[:a]:
                    if s[a:a+2] == u'~∃':
                        colon = theorem.find(':', a+1)
                        u = theorem[a+1:colon]
                        assert is_variable(u)
                        if theorem[colon+1] == '~':
                            if s == theorem[:a] + u'~∃' + u + ':' + theorem[colon+2:]:
                                return True
                    a = theorem.find(u'∀', a+1)
                ne = theorem.find(u'~∃')
                while ne >= 0 and s[:ne] == theorem[:ne]:
                    if s[ne] == u'∀':
                        colon = theorem.find(':', ne+2)
                        u = theorem[ne+2:colon]
                        assert is_variable(u)
                        if s == theorem[:ne] + u'∀' + u + ':~' + theorem[colon+1:]:
                            return True
                    ne = theorem.find(u'~∃', ne+2)
        return False

    def is_valid_by_existence(self, s):
        s = U(s)
        if s.startswith(u'∃'):
            colon = s.find(':')
            if colon >= 0:
                u, x = s[1:colon], s[colon+1:]
                if is_variable(u) and u in wff.get_free_variables(x):
                    for theorem in self.theorems:
                        if self._is_substitution_of_some_term_for_variable(u, x, theorem):
                            return True
        return False

    def is_valid_by_equality(self, s):
        s = U(s)
        equals = s.find('=')
        if equals > 0:
            first, second = s[:equals], s[equals+1:]
            if is_term(first) and is_term(second):
                symmetrical_s = u'%s=%s' % (second, first)
                if symmetrical_s in self.theorems:
                    return True
            for theorem in self.theorems:
                if theorem.startswith(first + '='):
                    middle = theorem[len(first)+1:]
                    transitive_s = u'%s=%s' % (middle, second)
                    if transitive_s in self.theorems:
                        return True
        return False

    def is_valid_by_successorship(self, s):
        s = U(s)
        equals = s.find('=')
        if equals > 0:
            first, second = s[:equals], s[equals+1:]
            if is_term(first) and is_term(second):
                add_s = u'S%s=S%s' % (first, second)
                if add_s in self.theorems:
                    return True
                if first[0] == 'S' and second[0] == 'S':
                    drop_s = u'%s=%s' % (first[1:], second[1:])
                    if drop_s in self.theorems:
                        return True
        return False

    def is_valid_by_induction(self, s):
        s = U(s)
        if wff.is_well_formed_formula(s) and s[0] == u'∀':
            colon = s.find(':')
            assert colon >= 0
            u, x = s[1:colon], s[colon+1:]
            assert is_variable(u)
            base_case = x.replace(u, '0')
            if base_case in self.theorems:
                inductive_case = u'∀%s:<%s⊃%s>' % (u, x, x.replace(u, 'S' + u))
                if inductive_case in self.theorems:
                    return True
        return False

    def is_valid_new_theorem(self, s):
        s = U(s)
        return (
            (s in self.theorems) or
            self.is_valid_by_joining(s) or
            self.is_valid_by_separation(s) or
            self.is_valid_by_double_tilde(s) or
            self.is_valid_by_detachment(s) or
            self.is_valid_by_contrapositive(s) or
            self.is_valid_by_de_morgans(s) or
            self.is_valid_by_switcheroo(s) or
            self.is_valid_by_specification(s) or
            self.is_valid_by_generalization(s) or
            self.is_valid_by_interchange(s) or
            self.is_valid_by_existence(s) or
            self.is_valid_by_equality(s) or
            self.is_valid_by_successorship(s) or
            self.is_valid_by_induction(s) or
            False
        )

    def handwave(self):
        self.handwaving = True

    def step(self, s):
        s = U(s)
        if not (self.handwaving or self.is_valid_new_theorem(s)):
            raise InvalidStep()
        self.handwaving = False
        self.theorems.add(s)
        self.conclusion = s

    @contextlib.contextmanager
    def fantasy(self, premise):
        f = Derivation([U(premise), self.theorems.copy()])
        yield f
        s = u'<%s⊃%s>' % (f.premise, f.conclusion)
        self.theorems.add(s)
        self.conclusion = s

    def print_all_theorems(self):
        for theorem in self.theorems:
            print theorem
