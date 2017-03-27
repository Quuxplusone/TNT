# -*- coding: utf-8 -*-

import re

def U(s):
    if type(s) is unicode:
        return s
    return s.decode('utf8')

def is_alphabetically_correct(s):
    return set(s) <= set(u'0Sabcdefghijklmnopqrstuvwxyz′(+⋅)=~<∧∨⊃>∀∃:')

def is_numeral(s):
    return bool(re.match('S*0$', U(s)))

assert all(is_numeral(x) for x in ['0', 'S0', 'SS0', 'SSS0', 'SSSS0', 'SSSSS0'])

def is_variable(s):
    return bool(re.match(u'[a-z]′*$', U(s)))

assert all(is_variable(x) for x in ['a', 'b′', 'c′′', 'd′′′', 'e′′′′'])

def is_term(s):
    s = U(s)
    while s and s[0] == 'S':
        s = s[1:]
    if not s:
        return False
    if s[0] == '(' and s[-1] == ')':
        for i in range(len(s)):
            if s[i] in u'+⋅' and is_term(s[1:i]) and is_term(s[i+1:-1]):
                return True
    if is_numeral(s) or is_variable(s):
        return True
    return False

def get_free_variables_in_term(s):
    return set(re.findall(u'[a-z]′*', U(s)))

def is_definite_term(s):
    return is_term(s) and not get_free_variables_in_term(s)

def is_indefinite_term(s):
    return is_term(s) and get_free_variables_in_term(s)

assert all(is_definite_term(x) for x in ['0', '(S0+S0)', 'SS((SS0⋅SS0)+(S0⋅S0))'])
assert all(is_indefinite_term(x) for x in ['b', 'Sa', '(b′+S0)', '(((S0+S0)⋅S0)+e)'])

class FormulaInfo:
    def __init__(self, wf, fv, qv):
        assert type(qv) in [type(set()), type(None)]
        assert type(fv) in [type(set()), type(None)]
        self.is_well_formed = wf
        self.free_variables = fv
        self.quantified_variables = qv
    def __nonzero__(self):
        assert False  # you shouldn't be calling this

def check_atom(s):
    s = U(s)
    for i in range(len(s)):
        if s[i] == '=':
            t1, t2 = s[:i], s[i+1:]
            if is_term(t1) and is_term(t2):
                return FormulaInfo(True, get_free_variables_in_term(t1) | get_free_variables_in_term(t2), set())
    return FormulaInfo(False, None, None)

assert all(check_atom(x).is_well_formed for x in ['S0=0', '(SS0+SS0)=SSSS0', 'S(b+c)=((c⋅d)⋅e)'])

def check_negation(s):
    s = U(s)
    if s and s[0] == '~':
        return check_well_formed_formula(s[1:])
    return FormulaInfo(False, None, None)

def check_compound(s):
    s = U(s)
    if s and s[0] == '<' and s[-1] == '>':
        for i in range(len(s)):
            if s[i] in u'∧∨⊃':
                f1 = check_well_formed_formula(s[1:i])
                f2 = check_well_formed_formula(s[i+1:-1])
                if f1.is_well_formed and f2.is_well_formed:
                    fv = (f1.free_variables | f2.free_variables)
                    qv = (f1.quantified_variables | f2.quantified_variables)
                    if not (fv & qv):
                        return FormulaInfo(True, fv, qv)
                    break
    return FormulaInfo(False, None, None)

def check_quantification(s):
    s = U(s)
    if s and s[0] in u'∀∃':
        colon = s.find(':')
        if colon >= 0:
            v = s[1:colon]
            f = check_well_formed_formula(s[colon+1:])
            if is_variable(v) and f.is_well_formed and (v in f.free_variables):
                return FormulaInfo(True, f.free_variables - set([v]), f.quantified_variables | set([v]))
    return FormulaInfo(False, None, None)

def check_well_formed_formula(s):
    s = U(s)
    for check in [check_atom, check_negation, check_compound, check_quantification]:
        f = check(s)
        if f.is_well_formed:
            return f
    return FormulaInfo(False, None, None)

assert all(check_negation(x).is_well_formed for x in ['~S0=0', '~∃b:(b+b)=S0', '~<0=0⊃S0=0>', '~b=S0', '~∃c:Sc=d'])
assert all(check_compound(x).is_well_formed for x in ['<0=0∧~0=0>', '<b=b∨~∃c:c=b>', '<S0=0⊃∀c:~∃b:(b+b)=c>'])
assert all(check_quantification(x).is_well_formed for x in ['∀b:<b=b∨~∃c:c=b>', '∀c:~∃b:(b+b)=c'])

def is_well_formed_formula(s):
    return check_well_formed_formula(s).is_well_formed

def get_free_variables(s):
    return check_well_formed_formula(s).free_variables

def get_quantified_variables(s):
    return check_well_formed_formula(s).quantified_variables

assert is_well_formed_formula('∀a:a=SSSS0')  # "All natural numbers are equal to 2."
assert is_well_formed_formula('~∃a:(a⋅a)=a')  # "There is no natural number which equals its own square."
assert is_well_formed_formula('∀a:∀b:<~a=b⊃~Sa=Sb>')  # "Different natural numbers have different successors."
assert is_well_formed_formula('<S0=0⊃∀a:~∃b:(b⋅SS0)=a>')  # "If 1 equals 0, then every number is odd."
assert is_well_formed_formula('∀c:<∃d:(c⋅d)=b⊃∃d:(d⋅SS0)=c>')  # "b is a power of 2."
assert is_well_formed_formula('∃a:∃x:∃y:<<∃d:∃e:<x=(d⋅SSy)∧y=Se>∧∃d:∃e:<x=((d⋅S(Sa⋅y))+b)∧(Sa⋅y)=(b+e)>>∧∀k:∀z:<<∃n:(k+Sn)=a∧∃d:∃e:<x=((d⋅S(Sk⋅y))+z)∧(Sk⋅y)=(z+e)>>⊃∃d:∃e:<x=((d⋅S(SSk⋅y))+(SSSSSSSSSS0⋅z))∧S(SSk⋅y)=(S(SSSSSSSSSS0⋅z)+e)>>>')  # "b is a power of 10."

assert get_quantified_variables('∀c:<∃d:(c⋅d)=b⊃∃d:(d⋅SS0)=c>') == set(['c', 'd'])
assert get_free_variables('∀c:<∃d:(c⋅d)=b⊃∃d:(d⋅SS0)=c>') == set(['b'])
assert get_quantified_variables('∀a:<∃a′:(a⋅a′)=a′′⊃∃a′:(a′⋅SS0)=a>') == set(['a', u'a′'])
assert get_free_variables('∀a:<∃a′:(a⋅a′)=a′′⊃∃a′:(a′⋅SS0)=a>') == set([u'a′′'])
