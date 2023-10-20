# -*- coding: utf-8 -*-

import re

from wff import FormulaInfo, get_free_variables_in_term, is_variable

def check_well_formed_formula(s):
    opr, opd = [], []
    def opr_top():
        return opr[-1] if opr else 'X'
    def opr_push(x):
        return opr.append(x)
    def opd_push(x):
        assert not (x[2] & x[3])
        return opd.append(x)
    nope = FormulaInfo(False, set(), set())
    try:
        for token in re.split('(S*0)|(S*[a-z]′*)|(S+)|(.)', s):
            if not token:
                continue
            if is_variable(token):
                if opr_top() in '∀∃':
                    opd_push(['V', token, set([token]), set()])
                else:
                    opd_push(['T', token, set([token]), set()])
            elif re.match('(S*0)|(S*[a-z]′*)', token):
                opd_push(['T', token, get_free_variables_in_term(token), set()])
            elif re.match('S+', token):
                opr_push(token)
            elif token in '<(∀∃:+⋅~':
                opr_push(token)
            elif token == '=':
                if re.match('S+', opr_top()):
                    op = opr.pop()
                    t1 = opd.pop()
                    if t1[0] != 'T': return nope
                    opd_push(['T', op + t1[1], t1[2], set()])
                opr_push(token)
            elif token == ')':
                t2 = opd.pop()
                t1 = opd.pop()
                op = opr.pop()
                if opr.pop() != '(': return nope
                if op not in '+⋅': return nope
                if t1[0] != 'T' or t2[0] != 'T': return nope
                opd_push(['T', '(%s%s%s)' % (t1[1], op, t2[1]), t1[2] | t2[2], set()])
                if re.match('S+', opr_top()):
                    op = opr.pop()
                    t1 = opd.pop()
                    opd_push(['T', op + t1[1], t1[2], set()])
            elif token in '∧∨⊃':
                if re.match('S+', opr_top()):
                    op = opr.pop()
                    t1 = opd.pop()
                    if t1[0] != 'T': return nope
                    opd_push(['T', op + t1[1], t1[2], set()])
                if opr_top() == '=':
                    t2 = opd.pop()
                    t1 = opd.pop()
                    op = opr.pop()
                    if t1[0] != 'T' or t2[0] != 'T': return nope
                    opd_push(['F', '%s=%s' % (t1[1], t2[1]), t1[2] | t2[2], set()])
                while opr_top() in ':~':
                    op = opr.pop()
                    if op == '~':
                        t1 = opd.pop()
                        if t1[0] != 'F': return nope
                        opd_push(['F', '~%s' % t1[1], t1[2], t1[3]])
                    elif op == ':':
                        x = opd.pop()
                        v = opd.pop()
                        op = opr.pop()
                        if op not in '∀∃': return nope
                        if x[0] != 'F' or v[0] != 'V': return nope
                        if v[1] not in x[2]: return nope  # v must be free in x
                        opd_push(['F', '%s%s:%s' % (op, v[1], x[1]), x[2] - set([v[1]]), x[3] | set([v[1]])])
                opr_push(token)
            elif token == '>':
                if opr_top() == '=':
                    t2 = opd.pop()
                    t1 = opd.pop()
                    op = opr.pop()
                    if t1[0] != 'T' or t2[0] != 'T': return nope
                    opd_push(['F', '%s=%s' % (t1[1], t2[1]), t1[2] | t2[2], set()])
                while opr_top() in ':~':
                    op = opr.pop()
                    if op == '~':
                        t1 = opd.pop()
                        if t1[0] != 'F': return nope
                        opd_push(['F', '~%s' % t1[1], t1[2], t1[3]])
                    elif op == ':':
                        x = opd.pop()
                        v = opd.pop()
                        op = opr.pop()
                        if op not in '∀∃': return nope
                        if x[0] != 'F' or v[0] != 'V': return nope
                        if v[1] not in x[2]: return nope  # v must be free in x
                        opd_push(['F', '%s%s:%s' % (op, v[1], x[1]), x[2] - set([v[1]]), x[3] | set([v[1]])])
                t2 = opd.pop()
                t1 = opd.pop()
                op = opr.pop()
                if opr.pop() != '<': return nope
                if op not in '∧∨⊃': return nope
                if t1[0] != 'F' or t2[0] != 'F': return nope
                fv = (t1[2] | t2[2])
                qv = (t1[3] | t2[3])
                if (fv & qv):
                    return nope
                opd_push(['F', '<%s%s%s>' % (t1[1], op, t2[1]), fv, qv])
            else:
                assert False
        while opr:
            if re.match('S+', opr_top()):
                op = opr.pop()
                t1 = opd.pop()
                if t1[0] != 'T': return nope
                opd_push(['T', op + t1[1], t1[2], set()])
            elif opr_top() == '=':
                t2 = opd.pop()
                t1 = opd.pop()
                op = opr.pop()
                if t1[0] != 'T' or t2[0] != 'T': return nope
                opd_push(['F', '%s=%s' % (t1[1], t2[1]), t1[2] | t2[2], set()])
            elif opr_top() == '~':
                t1 = opd.pop()
                assert opr.pop() == '~'
                if t1[0] != 'F': return nope
                opd_push(['F', '~%s' % t1[1], t1[2], t1[3]])
            elif opr_top() == ':':
                x = opd.pop()
                v = opd.pop()
                assert opr.pop() == ':'
                op = opr.pop()
                if op not in '∀∃': return nope
                if x[0] != 'F' or v[0] != 'V': return nope
                if v[1] not in x[2]: return nope  # v must be free in x
                opd_push(['F', '%s%s:%s' % (op, v[1], x[1]), x[2] - set([v[1]]), x[3] | set([v[1]])])
            else:
                return nope
        result = opd.pop()
        if opd: return nope
        if result[1] != s:
            print('x is', s)
            print('r is', result[1])
            assert False
        return FormulaInfo(result[0] == 'F', result[2], result[3])
    except IndexError:
        # Failed to pop something from one of the two stacks.
        return nope

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
assert get_quantified_variables('∀a:<∃a′:(a⋅a′)=a′′⊃∃a′:(a′⋅SS0)=a>') == set(['a', 'a′'])
assert get_free_variables('∀a:<∃a′:(a⋅a′)=a′′⊃∃a′:(a′⋅SS0)=a>') == set(['a′′'])
