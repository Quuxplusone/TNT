# -*- coding: utf-8 -*-

import time

import wff as wff_slow
import wff_quick as wff
import wff_quick as wff_quick
from derivation import Derivation

def allocates_only_quantified_variables(memberfunc):
    def wrap(self, *args):
        sr = self.save_r()
        result = memberfunc(self, *args)
        self.restore_r(sr)
        fvs = [wff.get_free_variables(a) for a in args]
        fvs = map(list, fvs)
        fvs = set(sum(fvs, []))
        assert wff.get_free_variables(result) == fvs
        return result
    return wrap

class Encoder:
    def __init__(self):
        self.alphabet = 'abcdefghkmnopqrstuwxyz'
        self.exclude = set()
        self.r = None

    def do_not_allocate_variables_in_terms(self, *exclude):
        for t in exclude:
            self.exclude |= wff.get_free_variables_in_term(t)

    def reg(self, *exclude):
        if self.r is None:
            self.r = self.alphabet[0]
        if self.r[0] == self.alphabet[-1]:
            self.r = self.alphabet[0] + '′' + self.r[1:]
        else:
            self.r = self.alphabet[self.alphabet.find(self.r[0])+1] + self.r[1:]
        return self.reg() if self.r in self.exclude else self.r

    def save_r(self):
        return self.r

    def restore_r(self, saved_r):
        self.r = saved_r

    def numeral(self, n):
        return ''.join('S' for i in range(n)) + '0'

    @allocates_only_quantified_variables
    def a_lessthan_b(self, a, b):
        self.do_not_allocate_variables_in_terms(a,b)
        r = self.reg()
        return '∃{r}:({a}+S{r})={b}'.format(**locals())

    @allocates_only_quantified_variables
    def a_mod_b_equals_c(self, a, b, c):
        self.do_not_allocate_variables_in_terms(a,b,c)
        r = self.reg()
        c_lessthan_b = self.a_lessthan_b(c, b)
        result = '∃{r}:<{a}=(({b}⋅{r})+{c})∧{c_lessthan_b}>'.format(**locals())
        return result

    @allocates_only_quantified_variables
    def abs_kth_term_is_x(self, a, b, k, x):
        # The finite sequence "AB" is defined as
        #   AB(0) = a mod (b+1)
        #   AB(1) = a mod (2b+1)
        #   AB(2) = a mod (3b+1)
        #   ...
        # According to http://math.stackexchange.com/a/312915/121469,
        # any finite sequence can be represented in this way for at least one pair (a,b).
        result = self.a_mod_b_equals_c(a, 'S({b}⋅S{k})'.format(**locals()), x)
        assert wff.is_well_formed_formula(result)
        return result

    def all(self, *args):
        if len(args) == 1:
            return args[0]
        fv, qv = set(), set()
        for a in args:
            assert wff.is_well_formed_formula(a)
            fv |= wff.get_free_variables(a)
            qv |= wff.get_quantified_variables(a)
        assert not (qv & fv)
        return '<%s∧%s>' % (args[0], self.all(*args[1:]))

    @allocates_only_quantified_variables
    def a_raised_to_b_is_c(self, a, b, c):
        self.do_not_allocate_variables_in_terms(a,b,c)
        x, y, k, z = [self.reg() for i in [1,2,3,4]]
        first_term_is_1 = self.abs_kth_term_is_x(x, y, self.numeral(0), self.numeral(1))
        bth_term_is_c = self.abs_kth_term_is_x(x, y, b, c)
        kth_term_is_z = self.abs_kth_term_is_x(x, y, k, z)
        k1th_term_is_az = self.abs_kth_term_is_x(x, y, 'S'+k, '({a}⋅{z})'.format(**locals()))
        k_lessthan_b = self.a_lessthan_b(k, b)
        inductive_case = '∀{k}:∀{z}:<<{k_lessthan_b}∧{kth_term_is_z}>⊃{k1th_term_is_az}>'.format(**locals())
        return '∃%s:∃%s:%s' % (x, y, self.all(first_term_is_1, bth_term_is_c, inductive_case))

assert Encoder().numeral(0) == '0'
assert Encoder().numeral(3) == 'SSS0'

class MIUEncoder(Encoder):
    def godel_number(self, s):
        n = 0
        for ch in s:
            if ch == 'M':
                n = 10*n + 3
            elif ch == 'I':
                n = 10*n + 1
            elif ch == 'U':
                n = 10*n + 0
            else:
                assert False
        return n

    @allocates_only_quantified_variables
    def s_is_derivable_from_t_by_axiom_1(self, s, t):
        self.do_not_allocate_variables_in_terms(s,t)
        m = self.reg()
        ten = self.numeral(10)
        t_is_m1 = '∃{m}:{t}=(({ten}⋅{m})+S0)'.format(**locals())
        s_is_m10 = '{s}=({ten}⋅{t})'.format(**locals())
        return self.all(t_is_m1, s_is_m10)

    @allocates_only_quantified_variables
    def s_is_derivable_from_t_by_axiom_2(self, s, t):
        self.do_not_allocate_variables_in_terms(s,t)
        m, n, p = [self.reg() for i in [1,2,3]]
        ten = self.numeral(10)
        p_is_ten_to_m = self.a_raised_to_b_is_c(self.numeral(10), m, p)
        n_lessthan_p = self.a_lessthan_b(n, p)
        t_is_3n = '{t}=((SSS0⋅{p})+{n})'.format(**locals())
        s_is_3nn = '{s}=(({p}⋅{t})+{n})'.format(**locals())
        return '∃%s:∃%s:∃%s:%s' % (m, n, p, self.all(p_is_ten_to_m, n_lessthan_p, t_is_3n, s_is_3nn))

    @allocates_only_quantified_variables
    def s_is_derivable_from_t_by_axiom_3(self, s, t):
        self.do_not_allocate_variables_in_terms(s,t)
        k, m, n, p, q = [self.reg() for i in [1,2,3,4,5]]
        ten = self.numeral(10)
        p_is_ten_to_m = self.a_raised_to_b_is_c(self.numeral(10), m, p)
        n_lessthan_p = self.a_lessthan_b(n, p)
        q_is_ten_to_mplus3 = self.a_raised_to_b_is_c(self.numeral(10), 'SSS' + m, q)
        n111 = '((%s⋅S%s)+S0)' % (ten, ten)
        t_is_k111n = '{t}=((({k}⋅{q})+({n111}⋅{p}))+{n})'.format(**locals())
        s_is_kn = '{s}=((({ten}⋅{k})⋅{p})+{n})'.format(**locals())
        return '∃%s:∃%s:∃%s:∃%s:∃%s:%s' % (k, m, n, p, q, self.all(
            p_is_ten_to_m, n_lessthan_p, q_is_ten_to_mplus3, t_is_k111n, s_is_kn
        ))

    @allocates_only_quantified_variables
    def s_is_derivable_from_t_by_axiom_4(self, s, t):
        self.do_not_allocate_variables_in_terms(s,t)
        k, m, n, p, q = [self.reg() for i in [1,2,3,4,5]]
        ten = self.numeral(10)
        p_is_ten_to_m = self.a_raised_to_b_is_c(self.numeral(10), m, p)
        n_lessthan_p = self.a_lessthan_b(n, p)
        q_is_ten_to_mplus2 = self.a_raised_to_b_is_c(self.numeral(10), 'SS' + m, q)
        t_is_k00n = '{t}=(({k}⋅{q})+{n})'.format(**locals())
        s_is_kn = '{s}=(({k}⋅{p})+{n})'.format(**locals())
        return '∃%s:∃%s:∃%s:∃%s:∃%s:%s' % (k, m, n, p, q, self.all(
            p_is_ten_to_m, n_lessthan_p, q_is_ten_to_mplus2, t_is_k00n, s_is_kn
        ))

    @allocates_only_quantified_variables
    def s_is_directly_derivable_from_t(self, s, t):
        return self.all(
            self.s_is_derivable_from_t_by_axiom_1(s, t),
            self.s_is_derivable_from_t_by_axiom_2(s, t),
            self.s_is_derivable_from_t_by_axiom_3(s, t),
            self.s_is_derivable_from_t_by_axiom_4(s, t),
        )

    @allocates_only_quantified_variables
    def s_is_derivable_from_t(self, s, t):
        self.do_not_allocate_variables_in_terms(s,t)
        x, y, k, n, p, q = [self.reg() for i in [1,2,3,4,5,6]]
        first_term_is_t = self.abs_kth_term_is_x(x, y, self.numeral(0), t)
        nth_term_is_s = self.abs_kth_term_is_x(x, y, n, s)
        k_lessthan_n = self.a_lessthan_b(k, n)
        kth_term_is_p = self.abs_kth_term_is_x(x, y, k, p)
        k1th_term_is_q = self.abs_kth_term_is_x(x, y, 'S'+k, q)
        p_implies_q = self.s_is_directly_derivable_from_t(q, p)
        inductive_case = '∀%s:∀%s:∀%s:<%s⊃%s>' % (k, p, q, self.all(
            k_lessthan_n,
            kth_term_is_p,
            k1th_term_is_q,
        ), p_implies_q)
        return '∃%s:∃%s:∃%s:%s' % (x,y,n, self.all(
            first_term_is_t,
            nth_term_is_s,
            inductive_case,
        ))

    @allocates_only_quantified_variables
    def t_mod_3_is_0(self, t):
        self.do_not_allocate_variables_in_terms(t)
        x = self.reg()
        return '∃{x}:(SSS0⋅{x})={t}'.format(**locals())

    @allocates_only_quantified_variables
    def mumon(self):
        return self.s_is_derivable_from_t(self.numeral(self.godel_number('MU')), self.numeral(self.godel_number('MI')))

if __name__ == '__main__':
    assert wff.is_well_formed_formula(MIUEncoder().s_is_directly_derivable_from_t('s', 't'))
    assert wff.is_well_formed_formula(MIUEncoder().s_is_derivable_from_t('s', 't'))

    b_is_a_power_of_10 = '∃c:' + Encoder().a_raised_to_b_is_c(Encoder().numeral(10), 'c', 'b')
    print('A TNT expression encoding the statement "b is a power of 10" is:')
    print(b_is_a_power_of_10)
    assert wff.is_well_formed_formula(b_is_a_power_of_10)

    print('Computing MUMON...')
    mumon = MIUEncoder().mumon()
    print(mumon)

    e = MIUEncoder()
    print('Lemma 1 for proving MU underivable:')
    print('∀s:∀t:<<%s∧%s>⊃%s>' % (e.t_mod_3_is_0('t'), e.s_is_derivable_from_t_by_axiom_1('s', 't'), e.t_mod_3_is_0('s')))
    e = MIUEncoder()
    print('Lemma 2 for proving MU underivable:')
    print('∀s:∀t:<<%s∧%s>⊃%s>' % (e.t_mod_3_is_0('t'), e.s_is_derivable_from_t_by_axiom_2('s', 't'), e.t_mod_3_is_0('s')))
    e = MIUEncoder()
    print('Lemma 3 for proving MU underivable:')
    print('∀s:∀t:<<%s∧%s>⊃%s>' % (e.t_mod_3_is_0('t'), e.s_is_derivable_from_t_by_axiom_3('s', 't'), e.t_mod_3_is_0('s')))
    e = MIUEncoder()
    print('Lemma 4 for proving MU underivable:')
    print('∀s:∀t:<<%s∧%s>⊃%s>' % (e.t_mod_3_is_0('t'), e.s_is_derivable_from_t_by_axiom_4('s', 't'), e.t_mod_3_is_0('s')))

    start = time.time()
    assert wff_quick.is_well_formed_formula(mumon)
    print('is_wff_quick took %s seconds' % (time.time() - start))
    start = time.time()
    assert wff_slow.is_well_formed_formula(mumon)
    print('is_wff took %s seconds' % (time.time() - start))
