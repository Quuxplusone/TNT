# -*- coding: utf-8 -*-

from derivation import Derivation, InvalidStep
from wff_quick import is_well_formed_formula

# Page 188:
d = Derivation()
with d.fantasy('<p=0⊃~~p=0>') as f:
    f.step('<~~~p=0⊃~p=0>')  # contrapositive
    f.step('<~p=0⊃~p=0>')    # double-tilde
    f.step('<p=0∨~p=0>')     # switcheroo

# Pages 189–190:
d = Derivation()
with d.fantasy('<<p=0⊃q=0>∧<~p=0⊃q=0>>') as f:
    f.step('<p=0⊃q=0>')     # separation
    f.step('<~q=0⊃~p=0>')   # contrapositive
    f.step('<~p=0⊃q=0>')    # separation
    f.step('<~q=0⊃~~p=0>')  # contrapositive
    with f.fantasy('~q=0') as g:  # push again
        g.step('~q=0')            # premise
        g.step('<~q=0⊃~p=0>')     # carry-over of line 4
        g.step('~p=0')            # detachment
        g.step('<~q=0⊃~~p=0>')    # carry-over of line 6
        g.step('~~p=0')           # detachment
        g.step('<~p=0∧~~p=0>')    # joining
        g.step('~<p=0∨~p=0>')     # De Morgan
    f.step('<~q=0⊃~<p=0∨~p=0>>')  # fantasy rule
    f.step('<<p=0∨~p=0>⊃q=0>')  # contrapositive
    with f.fantasy('~p=0') as g:
        pass
    f.step('<~p=0⊃~p=0>')   # fantasy rule
    f.step('<p=0∨~p=0>')    # switcheroo
    f.step('q=0')           # detachment

# Page 196:
d = Derivation()
with d.fantasy('<p=0∧~p=0>') as f:
    f.step('p=0')           # separation
    f.step('~p=0')          # separation
    with f.fantasy('~q=0') as g:
        g.step('p=0')       # carry-over line 3
        g.step('~~p=0')     # double-tilde
    f.step('<~q=0⊃~~p=0>')  # fantasy
    f.step('<~p=0⊃q=0>')    # contrapositive
    f.step('q=0')           # detachment
d.step('<<p=0∧~p=0>⊃q=0>')

# Page 219: 1 plus 1 equals 2.
d = Derivation()
d.step('∀a:∀b:(a+Sb)=S(a+b)')
d.step('∀b:(S0+Sb)=S(S0+b)')
d.step('(S0+S0)=S(S0+0)')
d.step('∀a:(a+0)=a')
d.step('(S0+0)=S0')
d.step('S(S0+0)=SS0')
d.step('(S0+S0)=SS0')

# Page 219: 1 times 1 equals 1.
d = Derivation()
d.step('∀a:∀b:(a⋅Sb)=((a⋅b)+a)')
d.step('∀b:(S0⋅Sb)=((S0⋅b)+S0)')
d.step('(S0⋅S0)=((S0⋅0)+S0)')
d.step('∀a:∀b:(a+Sb)=S(a+b)')
d.step('∀b:((S0⋅0)+Sb)=S((S0⋅0)+b)')
d.step('((S0⋅0)+S0)=S((S0⋅0)+0)')
d.step('∀a:(a+0)=a')
d.step('((S0⋅0)+0)=(S0⋅0)')
d.step('∀a:(a⋅0)=0')  # axiom 4
d.step('(S0⋅0)=0')  # specification
d.step('((S0⋅0)+0)=0')  # transitivity
d.step('S((S0⋅0)+0)=S0')  # add S
d.step('((S0⋅0)+S0)=S0')  # transitivity
d.step('(S0⋅S0)=S0')  # transitivity

# Page 220. Illegal Shortcuts.
d = Derivation()
d.step('∀a:(a+0)=a')  # axiom 2
try:
    d.step('∀a:a=(a+0)')  # symmetry (Wrong!)
    assert False
    d.step('∀a:a=a')  # transitivity
except InvalidStep:
    pass

d = Derivation()
with d.fantasy('a=0') as f:
    try:
        f.step('∀a:a=0')  # generalization (Wrong!)
        assert False
    except InvalidStep:
        pass

d = Derivation()
with d.fantasy('∀a:a=a') as f:
    f.step('Sa=Sa')       # specification
    f.step('∃b:b=Sa')     # existence
    f.step('∀a:∃b:b=Sa')  # generalization
    try:
        f.step('∃b:b=Sb')     # specification (Wrong!)
        assert False
    except InvalidStep:
        pass

# Exercise, page 220: Derive "Different numbers have different successors" as a theorem of TNT.
d = Derivation()
with d.fantasy('Sa=Sb') as f:
    f.step('a=b')
d.step('<Sa=Sb⊃a=b>')
d.step('<~a=b⊃~Sa=Sb>')
d.step('∀b:<~a=b⊃~Sa=Sb>')
d.step('∀a:∀b:<~a=b⊃~Sa=Sb>')

# Page 221: Something Is Missing
assert is_well_formed_formula('∀a:(0+a)=a')
assert is_well_formed_formula('~∀a:(0+a)=a')

# Page 224: Induction
d = Derivation()
d.step('∀a:∀b:(a+Sb)=S(a+b)')     # axiom 3
d.step('∀b:(0+Sb)=S(0+b)')        # specification
d.step('(0+Sb)=S(0+b)')           # specification
with d.fantasy('(0+b)=b') as f:
    f.step('S(0+b)=Sb')           # add S
    f.step('(0+Sb)=S(0+b)')       # carry over line 3
    f.step('(0+Sb)=Sb')           # transitivity
d.step('<(0+b)=b⊃(0+Sb)=Sb>')     # fantasy rule
d.step('∀b:<(0+b)=b⊃(0+Sb)=Sb>')  # generalization
d.step('(0+0)=0')                 # specialization of axiom 2
d.step('∀b:(0+b)=b')              # induction
d.step('(0+a)=a')                 # specialization
d.step('∀a:(0+a)=a')              # generalization
