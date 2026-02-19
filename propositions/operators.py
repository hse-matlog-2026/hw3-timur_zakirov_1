# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    if is_variable(formula.root):
        return formula
    if is_constant(formula.root):
        p = Formula('p')
        if formula.root == 'F':
            return Formula('&', p, Formula('~', p))
        return Formula('~', Formula('&', p, Formula('~', p)))
    if is_unary(formula.root):
        return Formula('~', to_not_and_or(formula.first))
    left = to_not_and_or(formula.first)
    right = to_not_and_or(formula.second)
    if formula.root == '&':
        return Formula('&', left, right)
    if formula.root == '|':
        return Formula('|', left, right)
    if formula.root == '->':
        return Formula('|', Formula('~', left), right)
    if formula.root == '+':
        return to_not_and_or(Formula('|', Formula('&', Formula('~', left), right),
                                     Formula('&', left, Formula('~', right))))
    if formula.root == '<->':
        return to_not_and_or(Formula('&', Formula('->', left, right),
                                     Formula('->', right, left)))
    if formula.root == '-&':
        return Formula('~', Formula('&', left, right))
    if formula.root == '-|':
        return Formula('~', Formula('|', left, right))

    raise ValueError()

    # Task 3.5

def to_not_and(formula: Formula) -> Formula:
    f = to_not_and_or(formula)

    def replace_or(f):
        if is_variable(f.root) or is_constant(f.root):
            return f
        if is_unary(f.root):
            return Formula('~', replace_or(f.first))
        if f.root == '&':
            return Formula('&', replace_or(f.first), replace_or(f.second))
        if f.root == '|':
            A = replace_or(f.first)
            B = replace_or(f.second)
            return Formula('~', Formula('&', Formula('~', A), Formula('~', B)))
        raise ValueError()

    return replace_or(f)

    # Task 3.6a

def to_nand(formula: Formula) -> Formula:
    if is_variable(formula.root):
        return formula
    if is_constant(formula.root):
        p = Formula('p')
        t = Formula('-&', p, Formula('-&', p, p))
        if formula.root == 'T':
            return t
        return Formula('-&', t, t)
    if is_unary(formula.root):
        a = to_nand(formula.first)
        return Formula('-&', a, a)
    left = to_nand(formula.first)
    right = to_nand(formula.second)
    if formula.root == '&':
        x = Formula('-&', left, right)
        return Formula('-&', x, x)
    if formula.root == '|':
        nl = Formula('-&', left, left)
        nr = Formula('-&', right, right)
        return Formula('-&', nl, nr)
    if formula.root == '->':
        return to_nand(Formula('|', Formula('~', formula.first), formula.second))
    if formula.root == '+':
        return to_nand(to_not_and_or(formula))
    if formula.root == '<->':
        return to_nand(to_not_and_or(formula))
    if formula.root == '-&':
        return Formula('-&', left, right)
    if formula.root == '-|':
        return to_nand(Formula('~', Formula('|', formula.first, formula.second)))

    raise ValueError()

    # Task 3.6b

def to_implies_not(formula: Formula) -> Formula:
    if is_variable(formula.root):
        return formula
    if is_constant(formula.root):
        p = Formula('p')
        if formula.root == 'T':
            return Formula('->', p, p)
        return Formula('~', Formula('->', p, p))
    if is_unary(formula.root):
        return Formula('~', to_implies_not(formula.first))
    left = to_implies_not(formula.first)
    right = to_implies_not(formula.second)
    if formula.root == '->':
        return Formula('->', left, right)
    if formula.root == '&':
        return Formula('~', Formula('->', left, Formula('~', right)))
    if formula.root == '|':
        return Formula('->', Formula('~', left), right)
    if formula.root in {'+', '<->', '-&', '-|'}:
        return to_implies_not(to_not_and_or(formula))

    raise ValueError()

    # Task 3.6c

def to_implies_false(formula: Formula) -> Formula:
    if is_variable(formula.root):
        return formula
    if is_constant(formula.root):
        if formula.root == 'T':
            return Formula('->', Formula('F'), Formula('F'))
        return Formula('F')
    if is_unary(formula.root):
        a = to_implies_false(formula.first)
        return Formula('->', a, Formula('F'))
    if formula.root not in {'&', '|', '->'}:
        return to_implies_false(to_not_and_or(formula))
    left = to_implies_false(formula.first)
    right = to_implies_false(formula.second)
    if formula.root == '->':
        return Formula('->', left, right)
    if formula.root == '&':
        inner = Formula('->', left, Formula('->', right, Formula('F')))
        return Formula('->', inner, Formula('F'))
    if formula.root == '|':
        a = to_implies_false(Formula('&',
                                     Formula('->', left, Formula('F')),
                                     Formula('->', right, Formula('F'))))
        return Formula('->', a, Formula('F'))

    raise ValueError()

    # Task 3.6d
