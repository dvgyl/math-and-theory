"""Small sparse polynomial arithmetic over Fraction; no third-party dependencies.

This is an arithmetic checker, not a proof-assistant kernel. Variable names are
positional; all equalities are exact coefficient equalities, never sampling.
"""
from __future__ import annotations
from fractions import Fraction
from typing import Iterable, Mapping

class Poly:
    def __init__(self, arity: int, terms: Mapping[tuple[int, ...], int | Fraction] | None = None):
        if arity < 1:
            raise ValueError('A polynomial needs at least one variable')
        self.arity = arity
        self.terms: dict[tuple[int, ...], Fraction] = {}
        for exp, coefficient in (terms or {}).items():
            if len(exp) != arity or any(not isinstance(e, int) or e < 0 for e in exp):
                raise ValueError('Invalid exponent vector')
            c = Fraction(coefficient)
            if c:
                self.terms[tuple(exp)] = c

    @classmethod
    def constant(cls, arity: int, coefficient: int | Fraction) -> 'Poly':
        return cls(arity, {(0,) * arity: coefficient})

    @classmethod
    def variable(cls, arity: int, index: int) -> 'Poly':
        if not 0 <= index < arity:
            raise ValueError('Variable index out of range')
        exponent = [0] * arity
        exponent[index] = 1
        return cls(arity, {tuple(exponent): 1})

    def coerce(self, other: int | Fraction | 'Poly') -> 'Poly':
        if isinstance(other, Poly):
            if other.arity != self.arity:
                raise ValueError('Incompatible arities')
            return other
        return Poly.constant(self.arity, other)

    def __add__(self, other: int | Fraction | 'Poly') -> 'Poly':
        other = self.coerce(other)
        out = dict(self.terms)
        for exp, c in other.terms.items():
            out[exp] = out.get(exp, Fraction(0)) + c
        return Poly(self.arity, out)

    __radd__ = __add__

    def __neg__(self) -> 'Poly':
        return Poly(self.arity, {e: -c for e, c in self.terms.items()})

    def __sub__(self, other: int | Fraction | 'Poly') -> 'Poly':
        return self + -self.coerce(other)

    def __rsub__(self, other: int | Fraction | 'Poly') -> 'Poly':
        return self.coerce(other) + -self

    def __mul__(self, other: int | Fraction | 'Poly') -> 'Poly':
        other = self.coerce(other)
        out: dict[tuple[int, ...], Fraction] = {}
        for e, c in self.terms.items():
            for f, d in other.terms.items():
                g = tuple(a + b for a, b in zip(e, f))
                out[g] = out.get(g, Fraction(0)) + c * d
        return Poly(self.arity, out)

    __rmul__ = __mul__

    def __pow__(self, exponent: int) -> 'Poly':
        if not isinstance(exponent, int) or exponent < 0:
            raise ValueError('Polynomial exponent must be a nonnegative integer')
        out = Poly.constant(self.arity, 1)
        base = self
        while exponent:
            if exponent & 1:
                out = out * base
            base = base * base
            exponent //= 2
        return out

    def __eq__(self, other: object) -> bool:
        if isinstance(other, (int, Fraction)):
            other = self.coerce(other)
        return isinstance(other, Poly) and self.arity == other.arity and self.terms == other.terms

    def evaluate(self, values: Iterable[int | Fraction | 'Poly']) -> int | Fraction | 'Poly':
        values = tuple(values)
        if len(values) != self.arity:
            raise ValueError('Wrong number of substitution values')
        out: int | Fraction | Poly = Fraction(0)
        for e, c in self.terms.items():
            term: int | Fraction | Poly = c
            for x, k in zip(values, e):
                term = term * x ** k
            out = out + term
        return out

    def coefficients(self) -> list[int]:
        if self.arity != 1:
            raise ValueError('Only univariate polynomials have this serialization')
        degree = max((e[0] for e in self.terms), default=0)
        out = []
        for i in range(degree + 1):
            c = self.terms.get((i,), Fraction(0))
            if c.denominator != 1:
                raise ValueError('Expected integer coefficients')
            out.append(c.numerator)
        return out

    @classmethod
    def from_coefficients(cls, coefficients: Iterable[int]) -> 'Poly':
        return cls(1, {(i,): c for i, c in enumerate(coefficients)})
