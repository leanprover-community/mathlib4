/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.List.TFAE

/-! # Monomial orders

## Monomial orders

A *monomial order* is well ordering relation on a type of the form `σ →₀ ℕ` which
is compatible with addition and for which `0` is the smallest element.
Since several monomial orders may have to be used simultaneously, one cannot
get them as instances.

In this formalization, they are presented as a structure `MonomialOrder` which encapsulates
`MonomialOrder.toSyn`, an additive and monotone isomorphism to a linearly ordered cancellative
additive commutative monoid.
The entry `MonomialOrder.wf` asserts that `MonomialOrder.syn` is well founded.

The terminology comes from commutative algebra and algebraic geometry, especially Gröbner bases,
where `c : σ →₀ ℕ` are exponents of monomials.

Given a monomial order `m : MonomialOrder σ`, we provide the notation
`c ≼[m] d` and `c ≺[m] d` to compare `c d : σ →₀ ℕ` with respect to `m`.
It is activated using `open scoped MonomialOrder`.

## Examples

Commutative algebra defines many monomial orders, with different usefulness ranges.
In this file, we provide the basic example of lexicographic ordering.
For the graded lexicographic ordering, see `Mathlib/Data/Finsupp/DegLex.lean`

* `MonomialOrder.lex` : the lexicographic ordering on `σ →₀ ℕ`.
For this, `σ` needs to be embedded with an ordering relation which satisfies `WellFoundedGT σ`.
(This last property is automatic when `σ` is finite).

The type synonym is `Lex (σ →₀ ℕ)` and the two lemmas `MonomialOrder.lex_le_iff`
and `MonomialOrder.lex_lt_iff` rewrite the ordering as comparisons in the type `Lex (σ →₀ ℕ)`.

## References

* [Cox, Little and O'Shea, *Ideals, varieties, and algorithms*][coxlittleoshea1997]
* [Becker and Weispfenning, *Gröbner bases*][Becker-Weispfenning1993]

## Note

In algebraic geometry, when the finitely many variables are indexed by integers,
it is customary to order them using the opposite order : `MvPolynomial.X 0 > MvPolynomial.X 1 > … `

-/

/-- Monomial orders : equivalence of `σ →₀ ℕ` with a well ordered type -/
structure MonomialOrder (σ : Type*) where
  /-- The synonym type -/
  syn : Type*
  /-- `syn` is a additive commutative monoid -/
  acm : AddCommMonoid syn := by infer_instance
  /-- `syn` is linearly ordered -/
  lo : LinearOrder syn := by infer_instance
  /-- `syn` is a linearly ordered cancellative additive commutative monoid -/
  iocam : IsOrderedCancelAddMonoid syn := by infer_instance
  /-- the additive equivalence from `σ →₀ ℕ` to `syn` -/
  toSyn : (σ →₀ ℕ) ≃+ syn
  /-- `toSyn` is monotone -/
  toSyn_monotone : Monotone toSyn
  /-- `syn` is a well ordering -/
  wf : WellFoundedLT syn := by infer_instance

attribute [instance] MonomialOrder.acm MonomialOrder.lo MonomialOrder.iocam MonomialOrder.wf

namespace MonomialOrder

variable {σ : Type*} (m : MonomialOrder σ)

lemma le_add_right (a b : σ →₀ ℕ) :
    m.toSyn a ≤ m.toSyn a + m.toSyn b := by
  rw [← map_add]
  exact m.toSyn_monotone le_self_add

instance orderBot : OrderBot (m.syn) where
  bot := 0
  bot_le a := by
    have := m.le_add_right 0 (m.toSyn.symm a)
    simpa [map_add, zero_add]

@[simp]
theorem bot_eq_zero : (⊥ : m.syn) = 0 := rfl

theorem eq_zero_iff {a : m.syn} : a = 0 ↔ a ≤ 0 := eq_bot_iff

lemma toSyn_strictMono : StrictMono (m.toSyn) := by
  apply m.toSyn_monotone.strictMono_of_injective m.toSyn.injective

/-- Given a monomial order, notation for the corresponding strict order relation on `σ →₀ ℕ` -/
scoped
notation:50 c " ≺[" m:25 "] " d:50 => (MonomialOrder.toSyn m c < MonomialOrder.toSyn m d)

/-- Given a monomial order, notation for the corresponding order relation on `σ →₀ ℕ` -/
scoped
notation:50 c " ≼[" m:25 "] " d:50 => (MonomialOrder.toSyn m c ≤ MonomialOrder.toSyn m d)

end MonomialOrder

section Lex

open Finsupp

open scoped MonomialOrder

-- The linear order on `Finsupp`s obtained by the lexicographic ordering. -/
noncomputable instance {α N : Type*} [LinearOrder α]
    [AddCommMonoid N] [PartialOrder N] [IsOrderedCancelAddMonoid N] :
    IsOrderedCancelAddMonoid (Lex (α →₀ N)) where
  le_of_add_le_add_left a b c h := by simpa only [add_le_add_iff_left] using h
  add_le_add_left a b h c := by simpa only [add_le_add_iff_left] using h

/-- for the lexicographic ordering, X 0 * X 1 < X 0 ^ 2 -/
example : toLex (Finsupp.single 0 2) > toLex (Finsupp.single 0 1 + Finsupp.single 1 1) := by
  use 0; simp

/-- for the lexicographic ordering, X 1 < X 0 -/
example : toLex (Finsupp.single 1 1) < toLex (Finsupp.single 0 1) := by
  use 0; simp

/-- for the lexicographic ordering, X 1 < X 0 ^ 2 -/
example : toLex (Finsupp.single 1 1) < toLex (Finsupp.single 0 2) := by
  use 0; simp

variable {σ : Type*} [LinearOrder σ]

/-- The lexicographic order on `σ →₀ ℕ`, as a `MonomialOrder` -/
noncomputable def MonomialOrder.lex [WellFoundedGT σ] :
    MonomialOrder σ where
  syn := Lex (σ →₀ ℕ)
  toSyn :=
  { toEquiv := toLex
    map_add' := toLex_add }
  toSyn_monotone := Finsupp.toLex_monotone

theorem MonomialOrder.lex_le_iff [WellFoundedGT σ] {c d : σ →₀ ℕ} :
    c ≼[lex] d ↔ toLex c ≤ toLex d := Iff.rfl

theorem MonomialOrder.lex_lt_iff [WellFoundedGT σ] {c d : σ →₀ ℕ} :
    c ≺[lex] d ↔ toLex c < toLex d := Iff.rfl

theorem MonomialOrder.lex_lt_iff_of_unique [Unique σ] {c d : σ →₀ ℕ} :
    c ≺[lex] d ↔ c default < d default := by
  simp only [MonomialOrder.lex_lt_iff, Finsupp.lex_lt_iff_of_unique, ofLex_toLex]

theorem MonomialOrder.lex_le_iff_of_unique [Unique σ] {c d : σ →₀ ℕ} :
    c ≼[lex] d ↔ c default ≤ d default := by
  simp only [MonomialOrder.lex_le_iff, Finsupp.lex_le_iff_of_unique, ofLex_toLex]

end Lex
