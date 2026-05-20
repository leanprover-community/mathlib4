/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Generating functions of combinatorial classes

A *combinatorial class* is, informally, a type with a weight function whose fibres (the
objects of each given weight) are finite. Its *generating function* encodes those fibre
cardinalities as a formal power series. It works with *monomial-valued weights*
`weight : α → (σ →₀ ℕ)`, so the generating function lives in `MvPowerSeries σ ℕ`
(the coefficient of `X^d` counts the objects of weight `d`).

This file introduces the unbundled core: the `Prop`-valued typeclass `FiniteFibers` (a
sibling of `Finite`) and the weighted generating function `genFun : MvPowerSeries σ ℕ`
together with its weight-preserving-isomorphism invariance and the ℕ-valued total degree
`deg` driving finiteness arguments in the later files.

The companion files prove the basic *admissible constructions* of the symbolic method
(see [flajolet2009]):

* disjoint union `α ⊕ β` with weight `Sum.elim` has GF `A + B`;
* Cartesian product `α × β` with weight `prodWeight` (additive) has GF `A * B`;
* the neutral class (`PUnit`, weight `0`) has GF `1`;
* the sequence class (`List α`, weight `listWeight`) satisfies `S = 1 + A * S`.

## Main definitions (this file)

* `FiniteFibers`: only finitely many objects of any given weight.
* `genFun`: the weighted GF `∑_d |𝒜_d| X^d` of a weight `α → σ →₀ ℕ`.
* `deg`: the total exponent sum of a weight monomial.

## Main results (this file)

* `instFiniteFibersOfFinite`: a finite carrier has finite fibres.
* `coeff_genFun`: coefficient extraction is by fibre cardinality.
* `genFun_congr`: weight-preserving isomorphic classes have equal GF.
* `deg_eq_zero_iff`: degree-zero objects are exactly the weight-zero objects.

## Companion files (in `Mathlib/Combinatorics/Enumerative/GeneratingFunction/`)

The framework layer (over `MvPowerSeries σ ℕ` with monomial weights):

* `Sum`, `Prod`, `Atom`: basic admissible constructions and their `genFun` identities.
* `Seq`, `SeqEquation`: the sequence construction (`listWeight`) and its functional
  equation.
* `Map`, `MapSeq`: base change to a (semi)ring; closed form `invOfUnit (1 - A) 1`
  (`(1 - A)⁻¹` over a field).
* `Tsum`: the Flajolet–Sedgewick defining form `genFun = ∑' a, X^(wt a)`.
* `Mark`: marking a statistic; grading-aggregation recovery of the unmarked count.

Specialisation layers (sit on top of the framework — pick what your application needs):

* `Ogf`, `OgfCombinators`, `OgfSeq`: the `σ = Unit` / ℕ-size *ordinary* generating
  function `ogf size = ∑ₙ |𝒜ₙ| Xⁿ`, via `PowerSeries ℕ = MvPowerSeries Unit ℕ`.

## TODO

* Labelled classes and exponential generating functions (EGF: an `Egf*` specialisation
  layer with coefficients `Nat.card / n!`, sibling to the `Ogf*` files).
* General recursive classes via weighted `WType`s: prove the polynomial-functor
  fixed-point equation `A = ∑ₐ X^{w a} · A^|β a|` (under a contracting condition
  on weights). `genFun_listWeight` / `ogf_seq` is the linear special case
  `A = 1 + W·A`; the branching case is needed for binary trees (`T = 1 + X·T²`),
  Motzkin paths, ternary trees, etc.
* Refactor `PowerSeries.catalanSeries`, `PowerSeries.largeSchroderSeries`,
  `Nat.Partition.genFun` onto this framework.

## References

* [M. Bona, *Handbook of Enumerative Combinatorics*][Bona2015]
* [P. Flajolet and R. Sedgewick, *Analytic Combinatorics*][flajolet2009]
-/

@[expose] public section

universe u v w

namespace Combinatorics

variable {α : Type u} {β : Type v} {σ : Type w}

/-! ## Finite fibres -/

/-- The objects of each fixed weight form a finite type. -/
class FiniteFibers (wt : α → σ →₀ ℕ) : Prop where
  finite_fiber (d : σ →₀ ℕ) : Finite {a // wt a = d}

attribute [instance] FiniteFibers.finite_fiber

/-- A class with a finite carrier has finite fibres (every fibre is a subtype of the
carrier). -/
instance instFiniteFibersOfFinite [Finite α] (wt : α → σ →₀ ℕ) : FiniteFibers wt :=
  ⟨fun _ => inferInstance⟩

/-! ## The weighted generating function -/

/-- The weighted generating function `A(X) = ∑_{a} X^(wt a)`. -/
noncomputable def genFun (wt : α → σ →₀ ℕ) : MvPowerSeries σ ℕ :=
  fun d => Nat.card {a // wt a = d}

@[simp]
theorem coeff_genFun (wt : α → σ →₀ ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (genFun wt) = Nat.card {a // wt a = d} :=
  MvPowerSeries.coeff_apply (genFun wt) d

/-- The weighted GF is an invariant of weight-preserving isomorphism. -/
theorem genFun_congr {wα : α → σ →₀ ℕ} {wβ : β → σ →₀ ℕ} (e : α ≃ β)
    (he : ∀ a, wβ (e a) = wα a) : genFun wα = genFun wβ := by
  ext d
  rw [coeff_genFun, coeff_genFun]
  exact Nat.card_congr (Equiv.subtypeEquiv e fun a => by rw [he a])

/-- The total degree of an object: the sum of the exponents of its weight monomial. -/
def deg (wt : α → σ →₀ ℕ) (a : α) : ℕ := (wt a).sum fun _ n => n

theorem deg_eq_zero_iff (wt : α → σ →₀ ℕ) (a : α) : deg wt a = 0 ↔ wt a = 0 := by
  rw [deg, Finsupp.sum, Finset.sum_eq_zero_iff, Finsupp.ext_iff]
  simp [Finsupp.mem_support_iff]

end Combinatorics
