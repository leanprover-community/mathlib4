/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Defs
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Finite.Sigma
public import Mathlib.Data.Finsupp.Interval

/-!
# Generating function of a Cartesian product

`α × β` with weight `prodWeight wα wβ` (the additive monomial product) has GF
`genFun wα * genFun wβ`: at weight `d` it splits over the antidiagonal of `d`.

## Main definitions

* `prodWeight`: pointwise sum of the component weights.

## Main results

* `prodPairEquiv` / `prodFiberEquiv`: the fibre at `d` is a Σ-bundle over the
  antidiagonal of pair-fibres.
* `instFiniteFibersProdWeight`: finiteness propagates by instance resolution.
* `genFun_prod`: the GF of the product is the product of GFs.
-/

@[expose] public section

open Finset

universe u v w

namespace Combinatorics

variable {α : Type u} {β : Type v} {σ : Type w}

/-- The weight of a Cartesian product: the monomial product (exponent sum) of the
component weights. -/
noncomputable def prodWeight (wα : α → σ →₀ ℕ) (wβ : β → σ →₀ ℕ) : α × β → σ →₀ ℕ :=
  fun p => wα p.1 + wβ p.2

/-- The fiber of a product, at a fixed pair of component weights, is the product
of the fibers. -/
def prodPairEquiv (wα : α → σ →₀ ℕ) (wβ : β → σ →₀ ℕ) (c : (σ →₀ ℕ) × (σ →₀ ℕ)) :
    {p : α × β // (wα p.1, wβ p.2) = c} ≃ {a // wα a = c.1} × {b // wβ b = c.2} where
  toFun := fun ⟨⟨a, b⟩, h⟩ => (⟨a, congrArg Prod.fst h⟩, ⟨b, congrArg Prod.snd h⟩)
  invFun := fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ => ⟨(a, b), Prod.ext ha hb⟩
  left_inv := by rintro ⟨⟨a, b⟩, h⟩; rfl
  right_inv := by rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; rfl

instance instFiniteProdPair {wα : α → σ →₀ ℕ} {wβ : β → σ →₀ ℕ}
    [FiniteFibers wα] [FiniteFibers wβ] (c : (σ →₀ ℕ) × (σ →₀ ℕ)) :
    Finite {p : α × β // (wα p.1, wβ p.2) = c} :=
  Finite.of_equiv _ (prodPairEquiv wα wβ c).symm

/-- The fiber of a product splits, over the antidiagonal, into the pair-fibers. -/
noncomputable def prodFiberEquiv [DecidableEq σ] (wα : α → σ →₀ ℕ) (wβ : β → σ →₀ ℕ)
    (d : σ →₀ ℕ) :
    {p : α × β // wα p.1 + wβ p.2 = d} ≃
      Σ y : antidiagonal d,
        {p : α × β // (wα p.1, wβ p.2) = (y : (σ →₀ ℕ) × (σ →₀ ℕ))} :=
  (Equiv.subtypeEquivRight fun _ => by simp [mem_antidiagonal]).trans
    (Equiv.sigmaSubtypeFiberEquivSubtype
      (fun p : α × β => (wα p.1, wβ p.2)) fun _ => Iff.rfl).symm

instance instFiniteFibersProdWeight {wα : α → σ →₀ ℕ} {wβ : β → σ →₀ ℕ}
    [FiniteFibers wα] [FiniteFibers wβ] : FiniteFibers (prodWeight wα wβ) where
  finite_fiber d := by classical exact Finite.of_equiv _ (prodFiberEquiv wα wβ d).symm

private theorem card_prodWeight_fiber [DecidableEq σ] (wα : α → σ →₀ ℕ) (wβ : β → σ →₀ ℕ)
    [FiniteFibers wα] [FiniteFibers wβ] (d : σ →₀ ℕ) :
    Nat.card {p : α × β // prodWeight wα wβ p = d}
      = ∑ p ∈ antidiagonal d, Nat.card {a // wα a = p.1} * Nat.card {b // wβ b = p.2} := by
  have h1 : Nat.card {p : α × β // prodWeight wα wβ p = d}
      = Nat.card (Σ y : antidiagonal d,
          {p : α × β // (wα p.1, wβ p.2) = (y : (σ →₀ ℕ) × (σ →₀ ℕ))}) :=
    Nat.card_congr (prodFiberEquiv wα wβ d)
  rw [h1, Nat.card_sigma,
    ← Finset.sum_coe_sort (antidiagonal d)
      fun p => Nat.card {a // wα a = p.1} * Nat.card {b // wβ b = p.2}]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Nat.card_congr (prodPairEquiv wα wβ _), Nat.card_prod]

/-- The weighted GF of a Cartesian product is the product of the weighted GFs. -/
@[simp]
theorem genFun_prod {wα : α → σ →₀ ℕ} {wβ : β → σ →₀ ℕ}
    [FiniteFibers wα] [FiniteFibers wβ] :
    genFun (prodWeight wα wβ) = genFun wα * genFun wβ := by
  classical
  ext d
  simp [card_prodWeight_fiber, MvPowerSeries.coeff_mul]

end Combinatorics
