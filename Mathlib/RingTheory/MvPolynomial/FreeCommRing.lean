/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.RingTheory.FreeCommRing

/-!

# Constructing Ring terms from MvPolynomial

This file provides tools for constructing ring terms that can be evaluated to particular
`MvPolynomial`s. The main motivation is in model theory. It can be used to construct first order
formulas whose realization is a property of an `MvPolynomial`

## Main definitions

* `FirstOrder.Ring.genericPolyMap` is a function that given a finite set of monomials
  `monoms : ι → Finset (κ →₀ ℕ)` returns a function `ι → FreeCommRing ((Σ i : ι, monoms i) ⊕ κ)`
  such that `genericPolyMap monoms i` is a ring term that can be evaluated to a polynomial
  `p : MvPolynomial κ R` such that `p.support ⊆ monoms i`.

-/

assert_not_exists Cardinal

variable {ι κ R : Type*}

namespace FirstOrder

namespace Ring

open MvPolynomial FreeCommRing

/-- Given a finite set of monomials `monoms : ι → Finset (κ →₀ ℕ)`, the
`genericPolyMap monoms` is an indexed collection of elements of the `FreeCommRing`,
that can be evaluated to any collection `p : ι → MvPolynomial κ R` of
polynomials such that `∀ i, (p i).support ⊆ monoms i`. -/
def genericPolyMap (monoms : ι → Finset (κ →₀ ℕ)) :
    ι → FreeCommRing ((Σ i : ι, monoms i) ⊕ κ) :=
  fun i => (monoms i).attach.sum
    (fun m => FreeCommRing.of (Sum.inl ⟨i, m⟩) *
      Finsupp.prod m.1 (fun j n => FreeCommRing.of (Sum.inr j)^ n))

/-- Collections of `MvPolynomial`s, `p : ι → MvPolynomial κ R` such
that `∀ i, (p i).support ⊆ monoms i` can be identified with functions
`(Σ i, monoms i) → R` by using the coefficient function -/
noncomputable def mvPolynomialSupportLEEquiv
    [DecidableEq κ] [CommRing R] [DecidableEq R]
    (monoms : ι → Finset (κ →₀ ℕ)) :
    { p : ι → MvPolynomial κ R // ∀ i, (p i).support ⊆ monoms i } ≃
      ((Σ i, monoms i) → R) :=
  { toFun := fun p i => (p.1 i.1).coeff i.2,
    invFun := fun p => ⟨fun i =>
      { toFun := fun m => if hm : m ∈ monoms i then p ⟨i, ⟨m, hm⟩⟩ else 0
        support := {m ∈ monoms i | ∃ hm : m ∈ monoms i, p ⟨i, ⟨m, hm⟩⟩ ≠ 0},
        mem_support_toFun := by simp },
      fun i => Finset.filter_subset _ _⟩,
    left_inv := fun p => by
      ext i m
      simp only [coeff, ne_eq, exists_prop, dite_eq_ite, Finsupp.coe_mk, ite_eq_left_iff]
      intro hm
      have : m ∉ (p.1 i).support := fun h => hm (p.2 i h)
      simpa [coeff, eq_comm, MvPolynomial.mem_support_iff] using this
    right_inv := fun p => by simp [coeff] }

@[simp]
theorem MvPolynomialSupportLEEquiv_symm_apply_coeff [DecidableEq κ] [CommRing R] [DecidableEq R]
    (p : ι → MvPolynomial κ R) : (mvPolynomialSupportLEEquiv (fun i => (p i).support)).symm
      (fun i => (p i.1).coeff i.2.1) = ⟨p, fun _ => Finset.Subset.refl _⟩ :=
  (mvPolynomialSupportLEEquiv (R := R) (fun i : ι => (p i).support)).symm_apply_apply
    ⟨p, fun _ => Finset.Subset.refl _⟩

@[simp]
theorem lift_genericPolyMap [DecidableEq κ] [CommRing R]
    [DecidableEq R] (monoms : ι → Finset (κ →₀ ℕ))
    (f : (i : ι) × { x // x ∈ monoms i } ⊕ κ → R) (i : ι) :
    FreeCommRing.lift f (genericPolyMap monoms i) =
      MvPolynomial.eval (f ∘ Sum.inr)
        (((mvPolynomialSupportLEEquiv monoms).symm
          (f ∘ Sum.inl)).1 i) := by
  simp only [genericPolyMap, map_sum, map_mul, lift_of, support,
    mvPolynomialSupportLEEquiv, coeff, Finset.sum_filter, MvPolynomial.eval_eq,
    ne_eq, Function.comp, Equiv.coe_fn_symm_mk, Finsupp.coe_mk]
  conv_rhs => rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl ?_
  intro m _
  simp only [Finsupp.prod, map_prod, map_pow, lift_of, Subtype.coe_eta, Finset.coe_mem,
    exists_prop, true_and, dite_eq_ite, ite_true, ite_not]
  split_ifs with h0 <;> simp_all

end Ring

end FirstOrder
