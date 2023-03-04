/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker

! This file was ported from Lean 3 source module data.polynomial.monomial
! leanprover-community/mathlib commit 220f71ba506c8958c9b41bd82226b3d06b0991e8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.Basic

/-!
# Univariate monomials

Preparatory lemmas for degree_basic.
-/


noncomputable section

namespace Polynomial

open Polynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem monomial_one_eq_iff [Nontrivial R] {i j : ℕ} :
    (monomial i 1 : R[X]) = monomial j 1 ↔ i = j :=
  by
  simp_rw [← of_finsupp_single]
  exact add_monoid_algebra.of_injective.eq_iff
#align polynomial.monomial_one_eq_iff Polynomial.monomial_one_eq_iff

instance [Nontrivial R] : Infinite R[X] :=
  Infinite.of_injective (fun i => monomial i 1) fun m n h => by simpa [monomial_one_eq_iff] using h

theorem card_support_le_one_iff_monomial {f : R[X]} :
    Finset.card f.support ≤ 1 ↔ ∃ n a, f = monomial n a :=
  by
  constructor
  · intro H
    rw [Finset.card_le_one_iff_subset_singleton] at H
    rcases H with ⟨n, hn⟩
    refine' ⟨n, f.coeff n, _⟩
    ext i
    by_cases hi : i = n
    · simp [hi, coeff_monomial]
    · have : f.coeff i = 0 := by
        rw [← not_mem_support_iff]
        exact fun hi' => hi (Finset.mem_singleton.1 (hn hi'))
      simp [this, Ne.symm hi, coeff_monomial]
  · rintro ⟨n, a, rfl⟩
    rw [← Finset.card_singleton n]
    apply Finset.card_le_of_subset
    exact support_monomial' _ _
#align polynomial.card_support_le_one_iff_monomial Polynomial.card_support_le_one_iff_monomial

theorem ringHom_ext {S} [Semiring S] {f g : R[X] →+* S} (h₁ : ∀ a, f (c a) = g (c a))
    (h₂ : f x = g x) : f = g :=
  by
  set f' := f.comp (to_finsupp_iso R).symm.toRingHom with hf'
  set g' := g.comp (to_finsupp_iso R).symm.toRingHom with hg'
  have A : f' = g' := by
    ext
    · simp [h₁, RingEquiv.toRingHom_eq_coe]
    · simpa [RingEquiv.toRingHom_eq_coe] using h₂
  have B : f = f'.comp (to_finsupp_iso R) :=
    by
    rw [hf', RingHom.comp_assoc]
    ext x
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_apply_apply, Function.comp_apply,
      RingHom.coe_comp, RingEquiv.coe_toRingHom]
  have C : g = g'.comp (to_finsupp_iso R) :=
    by
    rw [hg', RingHom.comp_assoc]
    ext x
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_apply_apply, Function.comp_apply,
      RingHom.coe_comp, RingEquiv.coe_toRingHom]
  rw [B, C, A]
#align polynomial.ring_hom_ext Polynomial.ringHom_ext

@[ext]
theorem ringHom_ext' {S} [Semiring S] {f g : R[X] →+* S} (h₁ : f.comp c = g.comp c)
    (h₂ : f x = g x) : f = g :=
  ringHom_ext (RingHom.congr_fun h₁) h₂
#align polynomial.ring_hom_ext' Polynomial.ringHom_ext'

end Polynomial

