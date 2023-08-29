/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.Data.Polynomial.Basic

#align_import data.polynomial.monomial from "leanprover-community/mathlib"@"220f71ba506c8958c9b41bd82226b3d06b0991e8"

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
    (monomial i 1 : R[X]) = monomial j 1 ↔ i = j := by
  -- Porting note: `ofFinsupp.injEq` is required.
  simp_rw [← ofFinsupp_single, ofFinsupp.injEq]
  -- ⊢ Finsupp.single i 1 = Finsupp.single j 1 ↔ i = j
  exact AddMonoidAlgebra.of_injective.eq_iff
  -- 🎉 no goals
#align polynomial.monomial_one_eq_iff Polynomial.monomial_one_eq_iff

instance infinite [Nontrivial R] : Infinite R[X] :=
  Infinite.of_injective (fun i => monomial i 1) fun m n h => by simpa [monomial_one_eq_iff] using h
                                                                -- 🎉 no goals
#align polynomial.infinite Polynomial.infinite

theorem card_support_le_one_iff_monomial {f : R[X]} :
    Finset.card f.support ≤ 1 ↔ ∃ n a, f = monomial n a := by
  constructor
  -- ⊢ Finset.card (support f) ≤ 1 → ∃ n a, f = ↑(monomial n) a
  · intro H
    -- ⊢ ∃ n a, f = ↑(monomial n) a
    rw [Finset.card_le_one_iff_subset_singleton] at H
    -- ⊢ ∃ n a, f = ↑(monomial n) a
    rcases H with ⟨n, hn⟩
    -- ⊢ ∃ n a, f = ↑(monomial n) a
    refine' ⟨n, f.coeff n, _⟩
    -- ⊢ f = ↑(monomial n) (coeff f n)
    ext i
    -- ⊢ coeff f i = coeff (↑(monomial n) (coeff f n)) i
    by_cases hi : i = n
    -- ⊢ coeff f i = coeff (↑(monomial n) (coeff f n)) i
    · simp [hi, coeff_monomial]
      -- 🎉 no goals
    · have : f.coeff i = 0 := by
        rw [← not_mem_support_iff]
        exact fun hi' => hi (Finset.mem_singleton.1 (hn hi'))
      simp [this, Ne.symm hi, coeff_monomial]
      -- 🎉 no goals
  · rintro ⟨n, a, rfl⟩
    -- ⊢ Finset.card (support (↑(monomial n) a)) ≤ 1
    rw [← Finset.card_singleton n]
    -- ⊢ Finset.card (support (↑(monomial n) a)) ≤ Finset.card {n}
    apply Finset.card_le_of_subset
    -- ⊢ support (↑(monomial n) a) ⊆ {n}
    exact support_monomial' _ _
    -- 🎉 no goals
#align polynomial.card_support_le_one_iff_monomial Polynomial.card_support_le_one_iff_monomial

theorem ringHom_ext {S} [Semiring S] {f g : R[X] →+* S} (h₁ : ∀ a, f (C a) = g (C a))
    (h₂ : f X = g X) : f = g := by
  set f' := f.comp (toFinsuppIso R).symm.toRingHom with hf'
  -- ⊢ f = g
  set g' := g.comp (toFinsuppIso R).symm.toRingHom with hg'
  -- ⊢ f = g
  have A : f' = g' := by
    -- Porting note: Was `ext; simp [..]; simpa [..] using h₂`.
    ext : 1
    · ext
      simp [h₁, RingEquiv.toRingHom_eq_coe]
    · refine MonoidHom.ext_mnat ?_
      simpa [RingEquiv.toRingHom_eq_coe] using h₂
  have B : f = f'.comp (toFinsuppIso R) := by
    rw [hf', RingHom.comp_assoc]
    ext x
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_apply_apply, Function.comp_apply,
      RingHom.coe_comp, RingEquiv.coe_toRingHom]
  have C' : g = g'.comp (toFinsuppIso R) := by
    rw [hg', RingHom.comp_assoc]
    ext x
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_apply_apply, Function.comp_apply,
      RingHom.coe_comp, RingEquiv.coe_toRingHom]
  rw [B, C', A]
  -- 🎉 no goals
#align polynomial.ring_hom_ext Polynomial.ringHom_ext

@[ext high]
theorem ringHom_ext' {S} [Semiring S] {f g : R[X] →+* S} (h₁ : f.comp C = g.comp C)
    (h₂ : f X = g X) : f = g :=
  ringHom_ext (RingHom.congr_fun h₁) h₂
#align polynomial.ring_hom_ext' Polynomial.ringHom_ext'

end Polynomial
