/-
Copyright (c) 2026 metakunt All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: metakunt
-/
module


public import Mathlib.Algebra.CharP.Quotient
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot.Basic
public import Mathlib.RingTheory.Artinian.Instances
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Instances related to `AdjoinRoot`
-/

public section

namespace AdjoinRoot.Polynomial

open _root_.Polynomial

variable {r p : ℕ} {R : Type*} [CommRing R] [CharP R p]

set_option backward.isDefEq.respectTransparency false in
theorem IsReduced.X_pow_sub_one (hcprm : p.Coprime r) [IsArtinianRing R] [IsReduced R] :
    IsReduced (AdjoinRoot ((X : R[X]) ^ r - 1)) := by
  simp only [AdjoinRoot, ← Ideal.isRadical_iff_quotient_reduced,
    (Ideal.isRadical_iff_pow_one_lt 2 (by grind))]
  intro s hs
  rw [Ideal.mem_span_singleton] at *
  refine (Squarefree.dvd_pow_iff_dvd ?_ (by lia)).mp hs
  apply Separable.squarefree
  rw [← C_1, show 1 = ((1 : Rˣ) : R) by rfl]
  apply separable_X_pow_sub_C_unit 1
  convert ((ZMod.isUnit_iff_coprime _ _).mpr hcprm.symm).map (ZMod.castHom (Nat.dvd_refl p) R)
  simp

theorem CharP.X_pow_sub_one (hcprm : p.Coprime r) [Nontrivial R] :
    CharP (AdjoinRoot ((X : R[X]) ^ r - 1)) p  := by
  have hr : r ≠ 0 := by grind [Nat.coprime_zero_right, CharP.char_ne_one R p]
  apply CharP.quotient'
  intro z hz
  by_contra!
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hz
  by_cases hc : y = 0
  · grind
  · have : (z : R[X]).natDegree = 0 := by simp
    have : r ≤ (z : R[X]).natDegree := by
      rw [← hy, natDegree_mul']
      · suffices ((X : R[X]) ^ r - 1).natDegree = r by lia
        exact natDegree_X_pow_sub_C
      suffices ((X : R[X]) ^ r - 1).leadingCoeff = 1 by grind [leadingCoeff_eq_zero, mul_one]
      exact leadingCoeff_X_pow_sub_one (by lia)
    grind

end AdjoinRoot.Polynomial
