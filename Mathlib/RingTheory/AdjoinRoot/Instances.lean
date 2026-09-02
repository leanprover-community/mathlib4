/-
Copyright (c) 2026 metakunt. All rights reserved.
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
public import Mathlib.Algebra.CharP.Algebra

/-!
# Instances related to `AdjoinRoot`
-/

public section

namespace AdjoinRoot

open _root_.Polynomial Ideal

variable {r p : ℕ} {R : Type*} [CommRing R] {f : R[X]}

theorem spanRadical_iff_isReduced : (span {f}).IsRadical ↔ IsReduced (AdjoinRoot f) :=
  isRadical_iff_quotient_reduced (Ideal.span {f})

variable [CharP R p]

set_option backward.isDefEq.respectTransparency false in
theorem IsReduced.X_pow_sub_one (hcprm : p.Coprime r) [IsArtinianRing R] [IsReduced R] :
    IsReduced (AdjoinRoot ((X : R[X]) ^ r - 1)) := by
  simp only [← spanRadical_iff_isReduced, (Ideal.isRadical_iff_pow_one_lt 2 (by grind))]
  intro s hs
  rw [Ideal.mem_span_singleton] at *
  refine (Squarefree.dvd_pow_iff_dvd ?_ (by lia)).mp hs
  apply Separable.squarefree
  rw [← C_1, show 1 = ((1 : Rˣ) : R) by rfl]
  apply separable_X_pow_sub_C_unit 1
  convert ((ZMod.isUnit_iff_coprime _ _).mpr hcprm.symm).map (ZMod.castHom (Nat.dvd_refl p) R)
  simp

theorem charP_of_monic_of_degree_pos (monic : f.Monic) (deg : 0 < f.degree) :
    CharP (AdjoinRoot f) p  := by
  refine _root_.charP_of_injective_algebraMap (R := R) ?_ _
  apply (faithfulSMul_iff_algebraMap_injective R _).mp
  exact (faithfulSMul_of_monic_of_degree_pos monic deg)

theorem charP_of_X_pow_sub_one (h : 0 < r) [Nontrivial R] :
    CharP (AdjoinRoot ((X : R[X]) ^ r - 1)) p := by
  apply charP_of_monic_of_degree_pos
  · simp [Monic.def, leadingCoeff_X_pow_sub_one h]
  · refine natDegree_pos_iff_degree_pos.mp ?_
    suffices ((X : R[X]) ^ r - 1).natDegree = r by grind
    rw [← C_1, natDegree_X_pow_sub_C]

end AdjoinRoot
