/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Basic lemmas about the general linear group $GL(n, R)$

This file lists various basic lemmas about the general linear group $GL(n, R)$. For the definitions,
see `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`.
-/

@[expose] public section

namespace Matrix

section Examples

/-- The matrix $[a, -b; b, a]$ (inspired by multiplication by a complex number); it is an element of
$GL_2(R)$ if `a ^ 2 + b ^ 2` is nonzero. -/
@[simps! -fullyApplied val]
def planeConformalMatrix {R} [Field R] (a b : R) (hab : a ^ 2 + b ^ 2 ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) R :=
  GeneralLinearGroup.mkOfDetNeZero !![a, -b; b, a] (by simpa [det_fin_two, sq] using hab)

/- TODO: Add Iwasawa matrices `n_x=!![1,x; 0,1]`, `a_t=!![exp(t/2),0;0,exp(-t/2)]` and
  `k_θ=!![cos θ, sin θ; -sin θ, cos θ]`
-/
end Examples

namespace GeneralLinearGroup

section Center

variable {R n : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The center of `GL n R` consists of scalar matrices. -/
lemma mem_center_iff_val_mem_range_scalar {g : GL n R} :
    g ∈ Subgroup.center (GL n R) ↔ g.val ∈ Set.range (Matrix.scalar n) := by
  constructor
  · intro hg
    refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun t ↦ ?_
    simpa [Units.ext_iff] using! Subgroup.mem_center_iff.mp hg (.mk _ _ t.mul_inv t.inv_mul)
  · refine fun ⟨a, ha⟩ ↦ Subgroup.mem_center_iff.mpr fun h ↦ ?_
    simp [-scalar_apply, Units.ext_iff, ← ha, Matrix.scalar_comm a (Commute.all _)]

@[deprecated (since := "2026-02-08")]
alias mem_center_iff_val_eq_scalar := mem_center_iff_val_mem_range_scalar

/-- The center of `GL n R` is the image of `Rˣ`. -/
lemma center_eq_range_scalar :
    Subgroup.center (GL n R) = (scalar n).range := by
  ext g
  constructor
  · -- previous lemma shows the underlying matrix is scalar, but now need to show
    -- the scalar is a unit; so we apply argument both to `g` and `g⁻¹`
    intro hg
    cases isEmpty_or_nonempty n with
    | inl hn => simp [nontriviality]
    | inr hn =>
      obtain ⟨a, ha⟩ := mem_center_iff_val_mem_range_scalar.mp hg
      obtain ⟨b, hb⟩ := mem_center_iff_val_mem_range_scalar.mp (Subgroup.inv_mem _ hg)
      have hab : a * b = 1 := by
        simpa [-mul_inv_cancel, ← ha, ← hb, ← diagonal_one, Units.ext_iff] using mul_inv_cancel g
      refine ⟨⟨a, b, hab, mul_comm a b ▸ hab⟩, ?_⟩
      simp [Units.ext_iff, ← ha]
  · rintro ⟨a, rfl⟩
    exact mem_center_iff_val_mem_range_scalar.mpr ⟨a, rfl⟩

@[deprecated (since := "2026-02-08")]
alias center_eq_range_units := center_eq_range_scalar

end Center

end GeneralLinearGroup

lemma SpecialLinearGroup.toGL_mem_center_iff {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (g : SpecialLinearGroup n R) :
    toGL g ∈ Subgroup.center (GL n R) ↔ g ∈ Subgroup.center (SpecialLinearGroup n R) := by
  if hn : IsEmpty n then simp [Subgroup.center_eq_top] else
  replace hn : Nonempty n := by simpa using hn
  obtain ⟨i⟩ := hn
  simp only [GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range,
    mem_center_iff, scalar_apply]
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨r, by simpa [Units.ext_iff] using congr(GeneralLinearGroup.det $hr),
    by simpa [Units.ext_iff] using hr⟩, fun ⟨r, hr1, hr⟩ ↦ ⟨⟨r, g⁻¹.1 i i, ?_, ?_⟩,
      by simp [Units.ext_iff, hr]⟩⟩
  · simpa [-mul_inv_cancel, ← hr, ← pow_succ',
      Nat.sub_one_add_one Fintype.card_pos.ne.symm] using
        Matrix.ext_iff.2 (Subtype.ext_iff.1 (mul_inv_cancel g)) i i
  · simpa [-inv_mul_cancel, ← hr] using Matrix.ext_iff.2 (Subtype.ext_iff.1 (inv_mul_cancel g)) i i

end Matrix
