/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Basic lemmas about the general linear group $GL(n, R)$

This file lists various basic lemmas about the general linear group $GL(n, R)$. For the definitions,
see `LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`.
-/

namespace Matrix

section Examples

/-- The matrix [a, -b; b, a] (inspired by multiplication by a complex number); it is an element of
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
lemma mem_center_iff_val_eq_scalar {g : GL n R} :
    g ∈ Subgroup.center (GL n R) ↔ g.val ∈ Set.range (scalar _) := by
  rcases isEmpty_or_nonempty n
  · simpa [Subsingleton.elim (Subgroup.center _) ⊤] using ⟨1, Subsingleton.elim _ _⟩
  constructor
  · intro hg
    refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun t ↦ ?_
    simpa [Units.ext_iff] using Subgroup.mem_center_iff.mp hg (.mk _ _ t.mul_inv t.inv_mul)
  · refine fun ⟨a, ha⟩ ↦ Subgroup.mem_center_iff.mpr fun h ↦ ?_
    simpa [Units.ext_iff, ← ha] using (scalar_commute a (mul_comm a ·) h.val).symm

/-- The center of `GL n R` is the image of `Rˣ`. -/
lemma center_eq_range_units :
    Subgroup.center (GL n R) = (Units.map (algebraMap R _).toMonoidHom).range := by
  ext g
  -- eliminate tedious case `n = ∅`
  rcases isEmpty_or_nonempty n
  · simpa [Subsingleton.elim (Subgroup.center _) ⊤] using ⟨1, Subsingleton.elim _ _⟩
  constructor
  · -- previous lemma shows the underlying matrix is scalar, but now need to show
    -- the scalar is a unit; so we apply argument both to `g` and `g⁻¹`
    intro hg
    obtain ⟨a, ha⟩ := mem_center_iff_val_eq_scalar.mp hg
    obtain ⟨b, hb⟩ := mem_center_iff_val_eq_scalar.mp (Subgroup.inv_mem _ hg)
    have hab : a * b = 1 := by
      simpa [-mul_inv_cancel, ← ha, ← hb, ← diagonal_one, Units.ext_iff] using mul_inv_cancel g
    refine ⟨⟨a, b, hab, mul_comm a b ▸ hab⟩, ?_⟩
    simp [Units.ext_iff, ← ha, algebraMap_eq_diagonal]
  · rintro ⟨a, rfl⟩
    exact mem_center_iff_val_eq_scalar.mpr ⟨a, rfl⟩

end Center

end GeneralLinearGroup

end Matrix
