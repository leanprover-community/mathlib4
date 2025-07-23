import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.SchurComplement

variable {𝕜 E n : Type*} [AddCommMonoid E]

namespace LinearMap.BilinForm

section IsPos

section Def

variable [RCLike 𝕜] [Module 𝕜 E] (f : LinearMap.BilinForm 𝕜 E)

/-- A bilinear map `f` is positive if for any `x`, `0 ≤ re (f x x)` -/
structure IsPos : Prop where
  nonneg_re : ∀ x, 0 ≤ RCLike.re (f x x)

lemma isPos_def : f.IsPos ↔ ∀ x, 0 ≤ RCLike.re (f x x) where
  mp := fun ⟨h⟩ ↦ h
  mpr h := ⟨h⟩

end Def

section Real

variable [Module ℝ E] (f : LinearMap.BilinForm ℝ E) (b : Basis n ℝ E)

lemma isPos_def_real : f.IsPos ↔ ∀ x, 0 ≤ f x x := by simp [isPos_def]

variable {f} in
lemma IsPos.nonneg (hf : IsPos f) (x : E) : 0 ≤ f x x := f.isPos_def_real.1 hf x

end Real

end IsPos

variable [Module ℝ E] (f : LinearMap.BilinForm ℝ E) (b : Basis n ℝ E)

section IsPosSemidef

/-- A bilinear map is positive semidefinite if it is symmetric and positive. We only
define it for the real field, because for the complex case we may want to consider sesquilinear
forms instead. -/
structure IsPosSemidef : Prop extends f.IsSymm, f.IsPos

variable {f}

lemma IsPosSemidef.isSymm (hf : IsPosSemidef f) :f.IsSymm := hf.toIsSymm

lemma IsPosSemidef.isPos (hf : IsPosSemidef f) : f.IsPos := hf.toIsPos

variable (f)

lemma isPosSemidef_iff : f.IsPosSemidef ↔ f.IsSymm ∧ f.IsPos where
  mp h := ⟨h.isSymm, h.isPos⟩
  mpr := fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩

variable {f} [Fintype n] [DecidableEq n]

lemma isPosSemidef_iff_posSemidef_toMatrix :
    f.IsPosSemidef ↔ (BilinForm.toMatrix b f).PosSemidef := by
  rw [isPosSemidef_iff, Matrix.PosSemidef, Matrix.isHermitian_iff_isSymm]
  apply and_congr (BilinForm.isSymm_iff_isSymm_toMatrix b f)
  rw [isPos_def]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · rw [BilinForm.dotProduct_toMatrix_mulVec]
    exact h _
  · rw [BilinForm.apply_eq_dotProduct_toMatrix_mulVec b]
    exact h _

end IsPosSemidef

end LinearMap.BilinForm
