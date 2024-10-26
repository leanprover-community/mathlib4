/-
Copyright (c) 2024 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
Documentation
-/
/-
Hodge star operator or Hodge star is a linear map defined on the exterior algebra of a
finite-dimensional oriented vector space endowed with a nondegenerate symmetric bilinear form.

α = ⋀ α_i , β = ⋀ β_i ∈ ⋀ᵏ V
⟨α , β⟩ = det( ⟨α_i , β_j⟩ )

{e_i} orthonormal basis for V
ω = ⋀ e_i
α ∧ ⋆β = ⟨α , β⟩ ω
-/

open ExteriorAlgebra CliffordAlgebra LinearMap

namespace Hodge

noncomputable section HodgeStar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
instance : Nonempty (Fin <| Module.finrank ℝ E) := Fin.pos_iff_nonempty.mp Module.finrank_pos
variable (o : Orientation ℝ E (Fin <| Module.finrank ℝ E))

def orientedBasis : OrthonormalBasis (Fin <| Module.finrank ℝ E) ℝ E :=
  OrthonormalBasis.adjustToOrientation (stdOrthonormalBasis ℝ E) o

def vol : ExteriorAlgebra ℝ E := (ιMulti ℝ (Module.finrank ℝ E)) (orientedBasis o)

variable (B : LinearMap.BilinForm ℝ E) --(Bsymm : B.IsSymm) --(Bnondeg : B.Nondegenerate)

def Q := BilinMap.toQuadraticMap B
def C := CliffordAlgebra (Q B)

def star : (ExteriorAlgebra ℝ E) → (ExteriorAlgebra ℝ E) :=
  fun v ↦ equivExterior (Q B) ((equivExterior (Q B)).symm v * (equivExterior (Q B)).symm (vol o))

theorem star_add : ∀ v w : ExteriorAlgebra ℝ E, star o B (v + w) = star o B v + star o B w := by
  intro v w
  unfold star
  rw [map_add, add_mul, map_add]

theorem star_smul : ∀ (r : ℝ) (v : ExteriorAlgebra ℝ E), star o B (r • v) = r • star o B v := by
  intro r v
  unfold star
  rw [map_smul, smul_mul_assoc, map_smul]

def starLinear : ExteriorAlgebra ℝ E →ₗ[ℝ] ExteriorAlgebra ℝ E where
  toFun := star o B
  map_add' := star_add o B
  map_smul' := star_smul o B

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem equivExterior_one : equivExterior (Q B) 1 = 1 := by
  simp only [equivExterior, map_neg, changeFormEquiv_apply, changeForm_one]

theorem star_one : star o B 1 = vol o := by
  unfold star
  rw [← equivExterior_one, LinearEquiv.symm_apply_apply, one_mul, LinearEquiv.apply_symm_apply]

theorem star_vol : star o B (vol o) = 1 := by
  unfold star
  rw [← equivExterior_one B]
  congr

  sorry

theorem star_star (v : ExteriorAlgebra ℝ E) : star o B (star o B v) = v := by
  unfold star
  rw [LinearEquiv.symm_apply_apply]

  sorry

theorem star_grading {i : ℕ} {v : ExteriorAlgebra ℝ E} :
  v ∈ ⋀[ℝ]^i E → star o B v ∈ ⋀[ℝ]^(Module.finrank ℝ E - i) E := by
  intro hv

  sorry

end HodgeStar

end Hodge
