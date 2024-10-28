/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Geometry.Manifold.VectorField
import Mathlib.Algebra.Lie.Basic

/-!
# Glouglou2

-/

noncomputable section

section LieGroup

open Bundle Filter Function Set
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

variable (I G) in
abbrev LieGroupAlgebra : Type _ := (TangentSpace I (1 : G))

/-- The invariant vector field associated to a vector in the Lie alebra. -/
def invariantVectorField (v : LieGroupAlgebra I G) (g : G) : TangentSpace I g :=
  mfderiv I I (g * ·) (1 : G) v

lemma invariantVectorField_add (v w : LieGroupAlgebra I G) :
    invariantVectorField (v + w) = invariantVectorField v + invariantVectorField w := by
  ext g
  simp [invariantVectorField]


open VectorField

variable [LieGroup I G]

lemma mpullback_invariantVectorField (g : G) (v : LieGroupAlgebra I G) :
    mpullback I I (g * ·) (invariantVectorField v) = invariantVectorField v := by
  ext h
  simp [mpullback, invariantVectorField]
  have A (x : G) : mfderiv I I ((fun x ↦ g⁻¹ * x) ∘ (fun x ↦ g * x)) x =
      ContinuousLinearMap.id _ _ := by
    have : (fun x ↦ g⁻¹ * x) ∘ (fun x ↦ g * x) = id := by ext x; simp
    rw [this, id_eq, mfderiv_id]
  have B := A h
  rw [mfderiv_comp (I' := I) _ smooth_mul_left.smoothAt.mdifferentiableAt
    smooth_mul_left.smoothAt.mdifferentiableAt] at B
  have A' (x : G) : mfderiv I I ((fun x ↦ g * x) ∘ (fun x ↦ g⁻¹ * x)) x =
      ContinuousLinearMap.id _ _ := by
    have : (fun x ↦ g * x) ∘ (fun x ↦ g⁻¹ * x) = id := by ext x; simp
    rw [this, id_eq, mfderiv_id]
  have B' := A' (g * h)
  have : g⁻¹ * (g * h) = h := by group
  rw [mfderiv_comp (I' := I) _ smooth_mul_left.smoothAt.mdifferentiableAt
    smooth_mul_left.smoothAt.mdifferentiableAt, this] at B'
  have : (mfderiv I I (fun b ↦ g * b) h).inverse = (mfderiv I I (fun b ↦ g⁻¹ * b) (g * h)) :=
    ContinuousLinearMap.inverse_eq B' B
  rw [this, ← mfderiv_comp_apply]








#exit

theorem contMDiff_invariantVectorField [LieGroup I G] (v : LieGroupAlgebra I G) {n : ℕ∞} :
    ContMDiff I I.tangent n
      (fun (g : G) ↦ (invariantVectorField v g : TangentBundle I G)) := by
  apply ContMDiff.of_le _ le_top
  let fg : G → TangentBundle I G := fun g ↦ TotalSpace.mk' E g 0
  have sfg : Smooth I I.tangent fg := smooth_zeroSection _ _
  let fv : G → TangentBundle I G := fun _ ↦ TotalSpace.mk' E 1 v
  have sfv : Smooth I I.tangent fv := smooth_const
  let F₁ : G → (TangentBundle I G × TangentBundle I G) := fun g ↦ (fg g, fv g)
  have S₁ : Smooth I (I.tangent.prod I.tangent) F₁ := Smooth.prod_mk sfg sfv
  let F₂ : (TangentBundle I G × TangentBundle I G) → TangentBundle (I.prod I) (G × G) :=
    (equivTangentBundleProd I G I G).symm
  have S₂ : Smooth (I.tangent.prod I.tangent) (I.prod I).tangent F₂ :=
    smooth_equivTangentBundleProd_symm
  let F₃ : TangentBundle (I.prod I) (G × G) → TangentBundle I G :=
    tangentMap (I.prod I) I (fun (p : G × G) ↦ p.1 * p.2)
  have S₃ : Smooth (I.prod I).tangent I.tangent F₃ := by
    apply ContMDiff.contMDiff_tangentMap _ (m := ⊤) le_rfl
    exact smooth_mul I (G := G)
  let S := (S₃.comp S₂).comp S₁
  convert S with g
  · simp [F₁, F₂, F₃]
  · simp only [comp_apply, tangentMap, F₃, F₂, F₁]
    rw [mfderiv_prod_eq_add_apply (smooth_mul I (G := G)).mdifferentiableAt]
    simp [invariantVectorField]

open VectorField

instance : Bracket (LieGroupAlgebra I G) (LieGroupAlgebra I G) where
  bracket v w := mlieBracket I (invariantVectorField v) (invariantVectorField w) (1 : G)

lemma bracket_def (v w : LieGroupAlgebra I G) :
    ⁅v, w⁆ = mlieBracket I (invariantVectorField v) (invariantVectorField w) (1 : G) := rfl

variable [IsRCLikeNormedField 𝕜]

lemma foo (v w : LieGroupAlgebra I G) :
  invariantVectorField (mlieBracket I (invariantVectorField v) (invariantVectorField w) 1) =
  mlieBracket I (invariantVectorField v) (invariantVectorField w) := sorry

variable [LieGroup I G] [CompleteSpace E]

instance [LieGroup I G] : LieRing (TangentSpace I (1 : G)) where
  add_lie u v w := by
    simp only [bracket_def, invariantVectorField_add]
    rw [mlieBracket_add_left]
    · exact ((contMDiff_invariantVectorField _).mdifferentiable le_top).mdifferentiableAt
    · exact ((contMDiff_invariantVectorField _).mdifferentiable le_top).mdifferentiableAt
  lie_add u v w := by
    simp only [bracket_def, invariantVectorField_add]
    rw [mlieBracket_add_right]
    · exact ((contMDiff_invariantVectorField _).mdifferentiable le_top).mdifferentiableAt
    · exact ((contMDiff_invariantVectorField _).mdifferentiable le_top).mdifferentiableAt
  lie_self v := by simp [bracket_def]
  leibniz_lie u v w := by
    simp [bracket_def, foo]
    apply leibniz_identity_mlieBracket_apply <;>
    exact contMDiff_invariantVectorField _ _

end LieGroup
