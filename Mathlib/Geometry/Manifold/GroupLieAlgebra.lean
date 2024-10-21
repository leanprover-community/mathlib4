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
  mfderiv I I (fun a ↦ g * a) (1 : G) v

lemma invariantVectorField_add (v w : LieGroupAlgebra I G) :
    invariantVectorField (v + w) = invariantVectorField v + invariantVectorField w := by
  ext g
  simp [invariantVectorField]


theorem contMDiff_invariantVectorField [LieGroup I G] (v : LieGroupAlgebra I G) :
    ContMDiff I I.tangent ⊤
      (fun (g : G) ↦ (invariantVectorField v g : TangentBundle I G)) := by
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
    rw [mfderiv_prod_eq_add_apply _ _ _ (smooth_mul I (G := G)).mdifferentiableAt]
    simp [invariantVectorField]

open VectorField

instance : Bracket (LieGroupAlgebra I G) (LieGroupAlgebra I G) where
  bracket v w := mlieBracket I (invariantVectorField v) (invariantVectorField w) (1 : G)

lemma bracket_def (v w : LieGroupAlgebra I G) :
    ⁅v, w⁆ = mlieBracket I (invariantVectorField v) (invariantVectorField w) (1 : G) := rfl

variable [LieGroup I G] [CompleteSpace E]

instance [LieGroup I G] : LieRing (TangentSpace I (1 : G)) where
  add_lie v w x := by
    simp only [bracket_def, invariantVectorField_add, mlieBracket_add_left]
    rw [mlieBracket_add_left]
    apply ((contMDiff_invariantVectorField v).mdifferentiable le_top)






  lie_add := sorry
  lie_self := sorry
  leibniz_lie := sorry


end LieGroup
