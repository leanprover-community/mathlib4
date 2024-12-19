/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.VectorField

/-!
# The Lie algebra of a Lie group

Given a Lie group, we define `LieGroupAlgebra I G` as its tangent space at the identity, and we
endow it with a Lie bracket, as follows. Given two vectors `v, w : LieGroupAlgebra I G`, consider
the associated left-invariant vector fields `invariantVectorField v` (given at a point `g` by
the image of `v` under the derivative of left-multiplication by `g`) and `invariantVectorField w`.
Then take their Lie bracket at the identity: this is by definition the bracket of `v` and `w`.

Due to general properties of the Lie bracket of vector fields, this gives a Lie algebra structure
on `LieGroupAlgebra I G`.

Note that one can also define a Lie algebra on the space of left-invariant derivations on `C^∞`
functions (see `LeftInvariantDerivation.instLieAlgebra`). For finite-dimensional `C^∞` real
manifolds, this space of derivations can be canonically identified with the tangent space, and we
recover the same Lie algebra structure (TODO: prove this). In other smoothness classes or on other
fields, this identification is not always true, though, so the derivations point of view does not
work in these settings. Therefore, the point of view in the current file is more general, and
should be favored when possible.
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
/-- The Lie algebra of a Lie group, i.e., its tangent space at the identity. We use the word
`LieGroupAlgebra` instead of `LieAlgebra` as the latter is taken as a generic class. -/
abbrev LieGroupAlgebra : Type _ := TangentSpace I (1 : G)

/-- The invariant vector field associated to a vector in the Lie alebra. -/
def invariantVectorField (v : LieGroupAlgebra I G) (g : G) : TangentSpace I g :=
  mfderiv I I (g * ·) (1 : G) v

lemma invariantVectorField_add (v w : LieGroupAlgebra I G) :
    invariantVectorField (v + w) = invariantVectorField v + invariantVectorField w := by
  ext g
  simp [invariantVectorField]

lemma invariantVectorField_smul (c : 𝕜) (v : LieGroupAlgebra I G) :
    invariantVectorField (c • v) = c • invariantVectorField v := by
  ext g
  simp [invariantVectorField]

open VectorField

variable [LieGroup I G]

@[simp]
lemma inverse_mfderiv_mul_left {g h : G} :
    (mfderiv I I (fun b ↦ g * b) h).inverse = mfderiv I I (fun b ↦ g⁻¹ * b) (g * h) := by
  have A : mfderiv I I ((fun x ↦ g⁻¹ * x) ∘ (fun x ↦ g * x)) h =
      ContinuousLinearMap.id _ _ := by
    have : (fun x ↦ g⁻¹ * x) ∘ (fun x ↦ g * x) = id := by ext x; simp
    rw [this, id_eq, mfderiv_id]
  rw [mfderiv_comp (I' := I) _ (contMDiff_mul_left.contMDiffAt.mdifferentiableAt le_top)
    (contMDiff_mul_left.contMDiffAt.mdifferentiableAt le_top)] at A
  have A' : mfderiv I I ((fun x ↦ g * x) ∘ (fun x ↦ g⁻¹ * x)) (g * h) =
      ContinuousLinearMap.id _ _ := by
    have : (fun x ↦ g * x) ∘ (fun x ↦ g⁻¹ * x) = id := by ext x; simp
    rw [this, id_eq, mfderiv_id]
  rw [mfderiv_comp (I' := I) _ (contMDiff_mul_left.contMDiffAt.mdifferentiableAt le_top)
    (contMDiff_mul_left.contMDiffAt.mdifferentiableAt le_top), inv_mul_cancel_left g h] at A'
  exact ContinuousLinearMap.inverse_eq A' A

lemma mpullback_invariantVectorField (g : G) (v : LieGroupAlgebra I G) :
    mpullback I I (g * ·) (invariantVectorField v) = invariantVectorField v := by
  ext h
  simp only [mpullback, inverse_mfderiv_mul_left, invariantVectorField]
  have D : (fun x ↦ h * x) = (fun b ↦ g⁻¹ * b) ∘ (fun x ↦ g * h * x) := by
    ext x; simp only [comp_apply]; group
  rw [D, mfderiv_comp (I' := I)]
  · congr 2
    simp
  · exact contMDiff_mul_left.contMDiffAt.mdifferentiableAt le_top
  · exact contMDiff_mul_left.contMDiffAt.mdifferentiableAt le_top

lemma invariantVectorField_eq_mpullback (g : G) (V : Π (g : G), TangentSpace I g) :
    invariantVectorField (V 1) g = mpullback I I (g ⁻¹ * ·) V g := by
  have A : 1 = g⁻¹ * g := by simp
  simp [invariantVectorField, mpullback]
  congr
  simp

theorem contMDiff_invariantVectorField (v : LieGroupAlgebra I G) {n : ℕ∞} :
    ContMDiff I I.tangent n
      (fun (g : G) ↦ (invariantVectorField v g : TangentBundle I G)) := by
  apply ContMDiff.of_le _ le_top
  let fg : G → TangentBundle I G := fun g ↦ TotalSpace.mk' E g 0
  have sfg : ContMDiff I I.tangent ⊤ fg := contMDiff_zeroSection _ _
  let fv : G → TangentBundle I G := fun _ ↦ TotalSpace.mk' E 1 v
  have sfv : ContMDiff I I.tangent ⊤ fv := contMDiff_const
  let F₁ : G → (TangentBundle I G × TangentBundle I G) := fun g ↦ (fg g, fv g)
  have S₁ : ContMDiff I (I.tangent.prod I.tangent) ⊤ F₁ := ContMDiff.prod_mk sfg sfv
  let F₂ : (TangentBundle I G × TangentBundle I G) → TangentBundle (I.prod I) (G × G) :=
    (equivTangentBundleProd I G I G).symm
  have S₂ : ContMDiff (I.tangent.prod I.tangent) (I.prod I).tangent ⊤ F₂ :=
    smooth_equivTangentBundleProd_symm
  let F₃ : TangentBundle (I.prod I) (G × G) → TangentBundle I G :=
    tangentMap (I.prod I) I (fun (p : G × G) ↦ p.1 * p.2)
  have S₃ : ContMDiff (I.prod I).tangent I.tangent ⊤ F₃ := by
    apply ContMDiff.contMDiff_tangentMap _ (m := ⊤) le_rfl
    exact contMDiff_mul I (G := G)
  let S := (S₃.comp S₂).comp S₁
  convert S with g
  · simp [F₁, F₂, F₃]
  · simp only [comp_apply, tangentMap, F₃, F₂, F₁]
    rw [mfderiv_prod_eq_add_apply ((contMDiff_mul I (G := G)).mdifferentiableAt le_top)]
    simp [invariantVectorField]

theorem contMDiffAt_invariantVectorField (v : LieGroupAlgebra I G) {n : ℕ∞} {g : G }:
    ContMDiffAt I I.tangent n
      (fun (g : G) ↦ (invariantVectorField v g : TangentBundle I G)) g :=
  (contMDiff_invariantVectorField v).contMDiffAt

theorem mdifferentiable_invariantVectorField (v : LieGroupAlgebra I G) :
    MDifferentiable I I.tangent
      (fun (g : G) ↦ (invariantVectorField v g : TangentBundle I G)) :=
  (contMDiff_invariantVectorField v).mdifferentiable le_rfl

theorem mdifferentiableAt_invariantVectorField (v : LieGroupAlgebra I G) {g : G} :
    MDifferentiableAt I I.tangent
      (fun (g : G) ↦ (invariantVectorField v g : TangentBundle I G)) g :=
  (contMDiffAt_invariantVectorField v).mdifferentiableAt le_rfl

open VectorField

instance : Bracket (LieGroupAlgebra I G) (LieGroupAlgebra I G) where
  bracket v w := mlieBracket I (invariantVectorField v) (invariantVectorField w) (1 : G)

omit [LieGroup I G] in
lemma bracket_def (v w : LieGroupAlgebra I G) :
    ⁅v, w⁆ = mlieBracket I (invariantVectorField v) (invariantVectorField w) (1 : G) := rfl

variable [IsRCLikeNormedField 𝕜] [CompleteSpace E]

lemma invariantVector_mlieBracket (v w : LieGroupAlgebra I G) :
    invariantVectorField (mlieBracket I (invariantVectorField v) (invariantVectorField w) 1) =
    mlieBracket I (invariantVectorField v) (invariantVectorField w) := by
  ext g
  rw [invariantVectorField_eq_mpullback, mpullback_mlieBracket, mpullback_invariantVectorField,
    mpullback_invariantVectorField]
  · exact mdifferentiableAt_invariantVectorField _
  · exact mdifferentiableAt_invariantVectorField _
  · exact contMDiffAt_mul_left

instance : LieRing (LieGroupAlgebra I G) where
  add_lie u v w := by
    simp only [bracket_def, invariantVectorField_add]
    rw [mlieBracket_add_left]
    · exact mdifferentiableAt_invariantVectorField _
    · exact mdifferentiableAt_invariantVectorField _
  lie_add u v w := by
    simp only [bracket_def, invariantVectorField_add]
    rw [mlieBracket_add_right]
    · exact mdifferentiableAt_invariantVectorField _
    · exact mdifferentiableAt_invariantVectorField _
  lie_self v := by simp [bracket_def]
  leibniz_lie u v w := by
    simp [bracket_def, invariantVector_mlieBracket]
    apply leibniz_identity_mlieBracket_apply <;>
      exact contMDiff_invariantVectorField _ _

instance : LieAlgebra 𝕜 (LieGroupAlgebra I G) where
  lie_smul c v w := by
    simp only [bracket_def, invariantVectorField_smul]
    rw [mlieBracket_smul_right]
    exact mdifferentiableAt_invariantVectorField _

end LieGroup
