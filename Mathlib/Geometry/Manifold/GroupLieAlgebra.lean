/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# The Lie algebra of a Lie group

Given a Lie group, we define `GroupLieAlgebra I G` as its tangent space at the identity, and we
endow it with a Lie bracket, as follows. Given two vectors `v, w : GroupLieAlgebra I G`, consider
the associated left-invariant vector fields `mulInvariantVectorField v` (given at a point `g` by
the image of `v` under the derivative of left-multiplication by `g`) and
`mulInvariantVectorField w`. Then take their Lie bracket at the identity: this is by definition
the bracket of `v` and `w`.

Due to general properties of the Lie bracket of vector fields, this gives a Lie algebra structure
on `GroupLieAlgebra I G`.

Note that one can also define a Lie algebra on the space of left-invariant derivations on `C^∞`
functions (see `LeftInvariantDerivation.instLieAlgebra`). For finite-dimensional `C^∞` real
manifolds, this space of derivations can be canonically identified with the tangent space, and we
recover the same Lie algebra structure (TODO: prove this). In other smoothness classes or on other
fields, this identification is not always true, though, so the derivations point of view does not
work in these settings. Therefore, the point of view in the current file is more general, and
should be favored when possible.

The standing assumption in this file is that the group is `C^n` for `n = minSmoothness 𝕜 3`, i.e.,
it is `C^3` over `ℝ` or `ℂ`, and analytic otherwise.
-/

@[expose] public section

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
`GroupLieAlgebra` instead of `LieAlgebra` as the latter is taken as a generic class. -/
@[to_additive /-- The Lie algebra of an additive Lie group, i.e., its tangent space at zero. We use
the word `AddGroupLieAlgebra` instead of `LieAlgebra` as the latter is taken as a generic class. -/]
abbrev GroupLieAlgebra : Type _ := TangentSpace I (1 : G)

/-- The invariant vector field associated to a vector `v` in the Lie algebra. At a point `g`, it
is given by the image of `v` under left-multiplication by `g`. -/
@[to_additive /-- The invariant vector field associated to a vector `v` in the Lie algebra. At a
point `g`, it is given by the image of `v` under left-addition by `g`. -/]
noncomputable def mulInvariantVectorField (v : GroupLieAlgebra I G) (g : G) : TangentSpace I g :=
  mfderiv% (g * ·) (1 : G) v

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
lemma mulInvariantVectorField_add (v w : GroupLieAlgebra I G) :
    mulInvariantVectorField (v + w) = mulInvariantVectorField v + mulInvariantVectorField w := by
  ext g
  simp [mulInvariantVectorField]

set_option backward.isDefEq.respectTransparency false in
/- `to_additive` fails on the next lemma, as it tries to additivize `smul` while it shouldn't.
Therefore, we state and prove by hand the additive version. -/
lemma addInvariantVectorField_smul {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [AddGroup G]
    (c : 𝕜) (v : AddGroupLieAlgebra I G) :
    addInvariantVectorField (c • v) = c • addInvariantVectorField v := by
  ext g
  simp [addInvariantVectorField]

set_option backward.isDefEq.respectTransparency false in
lemma mulInvariantVectorField_smul (c : 𝕜) (v : GroupLieAlgebra I G) :
    mulInvariantVectorField (c • v) = c • mulInvariantVectorField v := by
  ext g
  simp [mulInvariantVectorField]

open VectorField

/-- The Lie bracket of two vectors `v` and `w` in the Lie algebra of a Lie group is obtained by
taking the Lie bracket of the associated invariant vector fields, at the identity. -/
@[to_additive /-- The Lie bracket of two vectors `v` and `w` in the Lie algebra of an additive Lie
group is obtained by taking the Lie bracket of the associated invariant vector fields, at zero. -/]
noncomputable instance : Bracket (GroupLieAlgebra I G) (GroupLieAlgebra I G) where
  bracket v w := mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w) (1 : G)

@[to_additive]
lemma GroupLieAlgebra.bracket_def (v w : GroupLieAlgebra I G) :
    ⁅v, w⁆ = mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w) (1 : G) := rfl

variable [LieGroup I (minSmoothness 𝕜 3) G]

@[to_additive (attr := simp)]
lemma inverse_mfderiv_mul_left {g h : G} :
    (mfderiv% (fun b ↦ g * b) h).inverse = mfderiv% (fun b ↦ g⁻¹ * b) (g * h) := by
  have M : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have A : mfderiv% ((fun x ↦ g⁻¹ * x) ∘ (fun x ↦ g * x)) h =
      ContinuousLinearMap.id _ _ := by
    have : (fun x ↦ g⁻¹ * x) ∘ (fun x ↦ g * x) = id := by ext x; simp
    rw [this, id_eq, mfderiv_id]
  rw [mfderiv_comp (I' := I) _ (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)
    (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)] at A
  have A' : mfderiv% ((fun x ↦ g * x) ∘ (fun x ↦ g⁻¹ * x)) (g * h) =
      ContinuousLinearMap.id _ _ := by
    have : (fun x ↦ g * x) ∘ (fun x ↦ g⁻¹ * x) = id := by ext x; simp
    rw [this, id_eq, mfderiv_id]
  rw [mfderiv_comp (I' := I) _ (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)
    (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M), inv_mul_cancel_left g h] at A'
  exact ContinuousLinearMap.inverse_eq A' A

/-- Invariant vector fields are invariant under pullbacks. -/
@[to_additive /-- Invariant vector fields are invariant under pullbacks. -/]
lemma mpullback_mulInvariantVectorField (g : G) (v : GroupLieAlgebra I G) :
    mpullback I I (g * ·) (mulInvariantVectorField v) = mulInvariantVectorField v := by
  have M : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  ext h
  simp only [mpullback, inverse_mfderiv_mul_left, mulInvariantVectorField]
  have D : (fun x ↦ h * x) = (fun b ↦ g⁻¹ * b) ∘ (fun x ↦ g * h * x) := by
    ext x; simp only [comp_apply]; group
  rw [D, mfderiv_comp (I' := I)]
  · congr 2
    simp
  · exact contMDiff_mul_left.contMDiffAt.mdifferentiableAt M
  · exact contMDiff_mul_left.contMDiffAt.mdifferentiableAt M

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
lemma mulInvariantVectorField_eq_mpullback (g : G) (V : Π (g : G), TangentSpace I g) :
    mulInvariantVectorField (V 1) g = mpullback I I (g⁻¹ * ·) V g := by
  have A : 1 = g⁻¹ * g := by simp
  simp only [mulInvariantVectorField, mpullback, inverse_mfderiv_mul_left]
  congr
  simp

@[to_additive]
theorem contMDiff_mulInvariantVectorField (v : GroupLieAlgebra I G) :
    CMDiff (minSmoothness 𝕜 2)
      (fun (g : G) ↦ (mulInvariantVectorField v g : TangentBundle I G)) := by
  /- We will write the desired map as a composition of obviously smooth maps.
  The derivative of the product `P : (g, h) ↦ g * h` is given by
  `DP (g, h) ⬝ (u, v) = DL_g v + DR_h u`, where `L_g` and `R_h` are respectively left and right
  multiplication by `g` and `h`. As `P` is smooth, so is `DP`.
  Consider the map `F₁ : M → T (M × M)` mapping `g` to `(0, v) ∈ T_(g, e) (M × M)`. Then the
  composition of `DP` with `F₁` maps `g` to `DL_g v ∈ T_g M`, thanks to the above formula. This
  is the desired invariant vector field. Since both `DP` and `F₁` are smooth, their composition is
  smooth as desired.
  There is a small abuse of notation in the above argument, where we have identified `T (M × M)`
  and `TM × TM`. In the formal proof, we need to introduce this identification, called `F₂` below,
  which is also already known to be smooth. -/
  have M : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have A : minSmoothness 𝕜 2 + 1 = minSmoothness 𝕜 3 := by
    rw [← minSmoothness_add]
    norm_num
  let fg : G → TangentBundle I G := fun g ↦ TotalSpace.mk' E g 0
  have sfg : CMDiff (minSmoothness 𝕜 2) fg := contMDiff_zeroSection _ _
  let fv : G → TangentBundle I G := fun _ ↦ TotalSpace.mk' E 1 v
  have sfv : CMDiff (minSmoothness 𝕜 2) fv := contMDiff_const
  let F₁ : G → (TangentBundle I G × TangentBundle I G) := fun g ↦ (fg g, fv g)
  have S₁ : CMDiff (minSmoothness 𝕜 2) F₁ := sfg.prodMk sfv
  let F₂ : (TangentBundle I G × TangentBundle I G) → TangentBundle (I.prod I) (G × G) :=
    (equivTangentBundleProd I G I G).symm
  have S₂ : CMDiff (minSmoothness 𝕜 2) F₂ := contMDiff_equivTangentBundleProd_symm
  let F₃ : TangentBundle (I.prod I) (G × G) → TangentBundle I G :=
    tangentMap (I.prod I) I (fun (p : G × G) ↦ p.1 * p.2)
  have S₃ : CMDiff (minSmoothness 𝕜 2) F₃ := by
    apply ContMDiff.contMDiff_tangentMap _ (m := minSmoothness 𝕜 2) le_rfl
    rw [A]
    exact contMDiff_mul I (minSmoothness 𝕜 3)
  let S := (S₃.comp S₂).comp S₁
  convert S with g
  · simp [F₁, F₂, F₃, fg, fv]
  · simp only [comp_apply, tangentMap, F₃, F₂, F₁, fg, fv]
    rw [mfderiv_prod_eq_add_apply ((contMDiff_mul I (minSmoothness 𝕜 3)).mdifferentiableAt M)]
    simp +instances [mulInvariantVectorField]

@[to_additive]
theorem contMDiffAt_mulInvariantVectorField (v : GroupLieAlgebra I G) {g : G} :
    CMDiffAt (minSmoothness 𝕜 2)
      (fun (g : G) ↦ (mulInvariantVectorField v g : TangentBundle I G)) g :=
  (contMDiff_mulInvariantVectorField v).contMDiffAt

@[to_additive]
theorem mdifferentiable_mulInvariantVectorField (v : GroupLieAlgebra I G) :
    MDiff (fun (g : G) ↦ (mulInvariantVectorField v g : TangentBundle I G)) :=
  (contMDiff_mulInvariantVectorField v).mdifferentiable
    (lt_of_lt_of_le (by simp) le_minSmoothness).ne'

@[to_additive]
theorem mdifferentiableAt_mulInvariantVectorField (v : GroupLieAlgebra I G) {g : G} :
    MDiffAt (fun (g : G) ↦ (mulInvariantVectorField v g : TangentBundle I G)) g :=
  (contMDiffAt_mulInvariantVectorField v).mdifferentiableAt
    (lt_of_lt_of_le (by simp) le_minSmoothness).ne'

open VectorField

variable [CompleteSpace E]

/-- The invariant vector field associated to the value at the identity of the Lie bracket of
two invariant vector fields, is everywhere the Lie bracket of the invariant vector fields. -/
@[to_additive /-- The invariant vector field associated to the value at zero of the Lie
bracket of two invariant vector fields, is everywhere the Lie bracket of the invariant vector
fields. -/]
lemma mulInvariantVector_mlieBracket (v w : GroupLieAlgebra I G) :
    mulInvariantVectorField
      (mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w) 1) =
    mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w) := by
  ext g
  rw [mulInvariantVectorField_eq_mpullback, mpullback_mlieBracket (n := minSmoothness 𝕜 3),
    mpullback_mulInvariantVectorField, mpullback_mulInvariantVectorField]
  · exact mdifferentiableAt_mulInvariantVectorField _
  · exact mdifferentiableAt_mulInvariantVectorField _
  · exact contMDiffAt_mul_left
  · exact minSmoothness_monotone (by norm_cast)

/-- The tangent space at the identity of a Lie group is a Lie ring, for the bracket
given by the Lie bracket of invariant vector fields. -/
@[to_additive /-- The tangent space at the identity of an additive Lie group is a Lie ring, for the
bracket given by the Lie bracket of invariant vector fields. -/]
noncomputable instance : LieRing (GroupLieAlgebra I G) where
  add_lie u v w := by
    simp only [GroupLieAlgebra.bracket_def, mulInvariantVectorField_add]
    rw [mlieBracket_add_left]
    · exact mdifferentiableAt_mulInvariantVectorField _
    · exact mdifferentiableAt_mulInvariantVectorField _
  lie_add u v w := by
    simp only [GroupLieAlgebra.bracket_def, mulInvariantVectorField_add]
    rw [mlieBracket_add_right]
    · exact mdifferentiableAt_mulInvariantVectorField _
    · exact mdifferentiableAt_mulInvariantVectorField _
  lie_self v := by simp [GroupLieAlgebra.bracket_def]
  leibniz_lie u v w := by
    simp only [GroupLieAlgebra.bracket_def, mulInvariantVector_mlieBracket]
    apply leibniz_identity_mlieBracket_apply <;>
      exact contMDiff_mulInvariantVectorField _ _

/- `to_additive` fails on the next instance, as it tries to additivize `smul` while it shouldn't.
Therefore, we state and prove by hand the additive version. -/

/-- The tangent space at the identity of an additive Lie group is a Lie algebra, for the bracket
given by the Lie bracket of invariant vector fields. -/
noncomputable instance instLieAlgebraAddGroupLieAlgebra
    {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [AddGroup G]
    [LieAddGroup I (minSmoothness 𝕜 3) G] : LieAlgebra 𝕜 (AddGroupLieAlgebra I G) where
  lie_smul c v w := by
    simp only [AddGroupLieAlgebra.bracket_def, addInvariantVectorField_smul]
    rw [mlieBracket_const_smul_right]
    exact mdifferentiableAt_addInvariantVectorField _

/-- The tangent space at the identity of a Lie group is a Lie algebra, for the bracket
given by the Lie bracket of invariant vector fields. -/
noncomputable instance instLieAlgebraGroupLieAlgebra : LieAlgebra 𝕜 (GroupLieAlgebra I G) where
  lie_smul c v w := by
    simp only [GroupLieAlgebra.bracket_def, mulInvariantVectorField_smul]
    rw [mlieBracket_const_smul_right]
    exact mdifferentiableAt_mulInvariantVectorField _

end LieGroup
