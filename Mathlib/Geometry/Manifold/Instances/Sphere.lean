/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.NormedSpace.BallAction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv

#align_import geometry.manifold.instances.sphere from "leanprover-community/mathlib"@"0dc4079202c28226b2841a51eb6d3cc2135bb80f"

/-!
# Manifold structure on the sphere

This file defines stereographic projection from the sphere in an inner product space `E`, and uses
it to put a smooth manifold structure on the sphere.

## Main results

For a unit vector `v` in `E`, the definition `stereographic` gives the stereographic projection
centred at `v`, a local homeomorphism from the sphere to `(ℝ ∙ v)ᗮ` (the orthogonal complement of
`v`).

For finite-dimensional `E`, we then construct a smooth manifold instance on the sphere; the charts
here are obtained by composing the local homeomorphisms `stereographic` with arbitrary isometries
from `(ℝ ∙ v)ᗮ` to Euclidean space.

We prove two lemmas about smooth maps:
* `contMDiff_coe_sphere` states that the coercion map from the sphere into `E` is smooth;
  this is a useful tool for constructing smooth maps *from* the sphere.
* `contMDiff.codRestrict_sphere` states that a map from a manifold into the sphere is
  smooth if its lift to a map to `E` is smooth; this is a useful tool for constructing smooth maps
  *to* the sphere.

As an application we prove `contMdiffNegSphere`, that the antipodal map is smooth.

Finally, we equip the `circle` (defined in `Analysis.Complex.Circle` to be the sphere in `ℂ`
centred at `0` of radius `1`) with the following structure:
* a charted space with model space `EuclideanSpace ℝ (Fin 1)` (inherited from `Metric.Sphere`)
* a Lie group with model with corners `𝓡 1`

We furthermore show that `expMapCircle` (defined in `Analysis.Complex.Circle` to be the natural
map `fun t ↦ exp (t * I)` from `ℝ` to `circle`) is smooth.


## Implementation notes

The model space for the charted space instance is `EuclideanSpace ℝ (Fin n)`, where `n` is a
natural number satisfying the typeclass assumption `[Fact (finrank ℝ E = n + 1)]`.  This may seem a
little awkward, but it is designed to circumvent the problem that the literal expression for the
dimension of the model space (up to definitional equality) determines the type.  If one used the
naive expression `EuclideanSpace ℝ (Fin (finrank ℝ E - 1))` for the model space, then the sphere in
`ℂ` would be a manifold with model space `EuclideanSpace ℝ (Fin (2 - 1))` but not with model space
`EuclideanSpace ℝ (Fin 1)`.

## TODO

Relate the stereographic projection to the inversion of the space.
-/


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable section

open Metric FiniteDimensional Function

open scoped Manifold

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

section StereographicProjection

variable (v : E)

/-! ### Construction of the stereographic projection -/


/-- Stereographic projection, forward direction. This is a map from an inner product space `E` to
the orthogonal complement of an element `v` of `E`. It is smooth away from the affine hyperplane
through `v` parallel to the orthogonal complement.  It restricts on the sphere to the stereographic
projection. -/
def stereoToFun (x : E) : (ℝ ∙ v)ᗮ :=
  (2 / ((1 : ℝ) - innerSL ℝ v x)) • orthogonalProjection (ℝ ∙ v)ᗮ x
#align stereo_to_fun stereoToFun

variable {v}

@[simp]
theorem stereoToFun_apply (x : E) :
    stereoToFun v x = (2 / ((1 : ℝ) - innerSL ℝ v x)) • orthogonalProjection (ℝ ∙ v)ᗮ x :=
  rfl
#align stereo_to_fun_apply stereoToFun_apply

theorem contDiffOn_stereoToFun :
    ContDiffOn ℝ ⊤ (stereoToFun v) {x : E | innerSL _ v x ≠ (1 : ℝ)} := by
  refine' ContDiffOn.smul _ (orthogonalProjection (ℝ ∙ v)ᗮ).contDiff.contDiffOn
  -- ⊢ ContDiffOn ℝ ⊤ (fun x => 2 / (1 - ↑(↑(innerSL ℝ) v) x)) {x | ↑(↑(innerSL ℝ)  …
  refine' contDiff_const.contDiffOn.div _ _
  -- ⊢ ContDiffOn ℝ ⊤ (fun x => 1 - ↑(↑(innerSL ℝ) v) x) {x | ↑(↑(innerSL ℝ) v) x ≠ …
  · exact (contDiff_const.sub (innerSL ℝ v).contDiff).contDiffOn
    -- 🎉 no goals
  · intro x h h'
    -- ⊢ False
    exact h (sub_eq_zero.mp h').symm
    -- 🎉 no goals
#align cont_diff_on_stereo_to_fun contDiffOn_stereoToFun

theorem continuousOn_stereoToFun :
    ContinuousOn (stereoToFun v) {x : E | innerSL _ v x ≠ (1 : ℝ)} :=
  contDiffOn_stereoToFun.continuousOn
#align continuous_on_stereo_to_fun continuousOn_stereoToFun

variable (v)

/-- Auxiliary function for the construction of the reverse direction of the stereographic
projection.  This is a map from the orthogonal complement of a unit vector `v` in an inner product
space `E` to `E`; we will later prove that it takes values in the unit sphere.

For most purposes, use `stereoInvFun`, not `stereoInvFunAux`. -/
def stereoInvFunAux (w : E) : E :=
  (‖w‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v)
#align stereo_inv_fun_aux stereoInvFunAux

variable {v}

@[simp]
theorem stereoInvFunAux_apply (w : E) :
    stereoInvFunAux v w = (‖w‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v) :=
  rfl
#align stereo_inv_fun_aux_apply stereoInvFunAux_apply

theorem stereoInvFunAux_mem (hv : ‖v‖ = 1) {w : E} (hw : w ∈ (ℝ ∙ v)ᗮ) :
    stereoInvFunAux v w ∈ sphere (0 : E) 1 := by
  have h₁ : (0 : ℝ) < ‖w‖ ^ 2 + 4 := by positivity
  -- ⊢ stereoInvFunAux v w ∈ sphere 0 1
  suffices : ‖(4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v‖ = ‖w‖ ^ 2 + 4
  -- ⊢ stereoInvFunAux v w ∈ sphere 0 1
  · simp only [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, this,
      abs_of_pos h₁, stereoInvFunAux_apply, inv_mul_cancel h₁.ne']
  suffices : ‖(4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v‖ ^ 2 = (‖w‖ ^ 2 + 4) ^ 2
  -- ⊢ ‖4 • w + (‖w‖ ^ 2 - 4) • v‖ = ‖w‖ ^ 2 + 4
  · simpa [sq_eq_sq_iff_abs_eq_abs, abs_of_pos h₁] using this
    -- 🎉 no goals
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hw
  -- ⊢ ‖4 • w + (‖w‖ ^ 2 - 4) • v‖ ^ 2 = (‖w‖ ^ 2 + 4) ^ 2
  simp [norm_add_sq_real, norm_smul, inner_smul_left, inner_smul_right, hw, mul_pow,
    Real.norm_eq_abs, hv]
  ring
  -- 🎉 no goals
#align stereo_inv_fun_aux_mem stereoInvFunAux_mem

theorem hasFDerivAt_stereoInvFunAux (v : E) :
    HasFDerivAt (stereoInvFunAux v) (ContinuousLinearMap.id ℝ E) 0 := by
  have h₀ : HasFDerivAt (fun w : E => ‖w‖ ^ 2) (0 : E →L[ℝ] ℝ) 0 := by
    convert (hasStrictFDerivAt_norm_sq (0 : E)).hasFDerivAt
    simp
  have h₁ : HasFDerivAt (fun w : E => (‖w‖ ^ 2 + 4)⁻¹) (0 : E →L[ℝ] ℝ) 0 := by
    convert (hasFDerivAt_inv _).comp _ (h₀.add (hasFDerivAt_const 4 0)) <;> simp
  have h₂ :
    HasFDerivAt (fun w => (4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v) ((4 : ℝ) • ContinuousLinearMap.id ℝ E) 0
  · convert ((hasFDerivAt_const (4 : ℝ) 0).smul (hasFDerivAt_id 0)).add
      ((h₀.sub (hasFDerivAt_const (4 : ℝ) 0)).smul (hasFDerivAt_const v 0)) using 1
    ext w
    -- ⊢ ↑(4 • ContinuousLinearMap.id ℝ E) w = ↑(4 • ContinuousLinearMap.id ℝ E + Con …
    simp
    -- 🎉 no goals
  convert h₁.smul h₂ using 1
  -- ⊢ ContinuousLinearMap.id ℝ E = (‖0‖ ^ 2 + 4)⁻¹ • 4 • ContinuousLinearMap.id ℝ  …
  ext w
  -- ⊢ ↑(ContinuousLinearMap.id ℝ E) w = ↑((‖0‖ ^ 2 + 4)⁻¹ • 4 • ContinuousLinearMa …
  simp
  -- 🎉 no goals
#align has_fderiv_at_stereo_inv_fun_aux hasFDerivAt_stereoInvFunAux

theorem hasFDerivAt_stereoInvFunAux_comp_coe (v : E) :
    HasFDerivAt (stereoInvFunAux v ∘ ((↑) : (ℝ ∙ v)ᗮ → E)) (ℝ ∙ v)ᗮ.subtypeL 0 := by
  have : HasFDerivAt (stereoInvFunAux v) (ContinuousLinearMap.id ℝ E) ((ℝ ∙ v)ᗮ.subtypeL 0) :=
    hasFDerivAt_stereoInvFunAux v
  convert this.comp (0 : (ℝ ∙ v)ᗮ) (by apply ContinuousLinearMap.hasFDerivAt)
  -- 🎉 no goals
#align has_fderiv_at_stereo_inv_fun_aux_comp_coe hasFDerivAt_stereoInvFunAux_comp_coe

theorem contDiff_stereoInvFunAux : ContDiff ℝ ⊤ (stereoInvFunAux v) := by
  have h₀ : ContDiff ℝ ⊤ fun w : E => ‖w‖ ^ 2 := contDiff_norm_sq ℝ
  -- ⊢ ContDiff ℝ ⊤ (stereoInvFunAux v)
  have h₁ : ContDiff ℝ ⊤ fun w : E => (‖w‖ ^ 2 + 4)⁻¹ := by
    refine' (h₀.add contDiff_const).inv _
    intro x
    nlinarith
  have h₂ : ContDiff ℝ ⊤ fun w => (4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v := by
    refine' (contDiff_const.smul contDiff_id).add _
    refine' (h₀.sub contDiff_const).smul contDiff_const
  exact h₁.smul h₂
  -- 🎉 no goals
#align cont_diff_stereo_inv_fun_aux contDiff_stereoInvFunAux

/-- Stereographic projection, reverse direction.  This is a map from the orthogonal complement of a
unit vector `v` in an inner product space `E` to the unit sphere in `E`. -/
def stereoInvFun (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) : sphere (0 : E) 1 :=
  ⟨stereoInvFunAux v (w : E), stereoInvFunAux_mem hv w.2⟩
#align stereo_inv_fun stereoInvFun

@[simp]
theorem stereoInvFun_apply (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) :
    (stereoInvFun hv w : E) = (‖w‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v) :=
  rfl
#align stereo_inv_fun_apply stereoInvFun_apply

theorem stereoInvFun_ne_north_pole (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) :
    stereoInvFun hv w ≠ (⟨v, by simp [hv]⟩ : sphere (0 : E) 1) := by
                                -- 🎉 no goals
  refine' Subtype.ne_of_val_ne _
  -- ⊢ ↑(stereoInvFun hv w) ≠ ↑{ val := v, property := (_ : v ∈ sphere 0 1) }
  rw [← inner_lt_one_iff_real_of_norm_one _ hv]
  -- ⊢ inner (↑(stereoInvFun hv w)) v < 1
  · have hw : ⟪v, w⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
    -- ⊢ inner (↑(stereoInvFun hv w)) v < 1
    have hw' : (‖(w : E)‖ ^ 2 + 4)⁻¹ * (‖(w : E)‖ ^ 2 - 4) < 1 := by
      refine' (inv_mul_lt_iff' _).mpr _
      · nlinarith
      linarith
    simpa [real_inner_comm, inner_add_right, inner_smul_right, real_inner_self_eq_norm_mul_norm, hw,
      hv] using hw'
  · simpa using stereoInvFunAux_mem hv w.2
    -- 🎉 no goals
#align stereo_inv_fun_ne_north_pole stereoInvFun_ne_north_pole

theorem continuous_stereoInvFun (hv : ‖v‖ = 1) : Continuous (stereoInvFun hv) :=
  continuous_induced_rng.2 (contDiff_stereoInvFunAux.continuous.comp continuous_subtype_val)
#align continuous_stereo_inv_fun continuous_stereoInvFun

theorem stereo_left_inv (hv : ‖v‖ = 1) {x : sphere (0 : E) 1} (hx : (x : E) ≠ v) :
    stereoInvFun hv (stereoToFun v x) = x := by
  ext
  -- ⊢ ↑(stereoInvFun hv (stereoToFun v ↑x)) = ↑x
  simp only [stereoToFun_apply, stereoInvFun_apply, smul_add]
  -- ⊢ (‖(2 / (1 - ↑(↑(innerSL ℝ) v) ↑x)) • ↑(orthogonalProjection (Submodule.span  …
  -- name two frequently-occuring quantities and write down their basic properties
  set a : ℝ := innerSL _ v x
  -- ⊢ (‖(2 / (1 - a)) • ↑(orthogonalProjection (Submodule.span ℝ {v})ᗮ) ↑x‖ ^ 2 +  …
  set y := orthogonalProjection (ℝ ∙ v)ᗮ x
  -- ⊢ (‖(2 / (1 - a)) • y‖ ^ 2 + 4)⁻¹ • ↑(4 • (2 / (1 - a)) • y) + (‖(2 / (1 - a)) …
  have split : ↑x = a • v + ↑y := by
    convert (orthogonalProjection_add_orthogonalProjection_orthogonal (ℝ ∙ v) x).symm
    exact (orthogonalProjection_unit_singleton ℝ hv x).symm
  have hvy : ⟪v, y⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.2
  -- ⊢ (‖(2 / (1 - a)) • y‖ ^ 2 + 4)⁻¹ • ↑(4 • (2 / (1 - a)) • y) + (‖(2 / (1 - a)) …
  have pythag : 1 = a ^ 2 + ‖y‖ ^ 2 := by
    have hvy' : ⟪a • v, y⟫_ℝ = 0 := by simp only [inner_smul_left, hvy, mul_zero]
    convert norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hvy' using 2
    -- Porting note: was simp [← split] but wasn't finding `norm_eq_of_mem_sphere`
    · simp only [norm_eq_of_mem_sphere, Nat.cast_one, mul_one, ← split]
    · simp [norm_smul, hv, ← sq, sq_abs]
    · exact sq _
  -- Porting note : added to work around cancel_denoms and nlinarith failures
  have duh : ‖y.val‖ ^ 2 = 1 - a ^ 2 := by
    rw [←Submodule.coe_norm, pythag]; ring
  -- two facts which will be helpful for clearing denominators in the main calculation
  have ha : 1 - a ≠ 0 := by
    have : a < 1 := (inner_lt_one_iff_real_of_norm_one hv (by simp)).mpr hx.symm
    linarith
  -- the core of the problem is these two algebraic identities:
  have h₁ : (2 ^ 2 / (1 - a) ^ 2 * ‖y‖ ^ 2 + 4)⁻¹ * 4 * (2 / (1 - a)) = 1 := by
    -- Porting note: used to be `field_simp; simp only [Submodule.coe_norm] at *; nlinarith`
    -- but cancel_denoms does not seem to be working and
    -- nlinarith cannot close the goal even if it did
    -- clear_value because field_simp does zeta-reduction (by design?) and is annoying
    clear_value a y
    field_simp
    rw [duh]
    ring
  have h₂ : (2 ^ 2 / (1 - a) ^ 2 * ‖y‖ ^ 2 + 4)⁻¹ * (2 ^ 2 / (1 - a) ^ 2 * ‖y‖ ^ 2 - 4) = a := by
    -- Porting note: field_simp is not behaving as in ml3
    -- see porting note above; previous proof used trans and was comparably complicated
    clear_value a y
    field_simp
    rw [duh]
    ring
  convert
    congr_arg₂ Add.add (congr_arg (fun t => t • (y : E)) h₁) (congr_arg (fun t => t • v) h₂) using 1
  · simp [inner_add_right, inner_smul_right, hvy, real_inner_self_eq_norm_mul_norm, hv, mul_smul,
      mul_pow, Real.norm_eq_abs, sq_abs, norm_smul]
    -- Porting note: used to be simp only [split, add_comm] but get maxRec errors
    · rw [split, add_comm]
      -- ⊢ (2 ^ 2 / (1 - inner v (a • v + ↑y)) ^ 2 * ‖a • v + ↑y - ↑(↑(orthogonalProjec …
      ac_rfl
      -- 🎉 no goals
  -- Porting note: this branch did not exit in ml3
  · rw [split, add_comm]
    -- ⊢ ↑y + a • v = Add.add ((fun t => t • ↑y) 1) ((fun t => t • v) a)
    congr!
    -- ⊢ ↑y = (fun t => t • ↑y) 1
    dsimp
    -- ⊢ ↑(↑(orthogonalProjection (Submodule.span ℝ {v})ᗮ) ↑x) = 1 • ↑(↑(orthogonalPr …
    rw [one_smul]
    -- 🎉 no goals
#align stereo_left_inv stereo_left_inv

theorem stereo_right_inv (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) : stereoToFun v (stereoInvFun hv w) = w := by
  have : 2 / (1 - (‖(w : E)‖ ^ 2 + 4)⁻¹ * (‖(w : E)‖ ^ 2 - 4)) * (‖(w : E)‖ ^ 2 + 4)⁻¹ * 4 = 1 := by
    field_simp; ring
  convert congr_arg (· • w) this
  -- ⊢ stereoToFun v ↑(stereoInvFun hv w) = (↑2 / (↑1 - (‖↑w‖ ^ 2 + 4)⁻¹ * (‖↑w‖ ^  …
  · have h₁ : orthogonalProjection (ℝ ∙ v)ᗮ v = 0 :=
      orthogonalProjection_orthogonalComplement_singleton_eq_zero v
    -- Porting note: was innerSL _ and now just inner
    have h₃ : inner v w = (0 : ℝ) := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
    -- ⊢ stereoToFun v ↑(stereoInvFun hv w) = (↑2 / (↑1 - (‖↑w‖ ^ 2 + 4)⁻¹ * (‖↑w‖ ^  …
    -- Porting note: was innerSL _ and now just inner
    have h₄ : inner v v = (1 : ℝ) := by simp [real_inner_self_eq_norm_mul_norm, hv]
    -- ⊢ stereoToFun v ↑(stereoInvFun hv w) = (↑2 / (↑1 - (‖↑w‖ ^ 2 + 4)⁻¹ * (‖↑w‖ ^  …
    simp [h₁, h₃, h₄, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, mul_smul]
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align stereo_right_inv stereo_right_inv

/-- Stereographic projection from the unit sphere in `E`, centred at a unit vector `v` in `E`; this
is the version as a local homeomorphism. -/
def stereographic (hv : ‖v‖ = 1) : LocalHomeomorph (sphere (0 : E) 1) (ℝ ∙ v)ᗮ where
  toFun := stereoToFun v ∘ (↑)
  invFun := stereoInvFun hv
  source := {⟨v, by simp [hv]⟩}ᶜ
                    -- 🎉 no goals
  target := Set.univ
  map_source' := by simp
                    -- 🎉 no goals
  map_target' {w} _ := fun h => (stereoInvFun_ne_north_pole hv w) (Set.eq_of_mem_singleton h)
  left_inv' x hx := stereo_left_inv hv fun h => hx (by
    rw [←h] at hv
    -- ⊢ x ∈ {{ val := v, property := ?m.687107 }}
    apply Subtype.ext
    -- ⊢ ↑x = ↑{ val := v, property := ?m.687107 }
    dsimp
    -- ⊢ ↑x = v
    exact h)
    -- 🎉 no goals
  right_inv' w _ := stereo_right_inv hv w
  open_source := isOpen_compl_singleton
  open_target := isOpen_univ
  continuous_toFun :=
    continuousOn_stereoToFun.comp continuous_subtype_val.continuousOn fun w h => by
      dsimp
      -- ⊢ ¬inner v ↑w = 1
      exact
        h ∘ Subtype.ext ∘ Eq.symm ∘ (inner_eq_one_iff_of_norm_one hv (by simp)).mp
  continuous_invFun := (continuous_stereoInvFun hv).continuousOn
#align stereographic stereographic

theorem stereographic_apply (hv : ‖v‖ = 1) (x : sphere (0 : E) 1) :
    stereographic hv x = (2 / ((1 : ℝ) - inner v x)) • orthogonalProjection (ℝ ∙ v)ᗮ x :=
  rfl
#align stereographic_apply stereographic_apply

@[simp]
theorem stereographic_source (hv : ‖v‖ = 1) : (stereographic hv).source = {⟨v, by simp [hv]⟩}ᶜ :=
                                                                                  -- 🎉 no goals
  rfl
#align stereographic_source stereographic_source

@[simp]
theorem stereographic_target (hv : ‖v‖ = 1) : (stereographic hv).target = Set.univ :=
  rfl
#align stereographic_target stereographic_target

@[simp]
theorem stereographic_apply_neg (v : sphere (0 : E) 1) :
    stereographic (norm_eq_of_mem_sphere v) (-v) = 0 := by
  simp [stereographic_apply, orthogonalProjection_orthogonalComplement_singleton_eq_zero]
  -- 🎉 no goals
#align stereographic_apply_neg stereographic_apply_neg

@[simp]
theorem stereographic_neg_apply (v : sphere (0 : E) 1) :
    stereographic (norm_eq_of_mem_sphere (-v)) v = 0 := by
  convert stereographic_apply_neg (-v)
  -- ⊢ v = - -v
  ext1
  -- ⊢ ↑v = ↑(- -v)
  simp
  -- 🎉 no goals
#align stereographic_neg_apply stereographic_neg_apply

end StereographicProjection

section ChartedSpace

/-!
### Charted space structure on the sphere

In this section we construct a charted space structure on the unit sphere in a finite-dimensional
real inner product space `E`; that is, we show that it is locally homeomorphic to the Euclidean
space of dimension one less than `E`.

The restriction to finite dimension is for convenience.  The most natural `charted_space`
structure for the sphere uses the stereographic projection from the antipodes of a point as the
canonical chart at this point.  However, the codomain of the stereographic projection constructed
in the previous section is `(ℝ ∙ v)ᗮ`, the orthogonal complement of the vector `v` in `E` which is
the "north pole" of the projection, so a priori these charts all have different codomains.

So it is necessary to prove that these codomains are all continuously linearly equivalent to a
fixed normed space.  This could be proved in general by a simple case of Gram-Schmidt
orthogonalization, but in the finite-dimensional case it follows more easily by dimension-counting.
-/

-- Porting note: unnecessary in Lean 3
private theorem findim (n : ℕ) [Fact (finrank ℝ E = n + 1)] : FiniteDimensional ℝ E :=
  fact_finiteDimensional_of_finrank_eq_succ n

/-- Variant of the stereographic projection, for the sphere in an `n + 1`-dimensional inner product
space `E`.  This version has codomain the Euclidean space of dimension `n`, and is obtained by
composing the original sterographic projection (`stereographic`) with an arbitrary linear isometry
from `(ℝ ∙ v)ᗮ` to the Euclidean space. -/
def stereographic' (n : ℕ) [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    LocalHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n)) :=
  stereographic (norm_eq_of_mem_sphere v) ≫ₕ
    (OrthonormalBasis.fromOrthogonalSpanSingleton n
            (ne_zero_of_mem_unit_sphere v)).repr.toHomeomorph.toLocalHomeomorph
#align stereographic' stereographic'

@[simp]
theorem stereographic'_source {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    (stereographic' n v).source = {v}ᶜ := by simp [stereographic']
                                             -- 🎉 no goals
#align stereographic'_source stereographic'_source

@[simp]
theorem stereographic'_target {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    (stereographic' n v).target = Set.univ := by simp [stereographic']
                                                 -- 🎉 no goals
#align stereographic'_target stereographic'_target

/-- The unit sphere in an `n + 1`-dimensional inner product space `E` is a charted space
modelled on the Euclidean space of dimension `n`. -/
instance chartedSpace {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (sphere (0 : E) 1) where
  atlas := {f | ∃ v : sphere (0 : E) 1, f = stereographic' n v}
  chartAt v := stereographic' n (-v)
  mem_chart_source v := by simpa using ne_neg_of_mem_unit_sphere ℝ v
                           -- 🎉 no goals
  chart_mem_atlas v := ⟨-v, rfl⟩

end ChartedSpace

section SmoothManifold

theorem sphere_ext_iff (u v : sphere (0 : E) 1) : u = v ↔ ⟪(u : E), v⟫_ℝ = 1 := by
  simp [Subtype.ext_iff, inner_eq_one_iff_of_norm_one]
  -- 🎉 no goals
#align sphere_ext_iff sphere_ext_iff

theorem stereographic'_symm_apply {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1)
    (x : EuclideanSpace ℝ (Fin n)) :
    ((stereographic' n v).symm x : E) =
      let U : (ℝ ∙ (v : E))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
        (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr
      (‖(U.symm x : E)‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • (U.symm x : E) +
        (‖(U.symm x : E)‖ ^ 2 + 4)⁻¹ • (‖(U.symm x : E)‖ ^ 2 - 4) • v.val :=
  by simp [real_inner_comm, stereographic, stereographic', ← Submodule.coe_norm]
     -- 🎉 no goals
#align stereographic'_symm_apply stereographic'_symm_apply

/-! ### Smooth manifold structure on the sphere -/

/-- The unit sphere in an `n + 1`-dimensional inner product space `E` is a smooth manifold,
modelled on the Euclidean space of dimension `n`. -/
instance smoothMfldWithCorners {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
    SmoothManifoldWithCorners (𝓡 n) (sphere (0 : E) 1) :=
  smoothManifoldWithCorners_of_contDiffOn (𝓡 n) (sphere (0 : E) 1)
    (by
      rintro _ _ ⟨v, rfl⟩ ⟨v', rfl⟩
      -- ⊢ ContDiffOn ℝ ⊤ (↑𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∘ ↑(LocalHomeomorph.symm (st …
      let U :=
        (-- Removed type ascription, and this helped for some reason with timeout issues?
            OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
            n (ne_zero_of_mem_unit_sphere v)).repr
      let U' :=
        (-- Removed type ascription, and this helped for some reason with timeout issues?
            OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
            n (ne_zero_of_mem_unit_sphere v')).repr
      -- Porting note: trouble synth instances
      have := findim (E := E) n
      -- ⊢ ContDiffOn ℝ ⊤ (↑𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∘ ↑(LocalHomeomorph.symm (st …
      have H₁ := U'.contDiff.comp_contDiffOn contDiffOn_stereoToFun
      -- ⊢ ContDiffOn ℝ ⊤ (↑𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∘ ↑(LocalHomeomorph.symm (st …
      -- Porting note: need to help with implicit variables again
      have H₂ := (contDiff_stereoInvFunAux (v := v.val)|>.comp
        (ℝ ∙ (v : E))ᗮ.subtypeL.contDiff).comp U.symm.contDiff
      convert H₁.comp' (H₂.contDiffOn : ContDiffOn ℝ ⊤ _ Set.univ) using 1
      -- ⊢ ↑(ModelWithCorners.symm 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ⁻¹' (LocalHomeomorph …
      -- -- squeezed from `ext, simp [sphere_ext_iff, stereographic'_symm_apply, real_inner_comm]`
      simp only [LocalHomeomorph.trans_toLocalEquiv, LocalHomeomorph.symm_toLocalEquiv,
        LocalEquiv.trans_source, LocalEquiv.symm_source, stereographic'_target,
        stereographic'_source]
      simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
        Set.range_id, Set.inter_univ, Set.univ_inter, Set.compl_singleton_eq, Set.preimage_setOf_eq]
      simp only [id.def, comp_apply, Submodule.subtypeL_apply, LocalHomeomorph.coe_coe_symm,
        innerSL_apply, Ne.def, sphere_ext_iff, real_inner_comm (v' : E)]
      rfl)
      -- 🎉 no goals

/-- The inclusion map (i.e., `coe`) from the sphere in `E` to `E` is smooth.  -/
theorem contMDiff_coe_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ ((↑) : sphere (0 : E) 1 → E) := by
  -- Porting note: trouble with filling these implicit variables in the instance
  have := smoothMfldWithCorners (E := E) (n := n)
  -- ⊢ ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ⊤ Subtype.val
  rw [contMDiff_iff]
  -- ⊢ Continuous Subtype.val ∧ ∀ (x : { x // x ∈ sphere 0 1 }) (y : E), ContDiffOn …
  constructor
  -- ⊢ Continuous Subtype.val
  · exact continuous_subtype_val
    -- 🎉 no goals
  · intro v _
    -- ⊢ ContDiffOn ℝ ⊤ (↑(extChartAt 𝓘(ℝ, E) y✝) ∘ Subtype.val ∘ ↑(LocalEquiv.symm ( …
    let U : _ ≃ₗᵢ[ℝ] _ :=
      (-- Again, partially removing type ascription...
          OrthonormalBasis.fromOrthogonalSpanSingleton
          n (ne_zero_of_mem_unit_sphere (-v))).repr
    exact
      ((contDiff_stereoInvFunAux.comp (ℝ ∙ (-v : E))ᗮ.subtypeL.contDiff).comp
          U.symm.contDiff).contDiffOn
#align cont_mdiff_coe_sphere contMDiff_coe_sphere

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]

/-- If a `cont_mdiff` function `f : M → E`, where `M` is some manifold, takes values in the
sphere, then it restricts to a `cont_mdiff` function from `M` to the sphere. -/
theorem ContMDiff.codRestrict_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)] {m : ℕ∞} {f : M → E}
    (hf : ContMDiff I 𝓘(ℝ, E) m f) (hf' : ∀ x, f x ∈ sphere (0 : E) 1) :
    ContMDiff I (𝓡 n) m (Set.codRestrict _ _ hf' : M → sphere (0 : E) 1) := by
  rw [contMDiff_iff_target]
  -- ⊢ Continuous (Set.codRestrict (fun x => f x) (sphere 0 1) hf') ∧ ∀ (y : ↑(sphe …
  refine' ⟨continuous_induced_rng.2 hf.continuous, _⟩
  -- ⊢ ∀ (y : ↑(sphere 0 1)), ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) m (↑(ext …
  intro v
  -- ⊢ ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) m (↑(extChartAt 𝓘(ℝ, EuclideanS …
  let U : _ ≃ₗᵢ[ℝ] _ :=
    (-- Again, partially removing type ascription... Weird that this helps!
        OrthonormalBasis.fromOrthogonalSpanSingleton
        n (ne_zero_of_mem_unit_sphere (-v))).repr
  have h : ContDiffOn ℝ ⊤ _ Set.univ := U.contDiff.contDiffOn
  -- ⊢ ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) m (↑(extChartAt 𝓘(ℝ, EuclideanS …
  have H₁ := (h.comp' contDiffOn_stereoToFun).contMDiffOn
  -- ⊢ ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) m (↑(extChartAt 𝓘(ℝ, EuclideanS …
  have H₂ : ContMDiffOn _ _ _ _ Set.univ := hf.contMDiffOn
  -- ⊢ ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) m (↑(extChartAt 𝓘(ℝ, EuclideanS …
  convert (H₁.of_le le_top).comp' H₂ using 1
  -- ⊢ Set.codRestrict (fun x => f x) (sphere 0 1) hf' ⁻¹' (extChartAt 𝓘(ℝ, Euclide …
  ext x
  -- ⊢ x ∈ Set.codRestrict (fun x => f x) (sphere 0 1) hf' ⁻¹' (extChartAt 𝓘(ℝ, Euc …
  have hfxv : f x = -↑v ↔ ⟪f x, -↑v⟫_ℝ = 1 := by
    have hfx : ‖f x‖ = 1 := by simpa using hf' x
    rw [inner_eq_one_iff_of_norm_one hfx]
    exact norm_eq_of_mem_sphere (-v)
  -- Porting note: unfold more
  dsimp [chartAt, Set.codRestrict, ChartedSpace.chartAt]
  -- ⊢ x ∈ (fun x => { val := f x, property := (_ : f x ∈ sphere 0 1) }) ⁻¹' (stere …
  simp [not_iff_not, Subtype.ext_iff, hfxv, real_inner_comm]
  -- 🎉 no goals
#align cont_mdiff.cod_restrict_sphere ContMDiff.codRestrict_sphere

/-- The antipodal map is smooth. -/
theorem contMDiff_neg_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
    ContMDiff (𝓡 n) (𝓡 n) ∞ fun x : sphere (0 : E) 1 => -x := by
  -- this doesn't elaborate well in term mode
  apply ContMDiff.codRestrict_sphere
  -- ⊢ ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ⊤ fun x => -↑x
  apply contDiff_neg.contMDiff.comp _
  -- ⊢ ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ⊤ fun x => ↑x
  exact contMDiff_coe_sphere
  -- 🎉 no goals
#align cont_mdiff_neg_sphere contMDiff_neg_sphere

/-- Consider the differential of the inclusion of the sphere in `E` at the point `v` as a continuous
linear map from `TangentSpace (𝓡 n) v` to `E`.  The range of this map is the orthogonal complement
of `v` in `E`.

Note that there is an abuse here of the defeq between `E` and the tangent space to `E` at `(v:E`).
In general this defeq is not canonical, but in this case (the tangent space of a vector space) it is
canonical. -/
theorem range_mfderiv_coe_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    LinearMap.range (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) v :
    TangentSpace (𝓡 n) v →L[ℝ] E) = (ℝ ∙ (v : E))ᗮ := by
  rw [((contMDiff_coe_sphere v).mdifferentiableAt le_top).mfderiv]
  -- ⊢ LinearMap.range (fderivWithin ℝ (writtenInExtChartAt 𝓘(ℝ, EuclideanSpace ℝ ( …
  dsimp [chartAt]
  -- ⊢ LinearMap.range (fderivWithin ℝ (↑(ChartedSpace.chartAt ↑v) ∘ Subtype.val ∘  …
  -- rw [LinearIsometryEquiv.toHomeomorph_symm]
  -- rw [←LinearIsometryEquiv.coe_toHomeomorph]
  simp only [chartAt, stereographic_neg_apply, fderivWithin_univ,
    LinearIsometryEquiv.toHomeomorph_symm, LinearIsometryEquiv.coe_toHomeomorph,
    LinearIsometryEquiv.map_zero, mfld_simps]
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
    (ne_zero_of_mem_unit_sphere (-v))).repr
  -- Porting note: this `suffices` was a `change`
  suffices :
    LinearMap.range (fderiv ℝ ((stereoInvFunAux (-v : E) ∘ (↑)) ∘ U.symm) 0) = (ℝ ∙ (v : E))ᗮ
  · convert this using 3
    -- ⊢ ↑(ChartedSpace.chartAt v) v = 0
    show stereographic' n (-v) v = 0
    -- ⊢ ↑(stereographic' n (-v)) v = 0
    dsimp [stereographic']
    -- ⊢ ↑(OrthonormalBasis.fromOrthogonalSpanSingleton n (_ : ↑(-v) ≠ 0)).repr (↑(st …
    simp only [AddEquivClass.map_eq_zero_iff]
    -- ⊢ ↑(stereographic (_ : ‖↑(-v)‖ = 1)) v = 0
    apply stereographic_neg_apply
    -- 🎉 no goals
  have :
    HasFDerivAt (stereoInvFunAux (-v : E) ∘ (Subtype.val : (ℝ ∙ (↑(-v) : E))ᗮ → E))
      (ℝ ∙ (↑(-v) : E))ᗮ.subtypeL (U.symm 0) := by
    convert hasFDerivAt_stereoInvFunAux_comp_coe (-v : E)
    simp
  convert congrArg LinearMap.range (this.comp 0 U.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv
  -- ⊢ (Submodule.span ℝ {↑v})ᗮ = LinearMap.range (ContinuousLinearMap.comp (Submod …
  symm
  -- ⊢ LinearMap.range (ContinuousLinearMap.comp (Submodule.subtypeL (Submodule.spa …
  convert
    (U.symm : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ (↑(-v) : E))ᗮ).range_comp
      (ℝ ∙ (↑(-v) : E))ᗮ.subtype using 1
  simp only [Submodule.range_subtype, coe_neg_sphere]
  -- ⊢ (Submodule.span ℝ {↑v})ᗮ = (Submodule.span ℝ {-↑v})ᗮ
  congr 1
  -- ⊢ Submodule.span ℝ {↑v} = Submodule.span ℝ {-↑v}
  -- we must show `submodule.span ℝ {v} = submodule.span ℝ {-v}`
  apply Submodule.span_eq_span
  -- ⊢ {↑v} ⊆ ↑(Submodule.span ℝ {-↑v})
  · simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    -- ⊢ ↑v ∈ Submodule.span ℝ {-↑v}
    rw [← Submodule.neg_mem_iff]
    -- ⊢ -↑v ∈ Submodule.span ℝ {-↑v}
    exact Submodule.mem_span_singleton_self (-v : E)
    -- 🎉 no goals
  · simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    -- ⊢ -↑v ∈ Submodule.span ℝ {↑v}
    rw [Submodule.neg_mem_iff]
    -- ⊢ ↑v ∈ Submodule.span ℝ {↑v}
    exact Submodule.mem_span_singleton_self (v:E)
    -- 🎉 no goals
#align range_mfderiv_coe_sphere range_mfderiv_coe_sphere

/-- Consider the differential of the inclusion of the sphere in `E` at the point `v` as a continuous
linear map from `TangentSpace (𝓡 n) v` to `E`.  This map is injective. -/
theorem mfderiv_coe_sphere_injective {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) v) := by
  rw [((contMDiff_coe_sphere v).mdifferentiableAt le_top).mfderiv]
  -- ⊢ Injective ↑(fderivWithin ℝ (writtenInExtChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n …
  simp only [chartAt, stereographic', stereographic_neg_apply, fderivWithin_univ,
    LinearIsometryEquiv.toHomeomorph_symm, LinearIsometryEquiv.coe_toHomeomorph,
    LinearIsometryEquiv.map_zero, mfld_simps]
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton
      (𝕜 := ℝ) n (ne_zero_of_mem_unit_sphere (-v))).repr
  suffices : Injective (fderiv ℝ ((stereoInvFunAux (-v : E) ∘ (↑)) ∘ U.symm) 0)
  -- ⊢ Injective ↑(fderiv ℝ (Subtype.val ∘ ↑(LocalHomeomorph.symm (ChartedSpace.cha …
  · convert this using 3
    -- ⊢ ↑(ChartedSpace.chartAt v) v = 0
    show stereographic' n (-v) v = 0
    -- ⊢ ↑(stereographic' n (-v)) v = 0
    dsimp [stereographic']
    -- ⊢ ↑(OrthonormalBasis.fromOrthogonalSpanSingleton n (_ : ↑(-v) ≠ 0)).repr (↑(st …
    simp only [AddEquivClass.map_eq_zero_iff]
    -- ⊢ ↑(stereographic (_ : ‖↑(-v)‖ = 1)) v = 0
    apply stereographic_neg_apply
    -- 🎉 no goals
  have :
    HasFDerivAt (stereoInvFunAux (-v : E) ∘ (Subtype.val : (ℝ ∙ (↑(-v) : E))ᗮ → E))
      (ℝ ∙ (↑(-v) : E))ᗮ.subtypeL (U.symm 0) := by
    convert hasFDerivAt_stereoInvFunAux_comp_coe (-v : E)
    simp
  have := congr_arg FunLike.coe <| (this.comp 0 U.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv
  -- ⊢ Injective ↑(fderiv ℝ ((stereoInvFunAux (-↑v) ∘ Subtype.val) ∘ ↑(LinearIsomet …
  refine Eq.subst this.symm ?_
  -- ⊢ Injective ↑(ContinuousLinearMap.comp (Submodule.subtypeL (Submodule.span ℝ { …
  rw [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe]
  -- ⊢ Injective (↑(Submodule.subtypeL (Submodule.span ℝ {↑(-v)})ᗮ) ∘ ↑(LinearIsome …
  simpa using Subtype.coe_injective
  -- 🎉 no goals
#align mfderiv_coe_sphere_injective mfderiv_coe_sphere_injective

end SmoothManifold

section circle

open Complex

-- Porting note: 1+1 = 2 except when synthing instances
theorem finrank_real_complex_fact' : Fact (finrank ℝ ℂ = 1 + 1) :=
  finrank_real_complex_fact

attribute [local instance] finrank_real_complex_fact'

/-- The unit circle in `ℂ` is a charted space modelled on `EuclideanSpace ℝ (Fin 1)`.  This
follows by definition from the corresponding result for `Metric.Sphere`. -/
instance : ChartedSpace (EuclideanSpace ℝ (Fin 1)) circle :=
  chartedSpace

instance : SmoothManifoldWithCorners (𝓡 1) circle :=
  smoothMfldWithCorners (E := ℂ)

/-- The unit circle in `ℂ` is a Lie group. -/
instance : LieGroup (𝓡 1) circle where
  smooth_mul := by
    apply ContMDiff.codRestrict_sphere
    -- ⊢ ContMDiff (ModelWithCorners.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, Euclide …
    let c : circle → ℂ := (↑)
    -- ⊢ ContMDiff (ModelWithCorners.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, Euclide …
    have h₂ : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞ fun z : ℂ × ℂ => z.fst * z.snd := by
      rw [contMDiff_iff]
      exact ⟨continuous_mul, fun x y => contDiff_mul.contDiffOn⟩
    -- Porting note: needed to fill in first 3 arguments or could not figure out typeclasses
    suffices h₁ : ContMDiff ((𝓡 1).prod (𝓡 1)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ⊤ (Prod.map c c)
    -- ⊢ ContMDiff (ModelWithCorners.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, Euclide …
    · apply h₂.comp h₁
      -- 🎉 no goals
    · apply ContMDiff.prod_map <;>
      -- ⊢ ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ⊤ c
      exact contMDiff_coe_sphere
      -- 🎉 no goals
      -- 🎉 no goals
  smooth_inv := by
    apply ContMDiff.codRestrict_sphere
    -- ⊢ ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ⊤ fun a => (↑a)⁻¹
    simp only [← coe_inv_circle, coe_inv_circle_eq_conj]
    -- ⊢ ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ⊤ fun a => ↑(starRingEnd ℂ) …
    exact Complex.conjCle.contDiff.contMDiff.comp contMDiff_coe_sphere
    -- 🎉 no goals

/-- The map `fun t ↦ exp (t * I)` from `ℝ` to the unit circle in `ℂ` is smooth. -/
theorem contMDiff_expMapCircle : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ expMapCircle :=
  (contDiff_exp.comp (contDiff_id.smul contDiff_const)).contMDiff.codRestrict_sphere _
#align cont_mdiff_exp_map_circle contMDiff_expMapCircle

end circle
