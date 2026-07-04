/-
# The Mercator Connection on S²

We define a connection on the domain of the spherical coordinate chart by
declaring two vectors to be parallel if they make the same angle to a given
meridian. This is equivalent to declaring the orthonormal frame
{e₁, e₂} = {∂_θ, (1/sinθ) ∂_φ} to be parallel.

NOTE ON THE DOMAIN. A single spherical chart with φ ∈ (-π, π) covers
`sphSource` = S² minus the *closed anti-meridian* {x ≤ 0, y = 0}, which is
strictly smaller than `S2_open` = S² minus the poles.

The connection has:
  - Γ^φ_{θφ} = cotθ  in the coordinate frame {∂_θ, ∂_φ}
  - All other Christoffel symbols zero
  - Torsion T(e₁, e₂) = cotθ · e₂ ≠ 0
  - Geodesics are rhumb lines (straight lines in the Mercator chart)

## The honest coframe and frame

Unlike an earlier draft that used the *constant model frame*
`{EuclideanSpace.single 0 1, EuclideanSpace.single 1 1}` (the "fake" 1-forms),
here `dθ`, `dφ`, `Xθ`, `Xφ` (defined in `MercatorGeom`) are the genuine
differential-geometric coframe/frame of the spherical chart:

* `dθ x = mfderiv θ_coord x`, `dφ x = mfderiv φ_coord x` are honest smooth
  sections of the cotangent bundle (`θ_coord = arccos z`, `φ_coord = arg`);
* `Xθ`, `Xφ` are the push-forwards of the standard basis under the chart inverse
  `sphInv`, forming the dual frame (`frame_dual`).

Because these are honest smooth objects, `mercatorCov` satisfies the *upstream*
`IsCovariantDerivativeOn` from
`Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic`, whose
`add`/`leibniz` axioms are stated for sections that are differentiable **as
bundled sections of the tangent bundle** (`MDiffAt (T% σ)`).  The bridge from
that bundled differentiability to differentiability of the chart components
`y ↦ dθ y (σ y)`, `y ↦ dφ y (σ y)` is `mdifferentiableAt_mfderiv_apply`
(pairing a smooth cotangent section with a differentiable vector field).

References: Dominic Steinitz, "Mercator: A Connection with Torsion"
  https://idontgetoutmuch.wordpress.com/2016/11/24/mercator-a-connection-with-torsion/
-/

import Mathlib
import Mathlib.Geometry.Manifold.Algebra.MercatorGeom

open scoped BigOperators Real Nat Pointwise Manifold ContDiff
set_option maxRecDepth 4000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Real Set Metric Manifold Bundle

noncomputable section

/-! ## The exterior derivative of a scalar function

`extDerivFun f x` is the genuine manifold (Fréchet) derivative of `f : S² → ℝ`
at `x`, viewed as a linear functional on the tangent space. Additivity is
upstream (`extDerivFun_add`); the product rule is not in Mathlib in this form. -/

/-- Product rule at the level of `extDerivFun`. -/
lemma extDerivFun_mul {g f : S2 → ℝ} {x : S2}
    (hg : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) g x)
    (hf : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) f x) :
    extDerivFun (g * f) x = g x • extDerivFun (I := 𝓡 2) f x + f x • extDerivFun g x := by
  exact (hg.hasMFDerivAt.mul hf.hasMFDerivAt).mfderiv

/-! ## The component-differentiability bridge

From differentiability of the bundled tangent section `T% σ` we obtain
differentiability of the chart components `y ↦ dθ y (σ y)` and `y ↦ dφ y (σ y)`,
using that `dθ`, `dφ` are the differentials of the smooth functions `θ_coord`,
`φ_coord` together with `mdifferentiableAt_mfderiv_apply`. -/

/-- The θ-component of a bundle-differentiable section is differentiable. -/
lemma mdiffAt_dθcomp {σ : Π y : S2, TangentSpace (𝓡 2) y} {x : S2}
    (hσ : MDifferentiableAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (fun y ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin 2)) y (σ y)) x)
    (hx : x ∈ S2_open) :
    MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (fun y ↦ dθ y (σ y)) x :=
  mdifferentiableAt_mfderiv_apply θ_coord σ x ((θ_coord_contMDiffAt hx).of_le (by norm_num)) hσ

/-- The φ-component of a bundle-differentiable section is differentiable. -/
lemma mdiffAt_dφcomp {σ : Π y : S2, TangentSpace (𝓡 2) y} {x : S2}
    (hσ : MDifferentiableAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (fun y ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin 2)) y (σ y)) x)
    (hx : x ∈ sphSource) :
    MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (fun y ↦ dφ y (σ y)) x :=
  mdifferentiableAt_mfderiv_apply φ_coord σ x
    ((φ_coord_contMDiffAt hx).of_le (by decide)) hσ

/-! ## The Mercator connection

The connection map sends a section σ of TS² to a section of Hom(TS², TS²).
At a point x ∈ sphSource with coordinate θ = θ_coord x:

  (∇σ)(x)(v) = dθ(v) · ∂θ-derivative + ... + cotθ · σ^φ(x) · v^θ · ∂_φ

This is the unique connection with Γ^φ_{θφ} = cotθ and all other Γ = 0. -/

open Classical in
noncomputable def mercatorCov :
    (Π x : S2, TangentSpace (𝓡 2) x) →
    (Π x : S2, TangentSpace (𝓡 2) x →L[ℝ] TangentSpace (𝓡 2) x) :=
  fun σ x =>
    if _hx : x ∈ sphSource then
      let θ    := θ_coord x
      let cotθ := Real.cos θ / Real.sin θ
      let Dσθ : TangentSpace (𝓡 2) x →L[ℝ] ℝ := extDerivFun (fun y ↦ dθ y (σ y)) x
      let Dσφ : TangentSpace (𝓡 2) x →L[ℝ] ℝ := extDerivFun (fun y ↦ dφ y (σ y)) x
      let Γ : TangentSpace (𝓡 2) x →L[ℝ] ℝ := (cotθ * dφ x (σ x)) • dθ x
      (Dσθ.smulRight (Xθ x)) + ((Dσφ + Γ).smulRight (Xφ x))
    else 0

lemma mercatorCov_apply (σ : Π y : S2, TangentSpace (𝓡 2) y) {x : S2} (hx : x ∈ sphSource) :
    mercatorCov σ x =
      (extDerivFun (fun y ↦ dθ y (σ y)) x).smulRight (Xθ x) +
      (extDerivFun (fun y ↦ dφ y (σ y)) x +
        ((Real.cos (θ_coord x) / Real.sin (θ_coord x)) * dφ x (σ x)) • dθ x).smulRight
        (Xφ x) := by
  simp only [mercatorCov, dif_pos hx]

/-! ## Verification: the upstream `IsCovariantDerivativeOn`

We check the two axioms:
  1. add:     ∇(σ + σ') = ∇σ + ∇σ'
  2. leibniz: ∇(f · σ) = f · ∇σ + df ⊗ σ

Both reduce to standard properties of `mfderiv`/`extDerivFun` plus linearity of
the correction, using `frame_dual` and the component-differentiability bridge. -/

theorem mercatorCov_isCovariantDerivativeOn :
    IsCovariantDerivativeOn (EuclideanSpace ℝ (Fin 2)) mercatorCov sphSource where
  add := by
    intro σ σ' x hσ hσ' hx
    have hxo := sphSource_subset_S2_open hx
    have hcθ : (fun y ↦ dθ y ((σ + σ') y)) =
        (fun y ↦ dθ y (σ y)) + fun y ↦ dθ y (σ' y) := by
      funext y; simp only [Pi.add_apply, map_add]
    have hcφ : (fun y ↦ dφ y ((σ + σ') y)) =
        (fun y ↦ dφ y (σ y)) + fun y ↦ dφ y (σ' y) := by
      funext y; simp only [Pi.add_apply, map_add]
    rw [mercatorCov_apply (σ + σ') hx, mercatorCov_apply σ hx, mercatorCov_apply σ' hx,
      hcθ, hcφ,
      extDerivFun_add (mdiffAt_dθcomp hσ hxo) (mdiffAt_dθcomp hσ' hxo),
      extDerivFun_add (mdiffAt_dφcomp hσ hx) (mdiffAt_dφcomp hσ' hx)]
    simp only [Pi.add_apply, map_add]
    ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    module
  leibniz := by
    intro σ g x hσ hg hx
    have hxo := sphSource_subset_S2_open hx
    have hcθ : (fun y ↦ dθ y ((g • σ) y)) = g * fun y ↦ dθ y (σ y) := by
      funext y; simp only [Pi.smul_apply', Pi.mul_apply, map_smul, smul_eq_mul]
    have hcφ : (fun y ↦ dφ y ((g • σ) y)) = g * fun y ↦ dφ y (σ y) := by
      funext y; simp only [Pi.smul_apply', Pi.mul_apply, map_smul, smul_eq_mul]
    rw [mercatorCov_apply (g • σ) hx, mercatorCov_apply σ hx, hcθ, hcφ,
      extDerivFun_mul hg (mdiffAt_dθcomp hσ hxo),
      extDerivFun_mul hg (mdiffAt_dφcomp hσ hx)]
    simp only [Pi.smul_apply', map_smul, smul_eq_mul]
    set a := dθ x (σ x) with ha
    set b := dφ x (σ x) with hb
    have hdual : σ x = a • Xθ x + b • Xφ x := by
      rw [ha, hb]; exact (frame_dual hx (σ x)).symm
    rw [hdual]
    ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    module

end
