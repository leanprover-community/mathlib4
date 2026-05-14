/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Topology.MetricSpace.TransferInstance
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Norm on the continuous affine maps between normed vector spaces.

We define a norm on the space of continuous affine maps between normed vector spaces by defining the
norm of `f : V →ᴬ[𝕜] W` to be `‖f‖ = max ‖f 0‖ ‖f.cont_linear‖`. This is chosen so that we have a
linear isometry: `(V →ᴬ[𝕜] W) ≃ₗᵢ[𝕜] W × (V →L[𝕜] W)`.

The abstract picture is that for an affine space `P` modelled on a vector space `V`, together with
a vector space `W`, there is an exact sequence of `𝕜`-modules: `0 → C → A → L → 0` where `C`, `A`
are the spaces of constant and affine maps `P → W` and `L` is the space of linear maps `V → W`.

Any choice of a base point in `P` corresponds to a splitting of this sequence so in particular if we
take `P = V`, using `0 : V` as the base point provides a splitting, and we prove this is an
isometric decomposition.

On the other hand, choosing a base point breaks the affine invariance so the norm fails to be
submultiplicative: for a composition of maps, we have only `‖f.comp g‖ ≤ ‖f‖ * ‖g‖ + ‖f 0‖`.

## Main definitions:

* `ContinuousAffineMap.hasNorm`
* `ContinuousAffineMap.norm_comp_le`
* `ContinuousAffineMap.toConstProdContinuousLinearMap`

-/

@[expose] public section


namespace ContinuousAffineMap

variable {𝕜 R V W W₂ Q : Type*}

section Seminormed

variable [SeminormedAddCommGroup V] [SeminormedAddCommGroup W] [SeminormedAddCommGroup W₂]
variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W] [NormedSpace 𝕜 W₂]
variable [PseudoMetricSpace Q] [NormedAddTorsor W Q]

variable (f : V →ᴬ[𝕜] W)

/-- Note that unlike the operator norm for linear maps, this norm is _not_ submultiplicative:
we do _not_ necessarily have `‖f.comp g‖ ≤ ‖f‖ * ‖g‖`. See `norm_comp_le` for what we can say. -/
noncomputable instance hasNorm : Norm (V →ᴬ[𝕜] W) :=
  ⟨fun f => max ‖f 0‖ ‖f.contLinear‖⟩

theorem norm_def : ‖f‖ = max ‖f 0‖ ‖f.contLinear‖ :=
  rfl

theorem norm_contLinear_le : ‖f.contLinear‖ ≤ ‖f‖ :=
  le_max_right _ _

theorem norm_image_zero_le : ‖f 0‖ ≤ ‖f‖ :=
  le_max_left _ _

@[simp]
theorem norm_eq (h : f 0 = 0) : ‖f‖ = ‖f.contLinear‖ :=
  calc
    ‖f‖ = max ‖f 0‖ ‖f.contLinear‖ := by rw [norm_def]
    _ = max 0 ‖f.contLinear‖ := by rw [h, norm_zero]
    _ = ‖f.contLinear‖ := max_eq_right (norm_nonneg _)

noncomputable instance : PseudoMetricSpace (V →ᴬ[𝕜] Q) :=
  (decompEquiv 𝕜 V Q).pseudometricSpace

noncomputable instance : SeminormedAddCommGroup (V →ᴬ[𝕜] W) where
  dist_eq _ _ := dist_eq_norm_neg_add (E := W × (V →L[𝕜] W)) _ _

noncomputable instance : NormedAddTorsor (V →ᴬ[𝕜] W) (V →ᴬ[𝕜] Q) where
  dist_eq_norm' _ _ := dist_eq_norm_vsub (P := Q × (V →L[𝕜] W)) _ _ _

noncomputable instance : NormedSpace 𝕜 (V →ᴬ[𝕜] W) where
  norm_smul_le t f := norm_smul_le t (f 0, f.contLinear)

theorem norm_comp_le (g : W₂ →ᴬ[𝕜] V) : ‖f.comp g‖ ≤ ‖f‖ * ‖g‖ + ‖f 0‖ := by
  rw [norm_def, max_le_iff]
  constructor
  · calc
      ‖f.comp g 0‖ = ‖f (g 0)‖ := by simp
      _ = ‖f.contLinear (g 0) + f 0‖ := by rw [f.decomp]; simp
      _ ≤ ‖f.contLinear‖ * ‖g 0‖ + ‖f 0‖ := by grw [norm_add_le, f.contLinear.le_opNorm]
      _ ≤ ‖f‖ * ‖g‖ + ‖f 0‖ := by grw [f.norm_contLinear_le, g.norm_image_zero_le]
  · calc
      ‖(f.comp g).contLinear‖ ≤ ‖f.contLinear‖ * ‖g.contLinear‖ :=
        (g.comp_contLinear f).symm ▸ f.contLinear.opNorm_comp_le _
      _ ≤ ‖f‖ * ‖g‖ := by grw [f.norm_contLinear_le, g.norm_contLinear_le]
      _ ≤ ‖f‖ * ‖g‖ + ‖f 0‖ := by rw [le_add_iff_nonneg_right]; apply norm_nonneg

variable (𝕜 R V W) [Ring R] [Module R W] [ContinuousConstSMul R W] [SMulCommClass 𝕜 R W]

/-- The space of affine maps between two normed spaces is linearly isometric to the product of the
codomain with the space of linear maps, by taking the value of the affine map at `(0 : V)` and the
linear part. -/
def decompLinearIsometryEquiv : (V →ᴬ[𝕜] W) ≃ₗᵢ[R] W × (V →L[𝕜] W) where
  __ := decompLinearEquiv 𝕜 R V W
  norm_map' _ := rfl

@[simp]
theorem fst_decompLinearIsometryEquiv (f : V →ᴬ[𝕜] W) :
    (decompLinearIsometryEquiv 𝕜 R V W f).1 = f 0 :=
  rfl

@[simp]
theorem snd_decompLinearIsometryEquiv (f : V →ᴬ[𝕜] W) :
    (decompLinearIsometryEquiv 𝕜 R V W f).2 = f.contLinear :=
  rfl

@[simp]
theorem decompLinearIsometryEquiv_symm_apply (p : W × (V →L[𝕜] W)) (x : V) :
    (decompLinearIsometryEquiv 𝕜 R V W).symm p x = p.2 x + p.1 :=
  rfl

@[simp]
theorem decompLinearIsometryEquiv_symm_contLinear (p : W × (V →L[𝕜] W)) :
    ((decompLinearIsometryEquiv 𝕜 R V W).symm p).contLinear = p.2 := by
  rw [decompLinearIsometryEquiv, ← LinearIsometryEquiv.coe_symm_toLinearEquiv,
    decompLinearEquiv_symm_contLinear]

@[deprecated decompLinearIsometryEquiv (since := "2026-03-03"),
  inherit_doc decompLinearIsometryEquiv]
abbrev toConstProdContinuousLinearMap := decompLinearIsometryEquiv 𝕜 𝕜 V W

set_option linter.deprecated false in
@[deprecated fst_decompLinearIsometryEquiv (since := "2026-03-03")]
theorem toConstProdContinuousLinearMap_fst (f : V →ᴬ[𝕜] W) :
    (toConstProdContinuousLinearMap 𝕜 V W f).fst = f 0 :=
  rfl

set_option linter.deprecated false in
@[deprecated snd_decompLinearIsometryEquiv (since := "2026-03-03")]
theorem toConstProdContinuousLinearMap_snd (f : V →ᴬ[𝕜] W) :
    (toConstProdContinuousLinearMap 𝕜 V W f).snd = f.contLinear :=
  rfl

end Seminormed

section Normed

variable [NormedAddCommGroup V] [NormedAddCommGroup W]
variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W]
variable [MetricSpace Q] [NormedAddTorsor W Q]

noncomputable instance : MetricSpace (V →ᴬ[𝕜] Q) :=
  (decompEquiv 𝕜 V Q).metricSpace

noncomputable instance : NormedAddCommGroup (V →ᴬ[𝕜] W) where
  __ : SeminormedAddCommGroup (V →ᴬ[𝕜] W) := inferInstance
  __ : MetricSpace (V →ᴬ[𝕜] W) := inferInstance

end Normed

end ContinuousAffineMap
