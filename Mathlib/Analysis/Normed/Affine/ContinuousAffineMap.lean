/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Group.AddTorsor

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


namespace ContinuousAffineMap

variable {𝕜 V W W₂ : Type*}
variable [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedAddCommGroup W₂]
variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W] [NormedSpace 𝕜 W₂]

section NormedSpaceStructure

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

noncomputable instance : NormedAddCommGroup (V →ᴬ[𝕜] W) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun f => max ‖f 0‖ ‖f.contLinear‖
      map_zero' := by simp [(ContinuousAffineMap.zero_apply)]
      neg' := fun f => by
        simp [(ContinuousAffineMap.neg_apply)]
      add_le' := fun f g => by
        simp only [coe_add, max_le_iff, Pi.add_apply, add_contLinear]
        exact
          ⟨(norm_add_le _ _).trans (add_le_add (le_max_left _ _) (le_max_left _ _)),
            (norm_add_le _ _).trans (add_le_add (le_max_right _ _) (le_max_right _ _))⟩
      eq_zero_of_map_eq_zero' := fun f h₀ => by
        rcases max_eq_iff.mp h₀ with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> rw [h₁] at h₂
        · rw [norm_le_zero_iff, contLinear_eq_zero_iff_exists_const] at h₂
          obtain ⟨q, rfl⟩ := h₂
          simp only [norm_eq_zero, coe_const, Function.const_apply] at h₁
          rw [h₁]
          rfl
        · rw [norm_eq_zero, contLinear_eq_zero_iff_exists_const] at h₁
          obtain ⟨q, rfl⟩ := h₁
          simp only [norm_le_zero_iff, coe_const, Function.const_apply] at h₂
          rw [h₂]
          rfl }

noncomputable instance : NormedSpace 𝕜 (V →ᴬ[𝕜] W) where
  norm_smul_le t f := by
    simp only [norm_def, coe_smul, Pi.smul_apply, norm_smul, smul_contLinear,
      ← mul_max_of_nonneg _ _ (norm_nonneg t), le_refl]

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

variable (𝕜 V W)

/-- The space of affine maps between two normed spaces is linearly isometric to the product of the
codomain with the space of linear maps, by taking the value of the affine map at `(0 : V)` and the
linear part. -/
noncomputable def toConstProdContinuousLinearMap : (V →ᴬ[𝕜] W) ≃ₗᵢ[𝕜] W × (V →L[𝕜] W) where
  toFun f := ⟨f 0, f.contLinear⟩
  invFun p := p.2.toContinuousAffineMap + const 𝕜 V p.1
  left_inv f := by
    ext
    rw [f.decomp]
    simp only [coe_add, ContinuousLinearMap.coe_toContinuousAffineMap, Pi.add_apply, coe_const]
  right_inv := by rintro ⟨v, f⟩; ext <;> simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

@[simp]
theorem toConstProdContinuousLinearMap_fst (f : V →ᴬ[𝕜] W) :
    (toConstProdContinuousLinearMap 𝕜 V W f).fst = f 0 :=
  rfl

@[simp]
theorem toConstProdContinuousLinearMap_snd (f : V →ᴬ[𝕜] W) :
    (toConstProdContinuousLinearMap 𝕜 V W f).snd = f.contLinear :=
  rfl

end NormedSpaceStructure

end ContinuousAffineMap
