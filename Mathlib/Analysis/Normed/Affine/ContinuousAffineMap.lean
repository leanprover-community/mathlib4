/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace

/-!
# Continuous affine maps between normed spaces.

This file develops the theory of continuous affine maps between affine spaces modelled on normed
spaces.

In the particular case that the affine spaces are just normed vector spaces `V`, `W`, we define a
norm on the space of continuous affine maps by defining the norm of `f : V →ᴬ[𝕜] W` to be
`‖f‖ = max ‖f 0‖ ‖f.cont_linear‖`. This is chosen so that we have a linear isometry:
`(V →ᴬ[𝕜] W) ≃ₗᵢ[𝕜] W × (V →L[𝕜] W)`.

The abstract picture is that for an affine space `P` modelled on a vector space `V`, together with
a vector space `W`, there is an exact sequence of `𝕜`-modules: `0 → C → A → L → 0` where `C`, `A`
are the spaces of constant and affine maps `P → W` and `L` is the space of linear maps `V → W`.

Any choice of a base point in `P` corresponds to a splitting of this sequence so in particular if we
take `P = V`, using `0 : V` as the base point provides a splitting, and we prove this is an
isometric decomposition.

On the other hand, choosing a base point breaks the affine invariance so the norm fails to be
submultiplicative: for a composition of maps, we have only `‖f.comp g‖ ≤ ‖f‖ * ‖g‖ + ‖f 0‖`.

## Main definitions:

* `ContinuousAffineMap.contLinear`
* `ContinuousAffineMap.hasNorm`
* `ContinuousAffineMap.norm_comp_le`
* `ContinuousAffineMap.toConstProdContinuousLinearMap`

-/


namespace ContinuousAffineMap

variable {𝕜 R V W W₂ P Q Q₂ : Type*}
variable [NormedAddCommGroup V] [MetricSpace P] [NormedAddTorsor V P]
variable [NormedAddCommGroup W] [MetricSpace Q] [NormedAddTorsor W Q]
variable [NormedAddCommGroup W₂] [MetricSpace Q₂] [NormedAddTorsor W₂ Q₂]
variable [NormedField R] [NormedSpace R V] [NormedSpace R W] [NormedSpace R W₂]
variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W] [NormedSpace 𝕜 W₂]

/-- The linear map underlying a continuous affine map is continuous. -/
def contLinear (f : P →ᴬ[R] Q) : V →L[R] W :=
  { f.linear with
    toFun := f.linear
    cont := by rw [AffineMap.continuous_linear_iff]; exact f.cont }

@[simp]
theorem coe_contLinear (f : P →ᴬ[R] Q) : (f.contLinear : V → W) = f.linear :=
  rfl

@[simp]
theorem coe_contLinear_eq_linear (f : P →ᴬ[R] Q) :
    (f.contLinear : V →ₗ[R] W) = (f : P →ᵃ[R] Q).linear := by ext; rfl

@[simp]
theorem coe_mk_const_linear_eq_linear (f : P →ᵃ[R] Q) (h) :
    ((⟨f, h⟩ : P →ᴬ[R] Q).contLinear : V → W) = f.linear :=
  rfl

theorem coe_linear_eq_coe_contLinear (f : P →ᴬ[R] Q) :
    ((f : P →ᵃ[R] Q).linear : V → W) = (⇑f.contLinear : V → W) :=
  rfl

@[simp]
theorem comp_contLinear (f : P →ᴬ[R] Q) (g : Q →ᴬ[R] Q₂) :
    (g.comp f).contLinear = g.contLinear.comp f.contLinear :=
  rfl

@[simp]
theorem map_vadd (f : P →ᴬ[R] Q) (p : P) (v : V) : f (v +ᵥ p) = f.contLinear v +ᵥ f p :=
  f.map_vadd' p v

@[simp]
theorem contLinear_map_vsub (f : P →ᴬ[R] Q) (p₁ p₂ : P) : f.contLinear (p₁ -ᵥ p₂) = f p₁ -ᵥ f p₂ :=
  f.toAffineMap.linearMap_vsub p₁ p₂

@[simp]
theorem const_contLinear (q : Q) : (const R P q).contLinear = 0 :=
  rfl

theorem contLinear_eq_zero_iff_exists_const (f : P →ᴬ[R] Q) :
    f.contLinear = 0 ↔ ∃ q, f = const R P q := by
  have h₁ : f.contLinear = 0 ↔ (f : P →ᵃ[R] Q).linear = 0 := by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> ext
    · rw [← coe_contLinear_eq_linear, h]; rfl
    · rw [← coe_linear_eq_coe_contLinear, h]; rfl
  have h₂ : ∀ q : Q, f = const R P q ↔ (f : P →ᵃ[R] Q) = AffineMap.const R P q := by
    intro q
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> ext
    · rw [h]; rfl
    · rw [← coe_toAffineMap, h, AffineMap.const_apply, coe_const, Function.const_apply]
  simp_rw [h₁, h₂]
  exact (f : P →ᵃ[R] Q).linear_eq_zero_iff_exists_const

@[simp]
theorem to_affine_map_contLinear (f : V →L[R] W) : f.toContinuousAffineMap.contLinear = f := by
  ext
  rfl

@[simp]
theorem zero_contLinear : (0 : P →ᴬ[R] W).contLinear = 0 :=
  rfl

@[simp]
theorem add_contLinear (f g : P →ᴬ[R] W) : (f + g).contLinear = f.contLinear + g.contLinear :=
  rfl

@[simp]
theorem sub_contLinear (f g : P →ᴬ[R] W) : (f - g).contLinear = f.contLinear - g.contLinear :=
  rfl

@[simp]
theorem neg_contLinear (f : P →ᴬ[R] W) : (-f).contLinear = -f.contLinear :=
  rfl

@[simp]
theorem smul_contLinear (t : R) (f : P →ᴬ[R] W) : (t • f).contLinear = t • f.contLinear :=
  rfl

theorem decomp (f : V →ᴬ[R] W) : (f : V → W) = f.contLinear + Function.const V (f 0) := by
  rcases f with ⟨f, h⟩
  rw [coe_mk_const_linear_eq_linear, coe_mk, f.decomp, Pi.add_apply, LinearMap.map_zero, zero_add,
    ← Function.const_def]

/-- The space of continuous affine maps from `P` to `Q` is an affine space over the space of
continuous affine maps from `P` to `W`. -/
instance : AddTorsor (P →ᴬ[R] W) (P →ᴬ[R] Q) where
  vadd f g := { __ := f.toAffineMap +ᵥ g.toAffineMap, cont := f.cont.vadd g.cont }
  zero_vadd _ := ext fun _ ↦ zero_vadd _ _
  add_vadd _ _ _ := ext fun _ ↦ add_vadd _ _ _
  vsub f g := { __ := f.toAffineMap -ᵥ g.toAffineMap, cont := f.cont.vsub g.cont }
  vsub_vadd' _ _ := ext fun _ ↦ vsub_vadd _ _
  vadd_vsub' _ _ := ext fun _ ↦ vadd_vsub _ _

@[simp] lemma vadd_apply (f : P →ᴬ[R] W) (g : P →ᴬ[R] Q) (p : P) : (f +ᵥ g) p = f p +ᵥ g p :=
  rfl

@[simp] lemma vsub_apply (f g : P →ᴬ[R] Q) (p : P) : (f -ᵥ g) p = f p -ᵥ g p :=
  rfl

@[simp] lemma vadd_toAffineMap (f : P →ᴬ[R] W) (g : P →ᴬ[R] Q) :
    (f +ᵥ g).toAffineMap = f.toAffineMap +ᵥ g.toAffineMap :=
  rfl

@[simp] lemma vsub_toAffineMap (f g : P →ᴬ[R] Q) :
    (f -ᵥ g).toAffineMap = f.toAffineMap -ᵥ g.toAffineMap :=
  rfl

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
      _ ≤ ‖f.contLinear‖ * ‖g 0‖ + ‖f 0‖ :=
        ((norm_add_le _ _).trans (add_le_add_right (f.contLinear.le_opNorm _) _))
      _ ≤ ‖f‖ * ‖g‖ + ‖f 0‖ :=
        add_le_add_right
          (mul_le_mul f.norm_contLinear_le g.norm_image_zero_le (norm_nonneg _) (norm_nonneg _)) _
  · calc
      ‖(f.comp g).contLinear‖ ≤ ‖f.contLinear‖ * ‖g.contLinear‖ :=
        (g.comp_contLinear f).symm ▸ f.contLinear.opNorm_comp_le _
      _ ≤ ‖f‖ * ‖g‖ :=
        (mul_le_mul f.norm_contLinear_le g.norm_contLinear_le (norm_nonneg _) (norm_nonneg _))
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
