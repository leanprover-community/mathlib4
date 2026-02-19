/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Tensor products and linear maps

This file defines `TensorProduct.map`, the `R`-linear map from `M ⊗ N` to `M₂ ⊗ N₂` defined by
a pair of linear (or more generally semilinear) maps `f : M → M₂` and `g : N → N₂`.

The notation `f ⊗ₘ g` is available for this map.

We also define one-sided versions `lTensor` and `rTensor`.

## Tags

bilinear, tensor, tensor product
-/

@[expose] public section

section Semiring

variable {R R₂ R₃ R' R'' : Type*}
variable [CommSemiring R] [CommSemiring R₂] [CommSemiring R₃] [Monoid R'] [Semiring R'']
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variable {A M N P Q S : Type*}
variable {M₂ M₃ N₂ N₃ P' P₂ P₃ Q' Q₂ Q₃ : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [AddCommMonoid S]
variable [AddCommMonoid P'] [AddCommMonoid Q']
variable [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P₂] [AddCommMonoid Q₂]
variable [AddCommMonoid M₃] [AddCommMonoid N₃] [AddCommMonoid P₃] [AddCommMonoid Q₃]
variable [DistribMulAction R' M]
variable [Module R'' M]
variable [Module R M] [Module R N] [Module R S]
variable [Module R P'] [Module R Q']
variable [Module R₂ M₂] [Module R₂ N₂] [Module R₂ P₂] [Module R₂ Q₂]
variable [Module R₃ M₃] [Module R₃ N₃] [Module R₃ P₃] [Module R₃ Q₃]

variable (M N)

namespace TensorProduct

variable [Module R P] [Module R Q]

variable {M N}

open LinearMap

/-- The tensor product of a pair of linear maps between modules. -/
def map (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) : M ⊗[R] N →ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂ :=
  lift <| comp (compl₂ (mk _ _ _) g) f

@[inherit_doc] scoped[RingTheory.LinearMap] infix:70 " ⊗ₘ " => TensorProduct.map

@[simp]
theorem map_tmul (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) (m : M) (n : N) :
    map f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  rfl

/-- Given semilinear maps `f : M → P`, `g : N → Q`, if we identify `M ⊗ N` with `N ⊗ M` and `P ⊗ Q`
with `Q ⊗ P`, then this lemma states that `f ⊗ g = g ⊗ f`. -/
lemma map_comp_comm_eq (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) :
    map f g ∘ₛₗ (TensorProduct.comm R N M).toLinearMap =
      (TensorProduct.comm R₂ N₂ M₂).toLinearMap ∘ₛₗ map g f :=
  ext rfl

lemma map_comm (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) (x : N ⊗[R] M) :
    map f g (TensorProduct.comm R N M x) = TensorProduct.comm R₂ N₂ M₂ (map g f x) :=
  DFunLike.congr_fun (map_comp_comm_eq _ _) _

theorem range_map (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    range (map f g) = .map₂ (mk R _ _) (range f) (range g) := by
  simp_rw [← Submodule.map_top, Submodule.map₂_map_map, ← map₂_mk_top_top_eq_top,
    Submodule.map_map₂]
  rfl

theorem range_map_eq_span_tmul (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    range (map f g) = Submodule.span R { t | ∃ m n, f m ⊗ₜ g n = t } := by
  simp only [← Submodule.map_top, ← span_tmul_eq_top, Submodule.map_span]
  congr; ext t
  simp

@[deprecated (since := "2025-09-07")] alias map_range_eq_span_tmul := range_map_eq_span_tmul

/-- Given submodules `p ⊆ P` and `q ⊆ Q`, this is the natural map: `p ⊗ q → P ⊗ Q`. -/
@[simp]
def mapIncl (p : Submodule R P) (q : Submodule R Q) : p ⊗[R] q →ₗ[R] P ⊗[R] Q :=
  map p.subtype q.subtype

lemma range_mapIncl (p : Submodule R P) (q : Submodule R Q) :
    LinearMap.range (mapIncl p q) = .map₂ (mk R _ _) p q := by
  simp_rw [mapIncl, range_map, Submodule.range_subtype]

theorem map₂_eq_range_lift_comp_mapIncl (f : P →ₗ[R] Q →ₗ[R] M)
    (p : Submodule R P) (q : Submodule R Q) :
    Submodule.map₂ f p q = LinearMap.range (lift f ∘ₗ mapIncl p q) := by
  simp_rw [LinearMap.range_comp, range_mapIncl, Submodule.map_map₂]
  rfl

section

variable {P' Q' : Type*}
variable [AddCommMonoid P'] [Module R P']
variable [AddCommMonoid Q'] [Module R Q']
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

theorem map_comp (f₂ : M₂ →ₛₗ[σ₂₃] M₃) (g₂ : N₂ →ₛₗ[σ₂₃] N₃)
    (f₁ : M →ₛₗ[σ₁₂] M₂) (g₁ : N →ₛₗ[σ₁₂] N₂) :
    map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁) = (map f₂ g₂) ∘ₛₗ (map f₁ g₁) := ext' fun _ _ => rfl

theorem map_map (f₂ : M₂ →ₛₗ[σ₂₃] M₃) (g₂ : N₂ →ₛₗ[σ₂₃] N₃)
    (f₁ : M →ₛₗ[σ₁₂] M₂) (g₁ : N →ₛₗ[σ₁₂] N₂) (x : M ⊗[R] N) :
    map f₂ g₂ (map f₁ g₁ x) = map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁) x :=
  DFunLike.congr_fun (map_comp ..).symm x

lemma range_map_mono [Module R M₂] [Module R M₃] [Module R N₂] [Module R N₃]
    {a : M →ₗ[R] M₂} {b : M₃ →ₗ[R] M₂} {c : N →ₗ[R] N₂} {d : N₃ →ₗ[R] N₂}
    (hab : range a ≤ range b) (hcd : range c ≤ range d) : range (map a c) ≤ range (map b d) := by
  simp_rw [range_map]
  exact Submodule.map₂_le_map₂ hab hcd

lemma range_mapIncl_mono {p p' : Submodule R P} {q q' : Submodule R Q} (hp : p ≤ p') (hq : q ≤ q') :
    LinearMap.range (mapIncl p q) ≤ LinearMap.range (mapIncl p' q') :=
  range_map_mono (by simpa) (by simpa)

theorem lift_comp_map (i : M₂ →ₛₗ[σ₂₃] N₂ →ₛₗ[σ₂₃] P₃) (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) :
    (lift i).comp (map f g) = lift ((i.comp f).compl₂ g) :=
  ext' fun _ _ => rfl

attribute [local ext high] ext

@[simp]
theorem map_id : map (id : M →ₗ[R] M) (id : N →ₗ[R] N) = .id := by
  ext
  simp only [mk_apply, id_coe, compr₂ₛₗ_apply, _root_.id, map_tmul]

@[simp]
protected theorem map_one : map (1 : M →ₗ[R] M) (1 : N →ₗ[R] N) = 1 :=
  map_id

protected theorem map_mul (f₁ f₂ : M →ₗ[R] M) (g₁ g₂ : N →ₗ[R] N) :
    map (f₁ * f₂) (g₁ * g₂) = map f₁ g₁ * map f₂ g₂ :=
  map_comp ..

@[simp]
protected theorem map_pow (f : M →ₗ[R] M) (g : N →ₗ[R] N) (n : ℕ) :
    map f g ^ n = map (f ^ n) (g ^ n) := by
  induction n with
  | zero => simp only [pow_zero, TensorProduct.map_one]
  | succ n ih => simp only [pow_succ', ih, TensorProduct.map_mul]

theorem map_add_left (f₁ f₂ : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) :
    map (f₁ + f₂) g = map f₁ g + map f₂ g := by
  ext
  simp only [add_tmul, compr₂ₛₗ_apply, mk_apply, map_tmul, add_apply]

theorem map_add_right (f : M →ₛₗ[σ₁₂] M₂) (g₁ g₂ : N →ₛₗ[σ₁₂] N₂) :
    map f (g₁ + g₂) = map f g₁ + map f g₂ := by
  ext
  simp only [tmul_add, compr₂ₛₗ_apply, mk_apply, map_tmul, add_apply]

theorem map_smul_left (r : R₂) (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) :
    map (r • f) g = r • map f g := by
  ext
  simp only [smul_tmul, compr₂ₛₗ_apply, mk_apply, map_tmul, smul_apply, tmul_smul]

theorem map_smul_right (r : R₂) (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) :
    map f (r • g) = r • map f g := by
  ext
  simp only [compr₂ₛₗ_apply, mk_apply, map_tmul, smul_apply, tmul_smul]

variable (M N P M₂ N₂ σ₁₂)

/-- The tensor product of a pair of semilinear maps between modules, bilinear in both maps. -/
def mapBilinear : (M →ₛₗ[σ₁₂] M₂) →ₗ[R₂] (N →ₛₗ[σ₁₂] N₂) →ₗ[R₂] M ⊗[R] N →ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂ :=
  LinearMap.mk₂ R₂ map map_add_left map_smul_left map_add_right map_smul_right

/-- The canonical linear map from `M₂ ⊗[R₂] (P →ₛₗ[σ₁₂] N₂)` to `P →ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂`. -/
def lTensorHomToHomLTensor : M₂ ⊗[R₂] (P →ₛₗ[σ₁₂] N₂) →ₗ[R₂] P →ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂ :=
  TensorProduct.lift (llcomp _ P N₂ _ ∘ₛₗ mk R₂ M₂ N₂)

/-- The canonical linear map from `(P →ₛₗ[σ₁₂] M₂) ⊗[R₂] N₂` to `P →ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂`. -/
def rTensorHomToHomRTensor : (P →ₛₗ[σ₁₂] M₂) ⊗[R₂] N₂ →ₗ[R₂] P →ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂ :=
  TensorProduct.lift (llcomp _ P M₂ _ ∘ₗ (mk R₂ M₂ N₂).flip).flip

/-- The linear map from `(M →ₛₗ[σ₁₂] M₂) ⊗ (N →ₛₗ[σ₁₂] N₂)` to `M ⊗ N →ₛₗ[σ₁₂] M₂ ⊗ N₂`
sending `f ⊗ₜ g` to `TensorProduct.map f g`, the tensor product of the two maps. -/
def homTensorHomMap : (M →ₛₗ[σ₁₂] M₂) ⊗[R₂] (N →ₛₗ[σ₁₂] N₂) →ₗ[R₂] M ⊗[R] N →ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂ :=
  lift (mapBilinear σ₁₂ M N M₂ N₂)

variable {M N P M₂ N₂ σ₁₂}

/--
This is a binary version of `TensorProduct.map`: Given a bilinear map `f : M ⟶ P ⟶ Q` and a
bilinear map `g : N ⟶ S ⟶ T`, if we think `f` and `g` as semilinear maps with two inputs, then
`map₂ f g` is a bilinear map taking two inputs `M ⊗ N → P ⊗ S → Q ⊗ S` defined by
`map₂ f g (m ⊗ n) (p ⊗ s) = f m p ⊗ g n s`.

Mathematically, `TensorProduct.map₂` is defined as the composition
`M ⊗ N -map→ Hom(P, Q) ⊗ Hom(S, T) -homTensorHomMap→ Hom(P ⊗ S, Q ⊗ T)`.
-/
def map₂ (f : M →ₛₗ[σ₁₃] M₂ →ₛₗ[σ₂₃] M₃) (g : N →ₛₗ[σ₁₃] N₂ →ₛₗ[σ₂₃] N₃) :
    M ⊗[R] N →ₛₗ[σ₁₃] M₂ ⊗[R₂] N₂ →ₛₗ[σ₂₃] M₃ ⊗[R₃] N₃ :=
  homTensorHomMap σ₂₃ _ _ _ _ ∘ₛₗ map f g

@[simp]
theorem mapBilinear_apply (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) :
    mapBilinear σ₁₂ M N M₂ N₂ f g = map f g :=
  rfl

@[simp]
theorem lTensorHomToHomLTensor_apply (m₂ : M₂) (f : P →ₛₗ[σ₁₂] N₂) (p : P) :
    lTensorHomToHomLTensor _ P M₂ N₂ (m₂ ⊗ₜ f) p = m₂ ⊗ₜ f p :=
  rfl

@[simp]
theorem rTensorHomToHomRTensor_apply (f : P →ₛₗ[σ₁₂] M₂) (n₂ : N₂) (p : P) :
    rTensorHomToHomRTensor _ P M₂ N₂ (f ⊗ₜ n₂) p = f p ⊗ₜ n₂ :=
  rfl

@[simp]
theorem homTensorHomMap_apply (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) :
    homTensorHomMap _ M N M₂ N₂ (f ⊗ₜ g) = map f g :=
  rfl

@[simp]
theorem map₂_apply_tmul (f : M →ₛₗ[σ₁₃] M₂ →ₛₗ[σ₂₃] M₃) (g : N →ₛₗ[σ₁₃] N₂ →ₛₗ[σ₂₃] N₃)
    (m : M) (n : N) :
    map₂ f g (m ⊗ₜ n) = map (f m) (g n) := rfl

@[simp]
theorem map_zero_left (g : N →ₛₗ[σ₁₂] N₂) : map (0 : M →ₛₗ[σ₁₂] M₂) g = 0 :=
  (mapBilinear _ M N M₂ N₂).map_zero₂ _

@[simp]
theorem map_zero_right (f : M →ₛₗ[σ₁₂] M₂) : map f (0 : N →ₛₗ[σ₁₂] N₂) = 0 :=
  (mapBilinear _ M N M₂ N₂ f).map_zero

end

variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/-- If `M` and `P` are semilinearly equivalent and `N` and `Q` are semilinearly equivalent
then `M ⊗ N` and `P ⊗ Q` are semilinearly equivalent. -/
def congr (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) : M ⊗[R] N ≃ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂ :=
  LinearEquiv.ofLinear (map f g) (map f.symm g.symm)
    (ext' fun m n => by simp)
    (ext' fun m n => by simp)

@[simp]
lemma toLinearMap_congr (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) :
    (congr f g).toLinearMap = map f g := rfl

@[simp]
theorem congr_tmul (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) (m : M) (n : N) :
    congr f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  rfl

@[simp]
theorem congr_symm_tmul (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) (p : M₂) (q : N₂) :
    (congr f g).symm (p ⊗ₜ q) = f.symm p ⊗ₜ g.symm q :=
  rfl

theorem congr_symm (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) :
    (congr f g).symm = congr f.symm g.symm := rfl

@[simp] theorem congr_refl_refl : congr (.refl R M) (.refl R N) = .refl R _ :=
  LinearEquiv.toLinearMap_injective <| ext' fun _ _ ↦ rfl

section congr_congr
variable {σ₃₂ : R₃ →+* R₂} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
  {σ₃₁ : R₃ →+* R} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
  (f₂ : M₂ ≃ₛₗ[σ₂₃] M₃) (g₂ : N₂ ≃ₛₗ[σ₂₃] N₃) (f₁ : M ≃ₛₗ[σ₁₂] M₂) (g₁ : N ≃ₛₗ[σ₁₂] N₂)

theorem congr_trans : congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (congr f₂ g₂) :=
  LinearEquiv.toLinearMap_injective <| map_comp _ _ _ _

theorem congr_congr (x : M ⊗[R] N) :
    congr f₂ g₂ (congr f₁ g₁ x) = congr (f₁.trans f₂) (g₁.trans g₂) x :=
  DFunLike.congr_fun (congr_trans ..).symm x

end congr_congr

theorem congr_mul (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (f' : M ≃ₗ[R] M) (g' : N ≃ₗ[R] N) :
    congr (f * f') (g * g') = congr f g * congr f' g' := congr_trans _ _ _ _

@[simp] theorem congr_pow (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (n : ℕ) :
    congr f g ^ n = congr (f ^ n) (g ^ n) := by
  induction n with
  | zero => exact congr_refl_refl.symm
  | succ n ih => simp_rw [pow_succ, ih, congr_mul]

@[simp] theorem congr_zpow (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (n : ℤ) :
    congr f g ^ n = congr (f ^ n) (g ^ n) := by
  cases n with
  | ofNat n => exact congr_pow _ _ _
  | negSucc n => simp_rw [zpow_negSucc, congr_pow]; exact congr_symm _ _

lemma map_bijective {f : M →ₗ[R] N} {g : P →ₗ[R] Q}
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (map f g) :=
  (TensorProduct.congr (.ofBijective f hf) (.ofBijective g hg)).bijective

universe u in
instance {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Small.{u} M] [Small.{u} N] : Small.{u} (M ⊗[R] N) :=
  ⟨_, ⟨(TensorProduct.congr
    (Shrink.linearEquiv R M) (Shrink.linearEquiv R N)).symm.toEquiv⟩⟩

end TensorProduct

open scoped TensorProduct

variable [Module R P] [Module R Q]

namespace LinearMap

variable {N}

/-- `LinearMap.lTensor M f : M ⊗ N →ₗ M ⊗ P` is the natural linear map
induced by `f : N →ₗ P`. -/
def lTensor (f : N →ₗ[R] P) : M ⊗[R] N →ₗ[R] M ⊗[R] P :=
  TensorProduct.map id f

/-- `LinearMap.rTensor M f : N ⊗ M →ₗ P ⊗ M` is the natural linear map
induced by `f : N →ₗ P`. -/
def rTensor (f : N →ₗ[R] P) : N ⊗[R] M →ₗ[R] P ⊗[R] M :=
  TensorProduct.map f id

variable (g : P →ₗ[R] Q) (f : N →ₗ[R] P)

theorem lTensor_def : f.lTensor M = TensorProduct.map LinearMap.id f := rfl

theorem rTensor_def : f.rTensor M = TensorProduct.map f LinearMap.id := rfl

@[simp]
theorem lTensor_tmul (m : M) (n : N) : f.lTensor M (m ⊗ₜ n) = m ⊗ₜ f n :=
  rfl

@[simp]
theorem rTensor_tmul (m : M) (n : N) : f.rTensor M (n ⊗ₜ m) = f n ⊗ₜ m :=
  rfl

@[simp]
theorem lTensor_comp_mk (m : M) :
    f.lTensor M ∘ₗ TensorProduct.mk R M N m = TensorProduct.mk R M P m ∘ₗ f :=
  rfl

@[simp]
theorem rTensor_comp_flip_mk (m : M) :
    f.rTensor M ∘ₗ (TensorProduct.mk R N M).flip m = (TensorProduct.mk R P M).flip m ∘ₗ f :=
  rfl

lemma comm_comp_rTensor_comp_comm_eq (g : N →ₗ[R] P) :
    TensorProduct.comm R P Q ∘ₗ rTensor Q g ∘ₗ TensorProduct.comm R Q N =
      lTensor Q g :=
  TensorProduct.ext rfl

lemma comm_comp_lTensor_comp_comm_eq (g : N →ₗ[R] P) :
    TensorProduct.comm R Q P ∘ₗ lTensor Q g ∘ₗ TensorProduct.comm R N Q =
      rTensor Q g :=
  TensorProduct.ext rfl

/-- Given a linear map `f : N → P`, `f ⊗ M` is injective if and only if `M ⊗ f` is injective. -/
theorem lTensor_inj_iff_rTensor_inj :
    Function.Injective (lTensor M f) ↔ Function.Injective (rTensor M f) := by
  simp [← comm_comp_rTensor_comp_comm_eq]

/-- Given a linear map `f : N → P`, `f ⊗ M` is surjective if and only if `M ⊗ f` is surjective. -/
theorem lTensor_surj_iff_rTensor_surj :
    Function.Surjective (lTensor M f) ↔ Function.Surjective (rTensor M f) := by
  simp [← comm_comp_rTensor_comp_comm_eq]

/-- Given a linear map `f : N → P`, `f ⊗ M` is bijective if and only if `M ⊗ f` is bijective. -/
theorem lTensor_bij_iff_rTensor_bij :
    Function.Bijective (lTensor M f) ↔ Function.Bijective (rTensor M f) := by
  simp [← comm_comp_rTensor_comp_comm_eq]

variable {M} in
theorem smul_lTensor {S : Type*} [CommSemiring S] [SMul R S] [Module S M] [IsScalarTower R S M]
    [SMulCommClass R S M] (s : S) (m : M ⊗[R] N) : s • (f.lTensor M) m = (f.lTensor M) (s • m) :=
  have h : s • (f.lTensor M) = f.lTensor M ∘ₗ (LinearMap.lsmul S (M ⊗[R] N) s).restrictScalars R :=
    TensorProduct.ext rfl
  congrFun (congrArg DFunLike.coe h) m

open TensorProduct

attribute [local ext high] TensorProduct.ext

/-- `lTensorHom M` is the natural linear map that sends a linear map `f : N →ₗ P` to `M ⊗ f`.

See also `Module.End.lTensorAlgHom`. -/
def lTensorHom : (N →ₗ[R] P) →ₗ[R] M ⊗[R] N →ₗ[R] M ⊗[R] P where
  toFun := lTensor M
  map_add' f g := by
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, add_apply, lTensor_tmul, tmul_add]
  map_smul' r f := by
    dsimp
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, tmul_smul, smul_apply, lTensor_tmul]

/-- `rTensorHom M` is the natural linear map that sends a linear map `f : N →ₗ P` to `f ⊗ M`.

See also `Module.End.rTensorAlgHom`. -/
def rTensorHom : (N →ₗ[R] P) →ₗ[R] N ⊗[R] M →ₗ[R] P ⊗[R] M where
  toFun f := f.rTensor M
  map_add' f g := by
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, add_apply, rTensor_tmul, add_tmul]
  map_smul' r f := by
    dsimp
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, smul_tmul, tmul_smul, smul_apply, rTensor_tmul]

@[simp]
theorem coe_lTensorHom : (lTensorHom M : (N →ₗ[R] P) → M ⊗[R] N →ₗ[R] M ⊗[R] P) = lTensor M :=
  rfl

@[simp]
theorem coe_rTensorHom : (rTensorHom M : (N →ₗ[R] P) → N ⊗[R] M →ₗ[R] P ⊗[R] M) = rTensor M :=
  rfl

@[simp]
theorem lTensor_add (f g : N →ₗ[R] P) : (f + g).lTensor M = f.lTensor M + g.lTensor M :=
  (lTensorHom M).map_add f g

@[simp]
theorem rTensor_add (f g : N →ₗ[R] P) : (f + g).rTensor M = f.rTensor M + g.rTensor M :=
  (rTensorHom M).map_add f g

@[simp]
theorem lTensor_zero : lTensor M (0 : N →ₗ[R] P) = 0 :=
  (lTensorHom M).map_zero

@[simp]
theorem rTensor_zero : rTensor M (0 : N →ₗ[R] P) = 0 :=
  (rTensorHom M).map_zero

@[simp]
theorem lTensor_smul (r : R) (f : N →ₗ[R] P) : (r • f).lTensor M = r • f.lTensor M :=
  (lTensorHom M).map_smul r f

@[simp]
theorem rTensor_smul (r : R) (f : N →ₗ[R] P) : (r • f).rTensor M = r • f.rTensor M :=
  (rTensorHom M).map_smul r f

theorem lTensor_comp : (g.comp f).lTensor M = (g.lTensor M).comp (f.lTensor M) := by
  ext m n
  simp only [compr₂ₛₗ_apply, mk_apply, comp_apply, lTensor_tmul]

theorem lTensor_comp_apply (x : M ⊗[R] N) :
    (g.comp f).lTensor M x = (g.lTensor M) ((f.lTensor M) x) := by rw [lTensor_comp, coe_comp]; rfl

theorem rTensor_comp : (g.comp f).rTensor M = (g.rTensor M).comp (f.rTensor M) := by
  ext m n
  simp only [compr₂ₛₗ_apply, mk_apply, comp_apply, rTensor_tmul]

theorem rTensor_comp_apply (x : N ⊗[R] M) :
    (g.comp f).rTensor M x = (g.rTensor M) ((f.rTensor M) x) := by rw [rTensor_comp, coe_comp]; rfl

theorem lTensor_mul (f g : Module.End R N) : (f * g).lTensor M = f.lTensor M * g.lTensor M :=
  lTensor_comp M f g

theorem rTensor_mul (f g : Module.End R N) : (f * g).rTensor M = f.rTensor M * g.rTensor M :=
  rTensor_comp M f g

variable (N)

@[simp]
theorem lTensor_id : (id : N →ₗ[R] N).lTensor M = id :=
  map_id

-- `simp` can prove this.
theorem lTensor_id_apply (x : M ⊗[R] N) : (LinearMap.id : N →ₗ[R] N).lTensor M x = x := by
  rw [lTensor_id, id_coe, _root_.id]

@[simp]
theorem rTensor_id : (id : N →ₗ[R] N).rTensor M = id :=
  map_id

-- `simp` can prove this.
theorem rTensor_id_apply (x : N ⊗[R] M) : (LinearMap.id : N →ₗ[R] N).rTensor M x = x := by
  rw [rTensor_id, id_coe, _root_.id]

@[simp]
theorem lTensor_smul_action (r : R) :
    (DistribSMul.toLinearMap R N r).lTensor M =
      DistribSMul.toLinearMap R (M ⊗[R] N) r :=
  (lTensor_smul M r LinearMap.id).trans (congrArg _ (lTensor_id M N))

@[simp]
theorem rTensor_smul_action (r : R) :
    (DistribSMul.toLinearMap R N r).rTensor M =
      DistribSMul.toLinearMap R (N ⊗[R] M) r :=
  (rTensor_smul M r LinearMap.id).trans (congrArg _ (rTensor_id M N))

variable {N}

@[simp]
theorem lTensor_comp_rTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (g.lTensor P).comp (f.rTensor N) = map f g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]

@[simp]
theorem rTensor_comp_lTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (f.rTensor Q).comp (g.lTensor M) = map f g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]

@[simp]
theorem map_comp_rTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (f' : S →ₗ[R] M) :
    (map f g).comp (f'.rTensor _) = map (f.comp f') g := by
  simp only [rTensor, ← map_comp, comp_id]

@[simp]
theorem map_rTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (f' : S →ₗ[R] M) (x : S ⊗[R] N) :
    map f g (f'.rTensor _ x) = map (f.comp f') g x :=
  LinearMap.congr_fun (map_comp_rTensor _ _ _ _) x

@[simp]
theorem map_comp_lTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (g' : S →ₗ[R] N) :
    (map f g).comp (g'.lTensor _) = map f (g.comp g') := by
  simp only [lTensor, ← map_comp, comp_id]

@[simp]
lemma map_lTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (g' : S →ₗ[R] N) (x : M ⊗[R] S) :
    map f g (g'.lTensor M x) = map f (g ∘ₗ g') x :=
  LinearMap.congr_fun (map_comp_lTensor _ _ _ _) x

@[simp]
theorem rTensor_comp_map (f' : P →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (f'.rTensor _).comp (map f g) = map (f'.comp f) g := by
  simp only [rTensor, ← map_comp, id_comp]

@[simp]
lemma rTensor_map (f' : P →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (x : M ⊗[R] N) :
    f'.rTensor Q (map f g x) = map (f' ∘ₗ f) g x :=
  LinearMap.congr_fun (rTensor_comp_map _ _ f g) x

@[simp]
theorem lTensor_comp_map (g' : Q →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (g'.lTensor _).comp (map f g) = map f (g'.comp g) := by
  simp only [lTensor, ← map_comp, id_comp]

@[simp]
lemma lTensor_map (g' : Q →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (x : M ⊗[R] N) :
    g'.lTensor P (map f g x) = map f (g' ∘ₗ g) x :=
  LinearMap.congr_fun (lTensor_comp_map _ _ f g) x

variable {M}

theorem lTensor_comp_comm (f : M →ₗ[R] P) :
    lTensor N f ∘ₗ TensorProduct.comm R M N = TensorProduct.comm R P N ∘ₗ rTensor N f :=
  TensorProduct.map_comp_comm_eq _ _

theorem rTensor_comp_comm (f : M →ₗ[R] P) :
    rTensor N f ∘ₗ TensorProduct.comm R N M = TensorProduct.comm R N P ∘ₗ lTensor N f :=
  TensorProduct.map_comp_comm_eq _ _

theorem lTensor_comm (f : M →ₗ[R] P) (x : M ⊗[R] N) :
    lTensor N f (TensorProduct.comm R M N x) = TensorProduct.comm R P N (rTensor N f x) :=
  congr($(LinearMap.lTensor_comp_comm f) _)

theorem rTensor_comm (f : M →ₗ[R] P) (x : N ⊗[R] M) :
    rTensor N f (TensorProduct.comm R N M x) = TensorProduct.comm R N P (lTensor N f x) :=
  congr($(LinearMap.rTensor_comp_comm f) _)

@[simp]
theorem rTensor_pow (f : M →ₗ[R] M) (n : ℕ) : f.rTensor N ^ n = (f ^ n).rTensor N := by
  have h := TensorProduct.map_pow f (id : N →ₗ[R] N) n
  rwa [Module.End.id_pow] at h

@[simp]
theorem lTensor_pow (f : N →ₗ[R] N) (n : ℕ) : f.lTensor M ^ n = (f ^ n).lTensor M := by
  have h := TensorProduct.map_pow (id : M →ₗ[R] M) f n
  rwa [Module.End.id_pow] at h

end LinearMap

namespace LinearEquiv

variable {N}

/-- `LinearEquiv.lTensor M f : M ⊗ N ≃ₗ M ⊗ P` is the natural linear equivalence
induced by `f : N ≃ₗ P`. -/
def lTensor (f : N ≃ₗ[R] P) : M ⊗[R] N ≃ₗ[R] M ⊗[R] P := TensorProduct.congr (refl R M) f

/-- `LinearEquiv.rTensor M f : N₁ ⊗ M ≃ₗ N₂ ⊗ M` is the natural linear equivalence
induced by `f : N₁ ≃ₗ N₂`. -/
def rTensor (f : N ≃ₗ[R] P) : N ⊗[R] M ≃ₗ[R] P ⊗[R] M := TensorProduct.congr f (refl R M)

variable (g : P ≃ₗ[R] Q) (f : N ≃ₗ[R] P) (m : M) (n : N) (p : P) (x : M ⊗[R] N) (y : N ⊗[R] M)

@[simp] theorem coe_lTensor : lTensor M f = (f : N →ₗ[R] P).lTensor M := rfl

@[simp] theorem coe_lTensor_symm : (lTensor M f).symm = (f.symm : P →ₗ[R] N).lTensor M := rfl

@[simp] theorem coe_rTensor : rTensor M f = (f : N →ₗ[R] P).rTensor M := rfl

@[simp] theorem coe_rTensor_symm : (rTensor M f).symm = (f.symm : P →ₗ[R] N).rTensor M := rfl

@[simp] theorem lTensor_tmul : f.lTensor M (m ⊗ₜ n) = m ⊗ₜ f n := rfl

@[simp] theorem lTensor_symm_tmul : (f.lTensor M).symm (m ⊗ₜ p) = m ⊗ₜ f.symm p := rfl

@[simp] theorem rTensor_tmul : f.rTensor M (n ⊗ₜ m) = f n ⊗ₜ m := rfl

@[simp] theorem rTensor_symm_tmul : (f.rTensor M).symm (p ⊗ₜ m) = f.symm p ⊗ₜ m := rfl

lemma comm_trans_rTensor_trans_comm_eq (g : N ≃ₗ[R] P) :
    TensorProduct.comm R Q N ≪≫ₗ rTensor Q g ≪≫ₗ TensorProduct.comm R P Q = lTensor Q g :=
  toLinearMap_injective <| TensorProduct.ext rfl

lemma comm_trans_lTensor_trans_comm_eq (g : N ≃ₗ[R] P) :
    TensorProduct.comm R N Q ≪≫ₗ lTensor Q g ≪≫ₗ TensorProduct.comm R Q P = rTensor Q g :=
  toLinearMap_injective <| TensorProduct.ext rfl

theorem lTensor_trans : (f ≪≫ₗ g).lTensor M = f.lTensor M ≪≫ₗ g.lTensor M :=
  toLinearMap_injective <| LinearMap.lTensor_comp M _ _

theorem lTensor_trans_apply : (f ≪≫ₗ g).lTensor M x = g.lTensor M (f.lTensor M x) :=
  LinearMap.lTensor_comp_apply M _ _ x

theorem rTensor_trans : (f ≪≫ₗ g).rTensor M = f.rTensor M ≪≫ₗ g.rTensor M :=
  toLinearMap_injective <| LinearMap.rTensor_comp M _ _

theorem rTensor_trans_apply : (f ≪≫ₗ g).rTensor M y = g.rTensor M (f.rTensor M y) :=
  LinearMap.rTensor_comp_apply M _ _ y

theorem lTensor_mul (f g : N ≃ₗ[R] N) : (f * g).lTensor M = f.lTensor M * g.lTensor M :=
  lTensor_trans M f g

theorem rTensor_mul (f g : N ≃ₗ[R] N) : (f * g).rTensor M = f.rTensor M * g.rTensor M :=
  rTensor_trans M f g

variable (N)

@[simp] theorem lTensor_refl : (refl R N).lTensor M = refl R _ := TensorProduct.congr_refl_refl

theorem lTensor_refl_apply : (refl R N).lTensor M x = x := by rw [lTensor_refl, refl_apply]

@[simp] theorem rTensor_refl : (refl R N).rTensor M = refl R _ := TensorProduct.congr_refl_refl

theorem rTensor_refl_apply : (refl R N).rTensor M y = y := by rw [rTensor_refl, refl_apply]

variable {N}

@[simp] theorem rTensor_trans_lTensor (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    f.rTensor N ≪≫ₗ g.lTensor P = TensorProduct.congr f g :=
  toLinearMap_injective <| LinearMap.lTensor_comp_rTensor M _ _

@[simp] theorem lTensor_trans_rTensor (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    g.lTensor M ≪≫ₗ f.rTensor Q = TensorProduct.congr f g :=
  toLinearMap_injective <| LinearMap.rTensor_comp_lTensor M _ _

@[simp] theorem rTensor_trans_congr (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (f' : S ≃ₗ[R] M) :
    f'.rTensor _ ≪≫ₗ TensorProduct.congr f g = TensorProduct.congr (f' ≪≫ₗ f) g :=
  toLinearMap_injective <| LinearMap.map_comp_rTensor M _ _ _

@[simp] theorem lTensor_trans_congr (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (g' : S ≃ₗ[R] N) :
    g'.lTensor _ ≪≫ₗ TensorProduct.congr f g = TensorProduct.congr f (g' ≪≫ₗ g) :=
  toLinearMap_injective <| LinearMap.map_comp_lTensor M _ _ _

@[simp] theorem congr_trans_rTensor (f' : P ≃ₗ[R] S) (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    TensorProduct.congr f g ≪≫ₗ f'.rTensor _ = TensorProduct.congr (f ≪≫ₗ f') g :=
  toLinearMap_injective <| LinearMap.rTensor_comp_map M _ _ _

@[simp] theorem congr_trans_lTensor (g' : Q ≃ₗ[R] S) (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    TensorProduct.congr f g ≪≫ₗ g'.lTensor _ = TensorProduct.congr f (g ≪≫ₗ g') :=
  toLinearMap_injective <| LinearMap.lTensor_comp_map M _ _ _

variable {M}

@[simp] theorem rTensor_pow (f : M ≃ₗ[R] M) (n : ℕ) : f.rTensor N ^ n = (f ^ n).rTensor N := by
  simpa only [one_pow] using TensorProduct.congr_pow f (1 : N ≃ₗ[R] N) n

@[simp] theorem rTensor_zpow (f : M ≃ₗ[R] M) (n : ℤ) : f.rTensor N ^ n = (f ^ n).rTensor N := by
  simpa only [one_zpow] using TensorProduct.congr_zpow f (1 : N ≃ₗ[R] N) n

@[simp] theorem lTensor_pow (f : N ≃ₗ[R] N) (n : ℕ) : f.lTensor M ^ n = (f ^ n).lTensor M := by
  simpa only [one_pow] using TensorProduct.congr_pow (1 : M ≃ₗ[R] M) f n

@[simp] theorem lTensor_zpow (f : N ≃ₗ[R] N) (n : ℤ) : f.lTensor M ^ n = (f ^ n).lTensor M := by
  simpa only [one_zpow] using TensorProduct.congr_zpow (1 : M ≃ₗ[R] M) f n

end LinearEquiv

end Semiring

section Ring

variable {R : Type*} [CommSemiring R]
variable {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}
variable [AddCommGroup M] [AddCommMonoid N] [AddCommGroup P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]

namespace LinearMap

@[simp]
theorem lTensor_sub (f g : N →ₗ[R] P) : (f - g).lTensor M = f.lTensor M - g.lTensor M := by
  simp_rw [← coe_lTensorHom]
  exact (lTensorHom (R := R) (N := N) (P := P) M).map_sub f g

@[simp]
theorem rTensor_sub (f g : N →ₗ[R] P) : (f - g).rTensor Q = f.rTensor Q - g.rTensor Q := by
  simp only [← coe_rTensorHom]
  exact (rTensorHom (R := R) (N := N) (P := P) Q).map_sub f g

@[simp]
theorem lTensor_neg (f : N →ₗ[R] P) : (-f).lTensor M = -f.lTensor M := by
  simp only [← coe_lTensorHom]
  exact (lTensorHom (R := R) (N := N) (P := P) M).map_neg f

@[simp]
theorem rTensor_neg (f : N →ₗ[R] P) : (-f).rTensor Q = -f.rTensor Q := by
  simp only [← coe_rTensorHom]
  exact (rTensorHom (R := R) (N := N) (P := P) Q).map_neg f

end LinearMap

end Ring

namespace Equiv
variable {R A A' B B' : Type*} [CommSemiring R]
  [AddCommMonoid A'] [AddCommMonoid B'] [Module R A'] [Module R B']

variable (R) in
open TensorProduct in
lemma tensorProductComm_def (eA : A ≃ A') (eB : B ≃ B') :
    letI := eA.addCommMonoid
    letI := eB.addCommMonoid
    letI := eA.module R
    letI := eB.module R
    TensorProduct.comm R A B = .trans
      (congr (eA.linearEquiv R) (eB.linearEquiv R)) (.trans
      (TensorProduct.comm R A' B') <| congr (eB.linearEquiv R).symm (eA.linearEquiv R).symm) := by
  ext x; induction x <;> simp [*]

end Equiv
