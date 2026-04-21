/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Continuous affine equivalences

In this file, we define continuous affine equivalences, affine equivalences
which are continuous with continuous inverse.

## Main definitions
* `ContinuousAffineEquiv.refl k P`: the identity map as a `ContinuousAffineEquiv`;
* `e.symm`: the inverse map of a `ContinuousAffineEquiv` as a `ContinuousAffineEquiv`;
* `e.trans e'`: composition of two `ContinuousAffineEquiv`s; note that the order
  follows `mathlib`'s `CategoryTheory` convention (apply `e`, then `e'`),
  not the convention used in function composition and compositions of bundled morphisms.

* `e.toHomeomorph`: the continuous affine equivalence `e` as a homeomorphism
* `e.toContinuousAffineMap`: the continuous affine equivalence `e` as a continuous affine map
* `ContinuousLinearEquiv.toContinuousAffineEquiv`: a continuous linear equivalence as a continuous
  affine equivalence
* `ContinuousAffineEquiv.constVAdd`: `AffineEquiv.constVAdd` as a continuous affine equivalence

## TODO
- equip `ContinuousAffineEquiv k P P` with a `Group` structure,
  with multiplication corresponding to composition in `AffineEquiv.group`.

-/

@[expose] public section

open Function

/-- A continuous affine equivalence, denoted `P₁ ≃ᴬ[k] P₂`, between two affine topological spaces
is an affine equivalence such that forward and inverse maps are continuous. -/
structure ContinuousAffineEquiv (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [Ring k]
    [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁] [TopologicalSpace P₁]
    [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] [TopologicalSpace P₂]
    extends P₁ ≃ᵃ[k] P₂ where
  continuous_toFun : Continuous toFun := by fun_prop
  continuous_invFun : Continuous invFun := by fun_prop

@[inherit_doc]
notation:25 P₁ " ≃ᴬ[" k:25 "] " P₂:0 => ContinuousAffineEquiv k P₁ P₂

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁] [TopologicalSpace P₁]
  [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] [TopologicalSpace P₂]
  [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃] [TopologicalSpace P₃]
  [AddCommGroup V₄] [Module k V₄] [AddTorsor V₄ P₄] [TopologicalSpace P₄]

namespace ContinuousAffineEquiv

-- Basic set-up: standard fields, coercions and ext lemmas
section Basic

/-- A continuous affine equivalence is a homeomorphism. -/
def toHomeomorph (e : P₁ ≃ᴬ[k] P₂) : P₁ ≃ₜ P₂ where
  __ := e

theorem toAffineEquiv_injective : Injective (toAffineEquiv : (P₁ ≃ᴬ[k] P₂) → P₁ ≃ᵃ[k] P₂) := by
  rintro ⟨e, econt, einv_cont⟩ ⟨e', e'cont, e'inv_cont⟩ H
  congr

instance instEquivLike : EquivLike (P₁ ≃ᴬ[k] P₂) P₁ P₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ h _ := toAffineEquiv_injective (DFunLike.coe_injective h)

instance : HomeomorphClass (P₁ ≃ᴬ[k] P₂) P₁ P₂ where
  map_continuous f := f.continuous_toFun
  inv_continuous f := f.continuous_invFun

attribute [coe] ContinuousAffineEquiv.toAffineEquiv

/-- Coerce continuous affine equivalences to affine equivalences. -/
instance coe : Coe (P₁ ≃ᴬ[k] P₂) (P₁ ≃ᵃ[k] P₂) := ⟨toAffineEquiv⟩

instance instFunLike : FunLike (P₁ ≃ᴬ[k] P₂) P₁ P₂ where
  coe f := f.toAffineEquiv
  coe_injective' _ _ h := toAffineEquiv_injective (DFunLike.coe_injective h)

@[simp, norm_cast]
theorem coe_coe (e : P₁ ≃ᴬ[k] P₂) : ⇑(e : P₁ ≃ᵃ[k] P₂) = e :=
  rfl

@[simp]
theorem coe_toEquiv (e : P₁ ≃ᴬ[k] P₂) : ⇑e.toEquiv = e :=
  rfl

/-- See Note [custom simps projection].
  We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (e : P₁ ≃ᴬ[k] P₂) : P₁ → P₂ :=
  e

/-- See Note [custom simps projection]. -/
def Simps.symm_apply (e : P₁ ≃ᴬ[k] P₂) : P₂ → P₁ :=
  e.symm

initialize_simps_projections ContinuousAffineEquiv (toFun → apply, invFun → symm_apply)

@[ext]
theorem ext {e e' : P₁ ≃ᴬ[k] P₂} (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

@[continuity]
protected theorem continuous (e : P₁ ≃ᴬ[k] P₂) : Continuous e :=
  e.2

/-- A continuous affine equivalence is a continuous affine map. -/
def toContinuousAffineMap (e : P₁ ≃ᴬ[k] P₂) : P₁ →ᴬ[k] P₂ where
  __ := e
  cont := e.continuous_toFun

/-- Coerce continuous linear equivs to continuous linear maps. -/
instance ContinuousAffineMap.coe : Coe (P₁ ≃ᴬ[k] P₂) (P₁ →ᴬ[k] P₂) :=
  ⟨toContinuousAffineMap⟩

@[simp]
lemma coe_toContinuousAffineMap (e : P₁ ≃ᴬ[k] P₂) : ⇑e.toContinuousAffineMap = e :=
  rfl

lemma toContinuousAffineMap_injective :
    Function.Injective (toContinuousAffineMap : (P₁ ≃ᴬ[k] P₂) → (P₁ →ᴬ[k] P₂)) := by
  intro e e' h
  ext p
  simp_rw [← coe_toContinuousAffineMap, h]

lemma toContinuousAffineMap_toAffineMap (e : P₁ ≃ᴬ[k] P₂) :
    e.toContinuousAffineMap.toAffineMap = e.toAffineEquiv.toAffineMap :=
  rfl

lemma toContinuousAffineMap_toContinuousMap (e : P₁ ≃ᴬ[k] P₂) :
    e.toContinuousAffineMap.toContinuousMap = toContinuousMap e.toHomeomorph :=
  rfl

end Basic

section ReflSymmTrans

variable (k P₁) in
/-- Identity map as a `ContinuousAffineEquiv`. -/
def refl : P₁ ≃ᴬ[k] P₁ where
  toEquiv := Equiv.refl P₁
  linear := LinearEquiv.refl k V₁
  map_vadd' _ _ := rfl

@[simp]
theorem coe_refl : ⇑(refl k P₁) = id :=
  rfl

@[simp]
theorem refl_apply (x : P₁) : refl k P₁ x = x :=
  rfl

@[simp]
theorem toAffineEquiv_refl : (refl k P₁).toAffineEquiv = AffineEquiv.refl k P₁ :=
  rfl

@[simp]
theorem toEquiv_refl : (refl k P₁).toEquiv = Equiv.refl P₁ :=
  rfl

/-- Inverse of a continuous affine equivalence as a continuous affine equivalence. -/
@[symm]
def symm (e : P₁ ≃ᴬ[k] P₂) : P₂ ≃ᴬ[k] P₁ where
  toAffineEquiv := e.toAffineEquiv.symm
  continuous_toFun := e.continuous_invFun
  continuous_invFun := e.continuous_toFun

@[simp]
theorem toAffineEquiv_symm (e : P₁ ≃ᴬ[k] P₂) : e.symm.toAffineEquiv = e.toAffineEquiv.symm :=
  rfl

@[simp]
theorem coe_symm_toAffineEquiv (e : P₁ ≃ᴬ[k] P₂) : ⇑e.toAffineEquiv.symm = e.symm := rfl

@[simp]
theorem toEquiv_symm (e : P₁ ≃ᴬ[k] P₂) : e.symm.toEquiv = e.toEquiv.symm := rfl

@[simp]
theorem coe_symm_toEquiv (e : P₁ ≃ᴬ[k] P₂) : ⇑e.toEquiv.symm = e.symm := rfl

@[simp]
theorem apply_symm_apply (e : P₁ ≃ᴬ[k] P₂) (p : P₂) : e (e.symm p) = p :=
  e.toEquiv.apply_symm_apply p

@[simp]
theorem symm_apply_apply (e : P₁ ≃ᴬ[k] P₂) (p : P₁) : e.symm (e p) = p :=
  e.toEquiv.symm_apply_apply p

theorem apply_eq_iff_eq_symm_apply (e : P₁ ≃ᴬ[k] P₂) {p₁ p₂} : e p₁ = p₂ ↔ p₁ = e.symm p₂ :=
  e.toEquiv.apply_eq_iff_eq_symm_apply

theorem apply_eq_iff_eq (e : P₁ ≃ᴬ[k] P₂) {p₁ p₂ : P₁} : e p₁ = e p₂ ↔ p₁ = p₂ :=
  e.toEquiv.apply_eq_iff_eq

@[simp]
theorem symm_symm (e : P₁ ≃ᴬ[k] P₂) : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (symm : (P₁ ≃ᴬ[k] P₂) → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

theorem symm_symm_apply (e : P₁ ≃ᴬ[k] P₂) (x : P₁) : e.symm.symm x = e x :=
  rfl

theorem symm_apply_eq (e : P₁ ≃ᴬ[k] P₂) {x y} : e.symm x = y ↔ x = e y :=
  e.toAffineEquiv.symm_apply_eq

theorem eq_symm_apply (e : P₁ ≃ᴬ[k] P₂) {x y} : y = e.symm x ↔ e y = x :=
  e.toAffineEquiv.eq_symm_apply

@[simp]
theorem image_symm (f : P₁ ≃ᴬ[k] P₂) (s : Set P₂) : f.symm '' s = f ⁻¹' s :=
  f.symm.toEquiv.image_eq_preimage_symm _

@[simp]
theorem preimage_symm (f : P₁ ≃ᴬ[k] P₂) (s : Set P₁) : f.symm ⁻¹' s = f '' s :=
  (f.symm.image_symm _).symm

protected theorem bijective (e : P₁ ≃ᴬ[k] P₂) : Bijective e :=
  e.toEquiv.bijective

protected theorem surjective (e : P₁ ≃ᴬ[k] P₂) : Surjective e :=
  e.toEquiv.surjective

protected theorem injective (e : P₁ ≃ᴬ[k] P₂) : Injective e :=
  e.toEquiv.injective

protected theorem image_eq_preimage_symm (e : P₁ ≃ᴬ[k] P₂) (s : Set P₁) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage_symm s

protected theorem image_symm_eq_preimage (e : P₁ ≃ᴬ[k] P₂) (s : Set P₂) :
    e.symm '' s = e ⁻¹' s := by
  rw [e.symm.image_eq_preimage_symm, e.symm_symm]

@[simp]
theorem image_preimage (e : P₁ ≃ᴬ[k] P₂) (s : Set P₂) : e '' (e ⁻¹' s) = s :=
  e.surjective.image_preimage s

@[simp]
theorem preimage_image (e : P₁ ≃ᴬ[k] P₂) (s : Set P₁) : e ⁻¹' (e '' s) = s :=
  e.injective.preimage_image s

theorem symm_image_image (e : P₁ ≃ᴬ[k] P₂) (s : Set P₁) : e.symm '' (e '' s) = s :=
  e.toEquiv.symm_image_image s

theorem image_symm_image (e : P₁ ≃ᴬ[k] P₂) (s : Set P₂) : e '' (e.symm '' s) = s :=
  e.symm.symm_image_image s

@[simp]
theorem refl_symm : (refl k P₁).symm = refl k P₁ :=
  rfl

@[simp]
theorem symm_refl : (refl k P₁).symm = refl k P₁ :=
  rfl

/-- Composition of two `ContinuousAffineEquiv`alences, applied left to right. -/
@[trans]
def trans (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) : P₁ ≃ᴬ[k] P₃ where
  toAffineEquiv := e.toAffineEquiv.trans e'.toAffineEquiv
  continuous_toFun := e'.continuous_toFun.comp (e.continuous_toFun)
  continuous_invFun := e.continuous_invFun.comp (e'.continuous_invFun)

@[simp]
theorem coe_trans (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) : ⇑(e.trans e') = e' ∘ e :=
  rfl

@[simp]
theorem trans_apply (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) (p : P₁) : e.trans e' p = e' (e p) :=
  rfl

theorem trans_assoc (e₁ : P₁ ≃ᴬ[k] P₂) (e₂ : P₂ ≃ᴬ[k] P₃) (e₃ : P₃ ≃ᴬ[k] P₄) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) :=
  ext fun _ ↦ rfl

@[simp]
theorem trans_refl (e : P₁ ≃ᴬ[k] P₂) : e.trans (refl k P₂) = e :=
  ext fun _ ↦ rfl

@[simp]
theorem refl_trans (e : P₁ ≃ᴬ[k] P₂) : (refl k P₁).trans e = e :=
  ext fun _ ↦ rfl

@[simp]
theorem self_trans_symm (e : P₁ ≃ᴬ[k] P₂) : e.trans e.symm = refl k P₁ :=
  ext e.symm_apply_apply

@[simp]
theorem symm_trans_self (e : P₁ ≃ᴬ[k] P₂) : e.symm.trans e = refl k P₂ :=
  ext e.apply_symm_apply

lemma trans_toContinuousAffineMap (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) :
    (e.trans e').toContinuousAffineMap = e'.toContinuousAffineMap.comp e.toContinuousAffineMap :=
  rfl

end ReflSymmTrans

section

variable {E F : Type*} [AddCommGroup E] [Module k E] [TopologicalSpace E]
  [AddCommGroup F] [Module k F] [TopologicalSpace F]

/-- Reinterpret a continuous linear equivalence between modules
as a continuous affine equivalence. -/
def _root_.ContinuousLinearEquiv.toContinuousAffineEquiv (L : E ≃L[k] F) : E ≃ᴬ[k] F where
  toAffineEquiv := L.toAffineEquiv
  continuous_toFun := L.continuous_toFun
  continuous_invFun := L.continuous_invFun

@[simp]
theorem _root_.ContinuousLinearEquiv.coe_toContinuousAffineEquiv (e : E ≃L[k] F) :
    ⇑e.toContinuousAffineEquiv = e :=
  rfl

lemma _root_.ContinuousLinearEquiv.toContinuousAffineEquiv_toContinuousAffineMap (L : E ≃L[k] F) :
    L.toContinuousAffineEquiv.toContinuousAffineMap =
      L.toContinuousLinearMap.toContinuousAffineMap :=
  rfl

variable (k P₁) in
/-- The map `p ↦ v +ᵥ p` as a continuous affine automorphism of an affine space
  on which addition is continuous. -/
def constVAdd [ContinuousConstVAdd V₁ P₁] (v : V₁) : P₁ ≃ᴬ[k] P₁ where
  toAffineEquiv := AffineEquiv.constVAdd k P₁ v
  continuous_toFun := continuous_const_vadd v
  continuous_invFun := continuous_const_vadd (-v)

lemma constVAdd_coe [ContinuousConstVAdd V₁ P₁] (v : V₁) :
    (constVAdd k P₁ v).toAffineEquiv = .constVAdd k P₁ v := rfl

end

section

variable (e₁ : P₁ ≃ᴬ[k] P₂) (e₂ : P₃ ≃ᴬ[k] P₄)

/-- Product of two continuous affine equivalences. The map comes from `Equiv.prodCongr` -/
@[simps toAffineEquiv]
def prodCongr : P₁ × P₃ ≃ᴬ[k] P₂ × P₄ where
  __ := AffineEquiv.prodCongr e₁ e₂
  continuous_toFun := by eta_expand; dsimp; fun_prop
  continuous_invFun := by eta_expand; dsimp; fun_prop

@[simp]
theorem prodCongr_symm : (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm :=
  rfl

@[simp]
theorem prodCongr_apply (p : P₁ × P₃) : e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2) :=
  rfl

@[simp]
theorem prodCongr_toContinuousAffineMap : (e₁.prodCongr e₂).toContinuousAffineMap =
    e₁.toContinuousAffineMap.prodMap e₂.toContinuousAffineMap :=
  rfl

end

section

variable (k P₁ P₂ P₃)

/-- Product of affine spaces is commutative up to continuous affine isomorphism. -/
@[simps! apply symm_apply toAffineEquiv]
def prodComm : P₁ × P₂ ≃ᴬ[k] P₂ × P₁ where
  __ := AffineEquiv.prodComm k P₁ P₂
  continuous_toFun := continuous_swap
  continuous_invFun := continuous_swap

@[simp]
theorem prodComm_symm : (prodComm k P₁ P₂).symm = prodComm k P₂ P₁ :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- Product of affine spaces is associative up to continuous affine isomorphism. -/
@[simps! apply symm_apply toAffineEquiv]
def prodAssoc : (P₁ × P₂) × P₃ ≃ᴬ[k] P₁ × (P₂ × P₃) where
  __ := AffineEquiv.prodAssoc k P₁ P₂ P₃
  continuous_toFun := by eta_expand; dsimp; fun_prop
  continuous_invFun := by eta_expand; dsimp; fun_prop

end

end ContinuousAffineEquiv
