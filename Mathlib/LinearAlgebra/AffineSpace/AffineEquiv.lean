/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.Algebra.Invertible

#align_import linear_algebra.affine_space.affine_equiv from "leanprover-community/mathlib"@"bd1fc183335ea95a9519a1630bcf901fe9326d83"

/-!
# Affine equivalences

In this file we define `AffineEquiv k P₁ P₂` (notation: `P₁ ≃ᵃ[k] P₂`) to be the type of affine
equivalences between `P₁` and `P₂`, i.e., equivalences such that both forward and inverse maps are
affine maps.

We define the following equivalences:

* `AffineEquiv.refl k P`: the identity map as an `AffineEquiv`;

* `e.symm`: the inverse map of an `AffineEquiv` as an `AffineEquiv`;

* `e.trans e'`: composition of two `AffineEquiv`s; note that the order follows `mathlib`'s
  `CategoryTheory` convention (apply `e`, then `e'`), not the convention used in function
  composition and compositions of bundled morphisms.

We equip `AffineEquiv k P P` with a `Group` structure with multiplication corresponding to
composition in `AffineEquiv.group`.

## Tags

affine space, affine equivalence
-/

open Function Set

open Affine

/-- An affine equivalence is an equivalence between affine spaces such that both forward
and inverse maps are affine.

We define it using an `Equiv` for the map and a `LinearEquiv` for the linear part in order
to allow affine equivalences with good definitional equalities. -/
--@[nolint has_nonempty_instance]
structure AffineEquiv (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [Ring k] [AddCommGroup V₁] [Module k V₁]
  [AddTorsor V₁ P₁] [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] extends P₁ ≃ P₂ where
  linear : V₁ ≃ₗ[k] V₂
  map_vadd' : ∀ (p : P₁) (v : V₁), toEquiv (v +ᵥ p) = linear v +ᵥ toEquiv p
#align affine_equiv AffineEquiv

notation:25 P₁ " ≃ᵃ[" k:25 "] " P₂:0 => AffineEquiv k P₁ P₂

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k] [AddCommGroup V₁] [Module k V₁]
  [AddTorsor V₁ P₁] [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] [AddCommGroup V₃]
  [Module k V₃] [AddTorsor V₃ P₃] [AddCommGroup V₄] [Module k V₄] [AddTorsor V₄ P₄]

namespace AffineEquiv

/-- Reinterpret an `AffineEquiv` as an `AffineMap`. -/
@[coe]
def toAffineMap (e : P₁ ≃ᵃ[k] P₂) : P₁ →ᵃ[k] P₂ :=
  { e with }
#align affine_equiv.to_affine_map AffineEquiv.toAffineMap

@[simp]
theorem toAffineMap_mk (f : P₁ ≃ P₂) (f' : V₁ ≃ₗ[k] V₂) (h) :
    toAffineMap (mk f f' h) = ⟨f, f', h⟩ :=
  rfl
#align affine_equiv.to_affine_map_mk AffineEquiv.toAffineMap_mk

@[simp]
theorem linear_toAffineMap (e : P₁ ≃ᵃ[k] P₂) : e.toAffineMap.linear = e.linear :=
  rfl
#align affine_equiv.linear_to_affine_map AffineEquiv.linear_toAffineMap

theorem toAffineMap_injective : Injective (toAffineMap : (P₁ ≃ᵃ[k] P₂) → P₁ →ᵃ[k] P₂) := by
  rintro ⟨e, el, h⟩ ⟨e', el', h'⟩ H
  -- ⊢ { toEquiv := e, linear := el, map_vadd' := h } = { toEquiv := e', linear :=  …
  -- porting note: added `()`s and `AffineMap.mk.injEq`
  simp only [(toAffineMap_mk), (AffineMap.mk.injEq), Equiv.coe_inj,
    LinearEquiv.toLinearMap_inj] at H
  congr
  -- ⊢ e = e'
  exacts [H.1, H.2]
  -- 🎉 no goals
#align affine_equiv.to_affine_map_injective AffineEquiv.toAffineMap_injective

@[simp]
theorem toAffineMap_inj {e e' : P₁ ≃ᵃ[k] P₂} : e.toAffineMap = e'.toAffineMap ↔ e = e' :=
  toAffineMap_injective.eq_iff
#align affine_equiv.to_affine_map_inj AffineEquiv.toAffineMap_inj

instance equivLike : EquivLike (P₁ ≃ᵃ[k] P₂) P₁ P₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ h _ := toAffineMap_injective (FunLike.coe_injective h)
#align affine_equiv.equiv_like AffineEquiv.equivLike

instance : CoeFun (P₁ ≃ᵃ[k] P₂) fun _ => P₁ → P₂ :=
  FunLike.hasCoeToFun

instance : CoeOut (P₁ ≃ᵃ[k] P₂) (P₁ ≃ P₂) :=
  ⟨AffineEquiv.toEquiv⟩

@[simp]
theorem map_vadd (e : P₁ ≃ᵃ[k] P₂) (p : P₁) (v : V₁) : e (v +ᵥ p) = e.linear v +ᵥ e p :=
  e.map_vadd' p v
#align affine_equiv.map_vadd AffineEquiv.map_vadd

@[simp]
theorem coe_toEquiv (e : P₁ ≃ᵃ[k] P₂) : ⇑e.toEquiv = e :=
  rfl
#align affine_equiv.coe_to_equiv AffineEquiv.coe_toEquiv

instance : Coe (P₁ ≃ᵃ[k] P₂) (P₁ →ᵃ[k] P₂) :=
  ⟨toAffineMap⟩

@[simp]
theorem coe_toAffineMap (e : P₁ ≃ᵃ[k] P₂) : (e.toAffineMap : P₁ → P₂) = (e : P₁ → P₂) :=
  rfl
#align affine_equiv.coe_to_affine_map AffineEquiv.coe_toAffineMap

@[norm_cast, simp]
theorem coe_coe (e : P₁ ≃ᵃ[k] P₂) : ((e : P₁ →ᵃ[k] P₂) : P₁ → P₂) = e :=
  rfl
#align affine_equiv.coe_coe AffineEquiv.coe_coe

@[simp]
theorem coe_linear (e : P₁ ≃ᵃ[k] P₂) : (e : P₁ →ᵃ[k] P₂).linear = e.linear :=
  rfl
#align affine_equiv.coe_linear AffineEquiv.coe_linear

@[ext]
theorem ext {e e' : P₁ ≃ᵃ[k] P₂} (h : ∀ x, e x = e' x) : e = e' :=
  FunLike.ext _ _ h
#align affine_equiv.ext AffineEquiv.ext

theorem coeFn_injective : @Injective (P₁ ≃ᵃ[k] P₂) (P₁ → P₂) (⇑) :=
  FunLike.coe_injective
#align affine_equiv.coe_fn_injective AffineEquiv.coeFn_injective

@[norm_cast]
-- Porting note: removed `simp`: proof is `simp only [FunLike.coe_fn_eq]`
theorem coeFn_inj {e e' : P₁ ≃ᵃ[k] P₂} : (e : P₁ → P₂) = e' ↔ e = e' :=
  coeFn_injective.eq_iff
#align affine_equiv.coe_fn_inj AffineEquiv.coeFn_inj

theorem toEquiv_injective : Injective (toEquiv : (P₁ ≃ᵃ[k] P₂) → P₁ ≃ P₂) := fun _ _ H =>
  ext <| Equiv.ext_iff.1 H
#align affine_equiv.to_equiv_injective AffineEquiv.toEquiv_injective

@[simp]
theorem toEquiv_inj {e e' : P₁ ≃ᵃ[k] P₂} : e.toEquiv = e'.toEquiv ↔ e = e' :=
  toEquiv_injective.eq_iff
#align affine_equiv.to_equiv_inj AffineEquiv.toEquiv_inj

@[simp]
theorem coe_mk (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (h) : ((⟨e, e', h⟩ : P₁ ≃ᵃ[k] P₂) : P₁ → P₂) = e :=
  rfl
#align affine_equiv.coe_mk AffineEquiv.coe_mk

/-- Construct an affine equivalence by verifying the relation between the map and its linear part at
one base point. Namely, this function takes a map `e : P₁ → P₂`, a linear equivalence
`e' : V₁ ≃ₗ[k] V₂`, and a point `p` such that for any other point `p'` we have
`e p' = e' (p' -ᵥ p) +ᵥ e p`. -/
def mk' (e : P₁ → P₂) (e' : V₁ ≃ₗ[k] V₂) (p : P₁) (h : ∀ p' : P₁, e p' = e' (p' -ᵥ p) +ᵥ e p) :
    P₁ ≃ᵃ[k] P₂ where
  toFun := e
  invFun := fun q' : P₂ => e'.symm (q' -ᵥ e p) +ᵥ p
  -- Porting note: `simp` needs `()`
  left_inv p' := by simp [h p', (vadd_vsub), (vsub_vadd)]
                    -- 🎉 no goals
  -- Porting note: `simp` needs `()`
  right_inv q' := by simp [h (e'.symm (q' -ᵥ e p) +ᵥ p), (vadd_vsub), (vsub_vadd)]
                     -- 🎉 no goals
  linear := e'
  -- Porting note: `simp` needs `()`
  map_vadd' p' v := by simp [h p', h (v +ᵥ p'), (vadd_vsub_assoc), (vadd_vadd)]
                       -- 🎉 no goals
#align affine_equiv.mk' AffineEquiv.mk'

@[simp]
theorem coe_mk' (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h) : ⇑(mk' e e' p h) = e :=
  rfl
#align affine_equiv.coe_mk' AffineEquiv.coe_mk'

@[simp]
theorem linear_mk' (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h) : (mk' e e' p h).linear = e' :=
  rfl
#align affine_equiv.linear_mk' AffineEquiv.linear_mk'

/-- Inverse of an affine equivalence as an affine equivalence. -/
@[symm]
def symm (e : P₁ ≃ᵃ[k] P₂) : P₂ ≃ᵃ[k] P₁ where
  toEquiv := e.toEquiv.symm
  linear := e.linear.symm
  map_vadd' p v :=
    e.toEquiv.symm.apply_eq_iff_eq_symm_apply.2 <| by
      rw [Equiv.symm_symm, e.map_vadd' ((Equiv.symm e.toEquiv) p) ((LinearEquiv.symm e.linear) v),
        LinearEquiv.apply_symm_apply, Equiv.apply_symm_apply]
#align affine_equiv.symm AffineEquiv.symm

@[simp]
theorem symm_toEquiv (e : P₁ ≃ᵃ[k] P₂) : e.toEquiv.symm = e.symm.toEquiv :=
  rfl
#align affine_equiv.symm_to_equiv AffineEquiv.symm_toEquiv

@[simp]
theorem symm_linear (e : P₁ ≃ᵃ[k] P₂) : e.linear.symm = e.symm.linear :=
  rfl
#align affine_equiv.symm_linear AffineEquiv.symm_linear

/-- See Note [custom simps projection] -/
def Simps.apply (e : P₁ ≃ᵃ[k] P₂) : P₁ → P₂ :=
  e
#align affine_equiv.simps.apply AffineEquiv.Simps.apply

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : P₁ ≃ᵃ[k] P₂) : P₂ → P₁ :=
  e.symm
#align affine_equiv.simps.symm_apply AffineEquiv.Simps.symm_apply

initialize_simps_projections AffineEquiv (toEquiv_toFun → apply, toEquiv_invFun → symm_apply,
  linear → linear, as_prefix linear, -toEquiv)

protected theorem bijective (e : P₁ ≃ᵃ[k] P₂) : Bijective e :=
  e.toEquiv.bijective
#align affine_equiv.bijective AffineEquiv.bijective

protected theorem surjective (e : P₁ ≃ᵃ[k] P₂) : Surjective e :=
  e.toEquiv.surjective
#align affine_equiv.surjective AffineEquiv.surjective

protected theorem injective (e : P₁ ≃ᵃ[k] P₂) : Injective e :=
  e.toEquiv.injective
#align affine_equiv.injective AffineEquiv.injective

/-- Bijective affine maps are affine isomorphisms. -/
@[simps! linear apply]
noncomputable def ofBijective {φ : P₁ →ᵃ[k] P₂} (hφ : Function.Bijective φ) : P₁ ≃ᵃ[k] P₂ :=
  { Equiv.ofBijective _ hφ with
    linear := LinearEquiv.ofBijective φ.linear (φ.linear_bijective_iff.mpr hφ)
    map_vadd' := φ.map_vadd }
#align affine_equiv.of_bijective AffineEquiv.ofBijective

theorem ofBijective.symm_eq {φ : P₁ →ᵃ[k] P₂} (hφ : Function.Bijective φ) :
    (ofBijective hφ).symm.toEquiv = (Equiv.ofBijective _ hφ).symm :=
  rfl
#align affine_equiv.of_bijective.symm_eq AffineEquiv.ofBijective.symm_eq

@[simp]
theorem range_eq (e : P₁ ≃ᵃ[k] P₂) : range e = univ :=
  e.surjective.range_eq
#align affine_equiv.range_eq AffineEquiv.range_eq

@[simp]
theorem apply_symm_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₂) : e (e.symm p) = p :=
  e.toEquiv.apply_symm_apply p
#align affine_equiv.apply_symm_apply AffineEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₁) : e.symm (e p) = p :=
  e.toEquiv.symm_apply_apply p
#align affine_equiv.symm_apply_apply AffineEquiv.symm_apply_apply

theorem apply_eq_iff_eq_symm_apply (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : e p₁ = p₂ ↔ p₁ = e.symm p₂ :=
  e.toEquiv.apply_eq_iff_eq_symm_apply
#align affine_equiv.apply_eq_iff_eq_symm_apply AffineEquiv.apply_eq_iff_eq_symm_apply

-- Porting note: removed `simp`, proof is `by simp only [@EmbeddingLike.apply_eq_iff_eq]`
theorem apply_eq_iff_eq (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂ : P₁} : e p₁ = e p₂ ↔ p₁ = p₂ :=
  e.toEquiv.apply_eq_iff_eq
#align affine_equiv.apply_eq_iff_eq AffineEquiv.apply_eq_iff_eq

@[simp]
theorem image_symm (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂) : f.symm '' s = f ⁻¹' s :=
  f.symm.toEquiv.image_eq_preimage _
#align affine_equiv.image_symm AffineEquiv.image_symm

@[simp]
theorem preimage_symm (f : P₁ ≃ᵃ[k] P₂) (s : Set P₁) : f.symm ⁻¹' s = f '' s :=
  (f.symm.image_symm _).symm
#align affine_equiv.preimage_symm AffineEquiv.preimage_symm

variable (k P₁)

/-- Identity map as an `AffineEquiv`. -/
-- @[refl] -- Porting note: removed attribute
def refl : P₁ ≃ᵃ[k] P₁ where
  toEquiv := Equiv.refl P₁
  linear := LinearEquiv.refl k V₁
  map_vadd' _ _ := rfl
#align affine_equiv.refl AffineEquiv.refl

@[simp]
theorem coe_refl : ⇑(refl k P₁) = id :=
  rfl
#align affine_equiv.coe_refl AffineEquiv.coe_refl

@[simp]
theorem coe_refl_to_affineMap : ↑(refl k P₁) = AffineMap.id k P₁ :=
  rfl
#align affine_equiv.coe_refl_to_affine_map AffineEquiv.coe_refl_to_affineMap

@[simp]
theorem refl_apply (x : P₁) : refl k P₁ x = x :=
  rfl
#align affine_equiv.refl_apply AffineEquiv.refl_apply

@[simp]
theorem toEquiv_refl : (refl k P₁).toEquiv = Equiv.refl P₁ :=
  rfl
#align affine_equiv.to_equiv_refl AffineEquiv.toEquiv_refl

@[simp]
theorem linear_refl : (refl k P₁).linear = LinearEquiv.refl k V₁ :=
  rfl
#align affine_equiv.linear_refl AffineEquiv.linear_refl

@[simp]
theorem symm_refl : (refl k P₁).symm = refl k P₁ :=
  rfl
#align affine_equiv.symm_refl AffineEquiv.symm_refl

variable {k P₁}

/-- Composition of two `AffineEquiv`alences, applied left to right. -/
@[trans]
def trans (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) : P₁ ≃ᵃ[k] P₃ where
  toEquiv := e.toEquiv.trans e'.toEquiv
  linear := e.linear.trans e'.linear
  map_vadd' p v := by
    -- porting note: added `()`
    simp only [LinearEquiv.trans_apply, (coe_toEquiv), (· ∘ ·), Equiv.coe_trans, (map_vadd)]
    -- 🎉 no goals
#align affine_equiv.trans AffineEquiv.trans

@[simp]
theorem coe_trans (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) : ⇑(e.trans e') = e' ∘ e :=
  rfl
#align affine_equiv.coe_trans AffineEquiv.coe_trans

@[simp]
theorem coe_trans_to_affineMap (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) :
    (e.trans e' : P₁ →ᵃ[k] P₃) = (e' : P₂ →ᵃ[k] P₃).comp e :=
  rfl
#align affine_equiv.coe_trans_to_affine_map AffineEquiv.coe_trans_to_affineMap

@[simp]
theorem trans_apply (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) (p : P₁) : e.trans e' p = e' (e p) :=
  rfl
#align affine_equiv.trans_apply AffineEquiv.trans_apply

theorem trans_assoc (e₁ : P₁ ≃ᵃ[k] P₂) (e₂ : P₂ ≃ᵃ[k] P₃) (e₃ : P₃ ≃ᵃ[k] P₄) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) :=
  ext fun _ => rfl
#align affine_equiv.trans_assoc AffineEquiv.trans_assoc

@[simp]
theorem trans_refl (e : P₁ ≃ᵃ[k] P₂) : e.trans (refl k P₂) = e :=
  ext fun _ => rfl
#align affine_equiv.trans_refl AffineEquiv.trans_refl

@[simp]
theorem refl_trans (e : P₁ ≃ᵃ[k] P₂) : (refl k P₁).trans e = e :=
  ext fun _ => rfl
#align affine_equiv.refl_trans AffineEquiv.refl_trans

@[simp]
theorem self_trans_symm (e : P₁ ≃ᵃ[k] P₂) : e.trans e.symm = refl k P₁ :=
  ext e.symm_apply_apply
#align affine_equiv.self_trans_symm AffineEquiv.self_trans_symm

@[simp]
theorem symm_trans_self (e : P₁ ≃ᵃ[k] P₂) : e.symm.trans e = refl k P₂ :=
  ext e.apply_symm_apply
#align affine_equiv.symm_trans_self AffineEquiv.symm_trans_self

@[simp]
theorem apply_lineMap (e : P₁ ≃ᵃ[k] P₂) (a b : P₁) (c : k) :
    e (AffineMap.lineMap a b c) = AffineMap.lineMap (e a) (e b) c :=
  e.toAffineMap.apply_lineMap a b c
#align affine_equiv.apply_line_map AffineEquiv.apply_lineMap

instance group : Group (P₁ ≃ᵃ[k] P₁) where
  one := refl k P₁
  mul e e' := e'.trans e
  inv := symm
  mul_assoc e₁ e₂ e₃ := trans_assoc _ _ _
  one_mul := trans_refl
  mul_one := refl_trans
  mul_left_inv := self_trans_symm
#align affine_equiv.group AffineEquiv.group

theorem one_def : (1 : P₁ ≃ᵃ[k] P₁) = refl k P₁ :=
  rfl
#align affine_equiv.one_def AffineEquiv.one_def

@[simp]
theorem coe_one : ⇑(1 : P₁ ≃ᵃ[k] P₁) = id :=
  rfl
#align affine_equiv.coe_one AffineEquiv.coe_one

theorem mul_def (e e' : P₁ ≃ᵃ[k] P₁) : e * e' = e'.trans e :=
  rfl
#align affine_equiv.mul_def AffineEquiv.mul_def

@[simp]
theorem coe_mul (e e' : P₁ ≃ᵃ[k] P₁) : ⇑(e * e') = e ∘ e' :=
  rfl
#align affine_equiv.coe_mul AffineEquiv.coe_mul

theorem inv_def (e : P₁ ≃ᵃ[k] P₁) : e⁻¹ = e.symm :=
  rfl
#align affine_equiv.inv_def AffineEquiv.inv_def

/-- `AffineEquiv.linear` on automorphisms is a `MonoidHom`. -/
@[simps]
def linearHom : (P₁ ≃ᵃ[k] P₁) →* V₁ ≃ₗ[k] V₁ where
  toFun := linear
  map_one' := rfl
  map_mul' _ _ := rfl
#align affine_equiv.linear_hom AffineEquiv.linearHom

/-- The group of `AffineEquiv`s are equivalent to the group of units of `AffineMap`.

This is the affine version of `LinearMap.GeneralLinearGroup.generalLinearEquiv`. -/
@[simps]
def equivUnitsAffineMap : (P₁ ≃ᵃ[k] P₁) ≃* (P₁ →ᵃ[k] P₁)ˣ where
  toFun e :=
    { val := e, inv := e.symm,
      val_inv := congr_arg toAffineMap e.symm_trans_self
      inv_val := congr_arg toAffineMap e.self_trans_symm }
  invFun u :=
    { toFun := (u : P₁ →ᵃ[k] P₁)
      invFun := (↑u⁻¹ : P₁ →ᵃ[k] P₁)
      left_inv := AffineMap.congr_fun u.inv_mul
      right_inv := AffineMap.congr_fun u.mul_inv
      linear :=
        LinearMap.GeneralLinearGroup.generalLinearEquiv _ _ <| Units.map AffineMap.linearHom u
      map_vadd' := fun _ _ => (u : P₁ →ᵃ[k] P₁).map_vadd _ _ }
  left_inv _ := AffineEquiv.ext fun _ => rfl
  right_inv _ := Units.ext <| AffineMap.ext fun _ => rfl
  map_mul' _ _ := rfl
#align affine_equiv.equiv_units_affine_map AffineEquiv.equivUnitsAffineMap

variable (k)

/-- The map `v ↦ v +ᵥ b` as an affine equivalence between a module `V` and an affine space `P` with
tangent space `V`. -/
@[simps! linear apply symm_apply]
def vaddConst (b : P₁) : V₁ ≃ᵃ[k] P₁ where
  toEquiv := Equiv.vaddConst b
  linear := LinearEquiv.refl _ _
  map_vadd' _ _ := add_vadd _ _ _
#align affine_equiv.vadd_const AffineEquiv.vaddConst

/-- `p' ↦ p -ᵥ p'` as an equivalence. -/
def constVSub (p : P₁) : P₁ ≃ᵃ[k] V₁ where
  toEquiv := Equiv.constVSub p
  linear := LinearEquiv.neg k
  -- porting note: added `coe_constVSub` and `()`s
  map_vadd' p' v := by simp [(Equiv.coe_constVSub), (vsub_vadd_eq_vsub_sub), neg_add_eq_sub]
                       -- 🎉 no goals
#align affine_equiv.const_vsub AffineEquiv.constVSub

@[simp]
theorem coe_constVSub (p : P₁) : ⇑(constVSub k p) = (· -ᵥ ·) p :=
  rfl
#align affine_equiv.coe_const_vsub AffineEquiv.coe_constVSub

@[simp]
theorem coe_constVSub_symm (p : P₁) : ⇑(constVSub k p).symm = fun v : V₁ => -v +ᵥ p :=
  rfl
#align affine_equiv.coe_const_vsub_symm AffineEquiv.coe_constVSub_symm

variable (P₁)

/-- The map `p ↦ v +ᵥ p` as an affine automorphism of an affine space.

Note that there is no need for an `AffineMap.constVAdd` as it is always an equivalence.
This is roughly to `DistribMulAction.toLinearEquiv` as `+ᵥ` is to `•`. -/
@[simps! apply linear]
def constVAdd (v : V₁) : P₁ ≃ᵃ[k] P₁ where
  toEquiv := Equiv.constVAdd P₁ v
  linear := LinearEquiv.refl _ _
  map_vadd' _ _ := vadd_comm _ _ _
#align affine_equiv.const_vadd AffineEquiv.constVAdd

@[simp]
theorem constVAdd_zero : constVAdd k P₁ 0 = AffineEquiv.refl _ _ :=
  ext <| zero_vadd _
#align affine_equiv.const_vadd_zero AffineEquiv.constVAdd_zero

@[simp]
theorem constVAdd_add (v w : V₁) :
    constVAdd k P₁ (v + w) = (constVAdd k P₁ w).trans (constVAdd k P₁ v) :=
  ext <| add_vadd _ _
#align affine_equiv.const_vadd_add AffineEquiv.constVAdd_add

@[simp]
theorem constVAdd_symm (v : V₁) : (constVAdd k P₁ v).symm = constVAdd k P₁ (-v) :=
  ext fun _ => rfl
#align affine_equiv.const_vadd_symm AffineEquiv.constVAdd_symm

/-- A more bundled version of `AffineEquiv.constVAdd`. -/
@[simps]
def constVAddHom : Multiplicative V₁ →* P₁ ≃ᵃ[k] P₁ where
  toFun v := constVAdd k P₁ (Multiplicative.toAdd v)
  map_one' := constVAdd_zero _ _
  map_mul' := constVAdd_add _ P₁
#align affine_equiv.const_vadd_hom AffineEquiv.constVAddHom

theorem constVAdd_nsmul (n : ℕ) (v : V₁) : constVAdd k P₁ (n • v) = constVAdd k P₁ v ^ n :=
  (constVAddHom k P₁).map_pow _ _
#align affine_equiv.const_vadd_nsmul AffineEquiv.constVAdd_nsmul

theorem constVAdd_zsmul (z : ℤ) (v : V₁) : constVAdd k P₁ (z • v) = constVAdd k P₁ v ^ z :=
  (constVAddHom k P₁).map_zpow _ _
#align affine_equiv.const_vadd_zsmul AffineEquiv.constVAdd_zsmul

section Homothety

variable {R V P : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AffineSpace V P]

/-- Fixing a point in affine space, homothety about this point gives a group homomorphism from (the
centre of) the units of the scalars into the group of affine equivalences. -/
def homothetyUnitsMulHom (p : P) : Rˣ →* P ≃ᵃ[R] P :=
  equivUnitsAffineMap.symm.toMonoidHom.comp <| Units.map (AffineMap.homothetyHom p)
#align affine_equiv.homothety_units_mul_hom AffineEquiv.homothetyUnitsMulHom

@[simp]
theorem coe_homothetyUnitsMulHom_apply (p : P) (t : Rˣ) :
    (homothetyUnitsMulHom p t : P → P) = AffineMap.homothety p (t : R) :=
  rfl
#align affine_equiv.coe_homothety_units_mul_hom_apply AffineEquiv.coe_homothetyUnitsMulHom_apply

@[simp]
theorem coe_homothetyUnitsMulHom_apply_symm (p : P) (t : Rˣ) :
    ((homothetyUnitsMulHom p t).symm : P → P) = AffineMap.homothety p (↑t⁻¹ : R) :=
  rfl
#align affine_equiv.coe_homothety_units_mul_hom_apply_symm AffineEquiv.coe_homothetyUnitsMulHom_apply_symm

@[simp]
theorem coe_homothetyUnitsMulHom_eq_homothetyHom_coe (p : P) :
    ((↑) : (P ≃ᵃ[R] P) → P →ᵃ[R] P) ∘ homothetyUnitsMulHom p =
      AffineMap.homothetyHom p ∘ ((↑) : Rˣ → R) :=
  funext fun _ => rfl
#align affine_equiv.coe_homothety_units_mul_hom_eq_homothety_hom_coe AffineEquiv.coe_homothetyUnitsMulHom_eq_homothetyHom_coe

end Homothety

variable {P₁}

open Function

/-- Point reflection in `x` as a permutation. -/
def pointReflection (x : P₁) : P₁ ≃ᵃ[k] P₁ :=
  (constVSub k x).trans (vaddConst k x)
#align affine_equiv.point_reflection AffineEquiv.pointReflection

theorem pointReflection_apply (x y : P₁) : pointReflection k x y = x -ᵥ y +ᵥ x :=
  rfl
#align affine_equiv.point_reflection_apply AffineEquiv.pointReflection_apply

@[simp]
theorem pointReflection_symm (x : P₁) : (pointReflection k x).symm = pointReflection k x :=
  toEquiv_injective <| Equiv.pointReflection_symm x
#align affine_equiv.point_reflection_symm AffineEquiv.pointReflection_symm

@[simp]
theorem toEquiv_pointReflection (x : P₁) :
    (pointReflection k x).toEquiv = Equiv.pointReflection x :=
  rfl
#align affine_equiv.to_equiv_point_reflection AffineEquiv.toEquiv_pointReflection

@[simp]
theorem pointReflection_self (x : P₁) : pointReflection k x x = x :=
  vsub_vadd _ _
#align affine_equiv.point_reflection_self AffineEquiv.pointReflection_self

theorem pointReflection_involutive (x : P₁) : Involutive (pointReflection k x : P₁ → P₁) :=
  Equiv.pointReflection_involutive x
#align affine_equiv.point_reflection_involutive AffineEquiv.pointReflection_involutive

set_option linter.deprecated false in
/-- `x` is the only fixed point of `pointReflection x`. This lemma requires
`x + x = y + y ↔ x = y`. There is no typeclass to use here, so we add it as an explicit argument. -/
theorem pointReflection_fixed_iff_of_injective_bit0 {x y : P₁} (h : Injective (bit0 : V₁ → V₁)) :
    pointReflection k x y = y ↔ y = x :=
  Equiv.pointReflection_fixed_iff_of_injective_bit0 h
#align affine_equiv.point_reflection_fixed_iff_of_injective_bit0 AffineEquiv.pointReflection_fixed_iff_of_injective_bit0

set_option linter.deprecated false in
theorem injective_pointReflection_left_of_injective_bit0 (h : Injective (bit0 : V₁ → V₁)) (y : P₁) :
    Injective fun x : P₁ => pointReflection k x y :=
  Equiv.injective_pointReflection_left_of_injective_bit0 h y
#align affine_equiv.injective_point_reflection_left_of_injective_bit0 AffineEquiv.injective_pointReflection_left_of_injective_bit0

theorem injective_pointReflection_left_of_module [Invertible (2 : k)] :
    ∀ y, Injective fun x : P₁ => pointReflection k x y :=
  injective_pointReflection_left_of_injective_bit0 k fun x y h => by
    rwa [bit0, bit0, ← two_smul k x, ← two_smul k y,
      (isUnit_of_invertible (2 : k)).smul_left_cancel] at h
#align affine_equiv.injective_point_reflection_left_of_module AffineEquiv.injective_pointReflection_left_of_module

theorem pointReflection_fixed_iff_of_module [Invertible (2 : k)] {x y : P₁} :
    pointReflection k x y = y ↔ y = x :=
  ((injective_pointReflection_left_of_module k y).eq_iff' (pointReflection_self k y)).trans eq_comm
#align affine_equiv.point_reflection_fixed_iff_of_module AffineEquiv.pointReflection_fixed_iff_of_module

end AffineEquiv

namespace LinearEquiv

/-- Interpret a linear equivalence between modules as an affine equivalence. -/
def toAffineEquiv (e : V₁ ≃ₗ[k] V₂) : V₁ ≃ᵃ[k] V₂ where
  toEquiv := e.toEquiv
  linear := e
  map_vadd' p v := e.map_add v p
#align linear_equiv.to_affine_equiv LinearEquiv.toAffineEquiv

@[simp]
theorem coe_toAffineEquiv (e : V₁ ≃ₗ[k] V₂) : ⇑e.toAffineEquiv = e :=
  rfl
#align linear_equiv.coe_to_affine_equiv LinearEquiv.coe_toAffineEquiv

end LinearEquiv

namespace AffineMap

open AffineEquiv

theorem lineMap_vadd (v v' : V₁) (p : P₁) (c : k) :
    lineMap v v' c +ᵥ p = lineMap (v +ᵥ p) (v' +ᵥ p) c :=
  (vaddConst k p).apply_lineMap v v' c
#align affine_map.line_map_vadd AffineMap.lineMap_vadd

theorem lineMap_vsub (p₁ p₂ p₃ : P₁) (c : k) :
    lineMap p₁ p₂ c -ᵥ p₃ = lineMap (p₁ -ᵥ p₃) (p₂ -ᵥ p₃) c :=
  (vaddConst k p₃).symm.apply_lineMap p₁ p₂ c
#align affine_map.line_map_vsub AffineMap.lineMap_vsub

theorem vsub_lineMap (p₁ p₂ p₃ : P₁) (c : k) :
    p₁ -ᵥ lineMap p₂ p₃ c = lineMap (p₁ -ᵥ p₂) (p₁ -ᵥ p₃) c :=
  (constVSub k p₁).apply_lineMap p₂ p₃ c
#align affine_map.vsub_line_map AffineMap.vsub_lineMap

theorem vadd_lineMap (v : V₁) (p₁ p₂ : P₁) (c : k) :
    v +ᵥ lineMap p₁ p₂ c = lineMap (v +ᵥ p₁) (v +ᵥ p₂) c :=
  (constVAdd k P₁ v).apply_lineMap p₁ p₂ c
#align affine_map.vadd_line_map AffineMap.vadd_lineMap

variable {R' : Type*} [CommRing R'] [Module R' V₁]

theorem homothety_neg_one_apply (c p : P₁) : homothety c (-1 : R') p = pointReflection R' c p := by
  -- porting note: added `()`, `_`, and `neg_vsub_eq_vsub_rev`
  simp [(homothety_apply), pointReflection_apply _, (neg_vsub_eq_vsub_rev)]
  -- 🎉 no goals
#align affine_map.homothety_neg_one_apply AffineMap.homothety_neg_one_apply

end AffineMap
