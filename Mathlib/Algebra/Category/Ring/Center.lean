/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Small.Module

/-!
# A categorical description of the center of a ring

In this file we prove that the center of a ring `R` is isomorphic to `End (𝟭 R-Mod)` the
endomorphism ring of the identity functor on the category of `R`-modules. Consequently, the ring
structure of a commutative ring is completely determined by its module category.

## Main results

- `Subring.centerEquivEndIdFunctor`: the center of a ring `R` is isomorphic to `End (𝟭 R-Mod)`.
- `RingEquiv.ofModuleCatEquiv`: if two commutative rings have equivalent module categories, they are
  isomorphic as rings.

-/

universe v v'

variable (R : Type*) [Ring R]

open CategoryTheory

/--
For any ring `R`, the center of `R` is isomorphic to `End (𝟭 (ModuleCat R))`, the endomorphism ring
of the identity functor on the category of `R`-modules.
-/
@[simps]
noncomputable def Subring.centerEquivEndIdFunctor [Small.{v} R] :
    center R ≃+* End (𝟭 (ModuleCat.{v} R)) where
  toFun x :=
  { app M := ModuleCat.ofHom
      { toFun := (x.1 • ·)
        map_add' := by aesop
        map_smul' r := by simp [← mul_smul, mem_center_iff.1 x.2 r] } }
  invFun f := centerMulOppositeEquiv <| centerCongr
    ((ModuleCat.of R (Shrink.{v} R)).endRingEquiv.trans
      ((Module.moduleEndSelf R).trans (linearEquivShrink R R).conjRingEquiv).symm)
    ⟨f.app _, mem_center_iff.mpr fun g ↦ (f.naturality _).symm⟩
  left_inv r := Subtype.ext <| show (linearEquivShrink ..).symm (r.1 • _) = _ by
    rw [map_smul, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply, smul_eq_mul, mul_one]
  right_inv f := by
    apply NatTrans.ext
    ext M (m : M)
    simpa [linearEquivShrink, Equiv.linearEquiv] using
      congr($(f.naturality (X := .of R <| Shrink.{v} R) (Y := .of R M) <|
        ModuleCat.ofHom <| LinearMap.toSpanSingleton R M m ∘ₗ (linearEquivShrink R R).symm).hom
      (equivShrink R 1)).symm
  map_mul' x y := by
    apply NatTrans.ext
    ext M (m : M)
    exact mul_smul x.1 y.1 m
  map_add' x y := by
    apply NatTrans.ext
    ext M (m : M)
    exact add_smul x.1 y.1 m

/--
For any two commutative rings `R` and `S`, if the categories of `R`-modules and `S`-modules are
equivalent, then `R` and `S` are isomorphic as rings.
-/
noncomputable def RingEquiv.ofModuleCatEquiv {R S : Type*} [CommRing R] [CommRing S]
    [Small.{v} R] [Small.{v'} S]
    (e : ModuleCat.{v} R ≌ ModuleCat.{v'} S) : R ≃+* S :=
  letI : e.functor.Additive := Functor.additive_of_preserves_binary_products e.functor
  let i₁ : R ≃+* (⊤ : Subring R) := Subring.topEquiv.symm
  let i₂ : (⊤ : Subring R) ≃+* Subring.center R := Subring.center_eq_top R ▸ .refl _
  let i₃ : End (𝟭 (ModuleCat.{v} R)) ≃+* End (𝟭 (ModuleCat.{v'} S)) :=
    Equivalence.endRingEquiv (e := e) (e' := e) (by rfl)
  let i₄ : Subring.center S ≃+* (⊤ : Subring S) := Subring.center_eq_top S ▸ .refl _
  let i₅ : (⊤ : Subring S) ≃+* S := Subring.topEquiv
  i₁.trans <| i₂.trans <| (Subring.centerEquivEndIdFunctor R).trans <|
    i₃.trans <| (Subring.centerEquivEndIdFunctor S).symm.trans <| i₄.trans i₅
