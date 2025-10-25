/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Small.Ring

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

universe u u' v v'

variable (R : Type u) [Ring R]

open CategoryTheory

variable (M : ModuleCat R)

/--
For any ring `R`, the center of `R` is isomorphic to `End (𝟭 (ModuleCat R))`, the endomorphism ring
of the identity functor on the category of `R`-modules.

Note: this is an auxilary construction, please use `Subring.centerEquivEndIdFunctor` instead.
-/
@[simps]
noncomputable def Subring.centerEquivEndIdFunctorAux :
    center R ≃+* End (𝟭 (ModuleCat.{u} R)) where
  toFun r := { app M := r • 𝟙 M }
  invFun f := centerToMulOpposite.symm <| centerCongr
    ((ModuleCat.of R R).endRingEquiv.trans ((Module.moduleEndSelf R)).symm)
    ⟨f.app (.of R R), mem_center_iff.mpr fun g ↦ (f.naturality _).symm⟩
  left_inv r := Subtype.ext <| show r.1 • (1 : R) = r.1 by simp
  right_inv f := by
    apply NatTrans.ext
    ext M (m : M)
    simpa [Subring.smul_def, ModuleCat.endRingEquiv] using
      congr($(f.naturality (ModuleCat.ofHom <| LinearMap.toSpanSingleton R M m)) (1 : R)).symm
  map_mul' x y := by
    apply NatTrans.ext
    ext M (m : M)
    simp only [Functor.id_obj, ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq]
    erw [End.mul_def] -- why is this simp lemma not firing?
    simp only [NatTrans.comp_app, Functor.id_obj, ModuleCat.hom_comp, ModuleCat.hom_smul,
      ModuleCat.hom_id, LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq, LinearMap.map_smul_of_tower]
    exact mul_smul x y m
  map_add' x y := by
    apply NatTrans.ext
    ext M (m : M)
    simp only [Functor.id_obj, ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq]
    rw [NatTrans.app_add] -- why is this simp lemma not firing?
    simp only [Functor.id_obj, ModuleCat.hom_add, ModuleCat.hom_smul, ModuleCat.hom_id,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    exact add_smul x y m

/--
For any ring `R`, the center of `R` is isomorphic to `End (𝟭 (ModuleCat R))`, the endomorphism ring
of the identity functor on the category of `R`-modules.
-/
noncomputable def Subring.centerEquivEndIdFunctor [Small.{v} R] :
    center R ≃+* End (𝟭 (ModuleCat.{v} R)) :=
  (centerCongr (Shrink.ringEquiv R).symm).trans <|
    Subring.centerEquivEndIdFunctorAux (Shrink R) |>.trans
    (Equivalence.endRingEquiv
      (e := ModuleCat.restrictScalarsEquivalenceOfRingEquiv (Shrink.ringEquiv R))
      (e' := ModuleCat.restrictScalarsEquivalenceOfRingEquiv (Shrink.ringEquiv R)) (by rfl)).symm

/--
For any two rings `R` and `S`, if the categories of `R`-modules and `S`-modules are equivalent, then
the center of `R` and the center of `S` agree as well.
-/
noncomputable def Subring.centerEquivOfModuleCatEquiv {R S : Type*} [CommRing R] [CommRing S]
    [Small.{v} R] [Small.{v'} S]
    (e : ModuleCat.{v} R ≌ ModuleCat.{v'} S) : center R ≃+* center S :=
  letI : e.functor.Additive := Functor.additive_of_preserves_binary_products e.functor
  (Subring.centerEquivEndIdFunctor R).trans <|
    (Equivalence.endRingEquiv (e := e) (e' := e) (by rfl)).trans
    (Subring.centerEquivEndIdFunctor S).symm

/--
For any two commutative rings `R` and `S`, if the categories of `R`-modules and `S`-modules are
equivalent, then `R` and `S` are isomorphic as rings.
-/
noncomputable def RingEquiv.ofModuleCatEquiv {R : Type u} {S : Type u'} [CommRing R] [CommRing S]
    [Small.{v} R] [Small.{v'} S]
    (e : ModuleCat.{v} R ≌ ModuleCat.{v'} S) : R ≃+* S :=
  letI : e.functor.Additive := Functor.additive_of_preserves_binary_products e.functor
  let i₁ : R ≃+* (⊤ : Subring R) := Subring.topEquiv.symm
  let i₂ : (⊤ : Subring R) ≃+* Subring.center R := Subring.center_eq_top R ▸ .refl _
  let i₃ : Subring.center S ≃+* (⊤ : Subring S) := Subring.center_eq_top S ▸ .refl _
  let i₄ : (⊤ : Subring S) ≃+* S := Subring.topEquiv
  i₁.trans <| i₂.trans <| Subring.centerEquivOfModuleCatEquiv e |>.trans <| i₃.trans i₄
