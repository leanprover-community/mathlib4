/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!

# Ext Commute with Ulift Functor

In this file, we prove `Ext` commute with ulift functor, then use this to obtain
compatibility of `Ext` with (semi) linear equiv of general universe level.

-/

@[expose] public section

universe u u' v v'

variable {R : Type u} [CommRing R]

open CategoryTheory Abelian

section

/-- The linear equivalence `Ext M N n ≃ₗ[R] Ext (ULift M) (ULift N) n`. -/
noncomputable def ModuleCat.extUliftLinearEquiv [Small.{v} R] (M N : ModuleCat.{v} R) (n : ℕ) :
    haveI : Small.{max v v'} R := small_lift R
    Ext M N n ≃ₗ[R] Ext ((uliftFunctor.{v', v} R).obj M)
    ((uliftFunctor.{v', v} R).obj N) n :=
  haveI : Small.{max v v'} R := small_lift R
  LinearEquiv.ofBijective (Functor.mapExtLinearMap (uliftFunctor.{v', v} R) R M N n)
    (Functor.mapExt_bijective_of_preservesProjectiveObjects
    (uliftFunctor.{v', v} R) M N n)

lemma ModuleCat.extUliftLinearEquiv_apply [Small.{v} R] (M N : ModuleCat.{v} R) (n : ℕ) :
    haveI : Small.{max v v'} R := small_lift R
    ModuleCat.extUliftLinearEquiv M N n =
      (Functor.mapExtLinearMap (uliftFunctor.{v', v} R) R M N n) :=
  rfl

end

section

variable {M N : ModuleCat.{v} R} {M' N' : ModuleCat.{v'} R}

/-- If two modules are linear equivalent then their `ULift` are isomorphic in `ModuleCat`. -/
def ModuleCat.uliftFunctorObjIso (e1 : M ≃ₗ[R] M') :
    (uliftFunctor.{v'} R).obj M ≅ (uliftFunctor.{v} R).obj M' :=
  ((ULift.moduleEquiv.trans e1).trans ULift.moduleEquiv.symm).toModuleIso

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for the connection of `ModuleCat.extUliftLinearEquiv`. -/
noncomputable def ModuleCat.extUliftFunctorObjIso
    [Small.{max v v'} R] (e1 : M ≃ₗ[R] M') (e2 : N ≃ₗ[R] N') (n : ℕ) :
    Ext ((ModuleCat.uliftFunctor.{v'} R).obj M) ((ModuleCat.uliftFunctor.{v'} R).obj N) n ≃ₗ[R]
    Ext ((ModuleCat.uliftFunctor.{v} R).obj M') ((ModuleCat.uliftFunctor.{v} R).obj N') n := {
  __ := ((((extFunctor n).obj ⟨(ModuleCat.uliftFunctor.{v'} R).obj M⟩).mapIso
    (ModuleCat.uliftFunctorObjIso e2)).trans (((extFunctor n).mapIso
      (ModuleCat.uliftFunctorObjIso e1).symm.op).app
        ((ModuleCat.uliftFunctor.{v} R).obj N'))).addCommGroupIsoToAddEquiv
  map_smul' r' x := by simp [Iso.addCommGroupIsoToAddEquiv] }

/-- Given linear equivalence of `R`-modules `M ≃ₗ[R] M'` and `N ≃ₗ[R] N'`,
the linear equivalence `Ext M N n ≃ₗ[R] Ext M' N' n`. -/
noncomputable def ModuleCat.extLinearEquivOfLinearEquiv [Small.{v} R] [Small.{v'} R]
    (e1 : M ≃ₗ[R] M') (e2 : N ≃ₗ[R] N') (n : ℕ) : Ext M N n ≃ₗ[R] Ext M' N' n :=
  haveI : Small.{max v v'} R := small_lift R
  ((ModuleCat.extUliftLinearEquiv M N n).trans (ModuleCat.extUliftFunctorObjIso e1 e2 n)).trans
    (ModuleCat.extUliftLinearEquiv M' N' n).symm

end

section restrictScalars

variable {R' : Type u'} [CommRing R']

section

variable (e : R ≃+* R')

namespace ModuleCat

attribute [local instance] RingHomInvPair.of_ringEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The forward function of `ModuleCat.extRestrictScalarsSemiLinearEquiv`. -/
noncomputable def extRestrictScalarsSemiLinearMap [Small.{v} R] [Small.{v} R']
    (M N : ModuleCat.{v} R') (n : ℕ) : Ext M N n →ₛₗ[RingHomClass.toRingHom e.symm]
    Ext ((ModuleCat.restrictScalars (RingHomClass.toRingHom e)).obj M)
    ((ModuleCat.restrictScalars (RingHomClass.toRingHom e)).obj N) n where
  __ := Functor.mapExtAddHom (ModuleCat.restrictScalars.{v} e.toRingHom) M N n
  map_smul' r x := by
    simp only [RingEquiv.toRingHom_eq_coe, Functor.mapExtAddHom, Ext.smul_eq_comp_mk₀,
      ZeroHom.toFun_eq_coe, ZeroHom.coe_mk, RingHom.coe_coe]
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
    congr 2
    ext
    simp

instance : (restrictScalars (RingHomClass.toRingHom e)).IsEquivalence :=
  restrictScalars_isEquivalence_of_ringEquiv e

/-- For `R'` module `M N` and ring isomorphism `R ≃+* R'`,
the semi-linear equivalence `Ext (↑R M) (↑R N) n ≃ Ext M N n` -/
noncomputable def extRestrictScalarsSemiLinearEquiv [Small.{v} R] [Small.{v} R']
    (M N : ModuleCat.{v} R') (n : ℕ) : Ext M N n ≃ₛₗ[RingHomClass.toRingHom e.symm]
    Ext ((ModuleCat.restrictScalars (RingHomClass.toRingHom e)).obj M)
    ((ModuleCat.restrictScalars (RingHomClass.toRingHom e)).obj N) n :=
  LinearEquiv.ofBijective (ModuleCat.extRestrictScalarsSemiLinearMap e M N n)
    (Functor.mapExt_bijective_of_preservesProjectiveObjects
    (ModuleCat.restrictScalars.{v} (RingHomClass.toRingHom e)) M N n)

/-- Given semi linear equiv `M ≃ M'`, the categorical isomorphism `M ≅ ↑R M'` -/
noncomputable def isoRestrictScalars {M' : ModuleCat.{v} R'} {M : ModuleCat.{v} R}
    (e' : M ≃ₛₗ[RingHomClass.toRingHom e] M') :
    M ≅ ((ModuleCat.restrictScalars (RingHomClass.toRingHom e)).obj M') :=
  let e : M ≃ₗ[R] ((ModuleCat.restrictScalars (RingHomClass.toRingHom e)).obj M') := {
    __ := e'
    map_smul' r m := by simp }
  e.toModuleIso

set_option backward.isDefEq.respectTransparency false in
/-- Given semi linear equivalence `M ≃ M'` and `N ≃ N'` with respect to `R ≃+* R'`
within same universe, the semi linear equivalence `Ext M N n ≃ Ext M' N' n`. -/
noncomputable def extSemiLinearEquivOfSemiLinearEquivEqualUniverse [Small.{v} R] [Small.{v} R']
    {M N : ModuleCat.{v} R} {M' N' : ModuleCat.{v} R'}
    (e1 : M ≃ₛₗ[RingHomClass.toRingHom e] M') (e2 : N ≃ₛₗ[RingHomClass.toRingHom e] N')
    (n : ℕ) :  Ext M' N' n ≃ₛₗ[RingHomClass.toRingHom e.symm] Ext M N n :=
  let e3 : Ext ((ModuleCat.restrictScalars (RingHomClass.toRingHom e)).obj M')
    ((ModuleCat.restrictScalars (RingHomClass.toRingHom e)).obj N') n ≃ₗ[R] Ext M N n := {
      __ := ((((extFunctor n).obj
        ⟨(ModuleCat.restrictScalars (RingHomClass.toRingHom e)).obj M'⟩).mapIso
          (ModuleCat.isoRestrictScalars e e2).symm).trans (((extFunctor n).mapIso
            (ModuleCat.isoRestrictScalars e e1).op).app N)).addCommGroupIsoToAddEquiv
      map_smul' r' x := by simp [Iso.addCommGroupIsoToAddEquiv] }
  (ModuleCat.extRestrictScalarsSemiLinearEquiv e M' N' n).trans e3

end ModuleCat

end

section

variable (e : R ≃+* R')

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- Given semi linear equivalence `M ≃ M'` and `N ≃ N'` with respect to `R ≃+* R'`,
the semi linear equivalence `Ext M N n ≃ Ext M' N' n`. -/
noncomputable def ModuleCat.extSemiLinearEquivOfSemiLinearEquiv [Small.{v} R] [Small.{v'} R']
    {M N : ModuleCat.{v} R} {M' N' : ModuleCat.{v'} R'}
    (e1 : M ≃ₛₗ[RingHomClass.toRingHom e] M') (e2 : N ≃ₛₗ[RingHomClass.toRingHom e] N')
    (n : ℕ) : Ext M' N' n ≃ₛₗ[RingHomClass.toRingHom e.symm] Ext M N n :=
  haveI : Small.{max v v'} R := small_lift R
  haveI : Small.{max v v'} R' := small_lift R'
  let e1' : (uliftFunctor.{v'} R).obj M ≃ₛₗ[RingHomClass.toRingHom e]
    (uliftFunctor.{v} R').obj M' :=
    (ULift.moduleEquiv.trans e1).trans ULift.moduleEquiv.symm
  let e2' : (uliftFunctor.{v'} R).obj N ≃ₛₗ[RingHomClass.toRingHom e]
    (uliftFunctor.{v} R').obj N' :=
    (ULift.moduleEquiv.trans e2).trans ULift.moduleEquiv.symm
  ((ModuleCat.extUliftLinearEquiv M' N' n).trans
    (extSemiLinearEquivOfSemiLinearEquivEqualUniverse e e1' e2' n)).trans
      (ModuleCat.extUliftLinearEquiv M N n).symm

end

end restrictScalars
