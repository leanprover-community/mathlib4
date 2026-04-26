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

variable {R' : Type u'} [CommRing R']

variable (e : R ≃+* R')

namespace ModuleCat

attribute [local instance] RingHomInvPair.of_ringEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The forward function of `ModuleCat.extRestrictScalarsSemiLinearEquiv`. -/
noncomputable def extRestrictScalarsSemiLinearMap [Small.{v} R] [Small.{v} R']
    (M N : ModuleCat.{v} R') (n : ℕ) : Ext M N n →ₛₗ[RingHomClass.toRingHom e.symm]
    Ext ((ModuleCat.restrictScalars (RingHomClass.toRingHom e)).obj M)
    ((ModuleCat.restrictScalars (RingHomClass.toRingHom e)).obj N) n where
  __ := (ModuleCat.restrictScalars.{v} (RingHomClass.toRingHom e)).mapExtAddHom M N n
  map_smul' r x := by
    simp only [Functor.mapExtAddHom, Ext.smul_eq_comp_mk₀, Ext.mapExactFunctor_comp,
      Ext.mapExactFunctor_mk₀]
    congr 2
    ext
    simp

lemma extRestrictScalarsSemiLinearMap_toAddMonoidHom [Small.{v} R] [Small.{v} R']
    (M N : ModuleCat.{v} R') (n : ℕ) : extRestrictScalarsSemiLinearMap e M N n =
    (ModuleCat.restrictScalars.{v} (RingHomClass.toRingHom e)).mapExtAddHom M N n :=
  rfl

/-- For `R'` module `M N` and ring isomorphism `R ≃+* R'`,
the semi-linear equivalence `Ext (↑R M) (↑R N) n ≃ Ext M N n` -/
noncomputable def extRestrictScalarsSemiLinearEquiv [Small.{v} R] [Small.{v} R']
    (M N : ModuleCat.{v} R') (n : ℕ) : Ext M N n ≃ₛₗ[RingHomClass.toRingHom e.symm]
    Ext ((ModuleCat.restrictScalars (RingHomClass.toRingHom e)).obj M)
    ((ModuleCat.restrictScalars (RingHomClass.toRingHom e)).obj N) n :=
  haveI : (restrictScalars (RingHomClass.toRingHom e)).IsEquivalence :=
    restrictScalars_isEquivalence_of_ringEquiv e
  LinearEquiv.ofBijective (ModuleCat.extRestrictScalarsSemiLinearMap e M N n)
    (Functor.mapExt_bijective_of_preservesProjectiveObjects
    (ModuleCat.restrictScalars.{v} (RingHomClass.toRingHom e)) M N n)

set_option backward.isDefEq.respectTransparency false in
/-- Given semi linear equivalence `M ≃ M'` and `N ≃ N'` with respect to `R ≃+* R'`
within same universe, the semi linear equivalence `Ext M N n ≃ Ext M' N' n`. -/
noncomputable def extSemiLinearEquivOfSemiLinearEquiv [Small.{v} R] [Small.{v} R']
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
