/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Bijection
/-!

# Ext Commute with Ulift Functor

-/

universe w w' u u' v v'

variable {R : Type u} [CommRing R]

open CategoryTheory Abelian

section

variable [UnivLE.{v, w}] [UnivLE.{max v v', w'}]

instance hasExt_of_small'' [Small.{v} R] : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

noncomputable def ModuleCat.extUliftLinearEquiv [Small.{v} R] (M N : ModuleCat.{v} R) (n : ℕ) :
    letI : Small.{max v v'} R := small_lift R
    Ext.{w} M N n ≃ₗ[R] Ext.{w'} ((uliftFunctor.{u, v, v'} R).obj M)
    ((uliftFunctor.{u, v, v'} R).obj N) n :=
  letI : Small.{max v v'} R := small_lift R
  LinearEquiv.ofBijective (Functor.mapExtLinearMap.{w, w'} (uliftFunctor.{u, v, v'} R) R M N n)
    (Functor.mapExt_bijective_of_preservesProjectiveObjects.{w, w'}
    (uliftFunctor.{u, v, v'} R) (fullyFaithfulUliftFunctor.{u, v, v'} R) M N n)

lemma ModuleCat.extUliftLinearEquiv_toLinearMap [Small.{v} R] (M N : ModuleCat.{v} R) (n : ℕ) :
    letI : Small.{max v v'} R := small_lift R
    ModuleCat.extUliftLinearEquiv.{w, w', u, v, v'} M N n =
    (Functor.mapExtLinearMap.{w, w'} (uliftFunctor.{u, v, v'} R) R M N n) := rfl

end

section

variable [UnivLE.{v, w}] [UnivLE.{v', w'}]

def extLinearEquivOfLinearEquiv [Small.{v} R] [Small.{v'} R]
    {M N : ModuleCat.{v} R} {M' N' : ModuleCat.{v'} R}
    (e1 : M ≃ₗ[R] M') (e2 : N ≃ₗ[R] N') (n : ℕ) :
    Ext.{w} M N n ≃ₗ[R] Ext.{w'} M' N' n := sorry

end

section restrictScalars

variable {R' : Type u'} [CommRing R']

section

variable (f : R →+* R')

instance : (ModuleCat.restrictScalars.{v} f).Additive where
  map_add := by simp

lemma ModuleCat.restrictScalars_map_exact (S : ShortComplex (ModuleCat.{v} R')) (h : S.Exact) :
    (S.map (ModuleCat.restrictScalars.{v} f)).Exact := by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact h

instance : Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{v} f) := by
  have := ((CategoryTheory.Functor.exact_tfae (ModuleCat.restrictScalars.{v} f)).out 1 3).mp
    (ModuleCat.restrictScalars_map_exact f)
  exact this.1

instance : Limits.PreservesFiniteColimits (ModuleCat.restrictScalars.{v} f) := by
  have := ((CategoryTheory.Functor.exact_tfae (ModuleCat.restrictScalars.{v} f)).out 1 3).mp
    (ModuleCat.restrictScalars_map_exact f)
  exact this.2

end

section

variable (e : R ≃+* R')

variable [UnivLE.{v, w}] [UnivLE.{v, w'}]

namespace ModuleCat

noncomputable def extRestrictScalarsSemiLinearMap [Small.{v} R] [Small.{v} R']
    (M N : ModuleCat.{v} R') (n : ℕ) :
    letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
    letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
    Ext.{w} M N n →ₛₗ[e.symm.toRingHom] Ext.{w'} ((ModuleCat.restrictScalars e.toRingHom).obj M)
    ((ModuleCat.restrictScalars e.toRingHom).obj N) n where
  __ := Functor.mapExtAddHom.{w, w'} (ModuleCat.restrictScalars.{v} e.toRingHom) M N n
  map_smul' r x := by
    simp only [RingEquiv.toRingHom_eq_coe, Functor.mapExtAddHom, Ext.smul_eq_comp_mk₀,
      ZeroHom.toFun_eq_coe, ZeroHom.coe_mk, RingHom.coe_coe]
    rw [Ext.mapExt_comp_eq_comp_mapExt, Ext.mapExt_mk₀_eq_mk₀_map]
    congr 2
    ext
    simp

noncomputable def extRestrictScalarsSemiLinearEquiv [Small.{v} R] [Small.{v} R']
    (M N : ModuleCat.{v} R') (n : ℕ) :
    letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
    letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
    Ext.{w} M N n ≃ₛₗ[e.symm.toRingHom] Ext.{w'} ((ModuleCat.restrictScalars e.toRingHom).obj M)
    ((ModuleCat.restrictScalars e.toRingHom).obj N) n :=
  let _ : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let _ : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
  LinearEquiv.ofBijective (ModuleCat.extRestrictScalarsSemiLinearMap.{w, w'} e M N n)
    (Functor.mapExt_bijective_of_preservesProjectiveObjects.{w, w'}
    (ModuleCat.restrictScalars.{v} e.toRingHom)
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).fullyFaithfulFunctor M N n)

noncomputable def iso_restrictScalars {M' : ModuleCat.{v} R'} {M : ModuleCat.{v} R}
    (e' : letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
          letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
          M ≃ₛₗ[e.toRingHom] M') : M ≅ ((ModuleCat.restrictScalars e.toRingHom).obj M') :=
  let e : M ≃ₗ[R] ((ModuleCat.restrictScalars e.toRingHom).obj M') := {
    __ := e'
    map_smul' r m := by simp }
  e.toModuleIso

noncomputable def extSemiLinearEquivOfSemiLinearEquiv_equal_universe [Small.{v} R] [Small.{v} R']
    {M N : ModuleCat.{v} R} {M' N' : ModuleCat.{v} R'}
    (e1 : letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
          letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
          M ≃ₛₗ[e.toRingHom] M')
    (e2 : letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
          letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
          N ≃ₛₗ[e.toRingHom] N')
    (n : ℕ) : letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
    letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
    Ext.{w} M' N' n ≃ₛₗ[e.symm.toRingHom] Ext.{w'} M N n :=
  let e3 : Ext.{w'} ((ModuleCat.restrictScalars e.toRingHom).obj M')
    ((ModuleCat.restrictScalars e.toRingHom).obj N') n ≃ₗ[R] Ext.{w'} M N n := {
      __ := (((extFunctorObj.{w'} ((ModuleCat.restrictScalars e.toRingHom).obj M') n).mapIso
        (ModuleCat.iso_restrictScalars e e2).symm).trans (((extFunctor.{w'} n).mapIso
        (ModuleCat.iso_restrictScalars e e1).op).app N)).addCommGroupIsoToAddEquiv
      map_smul' r' x := by simp [Iso.addCommGroupIsoToAddEquiv] }
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
  (ModuleCat.extRestrictScalarsSemiLinearEquiv.{w, w'} e M' N' n).trans e3

end ModuleCat

end

section

variable (e : R ≃+* R') [UnivLE.{v, w}] [UnivLE.{v', w'}]

noncomputable def ModuleCat.extSemiLinearEquivOfSemiLinearEquiv [Small.{v} R] [Small.{v'} R']
    {M N : ModuleCat.{v} R} {M' N' : ModuleCat.{v'} R'}
    (e1 : letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
          letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
          M ≃ₛₗ[e.toRingHom] M')
    (e2 : letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
          letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
          N ≃ₛₗ[e.toRingHom] N')
    (n : ℕ) : letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
    letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
    Ext.{w'} M' N' n ≃ₛₗ[e.symm.toRingHom] Ext.{w} M N n :=
  letI : Small.{max v v'} R := small_lift R
  letI : Small.{max v v'} R' := small_lift R'
  let e3 : Ext.{w} M N n ≃ₗ[R] Ext.{max v v'} ((uliftFunctor.{u, v, v'} R).obj M)
    ((uliftFunctor.{u, v, v'} R).obj N) n := ModuleCat.extUliftLinearEquiv.{w, max v v'} M N n
  let e4 : Ext.{w'} M' N' n ≃ₗ[R'] Ext.{max v v'} ((uliftFunctor.{u', v', v} R').obj M')
    ((uliftFunctor.{u', v', v} R').obj N') n := ModuleCat.extUliftLinearEquiv.{w', max v v'} M' N' n
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
  let e1' : (uliftFunctor.{u, v, v'} R).obj M ≃ₛₗ[e.toRingHom]
    (uliftFunctor.{u', v', v} R').obj M' :=
    (ULift.moduleEquiv.trans e1).trans ULift.moduleEquiv.symm
  let e2' : (uliftFunctor.{u, v, v'} R).obj N ≃ₛₗ[e.toRingHom]
    (uliftFunctor.{u', v', v} R').obj N' :=
    (ULift.moduleEquiv.trans e2).trans ULift.moduleEquiv.symm
  (e4.trans (extSemiLinearEquivOfSemiLinearEquiv_equal_universe e e1' e2' n)).trans e3.symm

end

end restrictScalars
