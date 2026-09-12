/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.BaseChange
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Gorenstein.Defs
public import Mathlib.RingTheory.Regular.InjectiveDimension

/-!

# A Noetherian local ring is Gorenstein iff its completion is Gorenstein

-/

universe u

public section

variable (R : Type u) [CommRing R]

open CategoryTheory Abelian IsLocalRing

/-- The base change map `R ⧸ I → S ⧸ IS ` -/
def quotientIsBaseChangeMap' (S : Type*) [CommRing S] [Algebra R S] (I : Ideal R) :
    R ⧸ I →ₗ[R] S ⧸ I.map (algebraMap R S) :=
  Submodule.liftQ I ((Ideal.Quotient.mkₐ R (I.map (algebraMap R S))).toLinearMap.comp
    (Algebra.linearMap R S)) (fun x hx ↦ by
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, AlgHom.coe_toLinearMap,
        Ideal.Quotient.mkₐ_eq_mk, Function.comp_apply, Algebra.linearMap_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem (algebraMap R S) hx))

lemma quotientIsBaseChangeMap'_isBaseChange (S : Type*) [CommRing S] [Algebra R S] (I : Ideal R) :
    IsBaseChange S (quotientIsBaseChangeMap' R S I) := by
  apply IsBaseChange.of_equiv (Ideal.qoutMapEquivTensorQout S).symm
  intro x
  rcases Submodule.Quotient.mk_surjective _ x with ⟨y, rfl⟩
  simp only [quotientIsBaseChangeMap', Submodule.liftQ_apply]
  simp [Ideal.qoutMapEquivTensorQout, Algebra.smul_def]

lemma isBaseChange_adicCompletion_subsingleton_iff [IsLocalRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [AddCommGroup N] [Module R N]
    [Module (AdicCompletion (maximalIdeal R) R) N]
    [IsScalarTower R (AdicCompletion (maximalIdeal R) R) N]
    {f : M →ₗ[R] N} (isb : IsBaseChange (AdicCompletion (maximalIdeal R) R) f) :
    Subsingleton M ↔ Subsingleton N := by
  rw [← isb.equiv.subsingleton_congr]
  refine ⟨fun _ ↦ inferInstance, fun h ↦ ?_⟩
  rw [← subsingleton_tensorProduct (R := R)]
  have surj : Function.Surjective (AdicCompletion.evalOneₐ (maximalIdeal R)).toLinearMap :=
    AdicCompletion.evalOneₐ_surjective (maximalIdeal R)
  exact (LinearMap.rTensor_surjective M surj).subsingleton

variable [IsNoetherianRing R] [IsLocalRing R]

set_option backward.isDefEq.respectTransparency false in
lemma isGorensteinLocalRing_iff_exists' :
    IsGorensteinLocalRing R ↔ ∃ n, ∀ i ≥ n, Subsingleton
    (Ext (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) i) := by
  have (a : WithBot ℕ∞) : a ≠ ⊤ ↔ ∃ (n : ℕ), a < n := by
    induction a with
    | bot => simp
    | coe a =>
      induction a with
      | top => simp
      | coe a => simpa [-ENat.WithBot.coe_eq_natCast] using ⟨a + 1, Nat.cast_lt.mpr (lt_add_one a)⟩
  simp only [isGorensteinLocalRing_def, this, ge_iff_le]
  apply exists_congr (fun n ↦ ?_)
  rw [injectiveDimension_lt_iff_of_finite (ModuleCat.of R R) n]
  congr! 2
  exact (((extFunctor _).mapIso (Shrink.linearEquiv.{u} R (R ⧸ maximalIdeal R)).toModuleIso.op).app
    (ModuleCat.of R R)).symm.addCommGroupIsoToAddEquiv.subsingleton_congr

theorem IsGorensteinLocalRing.iff_adicCompletion :
    IsGorensteinLocalRing R ↔ IsGorensteinLocalRing (AdicCompletion (maximalIdeal R) R) := by
  let R' := AdicCompletion (maximalIdeal R) R
  let f := quotientIsBaseChangeMap' R R' (maximalIdeal R)
  have isbf : IsBaseChange R' f := quotientIsBaseChangeMap'_isBaseChange R R' (maximalIdeal R)
  let res' := R' ⧸ Ideal.map (algebraMap R R') (maximalIdeal R)
  let e : (R' ⧸ maximalIdeal R') ≃ₗ[R'] res' :=
    Submodule.quotEquivOfEq _ _ AdicCompletion.maximalIdeal_eq_map
  rw [isGorensteinLocalRing_iff_exists', isGorensteinLocalRing_iff_exists']
  congr! 4
  rename_i i _
  let eExt := ((extFunctor i).mapIso e.toModuleIso.op).app (ModuleCat.of R' R')
  apply Iff.trans _ eExt.addCommGroupIsoToAddEquiv.subsingleton_congr
  simp only [extFunctor_obj, extFunctorObj_obj_coe]
  let isbExt := Ext.isBaseChange R' (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R)
    (MS := ModuleCat.of R' res') (NS := ModuleCat.of R' R') f isbf
    (Algebra.linearMap R R') (IsBaseChange.linearMap R R') i
  exact isBaseChange_adicCompletion_subsingleton_iff R isbExt
