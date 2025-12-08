/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.QuasiFinite

/-!

# The meta properties of quasi-finite ring homomorphisms.

-/

@[expose] public section


universe u

namespace RingHom

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- A ring hom `R →+* S` is étale, if `S` is an étale `R`-algebra. -/
@[algebraize RingHom.QuasiFinite.toAlgebra]
def QuasiFinite {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  @Algebra.QuasiFinite R S _ _ f.toAlgebra

/-- Helper lemma for the `algebraize` tactic -/
lemma QuasiFinite.toAlgebra {f : R →+* S} (hf : QuasiFinite f) :
    @Algebra.QuasiFinite R S _ _ f.toAlgebra := hf

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

lemma quasiFinite_algebraMap [Algebra R S] :
    (algebraMap R S).QuasiFinite ↔ Algebra.QuasiFinite R S := by
  rw [RingHom.QuasiFinite, toAlgebra_algebraMap]

lemma QuasiFinite.comp {f : S →+* T} {g : R →+* S} (hf : f.QuasiFinite) (hg : g.QuasiFinite) :
    (f.comp g).QuasiFinite := by
  algebraize [f, g, (f.comp g)]
  exact .trans R S T

lemma QuasiFinite.of_comp {f : S →+* T} {g : R →+* S} (h : (f.comp g).QuasiFinite) :
    f.QuasiFinite := by
  algebraize [f, g, (f.comp g)]
  exact .of_restrictScalars R S T

lemma QuasiFinite.stableUnderComposition : StableUnderComposition QuasiFinite :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ comp hg hf

lemma QuasiFinite.of_surjective {f : R →+* S} (hf : Function.Surjective f) : f.QuasiFinite := by
  algebraize [f]
  exact .of_surjective_algHom (Algebra.ofId R S) hf

lemma QuasiFinite.respectsIso : RespectsIso QuasiFinite :=
  stableUnderComposition.respectsIso fun e ↦ .of_surjective (f := e.toRingHom) e.surjective

lemma QuasiFinite.isStableUnderBaseChange : IsStableUnderBaseChange QuasiFinite := by
  refine .mk respectsIso ?_
  introv H
  rw [quasiFinite_algebraMap] at H ⊢
  infer_instance

open TensorProduct in
/-- If `T` is both a finite type `R`-algebra, and the localization of an integral `R`-algebra,
then `T` is quasi-finite over `R` -/
lemma Algebra.QuasiFinite.of_isIntegral_of_finiteType
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] [Algebra.IsIntegral R S] [Algebra.FiniteType R T]
    (s : S) [IsLocalization.Away s T] : Algebra.QuasiFinite R T := by
  let A := Algebra.adjoin R {s}
  let sA : A := ⟨s, Algebra.subset_adjoin (by simp)⟩
  let f : Localization.Away sA →+* T := IsLocalization.Away.lift sA (g := algebraMap _ _)
    (IsLocalization.Away.algebraMap_isUnit s)
  let := f.toAlgebra
  let : Algebra A (Localization.Away sA) := OreLocalization.instAlgebra
  let : SMul A (Localization.Away sA) := Algebra.toSMul
  let : MulAction A (Localization.Away sA) := Algebra.toModule.toDistribMulAction.toMulAction
  have : IsScalarTower R A (Localization.Away sA) := OreLocalization.instIsScalarTower
  have : IsScalarTower A (Localization.Away sA) T :=
    .of_algebraMap_eq (by simp [f, RingHom.algebraMap_toAlgebra, A])
  have : IsScalarTower R (Localization.Away sA) T := .to₁₃₄ R A (Localization.Away sA) T
  have : Algebra.IsIntegral (Localization.Away sA) T := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers s) x
    have : _root_.IsIntegral (Localization.Away sA) (algebraMap S T x) :=
      (Algebra.IsIntegral.isIntegral (R := R) x).algebraMap.tower_top
    convert this.smul (Localization.Away.invSelf sA ^ n)
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    simp only [map_pow, Algebra.smul_mul_assoc]
    trans (sA • Localization.Away.invSelf sA) ^ n • (algebraMap S T x)
    · simp [Algebra.smul_def, -map_pow, Localization.Away.invSelf, Localization.mk_eq_mk']
    · simp only [Algebra.smul_def, map_pow, map_mul, mul_pow,
        ← IsScalarTower.algebraMap_apply, Subalgebra.algebraMap_def, sA]
      ring
  have : Module.Finite (Localization.Away sA) T :=
    have : Algebra.FiniteType (Localization.Away sA) T := .of_restrictScalars_finiteType R _ _
    Algebra.IsIntegral.finite
  have : Module.Finite R A :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral _)
  have : Algebra.QuasiFinite R (Localization.Away sA) := .of_isLocalization (.powers sA)
  exact .trans _ (Localization.Away sA) _

open TensorProduct in
/-- If `T` is both a finite type `R`-algebra, and the localization of an integral `R`-algebra,
then `T` is quasi-finite over `R` -/
lemma QuasiFinite.of_isIntegral_of_finiteType
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {f : R →+* S} (hf : f.IsIntegral)
    {g : R →+* T} (hg : g.FiniteType)
    [Algebra S T] (s : S) [IsLocalization.Away s T] (H : (algebraMap S T).comp f = g) :
    g.QuasiFinite := by
  algebraize [f, g]
  have : IsScalarTower R S T := .of_algebraMap_eq' H.symm
  exact Algebra.QuasiFinite.of_isIntegral_of_finiteType s

end RingHom
#min_imports
