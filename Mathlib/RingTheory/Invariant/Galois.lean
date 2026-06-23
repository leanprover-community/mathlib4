/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Invariant Extensions of Rings

Given an extension of rings `B/A` and an action of `G` on `B`, we introduce a predicate
`Algebra.IsInvariant A B G` which states that every fixed point of `B` lies in the image of `A`.

The main application is in algebraic number theory, where `G := Gal(L/K)` is the Galois group
of some finite Galois extension of number fields, and `A := 𝓞K` and `B := 𝓞L` are their ring of
integers. This main result in this file implies the existence of Frobenius elements in this setting.
See `Mathlib/RingTheory/Frobenius.lean`.

## Main statements

Let `G` be a finite group acting on a commutative ring `B` satisfying `Algebra.IsInvariant A B G`.

* `Algebra.IsInvariant.isIntegral`: `B/A` is an integral extension.
* `Algebra.IsInvariant.exists_smul_of_under_eq`: `G` acts transitivity on the prime ideals of `B`
  lying above a given prime ideal of `A`.

If `Q` is a prime ideal of `B` lying over a prime ideal `P` of `A`, then

* `IsFractionRing.stabilizerHom_surjective`:
  The stabilizer subgroup of `Q` surjects onto `Aut(Frac(B/Q)/Frac(A/P))`.
* `Ideal.Quotient.stabilizerHom_surjective`:
  The stabilizer subgroup of `Q` surjects onto `Aut((B/Q)/(A/P))`.
* `Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under`:
  If `k` is a domain containing `B/Q`, then any `A/P`-algebra automorphism of `k` restricts to
  an automorphism of `B/Q`.
-/

@[expose] public section

open scoped Pointwise

section Galois

variable (A K L B : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
  [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  [IsIntegrallyClosed A] [IsIntegralClosure B A L]

/-- In the AKLB setup, the Galois group of `L/K` acts on `B`. -/
@[implicit_reducible]
noncomputable def IsIntegralClosure.MulSemiringAction [Algebra.IsAlgebraic K L] :
    MulSemiringAction Gal(L/K) B :=
  MulSemiringAction.compHom B (galRestrict A K L B).toMonoidHom

instance [Algebra.IsAlgebraic K L] : let := IsIntegralClosure.MulSemiringAction A K L B
    SMulDistribClass Gal(L/K) B L :=
  let := IsIntegralClosure.MulSemiringAction A K L B
  ⟨fun g b l ↦ by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    exact Or.inl (algebraMap_galRestrictHom_apply A K L B g b).symm⟩

/-- In the AKLB setup, every fixed point of `B` lies in the image of `A`. -/
theorem Algebra.isInvariant_of_isGalois [FiniteDimensional K L] [h : IsGalois K L] :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    Algebra.IsInvariant A B Gal(L/K) := by
  replace h := ((IsGalois.tfae (F := K) (E := L)).out 0 1).mp h
  letI := IsIntegralClosure.MulSemiringAction A K L B
  refine ⟨fun b hb ↦ ?_⟩
  replace hb : algebraMap B L b ∈ IntermediateField.fixedField (⊤ : Subgroup Gal(L/K)) := by
    rintro ⟨g, -⟩
    exact (algebraMap_galRestrict_apply A g b).symm.trans (congrArg (algebraMap B L) (hb g))
  rw [h, IntermediateField.mem_bot] at hb
  obtain ⟨k, hk⟩ := hb
  have hb : IsIntegral A b := IsIntegralClosure.isIntegral A L b
  rw [← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective B L), ← hk,
    isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective K L)] at hb
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hb
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L,
    (FaithfulSMul.algebraMap_injective B L).eq_iff] at hk
  exact ⟨a, hk⟩

/-- A variant of `Algebra.isInvariant_of_isGalois`, replacing `Gal(L/K)` by `Aut(B/A)`. -/
theorem Algebra.isInvariant_of_isGalois' [FiniteDimensional K L] [IsGalois K L] :
    Algebra.IsInvariant A B (B ≃ₐ[A] B) :=
  ⟨fun b h ↦ (isInvariant_of_isGalois A K L B).1 b (fun g ↦ h (galRestrict A K L B g))⟩

end Galois

section normal

variable {A B k : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Finite G] [Group G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
  (P : Ideal A) (Q : Ideal B) [Q.LiesOver P]
  [CommRing k] [Algebra (A ⧸ P) k] [Algebra (B ⧸ Q) k] [IsScalarTower (A ⧸ P) (B ⧸ Q) k]
  [IsDomain k] [FaithfulSMul (B ⧸ Q) k]

namespace Ideal.IsFractionRing

variable [P.IsPrime] [Q.IsPrime] (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K] [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L]
    [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L] [IsScalarTower (A ⧸ P) K L]

open Polynomial in
include P Q G in
lemma normal : Normal K L := by
  have := Algebra.IsInvariant.isIntegral A B G
  have := isAlgebraic_of_isFractionRing (A ⧸ P) (B ⧸ Q) K L
  constructor
  intro x
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (B ⧸ Q) x
  obtain ⟨b, a, ha, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A ⧸ P) y).exists_smul_eq_mul x hy
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Quotient.mk_surjective b
  simp_rw [← Quotient.algebraMap_eq] at *
  cases nonempty_fintype G
  obtain ⟨p, hp, -, h_monic⟩ := lifts_and_natDegree_eq_and_monic
    (Algebra.IsInvariant.charpoly_mem_lifts A B G b) (MulSemiringAction.monic_charpoly ..)
  have h_eval : p.aeval b = 0 := by
    rw [← eval_map_algebraMap, hp, MulSemiringAction.eval_charpoly]
  let q := p.comp (C a * X)
  let d := (algebraMap (B ⧸ Q) L) x / (algebraMap (B ⧸ Q) L) y
  have comm₁ : (algebraMap K L).comp (algebraMap (A ⧸ P) K) =
      (algebraMap (B ⧸ Q) L).comp (algebraMap (A ⧸ P) (B ⧸ Q)) := by
    simp_rw [← IsScalarTower.algebraMap_eq]
  have comm₂ : (algebraMap (A ⧸ P) (B ⧸ Q)).comp (algebraMap A (A ⧸ P)) =
      (algebraMap B (B ⧸ Q)).comp (algebraMap A B) := by
    simp_rw [← IsScalarTower.algebraMap_eq]
  replace h_eval : ((q.map (algebraMap A (A ⧸ P))).map (algebraMap (A ⧸ P) K)).aeval d = 0 := by
    simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X, aeval_comp, aeval_mul, aeval_C, aeval_X,
      ← RingHom.comp_apply, ← RingHom.comp_assoc, comm₁, RingHom.comp_apply, d, mul_div, ← map_mul]
    rw [← Algebra.smul_def, h, map_mul, mul_div_cancel_left₀ _ (by simpa using hy),
      aeval_map_algebraMap, aeval_algebraMap_apply, aeval_map_algebraMap, aeval_algebraMap_apply,
      h_eval, map_zero, map_zero]
  replace h_splits : (p.map (algebraMap A B)).Splits := by
    rw [hp]
    exact MulSemiringAction.splits_charpoly G b
  refine .of_dvd ?_ ?_ (map_dvd (algebraMap K L) (minpoly.dvd K d h_eval))
  · simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X]
    refine .comp_of_degree_le_one ?_ (degree_C_mul_X_le _)
    rw [Polynomial.map_map, Polynomial.map_map, comm₁, RingHom.comp_assoc, comm₂,
      ← RingHom.comp_assoc, ← Polynomial.map_map]
    apply h_splits.map
  · simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X, Polynomial.map_map]
    exact mt (comp_C_mul_X_eq_zero_iff (by simpa)).mp (map_monic_ne_zero h_monic)

include P Q in
lemma finite_of_isInvariant [SMulCommClass G A B] [Algebra.IsSeparable K L] :
    Module.Finite K L := by
  have : IsGalois K L := { __ := normal G P Q K L }
  have := Finite.of_surjective _ (IsFractionRing.stabilizerHom_surjective G P Q K L)
  apply IsGalois.finiteDimensional_of_finite

end Ideal.IsFractionRing

attribute [local instance] Ideal.Quotient.field in
include G in
/--
For any domain `k` containing `B ⧸ Q`,
any endomorphism of `k` can be restricted to an endomorphism of `B ⧸ Q`. -/
lemma Ideal.Quotient.normal [P.IsMaximal] [Q.IsMaximal] :
    Normal (A ⧸ P) (B ⧸ Q) :=
  IsFractionRing.normal G P Q (A ⧸ P) (B ⧸ Q)

attribute [local instance] Ideal.Quotient.field in
include G in
/-- If the extension `B/Q` over `A/P` is separable, then it is finite dimensional. -/
lemma Ideal.Quotient.finite_of_isInvariant [P.IsMaximal] [Q.IsMaximal]
    [SMulCommClass G A B] [Algebra.IsSeparable (A ⧸ P) (B ⧸ Q)] :
    Module.Finite (A ⧸ P) (B ⧸ Q) :=
  IsFractionRing.finite_of_isInvariant G P Q (A ⧸ P) (B ⧸ Q)

end normal
