/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Jiedong Jiang
-/
import Mathlib.FieldTheory.Galois.IsFractionRing
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Ramification theory in Galois extensions of Dedekind domains

In this file, we discuss the ramification theory in Galois extensions of Dedekind domains, which is
  also called Hilbert's Ramification Theory.

Assume `B / A` is a finite extension of dedekind Domains, `K` is the fraction ring of `A`,
  `L` is the fraction ring of `K`, `L / K` is a Galois extension.

## Main definitions

* `Ideal.ramificationIdxIn`: It can be seen from
  the theorem `Ideal.ramificationIdx_eq_of_IsGalois` that all `Ideal.ramificationIdx` over a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.ramificationIdxIn`.

* `Ideal.inertiaDegIn`: It can be seen from
  the theorem `Ideal.inertiaDeg_eq_of_IsGalois` that all `Ideal.inertiaDeg` over a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.inertiaDegIn`.

## Main results

* `exists_map_eq_of_isGalois`: If `p` is a maximal ideal of `A`, `P` and `Q` are prime ideals
  lying over `p`, then there exists `σ ∈ Aut (B / A)` such that `σ P = Q`. In other words,
  the Galois group `Gal(L / K)` acts transitively on the set of all prime ideals lying over `p`.

* `ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`: Let `p` be a maximal ideal of `A`,
  `r` be the number of prime ideals lying over `p`, `e` be the ramification index of `p` in `B`,
  and `f` be the inertia degree of `p` in `B`. Then `r * (e * f) = [L : K]`. It is the form of the
  `Ideal.sum_ramification_inertia` in the case of Galois extension.

## References

 * [J Neukirch, *Algebraic Number Theory*][Neukirch1992]

-/

open Algebra

attribute [local instance] FractionRing.liftAlgebra

namespace Ideal

open scoped Classical in
/-- If `L / K` is a Galois extension, it can be seen from the theorem
  `Ideal.ramificationIdx_eq_of_IsGalois` that all `Ideal.ramificationIdx` over a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.ramificationIdxIn`. -/
noncomputable def ramificationIdxIn {A : Type*} [CommRing A] (p : Ideal A)
    (B : Type*) [CommRing B] [Algebra A B] : ℕ :=
  if h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p then
    p.ramificationIdx (algebraMap A B) h.choose else 0

open scoped Classical in
/-- If `L / K` is a Galois extension, it can be seen from
  the theorem `Ideal.inertiaDeg_eq_of_IsGalois` that all `Ideal.inertiaDeg` over a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.inertiaDegIn`. -/
noncomputable def inertiaDegIn {A : Type*} [CommRing A] (p : Ideal A)
    (B : Type*) [CommRing B] [Algebra A B] : ℕ :=
  if h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p then
    p.inertiaDeg (algebraMap A B) h.choose else 0

section MulAction

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A)
  (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [IsIntegralClosure B A L] [FiniteDimensional K L]

instance : MulAction (L ≃ₐ[K] L) (primesOver p B) where
  smul σ Q := primesOver.mk p (map (galRestrict A K L B σ) Q.1)
  one_smul Q := by
    apply Subtype.val_inj.mp
    show map _ Q.1 = Q.1
    simpa only [map_one] using map_id Q.1
  mul_smul σ τ Q := by
    apply Subtype.val_inj.mp
    show map _ Q.1 = map _ (map _ Q.1)
    rw [_root_.map_mul]
    exact (Q.1.map_map ((galRestrict A K L B) τ).toRingHom ((galRestrict A K L B) σ).toRingHom).symm

theorem coe_smul_primesOver (σ : L ≃ₐ[K] L) (P : primesOver p B):
  (σ • P).1 = map (galRestrict A K L B σ) P := rfl

theorem coe_smul_primesOver_mk (σ : L ≃ₐ[K] L) (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
  (σ • primesOver.mk p P).1 = map (galRestrict A K L B σ) P := rfl

end MulAction

section RamificationInertia

variable {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Algebra A B] [NoZeroSMulDivisors A B] [Module.Finite A B]
  (p : Ideal A) (P Q : Ideal B) [p.IsMaximal] [hPp : P.IsPrime] [hp : P.LiesOver p]
  [hQp : Q.IsPrime] [Q.LiesOver p]
  (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]

include p in
/-- If `p` is a maximal ideal of `A`, `P` and `Q` are prime ideals
  lying over `p`, then there exists `σ ∈ Aut (B / A)` such that `σ P = Q`. In other words,
  the Galois group `Gal(L / K)` acts transitively on the set of all prime ideals lying over `p`. -/
theorem exists_map_eq_of_isGalois [IsGalois K L] : ∃ σ : B ≃ₐ[A] B, map σ P = Q := by
  haveI := IsGalois.fractionRing_of_isGalois_isFractionRing A B K L
  haveI : P.IsMaximal := IsMaximal.of_liesOver_isMaximal P p
  haveI hQm : Q.IsMaximal := IsMaximal.of_liesOver_isMaximal Q p
  by_contra hs
  push_neg at hs
  rcases Submodule.mem_sup.mp <| (eq_top_iff_one (Q ⊔ ∏ σ : B ≃ₐ[A] B, map σ P)).mp <|
    sup_prod_eq_top fun σ _ ↦ hQm.coprime_of_ne inferInstance (hs σ).symm with ⟨x, hx, y, hy, hxy⟩
  let n : B := ∏ σ : B ≃ₐ[A] B, σ x
  have hnx : n = (algebraMap A B) (intNorm A B x) := (algebraMap_intNorm_of_isGalois A B).symm
  have hnk : intNorm A B x ∈ P.under A := by
    rw [← P.over_def p, Q.over_def p, mem_comap, ← hnx]
    refine (span_singleton_le_iff_mem Q).mp ?_
    rw [← prod_span_singleton]
    exact hQm.isPrime.prod_le.mpr ⟨1, Finset.mem_univ 1, (span_singleton_le_iff_mem Q).mpr hx⟩
  rcases IsPrime.prod_mem_iff.mp (Eq.mpr (hnx ▸ Eq.refl (n ∈ P)) hnk : n ∈ P) with ⟨σ, _, hs⟩
  have hxp : x ∈ map σ.symm P := by
    rw [← AlgEquiv.symm_apply_apply σ x]
    exact mem_map_of_mem σ.symm hs
  have h := (map σ.symm P).add_mem hxp <|
    (prod_le_inf.trans (Finset.inf_le (Finset.mem_univ σ.symm))) hy
  rw [hxy] at h
  exact IsMaximal.ne_top inferInstance ((eq_top_iff_one (map σ.symm P)).mpr h)

instance [FiniteDimensional K L] [IsGalois K L] :
    MulAction.IsPretransitive (L ≃ₐ[K] L) (primesOver p B) where
  exists_smul_eq P Q := by
    rcases exists_map_eq_of_isGalois p P.1 Q.1 K L with ⟨σ, hs⟩
    rw [show σ = _ from (MulEquiv.symm_apply_eq (galRestrict A K L B)).mp rfl] at hs
    exact ⟨(galRestrict A K L B).symm σ, Subtype.val_inj.mp hs⟩

/-- All the `ramificationIdx` over a fixed maximal ideal are the same. -/
theorem ramificationIdx_eq_of_isGalois [IsGalois K L] :
    ramificationIdx (algebraMap A B) p P = ramificationIdx (algebraMap A B) p Q := by
  rcases exists_map_eq_of_isGalois p P Q K L with ⟨σ, hs⟩
  rw [← hs]
  exact (ramificationIdx_map_eq p P σ).symm

/-- All the `inertiaDeg` over a fixed maximal ideal are the same. -/
theorem inertiaDeg_eq_of_isGalois [IsGalois K L] :
    inertiaDeg (algebraMap A B) p P = inertiaDeg (algebraMap A B) p Q := by
  rcases exists_map_eq_of_isGalois p P Q K L with ⟨σ, hs⟩
  rw [← hs]
  exact (inertiaDeg_map_eq p P σ).symm

/-- The `ramificationIdxIn` is equal to any ramification index over the same ideal. -/
theorem ramificationIdxIn_eq_ramificationIdx [IsGalois K L] :
    ramificationIdxIn p B = ramificationIdx (algebraMap A B) p P := by
  have h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [ramificationIdxIn, dif_pos h]
  exact ramificationIdx_eq_of_isGalois p h.choose P K L

/-- The `inertiaDegIn` is equal to any ramification index over the same ideal. -/
theorem inertiaDegIn_eq_inertiaDeg [IsGalois K L] :
    inertiaDegIn p B = inertiaDeg (algebraMap A B) p P := by
  have h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [inertiaDegIn, dif_pos h]
  exact inertiaDeg_eq_of_isGalois p h.choose P K L

end RamificationInertia

section fundamental_identity

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [NoZeroSMulDivisors A B] [Module.Finite A B]
  {p : Ideal A} (hpb : p ≠ ⊥) [p.IsMaximal] (P : Ideal B) [P.IsPrime] [hp : P.LiesOver p]
  (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]

include hpb in
/-- Let `p` be a maximal ideal of `A`, `r` be the number of prime ideals lying over `p`, `
  e` be the ramification index of `p` in `B`, and `f` be the inertia degree of `p` in `B`.
  Then `r * (e * f) = [L : K]`. It is the form of the Ideal.sum_ramification_inertia`
  in the case of Galois extension. -/
theorem ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn [IsGalois K L] :
    (primesOver p B).ncard * (ramificationIdxIn p B * inertiaDegIn p B) = Module.finrank K L := by
  rw [← smul_eq_mul, ← coe_primesOverFinset hpb B, Set.ncard_coe_Finset, ← Finset.sum_const]
  rw [← sum_ramification_inertia B p K L hpb]
  apply Finset.sum_congr rfl
  intro P hp
  rw [← Finset.mem_coe, coe_primesOverFinset hpb B] at hp
  obtain ⟨_, _⟩ := hp
  rw [ramificationIdxIn_eq_ramificationIdx p P K L, inertiaDegIn_eq_inertiaDeg p P K L]

end fundamental_identity

end Ideal
