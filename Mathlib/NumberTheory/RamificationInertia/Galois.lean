/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Jiedong Jiang
-/
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Invariant.Basic

/-!
# Ramification theory in Galois extensions of Dedekind domains

In this file, we discuss the ramification theory in Galois extensions of Dedekind domains, which is
  also called Hilbert's Ramification Theory.

Assume `B / A` is a finite extension of Dedekind domains, `K` is the fraction ring of `A`,
  `L` is the fraction ring of `K`, `L / K` is a Galois extension.

## Main definitions

* `Ideal.ramificationIdxIn`: It can be seen from
  the theorem `Ideal.ramificationIdx_eq_of_IsGalois` that all `Ideal.ramificationIdx` over a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.ramificationIdxIn`.

* `Ideal.inertiaDegIn`: It can be seen from
  the theorem `Ideal.inertiaDeg_eq_of_IsGalois` that all `Ideal.inertiaDeg` over a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.inertiaDegIn`.

## Main results

* `ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`: Let `p` be a maximal ideal of `A`,
  `r` be the number of prime ideals lying over `p`, `e` be the ramification index of `p` in `B`,
  and `f` be the inertia degree of `p` in `B`. Then `r * (e * f) = [L : K]`. It is the form of the
  `Ideal.sum_ramification_inertia` in the case of Galois extension.

## References

* [J Neukirch, *Algebraic Number Theory*][Neukirch1992]

-/

open Algebra Pointwise

attribute [local instance] FractionRing.liftAlgebra

namespace Ideal

open scoped Classical in
/-- If `L / K` is a Galois extension, it can be seen from the theorem
  `Ideal.ramificationIdx_eq_of_IsGalois` that all `Ideal.ramificationIdx` over a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.ramificationIdxIn`. -/
noncomputable def ramificationIdxIn {A : Type*} [CommRing A] (p : Ideal A)
    (B : Type*) [CommRing B] [Algebra A B] : ℕ :=
  if h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p then p.ramificationIdx (algebraMap A B) h.choose
  else 0

open scoped Classical in
/-- If `L / K` is a Galois extension, it can be seen from
  the theorem `Ideal.inertiaDeg_eq_of_IsGalois` that all `Ideal.inertiaDeg` over a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.inertiaDegIn`. -/
noncomputable def inertiaDegIn {A : Type*} [CommRing A] (p : Ideal A)
    (B : Type*) [CommRing B] [Algebra A B] : ℕ :=
  if h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p then p.inertiaDeg h.choose else 0

section MulAction

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {p : Ideal A}
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

instance : MulAction G (primesOver p B) where
  smul σ Q := primesOver.mk p (σ • Q.1)
  one_smul Q := Subtype.ext (one_smul G Q.1)
  mul_smul σ τ Q := Subtype.ext (mul_smul σ τ Q.1)

@[simp]
theorem coe_smul_primesOver (σ : G) (P : primesOver p B) : (σ • P).1 = σ • P.1 :=
  rfl

@[simp]
theorem coe_smul_primesOver_mk (σ : G) (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    (σ • primesOver.mk p P).1 = σ • P :=
  rfl

variable (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [IsIntegralClosure B A L] [FiniteDimensional K L]

noncomputable instance : MulAction Gal(L/K) (primesOver p B) where
  smul σ Q := primesOver.mk p (map (galRestrict A K L B σ) Q.1)
  one_smul Q := by
    apply Subtype.val_inj.mp
    change map _ Q.1 = Q.1
    simpa only [map_one] using map_id Q.1
  mul_smul σ τ Q := by
    apply Subtype.val_inj.mp
    change map _ Q.1 = map _ (map _ Q.1)
    rw [map_mul]
    exact (Q.1.map_map ((galRestrict A K L B) τ).toRingHom ((galRestrict A K L B) σ).toRingHom).symm

theorem coe_smul_primesOver_eq_map_galRestrict (σ : Gal(L/K)) (P : primesOver p B) :
    (σ • P).1 = map (galRestrict A K L B σ) P :=
  rfl

theorem coe_smul_primesOver_mk_eq_map_galRestrict (σ : Gal(L/K)) (P : Ideal B) [P.IsPrime]
    [P.LiesOver p] : (σ • primesOver.mk p P).1 = map (galRestrict A K L B σ) P :=
  rfl

end MulAction

section RamificationInertia

variable {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B] (p : Ideal A) (P Q : Ideal B)
  [hPp : P.IsPrime] [hp : P.LiesOver p] [hQp : Q.IsPrime] [Q.LiesOver p]
  (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [FiniteDimensional K L]

include p in
/-- If `p` is a maximal ideal of `A`, `P` and `Q` are prime ideals
  lying over `p`, then there exists `σ ∈ Aut (B / A)` such that `σ P = Q`. In other words,
  the Galois group `Gal(L / K)` acts transitively on the set of all prime ideals lying over `p`. -/
theorem exists_map_eq_of_isGalois [IsGalois K L] : ∃ σ : B ≃ₐ[A] B, map σ P = Q := by
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  have : IsInvariant A B (B ≃ₐ[A] B) := isInvariant_of_isGalois' A K L B
  rcases IsInvariant.exists_smul_of_under_eq A B (B ≃ₐ[A] B) P Q <|
    (over_def P p).symm.trans (over_def Q p) with ⟨σ, hs⟩
  exact ⟨σ, hs.symm⟩

theorem isPretransitive_of_isGalois [IsGalois K L] :
    MulAction.IsPretransitive (B ≃ₐ[A] B) (primesOver p B) where
  exists_smul_eq := by
    intro ⟨P, _, _⟩ ⟨Q, _, _⟩
    rcases exists_map_eq_of_isGalois p P Q K L with ⟨σ, hs⟩
    exact ⟨σ, Subtype.val_inj.mp hs⟩

instance [IsGalois K L] : MulAction.IsPretransitive Gal(L/K) (primesOver p B) where
  exists_smul_eq := by
    intro ⟨P, _, _⟩ ⟨Q, _, _⟩
    rcases exists_map_eq_of_isGalois p P Q K L with ⟨σ, hs⟩
    exact ⟨(galRestrict A K L B).symm σ, Subtype.val_inj.mp <|
      (congrFun (congrArg map ((galRestrict A K L B).apply_symm_apply σ)) P).trans hs⟩

/-- All the `ramificationIdx` over a fixed maximal ideal are the same. -/
theorem ramificationIdx_eq_of_isGalois [IsGalois K L] :
    ramificationIdx (algebraMap A B) p P = ramificationIdx (algebraMap A B) p Q := by
  rcases exists_map_eq_of_isGalois p P Q K L with ⟨σ, hs⟩
  rw [← hs]
  exact (ramificationIdx_map_eq p P σ).symm

/-- All the `inertiaDeg` over a fixed maximal ideal are the same. -/
theorem inertiaDeg_eq_of_isGalois [p.IsMaximal] [IsGalois K L] :
    inertiaDeg p P = inertiaDeg p Q := by
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

theorem ramificationIdxIn_ne_zero [IsDedekindDomain B] {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥)
    [IsGalois K L] [NoZeroSMulDivisors A B] : p.ramificationIdxIn B ≠ 0 := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (primesOver p B))
  rw [ramificationIdxIn_eq_ramificationIdx p P K L]
  exact IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P.1 hp

/-- The `inertiaDegIn` is equal to any ramification index over the same ideal. -/
theorem inertiaDegIn_eq_inertiaDeg [p.IsMaximal] [IsGalois K L] :
    inertiaDegIn p B = inertiaDeg p P := by
  have h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [inertiaDegIn, dif_pos h]
  exact inertiaDeg_eq_of_isGalois p h.choose P K L

theorem inertiaDegIn_ne_zero {p : Ideal A} [p.IsMaximal] [IsGalois K L] [NoZeroSMulDivisors A B] :
    inertiaDegIn p B ≠ 0 := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (primesOver p B))
  rw [inertiaDegIn_eq_inertiaDeg p P K L]
  exact inertiaDeg_ne_zero _ _

end RamificationInertia

section fundamental_identity

variable {A : Type*} [CommRing A] [IsDedekindDomain A] {p : Ideal A} (hpb : p ≠ ⊥) [p.IsMaximal]
  (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
  (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [FiniteDimensional K L]

include hpb in
/-- The form of the **fundamental identity** in the case of Galois extension. -/
theorem ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn [IsGalois K L] :
    (primesOver p B).ncard * (ramificationIdxIn p B * inertiaDegIn p B) = Module.finrank K L := by
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  rw [← smul_eq_mul, ← coe_primesOverFinset hpb B, Set.ncard_coe_finset, ← Finset.sum_const]
  rw [← sum_ramification_inertia B K L hpb]
  apply Finset.sum_congr rfl
  intro P hp
  rw [← Finset.mem_coe, coe_primesOverFinset hpb B] at hp
  obtain ⟨_, _⟩ := hp
  rw [ramificationIdxIn_eq_ramificationIdx p P K L, inertiaDegIn_eq_inertiaDeg p P K L]

end fundamental_identity

end Ideal
