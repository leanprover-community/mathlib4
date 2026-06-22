/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Jiedong Jiang
-/
module

public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Ramification theory in Galois extensions of Dedekind domains

In this file, we discuss the ramification theory in Galois extensions of Dedekind domains, which is
  also called Hilbert's Ramification Theory.

Assume `B / A` is a finite extension of Dedekind domains, `K` is the fraction ring of `A`,
  `L` is the fraction ring of `K`, `L / K` is a Galois extension.

## Main definitions

* `Ideal.ramificationIdxIn`: It can be seen from
  the theorem `Ideal.ramificationIdx_eq_of_isGaloisGroup` that all `Ideal.ramificationIdx` over a
  fixed maximal ideal `p` of `A` are the same, which we define as `Ideal.ramificationIdxIn`.

* `Ideal.inertiaDegIn`: It can be seen from
  the theorem `Ideal.inertiaDeg_eq_of_isGaloisGroup` that all `Ideal.inertiaDeg` over a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.inertiaDegIn`.

## Main results

* `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`: Let `p` be a prime of `A`,
  `r` be the number of prime ideals lying over `p`, `e` be the ramification index of `p` in `B`,
  and `f` be the inertia degree of `p` in `B`. Then `r * (e * f) = [L : K]`. It is the form of the
  `Ideal.sum_ramification_inertia` in the case of Galois extension.

* `Ideal.card_inertia_eq_ramificationIdxIn`:
  The cardinality of the inertia group is equal to the ramification index.

## References

* [J Neukirch, *Algebraic Number Theory*][Neukirch1992]

-/

@[expose] public section

open Algebra Module
open scoped Pointwise

attribute [local instance] FractionRing.liftAlgebra

namespace Ideal

open scoped Classical in
/-- If `L / K` is a Galois extension, it can be seen from the theorem
  `Ideal.ramificationIdx_eq_of_isGaloisGroup` that all `Ideal.ramificationIdx` over a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.ramificationIdxIn`. -/
noncomputable def ramificationIdxIn {A : Type*} [CommRing A] (p : Ideal A)
    (B : Type*) [CommRing B] [Algebra A B] : ℕ :=
  if h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p then h.choose.ramificationIdx' A
  else 0

open scoped Classical in
/-- If `L / K` is a Galois extension, it can be seen from
  the theorem `Ideal.inertiaDeg_eq_of_isGaloisGroup` that all `Ideal.inertiaDeg` over a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.inertiaDegIn`. -/
noncomputable def inertiaDegIn {A : Type*} [CommRing A] (p : Ideal A)
    (B : Type*) [CommRing B] [Algebra A B] : ℕ :=
  if h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p then h.choose.inertiaDeg' A else 0

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
    simpa only [map_one] using! map_id Q.1
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

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A) (P Q : Ideal B)
  [hPp : P.IsPrime] [hp : P.LiesOver p] [hQp : Q.IsPrime] [Q.LiesOver p]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

include p in
/-- If `p` is a maximal ideal of `A`, `P` and `Q` are prime ideals
  lying over `p`, then there exists `σ ∈ Aut (B / A)` such that `σ P = Q`. In other words,
  the Galois group `Gal(L / K)` acts transitively on the set of all prime ideals lying over `p`. -/
theorem exists_smul_eq_of_isGaloisGroup : ∃ σ : G, σ • P = Q := by
  rcases IsInvariant.exists_smul_of_under_eq A B G P Q <|
    (over_def P p).symm.trans (over_def Q p) with ⟨σ, hs⟩
  exact ⟨σ, hs.symm⟩

instance isPretransitive_of_isGaloisGroup : MulAction.IsPretransitive G (primesOver p B) where
  exists_smul_eq := by
    intro ⟨P, _, _⟩ ⟨Q, _, _⟩
    rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, hs⟩
    exact ⟨σ, Subtype.val_inj.mp hs⟩

include p G in
/-- All the `Ideal.ramificationIdx` over a fixed maximal ideal are the same. -/
theorem ramificationIdx_eq_of_isGaloisGroup :
    P.ramificationIdx' A = Q.ramificationIdx' A := by
  rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, rfl⟩
  rw [ramificationIdx'_smul]

include p G in
/-- All the `Ideal.inertiaDeg` over a fixed maximal ideal are the same. -/
theorem inertiaDeg_eq_of_isGaloisGroup :
    P.inertiaDeg' A = Q.inertiaDeg' A := by
  rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, rfl⟩
  rw [inertiaDeg'_smul]

include p G in
/-- The `ramificationIdxIn` is equal to any ramification index over the same ideal. -/
theorem ramificationIdxIn_eq_ramificationIdx :
    ramificationIdxIn p B = P.ramificationIdx' A := by
  have h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [ramificationIdxIn, dif_pos h]
  exact ramificationIdx_eq_of_isGaloisGroup p h.choose P G

include G in
theorem ramificationIdxIn_ne_zero [Module.Finite A B] [FaithfulSMul A B] {p : Ideal A} [p.IsPrime] :
    p.ramificationIdxIn B ≠ 0 := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (primesOver p B))
  rw [ramificationIdxIn_eq_ramificationIdx p P G]
  exact (P.1.ramificationIdx'_pos A).ne'

include G in
/-- The `inertiaDegIn` is equal to any ramification index over the same ideal. -/
theorem inertiaDegIn_eq_inertiaDeg :
    inertiaDegIn p B = P.inertiaDeg' A := by
  have h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [inertiaDegIn, dif_pos h]
  exact inertiaDeg_eq_of_isGaloisGroup p h.choose P G

include G in
theorem inertiaDegIn_ne_zero [Module.Finite A B] [FaithfulSMul A B] {p : Ideal A} [p.IsPrime] :
    inertiaDegIn p B ≠ 0 := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (primesOver p B))
  rw [inertiaDegIn_eq_inertiaDeg p P G]
  exact (P.1.inertiaDeg'_pos A).ne'

section tower

variable (C : Type*) [CommRing C] [Algebra A C] [Algebra B C]
  [Nonempty (P.primesOver C)] [IsScalarTower A B C]
  (GAC : Type*) [Group GAC] [Finite GAC] [MulSemiringAction GAC C] [IsGaloisGroup GAC A C]
  (GBC : Type*) [Group GBC] [Finite GBC] [MulSemiringAction GBC C] [IsGaloisGroup GBC B C]

include G GAC GBC in
theorem inertiaDegIn_mul_inertiaDegIn :
    p.inertiaDegIn B * P.inertiaDegIn C = p.inertiaDegIn C := by
  obtain ⟨⟨Q, _, _⟩⟩ := (inferInstance : Nonempty (primesOver P C))
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [inertiaDegIn_eq_inertiaDeg p P G, inertiaDegIn_eq_inertiaDeg p Q GAC,
    inertiaDegIn_eq_inertiaDeg P Q GBC, ← inertiaDeg'_tower P Q]

variable {p} in
include G GAC GBC in
theorem ramificationIdxIn_mul_ramificationIdxIn [Flat B C] :
    p.ramificationIdxIn B * P.ramificationIdxIn C = p.ramificationIdxIn C := by
  obtain ⟨⟨Q, _, hQ⟩⟩ := (inferInstance : Nonempty (primesOver P C))
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [ramificationIdxIn_eq_ramificationIdx p P G, ramificationIdxIn_eq_ramificationIdx p Q GAC,
    ramificationIdxIn_eq_ramificationIdx P Q GBC, ← ramificationIdx'_tower P Q]

@[deprecated (since := "2026-06-18")] alias ramificationIdxIn_mul_ramificationIdxIn' :=
  ramificationIdxIn_mul_ramificationIdxIn

end tower

end RamificationInertia

section fundamental_identity

variable {A : Type*} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]
  (B : Type*) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Flat A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

/-- The form of the **fundamental identity** in the case of Galois extension. -/
theorem ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn :
    (primesOver p B).ncard * (ramificationIdxIn p B * inertiaDegIn p B) = Nat.card G := by
  have : Fintype (primesOver p B) := (QuasiFinite.finite_primesOver p).fintype
  rw [← smul_eq_mul, ← Set.fintypeCard_eq_ncard, ← Finset.card_univ, ← Finset.sum_const,
    ← sum_ramification_inertia_eq_card p B]
  apply Finset.sum_congr rfl
  intro P hp
  rw [ramificationIdxIn_eq_ramificationIdx p P G, inertiaDegIn_eq_inertiaDeg p P G]

end fundamental_identity

section tower

variable {A B : Type*} [CommRing A] [CommRing B]
  [Algebra A B] [FaithfulSMul A B] {p : Ideal A} (P : Ideal B)
  [P.IsPrime] [P.LiesOver p] (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
  [IsGaloisGroup G A B] (C : Type*) [CommRing C] [IsDomain C] [Algebra A C]
  [Algebra B C] [FaithfulSMul B C] [IsScalarTower A B C]
  (GAC : Type*) [Group GAC] [Finite GAC] [MulSemiringAction GAC C] [IsGaloisGroup GAC A C]

include G GAC in
open IsGaloisGroup MulAction in
theorem ncard_primesOver_mul_ncard_primesOver :
    (p.primesOver B).ncard * (P.primesOver C).ncard = (p.primesOver C).ncard := by
  have : Algebra.IsIntegral A C := isInvariant.isIntegral A C GAC
  have : Algebra.IsIntegral B C := Algebra.IsIntegral.tower_top A
  let f := restrictHom GAC G A B C
  have key (Q Q' : Ideal C) [Q.LiesOver P] [Q'.LiesOver P] g (hg : g • Q = Q') :
      f g ∈ stabilizer G P := by
    simpa [← restrictHom_smul_under GAC G A B C, ← Ideal.over_def _ P] using congr_arg (under B) hg
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (P.primesOver C))
  have : Q.LiesOver p := .trans Q P p
  have h1 : orbit ((stabilizer G P).comap f) Q = P.primesOver C := by
    ext Q'
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      refine ⟨inferInstance, ?_⟩
      simp [liesOver_iff]
      simp at hg
      rw [← restrictHom_smul_under GAC G A B C, ← Q.over_def P]
      exact hg.symm
    · rintro ⟨_, _⟩
      have : Q'.LiesOver p := .trans Q' P p
      obtain ⟨g, hg⟩ := IsInvariant.exists_smul_of_under_eq A C GAC Q Q' (by
        rw [← Ideal.over_def Q p, ← Ideal.over_def Q' p])
      refine ⟨⟨g, ?_⟩, ?_⟩
      · apply key Q Q' g hg.symm
      · simpa [Subgroup.smul_def] using hg.symm
  rw [← IsInvariant.orbit_eq_primesOver A B G p P, ← index_stabilizer]
  rw [← IsInvariant.orbit_eq_primesOver A C GAC p Q, ← index_stabilizer]
  rw [← h1, ← index_stabilizer]
  have h2 : stabilizer ((stabilizer G P).comap f) Q =
    (stabilizer GAC Q).subgroupOf ((stabilizer G P).comap f) := by
    ext
    simp [Subgroup.mem_subgroupOf, Subgroup.smul_def]
  rw [h2, ← Subgroup.relIndex]
  rw [← Subgroup.index_comap_of_surjective (stabilizer G P) (restrictHom_surjective GAC G A B C),
    mul_comm, Subgroup.relIndex_mul_index]
  exact key Q Q

end tower

section inertia

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

open scoped Pointwise

open Algebra

attribute [local instance] Ideal.Quotient.field in
theorem card_stabilizer_eq_card_inertia_mul_finrank (p : Ideal R) [p.IsPrime]
    (P : Ideal S) [P.LiesOver p] [P.IsPrime] [PerfectField p.ResidueField] :
    Nat.card (MulAction.stabilizer G P) = Nat.card (inertia G P) * P.inertiaDeg' R := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  let : Algebra (R ⧸ p) p.ResidueField := inferInstance
  let : Algebra (S ⧸ P) P.ResidueField := inferInstance
  have heq : (algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P)) =
      (algebraMap p.ResidueField P.ResidueField).comp (algebraMap (R ⧸ p) p.ResidueField) := by
    ext
    simp [← IsScalarTower.algebraMap_apply]
  let := ((algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P))).toAlgebra
  have : IsScalarTower (R ⧸ p) (S ⧸ P) P.ResidueField := .of_algebraMap_eq' rfl
  have : IsScalarTower (R ⧸ p) p.ResidueField P.ResidueField := .of_algebraMap_eq' heq
  have : IsGalois p.ResidueField P.ResidueField :=
    { __ := Ideal.IsFractionRing.normal G p P p.ResidueField P.ResidueField }
  have : Module.Finite p.ResidueField P.ResidueField :=
    Ideal.IsFractionRing.finite_of_isInvariant G p P p.ResidueField P.ResidueField
  have : Subgroup.index _ = _ := Nat.card_congr
    (IsFractionRing.stabilizerQuotientInertiaEquiv G p P p.ResidueField P.ResidueField).toEquiv
  rw [inertiaDeg'_eq p P, ← IsGalois.card_aut_eq_finrank p.ResidueField P.ResidueField, ← this,
    ← ((inertia G P).subgroupOf (MulAction.stabilizer G P)).card_mul_index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inertia_le_stabilizer (M := G) P)).toEquiv,
    AddSubgroup.subgroupOf_inertia]

lemma ncard_primesOver_mul_card_inertia_mul_finrank (p : Ideal R) [p.IsPrime]
    (P : Ideal S) [P.LiesOver p] [P.IsPrime] [PerfectField p.ResidueField] :
    (p.primesOver S).ncard * Nat.card (P.inertia G) * P.inertiaDeg' R = Nat.card G := by
  rw [mul_assoc, ← card_stabilizer_eq_card_inertia_mul_finrank p P,
    ← IsInvariant.orbit_eq_primesOver R S G p P]
  simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)

/-- The cardinality of the inertia group is equal to the ramification index. -/
lemma card_inertia_eq_ramificationIdxIn [IsDomain R] [IsDomain S] [Module.Finite R S] [Flat R S]
    (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [PerfectField p.ResidueField] :
    Nat.card (P.inertia G) = Ideal.ramificationIdxIn p S := by
  have H := ncard_primesOver_mul_card_inertia_mul_finrank (G := G) p P
  rw [← inertiaDegIn_eq_inertiaDeg p P G] at H
  have h1 : (p.primesOver S).ncard ≠ 0 := by grind [Nat.card_pos]
  have h2 : p.inertiaDegIn S ≠ 0 := by grind [Nat.card_pos]
  rwa [← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G,
    mul_assoc, mul_right_inj' h1, mul_left_inj' h2] at H

/-- The cardinality of the decomposition group is equal to the ramification index times the
inertia degree. -/
lemma card_stabilizer_eq [IsDomain R] [IsDomain S] [Module.Finite R S] [Flat R S]
    (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [PerfectField p.ResidueField] :
    Nat.card (MulAction.stabilizer G P) = p.ramificationIdxIn S * p.inertiaDegIn S := by
  rw [card_stabilizer_eq_card_inertia_mul_finrank p P, card_inertia_eq_ramificationIdxIn p,
    inertiaDegIn_eq_inertiaDeg p P G]

end inertia

section galRestrict

variable (R K L S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [FiniteDimensional K L]

lemma exists_comap_galRestrict_eq [IsDedekindDomain R] [IsGalois K L] {p : Ideal R}
    {P₁ P₂ : Ideal S} (hP₁ : P₁ ∈ primesOver p S) (hP₂ : P₂ ∈ primesOver p S) :
    ∃ σ, P₁.comap (galRestrict R K L S σ) = P₂ := by
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
  have := IsIntegralClosure.isDedekindDomain R K L S
  have : Module.Finite R S := IsIntegralClosure.finite R K L S
  have := hP₁.1
  have := hP₁.2
  have := hP₂.1
  have := hP₂.2
  have : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  let : MulSemiringAction Gal(L/K) S := IsIntegralClosure.MulSemiringAction R K L S
  have : IsGaloisGroup Gal(L/K) R S := IsGaloisGroup.of_isFractionRing _ _ _ K L
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup p P₂ P₁ Gal(L/K)
  exact ⟨σ, comap_map_of_bijective _ ((galRestrict R K L S σ).bijective)⟩

end galRestrict

end Ideal
