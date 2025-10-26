/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Jiedong Jiang
-/
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.RamificationInertia.Basic

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

* `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`: Let `p` be a prime of `A`,
  `r` be the number of prime ideals lying over `p`, `e` be the ramification index of `p` in `B`,
  and `f` be the inertia degree of `p` in `B`. Then `r * (e * f) = [L : K]`. It is the form of the
  `Ideal.sum_ramification_inertia` in the case of Galois extension.

* `Ideal.card_inertia_eq_ramificationIdxIn`:
  The cardinality of the inertia group is equal to the ramification index.

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

@[deprecated (since := "2025-10-26")]
alias exists_map_eq_of_isGaloisGroup := exists_smul_eq_of_isGaloisGroup

instance isPretransitive_of_isGaloisGroup : MulAction.IsPretransitive G (primesOver p B) where
  exists_smul_eq := by
    intro ⟨P, _, _⟩ ⟨Q, _, _⟩
    rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, hs⟩
    exact ⟨σ, Subtype.val_inj.mp hs⟩

@[deprecated (since := "2025-10-26")]
alias isPretransitive_of_isGalois := isPretransitive_of_isGaloisGroup

include G in
/-- All the `ramificationIdx` over a fixed maximal ideal are the same. -/
theorem ramificationIdx_eq_of_isGaloisGroup :
    ramificationIdx (algebraMap A B) p P = ramificationIdx (algebraMap A B) p Q := by
  rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, rfl⟩
  exact (ramificationIdx_map_eq p P (MulSemiringAction.toAlgEquiv A B σ)).symm

@[deprecated (since := "2025-10-26")]
alias ramificationIdx_eq_of_isGalois := ramificationIdx_eq_of_isGaloisGroup

include G in
/-- All the `inertiaDeg` over a fixed maximal ideal are the same. -/
theorem inertiaDeg_eq_of_isGaloisGroup [p.IsMaximal] :
    inertiaDeg p P = inertiaDeg p Q := by
  rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, rfl⟩
  exact (inertiaDeg_map_eq p P (MulSemiringAction.toAlgEquiv A B σ)).symm

@[deprecated (since := "2025-10-26")]
alias inertiaDeg_eq_of_isGalois := inertiaDeg_eq_of_isGaloisGroup

include G in
/-- The `ramificationIdxIn` is equal to any ramification index over the same ideal. -/
theorem ramificationIdxIn_eq_ramificationIdx :
    ramificationIdxIn p B = ramificationIdx (algebraMap A B) p P := by
  have h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [ramificationIdxIn, dif_pos h]
  exact ramificationIdx_eq_of_isGaloisGroup p h.choose P G

include G in
theorem ramificationIdxIn_ne_zero [IsDedekindDomain B] {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥)
    [NoZeroSMulDivisors A B] [Nontrivial B] : p.ramificationIdxIn B ≠ 0 := by
  have : Algebra.IsIntegral A B := IsGaloisGroup.isInvariant.isIntegral A B G
  obtain ⟨P⟩ := (inferInstance : Nonempty (primesOver p B))
  rw [ramificationIdxIn_eq_ramificationIdx p P G]
  exact IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P.1 hp

include G in
/-- The `inertiaDegIn` is equal to any ramification index over the same ideal. -/
theorem inertiaDegIn_eq_inertiaDeg [p.IsMaximal] :
    inertiaDegIn p B = inertiaDeg p P := by
  have h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [inertiaDegIn, dif_pos h]
  exact inertiaDeg_eq_of_isGaloisGroup p h.choose P G

include G in
theorem inertiaDegIn_ne_zero {p : Ideal A} [p.IsMaximal] [NoZeroSMulDivisors A B]
    [Module.Finite A B] [Nontrivial B] :
    inertiaDegIn p B ≠ 0 := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (primesOver p B))
  rw [inertiaDegIn_eq_inertiaDeg p P G]
  exact inertiaDeg_ne_zero _ _

end RamificationInertia

section fundamental_identity

variable {A : Type*} [CommRing A] [IsDedekindDomain A] {p : Ideal A} (hpb : p ≠ ⊥) [p.IsMaximal]
  (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

include hpb in
/-- The form of the **fundamental identity** in the case of Galois extension. -/
theorem ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn :
    (primesOver p B).ncard * (ramificationIdxIn p B * inertiaDegIn p B) = Nat.card G := by
  let K := FractionRing A
  let L := FractionRing B
  let _ : MulSemiringAction G L := MulSemiringAction.compHom L
      ((IsFractionRing.fieldEquivOfAlgEquivHom K L).comp (MulSemiringAction.toAlgAut G A B))
  have hGKL : IsGaloisGroup G K L := IsGaloisGroup.to_isFractionRing G A B K L
    (fun g b ↦ IsFractionRing.fieldEquivOfAlgEquiv_algebraMap K L L _ b)
  rw [← smul_eq_mul, ← coe_primesOverFinset hpb B, Set.ncard_coe_finset, ← Finset.sum_const]
  rw [hGKL.card_eq_finrank, ← sum_ramification_inertia B K L hpb]
  apply Finset.sum_congr rfl
  intro P hp
  rw [← Finset.mem_coe, coe_primesOverFinset hpb B] at hp
  obtain ⟨_, _⟩ := hp
  rw [ramificationIdxIn_eq_ramificationIdx p P G, inertiaDegIn_eq_inertiaDeg p P G]

end fundamental_identity

section inertia

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G] [Finite G]

open scoped Pointwise

open Algebra

attribute [local instance 1001] Ideal.Quotient.field Module.Free.of_divisionRing in
lemma ncard_primesOver_mul_card_inertia_mul_finrank (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    (p.primesOver S).ncard * Nat.card (P.toAddSubgroup.inertia G) *
      Module.finrank (R ⧸ p) (S ⧸ P) = Nat.card G := by
  trans (p.primesOver S).ncard * Nat.card (MulAction.stabilizer G P); swap
  · rw [← IsInvariant.orbit_eq_primesOver R S G p P]
    simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  rw [mul_assoc]
  have : IsGalois (R ⧸ p) (S ⧸ P) := { __ := Ideal.Quotient.normal (A := R) G p P }
  have := Ideal.Quotient.finite_of_isInvariant G p P
  congr 1
  have : Subgroup.index _ = _ := Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective (Ideal.Quotient.stabilizerHom P p G)
      (Ideal.Quotient.stabilizerHom_surjective G p P)).toEquiv
  rw [← IsGalois.card_aut_eq_finrank, ← this]
  convert (Ideal.Quotient.stabilizerHom P p G).ker.card_mul_index using 2
  rw [Ideal.Quotient.ker_stabilizerHom]
  refine Nat.card_congr (Subgroup.subgroupOfEquivOfLe ?_).toEquiv.symm
  intro σ hσ
  ext x
  rw [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
  convert P.add_mem_iff_right (inv_mem hσ x) (b := x) using 2
  simp

-- TODO : get rid of `K` and `L` in the statement (and replace with `[IsGaloisGroup G R S]`)
/-- The cardinality of the inertia group is equal to the ramification index. -/
lemma card_inertia_eq_ramificationIdxIn
    [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
    (K L : Type*) [Field K] [Field L] [Algebra K L] [Algebra R L] [Algebra R K] [Algebra S L]
    [IsScalarTower R S L] [IsScalarTower R K L] [IsFractionRing R K] [IsFractionRing S L]
    [MulSemiringAction G L] [IsGaloisGroup G K L]
    (p : Ideal R) (hp : p ≠ ⊥)
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (P.toAddSubgroup.inertia G) = Ideal.ramificationIdxIn p S := by
  letI := IsGaloisGroup.isGalois G K L
  letI := IsGaloisGroup.finiteDimensional G K L
  have := (show p.IsPrime from P.over_def p ▸ inferInstance).isMaximal hp
  have := NoZeroSMulDivisors.trans_faithfulSMul R K L
  have : NoZeroSMulDivisors R S := IsIntegralClosure.noZeroSMulDivisors R L
  have H := ncard_primesOver_mul_card_inertia_mul_finrank (G := G) p P
  refine mul_right_injective₀ (primesOver_ncard_ne_zero p S) ?_
  refine mul_left_injective₀ (b := Module.finrank (R ⧸ p) (S ⧸ P)) ?_ ?_
  · intro e; simp [e, eq_comm, Nat.card_eq_zero, ‹Finite G›.not_infinite] at H
  dsimp only
  rw [H, mul_assoc, ← Ideal.inertiaDeg_algebraMap,
    ← Ideal.inertiaDegIn_eq_inertiaDeg p P K L,
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp S K L,
    IsGaloisGroup.card_eq_finrank G K L]

end inertia

end Ideal
