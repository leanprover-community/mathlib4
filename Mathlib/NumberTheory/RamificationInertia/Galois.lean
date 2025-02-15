/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Jiedong Jiang
-/
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Invariant

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

open Algebra Ideal

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

instance : MulAction (B ≃ₐ[A] B) (primesOver p B) where
  smul σ Q := primesOver.mk p (map σ Q.1)
  one_smul Q := Subtype.val_inj.mp (map_id Q.1)
  mul_smul σ τ Q := Subtype.val_inj.mp (Q.1.map_map τ.toRingHom σ.toRingHom).symm

@[simp]
theorem coe_smul_primesOver (σ : B ≃ₐ[A] B) (P : primesOver p B): (σ • P).1 = map σ P :=
  rfl

@[simp]
theorem coe_smul_primesOver_mk (σ : B ≃ₐ[A] B) (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    (σ • primesOver.mk p P).1 = map σ P :=
  rfl

variable (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
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

theorem coe_smul_primesOver_eq_map_galRestrict (σ : L ≃ₐ[K] L) (P : primesOver p B):
    (σ • P).1 = map (galRestrict A K L B σ) P :=
  rfl

theorem coe_smul_primesOver_mk_eq_map_galRestrict (σ : L ≃ₐ[K] L) (P : Ideal B) [P.IsPrime]
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

theorem isPretransitive_of_isGalois' [IsGalois K L] :
    MulAction.IsPretransitive (B ≃ₐ[A] B) (primesOver p B) where
  exists_smul_eq := by
    intro ⟨P, _, _⟩ ⟨Q, _, _⟩
    rcases exists_map_eq_of_isGalois p P Q K L with ⟨σ, hs⟩
    exact ⟨σ, Subtype.val_inj.mp hs⟩

instance isPretransitive_of_isGalois [IsGalois K L] :
    MulAction.IsPretransitive (L ≃ₐ[K] L) (primesOver p B) where
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

/-- The `inertiaDegIn` is equal to any ramification index over the same ideal. -/
theorem inertiaDegIn_eq_inertiaDeg [p.IsMaximal] [IsGalois K L] :
    inertiaDegIn p B = inertiaDeg p P := by
  have h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [inertiaDegIn, dif_pos h]
  exact inertiaDeg_eq_of_isGalois p h.choose P K L

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
  rw [← smul_eq_mul, ← coe_primesOverFinset hpb B, Set.ncard_coe_Finset, ← Finset.sum_const]
  rw [← sum_ramification_inertia B p K L hpb]
  apply Finset.sum_congr rfl
  intro P hp
  rw [← Finset.mem_coe, coe_primesOverFinset hpb B] at hp
  obtain ⟨_, _⟩ := hp
  rw [ramificationIdxIn_eq_ramificationIdx p P K L, inertiaDegIn_eq_inertiaDeg p P K L]

end fundamental_identity

end Ideal

section decompositionGroup

/-! ### decomposition Group -/

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A)
  (P : Ideal B) [P.IsPrime] [P.LiesOver p]
  (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [IsIntegralClosure B A L] [FiniteDimensional K L]

-- Maybe defined it as `MulAction.stabilizer (L ≃ₐ[K] L) P` is better, since maybe in this way
-- ` P ∈ decompositionGroup p P K L` is `defEq` to `map (galRestrict A K L B σ) P = P`.
/-- The decomposition group of `P` over `K`, is the stabilizer of `P` under the action of
  `Gal(L / K)`. -/
def decompositionGroup : Subgroup (L ≃ₐ[K] L) :=
  MulAction.stabilizer _ (primesOver.mk p P)

variable {K} {L} in
/-- The `decompositionGroup` is consisting of all elements of the Galois group `L ≃ₐ[K] L` such
that keep `P` invariant. -/
theorem decompositionGroup_mem (σ : L ≃ₐ[K] L) :
    σ ∈ decompositionGroup p P K L ↔ map (galRestrict A K L B σ) P = P := by
  rw [decompositionGroup, MulAction.mem_stabilizer_iff, ← Subtype.val_inj]
  rw [coe_smul_primesOver_mk_eq_map_galRestrict]

theorem decompositionGroup_mem' (σ : B ≃ₐ[A] B) :
    (galRestrict A K L B).symm σ ∈ decompositionGroup p P K L ↔ map σ P = P := sorry

/-- The decomposition field of `P` over `K` is the fixed field of `decompositionGroup p P`. -/
def decompositionField : IntermediateField K L :=
  IntermediateField.fixedField (decompositionGroup p P K L)

end decompositionGroup

open IntermediateField FiniteDimensional

section decompositionIdeal

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B] {p : Ideal A} (hpb : p ≠ ⊥) [p.IsMaximal]
  (P : Ideal B) [P.IsPrime] [hp : P.LiesOver p]
  (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]
  {D : Type*} [CommRing D] [IsDedekindDomain D]
  [Algebra A D] [Module.Finite A D] [Algebra D (decompositionField p P K L)]
  [IsFractionRing D (decompositionField p P K L)] [IsScalarTower A D (decompositionField p P K L)]
  [Algebra D B] [Module.Finite D B] [Algebra D L] [IsScalarTower D B L]
  [IsScalarTower D (decompositionField p P K L) L] [IsScalarTower A D B]
  (Pd : Ideal D) [P.LiesOver Pd] [Pd.LiesOver p]

include K L hpb

theorem decompositionGroup_card_eq_ramificationIdx_mul_inertiaDeg :
    Nat.card (decompositionGroup p P K L) = ramificationIdxIn p B * inertiaDegIn p B := by
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  apply mul_left_cancel₀ (primesOver_ncard_ne_zero p B)
  have : Fintype (MulAction.orbit (L ≃ₐ[K] L) (primesOver.mk p P)) := by
    classical exact Set.fintypeRange fun m ↦ m • primesOver.mk p P
  have : Fintype (decompositionGroup p P K L) := Fintype.ofFinite (decompositionGroup p P K L)
  have : Fintype (MulAction.stabilizer (L ≃ₐ[K] L) (primesOver.mk p P)) := this
  rw [ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hpb B K L,
    ← IsGalois.card_aut_eq_finrank, decompositionGroup]
  rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group (L ≃ₐ[K] L) (primesOver.mk p P)]
  rw [← Set.Nat.card_coe_set_eq, Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  rw [MulAction.orbit_eq_univ, Nat.card_univ]

theorem finrank_over_decompositionField_eq_ramificationIdx_mul_inertiaDeg :
    Module.finrank (decompositionField p P K L) L = ramificationIdxIn p B * inertiaDegIn p B := by
  classical
  rw [decompositionField, finrank_fixedField_eq_card (decompositionGroup p P K L)]
  rw [Fintype.card_eq_nat_card, decompositionGroup_card_eq_ramificationIdx_mul_inertiaDeg hpb P K L]

section Galois

open IntermediateField AlgEquiv QuotientGroup

variable {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L] [Algebra E L]
 [FiniteDimensional K L]

-- have better defEq comparing with `FixedPoints.toAlgAutMulEquiv`
/-- If `H` is a subgroup of `Gal(L/K)`, then `Gal(L / fixedField H)` is isomorphic to `H`. -/
def IntermediateField.subgroup_equiv_aut (H : Subgroup (L ≃ₐ[K] L)) :
    (L ≃ₐ[fixedField H] L) ≃* H where
  toFun ϕ := ⟨ϕ.restrictScalars K, le_of_eq (fixingSubgroup_fixedField H) ϕ.commutes⟩
  invFun ϕ := { toRingEquiv (ϕ : L ≃ₐ[K] L) with
    commutes' := (ge_of_eq (fixingSubgroup_fixedField H)) ϕ.mem }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

end Galois

/-- `P` is the unique ideal lying over the decomposition ideal. -/
theorem isMaximal_liesOver_decomposition_ideal_unique (Q : Ideal B) [Q.IsMaximal]
    [Q.LiesOver Pd] : Q = P := by
  have : Q.LiesOver p := LiesOver.trans Q Pd p
  rcases (isPretransitive_of_isGalois Pd (decompositionField p P K L) L).1
    (primesOver.mk Pd P) (primesOver.mk Pd Q) with ⟨σ, hs⟩
  have hs : map (galRestrict D (decompositionField p P K L) L B σ) P = Q := Subtype.val_inj.mpr hs
  let τ := (subgroup_equiv_aut (decompositionGroup p P K L)) σ
  have h := (decompositionGroup_mem p P τ.1).mp τ.2
  have : AlgEquiv.restrictScalars A ((galRestrict D (↥(decompositionField p P K L)) L B) σ) =
      (galRestrict A K L B) τ := by
    rfl
  exact hs.symm.trans ((decompositionGroup_mem p P τ.1).mp τ.2)
  /- rcases exists_map_eq_of_isGalois Pd P Q (decompositionField p P K L) L with ⟨σ, hs⟩
  let τ := (subgroup_equiv_aut (decompositionGroup p P K L)).toFun <|
    (galRestrict D (decompositionField p P K L) L B).symm σ
  have h := (decompositionGroup_mem p P τ.1).mp τ.2
  simp [τ, subgroup_equiv_aut] at h
  have : ((galRestrict A K L B) ((subgroup_equiv_aut (decompositionGroup p P K L))
  ((galRestrict D (↥(decompositionField p P K L)) L B).symm σ))).toFun = σ.toFun := by
    simp [subgroup_equiv_aut]
    --show (galRestrict A K L B) ((galRestrict A K L B).symm (AlgEquiv.restrictScalars A σ)) x = σ x
    have : (AlgEquiv.restrictScalars K ((galRestrict D (↥(decompositionField p P K L)) L B).symm σ))
     = (galRestrict A K L B).symm (AlgEquiv.restrictScalars A σ) := by
      ext x
      simp only [AlgEquiv.coe_restrictScalars']
      sorry
    sorry
  sorry -/
  -- rw [← h, ← hs]

  --rw [← hs, (decompositionGroup_mem p P τ.1).mp τ.2]
/-
/-- An alternative statement of `isMaximal_lies_over_decompositionideal_unique`. -/
theorem primes_over_decompositionideal_card_eq_one [IsGalois K L] :
  Finset.card (primes_over (decompositionIdeal p P) L) = 1 :=
    unique_primes_over_card_eq_one (decompositionIdeal p P) P

private lemma ramificationIdx_and_inertiaDeg_of_decompositionIdeal [IsGalois K L] :
    ramificationIdx_of_isGalois (decompositionIdeal p P) L = ramificationIdx_of_isGalois p L ∧
    inertiaDeg_of_isGalois (decompositionIdeal p P) L = inertiaDeg_of_isGalois p L := by
  let Pz := idealUnder (decompositionField p P) P
  let E := { x // x ∈ decompositionField p P }
  have h := ramificationIdx_mul_inertiaDeg_of_isGalois Pz L
  rw [primes_over_decompositionideal_card_eq_one p P, one_mul,
    finrank_over_decompositionField_eq_ramificationIdx_mul_inertiaDeg p P] at h
  have h0 := Nat.pos_of_ne_zero <| IsDedekindDomain.ramificationIdx_ne_zero
    (map_isMaximal_ne_bot p L) inferInstance (map_le_of_le_comap (le_of_eq hp.over))
  have hr := Nat.le_of_dvd h0 <| Dvd.intro_left _ <| Eq.symm <|
    ramificationIdx_algebra_tower (map_isMaximal_ne_bot Pz L)
      (map_isMaximal_ne_bot p L) (map_le_iff_le_comap.mpr (le_of_eq rfl))
  have h0 : inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p P > 0 := inertiaDeg_pos p P
  have hi := Nat.le_of_dvd h0 <| Dvd.intro_left _  <| Eq.symm <|
    inertiaDeg_algebra_tower p (decompositionIdeal p P) P
  rw [ramificationIdx_eq_ramificationIdx_of_isGalois Pz P,
    ramificationIdx_eq_ramificationIdx_of_isGalois p P] at hr
  rw [inertiaDeg_eq_inertiaDeg_of_isGalois Pz P, inertiaDeg_eq_inertiaDeg_of_isGalois p P] at hi
  have hr0 := Nat.pos_of_ne_zero <| IsDedekindDomain.ramificationIdx_ne_zero
    (map_isMaximal_ne_bot Pz L) inferInstance (map_le_of_le_comap (le_of_eq rfl))
  rw [inertiaDeg_eq_inertiaDeg_of_isGalois p P] at h0
  rw [ramificationIdx_eq_ramificationIdx_of_isGalois Pz P] at hr0
  exact (mul_eq_mul_iff_eq_and_eq_of_pos hr hi hr0 h0).mp h

theorem ramificationIdx_of_decompositionIdeal [IsGalois K L] :
  ramificationIdx_of_isGalois (decompositionIdeal p P) L = ramificationIdx_of_isGalois p L :=
    (ramificationIdx_and_inertiaDeg_of_decompositionIdeal p P).1

theorem inertiaDeg_of_decompositionIdeal [IsGalois K L] :
  inertiaDeg_of_isGalois (decompositionIdeal p P) L = inertiaDeg_of_isGalois p L :=
    (ramificationIdx_and_inertiaDeg_of_decompositionIdeal p P).2

theorem ramificationIdx_of_decompositionideal_over_bot_eq_one [IsGalois K L] : ramificationIdx
    (algebraMap (𝓞 K) (𝓞 (decompositionField p P))) p (decompositionIdeal p P) = 1 := by
  let Pz := idealUnder (decompositionField p P) P
  have h := ramificationIdx_algebra_tower (map_isMaximal_ne_bot Pz L)
    (map_isMaximal_ne_bot p L) (map_le_iff_le_comap.mpr (le_of_eq rfl))
  rw [ramificationIdx_eq_ramificationIdx_of_isGalois Pz P,
    ramificationIdx_of_decompositionIdeal p P,
    ← ramificationIdx_eq_ramificationIdx_of_isGalois p P] at h
  nth_rw 1 [← one_mul (ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p P)] at h
  exact mul_right_cancel₀ (IsDedekindDomain.ramificationIdx_ne_zero (map_isMaximal_ne_bot p L)
    inferInstance (map_le_of_le_comap (le_of_eq hp.over))) h.symm

/-- The residue class field corresponding to `decompositionField p P` is isomorphic to
residue class field corresponding to `p`. -/
theorem inertiaDeg_of_decompositionideal_over_bot_eq_one [IsGalois K L] : inertiaDeg
    (algebraMap (𝓞 K) (𝓞 (decompositionField p P))) p (decompositionIdeal p P) = 1 := by
  have h := inertiaDeg_algebra_tower p (decompositionIdeal p P) P
  rw [inertiaDeg_eq_inertiaDeg_of_isGalois (idealUnder (decompositionField p P) P) P,
    inertiaDeg_of_decompositionIdeal p P, ← inertiaDeg_eq_inertiaDeg_of_isGalois p P] at h
  nth_rw 1 [← one_mul (inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p P)] at h
  exact mul_right_cancel₀ (inertiaDeg_pos p P).ne.symm h.symm

end decompositionIdeal
-/
