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

/-! ### `ramificationIdx` and `inertiaDeg` in Galois extensions -/

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

section Galois

open IntermediateField AlgEquiv QuotientGroup

variable {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L] [Algebra E L]
 [FiniteDimensional K L]

-- have better defEq comparing with `FixedPoints.toAlgAutMulEquiv`
/-- If `H` is a subgroup of `Gal(L / K)`, then `Gal(L / fixedField H)` is isomorphic to `H`. -/
def IntermediateField.subgroup_equiv_aut (H : Subgroup (L ≃ₐ[K] L)) :
    (L ≃ₐ[fixedField H] L) ≃* H where
  toFun ϕ := ⟨ϕ.restrictScalars K, (fixingSubgroup_fixedField H).le ϕ.commutes⟩
  invFun ϕ := { toRingEquiv (ϕ : L ≃ₐ[K] L) with
    commutes' := (ge_of_eq (fixingSubgroup_fixedField H)) ϕ.mem }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

end Galois

open scoped Pointwise

section decompositionGroup

/-! ### decomposition group -/

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B)
  (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L]

/--The decomposition group of `P` over `K` is the stabilizer of `P` under the action of
  `L ≃ₐ[K] L`. -/
def decompositionGroup : Subgroup (L ≃ₐ[K] L) :=
  letI := IsIntegralClosure.MulSemiringAction A K L B
  MulAction.stabilizer (L ≃ₐ[K] L) P

variable {K} {L} in
/-- The decomposition group of `P` over `K` is consisting of all elements `σ` of the Galois group
  `L ≃ₐ[K] L` such that `σ P = P`. -/
theorem decompositionGroup_mem (σ : L ≃ₐ[K] L) :
    σ ∈ decompositionGroup A P K L ↔ map (galRestrict A K L B σ) P = P :=
  Iff.rfl

/-- The decomposition field of `P` over `K` is the fixed field of `decompositionGroup p P`. -/
def decompositionField : IntermediateField K L :=
  IntermediateField.fixedField (decompositionGroup A P K L)

end decompositionGroup

open IntermediateField FiniteDimensional

section decompositionIdeal

variable (A : Type*) [CommRing A] [IsDedekindDomain A] {p : Ideal A} (hpb : p ≠ ⊥) [p.IsMaximal]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
  (P : Ideal B) [P.IsPrime] [P.LiesOver p]
  (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]
  {D : Type*} [CommRing D] [IsDedekindDomain D] [Algebra D (decompositionField A P K L)]
  [IsFractionRing D (decompositionField A P K L)] [Algebra A D]
  [IsScalarTower A D (decompositionField A P K L)]
  [Algebra D B] [Module.Finite D B] [Algebra D L] [IsScalarTower D B L]
  [IsScalarTower D (decompositionField A P K L) L] [IsScalarTower A D B]
  (Pd : Ideal D) [Pd.IsMaximal] [P.LiesOver Pd]

include K L A in
omit [IsDedekindDomain A] [Algebra A D] [Pd.IsMaximal] in
/-- `P` is the unique ideal lying over the decomposition ideal. -/
theorem isMaximal_liesOver_decomposition_ideal_unique (Q : Ideal B) [Q.IsMaximal]
    [Q.LiesOver Pd] : Q = P := by
  obtain ⟨σ, hs⟩ := (isPretransitive_of_isGalois Pd (decompositionField A P K L) L).1
    (primesOver.mk Pd P) (primesOver.mk Pd Q)
  exact (Subtype.val_inj.mpr hs).symm.trans ((subgroup_equiv_aut (decompositionGroup A P K L)) σ).2

include A P K L in
omit [IsDedekindDomain A] [Algebra A D] in
theorem primes_over_decompositionIdeal_card_eq_one : (Pd.primesOver B).ncard = 1 :=
  Nat.card_eq_one_iff_exists.mpr ⟨primesOver.mk Pd P,
    fun Q ↦ Subtype.val_inj.mp <| isMaximal_liesOver_decomposition_ideal_unique A P K L Pd Q⟩

include hpb K L P

variable {A}

open Classical in
theorem decompositionGroup_card_eq_ramificationIdx_mul_inertiaDeg :
    Fintype.card (decompositionGroup A P K L) = ramificationIdxIn p B * inertiaDegIn p B := by
  letI := IsIntegralClosure.MulSemiringAction A K L B
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  have : Fintype (MulAction.orbit (L ≃ₐ[K] L) (primesOver.mk p P)) :=
    Set.fintypeRange fun m ↦ m • primesOver.mk p P
  apply mul_left_cancel₀ (primesOver_ncard_ne_zero p B)
  rw [ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hpb B K L]
  rw [← IsGalois.card_aut_eq_finrank, decompositionGroup]
  rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group (L ≃ₐ[K] L) (primesOver.mk p P)]
  simp only [← Set.Nat.card_coe_set_eq, Fintype.card_eq_nat_card]
  rw [MulAction.orbit_eq_univ, Nat.card_univ,
    show MulAction.stabilizer (L ≃ₐ[K] L) P = MulAction.stabilizer (L ≃ₐ[K] L) (primesOver.mk p P)
    from Subgroup.ext fun σ ↦ @Subtype.val_inj _ _ (σ • primesOver.mk p P) (primesOver.mk p P)]

theorem finrank_over_decompositionField_eq_ramificationIdx_mul_inertiaDeg :
    Module.finrank (decompositionField A P K L) L = ramificationIdxIn p B * inertiaDegIn p B := by
  classical rw [decompositionField, finrank_fixedField_eq_card (decompositionGroup A P K L)]
  rw [decompositionGroup_card_eq_ramificationIdx_mul_inertiaDeg hpb P K L]

private lemma ramificationIdx_and_inertiaDeg_of_decompositionIdeal :
    ramificationIdxIn Pd B = ramificationIdxIn p B ∧
    inertiaDegIn Pd B = inertiaDegIn p B := by
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  have : FaithfulSMul D B := FaithfulSMul.of_field_isFractionRing D B (decompositionField A P K L) L
  have : FaithfulSMul A D := FaithfulSMul.of_field_isFractionRing A D K (decompositionField A P K L)
  have : Pd.LiesOver p := LiesOver.tower_bot P Pd p
  have hdb : Pd ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hpb Pd
  have h := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hdb B
    (decompositionField A P K L) L
  rw [primes_over_decompositionIdeal_card_eq_one A P K L Pd, one_mul,
    finrank_over_decompositionField_eq_ramificationIdx_mul_inertiaDeg hpb] at h
  have h0 := ramificationIdx_pos P hpb
  have hr := Nat.le_of_dvd h0 <| Dvd.intro_left _ <| Eq.symm <|
    ramificationIdx_algebra_tower (map_ne_bot_of_ne_bot hdb) (map_ne_bot_of_ne_bot hpb) <|
      map_le_iff_le_comap.mpr (over_def P Pd).le
  have h0 : inertiaDeg p P > 0 := inertiaDeg_pos p P
  have hi := Nat.le_of_dvd h0 <| Dvd.intro_left _  (inertiaDeg_algebra_tower p Pd P).symm
  rw [ramificationIdxIn_eq_ramificationIdx Pd P (decompositionField A P K L) L,
    ramificationIdxIn_eq_ramificationIdx p P K L, inertiaDegIn_eq_inertiaDeg p P K L,
    inertiaDegIn_eq_inertiaDeg Pd P (decompositionField A P K L) L] at h ⊢
  exact (mul_eq_mul_iff_eq_and_eq_of_pos hr hi (ramificationIdx_pos P hdb) h0).mp h

theorem ramificationIdxIn_of_decompositionIdeal : ramificationIdxIn Pd B = ramificationIdxIn p B :=
  (ramificationIdx_and_inertiaDeg_of_decompositionIdeal hpb P K L Pd).1

theorem inertiaDegIn_of_decompositionIdeal : inertiaDegIn Pd B = inertiaDegIn p B :=
  (ramificationIdx_and_inertiaDeg_of_decompositionIdeal hpb P K L Pd).2

theorem ramificationIdx_of_decompositionideal_over_bot_eq_one :
    ramificationIdx (algebraMap A D) p Pd = 1 := by
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  have : FaithfulSMul D B := FaithfulSMul.of_field_isFractionRing D B (decompositionField A P K L) L
  have : FaithfulSMul A D := FaithfulSMul.of_field_isFractionRing A D K (decompositionField A P K L)
  have : Pd.LiesOver p := LiesOver.tower_bot P Pd p
  have h := ramificationIdx_algebra_tower
    (map_ne_bot_of_ne_bot (ne_bot_of_liesOver_of_ne_bot hpb Pd)) (map_ne_bot_of_ne_bot hpb) <|
      map_le_iff_le_comap.mpr (over_def P Pd).le
  rw [← ramificationIdxIn_eq_ramificationIdx Pd P (decompositionField A P K L) L,
    ramificationIdxIn_of_decompositionIdeal hpb P K L,
    ramificationIdxIn_eq_ramificationIdx p P K L] at h
  nth_rw 1 [← one_mul (ramificationIdx (algebraMap A B) p P)] at h
  exact mul_right_cancel₀ (ramificationIdx_pos P hpb).ne' h.symm

theorem inertiaDeg_of_decompositionideal_over_bot_eq_one : inertiaDeg p Pd = 1 := by
  have : Pd.LiesOver p := LiesOver.tower_bot P Pd p
  have h := inertiaDeg_algebra_tower p Pd P
  rw [← inertiaDegIn_eq_inertiaDeg Pd P (decompositionField A P K L) L,
    inertiaDegIn_of_decompositionIdeal hpb P K L, inertiaDegIn_eq_inertiaDeg p P K L] at h
  nth_rw 1 [← one_mul (inertiaDeg p P)] at h
  exact mul_right_cancel₀ (inertiaDeg_pos p P).ne.symm h.symm

end decompositionIdeal

section inertiaGroup

variable (A : Type*) [CommRing A] (p : Ideal A) {B : Type*} [CommRing B] [Algebra A B]
  (P : Ideal B) [P.LiesOver p]
  (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L]

/-- The inertia group of `P` over `K` is the subgorup of `L ≃ₐ[K] L` that consists of all
  the `σ : L ≃ₐ[K] L` that are identity modulo `P`. -/
def inertiaGroup : Subgroup (L ≃ₐ[K] L) where
  carrier := { σ | ∀ x : B, Ideal.Quotient.mk P (galRestrict A K L B σ x) = Ideal.Quotient.mk P x }
  mul_mem' := by
    intro _ τ hs ht x
    rw [← ht x, ← hs (galRestrict A K L B τ x), _root_.map_mul]
    rfl
  one_mem' _ := by
    rw [map_one, AlgEquiv.one_apply]
  inv_mem' := by
    intro σ hs x
    rw [show σ⁻¹ = σ.symm from rfl, ← hs (galRestrict A K L B σ.symm x)]
    exact congrArg (Ideal.Quotient.mk P) (((galRestrict A K L B) σ).apply_symm_apply x)

theorem inertiaGroup_le_decompositionGroup : inertiaGroup A P K L ≤ decompositionGroup A P K L := by
  refine fun σ hs ↦ Ideal.ext (fun x ↦ ?_)
  letI := IsIntegralClosure.MulSemiringAction A K L B
  have h : σ⁻¹ • x - (σ⁻¹ • x - x) ∈ P ↔ σ⁻¹ • x ∈ P :=
    Submodule.sub_mem_iff_left P (Ideal.Quotient.eq.mp (((inertiaGroup A P K L).inv_mem hs) x))
  rw [sub_sub_cancel] at h
  exact mem_pointwise_smul_iff_inv_smul_mem.trans h.symm
/-
variable {A}

/-- If `P` is the unique ideal lying over `p`, then the `inertiaGroup` is equal to the
kernel of the homomorphism `residueGaloisHom`. -/
theorem inertiaGroup_eq_ker :
    letI := IsIntegralClosure.MulSemiringAction A K L B;
    letI : SMulCommClass (L ≃ₐ[K] L) A B :=
    SMul.comp.smulCommClass (galRestrict A K L B).toMonoidHom
    inertiaGroup A P K L = MonoidHom.ker (Ideal.Quotient.stabilizerHom P p (L ≃ₐ[K] L)) := by
  ext σ
  rw [MonoidHom.mem_ker, AlgEquiv.ext_iff]
  constructor
  · rintro h ⟨x⟩
    nth_rw 2 [Submodule.Quotient.quot_mk_eq_mk]
    rw [Quotient.mk_eq_mk, ← h x]
    rfl
  · intro h x
    have h := h (Ideal.Quotient.mk P x)
    rw [AlgEquiv.one_apply] at h
    rw [← h]
    rfl

/-- If `P` is the unique ideal lying over `p`, then the `inertiaGroup K P` is a normal subgroup. -/
theorem inertiaGroup_normal {K L : Type*} [Field K] [Field L] [Algebra K L]
(p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal]
    [hp : P unique_lies_over p] : Subgroup.Normal (inertiaGroup K P) := by
  rw [inertiaGroup_eq_ker p P]
  exact MonoidHom.normal_ker (residueGaloisHom p P)

noncomputable def aut_quoutient_inertiaGroup_equiv_residueField_aut [Normal K L] :
    @MulEquiv ((L ≃ₐ[K] L) ⧸ (inertiaGroup K P)) (((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P))
    (letI := inertiaGroup_normal p P; inferInstance) _ :=
  letI := inertiaGroup_normal p P
  (QuotientGroup.quotientMulEquivOfEq (inertiaGroup_eq_ker p P)).trans <|
    QuotientGroup.quotientKerEquivOfSurjective _ (residueGaloisHom_surjective p P)

/-- The intermediate field fixed by `inertiaGroup K P`. -/
def inertiaFieldAux (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (P : Ideal (𝓞 L)) [P.IsMaximal] : IntermediateField K L :=
  fixedField (inertiaGroup K P)
 -/
end inertiaGroup
