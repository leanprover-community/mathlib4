/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Analysis.Complex.Polynomial.UnitTrinomial
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Relrank
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Invariant.Basic

/-!
# Irreducibility of Selmer Polynomials

This file proves irreducibility of the Selmer polynomials `X ^ n - X - 1`.

## Main results

- `X_pow_sub_X_sub_one_irreducible`: The Selmer polynomials `X ^ n - X - 1` are irreducible.

TODO: Show that the Selmer polynomials have full Galois group.
-/

section lem

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
  {M : Type*} [Monoid M] [MulSemiringAction M E] [SMulCommClass M F E]

@[simp] lemma IntermediateField.mem_fixedPoints_iff {x : E} :
    x ∈ (FixedPoints.intermediateField M : IntermediateField F E) ↔ ∀ m : M, m • x = x := Iff.rfl

end lem

section GeneralGalois

variable (G K L : Type*) [Group G] [Field K] [Field L] [Algebra K L] [MulSemiringAction G L]
   (H H' : Subgroup G) (F F' : IntermediateField K L)

namespace IsGaloisGroup

variable [hGKL : IsGaloisGroup G K L]

instance to_subgroup :
    IsGaloisGroup H (FixedPoints.intermediateField H : IntermediateField K L) L where
  faithful := have := hGKL.faithful; inferInstance
  commutes := ⟨fun g x y ↦ by
    simp_rw [Algebra.smul_def, IntermediateField.algebraMap_apply, smul_mul', x.2 g]⟩
  isInvariant := ⟨fun x h ↦ ⟨⟨x, h⟩, rfl⟩⟩

theorem card_subgroup_eq_finrank_fixedpoints :
    Nat.card H = Module.finrank (FixedPoints.intermediateField H : IntermediateField K L) L :=
  card_eq_finrank H (FixedPoints.intermediateField H) L

instance to_intermediateField [Finite G] :
    IsGaloisGroup (fixingSubgroup G (F : Set L)) F L where
  faithful := have := hGKL.faithful; inferInstance
  commutes := ⟨fun g x y ↦ by simp [Algebra.smul_def, Subgroup.smul_def, g.2 x]⟩
  isInvariant := ⟨fun x h ↦ ⟨⟨x, by
    have := hGKL.finiteDimensional
    have := hGKL.isGalois
    rw [← IsGalois.fixedField_fixingSubgroup F]
    intro ⟨g, hg⟩
    rw [Subtype.forall] at h
    simp only [Subgroup.mk_smul, IntermediateField.mem_fixingSubgroup_iff,
      mem_fixingSubgroup_iff] at h hg
    have key := mulEquivCongr_apply_smul (L ≃ₐ[K] L) G K L g x
    refine key.symm.trans (h _ (by simpa only [mulEquivCongr_apply_smul]))
  ⟩, rfl⟩⟩

theorem card_fixingSubgroup_eq_finrank [Finite G] :
    Nat.card (fixingSubgroup G (F : Set L)) = Module.finrank F L :=
  card_eq_finrank (fixingSubgroup G (F : Set L)) F L

end IsGaloisGroup

namespace IsGaloisGroup

theorem fixingSubgroup_le_of_le (h : F ≤ F') :
    fixingSubgroup G (F' : Set L) ≤ fixingSubgroup G (F : Set L) :=
  fun _ hσ ⟨x, hx⟩ ↦ hσ ⟨x, h hx⟩

section SMulCommClass

variable [SMulCommClass G K L]

theorem fixingSubgroup_bot : fixingSubgroup G ((⊥ : IntermediateField K L) : Set L) = ⊤ := by
  simp [Subgroup.ext_iff, mem_fixingSubgroup_iff, IntermediateField.mem_bot] -- simp lemmas?

theorem fixedPoints_bot :
    (FixedPoints.intermediateField (⊥ : Subgroup G) : IntermediateField K L) = ⊤ := by
  simp [IntermediateField.ext_iff]

theorem le_fixedPoints_iff_le_fixingSubgroup :
    F ≤ FixedPoints.intermediateField H ↔ H ≤ fixingSubgroup G (F : Set L) :=
  ⟨fun h g hg x => h (Subtype.mem x) ⟨g, hg⟩, fun h x hx g => h (Subtype.mem g) ⟨x, hx⟩⟩

theorem fixedPoints_le_of_le (h : H ≤ H') :
    FixedPoints.intermediateField H' ≤ (FixedPoints.intermediateField H : IntermediateField K L) :=
  fun _ hσ ⟨x, hx⟩ ↦ hσ ⟨x, h hx⟩

end SMulCommClass

variable [hGKL : IsGaloisGroup G K L]

theorem fixingSubgroup_top : fixingSubgroup G ((⊤ : IntermediateField K L) : Set L) = ⊥ := by
  simp only [Subgroup.ext_iff, mem_fixingSubgroup_iff, Subgroup.mem_bot]
  exact fun x ↦ ⟨fun h ↦ hGKL.faithful.eq_of_smul_eq_smul (by simpa using h), fun h ↦ by simp [h]⟩

theorem fixedPoints_top :
    (FixedPoints.intermediateField (⊤ : Subgroup G) : IntermediateField K L) = ⊥ := by
  simp only [eq_bot_iff, SetLike.le_def, IntermediateField.mem_fixedPoints_iff, Subtype.forall,
    Subgroup.mem_top, Subgroup.mk_smul, forall_const]
  exact hGKL.isInvariant.isInvariant

theorem fixingSubgroup_fixedPoints [Finite G] :
    fixingSubgroup G ((FixedPoints.intermediateField H : IntermediateField K L) : Set L) = H := by
  have : FiniteDimensional K L := hGKL.finiteDimensional
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · rw [← le_fixedPoints_iff_le_fixingSubgroup]
  · rw [hGKL.card_subgroup_eq_finrank_fixedpoints, hGKL.card_subgroup_eq_finrank_fixedpoints]
    apply IntermediateField.finrank_le_of_le_left
    rw [le_fixedPoints_iff_le_fixingSubgroup]

theorem fixedPoints_fixingSubgroup [Finite G] :
    FixedPoints.intermediateField (fixingSubgroup G (F : Set L)) = F := by
  have : FiniteDimensional K L := hGKL.finiteDimensional
  refine (IntermediateField.eq_of_le_of_finrank_eq' ?_ ?_).symm
  · rw [le_fixedPoints_iff_le_fixingSubgroup]
  · rw [← card_subgroup_eq_finrank_fixedpoints, card_fixingSubgroup_eq_finrank]

end IsGaloisGroup

end GeneralGalois

section Inertia

open scoped Pointwise

section Galois

variable (A K L B : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
  [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsIntegrallyClosed A] [IsIntegralClosure B A L]

-- todo: generalize this to arbitrary group acting
instance IsIntegralClosure.SMulCommClass [FiniteDimensional K L] :
    let _ := IsIntegralClosure.MulSemiringAction A K L B
    SMulCommClass (L ≃ₐ[K] L) A B := by
  intro
  exact ⟨fun f ↦ map_smul (galRestrict A K L B f)⟩

end Galois

section inertiadef

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (P : Ideal A) (Q : Ideal B) [Q.LiesOver P]
  (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

theorem Ideal.inertiaSubgroup_eq_ker : AddSubgroup.inertia Q.toAddSubgroup G =
    (Ideal.Quotient.stabilizerHom Q P G).ker.map (MulAction.stabilizer G Q).subtype := by
  simp_rw [Subgroup.ext_iff, AddSubgroup.mem_inertia, Submodule.mem_toAddSubgroup,
    Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.subtype_apply, AlgEquiv.ext_iff,
    AlgEquiv.one_apply, Submodule.Quotient.forall, Quotient.mk_eq_mk,
    Quotient.stabilizerHom_apply, Quotient.mk_eq_mk_iff_sub_mem]
  refine fun g ↦ ⟨fun h ↦ ⟨⟨g, ?_⟩, h, rfl⟩, fun ⟨g, h, hg⟩ x ↦ hg ▸ h x⟩
  rw [← Subgroup.inv_mem_iff, MulAction.mem_stabilizer_iff, Ideal.ext_iff]
  intro x
  rw [mem_inv_pointwise_smul_iff, iff_comm, ← Q.add_mem_iff_right (h x), sub_add_cancel]

end inertiadef

section inertiadef

variable {A : Type*} [CommRing A] [IsDedekindDomain A] {P : Ideal A} (hP : P ≠ ⊥) [P.IsMaximal]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
  (Q : Ideal B) [Q.IsPrime] (hQ : Q.LiesOver P)
  (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [FiniteDimensional K L] [hKL : IsGalois K L]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [MulSemiringAction G L]
  [SMulCommClass G A B] [Algebra.IsInvariant A B G] [IsGaloisGroup G K L]

-- need general galois group to have same cardinality as field extension

include hP hQ K L in
theorem Ideal.card_inertiaSubgroup [Algebra.IsSeparable (A ⧸ P) (B ⧸ Q)] :
    Nat.card (AddSubgroup.inertia Q.toAddSubgroup G) =
      Ideal.ramificationIdx (algebraMap A B) P Q := by
  rw [Ideal.inertiaSubgroup_eq_ker P Q G]
  have hf := Ideal.Quotient.stabilizerHom_surjective G P Q
  have : Finite ((B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q) := Finite.of_surjective _ hf
  have key := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hP B K L
  rw [← Algebra.IsInvariant.orbit_eq_primesOver A B G P Q, ← MulAction.index_stabilizer] at key
  have h1 : Nat.card G = Module.finrank K L := IsGaloisGroup.card_eq_finrank G K L
  have h2 : Nat.card ((B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q)) = Module.finrank (A ⧸ P) (B ⧸ Q) := by
    have : IsMaximal Q := Ideal.IsMaximal.of_liesOver_isMaximal Q P
    let _ : Field (A ⧸ P) := Quotient.field P
    let _ : Field (B ⧸ Q) := Quotient.field Q
    have := Ideal.Quotient.normal G P Q
    have := Ideal.Quotient.finite_of_isInvariant G P Q
    have : IsGalois (A ⧸ P) (B ⧸ Q) := { __ := Ideal.Quotient.normal (A := A) G P Q }
    rw [IsGalois.card_aut_eq_finrank]
  rw [inertiaDegIn_eq_inertiaDeg P Q K L, inertiaDeg_algebraMap] at key
  rw [← h1, ← h2, ← (MulAction.stabilizer G Q).index_mul_card] at key
  rw [mul_right_inj' Subgroup.index_ne_zero_of_finite] at key
  rw [← (Quotient.stabilizerHom Q P G).ker.card_mul_index, Subgroup.index_ker,
    MonoidHom.range_eq_top_of_surjective _ hf, Subgroup.card_top] at key
  rw [mul_left_inj' Nat.card_pos.ne'] at key
  rw [ramificationIdxIn_eq_ramificationIdx P Q K L] at key
  rw [Subgroup.card_subtype, key]

end inertiadef

end Inertia

namespace Polynomial

section Moore

-- Moore polynomial
-- monic polynomial degree n, at least n-1 distinct roots at each maximal ideal

-- possible that this doesn't need a separate definition?
def moore {R : Type*} [CommRing R] (f : R[X]) (S : Type*) [CommRing S] [Algebra R S] : Prop :=
  f.Monic ∧ ∀ m : MaximalSpectrum S, f.natDegree ≤ (f.rootSet (S ⧸ m.asIdeal)).ncard + 1

-- Galois group is generated by inertia subgroups, and each inertia subgroup is a transposition
-- Galois group is generated by transpositions

theorem aeval_smul {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] (f : R[X])
    (G : Type*) [Group G] [MulSemiringAction G S] [SMulCommClass G R S] (g : G) (x : S) :
    aeval (g • x) f = g • (aeval x f) := by
  rw [← MulSemiringAction.toAlgHom_apply R, aeval_algHom_apply, MulSemiringAction.toAlgHom_apply]

instance {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    [NoZeroSMulDivisors R S] (f : R[X])
    (G : Type*) [Group G] [MulSemiringAction G S] [SMulCommClass G R S] :
    MulAction G (f.rootSet S) where
  smul g x := ⟨g • x.1, by
    rw [mem_rootSet_of_ne (ne_zero_of_mem_rootSet x.2), aeval_smul,
      aeval_eq_zero_of_mem_rootSet x.2, smul_zero]⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

theorem _root_.Ideal.Quotient.mkₐ_apply (R₁ : Type*)
    {A : Type*} [CommSemiring R₁] [Ring A] [Algebra R₁ A]
    (I : Ideal A) [I.IsTwoSided] (x : A) : Ideal.Quotient.mkₐ R₁ I x = Ideal.Quotient.mk I x :=
  rfl

theorem _root_.Polynomial.Monic.mem_rootSet {T S : Type*} [CommRing T] [CommRing S] [IsDomain S]
    [Algebra T S] {p : T[X]} (hp : p.Monic) {a : S} : a ∈ p.rootSet S ↔ (aeval a) p = 0 := by
  simp [Polynomial.mem_rootSet', (hp.map (algebraMap T S)).ne_zero]

theorem tada -- R = ℤ, S = 𝓞 K
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S] [NoZeroSMulDivisors R S]
    (f : R[X]) (hmon : f.Monic) [DecidableEq (f.rootSet S)]
    (G : Type*) [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (m : MaximalSpectrum S)
     -- all roots already present (so no new roots in `S ⧸ m`)
    (hf : (f.map (algebraMap R S)).roots.card = f.natDegree)
    -- at most one collision
    (h : (f.rootSet S).ncard ≤ (f.rootSet (S ⧸ m.asIdeal)).ncard + 1) :
    ∀ g ∈ AddSubgroup.inertia m.asIdeal.toAddSubgroup G,
      MulAction.toPermHom G (f.rootSet S) g = 1 ∨
        (MulAction.toPermHom G (f.rootSet S) g).IsSwap := by
  intro g hg
  let π : S →ₐ[R] S ⧸ m.asIdeal := Ideal.Quotient.mkₐ R m.asIdeal
  have hπ (x : S) (hx : x ∈ f.rootSet S): π x ∈ f.rootSet (S ⧸ m.asIdeal) := by
    unfold π
    rw [hmon.mem_rootSet, aeval_algHom_apply, aeval_eq_zero_of_mem_rootSet hx, map_zero]
  have hπ (x : S) : π (g • x) = π x := (Ideal.Quotient.mk_eq_mk_iff_sub_mem (g • x) x).mpr (hg x)
  by_cases h₀ : ∃ x y : S, x ∈ f.rootSet S ∧ y ∈ f.rootSet S ∧ x ≠ y ∧ π x = π y; swap
  · sorry
  · sorry

theorem tada' {R S : Type*} [CommRing R] [Field S] [Algebra R S] [NoZeroSMulDivisors R S] (f : R[X])
    [Fact (f.Splits (algebraMap R S))] [DecidableEq (f.rootSet S)]
    (G : Type*) [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    [MulAction.IsPretransitive G (f.rootSet S)]
    (hG : ⨆ m : MaximalSpectrum S, AddSubgroup.inertia m.asIdeal.toAddSubgroup G = ⊤)
    (h : ∀ m : MaximalSpectrum S, f.natDegree ≤ (f.rootSet (S ⧸ m.asIdeal)).ncard + 1) :
    Function.Surjective (MulAction.toPermHom G (f.rootSet S)) := by
  let X := ⋃ m : MaximalSpectrum S,
    ((↑(AddSubgroup.inertia m.asIdeal.toAddSubgroup G : Subgroup G) : Set G) \ {1})
  have hS1 : Subgroup.closure X = ⊤ := by
    simpa only [X, Subgroup.closure_iUnion, Subgroup.closure_eq, Subgroup.closure_diff_one]
  have hS2 : ∀ σ ∈ X, (MulAction.toPermHom G (f.rootSet S) σ).IsSwap := by
    intro σ hσ
    simp only [X, Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff] at hσ
    obtain ⟨m, hm, hσ⟩ := hσ
    apply (tada f G m ?_ ?_ σ hm).resolve_left
    -- guess you really do need to assume faithful here?
    sorry
    sorry
    sorry
  exact surjective_of_isSwap_of_isPretransitive X hS2 hS1

-- if G is generated by inertia subgroups, then G is all of S_n
-- (i.e., MulAction.toPermHom is surjective)
-- surjective_of_isSwap_of_isPretransitive

end Moore

open scoped Polynomial

variable {n : ℕ}

theorem X_pow_sub_X_sub_one_irreducible_aux (z : ℂ) : ¬(z ^ n = z + 1 ∧ z ^ n + z ^ 2 = 0) := by
  rintro ⟨h1, h2⟩
  replace h3 : z ^ 3 = 1 := by
    linear_combination (1 - z - z ^ 2 - z ^ n) * h1 + (z ^ n - 2) * h2
  have key : z ^ n = 1 ∨ z ^ n = z ∨ z ^ n = z ^ 2 := by
    rw [← Nat.mod_add_div n 3, pow_add, pow_mul, h3, one_pow, mul_one]
    have : n % 3 < 3 := Nat.mod_lt n zero_lt_three
    interval_cases n % 3 <;>
    simp only [pow_zero, pow_one, or_true, true_or]
  have z_ne_zero : z ≠ 0 := fun h =>
    zero_ne_one ((zero_pow three_ne_zero).symm.trans (show (0 : ℂ) ^ 3 = 1 from h ▸ h3))
  rcases key with (key | key | key)
  · exact z_ne_zero (by rwa [key, right_eq_add] at h1)
  · exact one_ne_zero (by rwa [key, left_eq_add] at h1)
  · exact z_ne_zero (pow_eq_zero (by rwa [key, add_self_eq_zero] at h2))

theorem X_pow_sub_X_sub_one_irreducible (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℤ[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  rw [hp]
  apply IsUnitTrinomial.irreducible_of_coprime' ⟨0, 1, n, zero_lt_one, hn, -1, -1, 1, rfl⟩
  rintro z ⟨h1, h2⟩
  apply X_pow_sub_X_sub_one_irreducible_aux (n := n) z
  rw [trinomial_mirror zero_lt_one hn (-1 : ℤˣ).ne_zero (1 : ℤˣ).ne_zero] at h2
  simp_rw [trinomial, aeval_add, aeval_mul, aeval_X_pow, aeval_C,
    Units.val_neg, Units.val_one, map_neg, map_one] at h1 h2
  replace h1 : z ^ n = z + 1 := by linear_combination h1
  replace h2 := mul_eq_zero_of_left h2 z
  rw [add_mul, add_mul, add_zero, mul_assoc (-1 : ℂ), ← pow_succ, Nat.sub_add_cancel hn.le] at h2
  rw [h1] at h2 ⊢
  exact ⟨rfl, by linear_combination -h2⟩

theorem X_pow_sub_X_sub_one_irreducible_rat (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℚ[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have h := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast ?_).mp
    (X_pow_sub_X_sub_one_irreducible hn1)
  · rwa [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one,
      Polynomial.map_X] at h
  · exact hp.symm ▸ (trinomial_monic zero_lt_one hn).isPrimitive

open Equiv Pointwise

open IntermediateField

attribute [local instance] Gal.splits_ℚ_ℂ

open NumberField

variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
  (G : Type*) [Group G] [MulSemiringAction G K] [MulSemiringAction G (𝓞 K)] [SMulCommClass G ℚ K]

theorem keythm :
    ⨆ (q : Ideal (𝓞 K)) (hq : q.IsMaximal), AddSubgroup.inertia q.toAddSubgroup G = ⊤ := by
  -- key idea: fixed field of this subgroup has no ramified primes
  let H := ⨆ (q : Ideal (𝓞 K)) (hq : q.IsMaximal), AddSubgroup.inertia q.toAddSubgroup G
  let F : IntermediateField ℚ K := FixedPoints.intermediateField H
  change H = ⊤
  suffices h : F = ⊥ by
    -- rw [← fixingSubgroup_fixedField H]
    -- change fixingSubgroup F = ⊤
    -- rw [h, IntermediateField.fixingSubgroup_bot]
    sorry
  have : H.Normal := sorry
  have : IsGalois ℚ F := sorry
  have key0 : ∀ (q : Ideal (𝓞 K)) (hq : q.IsMaximal),
      AddSubgroup.inertia q.toAddSubgroup G ≤ H := by
    intro q hq
    exact le_iSup_of_le q (le_iSup_of_le hq le_rfl)
  -- have key : ∀ (q : Ideal (𝓞 F)) (hq : q.IsMaximal), inertiaSubgroup q = ⊥ := by
  --   intro q hq
  --   -- take prime of K lying over F
  --   -- inertia subgroup in F is quotient by H
  --   sorry
  suffices h : ¬ 1 < Module.finrank ℚ F by
    rw [← IntermediateField.finrank_eq_one_iff]
    rw [not_lt] at h
    refine le_antisymm h ?_
    rw [Nat.succ_le_iff]
    refine @Module.finrank_pos ℚ F _ _ _ _ _ ?_ _
    exact Module.Free.noZeroSMulDivisors ℚ ↥F
  intro h
  -- maybe better to use discriminant ideal here?
  replace h := NumberField.abs_discr_gt_two h
  sorry

-- x ^ n - x - 1 = 0 (mod p)
-- n x ^ (n - 1) - 1 = 0 (mod p)
--
-- x ^ n = x + 1
-- x ^ (n - 1) = 1 / n
-- x ^ n = x * (1 / n)
-- x + 1 = x * (1 / n)
-- x = 1 / ((1 / n) - 1)
-- x = n / (n - 1)

theorem tada {G S T : Type*} [Group G] [MulAction G S] [MulAction G T]
    [DecidableEq S] [DecidableEq T]
    (f : S →[G] T) (σ : G)
    (hσS : MulAction.toPermHom G S σ ≠ 1) (hσT : MulAction.toPermHom G T σ = 1)
    (h : ∀ s : Finset S, s.card ≤ (s.image f).card + 1) :
    (MulAction.toPermHom G S σ).IsSwap := by
  classical
  simp_rw [ne_eq, MulAction.toPermHom_apply, Perm.IsSwap, Perm.ext_iff, MulAction.toPerm_apply,
    Perm.one_apply, not_forall, ← ne_eq] at hσS hσT ⊢
  have h1 (x : S) : σ • σ • x = x := by
    contrapose! h
    have h' : σ • x ≠ x := by
      contrapose! h
      rw [h, h]
    use {σ • σ • x, σ • x, x}
    rw [Finset.card_eq_three.mpr ⟨σ • σ • x, σ • x, x, by simpa, h, h', rfl⟩]
    simp [hσT]
  obtain ⟨x, hx⟩ := hσS
  refine ⟨σ • x, x, hx, fun y ↦ ?_⟩
  rcases eq_or_ne y (σ • x) with rfl | h2
  · rw [swap_apply_left, h1]
  rcases eq_or_ne y x with rfl | h3
  · rw [swap_apply_right]
  rw [swap_apply_of_ne_of_ne h2 h3]
  contrapose! h
  use {y, σ • x, σ • y, x}
  rw [Finset.card_insert_of_notMem (by simp [h2, h3, h.symm]),
    Finset.card_insert_of_notMem (by simp [hx, h3.symm]), Finset.card_pair]
  · rw [Nat.lt_add_one_iff]
    simp [hσT, Finset.card_le_two]
  · rw [← h1 x]
    simp [h2]

theorem switchinglemma {F : Type*} [Field F] (p : F[X])
    (E₁ E₂ : Type*) [Field E₁] [Algebra F E₁] [Field E₂] [Algebra F E₂]
    [Fact (p.Splits (algebraMap F E₁))] [Fact (p.Splits (algebraMap F E₂))] :
    Gal.galActionHom p E₁ =
      ((Polynomial.Gal.rootsEquivRoots p E₂).symm.trans
        (Polynomial.Gal.rootsEquivRoots p E₁)).permCongrHom.toMonoidHom.comp
        (Gal.galActionHom p E₂)
       := by
  ext
  simp [permCongrHom, permCongrHom, Gal.galActionHom, Polynomial.Gal.smul_def]

attribute [-instance] Polynomial.Gal.galActionAux -- should be local to PolynomialGaloisGroup.lean

theorem X_pow_sub_X_sub_one_gal :
    Function.Bijective (Gal.galActionHom (X ^ n - X - 1 : ℚ[X]) ℂ) := by
  classical
  let f : ℚ[X] := X ^ n - X - 1
  let K := f.SplittingField
  have : Fact (f.Splits (algebraMap ℚ K)) := ⟨SplittingField.splits f⟩
  have : NumberField K := by constructor
  have : IsGalois ℚ K := by constructor
  let R := 𝓞 K
  let G := f.Gal
  suffices Function.Bijective (Gal.galActionHom f K) by
    rw [switchinglemma f ℂ K]
    exact (((Gal.rootsEquivRoots f f.SplittingField).symm.trans
      (Gal.rootsEquivRoots f ℂ)).permCongrHom.toEquiv.comp_bijective _).mpr this
  have : MulAction.IsPretransitive G (f.rootSet K) := by
    rcases eq_or_ne n 1 with rfl | hn
    · have : IsEmpty (rootSet f K) := by simp [f]
      infer_instance
    exact Gal.galAction_isPretransitive _ _ (X_pow_sub_X_sub_one_irreducible_rat hn)
  let _ : MulSemiringAction G R := IsIntegralClosure.MulSemiringAction ℤ ℚ K R
  let S : Set G := ⋃ (q : Ideal R) (hq : q.IsMaximal),
    ((↑(AddSubgroup.inertia q.toAddSubgroup G : Subgroup G) : Set G) \ {1})
  have hS1 : Subgroup.closure S = ⊤ := by
    simp only [S, Subgroup.closure_iUnion, Subgroup.closure_eq, Subgroup.closure_diff_one]
    exact keythm K _
  suffices hS2 : ∀ σ ∈ S, Perm.IsSwap (MulAction.toPermHom f.Gal (f.rootSet K) σ) by
    exact ⟨Gal.galActionHom_injective f K, surjective_of_isSwap_of_isPretransitive S hS2 hS1⟩
  simp only [S, Set.mem_diff, Set.mem_iUnion]
  rintro σ ⟨q, hq, hσ, hσ1 : σ ≠ 1⟩
  let H : Subgroup G := inertiaSubgroup q
  let F := R ⧸ q
  let π : R →+* F := Ideal.Quotient.mk q
  have : Field F := Ideal.Quotient.field q
  have : MulAction H (f.rootSet K) := inferInstance
  have : MulAction H F := sorry
  let ϕ : f.rootSet K → F := sorry -- equivariant map under which σ acts trivially
  let f' : F[X] := X ^ n - X - 1


  clear hS1 S

  -- σ ∈ inertiaSubgroup q
  -- σ acts trivially on the

  -- finite field, might not need to consider the characteristic
  -- reduce to action on roots in R
  sorry

  -- have : ∀ p : Nat.Primes, ∀ q : factors (map (algebraMap ℤ R) p)
  -- roots lie in the ring of integers OK
  -- if q is a prime idea of OK, then there is a ring homomorphism to the finite field OK/q
  -- the whole Galois group acts on OK
  -- the decomposition group acts on OK/q
  -- the inertia group acts trivially on OK/q
  --
  -- there are n roots in OK
  -- there are n or n-1 roots in OK/q (possible double root)
  -- Let σ(x) = x (mod p) for all x in OK
  -- If there are n roots in OK/q, then σ must act trivially on the roots in OK
  -- If x and y collapse (mod p), then maybe σ swaps x and y, but no more
  -- Now run through p's and σ's

  -- the key is proving closure/generating
  -- we need to know that if a subgroup contains every σ(x) = x (mod p) for every p, then it's ⊤
  -- we need to know that if a subfield is fixed by ..., then it's ⊥
  -- key facts from algebraic number theory: p divides discriminant implies ramified
  -- ramified means there exists σ(x) = x (mod p)

end Polynomial
