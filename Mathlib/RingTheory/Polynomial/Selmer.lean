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
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Invariant.Basic

/-!
# Irreducibility and Galois Groups of Selmer Polynomials

This file shows that the Selmer polynomial `X ^ n - X - 1` is irreducible with Galois group `S_n`.

## Main results

- `X_pow_sub_X_sub_one_irreducible`: The Selmer polynomials `X ^ n - X - 1` are irreducible.
- `X_pow_sub_X_sub_one_gal`: The Selmer polynomial `X ^ n - X - 1` has Galois group `S_n`.
-/

section GeneralGalois

variable (G K L : Type*) [Group G] [Field K] [Field L] [Algebra K L] [MulSemiringAction G L]
   (H H' : Subgroup G) (F F' : IntermediateField K L)

namespace IsGaloisGroup

variable [hGKL : IsGaloisGroup G K L]

protected theorem finite [FiniteDimensional K L] : Finite G := by
  apply Nat.finite_of_card_ne_zero
  rw [hGKL.card_eq_finrank]
  exact Module.finrank_pos.ne'

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
  simp only [eq_bot_iff, SetLike.le_def, FixedPoints.mem_intermediateField_iff, Subtype.forall,
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

section inertiadef

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (P : Ideal A) (Q : Ideal B) [Q.LiesOver P]
  (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

theorem Ideal.inertiaSubgroup_eq_ker : Q.toAddSubgroup.inertia G =
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
  (Q : Ideal B) [Q.IsPrime] [hQ : Q.LiesOver P] [NoZeroSMulDivisors A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

include hP in
theorem Ideal.card_inertiaSubgroup [Algebra.IsSeparable (A ⧸ P) (B ⧸ Q)] :
    Nat.card (Q.toAddSubgroup.inertia G) =
      Ideal.ramificationIdx (algebraMap A B) P Q := by
  let K := FractionRing A
  let L := FractionRing B
  have : FaithfulSMul A L := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq A B L]
    apply (IsFractionRing.injective B L).comp
    exact NoZeroSMulDivisors.iff_algebraMap_injective.mp inferInstance
  let : Algebra K L := FractionRing.liftAlgebra A L
  let _ : MulSemiringAction G L := MulSemiringAction.compHom L
      ((IsFractionRing.fieldEquivOfAlgEquivHom K L).comp (MulSemiringAction.toAlgAut G A B))
  have hGKL : IsGaloisGroup G K L := IsGaloisGroup.toIsFractionRing G A B K L
  have : IsGalois K L := hGKL.isGalois
  have : FiniteDimensional K L := hGKL.finiteDimensional
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

section inertia

theorem AddSubgroup.subgroupOf_inertia {M : Type*} [AddGroup M] (I : AddSubgroup M)
    (G : Type*) [Group G] [MulAction G M] (H : Subgroup G) :
    (I.inertia G).subgroupOf H = I.inertia H :=
  rfl

end inertia

section ram

open IsGaloisGroup

open NumberField

instance (K : Type*) [Field K] [NumberField K]
    (G : Type*) [Group G] [MulSemiringAction G K] : MulSemiringAction G (𝓞 K) where
  smul := fun g x ↦ ⟨g • (x : K), sorry⟩
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  smul_one := sorry
  smul_mul := sorry

instance inst4 (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (G : Type*) [Group G] [MulSemiringAction G L] [IsGaloisGroup G K L] :
    IsGaloisGroup G (𝓞 K) (𝓞 L) := by
  sorry

theorem genthm₀ (K : Type*) [Field K] [NumberField K]
    (G : Type*) [Group G] [MulSemiringAction G K]
    [IsGaloisGroup G ℚ K] :
    ⨆ m : MaximalSpectrum (𝓞 K), m.asIdeal.toAddSubgroup.inertia G = ⊤ := by
  have : Finite G := IsGaloisGroup.finite G ℚ K
  set H : Subgroup G := ⨆ m : MaximalSpectrum (𝓞 K), m.asIdeal.toAddSubgroup.inertia G
  rw [eq_top_iff, ← fixingSubgroup_fixedPoints G ℚ K H, ← le_fixedPoints_iff_le_fixingSubgroup,
    fixedPoints_top, le_bot_iff]
  set F : IntermediateField ℚ K := FixedPoints.intermediateField H
  have h : ∀ m : MaximalSpectrum (𝓞 K), m.asIdeal.toAddSubgroup.inertia G ≤ H := le_iSup _
  replace h (m : MaximalSpectrum (𝓞 K)) : Nat.card (m.asIdeal.toAddSubgroup.inertia H) =
      Nat.card (m.asIdeal.toAddSubgroup.inertia G) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (h m), Subgroup.card_subtype,
      AddSubgroup.subgroupOf_inertia]
  replace h (m : MaximalSpectrum (𝓞 K)) :
    Ideal.ramificationIdx (algebraMap (𝓞 F) (𝓞 K)) (m.asIdeal.under (𝓞 F)) m.asIdeal =
      Ideal.ramificationIdx (algebraMap (𝓞 ℚ) (𝓞 K)) (m.asIdeal.under (𝓞 ℚ)) m.asIdeal := by
    -- have : IsGalois ℚ K := IsGaloisGroup.isGalois G ℚ K
    -- have : IsGalois F K := (IsGaloisGroup.to_subgroup G ℚ K H).isGalois
    -- have : SMulCommClass (H) (𝓞 F) (𝓞 K) := sorry
    -- have : Algebra.IsInvariant (𝓞 F) (𝓞 K) H := sorry
    -- have : Algebra.IsInvariant ℤ (𝓞 K) G := sorry
    have : Algebra.IsSeparable (𝓞 F ⧸ Ideal.under (𝓞 F) m.asIdeal) (𝓞 K ⧸ m.asIdeal) := sorry
    have : Algebra.IsSeparable (𝓞 ℚ ⧸ Ideal.under (𝓞 ℚ) m.asIdeal) (𝓞 K ⧸ m.asIdeal) := sorry
    have key := @Ideal.card_inertiaSubgroup (𝓞 F) _ _ (m.asIdeal.under (𝓞 F)) ?_ _ (𝓞 K) _ _
      _ _ m.asIdeal _ _ _ H _ _ _ _ _
    rw [← @Ideal.card_inertiaSubgroup (𝓞 F) _ _ (m.asIdeal.under (𝓞 F)) ?_ _ (𝓞 K) _ _
      _ _ m.asIdeal _ _ _ H _ _ _ _ _]
    rw [← @Ideal.card_inertiaSubgroup (𝓞 ℚ) _ _ (m.asIdeal.under (𝓞 ℚ)) ?_ _ (𝓞 K) _ _
      _ _ m.asIdeal _ _ _ G _ _ _ _ _]
    apply h
    · sorry
    · have key := m.asIdeal.over_under (A := 𝓞 F)
      intro h
      rw [h] at key
      exact (m.asIdeal.bot_lt_of_maximal (RingOfIntegers.not_isField K)).ne'
        (m.asIdeal.eq_bot_of_liesOver_bot (A := 𝓞 F))
    · have key := m.asIdeal.over_under (A := 𝓞 F)
      intro h
      rw [h] at key
      exact (m.asIdeal.bot_lt_of_maximal (RingOfIntegers.not_isField K)).ne'
        (m.asIdeal.eq_bot_of_liesOver_bot (A := 𝓞 F))
  -- switch over from 𝓞 ℚ to ℤ at some point
  replace h (m : MaximalSpectrum (𝓞 F)) :
      Ideal.ramificationIdx (algebraMap ℤ (𝓞 F)) (m.asIdeal.under ℤ) m.asIdeal = 1 := by
    let q : MaximalSpectrum (𝓞 K) := sorry
    have key := @Ideal.ramificationIdx_algebra_tower ℤ (𝓞 F) (𝓞 K) _ _ _ _ _ _ _ _ _
      (m.asIdeal.under ℤ) m.asIdeal q.asIdeal _ _
    sorry
  replace h (m : MaximalSpectrum (𝓞 F)) : Algebra.IsUnramifiedAt ℤ m.asIdeal := by
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain]
    · exact h m
    · exact (m.asIdeal.bot_lt_of_maximal (RingOfIntegers.not_isField F)).ne'
  replace h (m : MaximalSpectrum (𝓞 F)) : ¬ m.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by
    rw [dvd_differentIdeal_iff, not_not]
    exact h m
  replace h : differentIdeal ℤ (𝓞 F) = ⊤ := by
    simp only [Ideal.dvd_iff_le] at h
    sorry
  -- define intermediate ring of integers and compute inertia degrees
  replace h : (discr ↥F).natAbs = 1 := by
    rw [← NumberField.absNorm_differentIdeal (K := F) (𝒪 := 𝓞 F), h, Ideal.absNorm_top]
  suffices Module.finrank ℚ F ≤ 1 from
    IntermediateField.finrank_eq_one_iff.mp (le_antisymm this Module.finrank_pos)
  contrapose! h
  replace h : 2 < |NumberField.discr F| := NumberField.abs_discr_gt_two h
  contrapose! h
  simp [Int.abs_eq_natAbs, h]

theorem genthm (K : Type*) [Field K] [NumberField K]
    (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K]
    (G : Type*) [Group G] [MulSemiringAction G K]
    [MulSemiringAction G R] [IsGaloisGroup G ℚ K] :
    ⨆ m : MaximalSpectrum R, m.asIdeal.toAddSubgroup.inertia G = ⊤ := by
  sorry

end ram

end Inertia

namespace Polynomial

section Moore

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
    ∀ g ∈ m.asIdeal.toAddSubgroup.inertia G,
      MulAction.toPermHom G (f.rootSet S) g = 1 ∨
        (MulAction.toPermHom G (f.rootSet S) g).IsSwap := by
  intro g hg
  let π : S →ₐ[R] S ⧸ m.asIdeal := Ideal.Quotient.mkₐ R m.asIdeal
  have hπ (x : S) (hx : x ∈ f.rootSet S): π x ∈ f.rootSet (S ⧸ m.asIdeal) := by
    unfold π
    rw [hmon.mem_rootSet, aeval_algHom_apply, aeval_eq_zero_of_mem_rootSet hx, map_zero]
  have hπ (x : S) : π (g • x) = π x := (Ideal.Quotient.mk_eq_mk_iff_sub_mem (g • x) x).mpr (hg x)
  rw [or_iff_not_imp_left]
  intro hg'
  rw [Equiv.ext_iff, not_forall] at hg'
  obtain ⟨x, hx⟩ := hg'
  change g • x ≠ x at hx
  refine ⟨g • x, x, hx, ?_⟩
  ext z
  rw [Equiv.swap_apply_def]
  split_ifs with hz hz'
  · subst hz
    simp
    sorry
  · simp [hz']
  · simp
    sorry

theorem tada' {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    [NoZeroSMulDivisors R S] (f : R[X])
    (hf : f.Monic) (hf' : (f.map (algebraMap R S)).roots.card = f.natDegree)
    (G : Type*) [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    [MulAction.IsPretransitive G (f.rootSet S)] [FaithfulSMul G (f.rootSet S)]
    (hG : ⨆ m : MaximalSpectrum S, m.asIdeal.toAddSubgroup.inertia G = ⊤)
    (h : ∀ m : MaximalSpectrum S, f.natDegree ≤ (f.rootSet (S ⧸ m.asIdeal)).ncard + 1) :
    Function.Bijective (MulAction.toPermHom G (f.rootSet S)) := by
  classical
  have hinj : Function.Injective (MulAction.toPermHom G (f.rootSet S)) := MulAction.toPerm_injective
  let X := ⋃ m : MaximalSpectrum S,
    ((↑(m.asIdeal.toAddSubgroup.inertia G : Subgroup G) : Set G) \ {1})
  have hS1 : Subgroup.closure X = ⊤ := by
    simpa only [X, Subgroup.closure_iUnion, Subgroup.closure_eq, Subgroup.closure_diff_one]
  have hS2 : ∀ σ ∈ X, (MulAction.toPermHom G (f.rootSet S) σ).IsSwap := by
    intro σ hσ
    simp only [X, Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff] at hσ
    obtain ⟨m, hm, hσ⟩ := hσ
    apply (tada f hf G m hf' ?_ σ hm).resolve_left
    · rwa [map_eq_one_iff _ hinj]
    · grw [← h]
      rw [rootSet, aroots, Set.ncard_coe_finset]
      classical
      grw [Multiset.toFinset_card_le, Polynomial.card_roots']
      rw [hf.natDegree_map]
  exact ⟨hinj, surjective_of_isSwap_of_isPretransitive X hS2 hS1⟩

open Equiv Pointwise

open IntermediateField

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

attribute [local instance] Gal.splits_ℚ_ℂ

open NumberField

theorem tada'' (f₀ : ℤ[X]) (hf₀ : f₀.Monic) (hf' : Irreducible f₀) :
    -- condition on at most on root collision mod p :
    Function.Bijective (Gal.galActionHom (f₀.map (algebraMap ℤ ℚ)) ℂ) := by
  classical
  let f : ℚ[X] := f₀.map (algebraMap ℤ ℚ)
  have hf := hf₀.map (algebraMap ℤ ℚ)
  let K := f.SplittingField
  have : Fact (f.Splits (algebraMap ℚ K)) := ⟨SplittingField.splits f⟩
  have : NumberField K := by constructor
  have : IsGalois ℚ K := by constructor
  let R := 𝓞 K
  let G := f.Gal
  let _ : MulSemiringAction G R := IsIntegralClosure.MulSemiringAction ℤ ℚ K R
  suffices Function.Bijective (Gal.galActionHom f K) by
    rw [switchinglemma f ℂ K]
    exact (((Gal.rootsEquivRoots f f.SplittingField).symm.trans
      (Gal.rootsEquivRoots f ℂ)).permCongrHom.toEquiv.comp_bijective _).mpr this
  let φ : f₀.rootSet R → f.rootSet K := fun x ↦ ⟨algebraMap R K x, by
    rw [hf.mem_rootSet, aeval_map_algebraMap, aeval_algebraMap_apply,
      aeval_eq_zero_of_mem_rootSet x.2, map_zero]⟩
  have hφ1 : ∀ g : G, ∀ x : f₀.rootSet R, φ (g • x) = g • φ x := by
    intro g x
    ext
    sorry
  have hφ2 : Function.Bijective φ := by
    -- injective and card
    sorry
  suffices Function.Bijective (MulAction.toPermHom G (f₀.rootSet R)) by
    sorry
  -- suffices Function.Bijective (Gal.galActionHom f K) by
  --   rw [switchinglemma f ℂ K]
  --   exact (((Gal.rootsEquivRoots f f.SplittingField).symm.trans
  --     (Gal.rootsEquivRoots f ℂ)).permCongrHom.toEquiv.comp_bijective _).mpr this
  have : MulAction.IsPretransitive G (f.rootSet K) :=
    Gal.galAction_isPretransitive _ _ (hf₀.irreducible_iff_irreducible_map_fraction_map.mp hf')
  have : FaithfulSMul G (f.rootSet K) :=
    -- use galActionHom_injective
    sorry
  -- need a bijection between f₀.rootSet R and
  have : MulAction.IsPretransitive G (f₀.rootSet R) := by
    sorry
  have : FaithfulSMul G (f₀.rootSet R) := by
    sorry
  refine tada' (S := R) f₀ hf₀ ?_ G ?_ ?_
  · sorry
  · have : IsGaloisGroup G ℚ K := IsGaloisGroup.of_isGalois ℚ K
    exact genthm K R G
  · sorry

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
  · exact z_ne_zero (eq_zero_of_pow_eq_zero (by rwa [key, add_self_eq_zero] at h2))

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
  · exact hp ▸ (trinomial_monic zero_lt_one hn).isPrimitive

open Equiv Pointwise

open IntermediateField

attribute [local instance] Gal.splits_ℚ_ℂ

theorem X_pow_sub_X_sub_one_gal :
    Function.Bijective (Gal.galActionHom (X ^ n - X - 1 : ℚ[X]) ℂ) := by
  rcases le_or_gt n 1 with hn | hn
  · have : Subsingleton ((X ^ n - X - 1 : ℚ[X]).rootSet ℂ) := by
      apply Finset.card_le_one_iff_subsingleton_coe.mp
      grw [Multiset.toFinset_card_le, card_roots', natDegree_map_le, natDegree_sub_le,
        natDegree_sub_le, natDegree_X_pow, natDegree_X, natDegree_one, hn, max_self, Nat.max_zero]
    have : Unique ((X ^ n - X - 1 : ℚ[X]).Gal) := by
      refine Gal.uniqueGalOfSplits _ (splits_of_natDegree_le_one _ (by compute_degree!))
    apply Unique.bijective
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  have h := tada'' (X ^ n - X - 1) (hp ▸ trinomial_monic zero_lt_one hn)
    (X_pow_sub_X_sub_one_irreducible hn.ne')
  rwa [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one,
    Polynomial.map_X] at h

end Polynomial
