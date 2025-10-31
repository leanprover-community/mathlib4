/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Analysis.Complex.Polynomial.UnitTrinomial
import Mathlib.FieldTheory.Finite.GaloisField
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

-- PR #29688
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

section inertia

theorem AddSubgroup.subgroupOf_inertia {M : Type*} [AddGroup M] (I : AddSubgroup M)
    (G : Type*) [Group G] [MulAction G M] (H : Subgroup G) :
    (I.inertia G).subgroupOf H = I.inertia H :=
  rfl

end inertia

-- PR #30666
section ram

variable {K 𝒪 : Type*} [Field K] [NumberField K] [CommRing 𝒪] [Algebra 𝒪 K]
variable [IsIntegralClosure 𝒪 ℤ K]

lemma NumberField.exists_not_isUramifiedAt_int (H : 1 < Module.finrank ℚ K) :
    ∃ (P : Ideal 𝒪) (_ : P.IsMaximal), P ≠ ⊥ ∧ ¬ Algebra.IsUnramifiedAt ℤ P :=
  sorry

end ram

section ram

open IsGaloisGroup

open NumberField

instance (R K : Type*) [CommRing R] [CommRing K] [Algebra R K]
    (G : Type*) [Group G] [MulSemiringAction G K] [SMulCommClass G R K] :
    MulSemiringAction G (integralClosure R K) where
  smul := fun g x ↦ ⟨g • (x : K), x.2.map (MulSemiringAction.toAlgHom R K g)⟩
  one_smul x := by ext; exact one_smul G (x : K)
  mul_smul g h x := by ext; exact mul_smul g h (x : K)
  smul_zero g := by ext; exact smul_zero g
  smul_add g x y := by ext; exact smul_add g (x : K) (y : K)
  smul_one g := by ext; exact smul_one g
  smul_mul g x y := by ext; exact smul_mul' g (x : K) (y : K)

instance {G K : Type*} [Group G] [Field K] [MulSemiringAction G K] :
    MulSemiringAction G (𝓞 K) :=
  inferInstanceAs (MulSemiringAction G (integralClosure _ _))

instance (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (G : Type*) [Group G] [MulSemiringAction G L] [IsGaloisGroup G K L] :
    IsGaloisGroup G (𝓞 K) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing G (𝓞 K) (𝓞 L) K L (fun _ _ ↦ rfl)

instance (L : Type*) [Field L] [NumberField L]
    (G : Type*) [Group G] [MulSemiringAction G L] [IsGaloisGroup G ℚ L] :
    IsGaloisGroup G ℤ (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing G ℤ (𝓞 L) ℚ L (fun _ _ ↦ rfl)

instance tada1 {K : Type*} [Field K] [NumberField K] (m : Ideal (𝓞 K)) [m.IsMaximal] :
    Finite (𝓞 K ⧸ m) :=
  m.finiteQuotientOfFreeOfNeBot (m.bot_lt_of_maximal (RingOfIntegers.not_isField K)).ne'

theorem Ideal.IsMaximal.ne_bot_of_isIntegral_int {R : Type*} [CommRing R]
    [CharZero R] [Algebra.IsIntegral ℤ R] (I : Ideal R) [I.IsMaximal] : I ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField ‹_› fun h ↦ Int.not_isField
    (isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective ℤ R) h)

theorem genthm₀ (K : Type*) [Field K] [NumberField K]
    (G : Type*) [Group G] [MulSemiringAction G K]
    [IsGaloisGroup G ℚ K] :
    ⨆ m : MaximalSpectrum (𝓞 K), m.asIdeal.toAddSubgroup.inertia G = ⊤ := by
  have : Finite G := IsGaloisGroup.finite G ℚ K
  set H : Subgroup G := ⨆ m : MaximalSpectrum (𝓞 K), m.asIdeal.toAddSubgroup.inertia G
  set F : IntermediateField ℚ K := FixedPoints.intermediateField H
  suffices Module.finrank ℚ F ≤ 1 by
    rw [eq_top_iff, ← fixingSubgroup_fixedPoints G ℚ K H, ← le_fixedPoints_iff_le_fixingSubgroup,
      fixedPoints_top, le_bot_iff, ← IntermediateField.finrank_eq_one_iff]
    exact le_antisymm this Module.finrank_pos
  suffices h : ∀ (m : Ideal (𝓞 F)) (hm : m.IsMaximal), Algebra.IsUnramifiedAt ℤ m by
    contrapose! h
    obtain ⟨p, h1, h2, h3⟩ := NumberField.exists_not_isUramifiedAt_int (𝒪 := 𝓞 F) h
    exact ⟨p, h1, h3⟩
  intro m _
  have hm2 := Ideal.IsMaximal.ne_bot_of_isIntegral_int m
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hm2]
  obtain ⟨m, hm, ⟨rfl⟩⟩ := Ideal.exists_ideal_liesOver_maximal_of_isIntegral m (𝓞 K)
  rw [Ideal.under_under]
  have hm1 := Ideal.IsMaximal.ne_bot_of_isIntegral_int (m.under ℤ)
  have h : m.toAddSubgroup.inertia G ≤ H :=
    le_iSup (fun m : MaximalSpectrum (𝓞 K) ↦ m.asIdeal.toAddSubgroup.inertia G) ⟨m, hm⟩
  replace h : Nat.card (m.toAddSubgroup.inertia H) = Nat.card (m.toAddSubgroup.inertia G) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le h, Subgroup.card_subtype,
      AddSubgroup.subgroupOf_inertia]
  let := Ideal.Quotient.field m
  let := Ideal.Quotient.field (m.under (𝓞 F))
  let := Ideal.Quotient.field (m.under ℤ)
  -- todo: clean up once #30934 is merged
  have : IsGalois ℚ K := IsGaloisGroup.isGalois G ℚ K
  rw [Ideal.card_inertia_eq_ramificationIdxIn F K (m.under (𝓞 F)) hm2 m,
    Ideal.card_inertia_eq_ramificationIdxIn ℚ K (m.under ℤ) hm1 m,
    Ideal.ramificationIdxIn_eq_ramificationIdx (m.under (𝓞 F)) m F K,
    Ideal.ramificationIdxIn_eq_ramificationIdx (m.under ℤ) m ℚ K] at h
  have key := Ideal.ramificationIdx_algebra_tower (Ideal.map_ne_bot_of_ne_bot hm2)
    (Ideal.map_ne_bot_of_ne_bot hm1) Ideal.map_comap_le
  rwa [h, right_eq_mul₀ (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver m hm1)] at key

-- generalize from `𝓞 K` to `IsIntegralClosure`?
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

theorem rootSet.coe_smul
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    [NoZeroSMulDivisors R S] {f : R[X]}
    {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (g : G) (x : f.rootSet S) : (g • x : f.rootSet S) = g • (x : S) := rfl

theorem Monic.mem_rootSet {T S : Type*} [CommRing T] [CommRing S] [IsDomain S]
    [Algebra T S] {p : T[X]} (hp : p.Monic) {a : S} : a ∈ p.rootSet S ↔ (aeval a) p = 0 := by
  simp [Polynomial.mem_rootSet', (hp.map (algebraMap T S)).ne_zero]

theorem fiddly''' {α β : Type*} [Finite α] {f : α → β} (hf : Function.Surjective f) :
    Nat.card α ≤ Nat.card β + 1 ↔ ∀ a b c d,
      f a = f b → f c = f d → a ≠ b → c ≠ d → {a, b} = ({c, d} : Set α) := by
  rcases isEmpty_or_nonempty α
  · simp
  let g := Function.surjInv hf
  rw [← Set.ncard_range_of_injective (Function.injective_surjInv hf),
    ← Set.ncard_add_ncard_compl (Set.range g), add_le_add_iff_left]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [Set.ncard_le_one_iff_subset_singleton] at h
    obtain ⟨x, hx⟩ := h
    suffices ∀ a b : α, f a = f b → a ≠ b → a = x ∨ a = g (f x) by grind
    intro a b hfab hab
    by_cases ha : a ∈ Set.range g
    · obtain ⟨a, rfl⟩ := ha
      rw [Function.surjInv_eq hf] at hfab
      subst hfab
      by_cases hb : b ∈ Set.range g
      · obtain ⟨b, rfl⟩ := hb
        rw [Function.surjInv_eq hf] at hab
        contradiction
      · exact Or.inr (congrArg (fun y ↦ g (f y)) (hx hb))
    · exact Or.inl (hx ha)
  · rw [Set.ncard_le_one]
    simp only [Set.mem_compl_iff, Set.mem_range, not_exists, ← ne_eq]
    intro a ha b hb
    simpa [(ha (f b)).symm] using congrArg (a ∈ ·) (h a (g (f a)) b (g (f b))
      (Function.surjInv_eq hf (f a)).symm (Function.surjInv_eq hf (f b)).symm
      (ha (f a)).symm (hb (f b)).symm)

theorem fiddly' {α β : Type*} (s : Set α) [Finite s] (f : α → β) :
    s.ncard ≤ (f '' s).ncard + 1 ↔ ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      f a = f b → f c = f d → a ≠ b → c ≠ d → {a, b} = ({c, d} : Set α) := by
  simpa [Subtype.ext_iff, ← Set.image_val_inj, Set.image_insert_eq] using
    fiddly''' (Set.surjective_mapsTo_image_restrict f s)

theorem tada -- R = ℤ, S = 𝓞 K
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    [NoZeroSMulDivisors R S]
    (f : R[X]) (hmon : f.Monic) [DecidableEq (f.rootSet S)]
    (G : Type*) [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (m : MaximalSpectrum S)
     -- all roots already present (so no new roots in `S ⧸ m`)
    (hf : (f.map (algebraMap R S)).Factors)
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
  have h0 : f.rootSet (S ⧸ m.asIdeal) = π '' f.rootSet S := by
    classical
    have key := Monic.roots_map_of_card_eq_natDegree (hmon.map (algebraMap R S))
      (π : S →+* S ⧸ m.asIdeal) hf.natDegree_eq_card_roots.symm
    rw [map_map, π.comp_algebraMap] at key
    simp [rootSet, aroots, ← key, Multiset.toFinset_map]
  rw [h0] at h
  split_ifs with hz hz'
  · subst hz
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, SetLike.coe_eq_coe]
    have key := (fiddly' (f.rootSet S) π).mp h
      (g • g • x) (g • g • x).2 (g • x) (g • x).2 (g • x) (g • x).2 x x.2
    simp [hπ] at key
    simp [← Polynomial.rootSet.coe_smul] at key
    simp [hx] at key
    replace key := congrArg (fun s ↦ (x : S) ∈ s) key
    simp [hx.symm] at key
    exact key.symm
  · simp [hz']
  · simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, SetLike.coe_eq_coe]
    have key := (fiddly' (f.rootSet S) π).mp h (g • z) (g • z).2 z z.2 (g • x) (g • x).2 x x.2
    simp [hπ] at key
    simp [← Polynomial.rootSet.coe_smul] at key
    simp [hx] at key
    rw [not_imp_comm] at key
    apply key
    contrapose! key
    replace key := congrArg (fun s ↦ (z : S) ∈ s) key
    simp [hz, hz'] at key

theorem tada' {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    [NoZeroSMulDivisors R S] (f : R[X])
    (hf : f.Monic) (hf' : (f.map (algebraMap R S)).Factors)
    (G : Type*) [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    [MulAction.IsPretransitive G (f.rootSet S)]
    (hG : ⨆ m : MaximalSpectrum S, m.asIdeal.toAddSubgroup.inertia G = ⊤)
    (h : ∀ m : MaximalSpectrum S, (f.rootSet S).ncard ≤ (f.rootSet (S ⧸ m.asIdeal)).ncard + 1) :
    Function.Surjective (MulAction.toPermHom G (f.rootSet S)) := by
  classical
  let X : Set G := ⋃ m : MaximalSpectrum S, m.asIdeal.toAddSubgroup.inertia G
  have hS1 : Subgroup.closure X = ⊤ := by
    simpa only [X, Subgroup.closure_iUnion, Subgroup.closure_eq, Subgroup.closure_diff_one]
  have hS2 : ∀ σ ∈ X, MulAction.toPermHom G (f.rootSet S) σ = 1 ∨
      (MulAction.toPermHom G (f.rootSet S) σ).IsSwap := by
    intro σ hσ
    simp only [X, Set.mem_iUnion] at hσ
    obtain ⟨m, hm⟩ := hσ
    have := tada f hf G m hf' (h m) σ hm
    exact this
  exact surjective_of_isSwap_of_isPretransitive' X hS2 hS1

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

attribute [-instance] Gal.smul Gal.galAction -- todo: redefine in more general semiring context

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
  suffices Function.Surjective (Gal.galActionHom f K) by
    use Polynomial.Gal.galActionHom_injective f ℂ
    rw [switchinglemma f ℂ K]
    exact (((Gal.rootsEquivRoots f f.SplittingField).symm.trans
      (Gal.rootsEquivRoots f ℂ)).permCongrHom.toEquiv.comp_surjective _).mpr this
  have hφ : Set.MapsTo (algebraMap R K) (f₀.rootSet R) (f.rootSet K) := by
    intro x hx
    rw [hf.mem_rootSet, aeval_map_algebraMap, aeval_algebraMap_apply,
      aeval_eq_zero_of_mem_rootSet hx, map_zero]
  let φ : f₀.rootSet R → f.rootSet K := hφ.restrict
  have hφ1 : ∀ g : G, ∀ x : f₀.rootSet R, φ (g • x) = g • φ x := by
    intro g x
    ext
    exact (rootSet.coe_smul g (φ x)).symm
  have hφ2 : Function.Bijective φ := by
    rw [Function.Bijective, hφ.restrict_inj, hφ.restrict_surjective_iff]
    refine ⟨RingOfIntegers.coe_injective.injOn, ?_⟩
    -- surjective
    sorry
  suffices Function.Surjective (MulAction.toPermHom G (f₀.rootSet R)) by
    sorry
  -- suffices Function.Bijective (Gal.galActionHom f K) by
  --   rw [switchinglemma f ℂ K]
  --   exact (((Gal.rootsEquivRoots f f.SplittingField).symm.trans
  --     (Gal.rootsEquivRoots f ℂ)).permCongrHom.toEquiv.comp_bijective _).mpr this
  have : MulAction.IsPretransitive G (f.rootSet K) := by
    convert Gal.galAction_isPretransitive f K
      (hf₀.irreducible_iff_irreducible_map_fraction_map.mp hf')
    ext
    -- diamond...
    sorry
  -- need a bijection between f₀.rootSet R and
  have : MulAction.IsPretransitive G (f₀.rootSet R) := by
    sorry
  have : FaithfulSMul G (f₀.rootSet R) := by
    sorry
  refine tada' (S := R) f₀ hf₀ ?_ G ?_ ?_
  · sorry
  · have : IsGaloisGroup G ℚ K := IsGaloisGroup.of_isGalois ℚ K
    exact genthm₀ K G
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
