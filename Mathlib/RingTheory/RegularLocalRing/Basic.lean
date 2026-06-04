/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!

# Regular Local Ring is Domain

In this file, we prove that regular local ring is domain

# Main definition and results

* `isDomain_of_isRegularLocalRing` : a regular local ring is domain

* `isRegular_of_span_eq_maximalIdeal` : for a regular local ring `R`, if a list of length equal to
  its dimension generates `maximalIdeal R`, it form a regular sequence.

-/

public section

open IsLocalRing IsRegularLocalRing

variable (R : Type*) [CommRing R]

variable {R} in
lemma IsLocalRing.spanFinrank_maximalIdeal_quotient [IsLocalRing R] [IsNoetherianRing R]
    (S : Finset R) (sub : (S : Set R) ⊆ maximalIdeal R)
    (li : LinearIndependent (ResidueField R) ((maximalIdeal R).toCotangent ∘ (Set.inclusion sub))) :
    letI : Nontrivial (R ⧸ Ideal.span (S : Set R)) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (Ideal.span_le.mpr sub))
    letI : IsLocalRing (R ⧸ Ideal.span (S : Set R)) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    (Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span (S : Set R)))) + S.card =
      (maximalIdeal R).spanFinrank := by
  have : Nontrivial (R ⧸ Ideal.span (S : Set R)) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (Ideal.span_le.mpr sub))
  have lochom : IsLocalHom (Ideal.Quotient.mk (Ideal.span (S : Set R))) :=
    IsLocalHom.of_surjective _ (Ideal.Quotient.mk_surjective)
  have : IsLocalRing (R ⧸ Ideal.span (S : Set R)) :=
    IsLocalRing.of_surjective _ Ideal.Quotient.mk_surjective
  have : _ +  Module.finrank (ResidueField R) ((Submodule.comap (maximalIdeal R).subtype
    (RingHom.ker (Ideal.Quotient.mk (Ideal.span S)))).map (toCotangentSpace R)) = _ :=
    IsLocalRing.spanFinrank_maximalIdeal_add_finrank_eq_of_surjective
    (Ideal.Quotient.mk_surjective (I := Ideal.span (S : Set R)))
  convert this
  have : S = Set.range (Subtype.val ∘ Set.inclusion sub) := by
    rw [Set.val_comp_inclusion, Subtype.range_val]
  have eqmap : Ideal.span S =
    (Submodule.span R (Set.range (Set.inclusion sub))).map (maximalIdeal R).subtype := by
    rw [Submodule.map_span, Ideal.submodule_span_eq, ← Set.range_comp]
    congr
  have : Submodule.comap (maximalIdeal R).subtype (Ideal.span S) =
    Submodule.span R (Set.range (Set.inclusion sub)) := by
    rw [eqmap, Submodule.comap_map_eq_of_injective (maximalIdeal R).subtype_injective]
  rw [Ideal.mk_ker, this, Submodule.map_span, ← Set.range_comp]
  simp only [SetLike.coe_sort_coe, toCotangentSpace, LinearMap.coe_mk, LinearMap.coe_toAddHom]
  exact (Fintype.card_coe S).symm.trans (finrank_span_eq_card li).symm

lemma quotient_isRegularLocalRing_tfae [IsRegularLocalRing R] (S : Finset R)
    (sub : (S : Set R) ⊆ maximalIdeal R) :
    [∃ (T : Finset R), S ⊆ T ∧ T.card = ringKrullDim R ∧ Ideal.span T = maximalIdeal R,
     LinearIndependent (ResidueField R) ((⇑(maximalIdeal R).toCotangent).comp (Set.inclusion sub)),
     IsRegularLocalRing (R ⧸ Ideal.span (S : Set R)) ∧
     (ringKrullDim (R ⧸ Ideal.span (S : Set R)) + S.card = ringKrullDim R)].TFAE := by
  have : Nontrivial (R ⧸ Ideal.span (S : Set R)) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (Ideal.span_le.mpr sub))
  have lochom : IsLocalHom (Ideal.Quotient.mk (Ideal.span (S : Set R))) :=
    IsLocalHom.of_surjective _ (Ideal.Quotient.mk_surjective)
  tfae_have 1 → 2 := by
    rintro ⟨T, h, card, span⟩
    have Tsub : (T : Set R) ⊆ maximalIdeal R := by simp [← span]
    have : LinearIndependent (ResidueField R)
      ((⇑(maximalIdeal R).toCotangent).comp (Set.inclusion Tsub)) := by
      apply linearIndependent_of_top_le_span_of_card_eq_finrank
      · suffices Submodule.span R (((↑) : maximalIdeal R → R) ⁻¹' T) = ⊤ by
          simpa [Set.range_comp, CotangentSpace.span_image_eq_top_iff, Set.range_inclusion Tsub]
        apply Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype
        simp [Submodule.map_span, Set.image_preimage_eq_inter_range, -mem_maximalIdeal,
          Set.inter_eq_left.mpr Tsub, span]
      · rw [← Nat.cast_inj (R := WithBot ℕ∞), (iff_finrank_cotangentSpace R).mp ‹_›, ← card]
        simp
    simpa [← Function.comp_assoc, ← Set.inclusion_comp_inclusion h Tsub] using
      this.comp _ (Set.inclusion_injective h)
  tfae_have 2 → 3 := by
    intro li
    let _ : IsLocalRing (R ⧸ Ideal.span (S : Set R)) :=
      IsLocalRing.of_surjective _ Ideal.Quotient.mk_surjective
    rw [isRegularLocalRing_iff]
    have le := ringKrullDim_le_ringKrullDim_quotient_add_card S
      (by simpa [IsLocalRing.ringJacobson_eq_maximalIdeal] using sub)
    have ge : (Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span (S : Set R)))) + S.card ≤
      ringKrullDim R := by
      simp [← Nat.cast_add, ← (isRegularLocalRing_iff R).mp ‹_›,
        spanFinrank_maximalIdeal_quotient S sub li]
    have : ringKrullDim (R ⧸ Ideal.span (S : Set R)) + S.card ≤
      (Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span (S : Set R)))) + S.card :=
      add_le_add_left (ringKrullDim_le_spanFinrank_maximalIdeal _) _
    exact ⟨ENat.WithBot.add_natCast_cancel.mp (le_antisymm (ge.trans le) this),
      le_antisymm (this.trans ge) le⟩
  tfae_have 3 → 1 := by
    classical
    rintro ⟨reg, dim⟩
    simp only [← (isRegularLocalRing_iff _).mp reg, ← Nat.cast_add, ←
      (isRegularLocalRing_iff R).mp ‹_›, Nat.cast_inj] at dim
    have fin : (maximalIdeal (R ⧸ Ideal.span (S : Set R))).generators.Finite :=
      (IsNoetherian.noetherian _).finite_generators
    let U := Quotient.out '' (maximalIdeal (R ⧸ Ideal.span (S : Set R))).generators
    let : Fintype U := (Set.Finite.image _ fin).fintype
    use S ∪ U.toFinset
    have span : Ideal.span (S ∪ U) = maximalIdeal R := by
      rw [Ideal.span_union, ← Ideal.mk_ker (I := Ideal.span (S : Set R)), sup_comm,
        ← Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.map_span]
      have : Ideal.span (⇑(Ideal.Quotient.mk (Ideal.span ↑S)) '' U) =
        Submodule.span _ (maximalIdeal (R ⧸ Ideal.span (S : Set R))).generators := by
        simp [U, ← Set.image_comp]
      rw [this, Submodule.span_generators, IsLocalRing.maximalIdeal_comap]
    simp only [Finset.subset_union_left, true_and, ← (isRegularLocalRing_iff R).mp ‹_›,
      Finset.coe_union, Set.coe_toFinset]
    refine ⟨le_antisymm ?_ ?_, span⟩
    · apply Nat.cast_le.mpr (le_trans (Finset.card_union_le _ _) _)
      simp only [Set.toFinset_card, ← dim, add_comm, add_le_add_iff_left,
        Fintype.card_eq_nat_card, Nat.card_coe_set_eq]
      exact (Set.ncard_image_le fin).trans (le_of_eq (IsNoetherian.noetherian _).generators_ncard)
    · simp only [← span, ← Set.ncard_coe_finset, Finset.coe_union, Set.coe_toFinset, Nat.cast_le]
      exact Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite (S ∪ U))
  tfae_finish

lemma quotient_span_singleton [IsRegularLocalRing R] {x : R} (mem : x ∈ maximalIdeal R)
    (nmem : x ∉ (maximalIdeal R) ^ 2) : IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
    (ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R) := by
  rw [← Nat.cast_one, ← Finset.card_singleton x, ← Finset.coe_singleton x]
  apply ((quotient_isRegularLocalRing_tfae R {x} (by simpa)).out 1 2).mp
  simpa [← LinearMap.mem_ker, Ideal.mem_toCotangent_ker] using nmem

lemma FiniteRingKrullDim.ringKrullDim_eq_nat [FiniteRingKrullDim R] :
    ∃ n : ℕ, ringKrullDim R = n := by
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := R))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (WithBot.coe_inj.not.mp (ne_of_eq_of_ne hm ringKrullDim_ne_top))
  exact ⟨n, ((WithBot.coe_inj.mpr hn).trans hm).symm⟩

variable {R} in
theorem Ideal.span_singleton_mul_eq_self_of_isPrime {p : Ideal R} [p.IsPrime]
    (x : R) (hx : x ∉ p) (hp : p ≤ Ideal.span {x}) : Ideal.span {x} * p = p := by
  refine Ideal.mul_le_left.antisymm ?_
  intro y hyp
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp (hp hyp)
  exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _)
    ((Ideal.IsPrime.mul_mem_left_iff hx).mp hyp)

open Pointwise in
theorem isDomain_of_isRegularLocalRing [IsRegularLocalRing R] : IsDomain R := by
  obtain ⟨n, hn⟩ := FiniteRingKrullDim.ringKrullDim_eq_nat R
  induction n generalizing R with
  | zero =>
    suffices IsField R from this.isDomain
    simpa [← (isRegularLocalRing_iff R).mp ‹_›, Submodule.spanFinrank_eq_zero_iff_eq_bot,
      IsNoetherian.noetherian, ← isField_iff_maximalIdeal_eq] using hn
  | succ n ih =>
    obtain ⟨x, xmem, xnmem⟩ :
        ∃ x ∈ maximalIdeal R, x ∉ ⋃ I ∈ (insert ((maximalIdeal R) ^ 2) (minimalPrimes R)), I := by
      by_contra! h
      have : ringKrullDim R ≠ 0 := hn.trans_ne (Nat.cast_inj.not.mpr (Nat.zero_ne_add_one n).symm)
      have lt := (maximalIdeal_sq_lt_maximalIdeal R).mpr (mt ringKrullDim_eq_zero_of_isField this)
      have fin := (minimalPrimes.finite_of_isNoetherianRing R).insert ((maximalIdeal R) ^ 2)
      absurd (Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite fin _ _
        (fun I hI ne _ ↦ (Set.mem_of_mem_insert_of_ne hI ne).1.1) lt.ne_top lt.ne_top).mp h
      simp only [Set.mem_insert_iff, lt.ne.symm, ← Ideal.height_eq_zero_iff, false_or]
      rwa [← WithBot.coe_inj, maximalIdeal_height_eq_ringKrullDim]
    replace xnmem : x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by simpa using xnmem
    obtain ⟨reg, dim⟩ := quotient_span_singleton R xmem xnmem.1
    simp only [hn, Nat.cast_add, Nat.cast_one] at dim
    have ih' := ih (R ⧸ Ideal.span {x}) (ENat.WithBot.add_one_cancel.mp dim)
    have : (Ideal.span {x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp ih'
    obtain ⟨p, min, hp⟩ := Ideal.exists_minimalPrimes_le (bot_le (a := Ideal.span {x}))
    suffices p = ⊥ from @IsDomain.of_bot_isPrime R _ (this ▸ min.1.1)
    exact Submodule.eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator (IsNoetherian.noetherian _)
      (@Ideal.span_singleton_mul_eq_self_of_isPrime _ _ _ min.1.1 _ (xnmem.2 _ min) hp).symm
      (((Ideal.span_singleton_le_iff_mem _).mpr xmem).trans (maximalIdeal_le_jacobson _))

instance [IsRegularLocalRing R] : IsDomain R := isDomain_of_isRegularLocalRing R

/-- Regular local ring of dimension one is discrete valuation ring.
For iff version, should exist after making `IsDiscreteValuationRing` extend `IsDomain`. -/
lemma IsDiscreteValuationRing.of_isRegularLocalRing_of_ringKrullDim_eq_one [IsRegularLocalRing R]
    (dim : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  have nisf : ¬ IsField R := (mt ringKrullDim_eq_zero_of_isField (by simp [dim]))
  apply ((IsDiscreteValuationRing.TFAE R nisf).out 0 4).mpr ((Submodule.spanFinrank_eq_one_iff _).mp
    (Nat.cast_inj.mp (((isRegularLocalRing_iff R).mp ‹_›).trans dim))).1

set_option backward.isDefEq.respectTransparency false in
open RingTheory.Sequence in
theorem isRegular_of_span_eq_maximalIdeal [IsRegularLocalRing R] (rs : List R)
    (span : Ideal.ofList rs = maximalIdeal R) (len : rs.length = ringKrullDim R) :
    IsRegular R rs := by
  refine ⟨⟨fun i hi ↦ ?_⟩, by simpa [span] using Ideal.IsPrime.ne_top'.symm⟩
  rw [smul_eq_mul, Ideal.mul_top]
  classical
  have mem : (rs.toFinset : Set R) ⊆ maximalIdeal R := by simp [← span, Ideal.ofList]
  have sub : (List.take i rs).toFinset ⊆ rs.toFinset :=
    fun x ↦ by simpa using fun a ↦ List.mem_of_mem_take a
  have card : rs.toFinset.card = ringKrullDim R := by
    apply le_antisymm (le_of_le_of_eq (Nat.cast_le.mpr rs.toFinset_card_le) len)
    simp only [← (isRegularLocalRing_iff R).mp ‹_›, Nat.cast_le, ← span, Ideal.ofList,
      ← List.coe_toFinset rs, ← Set.ncard_coe_finset rs.toFinset]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite rs.toFinset.finite_toSet)
  have : IsDomain (R ⧸ Ideal.ofList (List.take i rs)) := by
    refine @isDomain_of_isRegularLocalRing _ _ ?_
    rw [Ideal.ofList, ← (List.take i rs).coe_toFinset]
    refine And.left (((quotient_isRegularLocalRing_tfae R (List.take i rs).toFinset
      ((Finset.coe_subset.mpr sub).trans mem)).out 0 2).mp ?_)
    use rs.toFinset
    simpa [sub, card] using span
  have : (Ideal.Quotient.mk (Ideal.ofList (List.take i rs))) rs[i] ≠ 0 := by
    simp only [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    by_contra mem
    simp only [← (isRegularLocalRing_iff R).mp ‹_›, Nat.cast_inj] at len
    let rs' := (List.take i rs) ++ (List.drop (i + 1) rs)
    have span' : Ideal.ofList rs' = maximalIdeal R := by
      simp only [← span, rs']
      apply le_antisymm
      · apply Ideal.span_mono (fun x ↦ ?_)
        simpa [or_imp] using ⟨fun a ↦ List.mem_of_mem_take a, fun a ↦ List.mem_of_mem_drop a⟩
      · apply Ideal.span_le.mpr
        intro x hx
        have : rs = List.take i rs ++ (rs[i] :: List.drop (i + 1) rs) := by
          rw [List.cons_getElem_drop_succ, List.take_append_drop]
        rw [Set.mem_setOf, this, List.mem_append, List.mem_cons] at hx
        simp only [Ideal.ofList_append, SetLike.mem_coe]
        rcases hx with l|eq|r
        · exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_setOf.mpr l))
        · exact Ideal.mem_sup_left (eq ▸ mem)
        · exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_setOf.mpr r))
    have : Submodule.spanFinrank (Ideal.ofList rs') ≤ rs'.length := by
      apply (Submodule.spanFinrank_span_le_ncard_of_finite rs'.finite_toSet).trans
      apply le_of_eq_of_le _ (List.toFinset_card_le rs')
      simp [← (Set.ncard_coe_finset rs'.toFinset)]
    simp only [span', ← len, List.length_append, List.length_take, List.length_drop, rs'] at this
    omega
  exact (IsRegular.of_ne_zero this).isSMulRegular
