/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.KrullDimension.Field
/-!
# Define Regular Local Ring
-/

open IsLocalRing

variable (R : Type*) [CommRing R]

class IsRegularLocalRing : Prop extends IsLocalRing R, IsNoetherianRing R where
  reg : (Submodule.spanFinrank (maximalIdeal R)) = ringKrullDim R

lemma isRegularLocalRing_iff [IsLocalRing R] [IsNoetherianRing R] :
    IsRegularLocalRing R ↔ (Submodule.spanFinrank (maximalIdeal R)) = ringKrullDim R :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma ringKrullDim_le_spanFinrank_maximalIdeal [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R ≤ (Submodule.spanFinrank (maximalIdeal R)) :=
  le_of_eq_of_le IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
    (WithBot.coe_le_coe.mpr (Ideal.height_le_spanFinrank (maximalIdeal R) Ideal.IsPrime.ne_top'))

lemma isRegularLocalRing_of_exist_span [IsLocalRing R] [IsNoetherianRing R] (S : Finset R)
    (span : Ideal.span S = maximalIdeal R) (card : S.card ≤ ringKrullDim R) :
    IsRegularLocalRing R := by
  apply (isRegularLocalRing_iff _).mpr (le_antisymm _ (ringKrullDim_le_spanFinrank_maximalIdeal R))
  apply le_trans _ card
  rw [← span, ← Ideal.submodule_span_eq, ← Set.ncard_coe_finset S, Nat.cast_le]
  exact Submodule.spanFinrank_span_le_ncard_of_finite S.finite_toSet

variable {R} in
lemma IsLocalRing.comap_maximalIdeal [IsLocalRing R] {R' : Type*} [CommRing R'] [IsLocalRing R']
    (e : R ≃+* R') : maximalIdeal R = Ideal.comap e (maximalIdeal R') := by
  ext
  simp

variable {R} in
lemma IsLocalRing.map_maximalIdeal [IsLocalRing R] {R' : Type*} [CommRing R'] [IsLocalRing R']
    (e : R ≃+* R') : Ideal.map e (maximalIdeal R) = maximalIdeal R' := by
  rw [← Ideal.map_comap_of_surjective _ e.surjective (maximalIdeal R'),
    IsLocalRing.comap_maximalIdeal e]

variable {R} in
lemma isRegularLocalRing_of_ringEquiv [IsRegularLocalRing R] {R' : Type*} [CommRing R']
    (e : R ≃+* R') : IsRegularLocalRing R' := by
  let _ := e.isLocalRing
  let _ := isNoetherianRing_of_ringEquiv R e
  have fg : (maximalIdeal R).FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance _
  let _ : Fintype (Submodule.generators (maximalIdeal R)) :=
    (Submodule.FG.finite_generators fg).fintype
  apply isRegularLocalRing_of_exist_span R' ((maximalIdeal R).generators.toFinset.map e.toEmbedding)
  · simp only [RingEquiv.toEquiv_eq_coe, Finset.coe_map, Equiv.coe_toEmbedding, EquivLike.coe_coe,
      Set.coe_toFinset, ← Ideal.map_span]
    rw [← Ideal.submodule_span_eq, Submodule.span_generators (maximalIdeal R)]
    exact IsLocalRing.map_maximalIdeal e
  · simpa [← ringKrullDim_eq_of_ringEquiv e, ← IsRegularLocalRing.reg,
      ← Submodule.FG.generators_ncard fg] using le_of_eq (Set.ncard_eq_toFinset_card' _).symm

section

lemma span_eq_top_iff [IsLocalRing R] (S : Set (maximalIdeal R)) :
    Submodule.span R S = ⊤ ↔ Submodule.span R ((Submodule.subtype (maximalIdeal R)) '' S) =
    maximalIdeal R := by
  rw [← Submodule.map_span]
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  rw [← Submodule.comap_map_eq_of_injective (maximalIdeal R).injective_subtype
    (Submodule.span R S), h, Submodule.comap_subtype_self]

open Set in
lemma spanFinrank_maximalIdeal [IsLocalRing R] [IsNoetherianRing R] :
    (Submodule.spanFinrank (maximalIdeal R)) =
    Module.finrank (ResidueField R) (CotangentSpace R) := by
  let fg : Module.Finite (ResidueField R) (CotangentSpace R) := inferInstance
  let fg' : (maximalIdeal R).FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance _
  have : Submodule.spanFinrank (⊤ : Submodule (ResidueField R) (CotangentSpace R)) =
    Module.rank (ResidueField R) (CotangentSpace R) := by
    rw [← Submodule.fg_iff_spanRank_eq_spanFinrank.mpr fg.1, Submodule.rank_eq_spanRank_of_free]
  simp only [← Module.finrank_eq_rank, Nat.cast_inj] at this
  rw [← this]
  apply le_antisymm
  · have span : Submodule.span R
      ((⊤ : Submodule (ResidueField R) (CotangentSpace R)).generators.image Quotient.out) = ⊤ := by
      apply IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp
      convert Submodule.span_generators (⊤ : Submodule (ResidueField R) (CotangentSpace R))
      have : ⇑(maximalIdeal R).toCotangent ∘ Quotient.out = id := by
        ext
        exact Submodule.Quotient.mk_out _
      rw [← Set.image_comp, this, image_id]
    rw [span_eq_top_iff, ← Set.image_comp] at span
    rw [← Submodule.FG.generators_ncard fg.1, ← congrArg Submodule.spanFinrank span]
    apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite
      (Finite.image _ fg.1.finite_generators)) (Set.ncard_image_le fg.1.finite_generators)
  · let G := ({x | ↑x ∈ (maximalIdeal R).generators} : Set (maximalIdeal R))
    have : Submodule.span R G = ⊤ := by
      simp only [span_eq_top_iff, Submodule.subtype_apply, Ideal.submodule_span_eq, G]
      convert (maximalIdeal R).span_generators
      ext
      simpa using fun a ↦ Submodule.FG.generators_mem (maximalIdeal R) a
    have fin : G.Finite := Set.Finite.of_injOn (by simp [MapsTo, G]) injOn_subtype_val
        (Submodule.FG.finite_generators fg')
    rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff.mpr this,
      ← Submodule.FG.generators_ncard fg']
    apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Finite.image _ fin))
    exact le_trans (Set.ncard_image_le fin) (Set.ncard_le_ncard_of_injOn Subtype.val (by simp [G])
      injOn_subtype_val (Submodule.FG.finite_generators fg'))

variable {R} in
lemma IsLocalRing.ResidueField.map_injective [IsLocalRing R] {S : Type*} [CommRing S]
    [IsLocalRing S] (f : R →+* S) [IsLocalHom f] :
    Function.Injective (ResidueField.map f) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  simpa only [map_eq_zero] using hx

variable {R} in
lemma IsLocalRing.ResidueField.map_bijective_of_surjective [IsLocalRing R] {S : Type*} [CommRing S]
    [IsLocalRing S] (f : R →+* S) (surj : Function.Surjective f) [IsLocalHom f] :
    Function.Bijective (ResidueField.map f) := by
  refine ⟨ResidueField.map_injective f, ?_⟩
  apply Ideal.Quotient.lift_surjective_of_surjective
  convert Function.Surjective.comp (Ideal.Quotient.mk_surjective (I := (maximalIdeal S))) surj

variable {R} in
lemma _root_.ringKrullDim_le_ringKrullDim_add_card [IsLocalRing R] [IsNoetherianRing R]
    {S : Finset R} (hS : (S : Set R) ⊆ maximalIdeal R) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span S.toSet) + S.card := by
  sorry

lemma quotient_isRegularLocalRing_tfae [IsRegularLocalRing R] (S : Finset R)
    (sub : (S : Set R) ⊆ maximalIdeal R) :
    [∃ (T : Finset R), S ⊆ T ∧ T.card = ringKrullDim R ∧ Ideal.span T = maximalIdeal R,
     LinearIndependent (ResidueField R) ((⇑(maximalIdeal R).toCotangent).comp (Set.inclusion sub)),
     IsRegularLocalRing (R ⧸ Ideal.span (S : Set R)) ∧
     (ringKrullDim (R ⧸ Ideal.span (S : Set R)) + S.card = ringKrullDim R)].TFAE := by
  have : Nontrivial (R ⧸ Ideal.span S.toSet) :=
    Ideal.Quotient.nontrivial (ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (Ideal.span_le.mpr sub))
  have lochom : IsLocalHom (Ideal.Quotient.mk (Ideal.span S.toSet)) :=
    IsLocalHom.of_surjective _ (Ideal.Quotient.mk_surjective)
  tfae_have 1 → 2 := by
    rintro ⟨T, h, card, span⟩
    have Tsub : (T : Set R) ⊆ maximalIdeal R := by simpa [← span] using Ideal.subset_span
    have : LinearIndependent (ResidueField R)
      ((⇑(maximalIdeal R).toCotangent).comp (Set.inclusion Tsub)) := by
      apply linearIndependent_of_top_le_span_of_card_eq_finrank
      · simp only [Finset.coe_sort_coe, Set.range_comp, Set.range_inclusion Tsub,
          SetLike.coe_sort_coe, Finset.mem_coe, top_le_iff,
          IsLocalRing.CotangentSpace.span_image_eq_top_iff]
        simp only [span_eq_top_iff, Submodule.subtype_apply, Ideal.submodule_span_eq]
        convert span
        ext
        simpa using fun a ↦ Tsub a
      · rw [← spanFinrank_maximalIdeal R, ← Nat.cast_inj (R := WithBot ℕ∞),
          (isRegularLocalRing_iff R).mp ‹_›, ← card]
        simp
    have li := LinearIndependent.comp this (Set.inclusion h) (Set.inclusion_injective h)
    have inc : Set.inclusion Tsub ∘ Set.inclusion h = Set.inclusion sub := rfl
    simpa [← Function.comp_assoc, ← inc] using li
  tfae_have 2 → 3 := by
    intro li
    let _ : IsLocalRing (R ⧸ Ideal.span S.toSet) :=
      IsLocalRing.of_surjective _ Ideal.Quotient.mk_surjective
    rw [isRegularLocalRing_iff]
    have le := ringKrullDim_le_ringKrullDim_add_card sub
    have ge : (Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span S.toSet))) + S.card ≤
      ringKrullDim R := by
      simp only [← Nat.cast_add, ← (isRegularLocalRing_iff R).mp ‹_›, Nat.cast_le,
        spanFinrank_maximalIdeal]
      let f := Ideal.mapCotangent (maximalIdeal R) (maximalIdeal (R ⧸ Ideal.span S.toSet))
        (Ideal.Quotient.mkₐ R (Ideal.span S.toSet)) (fun x hx ↦ by simpa)
      have ker : (LinearMap.ker f : Set (maximalIdeal R).Cotangent) = (Submodule.span
        (ResidueField R) (Set.range (⇑(maximalIdeal R).toCotangent ∘ Set.inclusion sub))) := by
        simp only [ Submodule.coe_span_eq_span_of_surjective R (ResidueField R)
          IsLocalRing.residue_surjective, Finset.coe_sort_coe, SetLike.coe_set_eq]
        ext x
        induction' x using Submodule.Quotient.induction_on with x
        simp only [Ideal.mapCotangent, LinearMap.mem_ker, f]
        change (maximalIdeal (R ⧸ Ideal.span S.toSet)).toCotangent ⟨(Ideal.Quotient.mkₐ R
          (Ideal.span S.toSet)) x, _⟩ = 0 ↔ (maximalIdeal R).toCotangent x ∈ _
        simp only [Ideal.Quotient.mkₐ_eq_mk, Set.range_comp,
          Submodule.span_image', Ideal.toCotangent_eq_zero]
        have : maximalIdeal (R ⧸ Ideal.span S.toSet) =
          (maximalIdeal R).map (Ideal.Quotient.mk _) := by
          simp only [← ((local_hom_TFAE _).out 0 4).mp lochom,
            Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
        rw [this, ← Ideal.map_pow, ← Ideal.mem_comap, ← Submodule.mem_comap, Submodule.comap_map_eq,
          Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm,
          ← Submodule.comap_map_eq_of_injective (maximalIdeal R).subtype_injective (Submodule.span
          R (Set.range (Set.inclusion sub)) ⊔ LinearMap.ker (maximalIdeal R).toCotangent)]
        simp only [Finset.coe_sort_coe, Submodule.map_sup, Submodule.mem_comap,
          Submodule.subtype_apply]
        congr!
        · simp only [Submodule.map_span, Submodule.subtype_apply, Ideal.submodule_span_eq]
          congr
          ext
          simpa using fun a ↦ sub a
        · exact (Ideal.map_toCotangent_ker (maximalIdeal R)).symm
      let Q := (CotangentSpace R) ⧸ (Submodule.span (ResidueField R)
        (Set.range (⇑(maximalIdeal R).toCotangent ∘ Set.inclusion sub)))
      let f' : Q →+ (CotangentSpace (R ⧸ Ideal.span S.toSet)) :=
        QuotientAddGroup.lift _ f
        (le_of_eq (AddSubgroup.ext (fun x ↦ (congrFun ker.symm x).to_iff)))
      have bij : Function.Bijective f' := by
        constructor
        · rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
          intro x hx
          induction' x using QuotientAddGroup.induction_on with x
          have : x ∈ (LinearMap.ker f : Set (maximalIdeal R).Cotangent) := LinearMap.mem_ker.mpr hx
          rw [ker] at this
          exact AddSubgroup.mem_bot.mpr ((QuotientAddGroup.eq_zero_iff _).mpr this)
        · apply QuotientAddGroup.lift_surjective_of_surjective
          intro x
          rcases Ideal.toCotangent_surjective _ x with ⟨y, hy⟩
          rcases Ideal.Quotient.mk_surjective y.1 with ⟨z, hz⟩
          have : z ∈ maximalIdeal R := by simp [← ((local_hom_TFAE _).out 0 4).mp lochom, hz]
          use (maximalIdeal R).toCotangent ⟨z, this⟩
          simp [f, ← hy, hz]
      let e : Q ≃+ (CotangentSpace (R ⧸ Ideal.span S.toSet)) :=
        AddEquiv.ofBijective f' bij
      have rk := rank_eq_of_equiv_equiv (ResidueField.map (Ideal.Quotient.mk (Ideal.span S.toSet)))
        e (ResidueField.map_bijective_of_surjective _ Ideal.Quotient.mk_surjective) (fun r m ↦ by
          induction' m using Submodule.Quotient.induction_on with m
          rw [← Submodule.Quotient.mk_smul]
          simp only [Finset.coe_sort_coe, AddEquiv.ofBijective_apply, e, f']
          induction' r using Submodule.Quotient.induction_on with r
          change f (r • m) = (ResidueField.map (Ideal.Quotient.mk (Ideal.span S.toSet)))
            (IsLocalRing.residue R r) • (f m)
          simp only [map_smul]
          rfl)
      have frk : Module.finrank (ResidueField R) Q = Module.finrank
        (ResidueField (R ⧸ Ideal.span S.toSet)) (CotangentSpace (R ⧸ Ideal.span S.toSet)) := by
        simp [Module.finrank, rk]
      have : Fintype.card S.toSet = S.card := Fintype.card_ofFinset S (fun x ↦ Finset.mem_coe)
      rw [← frk, ← this, ← finrank_span_eq_card li]
      apply Module.finrank_quotient_add_finrank_le
    have : ringKrullDim (R ⧸ Ideal.span S.toSet) + S.card ≤
      (Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span S.toSet))) + S.card :=
      add_le_add_right (ringKrullDim_le_spanFinrank_maximalIdeal _) _
    exact ⟨(withBotENat_add_coe_cancel _ _ S.card).mp
      (le_antisymm (ge.trans le) this), le_antisymm (this.trans ge) le⟩
  tfae_have 3 → 1 := by
    classical
    rintro ⟨reg, dim⟩
    simp only [← (isRegularLocalRing_iff _).mp reg, ← Nat.cast_add, ←
      (isRegularLocalRing_iff R).mp ‹_›, Nat.cast_inj] at dim
    let fg : (maximalIdeal (R ⧸ Ideal.span S.toSet)).FG :=
      (isNoetherianRing_iff_ideal_fg _).mp inferInstance _
    have fin : (maximalIdeal (R ⧸ Ideal.span S.toSet)).generators.Finite :=
      Submodule.FG.finite_generators fg
    let U := Quotient.out '' (maximalIdeal (R ⧸ Ideal.span S.toSet)).generators
    let _ : Fintype U := (Set.Finite.image _ fin).fintype
    use S ∪ U.toFinset
    have span : Ideal.span (S ∪ U) = maximalIdeal R := by
      rw [Ideal.span_union, ← Ideal.mk_ker (I := Ideal.span S.toSet), sup_comm,
        ← Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.map_span]
      have : Ideal.span (⇑(Ideal.Quotient.mk (Ideal.span ↑S)) '' U) =
        Submodule.span _ (maximalIdeal (R ⧸ Ideal.span S.toSet)).generators := by
        simp [U, ← Set.image_comp]
      rw [this, Submodule.span_generators]
      exact ((local_hom_TFAE _).out 0 4).mp lochom
    simp only [Finset.subset_union_left, true_and, ← (isRegularLocalRing_iff R).mp ‹_›,
      Finset.coe_union, Set.coe_toFinset]
    refine ⟨le_antisymm ?_ ?_, span⟩
    · apply Nat.cast_le.mpr (le_trans (Finset.card_union_le _ _) _)
      simp only [Set.toFinset_card, ← dim, add_comm, add_le_add_iff_left]
      rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]
      apply le_trans (Set.ncard_image_le fin) (le_of_eq (Submodule.FG.generators_ncard fg))
    · simp only [← span, ← Set.ncard_coe_finset, Finset.coe_union, Set.coe_toFinset, Nat.cast_le]
      exact Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite (S ∪ U))
  tfae_finish

lemma quotient_span_singleton [IsRegularLocalRing R] {x : R} (mem : x ∈ maximalIdeal R)
    (nmem : x ∉ (maximalIdeal R) ^ 2) : IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
    (ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R) := by
  have : ({x} : Finset R).toSet = {x} := by exact Finset.coe_singleton x
  rw [← Nat.cast_one, ← Finset.card_singleton x, ← Finset.coe_singleton x]
  apply ((quotient_isRegularLocalRing_tfae R {x} (by simpa)).out 1 2).mp
  simpa [← LinearMap.mem_ker, Ideal.mem_toCotangent_ker] using nmem

lemma exist_nat_eq [FiniteRingKrullDim R] : ∃ n : ℕ, ringKrullDim R = n := by
  have : (ringKrullDim R).unbot ringKrullDim_ne_bot ≠ ⊤ := by
    by_contra eq
    rw [← WithBot.coe_inj, WithBot.coe_unbot, WithBot.coe_top] at eq
    exact ringKrullDim_ne_top eq
  use ((ringKrullDim R).unbot ringKrullDim_ne_bot).toNat
  exact (WithBot.coe_unbot (ringKrullDim R) ringKrullDim_ne_bot).symm.trans
    (WithBot.coe_inj.mpr (ENat.coe_toNat this).symm)

open Pointwise in
theorem isDomain_of_isRegularLocalRing [IsRegularLocalRing R] : IsDomain R := by
  obtain ⟨n, hn⟩ := exist_nat_eq R
  induction' n with n ih generalizing R
  · simp only [← (isRegularLocalRing_iff R).mp ‹_›, CharP.cast_eq_zero, Nat.cast_eq_zero] at hn
    have : maximalIdeal R = ⊥ := by
      rw [← Submodule.spanRank_eq_zero_iff_eq_bot, Submodule.fg_iff_spanRank_eq_spanFinrank.mpr
        ((isNoetherianRing_iff_ideal_fg R).mp inferInstance _), hn, Nat.cast_zero]
    exact (isField_iff_maximalIdeal_eq.mpr this).isDomain
  · obtain ⟨x, xmem, xnmem⟩ : ∃ x ∈ maximalIdeal R,
      x ∉ ⋃ I ∈ {(maximalIdeal R) ^ 2} ∪ minimalPrimes R, I := by
      by_contra! h
      have fin : ({(maximalIdeal R) ^ 2} ∪ minimalPrimes R).Finite :=
        Set.Finite.union (Set.finite_singleton _) (minimalPrimes.finite_of_isNoetherianRing R)
      rcases (Ideal.subset_union_prime_finite fin ((maximalIdeal R) ^ 2) ((maximalIdeal R) ^ 2)
        (fun I hI ne _ ↦ Ideal.minimalPrimes_isPrime (by simpa [ne] using hI))).mp h with
        ⟨I, hI, sub⟩
      simp only [Set.singleton_union, Set.mem_insert_iff] at hI
      rcases hI with eq|min
      · have : IsField R := by
          simp only [← subsingleton_cotangentSpace_iff, Ideal.cotangent_subsingleton_iff,
            IsIdempotentElem]
          exact le_antisymm Ideal.mul_le_right (le_of_le_of_eq sub (eq.trans (pow_two _)))
        rw [ringKrullDim_eq_zero_of_isField this, ← Nat.cast_zero, Nat.cast_inj] at hn
        exact Nat.zero_ne_add_one n hn
      · let _ : I.IsPrime := Ideal.minimalPrimes_isPrime min
        rw [← Ideal.primeHeight_eq_ringKrullDim_iff.mpr (le_antisymm (le_maximalIdeal_of_isPrime I)
          sub), Ideal.primeHeight_eq_zero_iff.mpr min, ← Nat.cast_zero] at hn
        exact Nat.zero_ne_add_one n (Nat.cast_inj.mp hn)
    simp only [Set.singleton_union, Set.mem_insert_iff, Set.iUnion_iUnion_eq_or_left, Set.mem_union,
      SetLike.mem_coe, Set.mem_iUnion, exists_prop, not_or, not_exists, not_and] at xnmem
    obtain ⟨reg, dim⟩ := quotient_span_singleton R xmem xnmem.1
    simp only [hn, Nat.cast_add, Nat.cast_one] at dim
    have ih' := ih (R ⧸ Ideal.span {x}) ((withBotENat_add_coe_cancel _ _ 1).mp dim)
    have : (Ideal.span {x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp ih'
    obtain ⟨p, min, hp⟩ := Ideal.exists_minimalPrimes_le (bot_le (a := Ideal.span {x}))
    let _ : p.IsPrime := Ideal.minimalPrimes_isPrime min
    have eq_smul : p = Ideal.span {x} • p := by
      ext y
      simp only [smul_eq_mul, Ideal.mem_span_singleton_mul]
      refine ⟨fun h ↦ ?_, fun ⟨z, hz, eq⟩ ↦ by simpa [← eq] using Ideal.mul_mem_left p x hz⟩
      rcases Ideal.mem_span_singleton'.mp (hp h) with ⟨z, hz⟩
      use z
      simp only [← hz, mul_comm, and_true]
      have : z ∈ p ∨ x ∈ p := (Ideal.IsPrime.mem_or_mem ‹_›  (by simpa [hz]))
      simpa [xnmem.2 p min] using this
    have pfg : p.FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance _
    have := Submodule.eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator pfg eq_smul
        (le_trans ((Ideal.span_singleton_le_iff_mem _).mpr xmem) (maximalIdeal_le_jacobson _))
    have : (⊥ : Ideal R).IsPrime := by simpa [← this]
    exact IsDomain.of_bot_isPrime R

open RingTheory.Sequence in
theorem isRegular_of_span_eq_maximalIdeal [IsRegularLocalRing R] (rs : List R)
    (eq : Ideal.ofList rs = maximalIdeal R) (len : rs.length = ringKrullDim R) :
    IsRegular R rs := by
  sorry

end
