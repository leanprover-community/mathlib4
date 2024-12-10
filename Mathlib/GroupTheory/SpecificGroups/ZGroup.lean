/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Z-Groups

A Z-group is a group whose Sylow subgroups are all cyclic.

## Main definitions

* `IsZGroup G`: A predicate stating that all Sylow subgroups of `G` are cyclic.

TODO: Show that if `G` is a Z-group with commutator subgroup `G'`, then `G = G' ⋊ G/G'` where `G'`
and `G/G'` are cyclic of coprime orders.

-/

-- @[to_additive]
-- theorem Subgroup.relindex_map_of_injective {G G' : Type*} [Group G] [Group G'] (H : Subgroup G)
--     {f : G →* G'} (hf : Function.Injective f) :
--     (H.map f).relindex f.range = H.index := by
--   rw [← f.ker_eq_bot_iff] at hf
--   have key : (H.map f).subgroupOf f.range = H.map f.rangeRestrict := by
--     simp [Subgroup.ext_iff, mem_subgroupOf, Subtype.ext_iff]
--   rw [relindex, key, H.index_map_eq f.rangeRestrict_surjective]
--   rw [f.ker_rangeRestrict, hf]
--   exact bot_le

-- @[to_additive]
-- theorem Subgroup.relindex_map_subtype {G : Type*} [Group G] {H : Subgroup G} (K : Subgroup H) :
--     (K.map H.subtype).relindex H = K.index := by
--   rw [← relindex_map_of_injective K H.subtype_injective, H.range_subtype]

@[to_additive]
theorem Subgroup.map_lt_map_iff_of_injective {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) {H K : Subgroup G} : H.map f < K.map f ↔ H < K := by
  simp_rw [lt_iff_le_not_le, map_le_map_iff_of_injective hf]

@[to_additive (attr := simp)]
theorem Subgroup.map_subtype_lt_map_subtype {G : Type*} [Group G] {G' : Subgroup G}
    {H K : Subgroup G'} : H.map G'.subtype < K.map G'.subtype ↔ H < K :=
  map_lt_map_iff_of_injective G'.subtype_injective -- also clean up map_subtype_le_map_subtype

theorem IsSolvable.commutator_lt_top_of_nontrivial (G : Type*) [Group G] [hG : IsSolvable G]
    [Nontrivial G] : commutator G < ⊤ := by
  obtain ⟨n, hn⟩ := hG
  contrapose! hn
  refine ne_of_eq_of_ne ?_ top_ne_bot
  induction' n with n h
  · exact derivedSeries_zero G
  · rwa [derivedSeries_succ, h, ← commutator_def, ← not_lt_top_iff]

theorem IsSolvable.commutator_lt_of_ne_bot {G : Type*} [Group G] [IsSolvable G]
    {H : Subgroup G} (hH : H ≠ ⊥) : ⁅H, H⁆ < H := by
  rw [← Subgroup.nontrivial_iff_ne_bot] at hH
  rw [← H.range_subtype, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
    Subgroup.map_subtype_lt_map_subtype]
  exact commutator_lt_top_of_nontrivial H

theorem isSolvable_iff_commutator_lt {G : Type*} [Group G] [WellFoundedLT (Subgroup G)] :
    IsSolvable G ↔ ∀ H : Subgroup G, H ≠ ⊥ → ⁅H, H⁆ < H := by
  refine ⟨fun _ _ ↦ IsSolvable.commutator_lt_of_ne_bot, fun h ↦ ?_⟩
  suffices h : IsSolvable (⊤ : Subgroup G) from
    solvable_of_surjective (MonoidHom.range_eq_top.mp (Subgroup.range_subtype ⊤))
  refine WellFoundedLT.induction (C := fun (H : Subgroup G) ↦ IsSolvable H) (⊤ : Subgroup G) ?_
  intro H hH
  rcases eq_or_ne H ⊥ with rfl | h'
  · apply isSolvable_of_subsingleton
  · specialize h H h'
    specialize hH ⁅H, H⁆ h
    obtain ⟨n, hn⟩ := hH
    use n + 1
    rw [← (Subgroup.map_injective H.subtype_injective).eq_iff]
    rw [← (Subgroup.map_injective ⁅H, H⁆.subtype_injective).eq_iff] at hn
    rw [Subgroup.map_bot] at hn ⊢
    rw [← hn]
    clear hn
    induction' n with n ih
    · simp_rw [derivedSeries_succ, derivedSeries_zero, Subgroup.map_commutator,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    · rw [derivedSeries_succ, Subgroup.map_commutator, ih, derivedSeries_succ,
        Subgroup.map_commutator]

variable (G G' : Type*) [Group G] [Group G'] (f : G →* G')

/-- A Z-group is a group whose Sylow subgroups are all cyclic. -/
@[mk_iff] class IsZGroup : Prop where
  isZGroup : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsCyclic P

variable {G G' f}

namespace IsZGroup

instance [IsZGroup G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) : IsCyclic P :=
  isZGroup p Fact.out P

theorem of_squarefree (hG : Squarefree (Nat.card G)) : IsZGroup G := by
  have : Finite G := Nat.finite_of_card_ne_zero hG.ne_zero
  refine ⟨fun p hp P ↦ ?_⟩
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  exact isCyclic_of_card_dvd_prime ((hk ▸ hG.pow_dvd_of_pow_dvd) P.card_subgroup_dvd_card)

theorem of_injective [hG' : IsZGroup G'] (hf : Function.Injective f) : IsZGroup G := by
  rw [isZGroup_iff] at hG' ⊢
  intro p hp P
  obtain ⟨Q, hQ⟩ := P.exists_comap_eq_of_injective hf
  specialize hG' p hp Q
  have h : Subgroup.map f P ≤ Q := hQ ▸ Subgroup.map_comap_le f ↑Q
  have := isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe h).surjective
  exact isCyclic_of_surjective _ (Subgroup.equivMapOfInjective P f hf).symm.surjective

instance [IsZGroup G] (H : Subgroup G) : IsZGroup H := of_injective H.subtype_injective

theorem of_surjective [Finite G] [hG : IsZGroup G] (hf : Function.Surjective f) : IsZGroup G' := by
  rw [isZGroup_iff] at hG ⊢
  intro p hp P
  have := Fact.mk hp
  obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective hf p P
  specialize hG p hp Q
  exact isCyclic_of_surjective _ (f.subgroupMap_surjective Q)

instance [Finite G] [IsZGroup G] (H : Subgroup G) [H.Normal] : IsZGroup (G ⧸ H) :=
  of_surjective (QuotientGroup.mk'_surjective H)

section Solvable

variable (G)

theorem commutator_lt [Finite G] [IsZGroup G] [Nontrivial G] : commutator G < ⊤ := by
  let p := (Nat.card G).minFac
  have hp : p.Prime := Nat.minFac_prime Finite.one_lt_card.ne'
  have := Fact.mk hp
  let P : Sylow p G := default
  have hP := isZGroup p hp P
  let f := MonoidHom.transferSylow P hP.normalizer_le_centralizer
  let K := f.ker
  have key : f.ker.IsComplement' P := hP.isComplement'
  have key1 : commutator G ≤ f.ker := by
    let _ := hP.commGroup
    exact Abelianization.commutator_subset_ker f
  have key2 : f.ker < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [h, Subgroup.isComplement'_top_left] at key
    exact P.ne_bot_of_dvd_card (Nat.card G).minFac_dvd key
  exact lt_of_le_of_lt key1 key2

instance [Finite G] [IsZGroup G] : IsSolvable G := by
  rw [isSolvable_iff_commutator_lt]
  intro H h
  rw [← H.nontrivial_iff_ne_bot] at h
  rw [← H.range_subtype, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
    Subgroup.map_subtype_lt_map_subtype]
  exact commutator_lt H

end Solvable

section Nilpotent

variable (G)

theorem exponent_eq_card [Finite G] [IsZGroup G] : Monoid.exponent G = Nat.card G := by
  refine dvd_antisymm Group.exponent_dvd_nat_card ?_
  rw [← Nat.factorization_prime_le_iff_dvd Nat.card_pos.ne' Monoid.exponent_ne_zero_of_finite]
  intro p hp
  have := Fact.mk hp
  let P : Sylow p G := default
  rw [← hp.pow_dvd_iff_le_factorization Monoid.exponent_ne_zero_of_finite,
      ← P.card_eq_multiplicity, ← (isZGroup p hp P).exponent_eq_card]
  exact Monoid.exponent_dvd_of_monoidHom P.1.subtype P.1.subtype_injective

instance [Finite G] [IsZGroup G] [hG : Group.IsNilpotent G] : IsCyclic G := by
  have (p : { x // x ∈ (Nat.card G).primeFactors }) : Fact p.1.Prime :=
    ⟨Nat.prime_of_mem_primeFactors p.2⟩
  let h (p : { x // x ∈ (Nat.card G).primeFactors }) (P : Sylow p G) : CommGroup P :=
    IsCyclic.commGroup
  obtain ⟨ϕ⟩ := ((isNilpotent_of_finite_tfae (G := G)).out 0 4).mp hG
  let _ : CommGroup G :=
    ⟨fun g h ↦ by rw [← ϕ.symm.injective.eq_iff, map_mul, mul_comm, ← map_mul]⟩
  exact IsCyclic.of_exponent_eq_card (exponent_eq_card G)

end Nilpotent

section Hall

theorem _root_.IsCyclic.normalizer_le_centralizer_or_le_commutator {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [IsCyclic P] :
    P.normalizer ≤ Subgroup.centralizer P ∨ P ≤ commutator G := by

  sorry

theorem _root_.IsCyclic.not_dvd_card_commutator_or_not_dvd_index_commutator [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) [IsCyclic P] :
    ¬ p ∣ Nat.card (commutator G) ∨ ¬ p ∣ (commutator G).index := by
  refine (IsCyclic.normalizer_le_centralizer_or_le_commutator P).imp ?_ ?_ <;>
      refine fun hP h ↦ P.not_dvd_index (h.trans ?_)
  · let _ : CommGroup P := IsCyclic.commGroup
    rw [(MonoidHom.ker_transferSylow_isComplement' P hP).index_eq_card]
    exact Subgroup.card_dvd_of_le (Abelianization.commutator_subset_ker _)
  · exact Subgroup.index_dvd_of_le hP

variable (G)

theorem coprime_commutator_index [Finite G] [IsZGroup G] :
    (Nat.card (commutator G)).Coprime (commutator G).index := by
  suffices h : ∀ p, p.Prime → (¬ p ∣ Nat.card (commutator G) ∨ ¬ p ∣ (commutator G).index) by
    contrapose! h
    exact Nat.Prime.not_coprime_iff_dvd.mp h
  intro p hp
  let P : Sylow p G := default
  have := Fact.mk hp
  exact IsCyclic.not_dvd_card_commutator_or_not_dvd_index_commutator P

end Hall

end IsZGroup
