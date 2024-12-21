/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.GroupTheory.Nilpotent

/-!
# Z-Groups

A Z-group is a group whose Sylow subgroups are all cyclic.

## Main definitions

* `IsZGroup G`: a predicate stating that all Sylow subgroups of `G` are cyclic.

## Main results

* `IsZGroup.isCyclic_abelianization`: a finite Z-group has cyclic abelianization.

TODO: Show that if `G` is a Z-group with commutator subgroup `G'`, then `G = G' ⋊ G/G'` where `G'`
and `G/G'` are cyclic of coprime orders.

-/

variable (G G' : Type*) [Group G] [Group G'] (f : G →* G')

/-- A Z-group is a group whose Sylow subgroups are all cyclic. -/
@[mk_iff] class IsZGroup : Prop where
  isZGroup : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsCyclic P

variable {G G' f}

namespace IsZGroup

instance [IsZGroup G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) : IsCyclic P :=
  isZGroup p Fact.out P

theorem _root_.IsPGroup.isCyclic_of_zgroup [IsZGroup G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsPGroup p P) : IsCyclic P := by
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  exact Subgroup.isCyclic_of_le hQ

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

section Nilpotent

variable (G) in
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
  obtain ⟨ϕ⟩ := ((isNilpotent_of_finite_tfae (G := G)).out 0 4).mp hG
  let _ : CommGroup G :=
    ⟨fun g h ↦ by rw [← ϕ.symm.injective.eq_iff, map_mul, mul_comm, ← map_mul]⟩
  exact IsCyclic.of_exponent_eq_card (exponent_eq_card G)

/-- A finite Z-group has cyclic abelianization. -/
instance isCyclic_abelianization [Finite G] [IsZGroup G] : IsCyclic (Abelianization G) :=
  let _ : IsZGroup (Abelianization G) := inferInstanceAs (IsZGroup (G ⧸ commutator G))
  inferInstance

end Nilpotent

end IsZGroup

/-- An extension of coprime Z-groups is a Z-group. -/
theorem isZGroup_of_coprime {G H K : Type*} [Group G] [Group H] [Group K]
    [Finite G] [IsZGroup G] [IsZGroup K] (f : G →* H) (g : H →* K) (h_le : g.ker ≤ f.range)
    (h_cop : (Nat.card G).Coprime (Nat.card K)) : IsZGroup H := by
  have h_dvd : Nat.card g.ker ∣ Nat.card G :=
    (Subgroup.card_dvd_of_le h_le).trans (Subgroup.card_range_dvd f)
  by_cases hK : Nat.card K = 0
  · rw [hK, Nat.coprime_zero_right] at h_cop
    rw [h_cop, Nat.dvd_one, Subgroup.card_eq_one, MonoidHom.ker_eq_bot_iff] at h_dvd
    exact IsZGroup.of_injective h_dvd
  have : Finite K := Nat.finite_of_card_ne_zero hK
  have : Finite H := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [← g.ker.card_mul_index, Subgroup.index_ker]
    exact mul_ne_zero (ne_zero_of_dvd_ne_zero Finite.card_pos.ne' h_dvd) Finite.card_pos.ne'
  refine ⟨fun p hp P ↦ ?_⟩
  have := Fact.mk hp
  replace h_cop : (Nat.card G).Coprime (Nat.card P) ∨ (Nat.card K).Coprime (Nat.card P) := by
    obtain ⟨k, hk⟩ := P.2.exists_card_eq
    refine hk ▸ Or.imp hp.coprime_pow_of_not_dvd hp.coprime_pow_of_not_dvd ?_
    contrapose! h_cop
    exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, h_cop⟩
  rcases h_cop with hP | hP
  · have := (P.2.map g).isCyclic_of_zgroup
    refine isCyclic_of_injective (g.subgroupMap P) ?_
    rw [← MonoidHom.ker_eq_bot_iff, P.ker_subgroupMap g, Subgroup.subgroupOf_eq_bot, disjoint_iff]
    exact Subgroup.inf_eq_bot_of_coprime (hP.coprime_dvd_left h_dvd)
  · replace h_le : P ≤ f.range := by
      refine le_trans ?_ h_le
      rw [← Subgroup.map_eq_bot_iff, ← Subgroup.card_eq_one]
      exact Nat.eq_one_of_dvd_coprimes hP (P.map g).card_subgroup_dvd_card (P.card_map_dvd g)
    suffices IsCyclic (P.subgroupOf f.range) by
      have key := Subgroup.subgroupOfEquivOfLe h_le
      exact isCyclic_of_surjective key key.surjective
    obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective f.rangeRestrict_surjective p (P.subtype h_le)
    rw [Sylow.ext_iff, Sylow.coe_mapSurjective, Sylow.coe_subtype] at hQ
    exact hQ ▸ isCyclic_of_surjective _ (f.rangeRestrict.subgroupMap_surjective Q)
