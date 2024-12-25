/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Transfer

/-!
# Z-Groups

A Z-group is a group whose Sylow subgroups are all cyclic.

## Main definitions

* `IsZGroup G`: a predicate stating that all Sylow subgroups of `G` are cyclic.

## Main results

* `IsZGroup.isCyclic_abelianization`: a finite Z-group has cyclic abelianization.
* `IsZGroup.isCyclic_commutator`: a finite Z-group has cyclic commutator subgroup.

TODO: Show that if `G` is a Z-group with commutator subgroup `G'`, then `G = G' ⋊ G/G'` where `G'`
and `G/G'` are cyclic of coprime orders.

-/

variable (G G' G'' : Type*) [Group G] [Group G'] [Group G''] (f : G →* G') (f' : G' →* G'')

/-- A Z-group is a group whose Sylow subgroups are all cyclic. -/
@[mk_iff] class IsZGroup : Prop where
  isZGroup : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsCyclic P

variable {G G' G'' f f'}

namespace IsZGroup

instance [IsZGroup G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) : IsCyclic P :=
  isZGroup p Fact.out P

theorem _root_.IsPGroup.isCyclic_of_isZGroup [IsZGroup G] {p : ℕ} [Fact p.Prime]
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

section Solvable

variable (G) in
theorem commutator_lt [Finite G] [IsZGroup G] [Nontrivial G] : commutator G < ⊤ := by
  let p := (Nat.card G).minFac
  have hp : p.Prime := Nat.minFac_prime Finite.one_lt_card.ne'
  have := Fact.mk hp
  let P : Sylow p G := default
  have hP := isZGroup p hp P
  let f := MonoidHom.transferSylow P (hP.normalizer_le_centralizer rfl)
  refine lt_of_le_of_lt (Abelianization.commutator_subset_ker f) ?_
  have h := P.ne_bot_of_dvd_card (Nat.card G).minFac_dvd
  contrapose! h
  rw [← Subgroup.isComplement'_top_left, ← (not_lt_top_iff.mp h)]
  exact hP.isComplement' rfl

instance [Finite G] [IsZGroup G] : IsSolvable G := by
  rw [isSolvable_iff_commutator_lt]
  intro H h
  rw [← H.nontrivial_iff_ne_bot] at h
  rw [← H.range_subtype, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
    Subgroup.map_subtype_lt_map_subtype]
  exact commutator_lt H

end Solvable

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

section Commutator

variable (G) in
/-- A finite Z-group has cyclic commutator subgroup. -/
theorem isCyclic_commutator [Finite G] [IsZGroup G] : IsCyclic (commutator G) := by
  refine WellFoundedLT.induction (C := fun H ↦ IsCyclic (⁅H, H⁆ : Subgroup G)) (⊤ : Subgroup G) ?_
  intro H hH
  rcases eq_or_ne H ⊥ with rfl | h
  · rw [Subgroup.commutator_bot_left]
    infer_instance
  · specialize hH ⁅H, H⁆ (IsSolvable.commutator_lt_of_ne_bot h)
    replace hH : IsCyclic (⁅commutator H, commutator H⁆ : Subgroup H) := by
      let f := Subgroup.equivMapOfInjective ⁅commutator H, commutator H⁆ _ H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subtype_commutator] at f
      exact isCyclic_of_surjective f.symm f.symm.surjective
    suffices IsCyclic (commutator H) by
      let f := Subgroup.equivMapOfInjective (commutator H) _ H.subtype_injective
      rw [Subgroup.map_subtype_commutator] at f
      exact isCyclic_of_surjective f f.surjective
    suffices h : commutator (commutator H) ≤ Subgroup.center (commutator H) by
      rw [← Abelianization.ker_of (commutator H)] at h
      let _ := commGroupOfCyclicCenterQuotient Abelianization.of h
      infer_instance
    suffices h : (commutator (commutator H)).map (commutator H).subtype ≤
        Subgroup.centralizer (commutator H) by
      simpa [SetLike.le_def, Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff] using h
    rw [Subgroup.map_subtype_commutator, Subgroup.le_centralizer_iff]
    let _ := (hH.mulAutMulEquiv _).toMonoidHom.commGroupOfInjective (hH.mulAutMulEquiv _).injective
    have h := Abelianization.commutator_subset_ker ⁅commutator H, commutator H⁆.normalizerMonoidHom
    rwa [Subgroup.normalizerMonoidHom_ker, Subgroup.normalizer_eq_top,
      ← Subgroup.map_subtype_le_map_subtype, Subgroup.map_subtype_commutator,
        Subgroup.map_subgroupOf_eq_of_le le_top] at h

end Commutator

section Classification

/-- An extension of coprime Z-groups is a Z-group. -/
theorem isZGroup_of_coprime [Finite G] [IsZGroup G] [IsZGroup G'']
    (h_le : f'.ker ≤ f.range) (h_cop : (Nat.card G).Coprime (Nat.card G'')) :
    IsZGroup G' := by
  refine ⟨fun p hp P ↦ ?_⟩
  have := Fact.mk hp
  replace h_cop := (h_cop.of_dvd ((Subgroup.card_dvd_of_le h_le).trans
    (Subgroup.card_range_dvd f)) (Subgroup.index_ker f' ▸ f'.range.card_subgroup_dvd_card))
  rcases P.2.le_or_disjoint_of_coprime h_cop with h | h
  · replace h_le : P ≤ f.range := h.trans h_le
    suffices IsCyclic (P.subgroupOf f.range) by
      have key := Subgroup.subgroupOfEquivOfLe h_le
      exact isCyclic_of_surjective key key.surjective
    obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective f.rangeRestrict_surjective p (P.subtype h_le)
    rw [Sylow.ext_iff, Sylow.coe_mapSurjective, Sylow.coe_subtype] at hQ
    exact hQ ▸ isCyclic_of_surjective _ (f.rangeRestrict.subgroupMap_surjective Q)
  · have := (P.2.map f').isCyclic_of_isZGroup
    apply isCyclic_of_injective (f'.subgroupMap P)
    rwa [← MonoidHom.ker_eq_bot_iff, P.ker_subgroupMap f', Subgroup.subgroupOf_eq_bot]

end Classification

end IsZGroup
