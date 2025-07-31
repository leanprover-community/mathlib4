/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Z-Groups

A Z-group is a group whose Sylow subgroups are all cyclic.

## Main definitions

* `IsZGroup G`: a predicate stating that all Sylow subgroups of `G` are cyclic.

## Main results

* `IsZGroup.isCyclic_abelianization`: a finite Z-group has cyclic abelianization.
* `IsZGroup.isCyclic_commutator`: a finite Z-group has cyclic commutator subgroup.
* `IsZGroup.coprime_commutator_index`: the commutator subgroup of a finite Z-group is a
  Hall-subgroup (the commutator subgroup has cardinality coprime to its index).
* `isZGroup_iff_exists_mulEquiv`: a finite group `G` is a Z-group if and only if `G` is isomorphic
  to a semidirect product of two cyclic subgroups of coprime order.

-/

variable (G G' G'' : Type*) [Group G] [Group G'] [Group G''] (f : G →* G') (f' : G' →* G'')

/-- A Z-group is a group whose Sylow subgroups are all cyclic. -/
@[mk_iff] class IsZGroup : Prop where
  isZGroup : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsCyclic P

variable {G G' G'' f f'}

namespace IsZGroup

instance [IsCyclic G] : IsZGroup G :=
  ⟨inferInstance⟩

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

end IsZGroup

section Hall

variable {p : ℕ} [Fact p.Prime]

namespace IsPGroup

/-- If a group `K` acts on a cyclic `p`-group `G` of coprime order, then the map `K × G → G`
  defined by `(k, g) ↦ k • g * g⁻¹` is either trivial or surjective. -/
theorem smul_mul_inv_trivial_or_surjective [IsCyclic G] (hG : IsPGroup p G)
    {K : Type*} [Group K] [MulDistribMulAction K G] (hGK : (Nat.card G).Coprime (Nat.card K)) :
    (∀ g : G, ∀ k : K, k • g * g⁻¹ = 1) ∨ (∀ g : G, ∃ k : K, ∃ q : G, k • q * q⁻¹ = g) := by
  by_cases hc : Nat.card G = 0
  · rw [hc, Nat.coprime_zero_left, Nat.card_eq_one_iff_unique] at hGK
    simp [← hGK.1.elim 1]
  have := Nat.finite_of_card_ne_zero hc
  let ϕ := MulDistribMulAction.toMonoidHomZModOfIsCyclic G K rfl
  have h (g : G) (k : K) (n : ℤ) (h : ϕ k - 1 = n) : k • g * g⁻¹ = g ^ n := by
    rw [sub_eq_iff_eq_add, ← Int.cast_one, ← Int.cast_add] at h
    rw [MulDistribMulAction.toMonoidHomZModOfIsCyclic_apply rfl k g (n + 1) h,
      zpow_add_one, mul_inv_cancel_right]
  replace hG k : ϕ k = 1 ∨ IsUnit (ϕ k - 1) := by
    obtain ⟨n, hn⟩ := hG.exists_card_eq
    exact ZMod.eq_one_or_isUnit_sub_one hn (ϕ k)
      (hGK.symm.coprime_dvd_left ((orderOf_map_dvd ϕ k).trans (orderOf_dvd_natCard k)))
  rcases forall_or_exists_not (fun k : K ↦ ϕ k = 1) with hϕ | ⟨k, hk⟩
  · exact Or.inl fun p k ↦ by rw [h p k 0 (by rw [hϕ, sub_self, Int.cast_zero]), zpow_zero]
  · obtain ⟨⟨u, v, -, hvu⟩, hu : u = ϕ k - 1⟩ := (hG k).resolve_left hk
    rw [← u.intCast_zmod_cast] at hu hvu
    rw [← v.intCast_zmod_cast, ← Int.cast_mul, ← Int.cast_one, ZMod.intCast_eq_intCast_iff] at hvu
    refine Or.inr fun p ↦ zpow_one p ▸ ⟨k, p ^ (v.cast : ℤ), ?_⟩
    rw [h (p ^ v.cast) k u.cast hu.symm, ← zpow_mul, zpow_eq_zpow_iff_modEq]
    exact hvu.of_dvd (Int.natCast_dvd_natCast.mpr (orderOf_dvd_natCard p))

/-- If a cyclic `p`-subgroup `P` acts by conjugation on a subgroup `K` of coprime order, then
  either `⁅K, P⁆ = ⊥` or `⁅K, P⁆ = P`. -/
theorem commutator_eq_bot_or_commutator_eq_self {P K : Subgroup G} [IsCyclic P]
    (hP : IsPGroup p P) (hKP : K ≤ P.normalizer) (hPK : (Nat.card P).Coprime (Nat.card K)) :
    ⁅K, P⁆ = ⊥ ∨ ⁅K, P⁆ = P := by
  let _ := MulDistribMulAction.compHom P (P.normalizerMonoidHom.comp (Subgroup.inclusion hKP))
  refine (smul_mul_inv_trivial_or_surjective hP hPK).imp (fun h ↦ ?_) fun h ↦ ?_
  · rw [eq_bot_iff, Subgroup.commutator_le]
    exact fun k hk g hg ↦ Subtype.ext_iff.mp (h ⟨g, hg⟩ ⟨k, hk⟩)
  · rw [le_antisymm_iff, Subgroup.commutator_le]
    refine ⟨fun k hk g hg ↦ P.mul_mem ((hKP hk g).mp hg) (P.inv_mem hg), fun g hg ↦ ?_⟩
    obtain ⟨k, q, hkq⟩ := h ⟨g, hg⟩
    rw [← Subtype.coe_mk g hg, ← hkq]
    exact Subgroup.commutator_mem_commutator k.2 q.2

end IsPGroup

namespace Sylow

variable [Finite G] (P : Sylow p G) [IsCyclic P]

/-- If a normal cyclic Sylow `p`-subgroup `P` has a complement `K`, then either `⁅K, P⁆ = ⊥` or
  `⁅K, P⁆ = P`. -/
theorem commutator_eq_bot_or_commutator_eq_self [P.Normal] {K : Subgroup G}
    (h : K.IsComplement' P) : ⁅K, P.1⁆ = ⊥ ∨ ⁅K, P.1⁆ = P :=
  P.2.commutator_eq_bot_or_commutator_eq_self (P.normalizer_eq_top ▸ le_top)
    (h.index_eq_card ▸ P.card_coprime_index)

/-- A normal cyclic Sylow subgroup is either central or contained in the commutator subgroup. -/
theorem le_center_or_le_commutator [P.Normal] : P ≤ Subgroup.center G ∨ P ≤ commutator G := by
  obtain ⟨K, hK⟩ := Subgroup.exists_left_complement'_of_coprime P.card_coprime_index
  refine (commutator_eq_bot_or_commutator_eq_self P hK).imp (fun h ↦ ?_) (fun h ↦ ?_)
  · replace h := sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) P.le_centralizer
    rwa [hK.sup_eq_top, top_le_iff, Subgroup.centralizer_eq_top_iff_subset] at h
  · rw [← h, commutator_def]
    exact Subgroup.commutator_mono le_top le_top

/-- A cyclic Sylow subgroup is either central in its normalizer or contained in the commutator
  subgroup. -/
theorem normalizer_le_centralizer_or_le_commutator :
    P.normalizer ≤ Subgroup.centralizer P ∨ P ≤ commutator G := by
  let Q : Sylow p P.normalizer := P.subtype P.le_normalizer
  have : Q.Normal := P.normal_in_normalizer
  have : IsCyclic Q :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe P.le_normalizer).symm.surjective
  refine (le_center_or_le_commutator Q).imp (fun h ↦ ?_) (fun h ↦ ?_)
  · rw [← SetLike.coe_subset_coe, ← Subgroup.centralizer_eq_top_iff_subset, eq_top_iff,
      ← Subgroup.map_subtype_le_map_subtype, ← MonoidHom.range_eq_map,
      P.normalizer.range_subtype] at h
    replace h := h.trans (Subgroup.map_centralizer_le_centralizer_image _ _)
    rwa [← Subgroup.coe_map, P.coe_subtype, Subgroup.map_subgroupOf_eq_of_le P.le_normalizer] at h
  · rw [P.coe_subtype, ← Subgroup.map_subtype_le_map_subtype,
      Subgroup.map_subgroupOf_eq_of_le P.le_normalizer, Subgroup.map_subtype_commutator] at h
    exact h.trans (Subgroup.commutator_mono le_top le_top)

include P in
/-- If `G` has a cyclic Sylow `p`-subgroup, then the cardinality and index of the commutator
  subgroup of `G` cannot both be divisible by `p`. -/
theorem not_dvd_card_commutator_or_not_dvd_index_commutator :
    ¬ p ∣ Nat.card (commutator G) ∨ ¬ p ∣ (commutator G).index := by
  refine (normalizer_le_centralizer_or_le_commutator P).imp ?_ ?_ <;>
      refine fun hP h ↦ P.not_dvd_index (h.trans ?_)
  · rw [(MonoidHom.ker_transferSylow_isComplement' P hP).index_eq_card]
    exact Subgroup.card_dvd_of_le (Abelianization.commutator_subset_ker _)
  · exact Subgroup.index_dvd_of_le hP

end Sylow

variable (G) in
/-- If `G` is a finite Z-group, then `commutator G` is a Hall subgroup of `G`. -/
theorem IsZGroup.coprime_commutator_index [Finite G] [IsZGroup G] :
    (Nat.card (commutator G)).Coprime (commutator G).index := by
  suffices h : ∀ p, p.Prime → (¬ p ∣ Nat.card (commutator G) ∨ ¬ p ∣ (commutator G).index) by
    contrapose! h
    exact Nat.Prime.not_coprime_iff_dvd.mp h
  intro p hp
  have := Fact.mk hp
  exact Sylow.not_dvd_card_commutator_or_not_dvd_index_commutator default

end Hall

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

/-- A finite group `G` is a Z-group if and only if `G` is isomorphic to a semidirect product of two
  cyclic subgroups of coprime order. -/
theorem isZGroup_iff_exists_mulEquiv [Finite G] :
    IsZGroup G ↔ ∃ (N H : Subgroup G) (φ : H →* MulAut N) (_ : G ≃* N ⋊[φ] H),
      IsCyclic H ∧ IsCyclic N ∧ (Nat.card N).Coprime (Nat.card H) := by
  refine ⟨fun hG ↦ ?_, ?_⟩
  · obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hG.coprime_commutator_index
    have h1 : Abelianization G ≃* H := hH.symm.QuotientMulEquiv
    refine ⟨commutator G, H, _, (SemidirectProduct.mulEquivSubgroup hH).symm,
      isCyclic_of_surjective _ h1.surjective, hG.isCyclic_commutator, ?_⟩
    exact Nat.card_congr h1.toEquiv ▸ hG.coprime_commutator_index
  · rintro ⟨N, H, φ, e, hH, hN, hHN⟩
    have : IsZGroup (N ⋊[φ] H) :=
      isZGroup_of_coprime SemidirectProduct.range_inl_eq_ker_rightHom.ge hHN
    exact IsZGroup.of_injective (f := e.toMonoidHom) e.injective

end Classification
