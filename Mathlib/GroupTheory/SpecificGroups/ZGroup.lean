/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Module.ZMod
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

instance {G : Type*} [Group G] (H : Subgroup G) [IsCyclic H] : H.IsCommutative :=
  ⟨⟨IsCyclic.commGroup.mul_comm⟩⟩

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
  obtain ⟨ϕ⟩ := ((isNilpotent_of_finite_tfae (G := G)).out 0 4).mp hG
  let _ : CommGroup G :=
    ⟨fun g h ↦ by rw [← ϕ.symm.injective.eq_iff, map_mul, mul_comm, ← map_mul]⟩
  exact IsCyclic.of_exponent_eq_card (exponent_eq_card G)

end Nilpotent

section Hall

-- key: any element of K has order coprime to p
-- so the conjugation action on P satisfies k^(p-1) = 1
-- either k = 1 or k - 1 is indivisible by p (still an automorphism)
-- we have k -> zmod (actually maps to units, of course)
-- key is that if k has order indivisible by p, then k - 1 = 0 or is a unit

-- ok, so a monoid action on a cyclic group induces a canonical map to zmod

noncomputable def IsCyclic.toMonoidHom
    (M G : Type*) [Monoid M] [Group G] [IsCyclic G] [MulDistribMulAction M G] :
    M →* ZMod (Nat.card G) where
  toFun := fun m ↦ (MonoidHom.map_cyclic (MulDistribMulAction.toMonoidHom G m)).choose
  map_one' := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
    rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff, ← hg, ← zpow_eq_zpow_iff_modEq, zpow_one,
      ← (MonoidHom.map_cyclic (MulDistribMulAction.toMonoidHom G 1)).choose_spec,
      MulDistribMulAction.toMonoidHom_apply, one_smul]
  map_mul' := fun m n ↦ by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
    rw [← Int.cast_mul, ZMod.intCast_eq_intCast_iff, ← hg, ← zpow_eq_zpow_iff_modEq, zpow_mul',
      ← (MonoidHom.map_cyclic (MulDistribMulAction.toMonoidHom G m)).choose_spec,
      ← (MonoidHom.map_cyclic (MulDistribMulAction.toMonoidHom G n)).choose_spec,
      ← (MonoidHom.map_cyclic (MulDistribMulAction.toMonoidHom G (m * n))).choose_spec,
      MulDistribMulAction.toMonoidHom_apply, MulDistribMulAction.toMonoidHom_apply,
      MulDistribMulAction.toMonoidHom_apply, mul_smul]

-- instance (M A : Type*) [Monoid M] [AddMonoid A] [DistribMulAction M A] :
--     MulDistribMulAction M (Multiplicative A) where
--   smul m a := m • a.toAdd
--   one_smul a := one_smul M a.toAdd
--   mul_smul m n a := mul_smul m n a.toAdd
--   smul_mul m a b := smul_add m a.toAdd b.toAdd
--   smul_one m := smul_zero (A := A) m

-- instance (M A : Type*) [Monoid M] [Monoid A] [MulDistribMulAction M A] :
--     DistribMulAction M (Additive A) where
--   smul m a := m • a.toMul
--   one_smul a := one_smul M a.toMul
--   mul_smul m n a := mul_smul m n a.toMul
--   smul_add m a b := smul_mul' m a.toMul b.toMul
--   smul_zero m := smul_one (A := A) m

-- instance (M A : Type*) [Monoid M] [Monoid A] [DistribMulAction M (Additive A)] :
--     MulDistribMulAction M A where
--   smul m a := m • Additive.ofMul a
--   one_smul a := one_smul M (Additive.ofMul a)
--   mul_smul m n a := mul_smul m n (Additive.ofMul a)
--   smul_mul m a b := smul_add m (Additive.ofMul a) (Additive.ofMul b)
--   smul_one m := smul_zero (A := Additive A) m

-- instance (M A : Type*) [Monoid M] [AddMonoid A] [MulDistribMulAction M (Multiplicative A)] :
--     DistribMulAction M A where
--   smul m a := m • Multiplicative.ofAdd a
--   one_smul a := one_smul M (Multiplicative.ofAdd a)
--   mul_smul m n a := mul_smul m n (Multiplicative.ofAdd a)
--   smul_add m a b := smul_mul' m (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
--   smul_zero m := smul_one (A := Multiplicative A) m

-- noncomputable instance tada1 (G : Type*) [AddCommGroup G] :
--     DistribMulAction (ZMod (AddMonoid.exponent G)) G :=
--   (AddCommGroup.zmodModule AddMonoid.exponent_nsmul_eq_zero).toDistribMulAction

-- theorem tada2_coe_smul (G : Type*) [AddCommGroup G] (k : ℤ) (g : G) :
--     (k : ZMod (AddMonoid.exponent G)) • g = k • g := by

--   sorry

-- noncomputable instance tada2 (G : Type*) [CommGroup G] :
--     MulDistribMulAction (ZMod (Monoid.exponent G)) G :=
--   inferInstanceAs (MulDistribMulAction (ZMod (AddMonoid.exponent (Additive G))) G)

-- theorem tada2_coe_smul (G : Type*) [CommGroup G] (k : ℤ) (g : G) :
--     (k : ZMod (Monoid.exponent G)) • g = g ^ k := by
--   sorry

noncomputable instance tada3 (G : Type*) [Group G] [IsCyclic G] :
    MulDistribMulAction (ZMod (Nat.card G)) G where
  smul k g := g ^ k.

theorem tada3_coe_smul (G : Type*) [Group G] [IsCyclic G] (k : ℤ) (g : G) :
    (k : ZMod (Nat.card G)) • g = g ^ k := by
  sorry

theorem tada3_add_smul (G : Type*) [Group G] [IsCyclic G] (k m : ZMod (Nat.card G)) (g : G) :
    (k + m) • g = k • g * m • g := by
  rw [← k.coe_valMinAbs, ← m.coe_valMinAbs, ← Int.cast_add, tada3_coe_smul, tada3_coe_smul,
    tada3_coe_smul, zpow_add]

theorem tada3_sub_smul (G : Type*) [Group G] [IsCyclic G] (k m : ZMod (Nat.card G)) (g : G) :
    (k - m) • g = k • g * (m • g)⁻¹ := by
  rw [← k.coe_valMinAbs, ← m.coe_valMinAbs, ← Int.cast_sub, tada3_coe_smul, tada3_coe_smul,
    tada3_coe_smul, zpow_sub]

theorem tada3_zero_smul (G : Type*) [Group G] [IsCyclic G] (g : G) :
    (0 : ZMod (Nat.card G)) • g = 1 := by
  rw [← Int.cast_zero, tada3_coe_smul, zpow_zero]

theorem IsCyclic.toMonoidHom_apply
    {M G : Type*} [Monoid M] [Group G] [IsCyclic G] [MulDistribMulAction M G] (m : M) (g : G) :
    IsCyclic.toMonoidHom M G m • g = m • g := by
  conv_rhs => rw [← MulDistribMulAction.toMonoidHom_apply]
  rw [(MonoidHom.map_cyclic (MulDistribMulAction.toMonoidHom G m)).choose_spec g]
  exact tada3_coe_smul G _ g

theorem ZMod.eq_one_or_isUnit
    {n p k : ℕ} [Fact p.Prime] (hn : n = p ^ k) (a : ZMod n) (ha : (orderOf a).Coprime n) :
    a = 1 ∨ IsUnit (a - 1) := by
  sorry

theorem _root_.IsCyclic.commutator_eq_bot_or_commutator_eq [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} [IsCyclic P] [P.Normal] {K : Subgroup G} (h : K.IsComplement' P) :
    ⁅K, P.1⁆ = ⊥ ∨ ⁅K, P.1⁆ = P := by
  have hK : K ≤ P.normalizer := by
    rw [Subgroup.normalizer_eq_top.mpr inferInstance]
    exact le_top
  let _ := MulDistribMulAction.compHom P (P.normalizerMonoidHom.comp (Subgroup.inclusion hK))
  let ϕ := IsCyclic.toMonoidHom K P
  have h0 (k : K) (g : P) : ⁅k.1, g.1⁆ = ((k • g) * g⁻¹ : P) := rfl
  have h1 (k : K) (g : P) : ⁅k.1, g.1⁆ = (ϕ k • g * g⁻¹ : P) := by
    rw [h0, Subtype.coe_inj, mul_left_inj]
    exact (IsCyclic.toMonoidHom_apply k g).symm
  have h2 (k : K) (g : P) : ⁅k.1, g.1⁆ = ((ϕ k - 1) • g : P) := by
    rw [h1, Subtype.coe_inj, tada3_sub_smul, one_smul]
  replace h k : ϕ k - 1 = 0 ∨ IsUnit (ϕ k - 1) := by
    rw [sub_eq_zero]
    obtain ⟨n, hn⟩ := P.2.exists_card_eq
    refine ZMod.eq_one_or_isUnit hn (ϕ k) (P.card_coprime_index.symm.coprime_dvd_left ?_)
    exact h.index_eq_card ▸ (orderOf_map_dvd ϕ k).trans (orderOf_dvd_natCard k)
  rcases forall_or_exists_not (fun k : K ↦ ϕ k - 1 = 0) with hϕ | ⟨k, hk⟩
  · left
    rw [Subgroup.commutator_def, Subgroup.closure_eq_bot_iff, Set.subset_singleton_iff]
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro - k hk g hg rfl
    rw [← Subtype.coe_mk k hk, ← Subtype.coe_mk g hg, h2, hϕ, tada3_zero_smul, Subgroup.coe_one]
  · refine Or.inr (le_antisymm (K.commutator_le_right ↑P) fun g hg ↦ ?_)
    have key := (h k).resolve_left hk
    obtain ⟨u, hu⟩ := key
    suffices h : g = ⁅k.1, (u⁻¹.1 • ⟨g, hg⟩ : P).1⁆ by
      rw [h]
      exact Subgroup.commutator_mem_commutator k.2 (u⁻¹ • ⟨g, hg⟩ : P).2
    rw [h2, ← hu, smul_smul, Units.mul_inv, one_smul]

theorem Subgroup.map_centralizer_le_centralizer_map {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (H : Subgroup G) : H.centralizer.map f ≤ Subgroup.centralizer (H.map f) := by
  rintro - ⟨g, hg, rfl⟩ - ⟨h, hh, rfl⟩
  rw [← map_mul, ← map_mul, hg h hh]

theorem _root_.IsCyclic.normalizer_le_centralizer_or_le_commutator [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [IsCyclic P] :
    P.normalizer ≤ Subgroup.centralizer P ∨ P ≤ commutator G := by
  let Q : Sylow p P.normalizer := P.subtype P.le_normalizer
  have : Q.Normal := P.normal_in_normalizer
  obtain ⟨K, hK⟩ := Subgroup.exists_left_complement'_of_coprime Q.card_coprime_index
  have : IsCyclic Q :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe P.le_normalizer).symm.surjective
  refine (IsCyclic.commutator_eq_bot_or_commutator_eq hK).imp ?_ ?_ <;>
    refine fun h ↦ ?_
  · replace h := sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) Q.le_centralizer
    rw [hK.sup_eq_top, ← Subgroup.map_subtype_le_map_subtype, ← MonoidHom.range_eq_map,
      P.normalizer.range_subtype] at h
    replace h := h.trans (Subgroup.map_centralizer_le_centralizer_map P.normalizer.subtype Q)
    rwa [P.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr P.le_normalizer] at h
  · rw [← (Subgroup.map_injective P.normalizer.subtype_injective).eq_iff, Subgroup.map_commutator,
      P.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr P.le_normalizer] at h
    rw [← h, commutator_def]
    exact Subgroup.commutator_mono le_top le_top

theorem _root_.IsCyclic.not_dvd_card_commutator_or_not_dvd_index_commutator [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) [IsCyclic P] :
    ¬ p ∣ Nat.card (commutator G) ∨ ¬ p ∣ (commutator G).index := by
  refine (IsCyclic.normalizer_le_centralizer_or_le_commutator P).imp ?_ ?_ <;>
      refine fun hP h ↦ P.not_dvd_index (h.trans ?_)
  · rw [(MonoidHom.ker_transferSylow_isComplement' P hP).index_eq_card]
    exact Subgroup.card_dvd_of_le (Abelianization.commutator_subset_ker _)
  · exact Subgroup.index_dvd_of_le hP

variable (G)

/-- If `G` is a finite Z-group, then the commutator subgroup `G'` is a Hall subgroup of `G`. -/
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
