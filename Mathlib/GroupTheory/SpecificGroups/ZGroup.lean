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

## Main results

* `commutator G` is cyclic
* `commutator G` is a Hall subgroup (and thus has a complement by Schur-Zassenhaus)
* `abelianization G` is cyclic
* `G` is a semidirect product of two cyclic groups (probably should right this explicitly)

TODO: Show that if `G` is a Z-group with commutator subgroup `G'`, then `G = G' ⋊ G/G'` where `G'`
and `G/G'` are cyclic of coprime orders.

-/

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

instance [Finite G] [IsZGroup G] : IsCyclic (Abelianization G) :=
  let _ : IsZGroup (Abelianization G) := inferInstanceAs (IsZGroup (G ⧸ commutator G))
  inferInstance

end Nilpotent

section Hall

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

noncomputable def _root_.CommGroup.zmodModule
    {G : Type*} [CommGroup G] {n : ℕ} (h : ∀ (g : G), g ^ n = 1) :
    MulDistribMulAction (ZMod n) G :=
  let _ := (AddCommGroup.zmodModule (G := Additive G) h).toDistribMulAction
  { smul m a := m • Additive.ofMul a
    one_smul a := one_smul (ZMod n) (Additive.ofMul a)
    mul_smul m n a := mul_smul m n (Additive.ofMul a)
    smul_mul m a b := smul_add m (Additive.ofMul a) (Additive.ofMul b)
    smul_one m := smul_zero (A := Additive G) m }

theorem _root_.AddCommGroup.zmodModule.coe_smul
    {G : Type*} [AddCommGroup G] {n : ℕ} (h : ∀ (g : G), n • g = 0)
    (k : ℤ) (g : G) :
    let _ := AddCommGroup.zmodModule h
    (k : ZMod n) • g = k • g :=
  match n with
  | 0 => rfl
  | m + 1 => by
    have H := (k.mod_modEq (m + 1 : ℕ)).of_dvd
      (Int.natCast_dvd_natCast.mpr (addOrderOf_dvd_iff_nsmul_eq_zero.mpr (h g)))
    rwa [← zsmul_eq_zsmul_iff_modEq, ← ZMod.val_intCast, Nat.cast_smul_eq_nsmul] at H

theorem _root_.CommGroup.zmodModule.coe_smul
    {G : Type*} [CommGroup G] {n : ℕ} (h : ∀ (g : G), g ^ n = 1)
    (k : ℤ) (g : G) :
    let _ := CommGroup.zmodModule h
    (k : ZMod n) • g = g ^ k :=
  _root_.AddCommGroup.zmodModule.coe_smul (G := Additive G) h k g

theorem _root_.CommGroup.zmodModule.add_smul
    {G : Type*} [CommGroup G] {n : ℕ} (h : ∀ (g : G), g ^ n = 1)
    (k m : ZMod n) (g : G) :
    let _ := CommGroup.zmodModule h
    (k + m) • g = k • g * m • g :=
  let _ := AddCommGroup.zmodModule (G := Additive G) h
  _root_.add_smul (M := Additive G) k m g

theorem _root_.CommGroup.zmodModule.sub_smul
    {G : Type*} [CommGroup G] {n : ℕ} (h : ∀ (g : G), g ^ n = 1)
    (k m : ZMod n) (g : G) :
    let _ := CommGroup.zmodModule h
    (k - m) • g = k • g / m • g :=
  let _ := AddCommGroup.zmodModule (G := Additive G) h
  _root_.sub_smul (M := Additive G) k m g

theorem _root_.CommGroup.zmodModule.zero_smul
    {G : Type*} [CommGroup G] {n : ℕ} (h : ∀ (g : G), g ^ n = 1)
    (g : G) :
    let _ := CommGroup.zmodModule h
    (0 : ZMod n) • g = 1 :=
  let _ := AddCommGroup.zmodModule (G := Additive G) h
  _root_.zero_smul (M := Additive G) (ZMod n) g

noncomputable instance tada3 (G : Type*) [Group G] [IsCyclic G] :
    MulDistribMulAction (ZMod (Nat.card G)) G :=
  let _ : CommGroup G := IsCyclic.commGroup
  CommGroup.zmodModule (fun _ ↦ pow_card_eq_one')

theorem tada3_coe_smul (G : Type*) [Group G] [IsCyclic G] (k : ℤ) (g : G) :
    (k : ZMod (Nat.card G)) • g = g ^ k :=
  let _ : CommGroup G := IsCyclic.commGroup
  CommGroup.zmodModule.coe_smul _ k g

theorem tada3_add_smul (G : Type*) [Group G] [IsCyclic G] (k m : ZMod (Nat.card G)) (g : G) :
    (k + m) • g = k • g * m • g :=
  let _ : CommGroup G := IsCyclic.commGroup
  CommGroup.zmodModule.add_smul _ k m g

theorem tada3_sub_smul (G : Type*) [Group G] [IsCyclic G] (k m : ZMod (Nat.card G)) (g : G) :
    (k - m) • g = k • g / m • g :=
  let _ : CommGroup G := IsCyclic.commGroup
  CommGroup.zmodModule.sub_smul _ k m g

theorem tada3_zero_smul (G : Type*) [Group G] [IsCyclic G] (g : G) :
    (0 : ZMod (Nat.card G)) • g = 1 :=
  let _ : CommGroup G := IsCyclic.commGroup
  CommGroup.zmodModule.zero_smul _ g

theorem IsCyclic.toMonoidHom_apply
    {M G : Type*} [Monoid M] [Group G] [IsCyclic G] [MulDistribMulAction M G] (m : M) (g : G) :
    IsCyclic.toMonoidHom M G m • g = m • g := by
  conv_rhs => rw [← MulDistribMulAction.toMonoidHom_apply]
  rw [(MonoidHom.map_cyclic (MulDistribMulAction.toMonoidHom G m)).choose_spec g]
  exact tada3_coe_smul G _ g

theorem exists_pow_modEq_one (p m a : ℕ) :
    (1 + p * a) ^ (p ^ m) ≡ 1 [MOD p ^ m] := by
  induction' m with m hm
  · exact Nat.modEq_one
  · rw [Nat.ModEq.comm, add_comm, Nat.modEq_iff_dvd' (Nat.one_le_pow' _ _)] at hm
    obtain ⟨d, hd⟩ := hm
    rw [tsub_eq_iff_eq_add_of_le (Nat.one_le_pow' _ _), add_comm] at hd
    rw [pow_succ, pow_mul, hd, add_pow, Finset.sum_range_succ', pow_zero, one_mul, one_pow,
      one_mul, Nat.choose_zero_right, Nat.cast_one]
    refine Nat.ModEq.add_right 1 ?_
    rw [Nat.modEq_zero_iff_dvd]
    simp_rw [one_pow, mul_one, pow_succ', mul_assoc, ← Finset.mul_sum]
    refine mul_dvd_mul_left (p ^ m) (dvd_mul_of_dvd_right (Finset.dvd_sum fun k hk ↦ ?_) d)
    cases m
    · rw [pow_zero, pow_one, one_mul, add_comm, add_left_inj] at hd
      cases k <;> simp [← hd, mul_assoc, pow_succ']
    · cases k <;> simp [mul_assoc, pow_succ']

theorem ZMod.eq_one_or_isUnit
    {n p k : ℕ} [Fact p.Prime] (hn : n = p ^ k) (a : ZMod n) (ha : (orderOf a).Coprime n) :
    a = 1 ∨ IsUnit (a - 1) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact Or.inl (orderOf_eq_one_iff.mp ((orderOf a).coprime_zero_right.mp ha))
  rcases eq_or_ne a 0 with rfl | ha0
  · exact Or.inr (zero_sub (1 : ZMod n) ▸ isUnit_neg_one)
  have : NeZero n := ⟨hn0⟩
  rw [← orderOf_eq_one_iff, or_iff_not_imp_right]
  refine fun h ↦ ha.eq_one_of_dvd ?_
  rw [orderOf_dvd_iff_pow_eq_one]
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective a
  rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.eq_iff_modEq_nat, hn]
  replace ha0 : a ≠ 0 := by
    contrapose! ha0
    rw [ha0, Nat.cast_zero]
  rw [← Nat.one_le_iff_ne_zero] at ha0
  rw [← Nat.cast_one, ← Nat.cast_sub ha0, ZMod.isUnit_iff_coprime, hn] at h
  replace h : p ∣ a - 1 := by
    contrapose! h
    exact Nat.Prime.coprime_pow_of_not_dvd Fact.out h
  obtain ⟨b, hb⟩ := h
  rw [tsub_eq_iff_eq_add_of_le ha0, add_comm] at hb
  rw [hb]
  exact exists_pow_modEq_one p k b

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
    rw [h1, Subtype.coe_inj, tada3_sub_smul, one_smul, div_eq_mul_inv]
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
