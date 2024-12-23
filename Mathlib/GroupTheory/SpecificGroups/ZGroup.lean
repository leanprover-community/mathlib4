/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.FieldTheory.Finite.Basic
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
* `IsZGroup.coprime_commutator_index`: if `G` is a finite Z-group, then `commutator G` is a Hall
  subgroup of `G` (`commutator G` has cardinality coprime to its index in `G`).
* `isZGroup_iff_mulEquiv`: a finite group `G` is a Z-group if and only if `G` is isomorphic to a
  semidirect product of two cyclic groups of coprime order.

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

-- check if this can be used to golf some proofs after #20107 is merged?
theorem _root_.Subgroup.map_subtype_commutator {G : Type*} [Group G] (H : Subgroup G) :
    (commutator H).map H.subtype = ⁅H, H⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, H.range_subtype]

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
    let _ : CommGroup (MulAut (⁅commutator H, commutator H⁆ : Subgroup H)) :=
      ⟨fun g h ↦ by
        let f := hH.mulAutMulEquiv
        rw [← f.apply_eq_iff_eq, map_mul, mul_comm, ← map_mul]⟩
    have key := Abelianization.commutator_subset_ker
      (Subgroup.normalizerMonoidHom ⁅commutator H, commutator H⁆)
    rwa [Subgroup.normalizerMonoidHom_ker, ⁅commutator H, commutator H⁆.normalizer_eq_top,
      ← Subgroup.map_subtype_le_map_subtype, Subgroup.map_subtype_commutator,
        Subgroup.subgroupOf, Subgroup.map_comap_eq_self] at key
    rw [Subgroup.range_subtype]
    exact le_top

end Commutator

section Hall

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

noncomputable def _root_.IsCyclic.toMonoidHom
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

theorem _root_.IsCyclic.toMonoidHom_apply
    {M G : Type*} [Monoid M] [Group G] [IsCyclic G] [MulDistribMulAction M G] (m : M) (g : G) :
    IsCyclic.toMonoidHom M G m • g = m • g := by
  conv_rhs => rw [← MulDistribMulAction.toMonoidHom_apply]
  rw [(MonoidHom.map_cyclic (MulDistribMulAction.toMonoidHom G m)).choose_spec g]
  exact tada3_coe_smul G _ g

theorem _root_.IsCyclic.commutator_eq_bot_or_commutator_eq [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} [IsCyclic P] [P.Normal] {K : Subgroup G} (h : K.IsComplement' P) :
    ⁅K, P.1⁆ = ⊥ ∨ ⁅K, P.1⁆ = P := by
  have hK : K ≤ P.normalizer := by
    rw [P.normalizer_eq_top]
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
    refine ZMod.eq_one_or_isUnit_sub_one hn (ϕ k) (P.card_coprime_index.symm.coprime_dvd_left ?_)
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

/-- If `G` is a finite Z-group, then `commutator G` is a Hall subgroup of `G`. -/
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

instance {G : Type*} [Group G] [IsCyclic G] : IsZGroup G :=
  ⟨inferInstance⟩

theorem isZGroup_iff_mulEquiv [Finite G] :
    IsZGroup G ↔ ∃ (m n : ℕ) (φ : Multiplicative (ZMod m) →* MulAut (Multiplicative (ZMod n)))
      (e : G ≃* SemidirectProduct _ _ φ), Nat.Coprime m n := by
  refine ⟨fun hG ↦ ?_, ?_⟩
  · obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime
      (IsZGroup.coprime_commutator_index G)
    exact ⟨_, _, _, (SemidirectProduct.mulEquivSubgroup hH).symm.trans
      (SemidirectProduct.congr' (zmodCyclicMulEquiv (IsZGroup.isCyclic_commutator G)).symm
        (hH.symm.QuotientMulEquiv.symm.trans
          (zmodCyclicMulEquiv IsZGroup.isCyclic_abelianization).symm)),
            (IsZGroup.coprime_commutator_index G).symm⟩
  · rintro ⟨m, n, φ, e, h⟩
    have : Finite (Multiplicative (ZMod n)) := by
      have key := e.symm.toMonoidHom.comp (SemidirectProduct.inl (φ := φ))
      refine Nat.finite_of_card_ne_zero ?_
      refine ne_zero_of_dvd_ne_zero ?_
        (Subgroup.card_dvd_of_injective (SemidirectProduct.inl (φ := φ))
          SemidirectProduct.inl_injective)
      rw [Nat.card_congr e.symm.toEquiv]
      exact Finite.card_pos.ne'
    rw [← m.card_zmod, ← n.card_zmod, Nat.coprime_comm] at h
    have key : IsZGroup (Multiplicative (ZMod n) ⋊[φ] Multiplicative (ZMod m)) :=
      IsZGroup.isZGroup_of_coprime SemidirectProduct.range_inl_eq_ker_rightHom.ge h
    exact IsZGroup.of_injective (f := e.toMonoidHom) e.injective
