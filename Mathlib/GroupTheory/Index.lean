/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finite.Card
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Quotient

#align_import group_theory.index from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Index of a Subgroup

In this file we define the index of a subgroup, and prove several divisibility properties.
Several theorems proved in this file are known as Lagrange's theorem.

## Main definitions

- `H.index` : the index of `H : Subgroup G` as a natural number,
  and returns 0 if the index is infinite.
- `H.relindex K` : the relative index of `H : Subgroup G` in `K : Subgroup G` as a natural number,
  and returns 0 if the relative index is infinite.

# Main results

- `card_mul_index` : `Nat.card H * H.index = Nat.card G`
- `index_mul_card` : `H.index * Fintype.card H = Fintype.card G`
- `index_dvd_card` : `H.index ∣ Fintype.card G`
- `relindex_mul_index` : If `H ≤ K`, then `H.relindex K * K.index = H.index`
- `index_dvd_of_le` : If `H ≤ K`, then `K.index ∣ H.index`
- `relindex_mul_relindex` : `relindex` is multiplicative in towers

-/


namespace Subgroup

open Cardinal

variable {G : Type*} [Group G] (H K L : Subgroup G)

/-- The index of a subgroup as a natural number, and returns 0 if the index is infinite. -/
@[to_additive "The index of a subgroup as a natural number,
and returns 0 if the index is infinite."]
noncomputable def index : ℕ :=
  Nat.card (G ⧸ H)
#align subgroup.index Subgroup.index
#align add_subgroup.index AddSubgroup.index

/-- The relative index of a subgroup as a natural number,
  and returns 0 if the relative index is infinite. -/
@[to_additive "The relative index of a subgroup as a natural number,
and returns 0 if the relative index is infinite."]
noncomputable def relindex : ℕ :=
  (H.subgroupOf K).index
#align subgroup.relindex Subgroup.relindex
#align add_subgroup.relindex AddSubgroup.relindex

@[to_additive]
theorem index_comap_of_surjective {G' : Type*} [Group G'] {f : G' →* G}
    (hf : Function.Surjective f) : (H.comap f).index = H.index := by
  letI := QuotientGroup.leftRel H
  letI := QuotientGroup.leftRel (H.comap f)
  have key : ∀ x y : G', Setoid.r x y ↔ Setoid.r (f x) (f y) := by
    simp only [QuotientGroup.leftRel_apply]
    exact fun x y => iff_of_eq (congr_arg (· ∈ H) (by rw [f.map_mul, f.map_inv]))
  refine Cardinal.toNat_congr (Equiv.ofBijective (Quotient.map' f fun x y => (key x y).mp) ⟨?_, ?_⟩)
  · simp_rw [← Quotient.eq''] at key
    refine Quotient.ind' fun x => ?_
    refine Quotient.ind' fun y => ?_
    exact (key x y).mpr
  · refine Quotient.ind' fun x => ?_
    obtain ⟨y, hy⟩ := hf x
    exact ⟨y, (Quotient.map'_mk'' f _ y).trans (congr_arg Quotient.mk'' hy)⟩
#align subgroup.index_comap_of_surjective Subgroup.index_comap_of_surjective
#align add_subgroup.index_comap_of_surjective AddSubgroup.index_comap_of_surjective

@[to_additive]
theorem index_comap {G' : Type*} [Group G'] (f : G' →* G) :
    (H.comap f).index = H.relindex f.range :=
  Eq.trans (congr_arg index (by rfl))
    ((H.subgroupOf f.range).index_comap_of_surjective f.rangeRestrict_surjective)
#align subgroup.index_comap Subgroup.index_comap
#align add_subgroup.index_comap AddSubgroup.index_comap

@[to_additive]
theorem relindex_comap {G' : Type*} [Group G'] (f : G' →* G) (K : Subgroup G') :
    relindex (comap f H) K = relindex H (map f K) := by
  rw [relindex, subgroupOf, comap_comap, index_comap, ← f.map_range, K.subtype_range]
#align subgroup.relindex_comap Subgroup.relindex_comap
#align add_subgroup.relindex_comap AddSubgroup.relindex_comap

variable {H K L}

@[to_additive relindex_mul_index]
theorem relindex_mul_index (h : H ≤ K) : H.relindex K * K.index = H.index :=
  ((mul_comm _ _).trans (Cardinal.toNat_mul _ _).symm).trans
    (congr_arg Cardinal.toNat (Equiv.cardinal_eq (quotientEquivProdOfLE h))).symm
#align subgroup.relindex_mul_index Subgroup.relindex_mul_index
#align add_subgroup.relindex_mul_index AddSubgroup.relindex_mul_index

@[to_additive]
theorem index_dvd_of_le (h : H ≤ K) : K.index ∣ H.index :=
  dvd_of_mul_left_eq (H.relindex K) (relindex_mul_index h)
#align subgroup.index_dvd_of_le Subgroup.index_dvd_of_le
#align add_subgroup.index_dvd_of_le AddSubgroup.index_dvd_of_le

@[to_additive]
theorem relindex_dvd_index_of_le (h : H ≤ K) : H.relindex K ∣ H.index :=
  dvd_of_mul_right_eq K.index (relindex_mul_index h)
#align subgroup.relindex_dvd_index_of_le Subgroup.relindex_dvd_index_of_le
#align add_subgroup.relindex_dvd_index_of_le AddSubgroup.relindex_dvd_index_of_le

@[to_additive]
theorem relindex_subgroupOf (hKL : K ≤ L) :
    (H.subgroupOf L).relindex (K.subgroupOf L) = H.relindex K :=
  ((index_comap (H.subgroupOf L) (inclusion hKL)).trans (congr_arg _ (inclusion_range hKL))).symm
#align subgroup.relindex_subgroup_of Subgroup.relindex_subgroupOf
#align add_subgroup.relindex_add_subgroup_of AddSubgroup.relindex_addSubgroupOf

variable (H K L)

@[to_additive relindex_mul_relindex]
theorem relindex_mul_relindex (hHK : H ≤ K) (hKL : K ≤ L) :
    H.relindex K * K.relindex L = H.relindex L := by
  rw [← relindex_subgroupOf hKL]
  exact relindex_mul_index fun x hx => hHK hx
#align subgroup.relindex_mul_relindex Subgroup.relindex_mul_relindex
#align add_subgroup.relindex_mul_relindex AddSubgroup.relindex_mul_relindex

@[to_additive]
theorem inf_relindex_right : (H ⊓ K).relindex K = H.relindex K := by
  rw [relindex, relindex, inf_subgroupOf_right]
#align subgroup.inf_relindex_right Subgroup.inf_relindex_right
#align add_subgroup.inf_relindex_right AddSubgroup.inf_relindex_right

@[to_additive]
theorem inf_relindex_left : (H ⊓ K).relindex H = K.relindex H := by
  rw [inf_comm, inf_relindex_right]
#align subgroup.inf_relindex_left Subgroup.inf_relindex_left
#align add_subgroup.inf_relindex_left AddSubgroup.inf_relindex_left

@[to_additive relindex_inf_mul_relindex]
theorem relindex_inf_mul_relindex : H.relindex (K ⊓ L) * K.relindex L = (H ⊓ K).relindex L := by
  rw [← inf_relindex_right H (K ⊓ L), ← inf_relindex_right K L, ← inf_relindex_right (H ⊓ K) L,
    inf_assoc, relindex_mul_relindex (H ⊓ (K ⊓ L)) (K ⊓ L) L inf_le_right inf_le_right]
#align subgroup.relindex_inf_mul_relindex Subgroup.relindex_inf_mul_relindex
#align add_subgroup.relindex_inf_mul_relindex AddSubgroup.relindex_inf_mul_relindex

@[to_additive (attr := simp)]
theorem relindex_sup_right [K.Normal] : K.relindex (H ⊔ K) = K.relindex H :=
  Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient H K).toEquiv.symm
#align subgroup.relindex_sup_right Subgroup.relindex_sup_right
#align add_subgroup.relindex_sup_right AddSubgroup.relindex_sup_right

@[to_additive (attr := simp)]
theorem relindex_sup_left [K.Normal] : K.relindex (K ⊔ H) = K.relindex H := by
  rw [sup_comm, relindex_sup_right]
#align subgroup.relindex_sup_left Subgroup.relindex_sup_left
#align add_subgroup.relindex_sup_left AddSubgroup.relindex_sup_left

@[to_additive]
theorem relindex_dvd_index_of_normal [H.Normal] : H.relindex K ∣ H.index :=
  relindex_sup_right K H ▸ relindex_dvd_index_of_le le_sup_right
#align subgroup.relindex_dvd_index_of_normal Subgroup.relindex_dvd_index_of_normal
#align add_subgroup.relindex_dvd_index_of_normal AddSubgroup.relindex_dvd_index_of_normal

variable {H K}

@[to_additive]
theorem relindex_dvd_of_le_left (hHK : H ≤ K) : K.relindex L ∣ H.relindex L :=
  inf_of_le_left hHK ▸ dvd_of_mul_left_eq _ (relindex_inf_mul_relindex _ _ _)
#align subgroup.relindex_dvd_of_le_left Subgroup.relindex_dvd_of_le_left
#align add_subgroup.relindex_dvd_of_le_left AddSubgroup.relindex_dvd_of_le_left

/-- A subgroup has index two if and only if there exists `a` such that for all `b`, exactly one
of `b * a` and `b` belong to `H`. -/
@[to_additive "An additive subgroup has index two if and only if there exists `a` such that
for all `b`, exactly one of `b + a` and `b` belong to `H`."]
theorem index_eq_two_iff : H.index = 2 ↔ ∃ a, ∀ b, Xor' (b * a ∈ H) (b ∈ H) := by
  simp only [index, Nat.card_eq_two_iff' ((1 : G) : G ⧸ H), ExistsUnique, inv_mem_iff,
    QuotientGroup.exists_mk, QuotientGroup.forall_mk, Ne, QuotientGroup.eq, mul_one,
    xor_iff_iff_not]
  refine exists_congr fun a =>
    ⟨fun ha b => ⟨fun hba hb => ?_, fun hb => ?_⟩, fun ha => ⟨?_, fun b hb => ?_⟩⟩
  · exact ha.1 ((mul_mem_cancel_left hb).1 hba)
  · exact inv_inv b ▸ ha.2 _ (mt (inv_mem_iff (x := b)).1 hb)
  · rw [← inv_mem_iff (x := a), ← ha, inv_mul_self]
    exact one_mem _
  · rwa [ha, inv_mem_iff (x := b)]
#align subgroup.index_eq_two_iff Subgroup.index_eq_two_iff
#align add_subgroup.index_eq_two_iff AddSubgroup.index_eq_two_iff

@[to_additive]
theorem mul_mem_iff_of_index_two (h : H.index = 2) {a b : G} : a * b ∈ H ↔ (a ∈ H ↔ b ∈ H) := by
  by_cases ha : a ∈ H; · simp only [ha, true_iff_iff, mul_mem_cancel_left ha]
  by_cases hb : b ∈ H; · simp only [hb, iff_true_iff, mul_mem_cancel_right hb]
  simp only [ha, hb, iff_self_iff, iff_true_iff]
  rcases index_eq_two_iff.1 h with ⟨c, hc⟩
  refine (hc _).or.resolve_left ?_
  rwa [mul_assoc, mul_mem_cancel_right ((hc _).or.resolve_right hb)]
#align subgroup.mul_mem_iff_of_index_two Subgroup.mul_mem_iff_of_index_two
#align add_subgroup.add_mem_iff_of_index_two AddSubgroup.add_mem_iff_of_index_two

@[to_additive]
theorem mul_self_mem_of_index_two (h : H.index = 2) (a : G) : a * a ∈ H := by
  rw [mul_mem_iff_of_index_two h]
#align subgroup.mul_self_mem_of_index_two Subgroup.mul_self_mem_of_index_two
#align add_subgroup.add_self_mem_of_index_two AddSubgroup.add_self_mem_of_index_two

@[to_additive two_smul_mem_of_index_two]
theorem sq_mem_of_index_two (h : H.index = 2) (a : G) : a ^ 2 ∈ H :=
  (pow_two a).symm ▸ mul_self_mem_of_index_two h a
#align subgroup.sq_mem_of_index_two Subgroup.sq_mem_of_index_two
#align add_subgroup.two_smul_mem_of_index_two AddSubgroup.two_smul_mem_of_index_two

variable (H K)

-- Porting note: had to replace `Cardinal.toNat_eq_one_iff_unique` with `Nat.card_eq_one_iff_unique`
@[to_additive (attr := simp)]
theorem index_top : (⊤ : Subgroup G).index = 1 :=
  Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩
#align subgroup.index_top Subgroup.index_top
#align add_subgroup.index_top AddSubgroup.index_top

@[to_additive (attr := simp)]
theorem index_bot : (⊥ : Subgroup G).index = Nat.card G :=
  Cardinal.toNat_congr QuotientGroup.quotientBot.toEquiv
#align subgroup.index_bot Subgroup.index_bot
#align add_subgroup.index_bot AddSubgroup.index_bot

@[to_additive]
theorem index_bot_eq_card [Fintype G] : (⊥ : Subgroup G).index = Fintype.card G :=
  index_bot.trans Nat.card_eq_fintype_card
#align subgroup.index_bot_eq_card Subgroup.index_bot_eq_card
#align add_subgroup.index_bot_eq_card AddSubgroup.index_bot_eq_card

@[to_additive (attr := simp)]
theorem relindex_top_left : (⊤ : Subgroup G).relindex H = 1 :=
  index_top
#align subgroup.relindex_top_left Subgroup.relindex_top_left
#align add_subgroup.relindex_top_left AddSubgroup.relindex_top_left

@[to_additive (attr := simp)]
theorem relindex_top_right : H.relindex ⊤ = H.index := by
  rw [← relindex_mul_index (show H ≤ ⊤ from le_top), index_top, mul_one]
#align subgroup.relindex_top_right Subgroup.relindex_top_right
#align add_subgroup.relindex_top_right AddSubgroup.relindex_top_right

@[to_additive (attr := simp)]
theorem relindex_bot_left : (⊥ : Subgroup G).relindex H = Nat.card H := by
  rw [relindex, bot_subgroupOf, index_bot]
#align subgroup.relindex_bot_left Subgroup.relindex_bot_left
#align add_subgroup.relindex_bot_left AddSubgroup.relindex_bot_left

@[to_additive]
theorem relindex_bot_left_eq_card [Fintype H] : (⊥ : Subgroup G).relindex H = Fintype.card H :=
  H.relindex_bot_left.trans Nat.card_eq_fintype_card
#align subgroup.relindex_bot_left_eq_card Subgroup.relindex_bot_left_eq_card
#align add_subgroup.relindex_bot_left_eq_card AddSubgroup.relindex_bot_left_eq_card

@[to_additive (attr := simp)]
theorem relindex_bot_right : H.relindex ⊥ = 1 := by rw [relindex, subgroupOf_bot_eq_top, index_top]
#align subgroup.relindex_bot_right Subgroup.relindex_bot_right
#align add_subgroup.relindex_bot_right AddSubgroup.relindex_bot_right

@[to_additive (attr := simp)]
theorem relindex_self : H.relindex H = 1 := by rw [relindex, subgroupOf_self, index_top]
#align subgroup.relindex_self Subgroup.relindex_self
#align add_subgroup.relindex_self AddSubgroup.relindex_self

@[to_additive]
theorem index_ker {H} [Group H] (f : G →* H) : f.ker.index = Nat.card (Set.range f) := by
  rw [← MonoidHom.comap_bot, index_comap, relindex_bot_left]
  rfl
#align subgroup.index_ker Subgroup.index_ker
#align add_subgroup.index_ker AddSubgroup.index_ker

@[to_additive]
theorem relindex_ker {H} [Group H] (f : G →* H) (K : Subgroup G) :
    f.ker.relindex K = Nat.card (f '' K) := by
  rw [← MonoidHom.comap_bot, relindex_comap, relindex_bot_left]
  rfl
#align subgroup.relindex_ker Subgroup.relindex_ker
#align add_subgroup.relindex_ker AddSubgroup.relindex_ker

@[to_additive (attr := simp) card_mul_index]
theorem card_mul_index : Nat.card H * H.index = Nat.card G := by
  rw [← relindex_bot_left, ← index_bot]
  exact relindex_mul_index bot_le
#align subgroup.card_mul_index Subgroup.card_mul_index
#align add_subgroup.card_mul_index AddSubgroup.card_mul_index

@[to_additive]
theorem nat_card_dvd_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) : Nat.card G ∣ Nat.card H := by
  rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  exact Dvd.intro f.range.index f.range.card_mul_index
#align subgroup.nat_card_dvd_of_injective Subgroup.nat_card_dvd_of_injective
#align add_subgroup.nat_card_dvd_of_injective AddSubgroup.nat_card_dvd_of_injective

@[to_additive]
theorem nat_card_dvd_of_le (hHK : H ≤ K) : Nat.card H ∣ Nat.card K :=
  nat_card_dvd_of_injective (inclusion hHK) (inclusion_injective hHK)
#align subgroup.nat_card_dvd_of_le Subgroup.nat_card_dvd_of_le
#align add_subgroup.nat_card_dvd_of_le AddSubgroup.nat_card_dvd_of_le

@[to_additive]
theorem nat_card_dvd_of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) : Nat.card H ∣ Nat.card G := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  exact Dvd.intro_left (Nat.card f.ker) f.ker.card_mul_index
#align subgroup.nat_card_dvd_of_surjective Subgroup.nat_card_dvd_of_surjective
#align add_subgroup.nat_card_dvd_of_surjective AddSubgroup.nat_card_dvd_of_surjective

@[to_additive]
theorem card_dvd_of_surjective {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (f : G →* H) (hf : Function.Surjective f) : Fintype.card H ∣ Fintype.card G := by
  simp only [← Nat.card_eq_fintype_card, nat_card_dvd_of_surjective f hf]
#align subgroup.card_dvd_of_surjective Subgroup.card_dvd_of_surjective
#align add_subgroup.card_dvd_of_surjective AddSubgroup.card_dvd_of_surjective

@[to_additive]
theorem index_map {G' : Type*} [Group G'] (f : G →* G') :
    (H.map f).index = (H ⊔ f.ker).index * f.range.index := by
  rw [← comap_map_eq, index_comap, relindex_mul_index (H.map_le_range f)]
#align subgroup.index_map Subgroup.index_map
#align add_subgroup.index_map AddSubgroup.index_map

@[to_additive]
theorem index_map_dvd {G' : Type*} [Group G'] {f : G →* G'} (hf : Function.Surjective f) :
    (H.map f).index ∣ H.index := by
  rw [index_map, f.range_top_of_surjective hf, index_top, mul_one]
  exact index_dvd_of_le le_sup_left
#align subgroup.index_map_dvd Subgroup.index_map_dvd
#align add_subgroup.index_map_dvd AddSubgroup.index_map_dvd

@[to_additive]
theorem dvd_index_map {G' : Type*} [Group G'] {f : G →* G'} (hf : f.ker ≤ H) :
    H.index ∣ (H.map f).index := by
  rw [index_map, sup_of_le_left hf]
  apply dvd_mul_right
#align subgroup.dvd_index_map Subgroup.dvd_index_map
#align add_subgroup.dvd_index_map AddSubgroup.dvd_index_map

@[to_additive]
theorem index_map_eq {G' : Type*} [Group G'] {f : G →* G'} (hf1 : Function.Surjective f)
    (hf2 : f.ker ≤ H) : (H.map f).index = H.index :=
  Nat.dvd_antisymm (H.index_map_dvd hf1) (H.dvd_index_map hf2)
#align subgroup.index_map_eq Subgroup.index_map_eq
#align add_subgroup.index_map_eq AddSubgroup.index_map_eq

@[to_additive]
theorem index_eq_card [Fintype (G ⧸ H)] : H.index = Fintype.card (G ⧸ H) :=
  Nat.card_eq_fintype_card
#align subgroup.index_eq_card Subgroup.index_eq_card
#align add_subgroup.index_eq_card AddSubgroup.index_eq_card

@[to_additive index_mul_card]
theorem index_mul_card [Fintype G] [hH : Fintype H] :
    H.index * Fintype.card H = Fintype.card G := by
  rw [← relindex_bot_left_eq_card, ← index_bot_eq_card, mul_comm];
    exact relindex_mul_index bot_le
#align subgroup.index_mul_card Subgroup.index_mul_card
#align add_subgroup.index_mul_card AddSubgroup.index_mul_card

@[to_additive]
theorem index_dvd_card [Fintype G] : H.index ∣ Fintype.card G := by
  classical exact ⟨Fintype.card H, H.index_mul_card.symm⟩
#align subgroup.index_dvd_card Subgroup.index_dvd_card
#align add_subgroup.index_dvd_card AddSubgroup.index_dvd_card

variable {H K L}

@[to_additive]
theorem relindex_eq_zero_of_le_left (hHK : H ≤ K) (hKL : K.relindex L = 0) : H.relindex L = 0 :=
  eq_zero_of_zero_dvd (hKL ▸ relindex_dvd_of_le_left L hHK)
#align subgroup.relindex_eq_zero_of_le_left Subgroup.relindex_eq_zero_of_le_left
#align add_subgroup.relindex_eq_zero_of_le_left AddSubgroup.relindex_eq_zero_of_le_left

@[to_additive]
theorem relindex_eq_zero_of_le_right (hKL : K ≤ L) (hHK : H.relindex K = 0) : H.relindex L = 0 :=
  Finite.card_eq_zero_of_embedding (quotientSubgroupOfEmbeddingOfLE H hKL) hHK
#align subgroup.relindex_eq_zero_of_le_right Subgroup.relindex_eq_zero_of_le_right
#align add_subgroup.relindex_eq_zero_of_le_right AddSubgroup.relindex_eq_zero_of_le_right

@[to_additive]
theorem index_eq_zero_of_relindex_eq_zero (h : H.relindex K = 0) : H.index = 0 :=
  H.relindex_top_right.symm.trans (relindex_eq_zero_of_le_right le_top h)
#align subgroup.index_eq_zero_of_relindex_eq_zero Subgroup.index_eq_zero_of_relindex_eq_zero
#align add_subgroup.index_eq_zero_of_relindex_eq_zero AddSubgroup.index_eq_zero_of_relindex_eq_zero

@[to_additive]
theorem relindex_le_of_le_left (hHK : H ≤ K) (hHL : H.relindex L ≠ 0) :
    K.relindex L ≤ H.relindex L :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hHL) (relindex_dvd_of_le_left L hHK)
#align subgroup.relindex_le_of_le_left Subgroup.relindex_le_of_le_left
#align add_subgroup.relindex_le_of_le_left AddSubgroup.relindex_le_of_le_left

@[to_additive]
theorem relindex_le_of_le_right (hKL : K ≤ L) (hHL : H.relindex L ≠ 0) :
    H.relindex K ≤ H.relindex L :=
  Finite.card_le_of_embedding' (quotientSubgroupOfEmbeddingOfLE H hKL) fun h => (hHL h).elim
#align subgroup.relindex_le_of_le_right Subgroup.relindex_le_of_le_right
#align add_subgroup.relindex_le_of_le_right AddSubgroup.relindex_le_of_le_right

@[to_additive]
theorem relindex_ne_zero_trans (hHK : H.relindex K ≠ 0) (hKL : K.relindex L ≠ 0) :
    H.relindex L ≠ 0 := fun h =>
  mul_ne_zero (mt (relindex_eq_zero_of_le_right (show K ⊓ L ≤ K from inf_le_left)) hHK) hKL
    ((relindex_inf_mul_relindex H K L).trans (relindex_eq_zero_of_le_left inf_le_left h))
#align subgroup.relindex_ne_zero_trans Subgroup.relindex_ne_zero_trans
#align add_subgroup.relindex_ne_zero_trans AddSubgroup.relindex_ne_zero_trans

@[to_additive]
theorem relindex_inf_ne_zero (hH : H.relindex L ≠ 0) (hK : K.relindex L ≠ 0) :
    (H ⊓ K).relindex L ≠ 0 := by
  replace hH : H.relindex (K ⊓ L) ≠ 0 := mt (relindex_eq_zero_of_le_right inf_le_right) hH
  rw [← inf_relindex_right] at hH hK ⊢
  rw [inf_assoc]
  exact relindex_ne_zero_trans hH hK
#align subgroup.relindex_inf_ne_zero Subgroup.relindex_inf_ne_zero
#align add_subgroup.relindex_inf_ne_zero AddSubgroup.relindex_inf_ne_zero

@[to_additive]
theorem index_inf_ne_zero (hH : H.index ≠ 0) (hK : K.index ≠ 0) : (H ⊓ K).index ≠ 0 := by
  rw [← relindex_top_right] at hH hK ⊢
  exact relindex_inf_ne_zero hH hK
#align subgroup.index_inf_ne_zero Subgroup.index_inf_ne_zero
#align add_subgroup.index_inf_ne_zero AddSubgroup.index_inf_ne_zero

@[to_additive]
theorem relindex_inf_le : (H ⊓ K).relindex L ≤ H.relindex L * K.relindex L := by
  by_cases h : H.relindex L = 0
  · exact (le_of_eq (relindex_eq_zero_of_le_left inf_le_left h)).trans (zero_le _)
  rw [← inf_relindex_right, inf_assoc, ← relindex_mul_relindex _ _ L inf_le_right inf_le_right,
    inf_relindex_right, inf_relindex_right]
  exact mul_le_mul_right' (relindex_le_of_le_right inf_le_right h) (K.relindex L)
#align subgroup.relindex_inf_le Subgroup.relindex_inf_le
#align add_subgroup.relindex_inf_le AddSubgroup.relindex_inf_le

@[to_additive]
theorem index_inf_le : (H ⊓ K).index ≤ H.index * K.index := by
  simp_rw [← relindex_top_right, relindex_inf_le]
#align subgroup.index_inf_le Subgroup.index_inf_le
#align add_subgroup.index_inf_le AddSubgroup.index_inf_le

@[to_additive]
theorem relindex_iInf_ne_zero {ι : Type*} [_hι : Finite ι] {f : ι → Subgroup G}
    (hf : ∀ i, (f i).relindex L ≠ 0) : (⨅ i, f i).relindex L ≠ 0 :=
  haveI := Fintype.ofFinite ι
  (Finset.prod_ne_zero_iff.mpr fun i _hi => hf i) ∘
    Nat.card_pi.symm.trans ∘
      Finite.card_eq_zero_of_embedding (quotientiInfSubgroupOfEmbedding f L)
#align subgroup.relindex_infi_ne_zero Subgroup.relindex_iInf_ne_zero
#align add_subgroup.relindex_infi_ne_zero AddSubgroup.relindex_iInf_ne_zero

@[to_additive]
theorem relindex_iInf_le {ι : Type*} [Fintype ι] (f : ι → Subgroup G) :
    (⨅ i, f i).relindex L ≤ ∏ i, (f i).relindex L :=
  le_of_le_of_eq
    (Finite.card_le_of_embedding' (quotientiInfSubgroupOfEmbedding f L) fun h =>
      let ⟨i, _hi, h⟩ := Finset.prod_eq_zero_iff.mp (Nat.card_pi.symm.trans h)
      relindex_eq_zero_of_le_left (iInf_le f i) h)
    Nat.card_pi
#align subgroup.relindex_infi_le Subgroup.relindex_iInf_le
#align add_subgroup.relindex_infi_le AddSubgroup.relindex_iInf_le

@[to_additive]
theorem index_iInf_ne_zero {ι : Type*} [Finite ι] {f : ι → Subgroup G}
    (hf : ∀ i, (f i).index ≠ 0) : (⨅ i, f i).index ≠ 0 := by
  simp_rw [← relindex_top_right] at hf ⊢
  exact relindex_iInf_ne_zero hf
#align subgroup.index_infi_ne_zero Subgroup.index_iInf_ne_zero
#align add_subgroup.index_infi_ne_zero AddSubgroup.index_iInf_ne_zero

@[to_additive]
theorem index_iInf_le {ι : Type*} [Fintype ι] (f : ι → Subgroup G) :
    (⨅ i, f i).index ≤ ∏ i, (f i).index := by simp_rw [← relindex_top_right, relindex_iInf_le]
#align subgroup.index_infi_le Subgroup.index_iInf_le
#align add_subgroup.index_infi_le AddSubgroup.index_iInf_le

-- Porting note: had to replace `Cardinal.toNat_eq_one_iff_unique` with `Nat.card_eq_one_iff_unique`
@[to_additive (attr := simp) index_eq_one]
theorem index_eq_one : H.index = 1 ↔ H = ⊤ :=
  ⟨fun h =>
    QuotientGroup.subgroup_eq_top_of_subsingleton H (Nat.card_eq_one_iff_unique.mp h).1,
    fun h => (congr_arg index h).trans index_top⟩
#align subgroup.index_eq_one Subgroup.index_eq_one
#align add_subgroup.index_eq_one AddSubgroup.index_eq_one

@[to_additive (attr := simp) relindex_eq_one]
theorem relindex_eq_one : H.relindex K = 1 ↔ K ≤ H :=
  index_eq_one.trans subgroupOf_eq_top
#align subgroup.relindex_eq_one Subgroup.relindex_eq_one
#align add_subgroup.relindex_eq_one AddSubgroup.relindex_eq_one

@[to_additive (attr := simp) card_eq_one]
theorem card_eq_one : Nat.card H = 1 ↔ H = ⊥ :=
  H.relindex_bot_left ▸ relindex_eq_one.trans le_bot_iff
#align subgroup.card_eq_one Subgroup.card_eq_one
#align add_subgroup.card_eq_one AddSubgroup.card_eq_one

@[to_additive]
theorem index_ne_zero_of_finite [hH : Finite (G ⧸ H)] : H.index ≠ 0 := by
  cases nonempty_fintype (G ⧸ H)
  rw [index_eq_card]
  exact Fintype.card_ne_zero
#align subgroup.index_ne_zero_of_finite Subgroup.index_ne_zero_of_finite
#align add_subgroup.index_ne_zero_of_finite AddSubgroup.index_ne_zero_of_finite

-- Porting note: changed due to error with `Cardinal.toNat_apply_of_aleph0_le`
/-- Finite index implies finite quotient. -/
@[to_additive "Finite index implies finite quotient."]
noncomputable def fintypeOfIndexNeZero (hH : H.index ≠ 0) : Fintype (G ⧸ H) :=
  @Fintype.ofFinite _ (Nat.finite_of_card_ne_zero hH)
#align subgroup.fintype_of_index_ne_zero Subgroup.fintypeOfIndexNeZero
#align add_subgroup.fintype_of_index_ne_zero AddSubgroup.fintypeOfIndexNeZero

@[to_additive one_lt_index_of_ne_top]
theorem one_lt_index_of_ne_top [Finite (G ⧸ H)] (hH : H ≠ ⊤) : 1 < H.index :=
  Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨index_ne_zero_of_finite, mt index_eq_one.mp hH⟩
#align subgroup.one_lt_index_of_ne_top Subgroup.one_lt_index_of_ne_top
#align add_subgroup.one_lt_index_of_ne_top AddSubgroup.one_lt_index_of_ne_top

section FiniteIndex

variable (H K)

/-- Typeclass for finite index subgroups. -/
class FiniteIndex : Prop where
  /-- The subgroup has finite index -/
  finiteIndex : H.index ≠ 0
#align subgroup.finite_index Subgroup.FiniteIndex

/-- Typeclass for finite index subgroups. -/
class _root_.AddSubgroup.FiniteIndex {G : Type*} [AddGroup G] (H : AddSubgroup G) : Prop where
  /-- The additive subgroup has finite index -/
  finiteIndex : H.index ≠ 0
#align add_subgroup.finite_index AddSubgroup.FiniteIndex

/-- A finite index subgroup has finite quotient. -/
@[to_additive "A finite index subgroup has finite quotient"]
noncomputable def fintypeQuotientOfFiniteIndex [FiniteIndex H] : Fintype (G ⧸ H) :=
  fintypeOfIndexNeZero FiniteIndex.finiteIndex
#align subgroup.fintype_quotient_of_finite_index Subgroup.fintypeQuotientOfFiniteIndex
#align add_subgroup.fintype_quotient_of_finite_index AddSubgroup.fintypeQuotientOfFiniteIndex

@[to_additive]
instance finite_quotient_of_finiteIndex [FiniteIndex H] : Finite (G ⧸ H) :=
  H.fintypeQuotientOfFiniteIndex.finite
#align subgroup.finite_quotient_of_finite_index Subgroup.finite_quotient_of_finiteIndex
#align add_subgroup.finite_quotient_of_finite_index AddSubgroup.finite_quotient_of_finiteIndex

@[to_additive]
theorem finiteIndex_of_finite_quotient [Finite (G ⧸ H)] : FiniteIndex H :=
  ⟨index_ne_zero_of_finite⟩
#align subgroup.finite_index_of_finite_quotient Subgroup.finiteIndex_of_finite_quotient
#align add_subgroup.finite_index_of_finite_quotient AddSubgroup.finiteIndex_of_finite_quotient

-- Porting note: had to manually provide finite instance for quotient when it should be automatic
@[to_additive]
instance (priority := 100) finiteIndex_of_finite [Finite G] : FiniteIndex H :=
  @finiteIndex_of_finite_quotient _ _ H (Quotient.finite _)
#align subgroup.finite_index_of_finite Subgroup.finiteIndex_of_finite
#align add_subgroup.finite_index_of_finite AddSubgroup.finiteIndex_of_finite

@[to_additive]
instance : FiniteIndex (⊤ : Subgroup G) :=
  ⟨ne_of_eq_of_ne index_top one_ne_zero⟩

@[to_additive]
instance [FiniteIndex H] [FiniteIndex K] : FiniteIndex (H ⊓ K) :=
  ⟨index_inf_ne_zero FiniteIndex.finiteIndex FiniteIndex.finiteIndex⟩

variable {H K}

@[to_additive]
theorem finiteIndex_of_le [FiniteIndex H] (h : H ≤ K) : FiniteIndex K :=
  ⟨ne_zero_of_dvd_ne_zero FiniteIndex.finiteIndex (index_dvd_of_le h)⟩
#align subgroup.finite_index_of_le Subgroup.finiteIndex_of_le
#align add_subgroup.finite_index_of_le AddSubgroup.finiteIndex_of_le

variable (H K)

@[to_additive]
instance finiteIndex_ker {G' : Type*} [Group G'] (f : G →* G') [Finite f.range] :
    f.ker.FiniteIndex :=
  @finiteIndex_of_finite_quotient G _ f.ker
    (Finite.of_equiv f.range (QuotientGroup.quotientKerEquivRange f).symm)
#align subgroup.finite_index_ker Subgroup.finiteIndex_ker
#align add_subgroup.finite_index_ker AddSubgroup.finiteIndex_ker

instance finiteIndex_normalCore [H.FiniteIndex] : H.normalCore.FiniteIndex := by
  rw [normalCore_eq_ker]
  infer_instance
#align subgroup.finite_index_normal_core Subgroup.finiteIndex_normalCore

variable (G)

instance finiteIndex_center [Finite (commutatorSet G)] [Group.FG G] : FiniteIndex (center G) := by
  obtain ⟨S, -, hS⟩ := Group.rank_spec G
  exact ⟨mt (Finite.card_eq_zero_of_embedding (quotientCenterEmbedding hS)) Finite.card_pos.ne'⟩
#align subgroup.finite_index_center Subgroup.finiteIndex_center

theorem index_center_le_pow [Finite (commutatorSet G)] [Group.FG G] :
    (center G).index ≤ Nat.card (commutatorSet G) ^ Group.rank G := by
  obtain ⟨S, hS1, hS2⟩ := Group.rank_spec G
  rw [← hS1, ← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Finset.coe_sort_coe, ← Nat.card_fun]
  exact Finite.card_le_of_embedding (quotientCenterEmbedding hS2)
#align subgroup.index_center_le_pow Subgroup.index_center_le_pow

end FiniteIndex

end Subgroup

namespace MonoidHom

open Finset

variable {G M F : Type*} [Group G] [Fintype G] [Monoid M] [DecidableEq M]
  [FunLike F G M] [MonoidHomClass F G M]

@[to_additive]
lemma card_fiber_eq_of_mem_range (f : F) {x y : M} (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) :
    (univ.filter <| fun g => f g = x).card = (univ.filter <| fun g => f g = y).card := by
  rcases hx with ⟨x, rfl⟩
  rcases hy with ⟨y, rfl⟩
  rcases mul_left_surjective x y with ⟨y, rfl⟩
  conv_lhs =>
    rw [← map_univ_equiv (Equiv.mulRight y⁻¹), filter_map, card_map]
  congr 2 with g
  simp only [Function.comp, Equiv.toEmbedding_apply, Equiv.coe_mulRight, map_mul]
  let f' := MonoidHomClass.toMonoidHom f
  show f' g * f' y⁻¹ = f' x ↔ f' g = f' x * f' y
  rw [← f'.coe_toHomUnits y⁻¹, map_inv, Units.mul_inv_eq_iff_eq_mul, f'.coe_toHomUnits]

end MonoidHom
