/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finite.Card
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Index of a Subgroup

In this file we define the index of a subgroup, and prove several divisibility properties.
Several theorems proved in this file are known as Lagrange's theorem.

## Main definitions

- `H.index` : the index of `H : Subgroup G` as a natural number,
  and returns 0 if the index is infinite.
- `H.relIndex K` : the relative index of `H : Subgroup G` in `K : Subgroup G` as a natural number,
  and returns 0 if the relative index is infinite.

# Main results

- `card_mul_index` : `Nat.card H * H.index = Nat.card G`
- `index_mul_card` : `H.index * Fintype.card H = Fintype.card G`
- `index_dvd_card` : `H.index ∣ Fintype.card G`
- `relIndex_mul_index` : If `H ≤ K`, then `H.relIndex K * K.index = H.index`
- `index_dvd_of_le` : If `H ≤ K`, then `K.index ∣ H.index`
- `relIndex_mul_relIndex` : `relIndex` is multiplicative in towers
- `MulAction.index_stabilizer`: the index of the stabilizer is the cardinality of the orbit
-/


namespace Subgroup

open Cardinal

variable {G G' : Type*} [Group G] [Group G'] (H K L : Subgroup G)

/-- The index of a subgroup as a natural number. Returns `0` if the index is infinite. -/
@[to_additive "The index of an additive subgroup as a natural number.
Returns 0 if the index is infinite."]
noncomputable def index : ℕ :=
  Nat.card (G ⧸ H)

/-- If `H` and `K` are subgroups of a group `G`, then `relIndex H K : ℕ` is the index
of `H ∩ K` in `K`. The function returns `0` if the index is infinite. -/
@[to_additive "If `H` and `K` are subgroups of an additive group `G`, then `relIndex H K : ℕ`
is the index of `H ∩ K` in `K`. The function returns `0` if the index is infinite."]
noncomputable def relIndex : ℕ :=
  (H.subgroupOf K).index

@[deprecated (since := "2024-12-17")] alias relindex := relIndex

@[to_additive]
theorem index_comap_of_surjective {f : G' →* G} (hf : Function.Surjective f) :
    (H.comap f).index = H.index := by
  have key : ∀ x y : G',
      QuotientGroup.leftRel (H.comap f) x y ↔ QuotientGroup.leftRel H (f x) (f y) := by
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

@[to_additive]
theorem index_comap (f : G' →* G) :
    (H.comap f).index = H.relIndex f.range :=
  Eq.trans (congr_arg index (by rfl))
    ((H.subgroupOf f.range).index_comap_of_surjective f.rangeRestrict_surjective)

@[to_additive]
theorem relIndex_comap (f : G' →* G) (K : Subgroup G') :
    relIndex (comap f H) K = relIndex H (map f K) := by
  rw [relIndex, subgroupOf, comap_comap, index_comap, ← f.map_range, K.range_subtype]

@[deprecated (since := "2024-12-17")] alias relindex_comap := relIndex_comap

variable {H K L}

@[to_additive relIndex_mul_index]
theorem relIndex_mul_index (h : H ≤ K) : H.relIndex K * K.index = H.index :=
  ((mul_comm _ _).trans (Cardinal.toNat_mul _ _).symm).trans
    (congr_arg Cardinal.toNat (Equiv.cardinal_eq (quotientEquivProdOfLE h))).symm

@[deprecated (since := "2024-12-17")] alias relindex_mul_index := relIndex_mul_index

@[to_additive]
theorem index_dvd_of_le (h : H ≤ K) : K.index ∣ H.index :=
  dvd_of_mul_left_eq (H.relIndex K) (relIndex_mul_index h)

@[to_additive]
theorem relIndex_dvd_index_of_le (h : H ≤ K) : H.relIndex K ∣ H.index :=
  dvd_of_mul_right_eq K.index (relIndex_mul_index h)

@[deprecated (since := "2024-12-17")] alias relindex_dvd_index_of_le := relIndex_dvd_index_of_le

@[to_additive]
theorem relIndex_subgroupOf (hKL : K ≤ L) :
    (H.subgroupOf L).relIndex (K.subgroupOf L) = H.relIndex K :=
  ((index_comap (H.subgroupOf L) (inclusion hKL)).trans (congr_arg _ (inclusion_range hKL))).symm

@[deprecated (since := "2024-12-17")] alias relindex_subgroupOf := relIndex_subgroupOf

variable (H K L)

@[to_additive relIndex_mul_relIndex]
theorem relIndex_mul_relIndex (hHK : H ≤ K) (hKL : K ≤ L) :
    H.relIndex K * K.relIndex L = H.relIndex L := by
  rw [← relIndex_subgroupOf hKL]
  exact relIndex_mul_index fun x hx => hHK hx

@[deprecated (since := "2024-12-17")] alias relindex_mul_relindex := relIndex_mul_relIndex

@[to_additive]
theorem inf_relIndex_right : (H ⊓ K).relIndex K = H.relIndex K := by
  rw [relIndex, relIndex, inf_subgroupOf_right]

@[deprecated (since := "2024-12-17")] alias inf_relindex_right := inf_relIndex_right

@[to_additive]
theorem inf_relIndex_left : (H ⊓ K).relIndex H = K.relIndex H := by
  rw [inf_comm, inf_relIndex_right]

@[deprecated (since := "2024-12-17")] alias inf_relindex_left := inf_relIndex_left

@[to_additive relIndex_inf_mul_relIndex]
theorem relIndex_inf_mul_relIndex : H.relIndex (K ⊓ L) * K.relIndex L = (H ⊓ K).relIndex L := by
  rw [← inf_relIndex_right H (K ⊓ L), ← inf_relIndex_right K L, ← inf_relIndex_right (H ⊓ K) L,
    inf_assoc, relIndex_mul_relIndex (H ⊓ (K ⊓ L)) (K ⊓ L) L inf_le_right inf_le_right]

@[deprecated (since := "2024-12-17")] alias relindex_inf_mul_relindex := relIndex_inf_mul_relIndex

@[to_additive (attr := simp)]
theorem relIndex_sup_right [K.Normal] : K.relIndex (H ⊔ K) = K.relIndex H :=
  Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient H K).toEquiv.symm

@[deprecated (since := "2024-12-17")] alias relindex_sup_right := relIndex_sup_right

@[to_additive (attr := simp)]
theorem relIndex_sup_left [K.Normal] : K.relIndex (K ⊔ H) = K.relIndex H := by
  rw [sup_comm, relIndex_sup_right]

@[deprecated (since := "2024-12-17")] alias relindex_sup_left := relIndex_sup_left

@[to_additive]
theorem relIndex_dvd_index_of_normal [H.Normal] : H.relIndex K ∣ H.index :=
  relIndex_sup_right K H ▸ relIndex_dvd_index_of_le le_sup_right

@[deprecated (since := "2024-12-17")]
alias relindex_dvd_index_of_normal := relIndex_dvd_index_of_normal

variable {H K}

@[to_additive]
theorem relIndex_dvd_of_le_left (hHK : H ≤ K) : K.relIndex L ∣ H.relIndex L :=
  inf_of_le_left hHK ▸ dvd_of_mul_left_eq _ (relIndex_inf_mul_relIndex _ _ _)

@[deprecated (since := "2024-12-17")] alias relindex_dvd_of_le_left := relIndex_dvd_of_le_left

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
  · rw [← inv_mem_iff (x := a), ← ha, inv_mul_cancel]
    exact one_mem _
  · rwa [ha, inv_mem_iff (x := b)]

@[to_additive]
theorem mul_mem_iff_of_index_two (h : H.index = 2) {a b : G} : a * b ∈ H ↔ (a ∈ H ↔ b ∈ H) := by
  by_cases ha : a ∈ H; · simp only [ha, true_iff, mul_mem_cancel_left ha]
  by_cases hb : b ∈ H; · simp only [hb, iff_true, mul_mem_cancel_right hb]
  simp only [ha, hb, iff_true]
  rcases index_eq_two_iff.1 h with ⟨c, hc⟩
  refine (hc _).or.resolve_left ?_
  rwa [mul_assoc, mul_mem_cancel_right ((hc _).or.resolve_right hb)]

@[to_additive]
theorem mul_self_mem_of_index_two (h : H.index = 2) (a : G) : a * a ∈ H := by
  rw [mul_mem_iff_of_index_two h]

@[to_additive two_smul_mem_of_index_two]
theorem sq_mem_of_index_two (h : H.index = 2) (a : G) : a ^ 2 ∈ H :=
  (pow_two a).symm ▸ mul_self_mem_of_index_two h a

variable (H K)

-- Porting note: had to replace `Cardinal.toNat_eq_one_iff_unique` with `Nat.card_eq_one_iff_unique`
@[to_additive (attr := simp)]
theorem index_top : (⊤ : Subgroup G).index = 1 :=
  Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩

@[to_additive (attr := simp)]
theorem index_bot : (⊥ : Subgroup G).index = Nat.card G :=
  Cardinal.toNat_congr QuotientGroup.quotientBot.toEquiv

@[deprecated (since := "2024-06-15")] alias index_bot_eq_card := index_bot

@[to_additive (attr := simp)]
theorem relIndex_top_left : (⊤ : Subgroup G).relIndex H = 1 :=
  index_top

@[deprecated (since := "2024-12-17")] alias relindex_top_left := relIndex_top_left

@[to_additive (attr := simp)]
theorem relIndex_top_right : H.relIndex ⊤ = H.index := by
  rw [← relIndex_mul_index (show H ≤ ⊤ from le_top), index_top, mul_one]

@[deprecated (since := "2024-12-17")] alias relindex_top_right := relIndex_top_right

@[to_additive (attr := simp)]
theorem relIndex_bot_left : (⊥ : Subgroup G).relIndex H = Nat.card H := by
  rw [relIndex, bot_subgroupOf, index_bot]

@[deprecated (since := "2024-12-17")] alias relindex_bot_left := relIndex_bot_left

@[deprecated (since := "2024-06-15")] alias relIndex_bot_left_eq_card := relIndex_bot_left

@[to_additive (attr := simp)]
theorem relIndex_bot_right : H.relIndex ⊥ = 1 := by rw [relIndex, subgroupOf_bot_eq_top, index_top]

@[deprecated (since := "2024-12-17")] alias relindex_bot_right := relIndex_bot_right

@[to_additive (attr := simp)]
theorem relIndex_self : H.relIndex H = 1 := by rw [relIndex, subgroupOf_self, index_top]

@[deprecated (since := "2024-12-17")] alias relindex_self := relIndex_self

@[to_additive]
theorem index_ker (f : G →* G') : f.ker.index = Nat.card f.range := by
  rw [← MonoidHom.comap_bot, index_comap, relIndex_bot_left]

@[to_additive]
theorem relIndex_ker (f : G →* G') : f.ker.relIndex K = Nat.card (K.map f) := by
  rw [← MonoidHom.comap_bot, relIndex_comap, relIndex_bot_left]

@[deprecated (since := "2024-12-17")] alias relindex_ker := relIndex_ker

@[to_additive (attr := simp) card_mul_index]
theorem card_mul_index : Nat.card H * H.index = Nat.card G := by
  rw [← relIndex_bot_left, ← index_bot]
  exact relIndex_mul_index bot_le

@[deprecated (since := "2024-06-15")] alias nat_card_dvd_of_injective := card_dvd_of_injective

@[deprecated (since := "2024-06-15")] alias nat_card_dvd_of_le := card_dvd_of_le

@[to_additive]
theorem card_dvd_of_surjective (f : G →* G') (hf : Function.Surjective f) :
    Nat.card G' ∣ Nat.card G := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  exact Dvd.intro_left (Nat.card f.ker) f.ker.card_mul_index

@[deprecated (since := "2024-06-15")] alias nat_card_dvd_of_surjective := card_dvd_of_surjective

@[to_additive]
theorem card_range_dvd (f : G →* G') : Nat.card f.range ∣ Nat.card G :=
  card_dvd_of_surjective f.rangeRestrict f.rangeRestrict_surjective

@[to_additive]
theorem card_map_dvd (f : G →* G') : Nat.card (H.map f) ∣ Nat.card H :=
  card_dvd_of_surjective (f.subgroupMap H) (f.subgroupMap_surjective H)

@[to_additive]
theorem index_map (f : G →* G') :
    (H.map f).index = (H ⊔ f.ker).index * f.range.index := by
  rw [← comap_map_eq, index_comap, relIndex_mul_index (H.map_le_range f)]

@[to_additive]
theorem index_map_dvd {f : G →* G'} (hf : Function.Surjective f) :
    (H.map f).index ∣ H.index := by
  rw [index_map, f.range_eq_top_of_surjective hf, index_top, mul_one]
  exact index_dvd_of_le le_sup_left

@[to_additive]
theorem dvd_index_map {f : G →* G'} (hf : f.ker ≤ H) :
    H.index ∣ (H.map f).index := by
  rw [index_map, sup_of_le_left hf]
  apply dvd_mul_right

@[to_additive]
theorem index_map_eq {f : G →* G'} (hf1 : Function.Surjective f)
    (hf2 : f.ker ≤ H) : (H.map f).index = H.index :=
  Nat.dvd_antisymm (H.index_map_dvd hf1) (H.dvd_index_map hf2)

@[to_additive]
theorem index_map_of_injective {f : G →* G'} (hf : Function.Injective f) :
    (H.map f).index = H.index * f.range.index := by
  rw [H.index_map, f.ker_eq_bot_iff.mpr hf, sup_bot_eq]

@[to_additive]
theorem index_map_subtype {H : Subgroup G} (K : Subgroup H) :
    (K.map H.subtype).index = K.index * H.index := by
  rw [K.index_map_of_injective H.subtype_injective, H.range_subtype]

@[to_additive]
theorem index_eq_card : H.index = Nat.card (G ⧸ H) :=
  rfl

@[to_additive index_mul_card]
theorem index_mul_card : H.index * Nat.card H = Nat.card G := by
  rw [mul_comm, card_mul_index]

@[to_additive]
theorem index_dvd_card : H.index ∣ Nat.card G :=
  ⟨Nat.card H, H.index_mul_card.symm⟩

@[to_additive]
theorem relindex_dvd_card : H.relindex K ∣ Nat.card K :=
  (H.subgroupOf K).index_dvd_card

variable {H K L}

@[to_additive]
theorem relIndex_eq_zero_of_le_left (hHK : H ≤ K) (hKL : K.relIndex L = 0) : H.relIndex L = 0 :=
  eq_zero_of_zero_dvd (hKL ▸ relIndex_dvd_of_le_left L hHK)

@[deprecated (since := "2024-12-17")]
alias relindex_eq_zero_of_le_left := relIndex_eq_zero_of_le_left

@[to_additive]
theorem relIndex_eq_zero_of_le_right (hKL : K ≤ L) (hHK : H.relIndex K = 0) : H.relIndex L = 0 :=
  Finite.card_eq_zero_of_embedding (quotientSubgroupOfEmbeddingOfLE H hKL) hHK

@[deprecated (since := "2024-12-17")]
alias relindex_eq_zero_of_le_right := relIndex_eq_zero_of_le_right

@[to_additive]
theorem index_eq_zero_of_relIndex_eq_zero (h : H.relIndex K = 0) : H.index = 0 :=
  H.relIndex_top_right.symm.trans (relIndex_eq_zero_of_le_right le_top h)

@[deprecated (since := "2024-12-17")]
alias index_eq_zero_of_relindex_eq_zero := index_eq_zero_of_relIndex_eq_zero

@[to_additive]
theorem relIndex_le_of_le_left (hHK : H ≤ K) (hHL : H.relIndex L ≠ 0) :
    K.relIndex L ≤ H.relIndex L :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hHL) (relIndex_dvd_of_le_left L hHK)

@[deprecated (since := "2024-12-17")] alias relindex_le_of_le_left := relIndex_le_of_le_left

@[to_additive]
theorem relIndex_le_of_le_right (hKL : K ≤ L) (hHL : H.relIndex L ≠ 0) :
    H.relIndex K ≤ H.relIndex L :=
  Finite.card_le_of_embedding' (quotientSubgroupOfEmbeddingOfLE H hKL) fun h => (hHL h).elim

@[deprecated (since := "2024-12-17")] alias relindex_le_of_le_right := relIndex_le_of_le_right

@[to_additive]
theorem relIndex_ne_zero_trans (hHK : H.relIndex K ≠ 0) (hKL : K.relIndex L ≠ 0) :
    H.relIndex L ≠ 0 := fun h =>
  mul_ne_zero (mt (relIndex_eq_zero_of_le_right (show K ⊓ L ≤ K from inf_le_left)) hHK) hKL
    ((relIndex_inf_mul_relIndex H K L).trans (relIndex_eq_zero_of_le_left inf_le_left h))

@[deprecated (since := "2024-12-17")] alias relindex_ne_zero_trans := relIndex_ne_zero_trans

@[to_additive]
theorem relIndex_inf_ne_zero (hH : H.relIndex L ≠ 0) (hK : K.relIndex L ≠ 0) :
    (H ⊓ K).relIndex L ≠ 0 := by
  replace hH : H.relIndex (K ⊓ L) ≠ 0 := mt (relIndex_eq_zero_of_le_right inf_le_right) hH
  rw [← inf_relIndex_right] at hH hK ⊢
  rw [inf_assoc]
  exact relIndex_ne_zero_trans hH hK

@[deprecated (since := "2024-12-17")] alias relindex_inf_ne_zero := relIndex_inf_ne_zero

@[to_additive]
theorem index_inf_ne_zero (hH : H.index ≠ 0) (hK : K.index ≠ 0) : (H ⊓ K).index ≠ 0 := by
  rw [← relIndex_top_right] at hH hK ⊢
  exact relIndex_inf_ne_zero hH hK

@[to_additive]
theorem relIndex_inf_le : (H ⊓ K).relIndex L ≤ H.relIndex L * K.relIndex L := by
  by_cases h : H.relIndex L = 0
  · exact (le_of_eq (relIndex_eq_zero_of_le_left inf_le_left h)).trans (zero_le _)
  rw [← inf_relIndex_right, inf_assoc, ← relIndex_mul_relIndex _ _ L inf_le_right inf_le_right,
    inf_relIndex_right, inf_relIndex_right]
  exact mul_le_mul_right' (relIndex_le_of_le_right inf_le_right h) (K.relIndex L)

@[deprecated (since := "2024-12-17")] alias relindex_inf_le := relIndex_inf_le

@[to_additive]
theorem index_inf_le : (H ⊓ K).index ≤ H.index * K.index := by
  simp_rw [← relIndex_top_right, relIndex_inf_le]

@[to_additive]
theorem relIndex_iInf_ne_zero {ι : Type*} [_hι : Finite ι] {f : ι → Subgroup G}
    (hf : ∀ i, (f i).relIndex L ≠ 0) : (⨅ i, f i).relIndex L ≠ 0 :=
  haveI := Fintype.ofFinite ι
  (Finset.prod_ne_zero_iff.mpr fun i _hi => hf i) ∘
    Nat.card_pi.symm.trans ∘
      Finite.card_eq_zero_of_embedding (quotientiInfSubgroupOfEmbedding f L)

@[deprecated (since := "2024-12-17")] alias relindex_iInf_ne_zero := relIndex_iInf_ne_zero

@[to_additive]
theorem relIndex_iInf_le {ι : Type*} [Fintype ι] (f : ι → Subgroup G) :
    (⨅ i, f i).relIndex L ≤ ∏ i, (f i).relIndex L :=
  le_of_le_of_eq
    (Finite.card_le_of_embedding' (quotientiInfSubgroupOfEmbedding f L) fun h =>
      let ⟨i, _hi, h⟩ := Finset.prod_eq_zero_iff.mp (Nat.card_pi.symm.trans h)
      relIndex_eq_zero_of_le_left (iInf_le f i) h)
    Nat.card_pi

@[deprecated (since := "2024-12-17")] alias relindex_iInf_le := relIndex_iInf_le

@[to_additive]
theorem index_iInf_ne_zero {ι : Type*} [Finite ι] {f : ι → Subgroup G}
    (hf : ∀ i, (f i).index ≠ 0) : (⨅ i, f i).index ≠ 0 := by
  simp_rw [← relIndex_top_right] at hf ⊢
  exact relIndex_iInf_ne_zero hf

@[to_additive]
theorem index_iInf_le {ι : Type*} [Fintype ι] (f : ι → Subgroup G) :
    (⨅ i, f i).index ≤ ∏ i, (f i).index := by simp_rw [← relIndex_top_right, relIndex_iInf_le]

-- Porting note: had to replace `Cardinal.toNat_eq_one_iff_unique` with `Nat.card_eq_one_iff_unique`
@[to_additive (attr := simp) index_eq_one]
theorem index_eq_one : H.index = 1 ↔ H = ⊤ :=
  ⟨fun h =>
    QuotientGroup.subgroup_eq_top_of_subsingleton H (Nat.card_eq_one_iff_unique.mp h).1,
    fun h => (congr_arg index h).trans index_top⟩

@[to_additive (attr := simp) relIndex_eq_one]
theorem relIndex_eq_one : H.relIndex K = 1 ↔ K ≤ H :=
  index_eq_one.trans subgroupOf_eq_top

@[deprecated (since := "2024-12-17")] alias relindex_eq_one := relIndex_eq_one

@[to_additive (attr := simp) card_eq_one]
theorem card_eq_one : Nat.card H = 1 ↔ H = ⊥ :=
  H.relIndex_bot_left ▸ relIndex_eq_one.trans le_bot_iff

@[to_additive]
lemma inf_eq_bot_of_coprime (h : Nat.Coprime (Nat.card H) (Nat.card K)) : H ⊓ K = ⊥ :=
  card_eq_one.1 <| Nat.eq_one_of_dvd_coprimes h
    (card_dvd_of_le inf_le_left) (card_dvd_of_le inf_le_right)

@[deprecated (since := "2024-12-18")]
alias _root_.add_inf_eq_bot_of_coprime := AddSubgroup.inf_eq_bot_of_coprime

@[to_additive]
theorem index_ne_zero_of_finite [hH : Finite (G ⧸ H)] : H.index ≠ 0 := by
  cases nonempty_fintype (G ⧸ H)
  rw [index_eq_card]
  exact Nat.card_pos.ne'

-- Porting note: changed due to error with `Cardinal.toNat_apply_of_aleph0_le`
/-- Finite index implies finite quotient. -/
@[to_additive "Finite index implies finite quotient."]
noncomputable def fintypeOfIndexNeZero (hH : H.index ≠ 0) : Fintype (G ⧸ H) :=
  @Fintype.ofFinite _ (Nat.finite_of_card_ne_zero hH)

@[to_additive]
lemma index_eq_zero_iff_infinite : H.index = 0 ↔ Infinite (G ⧸ H) := by
  simp [index_eq_card, Nat.card_eq_zero]

@[to_additive one_lt_index_of_ne_top]
theorem one_lt_index_of_ne_top [Finite (G ⧸ H)] (hH : H ≠ ⊤) : 1 < H.index :=
  Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨index_ne_zero_of_finite, mt index_eq_one.mp hH⟩

@[to_additive]
lemma finite_quotient_of_finite_quotient_of_index_ne_zero {X : Type*} [MulAction G X]
    [Finite <| MulAction.orbitRel.Quotient G X] (hi : H.index ≠ 0) :
    Finite <| MulAction.orbitRel.Quotient H X := by
  have := fintypeOfIndexNeZero hi
  exact MulAction.finite_quotient_of_finite_quotient_of_finite_quotient

@[to_additive]
lemma finite_quotient_of_pretransitive_of_index_ne_zero {X : Type*} [MulAction G X]
    [MulAction.IsPretransitive G X] (hi : H.index ≠ 0) :
    Finite <| MulAction.orbitRel.Quotient H X := by
  have := (MulAction.pretransitive_iff_subsingleton_quotient G X).1 inferInstance
  exact finite_quotient_of_finite_quotient_of_index_ne_zero hi

@[to_additive]
lemma exists_pow_mem_of_index_ne_zero (h : H.index ≠ 0) (a : G) :
    ∃ n, 0 < n ∧ n ≤ H.index ∧ a ^ n ∈ H := by
  suffices ∃ n₁ n₂, n₁ < n₂ ∧ n₂ ≤ H.index ∧ ((a ^ n₂ : G) : G ⧸ H) = ((a ^ n₁ : G) : G ⧸ H) by
    rcases this with ⟨n₁, n₂, hlt, hle, he⟩
    refine ⟨n₂ - n₁, by omega, by omega, ?_⟩
    rw [eq_comm, QuotientGroup.eq, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add,
        add_comm] at he
    rw [← zpow_natCast]
    convert he
    omega
  suffices ∃ n₁ n₂, n₁ ≠ n₂ ∧ n₁ ≤ H.index ∧ n₂ ≤ H.index ∧
      ((a ^ n₂ : G) : G ⧸ H) = ((a ^ n₁ : G) : G ⧸ H) by
    rcases this with ⟨n₁, n₂, hne, hle₁, hle₂, he⟩
    rcases hne.lt_or_lt with hlt | hlt
    · exact ⟨n₁, n₂, hlt, hle₂, he⟩
    · exact ⟨n₂, n₁, hlt, hle₁, he.symm⟩
  by_contra hc
  simp_rw [not_exists] at hc
  let f : (Set.Icc 0 H.index) → G ⧸ H := fun n ↦ (a ^ (n : ℕ) : G)
  have hf : Function.Injective f := by
    rintro ⟨n₁, h₁, hle₁⟩ ⟨n₂, h₂, hle₂⟩ he
    have hc' := hc n₁ n₂
    dsimp only [f] at he
    simpa [hle₁, hle₂, he] using hc'
  have := (fintypeOfIndexNeZero h).finite
  have hcard := Finite.card_le_of_injective f hf
  simp [← index_eq_card] at hcard

@[to_additive]
lemma exists_pow_mem_of_relIndex_ne_zero (h : H.relIndex K ≠ 0) {a : G} (ha : a ∈ K) :
    ∃ n, 0 < n ∧ n ≤ H.relIndex K ∧ a ^ n ∈ H ⊓ K := by
  rcases exists_pow_mem_of_index_ne_zero h ⟨a, ha⟩ with ⟨n, hlt, hle, he⟩
  refine ⟨n, hlt, hle, ?_⟩
  simpa [pow_mem ha, mem_subgroupOf] using he

@[deprecated (since := "2024-12-17")]
alias exists_pow_mem_of_relindex_ne_zero := exists_pow_mem_of_relIndex_ne_zero

@[to_additive]
lemma pow_mem_of_index_ne_zero_of_dvd (h : H.index ≠ 0) (a : G) {n : ℕ}
    (hn : ∀ m, 0 < m → m ≤ H.index → m ∣ n) : a ^ n ∈ H := by
  rcases exists_pow_mem_of_index_ne_zero h a with ⟨m, hlt, hle, he⟩
  rcases hn m hlt hle with ⟨k, rfl⟩
  rw [pow_mul]
  exact pow_mem he _

@[to_additive]
lemma pow_mem_of_relIndex_ne_zero_of_dvd (h : H.relIndex K ≠ 0) {a : G} (ha : a ∈ K) {n : ℕ}
    (hn : ∀ m, 0 < m → m ≤ H.relIndex K → m ∣ n) : a ^ n ∈ H ⊓ K := by
  convert pow_mem_of_index_ne_zero_of_dvd h ⟨a, ha⟩ hn
  simp [pow_mem ha, mem_subgroupOf]

@[deprecated (since := "2024-12-17")]
alias pow_mem_of_relindex_ne_zero_of_dvd := pow_mem_of_relIndex_ne_zero_of_dvd

@[to_additive (attr := simp)]
lemma index_prod (H : Subgroup G) (K : Subgroup G') : (H.prod K).index = H.index * K.index := by
  simp_rw [index, ← Nat.card_prod]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.prodQuotientEquiv _ _).symm)
  rw [QuotientGroup.leftRel_prod]

@[to_additive (attr := simp)]
lemma index_pi {ι : Type*} [Fintype ι] (H : ι → Subgroup G) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

@[simp]
lemma index_toAddSubgroup : (Subgroup.toAddSubgroup H).index = H.index :=
  rfl

@[simp]
lemma _root_.AddSubgroup.index_toSubgroup {G : Type*} [AddGroup G] (H : AddSubgroup G) :
    (AddSubgroup.toSubgroup H).index = H.index :=
  rfl

@[simp]
lemma relIndex_toAddSubgroup :
    (Subgroup.toAddSubgroup H).relIndex (Subgroup.toAddSubgroup K) = H.relIndex K :=
  rfl

@[deprecated (since := "2024-12-17")] alias relindex_toAddSubgroup := relIndex_toAddSubgroup

@[simp]
lemma _root_.AddSubgroup.relIndex_toSubgroup {G : Type*} [AddGroup G] (H K : AddSubgroup G) :
    (AddSubgroup.toSubgroup H).relIndex (AddSubgroup.toSubgroup K) = H.relIndex K :=
  rfl

@[deprecated (since := "2024-12-17")]
alias _root_.AddSubgroup.relindex_toSubgroup := _root_.AddSubgroup.relIndex_toSubgroup

section FiniteIndex

variable (H K)

/-- Typeclass for finite index subgroups. -/
class FiniteIndex : Prop where
  /-- The subgroup has finite index -/
  index_ne_zero : H.index ≠ 0

/-- Typeclass for finite index subgroups. -/
class _root_.AddSubgroup.FiniteIndex {G : Type*} [AddGroup G] (H : AddSubgroup G) : Prop where
  /-- The additive subgroup has finite index -/
  index_ne_zero : H.index ≠ 0

/-- A finite index subgroup has finite quotient. -/
@[to_additive "A finite index subgroup has finite quotient"]
noncomputable def fintypeQuotientOfFiniteIndex [FiniteIndex H] : Fintype (G ⧸ H) :=
  fintypeOfIndexNeZero FiniteIndex.index_ne_zero

@[to_additive]
instance finite_quotient_of_finiteIndex [FiniteIndex H] : Finite (G ⧸ H) :=
  H.fintypeQuotientOfFiniteIndex.finite

@[to_additive]
theorem finiteIndex_of_finite_quotient [Finite (G ⧸ H)] : FiniteIndex H :=
  ⟨index_ne_zero_of_finite⟩

-- Porting note: had to manually provide finite instance for quotient when it should be automatic
@[to_additive]
instance (priority := 100) finiteIndex_of_finite [Finite G] : FiniteIndex H :=
  @finiteIndex_of_finite_quotient _ _ H (Quotient.finite _)

@[to_additive]
instance : FiniteIndex (⊤ : Subgroup G) :=
  ⟨ne_of_eq_of_ne index_top one_ne_zero⟩

@[to_additive]
instance [FiniteIndex H] [FiniteIndex K] : FiniteIndex (H ⊓ K) :=
  ⟨index_inf_ne_zero FiniteIndex.index_ne_zero FiniteIndex.index_ne_zero⟩

@[to_additive]
theorem finiteIndex_iInf {ι : Type*} [Finite ι] {f : ι → Subgroup G}
    (hf : ∀ i, (f i).FiniteIndex) : (⨅ i, f i).FiniteIndex :=
  ⟨index_iInf_ne_zero fun i => (hf i).index_ne_zero⟩

@[to_additive]
theorem finiteIndex_iInf' {ι : Type*} {s : Finset ι}
    (f : ι → Subgroup G) (hs : ∀ i ∈ s, (f i).FiniteIndex) :
    (⨅ i ∈ s, f i).FiniteIndex := by
  rw [iInf_subtype']
  exact finiteIndex_iInf fun ⟨i, hi⟩ => hs i hi

@[to_additive]
instance instFiniteIndex_subgroupOf (H K : Subgroup G) [H.FiniteIndex] :
    (H.subgroupOf K).FiniteIndex :=
  ⟨fun h => H.index_ne_zero_of_finite <| H.index_eq_zero_of_relIndex_eq_zero h⟩

variable {H K}

@[to_additive]
theorem finiteIndex_of_le [FiniteIndex H] (h : H ≤ K) : FiniteIndex K :=
  ⟨ne_zero_of_dvd_ne_zero FiniteIndex.index_ne_zero (index_dvd_of_le h)⟩

@[to_additive (attr := gcongr)]
lemma index_antitone (h : H ≤ K) [H.FiniteIndex] : K.index ≤ H.index :=
  Nat.le_of_dvd (Nat.zero_lt_of_ne_zero FiniteIndex.index_ne_zero) (index_dvd_of_le h)

@[to_additive (attr := gcongr)]
lemma index_strictAnti (h : H < K) [H.FiniteIndex] : K.index < H.index := by
  have h0 : K.index ≠ 0 := (finiteIndex_of_le h.le).index_ne_zero
  apply lt_of_le_of_ne (index_antitone h.le)
  rw [← relIndex_mul_index h.le, Ne, eq_comm, mul_eq_right₀ h0, relIndex_eq_one]
  exact h.not_le

variable (H K)

@[to_additive]
instance finiteIndex_ker {G' : Type*} [Group G'] (f : G →* G') [Finite f.range] :
    f.ker.FiniteIndex :=
  @finiteIndex_of_finite_quotient G _ f.ker
    (Finite.of_equiv f.range (QuotientGroup.quotientKerEquivRange f).symm)

instance finiteIndex_normalCore [H.FiniteIndex] : H.normalCore.FiniteIndex := by
  rw [normalCore_eq_ker]
  infer_instance

variable (G)

instance finiteIndex_center [Finite (commutatorSet G)] [Group.FG G] : FiniteIndex (center G) := by
  obtain ⟨S, -, hS⟩ := Group.rank_spec G
  exact ⟨mt (Finite.card_eq_zero_of_embedding (quotientCenterEmbedding hS)) Finite.card_pos.ne'⟩

theorem index_center_le_pow [Finite (commutatorSet G)] [Group.FG G] :
    (center G).index ≤ Nat.card (commutatorSet G) ^ Group.rank G := by
  obtain ⟨S, hS1, hS2⟩ := Group.rank_spec G
  rw [← hS1, ← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Finset.coe_sort_coe, ← Nat.card_fun]
  exact Finite.card_le_of_embedding (quotientCenterEmbedding hS2)

end FiniteIndex

end Subgroup

namespace MulAction

variable (G : Type*) {X : Type*} [Group G] [MulAction G X] (x : X)

@[to_additive] theorem index_stabilizer :
    (stabilizer G x).index = (orbit G x).ncard :=
  (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G x)).symm.trans
    (Set.Nat.card_coe_set_eq (orbit G x))

@[to_additive] theorem index_stabilizer_of_transitive [IsPretransitive G X] :
    (stabilizer G x).index = Nat.card X := by
  rw [index_stabilizer, orbit_eq_univ, Set.ncard_univ]

end MulAction

namespace MonoidHom

open Finset

variable {G M F : Type*} [Group G] [Fintype G] [Monoid M] [DecidableEq M]
  [FunLike F G M] [MonoidHomClass F G M]

@[to_additive]
lemma card_fiber_eq_of_mem_range (f : F) {x y : M} (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) :
    #{g | f g = x} = #{g | f g = y} := by
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
