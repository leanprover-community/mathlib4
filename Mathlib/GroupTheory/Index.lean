/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.GroupWithZero.Subgroup
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.QuotientGroup.Basic

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
- `index_mul_card` : `H.index * Nat.card H = Nat.card G`
- `index_dvd_card` : `H.index ∣ Nat.card G`
- `relindex_mul_index` : If `H ≤ K`, then `H.relindex K * K.index = H.index`
- `index_dvd_of_le` : If `H ≤ K`, then `K.index ∣ H.index`
- `relindex_mul_relindex` : `relindex` is multiplicative in towers
- `MulAction.index_stabilizer`: the index of the stabilizer is the cardinality of the orbit
-/

assert_not_exists Field

open scoped Pointwise

namespace Subgroup

open Cardinal Function

variable {G G' : Type*} [Group G] [Group G'] (H K L : Subgroup G)

/-- The index of a subgroup as a natural number. Returns `0` if the index is infinite. -/
@[to_additive /-- The index of an additive subgroup as a natural number.
Returns 0 if the index is infinite. -/]
noncomputable def index : ℕ :=
  Nat.card (G ⧸ H)

/-- If `H` and `K` are subgroups of a group `G`, then `relindex H K : ℕ` is the index
of `H ∩ K` in `K`. The function returns `0` if the index is infinite. -/
@[to_additive /-- If `H` and `K` are subgroups of an additive group `G`, then `relindex H K : ℕ`
is the index of `H ∩ K` in `K`. The function returns `0` if the index is infinite. -/]
noncomputable def relindex : ℕ :=
  (H.subgroupOf K).index

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
    (H.comap f).index = H.relindex f.range :=
  Eq.trans (congr_arg index (by rfl))
    ((H.subgroupOf f.range).index_comap_of_surjective f.rangeRestrict_surjective)

@[to_additive]
theorem relindex_comap (f : G' →* G) (K : Subgroup G') :
    relindex (comap f H) K = relindex H (map f K) := by
  rw [relindex, subgroupOf, comap_comap, index_comap, ← f.map_range, K.range_subtype]

@[to_additive]
theorem relindex_map_map_of_injective {f : G →* G'} (H K : Subgroup G) (hf : Function.Injective f) :
    relindex (map f H) (map f K) = relindex H K := by
  rw [← Subgroup.relindex_comap, Subgroup.comap_map_eq_self_of_injective hf]

@[to_additive]
theorem relindex_map_map (f : G →* G') (H K : Subgroup G) :
    (map f H).relindex (map f K) = (H ⊔ f.ker).relindex (K ⊔ f.ker) := by
  rw [← comap_map_eq, ← comap_map_eq, relindex_comap, (gc_map_comap f).l_u_l_eq_l]

variable {H K L}

@[to_additive relindex_mul_index]
theorem relindex_mul_index (h : H ≤ K) : H.relindex K * K.index = H.index :=
  ((mul_comm _ _).trans (Cardinal.toNat_mul _ _).symm).trans
    (congr_arg Cardinal.toNat (Equiv.cardinal_eq (quotientEquivProdOfLE h))).symm

@[to_additive]
theorem index_dvd_of_le (h : H ≤ K) : K.index ∣ H.index :=
  dvd_of_mul_left_eq (H.relindex K) (relindex_mul_index h)

@[to_additive]
theorem relindex_dvd_index_of_le (h : H ≤ K) : H.relindex K ∣ H.index :=
  dvd_of_mul_right_eq K.index (relindex_mul_index h)

@[to_additive]
theorem relindex_subgroupOf (hKL : K ≤ L) :
    (H.subgroupOf L).relindex (K.subgroupOf L) = H.relindex K :=
  ((index_comap (H.subgroupOf L) (inclusion hKL)).trans (congr_arg _ (inclusion_range hKL))).symm

variable (H K L)

@[to_additive relindex_mul_relindex]
theorem relindex_mul_relindex (hHK : H ≤ K) (hKL : K ≤ L) :
    H.relindex K * K.relindex L = H.relindex L := by
  rw [← relindex_subgroupOf hKL]
  exact relindex_mul_index fun x hx => hHK hx

@[to_additive]
theorem inf_relindex_right : (H ⊓ K).relindex K = H.relindex K := by
  rw [relindex, relindex, inf_subgroupOf_right]

@[to_additive]
theorem inf_relindex_left : (H ⊓ K).relindex H = K.relindex H := by
  rw [inf_comm, inf_relindex_right]

@[to_additive relindex_inf_mul_relindex]
theorem relindex_inf_mul_relindex : H.relindex (K ⊓ L) * K.relindex L = (H ⊓ K).relindex L := by
  rw [← inf_relindex_right H (K ⊓ L), ← inf_relindex_right K L, ← inf_relindex_right (H ⊓ K) L,
    inf_assoc, relindex_mul_relindex (H ⊓ (K ⊓ L)) (K ⊓ L) L inf_le_right inf_le_right]

@[to_additive (attr := simp)]
theorem relindex_sup_right [K.Normal] : K.relindex (H ⊔ K) = K.relindex H :=
  Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient H K).toEquiv.symm

@[to_additive (attr := simp)]
theorem relindex_sup_left [K.Normal] : K.relindex (K ⊔ H) = K.relindex H := by
  rw [sup_comm, relindex_sup_right]

@[to_additive]
theorem relindex_dvd_index_of_normal [H.Normal] : H.relindex K ∣ H.index :=
  relindex_sup_right K H ▸ relindex_dvd_index_of_le le_sup_right

variable {H K}

@[to_additive]
theorem relindex_dvd_of_le_left (hHK : H ≤ K) : K.relindex L ∣ H.relindex L :=
  inf_of_le_left hHK ▸ dvd_of_mul_left_eq _ (relindex_inf_mul_relindex _ _ _)

/-- A subgroup has index two if and only if there exists `a` such that for all `b`, exactly one
of `b * a` and `b` belong to `H`. -/
@[to_additive /-- An additive subgroup has index two if and only if there exists `a` such that
for all `b`, exactly one of `b + a` and `b` belong to `H`. -/]
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

variable (H K) {f : G →* G'}

@[to_additive (attr := simp)]
theorem index_top : (⊤ : Subgroup G).index = 1 :=
  Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩

@[to_additive (attr := simp)]
theorem index_bot : (⊥ : Subgroup G).index = Nat.card G :=
  Cardinal.toNat_congr QuotientGroup.quotientBot.toEquiv

@[to_additive (attr := simp)]
theorem relindex_top_left : (⊤ : Subgroup G).relindex H = 1 :=
  index_top

@[to_additive (attr := simp)]
theorem relindex_top_right : H.relindex ⊤ = H.index := by
  rw [← relindex_mul_index (show H ≤ ⊤ from le_top), index_top, mul_one]

@[to_additive (attr := simp)]
theorem relindex_bot_left : (⊥ : Subgroup G).relindex H = Nat.card H := by
  rw [relindex, bot_subgroupOf, index_bot]

@[to_additive (attr := simp)]
theorem relindex_bot_right : H.relindex ⊥ = 1 := by rw [relindex, subgroupOf_bot_eq_top, index_top]

@[to_additive (attr := simp)]
theorem relindex_self : H.relindex H = 1 := by rw [relindex, subgroupOf_self, index_top]

@[to_additive]
theorem index_ker (f : G →* G') : f.ker.index = Nat.card f.range := by
  rw [← MonoidHom.comap_bot, index_comap, relindex_bot_left]

@[to_additive]
theorem relindex_ker (f : G →* G') : f.ker.relindex K = Nat.card (K.map f) := by
  rw [← MonoidHom.comap_bot, relindex_comap, relindex_bot_left]

@[to_additive (attr := simp) card_mul_index]
theorem card_mul_index : Nat.card H * H.index = Nat.card G := by
  rw [← relindex_bot_left, ← index_bot]
  exact relindex_mul_index bot_le

@[to_additive]
theorem card_dvd_of_surjective (f : G →* G') (hf : Function.Surjective f) :
    Nat.card G' ∣ Nat.card G := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  exact Dvd.intro_left (Nat.card f.ker) f.ker.card_mul_index

@[to_additive]
theorem card_range_dvd (f : G →* G') : Nat.card f.range ∣ Nat.card G :=
  card_dvd_of_surjective f.rangeRestrict f.rangeRestrict_surjective

@[to_additive]
theorem card_map_dvd (f : G →* G') : Nat.card (H.map f) ∣ Nat.card H :=
  card_dvd_of_surjective (f.subgroupMap H) (f.subgroupMap_surjective H)

@[to_additive]
theorem index_map (f : G →* G') :
    (H.map f).index = (H ⊔ f.ker).index * f.range.index := by
  rw [← comap_map_eq, index_comap, relindex_mul_index (H.map_le_range f)]

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
theorem index_map_eq (hf1 : Surjective f) (hf2 : f.ker ≤ H) : (H.map f).index = H.index :=
  Nat.dvd_antisymm (H.index_map_dvd hf1) (H.dvd_index_map hf2)

@[to_additive]
lemma index_map_of_bijective (hf : Bijective f) (H : Subgroup G) : (H.map f).index = H.index :=
  index_map_eq _ hf.2 (by rw [f.ker_eq_bot_iff.2 hf.1]; exact bot_le)

@[to_additive (attr := simp)]
theorem index_map_equiv (e : G ≃* G') : (map (e : G →* G') H).index = H.index :=
  index_map_of_bijective e.bijective H

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
theorem relindex_eq_zero_of_le_left (hHK : H ≤ K) (hKL : K.relindex L = 0) : H.relindex L = 0 :=
  eq_zero_of_zero_dvd (hKL ▸ relindex_dvd_of_le_left L hHK)

@[to_additive]
theorem relindex_eq_zero_of_le_right (hKL : K ≤ L) (hHK : H.relindex K = 0) : H.relindex L = 0 :=
  Finite.card_eq_zero_of_embedding (quotientSubgroupOfEmbeddingOfLE H hKL) hHK

/-- If `J` has finite index in `K`, then the same holds for their comaps under any group hom. -/
@[to_additive /-- If `J` has finite index in `K`, then the same holds for their comaps under any
additive group hom. -/]
lemma relindex_comap_ne_zero (f : G →* G') {J K : Subgroup G'} (hJK : J.relindex K ≠ 0) :
    (J.comap f).relindex (K.comap f) ≠ 0 := by
  rw [relindex_comap]
  exact fun h ↦ hJK <| relindex_eq_zero_of_le_right (map_comap_le _ _) h

@[to_additive]
theorem index_eq_zero_of_relindex_eq_zero (h : H.relindex K = 0) : H.index = 0 :=
  H.relindex_top_right.symm.trans (relindex_eq_zero_of_le_right le_top h)

@[to_additive]
theorem relindex_le_of_le_left (hHK : H ≤ K) (hHL : H.relindex L ≠ 0) :
    K.relindex L ≤ H.relindex L :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hHL) (relindex_dvd_of_le_left L hHK)

@[to_additive]
theorem relindex_le_of_le_right (hKL : K ≤ L) (hHL : H.relindex L ≠ 0) :
    H.relindex K ≤ H.relindex L :=
  Finite.card_le_of_embedding' (quotientSubgroupOfEmbeddingOfLE H hKL) fun h => (hHL h).elim

@[to_additive]
theorem relindex_ne_zero_trans (hHK : H.relindex K ≠ 0) (hKL : K.relindex L ≠ 0) :
    H.relindex L ≠ 0 := fun h =>
  mul_ne_zero (mt (relindex_eq_zero_of_le_right (show K ⊓ L ≤ K from inf_le_left)) hHK) hKL
    ((relindex_inf_mul_relindex H K L).trans (relindex_eq_zero_of_le_left inf_le_left h))

@[to_additive]
theorem relindex_inf_ne_zero (hH : H.relindex L ≠ 0) (hK : K.relindex L ≠ 0) :
    (H ⊓ K).relindex L ≠ 0 := by
  replace hH : H.relindex (K ⊓ L) ≠ 0 := mt (relindex_eq_zero_of_le_right inf_le_right) hH
  rw [← inf_relindex_right] at hH hK ⊢
  rw [inf_assoc]
  exact relindex_ne_zero_trans hH hK

@[to_additive]
theorem index_inf_ne_zero (hH : H.index ≠ 0) (hK : K.index ≠ 0) : (H ⊓ K).index ≠ 0 := by
  rw [← relindex_top_right] at hH hK ⊢
  exact relindex_inf_ne_zero hH hK

/-- If `J` has finite index in `K`, then `J ⊓ L` has finite index in `K ⊓ L` for any `L`. -/
@[to_additive /-- If `J` has finite index in `K`, then `J ⊓ L` has finite index in `K ⊓ L` for any
`L`. -/]
lemma relindex_inter_ne_zero {J K : Subgroup G} (hJK : J.relindex K ≠ 0) (L : Subgroup G) :
    (J ⊓ L).relindex (K ⊓ L) ≠ 0 := by
  rw [← range_subtype L, inf_comm, ← map_comap_eq, inf_comm, ← map_comap_eq, ← relindex_comap,
    comap_map_eq_self_of_injective (subtype_injective L)]
  exact relindex_comap_ne_zero _ hJK

@[to_additive]
theorem relindex_inf_le : (H ⊓ K).relindex L ≤ H.relindex L * K.relindex L := by
  by_cases h : H.relindex L = 0
  · exact (le_of_eq (relindex_eq_zero_of_le_left inf_le_left h)).trans (zero_le _)
  rw [← inf_relindex_right, inf_assoc, ← relindex_mul_relindex _ _ L inf_le_right inf_le_right,
    inf_relindex_right, inf_relindex_right]
  exact mul_le_mul_right' (relindex_le_of_le_right inf_le_right h) (K.relindex L)

@[to_additive]
theorem index_inf_le : (H ⊓ K).index ≤ H.index * K.index := by
  simp_rw [← relindex_top_right, relindex_inf_le]

@[to_additive]
theorem relindex_iInf_ne_zero {ι : Type*} [_hι : Finite ι] {f : ι → Subgroup G}
    (hf : ∀ i, (f i).relindex L ≠ 0) : (⨅ i, f i).relindex L ≠ 0 :=
  haveI := Fintype.ofFinite ι
  (Finset.prod_ne_zero_iff.mpr fun i _hi => hf i) ∘
    Nat.card_pi.symm.trans ∘
      Finite.card_eq_zero_of_embedding (quotientiInfSubgroupOfEmbedding f L)

@[to_additive]
theorem relindex_iInf_le {ι : Type*} [Fintype ι] (f : ι → Subgroup G) :
    (⨅ i, f i).relindex L ≤ ∏ i, (f i).relindex L :=
  le_of_le_of_eq
    (Finite.card_le_of_embedding' (quotientiInfSubgroupOfEmbedding f L) fun h =>
      let ⟨i, _hi, h⟩ := Finset.prod_eq_zero_iff.mp (Nat.card_pi.symm.trans h)
      relindex_eq_zero_of_le_left (iInf_le f i) h)
    Nat.card_pi

@[to_additive]
theorem index_iInf_ne_zero {ι : Type*} [Finite ι] {f : ι → Subgroup G}
    (hf : ∀ i, (f i).index ≠ 0) : (⨅ i, f i).index ≠ 0 := by
  simp_rw [← relindex_top_right] at hf ⊢
  exact relindex_iInf_ne_zero hf

@[to_additive]
theorem index_iInf_le {ι : Type*} [Fintype ι] (f : ι → Subgroup G) :
    (⨅ i, f i).index ≤ ∏ i, (f i).index := by simp_rw [← relindex_top_right, relindex_iInf_le]

@[to_additive (attr := simp) index_eq_one]
theorem index_eq_one : H.index = 1 ↔ H = ⊤ :=
  ⟨fun h =>
    QuotientGroup.subgroup_eq_top_of_subsingleton H (Nat.card_eq_one_iff_unique.mp h).1,
    fun h => (congr_arg index h).trans index_top⟩

@[to_additive (attr := simp) relindex_eq_one]
theorem relindex_eq_one : H.relindex K = 1 ↔ K ≤ H :=
  index_eq_one.trans subgroupOf_eq_top

@[to_additive (attr := simp) card_eq_one]
theorem card_eq_one : Nat.card H = 1 ↔ H = ⊥ :=
  H.relindex_bot_left ▸ relindex_eq_one.trans le_bot_iff

@[to_additive]
lemma inf_eq_bot_of_coprime (h : Nat.Coprime (Nat.card H) (Nat.card K)) : H ⊓ K = ⊥ :=
  card_eq_one.1 <| Nat.eq_one_of_dvd_coprimes h
    (card_dvd_of_le inf_le_left) (card_dvd_of_le inf_le_right)

@[to_additive]
theorem index_ne_zero_of_finite [hH : Finite (G ⧸ H)] : H.index ≠ 0 := by
  cases nonempty_fintype (G ⧸ H)
  rw [index_eq_card]
  exact Nat.card_pos.ne'

/-- Finite index implies finite quotient. -/
@[to_additive /-- Finite index implies finite quotient. -/]
noncomputable def fintypeOfIndexNeZero (hH : H.index ≠ 0) : Fintype (G ⧸ H) :=
  @Fintype.ofFinite _ (Nat.finite_of_card_ne_zero hH)

@[to_additive]
lemma index_eq_zero_iff_infinite : H.index = 0 ↔ Infinite (G ⧸ H) := by
  simp [index_eq_card, Nat.card_eq_zero]

@[to_additive]
lemma index_ne_zero_iff_finite : H.index ≠ 0 ↔ Finite (G ⧸ H) := by
  simp [index_eq_zero_iff_infinite]

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
    rcases hne.lt_or_gt with hlt | hlt
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
lemma exists_pow_mem_of_relindex_ne_zero (h : H.relindex K ≠ 0) {a : G} (ha : a ∈ K) :
    ∃ n, 0 < n ∧ n ≤ H.relindex K ∧ a ^ n ∈ H ⊓ K := by
  rcases exists_pow_mem_of_index_ne_zero h ⟨a, ha⟩ with ⟨n, hlt, hle, he⟩
  refine ⟨n, hlt, hle, ?_⟩
  simpa [pow_mem ha, mem_subgroupOf] using he

@[to_additive]
lemma pow_mem_of_index_ne_zero_of_dvd (h : H.index ≠ 0) (a : G) {n : ℕ}
    (hn : ∀ m, 0 < m → m ≤ H.index → m ∣ n) : a ^ n ∈ H := by
  rcases exists_pow_mem_of_index_ne_zero h a with ⟨m, hlt, hle, he⟩
  rcases hn m hlt hle with ⟨k, rfl⟩
  rw [pow_mul]
  exact pow_mem he _

@[to_additive]
lemma pow_mem_of_relindex_ne_zero_of_dvd (h : H.relindex K ≠ 0) {a : G} (ha : a ∈ K) {n : ℕ}
    (hn : ∀ m, 0 < m → m ≤ H.relindex K → m ∣ n) : a ^ n ∈ H ⊓ K := by
  convert pow_mem_of_index_ne_zero_of_dvd h ⟨a, ha⟩ hn
  simp [pow_mem ha, mem_subgroupOf]

@[to_additive (attr := simp) index_prod]
lemma index_prod (H : Subgroup G) (K : Subgroup G') : (H.prod K).index = H.index * K.index := by
  simp_rw [index, ← Nat.card_prod]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.prodQuotientEquiv _ _).symm)
  rw [QuotientGroup.leftRel_prod]

@[deprecated (since := "2025-03-11")]
alias _root_.AddSubgroup.index_sum := AddSubgroup.index_prod

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
lemma relindex_toAddSubgroup :
    (Subgroup.toAddSubgroup H).relindex (Subgroup.toAddSubgroup K) = H.relindex K :=
  rfl

@[simp]
lemma _root_.AddSubgroup.relindex_toSubgroup {G : Type*} [AddGroup G] (H K : AddSubgroup G) :
    (AddSubgroup.toSubgroup H).relindex (AddSubgroup.toSubgroup K) = H.relindex K :=
  rfl

section FiniteIndex

/-- Typeclass for finite index subgroups. -/
class _root_.AddSubgroup.FiniteIndex {G : Type*} [AddGroup G] (H : AddSubgroup G) : Prop where
  /-- The additive subgroup has finite index;
  recall that `AddSubgroup.index` returns 0 when the index is infinite. -/
  index_ne_zero : H.index ≠ 0

@[deprecated (since := "2025-04-13")]
alias _root_AddSubgroup.FiniteIndex.finiteIndex := AddSubgroup.FiniteIndex.index_ne_zero

variable (H) in
/-- Typeclass for finite index subgroups. -/
@[to_additive] class FiniteIndex : Prop where
  /-- The subgroup has finite index;
  recall that `Subgroup.index` returns 0 when the index is infinite. -/
  index_ne_zero : H.index ≠ 0

@[deprecated (since := "2025-04-13")] alias FiniteIndex.finiteIndex := FiniteIndex.index_ne_zero

/-- Typeclass for a subgroup `H` to have finite index in a subgroup `K`. -/
class _root_.AddSubgroup.IsFiniteRelIndex {G : Type*} [AddGroup G] (H K : AddSubgroup G) :
    Prop where
  protected relindex_ne_zero : H.relindex K ≠ 0

variable (H K) in
/-- Typeclass for a subgroup `H` to have finite index in a subgroup `K`. -/
@[to_additive] class IsFiniteRelIndex : Prop where
  protected relindex_ne_zero : H.relindex K ≠ 0

@[to_additive] lemma relindex_ne_zero [H.IsFiniteRelIndex K] : H.relindex K ≠ 0 :=
  IsFiniteRelIndex.relindex_ne_zero

@[to_additive]
instance IsFiniteRelIndex.to_finiteIndex_subgroupOf [H.IsFiniteRelIndex K] :
    (H.subgroupOf K).FiniteIndex where
  index_ne_zero := relindex_ne_zero

@[to_additive]
theorem finiteIndex_iff : H.FiniteIndex ↔ H.index ≠ 0 :=
  ⟨fun h ↦ h.index_ne_zero, fun h ↦ ⟨h⟩⟩

@[to_additive]
theorem not_finiteIndex_iff {G : Type*} [Group G] {H : Subgroup G} :
    ¬ H.FiniteIndex ↔ H.index = 0 := by simp [finiteIndex_iff]

/-- A finite index subgroup has finite quotient. -/
@[to_additive /-- A finite index subgroup has finite quotient -/]
noncomputable def fintypeQuotientOfFiniteIndex [FiniteIndex H] : Fintype (G ⧸ H) :=
  fintypeOfIndexNeZero FiniteIndex.index_ne_zero

@[to_additive]
instance finite_quotient_of_finiteIndex [FiniteIndex H] : Finite (G ⧸ H) :=
  fintypeQuotientOfFiniteIndex.finite

@[to_additive]
theorem finiteIndex_of_finite_quotient [Finite (G ⧸ H)] : FiniteIndex H :=
  ⟨index_ne_zero_of_finite⟩

@[to_additive]
theorem finiteIndex_iff_finite_quotient : FiniteIndex H ↔ Finite (G ⧸ H) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ finiteIndex_of_finite_quotient⟩

@[to_additive]
instance (priority := 100) finiteIndex_of_finite [Finite G] : FiniteIndex H :=
  finiteIndex_of_finite_quotient

variable (H) in
@[to_additive]
theorem finite_iff_finite_and_finiteIndex : Finite G ↔ Finite H ∧ H.FiniteIndex where
  mp _ := ⟨inferInstance, inferInstance⟩
  mpr := fun ⟨_, _⟩ ↦ Nat.finite_of_card_ne_zero <|
    H.card_mul_index ▸ mul_ne_zero Nat.card_pos.ne' FiniteIndex.index_ne_zero

@[to_additive]
theorem _root_.MonoidHom.finite_iff_finite_ker_range (f : G →* G') :
    Finite G ↔ Finite f.ker ∧ Finite f.range := by
  rw [finite_iff_finite_and_finiteIndex f.ker, ← (QuotientGroup.quotientKerEquivRange f).finite_iff,
    finiteIndex_iff_finite_quotient]

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
  ⟨fun h => H.index_ne_zero_of_finite <| H.index_eq_zero_of_relindex_eq_zero h⟩

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
  rw [← relindex_mul_index h.le, Ne, eq_comm, mul_eq_right₀ h0, relindex_eq_one]
  exact h.not_ge

variable (H K)

@[to_additive]
instance finiteIndex_ker {G' : Type*} [Group G'] (f : G →* G') [Finite f.range] :
    f.ker.FiniteIndex :=
  @finiteIndex_of_finite_quotient G _ f.ker
    (Finite.of_equiv f.range (QuotientGroup.quotientKerEquivRange f).symm)

instance finiteIndex_normalCore [H.FiniteIndex] : H.normalCore.FiniteIndex := by
  rw [normalCore_eq_ker]
  infer_instance

@[to_additive]
theorem index_range {f : G →* G} [hf : f.ker.FiniteIndex] :
    f.range.index = Nat.card f.ker := by
  rw [← mul_left_inj' hf.index_ne_zero, card_mul_index, index_ker, index_mul_card]

end FiniteIndex

end Subgroup

section Pointwise

open Pointwise

variable {G H : Type*} [Group H] (h : H)

-- NB: `to_additive` does not work to generate the second lemma from the first here, because it
-- would need to additivize `G`, but not `H`.

lemma Subgroup.relindex_pointwise_smul [Group G] [MulDistribMulAction H G] (J K : Subgroup G) :
    (h • J).relindex (h • K) = J.relindex K := by
  rw [pointwise_smul_def K, ← relindex_comap, pointwise_smul_def,
    comap_map_eq_self_of_injective (by intro a b; simp)]

lemma AddSubgroup.relindex_pointwise_smul [AddGroup G] [DistribMulAction H G]
    (J K : AddSubgroup G) : (h • J).relindex (h • K) = J.relindex K := by
  rw [pointwise_smul_def K, ← relindex_comap, pointwise_smul_def,
    comap_map_eq_self_of_injective (by intro a b; simp)]

end Pointwise

namespace MulAction

variable (G : Type*) {X : Type*} [Group G] [MulAction G X] (x : X)

@[to_additive] theorem index_stabilizer :
    (stabilizer G x).index = (orbit G x).ncard :=
  (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G x)).symm.trans
    (Nat.card_coe_set_eq (orbit G x))

@[to_additive] theorem index_stabilizer_of_transitive [IsPretransitive G X] :
    (stabilizer G x).index = Nat.card X := by
  rw [index_stabilizer, orbit_eq_univ, Set.ncard_univ]

end MulAction

namespace MonoidHom

@[to_additive AddMonoidHom.surjective_of_card_ker_le_div]
lemma surjective_of_card_ker_le_div {G M : Type*} [Group G] [Group M] [Finite G] [Finite M]
    (f : G →* M) (h : Nat.card f.ker ≤ Nat.card G / Nat.card M) : Function.Surjective f := by
  refine range_eq_top.1 <| SetLike.ext' <| Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
  rw [Subgroup.coe_top, Set.ncard_univ, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  exact Nat.le_of_mul_le_mul_left (f.ker.card_mul_index ▸ Nat.mul_le_of_le_div _ _ _ h) Nat.card_pos

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
  change f' g * f' y⁻¹ = f' x ↔ f' g = f' x * f' y
  rw [← f'.coe_toHomUnits y⁻¹, map_inv, Units.mul_inv_eq_iff_eq_mul, f'.coe_toHomUnits]

end MonoidHom

namespace AddSubgroup
variable {G A : Type*} [Group G] [AddGroup A] [DistribMulAction G A]

@[simp]
lemma index_smul (a : G) (S : AddSubgroup A) : (a • S).index = S.index :=
  index_map_of_bijective (MulAction.bijective _) _

end AddSubgroup
