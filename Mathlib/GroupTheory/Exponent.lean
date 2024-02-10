/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Mathlib.Data.ZMod.Quotient
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Peel

#align_import group_theory.exponent from "leanprover-community/mathlib"@"52fa514ec337dd970d71d8de8d0fd68b455a1e54"

/-!
# Exponent of a group

This file defines the exponent of a group, or more generally a monoid. For a group `G` it is defined
to be the minimal `n≥1` such that `g ^ n = 1` for all `g ∈ G`. For a finite group `G`,
it is equal to the lowest common multiple of the order of all elements of the group `G`.

## Main definitions

* `Monoid.ExponentExists` is a predicate on a monoid `G` saying that there is some positive `n`
  such that `g ^ n = 1` for all `g ∈ G`.
* `Monoid.exponent` defines the exponent of a monoid `G` as the minimal positive `n` such that
  `g ^ n = 1` for all `g ∈ G`, by convention it is `0` if no such `n` exists.
* `AddMonoid.ExponentExists` the additive version of `Monoid.ExponentExists`.
* `AddMonoid.exponent` the additive version of `Monoid.exponent`.

## Main results

* `Monoid.lcm_order_eq_exponent`: For a finite left cancel monoid `G`, the exponent is equal to the
  `Finset.lcm` of the order of its elements.
* `Monoid.exponent_eq_iSup_orderOf(')`: For a commutative cancel monoid, the exponent is
  equal to `⨆ g : G, orderOf g` (or zero if it has any order-zero elements).
* `Monoid.exponent_pi` and `Monoid.exponent_prod`: The exponent of a finite product of monoids is
  the least common multiple (`Finset.lcm` and `lcm`, respectively) of the exponents of the
  constituent monoids.
* `MonoidHom.exponent_dvd`: If `f : M₁ →⋆ M₂` is surjective, then the exponent of `M₂` divides the
  exponent of `M₁`.

## TODO
* Refactor the characteristic of a ring to be the exponent of its underlying additive group.
-/


universe u

variable {G : Type u}

open Classical

namespace Monoid

section Monoid

variable (G) [Monoid G]

/-- A predicate on a monoid saying that there is a positive integer `n` such that `g ^ n = 1`
  for all `g`.-/
@[to_additive
      "A predicate on an additive monoid saying that there is a positive integer `n` such\n
      that `n • g = 0` for all `g`."]
def ExponentExists :=
  ∃ n, 0 < n ∧ ∀ g : G, g ^ n = 1
#align monoid.exponent_exists Monoid.ExponentExists
#align add_monoid.exponent_exists AddMonoid.ExponentExists

/-- The exponent of a group is the smallest positive integer `n` such that `g ^ n = 1` for all
  `g ∈ G` if it exists, otherwise it is zero by convention.-/
@[to_additive
      "The exponent of an additive group is the smallest positive integer `n` such that\n
      `n • g = 0` for all `g ∈ G` if it exists, otherwise it is zero by convention."]
noncomputable def exponent :=
  if h : ExponentExists G then Nat.find h else 0
#align monoid.exponent Monoid.exponent
#align add_monoid.exponent AddMonoid.exponent

variable {G}

@[simp]
theorem _root_.AddMonoid.exponent_additive :
    AddMonoid.exponent (Additive G) = exponent G := rfl

@[simp]
theorem exponent_multiplicative {G : Type*} [AddMonoid G] :
    exponent (Multiplicative G) = AddMonoid.exponent G := rfl

open MulOpposite in
@[to_additive (attr := simp)]
theorem _root_.MulOpposite.exponent : exponent (MulOpposite G) = exponent G := by
  simp only [Monoid.exponent, ExponentExists]
  congr!
  all_goals exact ⟨(op_injective <| · <| op ·), (unop_injective <| . <| unop .)⟩

@[to_additive]
theorem exponentExists_iff_ne_zero : ExponentExists G ↔ exponent G ≠ 0 := by
  rw [exponent]
  split_ifs with h
  · simp [h, @not_lt_zero' ℕ]
  --if this isn't done this way, `to_additive` freaks
  · tauto
#align monoid.exponent_exists_iff_ne_zero Monoid.exponentExists_iff_ne_zero
#align add_monoid.exponent_exists_iff_ne_zero AddMonoid.exponentExists_iff_ne_zero

@[to_additive]
theorem exponent_eq_zero_iff : exponent G = 0 ↔ ¬ExponentExists G := by
  simp only [exponentExists_iff_ne_zero, Classical.not_not]
#align monoid.exponent_eq_zero_iff Monoid.exponent_eq_zero_iff
#align add_monoid.exponent_eq_zero_iff AddMonoid.exponent_eq_zero_iff

@[to_additive exponent_eq_zero_addOrder_zero]
theorem exponent_eq_zero_of_order_zero {g : G} (hg : orderOf g = 0) : exponent G = 0 :=
  exponent_eq_zero_iff.mpr fun ⟨n, hn, hgn⟩ => orderOf_eq_zero_iff'.mp hg n hn <| hgn g
#align monoid.exponent_eq_zero_of_order_zero Monoid.exponent_eq_zero_of_order_zero
#align add_monoid.exponent_eq_zero_of_order_zero AddMonoid.exponent_eq_zero_addOrder_zero

@[to_additive exponent_nsmul_eq_zero]
theorem pow_exponent_eq_one (g : G) : g ^ exponent G = 1 := by
  by_cases h : ExponentExists G
  · simp_rw [exponent, dif_pos h]
    exact (Nat.find_spec h).2 g
  · simp_rw [exponent, dif_neg h, pow_zero]
#align monoid.pow_exponent_eq_one Monoid.pow_exponent_eq_one
#align add_monoid.exponent_nsmul_eq_zero AddMonoid.exponent_nsmul_eq_zero

@[to_additive]
theorem pow_eq_mod_exponent {n : ℕ} (g : G) : g ^ n = g ^ (n % exponent G) :=
  calc
    g ^ n = g ^ (n % exponent G + exponent G * (n / exponent G)) := by rw [Nat.mod_add_div]
    _ = g ^ (n % exponent G) := by simp [pow_add, pow_mul, pow_exponent_eq_one]

#align monoid.pow_eq_mod_exponent Monoid.pow_eq_mod_exponent
#align add_monoid.nsmul_eq_mod_exponent AddMonoid.nsmul_eq_mod_exponent

@[to_additive]
theorem exponent_pos_of_exists (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, g ^ n = 1) :
    0 < exponent G := by
  have h : ∃ n, 0 < n ∧ ∀ g : G, g ^ n = 1 := ⟨n, hpos, hG⟩
  rw [exponent, dif_pos]
  exact (Nat.find_spec h).1
#align monoid.exponent_pos_of_exists Monoid.exponent_pos_of_exists
#align add_monoid.exponent_pos_of_exists AddMonoid.exponent_pos_of_exists

@[to_additive]
theorem exponent_min' (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, g ^ n = 1) : exponent G ≤ n := by
  rw [exponent, dif_pos]
  · apply Nat.find_min'
    exact ⟨hpos, hG⟩
  · exact ⟨n, hpos, hG⟩
#align monoid.exponent_min' Monoid.exponent_min'
#align add_monoid.exponent_min' AddMonoid.exponent_min'

@[to_additive]
theorem exponent_min (m : ℕ) (hpos : 0 < m) (hm : m < exponent G) : ∃ g : G, g ^ m ≠ 1 := by
  by_contra! h
  have hcon : exponent G ≤ m := exponent_min' m hpos h
  linarith
#align monoid.exponent_min Monoid.exponent_min
#align add_monoid.exponent_min AddMonoid.exponent_min

@[to_additive (attr := simp)]
theorem exp_eq_one_of_subsingleton [Subsingleton G] : exponent G = 1 := by
  apply le_antisymm
  · apply exponent_min' _ Nat.one_pos
    simp [eq_iff_true_of_subsingleton]
  · apply Nat.succ_le_of_lt
    apply exponent_pos_of_exists 1 Nat.one_pos
    simp [eq_iff_true_of_subsingleton]
#align monoid.exp_eq_one_of_subsingleton Monoid.exp_eq_one_of_subsingleton
#align add_monoid.exp_eq_zero_of_subsingleton AddMonoid.exp_eq_zero_of_subsingleton

@[to_additive addOrder_dvd_exponent]
theorem order_dvd_exponent (g : G) : orderOf g ∣ exponent G :=
  orderOf_dvd_of_pow_eq_one <| pow_exponent_eq_one g
#align monoid.order_dvd_exponent Monoid.order_dvd_exponent
#align add_monoid.add_order_dvd_exponent AddMonoid.addOrder_dvd_exponent

variable (G)

@[to_additive]
theorem exponent_dvd_of_forall_pow_eq_one (G) [Monoid G] (n : ℕ) (hG : ∀ g : G, g ^ n = 1) :
    exponent G ∣ n := by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · exact dvd_zero _
  apply Nat.dvd_of_mod_eq_zero
  by_contra h
  have h₁ := Nat.pos_of_ne_zero h
  have h₂ : n % exponent G < exponent G := Nat.mod_lt _ (exponent_pos_of_exists n hpos hG)
  have h₃ : exponent G ≤ n % exponent G := by
    apply exponent_min' _ h₁
    simp_rw [← pow_eq_mod_exponent]
    exact hG
  linarith
#align monoid.exponent_dvd_of_forall_pow_eq_one Monoid.exponent_dvd_of_forall_pow_eq_one
#align add_monoid.exponent_dvd_of_forall_nsmul_eq_zero AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero

@[to_additive]
theorem lcm_orderOf_dvd_exponent [Fintype G] :
    (Finset.univ : Finset G).lcm orderOf ∣ exponent G := by
  apply Finset.lcm_dvd
  intro g _
  exact order_dvd_exponent g
#align monoid.lcm_order_of_dvd_exponent Monoid.lcm_orderOf_dvd_exponent
#align add_monoid.lcm_add_order_of_dvd_exponent AddMonoid.lcm_addOrderOf_dvd_exponent

@[to_additive exists_addOrderOf_eq_pow_padic_val_nat_add_exponent]
theorem _root_.Nat.Prime.exists_orderOf_eq_pow_factorization_exponent {p : ℕ} (hp : p.Prime) :
    ∃ g : G, orderOf g = p ^ (exponent G).factorization p := by
  haveI := Fact.mk hp
  rcases eq_or_ne ((exponent G).factorization p) 0 with (h | h)
  · refine' ⟨1, by rw [h, pow_zero, orderOf_one]⟩
  have he : 0 < exponent G :=
    Ne.bot_lt fun ht => by
      rw [ht] at h
      apply h
      rw [bot_eq_zero, Nat.factorization_zero, Finsupp.zero_apply]
  rw [← Finsupp.mem_support_iff] at h
  obtain ⟨g, hg⟩ : ∃ g : G, g ^ (exponent G / p) ≠ 1 := by
    suffices key : ¬exponent G ∣ exponent G / p
    · simpa using mt (exponent_dvd_of_forall_pow_eq_one G (exponent G / p)) key
    exact fun hd =>
      hp.one_lt.not_le
        ((mul_le_iff_le_one_left he).mp <|
          Nat.le_of_dvd he <| Nat.mul_dvd_of_dvd_div (Nat.dvd_of_mem_primeFactors h) hd)
  obtain ⟨k, hk : exponent G = p ^ _ * k⟩ := Nat.ord_proj_dvd _ _
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.mp h)
  refine' ⟨g ^ k, _⟩
  rw [ht]
  apply orderOf_eq_prime_pow
  · rwa [hk, mul_comm, ht, pow_succ', ← mul_assoc, Nat.mul_div_cancel _ hp.pos, pow_mul] at hg
  · rw [← Nat.succ_eq_add_one, ← ht, ← pow_mul, mul_comm, ← hk]
    exact pow_exponent_eq_one g
#align nat.prime.exists_order_of_eq_pow_factorization_exponent Nat.Prime.exists_orderOf_eq_pow_factorization_exponent
#align nat.prime.exists_order_of_eq_pow_padic_val_nat_add_exponent Nat.Prime.exists_addOrderOf_eq_pow_padic_val_nat_add_exponent

/-- A nontrivial monoid has prime exponent `p` if and only if every non-identity element has
order `p`. -/
@[to_additive]
lemma exponent_eq_prime_iff {G : Type*} [Monoid G] [Nontrivial G] {p : ℕ} (hp : p.Prime) :
    Monoid.exponent G = p ↔ ∀ g : G, g ≠ 1 → orderOf g = p := by
  refine ⟨fun hG g hg ↦ ?_, fun h ↦ dvd_antisymm ?_ ?_⟩
  · rw [Ne.def, ← orderOf_eq_one_iff] at hg
    exact Eq.symm <| (hp.dvd_iff_eq hg).mp <| hG ▸ Monoid.order_dvd_exponent g
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one G p fun g ↦ ?_
    by_cases hg : g = 1
    · simp [hg]
    · simpa [h g hg] using pow_orderOf_eq_one g
  · obtain ⟨g, hg⟩ := exists_ne (1 : G)
    simpa [h g hg] using Monoid.order_dvd_exponent g

variable {G}

@[to_additive]
theorem exponent_ne_zero_iff_range_orderOf_finite (h : ∀ g : G, 0 < orderOf g) :
    exponent G ≠ 0 ↔ (Set.range (orderOf : G → ℕ)).Finite := by
  refine' ⟨fun he => _, fun he => _⟩
  · by_contra h
    obtain ⟨m, ⟨t, rfl⟩, het⟩ := Set.Infinite.exists_gt h (exponent G)
    exact pow_ne_one_of_lt_orderOf' he het (pow_exponent_eq_one t)
  · lift Set.range (orderOf (G := G)) to Finset ℕ using he with t ht
    have htpos : 0 < t.prod id := by
      refine' Finset.prod_pos fun a ha => _
      rw [← Finset.mem_coe, ht] at ha
      obtain ⟨k, rfl⟩ := ha
      exact h k
    suffices exponent G ∣ t.prod id by
      intro h
      rw [h, zero_dvd_iff] at this
      exact htpos.ne' this
    refine' exponent_dvd_of_forall_pow_eq_one _ _ fun g => _
    rw [← pow_mod_orderOf, Nat.mod_eq_zero_of_dvd, pow_zero g]
    apply Finset.dvd_prod_of_mem
    rw [← Finset.mem_coe, ht]
    exact Set.mem_range_self g
#align monoid.exponent_ne_zero_iff_range_order_of_finite Monoid.exponent_ne_zero_iff_range_orderOf_finite
#align add_monoid.exponent_ne_zero_iff_range_order_of_finite AddMonoid.exponent_ne_zero_iff_range_addOrderOf_finite

@[to_additive]
theorem exponent_eq_zero_iff_range_orderOf_infinite (h : ∀ g : G, 0 < orderOf g) :
    exponent G = 0 ↔ (Set.range (orderOf : G → ℕ)).Infinite := by
  have := exponent_ne_zero_iff_range_orderOf_finite h
  rwa [Ne.def, not_iff_comm, Iff.comm] at this
#align monoid.exponent_eq_zero_iff_range_order_of_infinite Monoid.exponent_eq_zero_iff_range_orderOf_infinite
#align add_monoid.exponent_eq_zero_iff_range_order_of_infinite AddMonoid.exponent_eq_zero_iff_range_addOrderOf_infinite

@[to_additive lcm_addOrder_eq_exponent]
theorem lcm_order_eq_exponent [Fintype G] : (Finset.univ : Finset G).lcm orderOf = exponent G := by
  apply Nat.dvd_antisymm (lcm_orderOf_dvd_exponent G)
  refine' exponent_dvd_of_forall_pow_eq_one G _ fun g => _
  obtain ⟨m, hm⟩ : orderOf g ∣ Finset.univ.lcm orderOf := Finset.dvd_lcm (Finset.mem_univ g)
  rw [hm, pow_mul, pow_orderOf_eq_one, one_pow]
#align monoid.lcm_order_eq_exponent Monoid.lcm_order_eq_exponent
#align add_monoid.lcm_add_order_eq_exponent AddMonoid.lcm_addOrder_eq_exponent

end Monoid

section LeftCancelMonoid

variable [LeftCancelMonoid G]

@[to_additive]
theorem exponent_ne_zero_of_finite [Finite G] : exponent G ≠ 0 := by
  cases nonempty_fintype G
  simpa [← lcm_order_eq_exponent, Finset.lcm_eq_zero_iff] using fun x => (orderOf_pos x).ne'
#align monoid.exponent_ne_zero_of_finite Monoid.exponent_ne_zero_of_finite
#align add_monoid.exponent_ne_zero_of_finite AddMonoid.exponent_ne_zero_of_finite

end LeftCancelMonoid

section CommMonoid

variable [CommMonoid G]

@[to_additive]
theorem exponent_eq_iSup_orderOf (h : ∀ g : G, 0 < orderOf g) :
    exponent G = ⨆ g : G, orderOf g := by
  rw [iSup]
  rcases eq_or_ne (exponent G) 0 with (he | he)
  · rw [he, Set.Infinite.Nat.sSup_eq_zero <| (exponent_eq_zero_iff_range_orderOf_infinite h).1 he]
  have hne : (Set.range (orderOf : G → ℕ)).Nonempty := ⟨1, 1, orderOf_one⟩
  have hfin : (Set.range (orderOf : G → ℕ)).Finite := by
    rwa [← exponent_ne_zero_iff_range_orderOf_finite h]
  obtain ⟨t, ht⟩ := hne.cSup_mem hfin
  apply Nat.dvd_antisymm _
  · rw [← ht]
    apply order_dvd_exponent
  refine' Nat.dvd_of_factors_subperm he _
  rw [List.subperm_ext_iff]
  by_contra! h
  obtain ⟨p, hp, hpe⟩ := h
  replace hp := Nat.prime_of_mem_factors hp
  simp only [Nat.factors_count_eq] at hpe
  set k := (orderOf t).factorization p with hk
  obtain ⟨g, hg⟩ := hp.exists_orderOf_eq_pow_factorization_exponent G
  suffices orderOf t < orderOf (t ^ p ^ k * g) by
    rw [ht] at this
    exact this.not_le (le_csSup hfin.bddAbove <| Set.mem_range_self _)
  have hpk : p ^ k ∣ orderOf t := Nat.ord_proj_dvd _ _
  have hpk' : orderOf (t ^ p ^ k) = orderOf t / p ^ k := by
    rw [orderOf_pow' t (pow_ne_zero k hp.ne_zero), Nat.gcd_eq_right hpk]
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_lt hpe
  have hcoprime : (orderOf (t ^ p ^ k)).Coprime (orderOf g) := by
    rw [hg, Nat.coprime_pow_right_iff (pos_of_gt hpe), Nat.coprime_comm]
    apply Or.resolve_right (Nat.coprime_or_dvd_of_prime hp _)
    nth_rw 1 [← pow_one p]
    have : 1 = (Nat.factorization (orderOf (t ^ p ^ k))) p + 1 := by
     rw [hpk', Nat.factorization_div hpk]
     simp [hp]
    rw [this]
    -- Porting note: convert made to_additive complain
    apply Nat.pow_succ_factorization_not_dvd (h <| t ^ p ^ k).ne' hp
  rw [(Commute.all _ g).orderOf_mul_eq_mul_orderOf_of_coprime hcoprime, hpk',
    hg, ha, ← ht, ← hk, pow_add, pow_add, pow_one, ← mul_assoc, ← mul_assoc,
    Nat.div_mul_cancel, mul_assoc, lt_mul_iff_one_lt_right <| h t, ← pow_succ']
  exact one_lt_pow hp.one_lt a.succ_ne_zero
  exact hpk
#align monoid.exponent_eq_supr_order_of Monoid.exponent_eq_iSup_orderOf
#align add_monoid.exponent_eq_supr_order_of AddMonoid.exponent_eq_iSup_addOrderOf

@[to_additive]
theorem exponent_eq_iSup_orderOf' :
    exponent G = if ∃ g : G, orderOf g = 0 then 0 else ⨆ g : G, orderOf g := by
  split_ifs with h
  · obtain ⟨g, hg⟩ := h
    exact exponent_eq_zero_of_order_zero hg
  · have := not_exists.mp h
    exact exponent_eq_iSup_orderOf fun g => Ne.bot_lt <| this g
#align monoid.exponent_eq_supr_order_of' Monoid.exponent_eq_iSup_orderOf'
#align add_monoid.exponent_eq_supr_order_of' AddMonoid.exponent_eq_iSup_addOrderOf'

end CommMonoid

section CancelCommMonoid

variable [CancelCommMonoid G]

@[to_additive]
theorem exponent_eq_max'_orderOf [Fintype G] :
    exponent G = ((@Finset.univ G _).image orderOf).max' ⟨1, by simp⟩ := by
  rw [← Finset.Nonempty.cSup_eq_max', Finset.coe_image, Finset.coe_univ, Set.image_univ, ← iSup]
  exact exponent_eq_iSup_orderOf orderOf_pos
#align monoid.exponent_eq_max'_order_of Monoid.exponent_eq_max'_orderOf
#align add_monoid.exponent_eq_max'_order_of AddMonoid.exponent_eq_max'_addOrderOf

end CancelCommMonoid

end Monoid

section Group

@[to_additive AddGroup.one_lt_exponent]
lemma Group.one_lt_exponent [Group G] [Finite G] [Nontrivial G] :
    1 < Monoid.exponent G := by
  let _inst := Fintype.ofFinite G
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  rw [← Monoid.lcm_order_eq_exponent]
  have hg' : 2 ≤ orderOf g := Nat.lt_of_le_of_ne (orderOf_pos g) <| by
    simpa [eq_comm, orderOf_eq_one_iff] using hg
  refine hg'.trans <| Nat.le_of_dvd ?_ <| Finset.dvd_lcm (by simp)
  rw [Nat.pos_iff_ne_zero, Ne.def, Finset.lcm_eq_zero_iff]
  rintro ⟨x, -, hx⟩
  exact (orderOf_pos x).ne' hx

end Group

section CommGroup

open Subgroup

open BigOperators

variable (G) [CommGroup G] [Group.FG G]

@[to_additive]
theorem card_dvd_exponent_pow_rank : Nat.card G ∣ Monoid.exponent G ^ Group.rank G := by
  obtain ⟨S, hS1, hS2⟩ := Group.rank_spec G
  rw [← hS1, ← Fintype.card_coe, ← Finset.card_univ, ← Finset.prod_const]
  let f : (∀ g : S, zpowers (g : G)) →* G := noncommPiCoprod fun s t _ x y _ _ => mul_comm x _
  have hf : Function.Surjective f := by
    rw [← MonoidHom.range_top_iff_surjective, eq_top_iff, ← hS2, closure_le]
    exact fun g hg => ⟨Pi.mulSingle ⟨g, hg⟩ ⟨g, mem_zpowers g⟩, noncommPiCoprod_mulSingle _ _⟩
  replace hf := nat_card_dvd_of_surjective f hf
  rw [Nat.card_pi] at hf
  refine' hf.trans (Finset.prod_dvd_prod_of_dvd _ _ fun g _ => _)
  rw [Nat.card_zpowers]
  exact Monoid.order_dvd_exponent (g : G)
#align card_dvd_exponent_pow_rank card_dvd_exponent_pow_rank
#align card_dvd_exponent_nsmul_rank card_dvd_exponent_nsmul_rank

@[to_additive]
theorem card_dvd_exponent_pow_rank' {n : ℕ} (hG : ∀ g : G, g ^ n = 1) :
    Nat.card G ∣ n ^ Group.rank G :=
  (card_dvd_exponent_pow_rank G).trans
    (pow_dvd_pow_of_dvd (Monoid.exponent_dvd_of_forall_pow_eq_one G n hG) (Group.rank G))
#align card_dvd_exponent_pow_rank' card_dvd_exponent_pow_rank'
#align card_dvd_exponent_nsmul_rank' card_dvd_exponent_nsmul_rank'

end CommGroup

section PiProd

open Finset Monoid

@[to_additive]
theorem Monoid.exponent_pi_eq_zero {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)] {j : ι}
    (hj : exponent (M j) = 0) : exponent ((i : ι) → M i) = 0 := by
  rw [@exponent_eq_zero_iff, ExponentExists] at hj ⊢
  push_neg at hj ⊢
  peel hj with n hn _
  obtain ⟨m, hm⟩ := this
  refine ⟨Pi.mulSingle j m, fun h ↦ hm ?_⟩
  simpa using congr_fun h j

/-- If `f : M₁ →⋆ M₂` is surjective, then the exponent of `M₂` divides the exponent of `M₁`. -/
@[to_additive]
theorem MonoidHom.exponent_dvd {F M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂]
    [FunLike F M₁ M₂] [MonoidHomClass F M₁ M₂]
    {f : F} (hf : Function.Surjective f) : exponent M₂ ∣ exponent M₁ := by
  refine Monoid.exponent_dvd_of_forall_pow_eq_one M₂ _ fun m₂ ↦ ?_
  obtain ⟨m₁, rfl⟩ := hf m₂
  rw [← map_pow, pow_exponent_eq_one, map_one]

/-- The exponent of finite product of monoids is the `Finset.lcm` of the exponents of the
constituent monoids. -/
@[to_additive "The exponent of finite product of additive monoids is the `Finset.lcm` of the
exponents of the constituent additive monoids."]
theorem Monoid.exponent_pi {ι : Type*} [Fintype ι] {M : ι → Type*} [∀ i, Monoid (M i)] :
    exponent ((i : ι) → M i) = lcm univ (exponent <| M ·) := by
  refine dvd_antisymm ?_ ?_
  · refine exponent_dvd_of_forall_pow_eq_one _ _ fun m ↦ ?_
    ext i
    rw [Pi.pow_apply, Pi.one_apply, ← orderOf_dvd_iff_pow_eq_one]
    apply dvd_trans (Monoid.order_dvd_exponent (m i))
    exact Finset.dvd_lcm (mem_univ i)
  · apply Finset.lcm_dvd fun i _ ↦ ?_
    exact MonoidHom.exponent_dvd (f := Pi.evalMonoidHom (M ·) i) (Function.surjective_eval i)

/-- The exponent of product of two monoids is the `lcm` of the exponents of the
individuaul monoids. -/
@[to_additive AddMonoid.exponent_prod "The exponent of product of two additive monoids is the `lcm`
of the exponents of the individuaul additive monoids."]
theorem Monoid.exponent_prod {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] :
    exponent (M₁ × M₂) = lcm (exponent M₁) (exponent M₂) := by
  refine dvd_antisymm ?_ (lcm_dvd ?_ ?_)
  · refine exponent_dvd_of_forall_pow_eq_one _ _ fun g ↦ ?_
    ext1
    · rw [Prod.pow_fst, Prod.fst_one, ← orderOf_dvd_iff_pow_eq_one]
      exact dvd_trans (Monoid.order_dvd_exponent (g.1)) <| dvd_lcm_left _ _
    · rw [Prod.pow_snd, Prod.snd_one, ← orderOf_dvd_iff_pow_eq_one]
      exact dvd_trans (Monoid.order_dvd_exponent (g.2)) <| dvd_lcm_right _ _
  · exact MonoidHom.exponent_dvd (f := MonoidHom.fst M₁ M₂) Prod.fst_surjective
  · exact MonoidHom.exponent_dvd (f := MonoidHom.snd M₁ M₂) Prod.snd_surjective

end PiProd
