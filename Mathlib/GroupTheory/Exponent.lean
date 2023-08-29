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

@[to_additive]
theorem exponentExists_iff_ne_zero : ExponentExists G ↔ exponent G ≠ 0 := by
  rw [exponent]
  -- ⊢ ExponentExists G ↔ (if h : ExponentExists G then Nat.find h else 0) ≠ 0
  split_ifs with h
  -- ⊢ ExponentExists G ↔ Nat.find h ≠ 0
  · simp [h, @not_lt_zero' ℕ]
    -- 🎉 no goals
  --if this isn't done this way, `to_additive` freaks
  · tauto
    -- 🎉 no goals
#align monoid.exponent_exists_iff_ne_zero Monoid.exponentExists_iff_ne_zero
#align add_monoid.exponent_exists_iff_ne_zero AddMonoid.exponentExists_iff_ne_zero

@[to_additive]
theorem exponent_eq_zero_iff : exponent G = 0 ↔ ¬ExponentExists G := by
  simp only [exponentExists_iff_ne_zero, Classical.not_not]
  -- 🎉 no goals
#align monoid.exponent_eq_zero_iff Monoid.exponent_eq_zero_iff
#align add_monoid.exponent_eq_zero_iff AddMonoid.exponent_eq_zero_iff

@[to_additive exponent_eq_zero_addOrder_zero]
theorem exponent_eq_zero_of_order_zero {g : G} (hg : orderOf g = 0) : exponent G = 0 :=
  exponent_eq_zero_iff.mpr fun ⟨n, hn, hgn⟩ => orderOf_eq_zero_iff'.mp hg n hn <| hgn g
#align monoid.exponent_eq_zero_of_order_zero Monoid.exponent_eq_zero_of_order_zero
#align add_monoid.exponent_eq_zero_of_order_zero AddMonoid.exponent_eq_zero_addOrder_zero

@[to_additive exponent_nsmul_eq_zero]
theorem pow_exponent_eq_one (g : G) : g ^ exponent G = 1 := by
  by_cases ExponentExists G
  -- ⊢ g ^ exponent G = 1
  -- ⊢ g ^ exponent G = 1
  · simp_rw [exponent, dif_pos h]
    -- ⊢ g ^ Nat.find h = 1
    exact (Nat.find_spec h).2 g
    -- 🎉 no goals
  · simp_rw [exponent, dif_neg h, pow_zero]
    -- 🎉 no goals
#align monoid.pow_exponent_eq_one Monoid.pow_exponent_eq_one
#align add_monoid.exponent_nsmul_eq_zero AddMonoid.exponent_nsmul_eq_zero

@[to_additive]
theorem pow_eq_mod_exponent {n : ℕ} (g : G) : g ^ n = g ^ (n % exponent G) :=
  calc
    g ^ n = g ^ (n % exponent G + exponent G * (n / exponent G)) := by rw [Nat.mod_add_div]
                                                                       -- 🎉 no goals
    _ = g ^ (n % exponent G) := by simp [pow_add, pow_mul, pow_exponent_eq_one]
                                   -- 🎉 no goals

#align monoid.pow_eq_mod_exponent Monoid.pow_eq_mod_exponent
#align add_monoid.nsmul_eq_mod_exponent AddMonoid.nsmul_eq_mod_exponent

@[to_additive]
theorem exponent_pos_of_exists (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, g ^ n = 1) :
    0 < exponent G := by
  have h : ∃ n, 0 < n ∧ ∀ g : G, g ^ n = 1 := ⟨n, hpos, hG⟩
  -- ⊢ 0 < exponent G
  rw [exponent, dif_pos]
  -- ⊢ 0 < Nat.find ?hc
  exact (Nat.find_spec h).1
  -- 🎉 no goals
#align monoid.exponent_pos_of_exists Monoid.exponent_pos_of_exists
#align add_monoid.exponent_pos_of_exists AddMonoid.exponent_pos_of_exists

@[to_additive]
theorem exponent_min' (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, g ^ n = 1) : exponent G ≤ n := by
  rw [exponent, dif_pos]
  -- ⊢ Nat.find ?hc ≤ n
  · apply Nat.find_min'
    -- ⊢ 0 < n ∧ ∀ (g : G), g ^ n = 1
    exact ⟨hpos, hG⟩
    -- 🎉 no goals
  · exact ⟨n, hpos, hG⟩
    -- 🎉 no goals
#align monoid.exponent_min' Monoid.exponent_min'
#align add_monoid.exponent_min' AddMonoid.exponent_min'

@[to_additive]
theorem exponent_min (m : ℕ) (hpos : 0 < m) (hm : m < exponent G) : ∃ g : G, g ^ m ≠ 1 := by
  by_contra' h
  -- ⊢ False
  have hcon : exponent G ≤ m := exponent_min' m hpos h
  -- ⊢ False
  linarith
  -- 🎉 no goals
#align monoid.exponent_min Monoid.exponent_min
#align add_monoid.exponent_min AddMonoid.exponent_min

@[to_additive (attr := simp)]
theorem exp_eq_one_of_subsingleton [Subsingleton G] : exponent G = 1 := by
  apply le_antisymm
  -- ⊢ exponent G ≤ 1
  · apply exponent_min' _ Nat.one_pos
    -- ⊢ ∀ (g : G), g ^ 1 = 1
    simp
    -- 🎉 no goals
  · apply Nat.succ_le_of_lt
    -- ⊢ 0 < exponent G
    apply exponent_pos_of_exists 1 Nat.one_pos
    -- ⊢ ∀ (g : G), g ^ 1 = 1
    simp
    -- 🎉 no goals
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
  -- ⊢ exponent G ∣ 0
  · exact dvd_zero _
    -- 🎉 no goals
  apply Nat.dvd_of_mod_eq_zero
  -- ⊢ n % exponent G = 0
  by_contra h
  -- ⊢ False
  have h₁ := Nat.pos_of_ne_zero h
  -- ⊢ False
  have h₂ : n % exponent G < exponent G := Nat.mod_lt _ (exponent_pos_of_exists n hpos hG)
  -- ⊢ False
  have h₃ : exponent G ≤ n % exponent G := by
    apply exponent_min' _ h₁
    simp_rw [← pow_eq_mod_exponent]
    exact hG
  linarith
  -- 🎉 no goals
#align monoid.exponent_dvd_of_forall_pow_eq_one Monoid.exponent_dvd_of_forall_pow_eq_one
#align add_monoid.exponent_dvd_of_forall_nsmul_eq_zero AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero

@[to_additive]
theorem lcm_orderOf_dvd_exponent [Fintype G] :
    (Finset.univ : Finset G).lcm orderOf ∣ exponent G := by
  apply Finset.lcm_dvd
  -- ⊢ ∀ (b : G), b ∈ Finset.univ → orderOf b ∣ exponent G
  intro g _
  -- ⊢ orderOf g ∣ exponent G
  exact order_dvd_exponent g
  -- 🎉 no goals
#align monoid.lcm_order_of_dvd_exponent Monoid.lcm_orderOf_dvd_exponent
#align add_monoid.lcm_add_order_of_dvd_exponent AddMonoid.lcm_addOrderOf_dvd_exponent

@[to_additive exists_addOrderOf_eq_pow_padic_val_nat_add_exponent]
theorem _root_.Nat.Prime.exists_orderOf_eq_pow_factorization_exponent {p : ℕ} (hp : p.Prime) :
    ∃ g : G, orderOf g = p ^ (exponent G).factorization p := by
  haveI := Fact.mk hp
  -- ⊢ ∃ g, orderOf g = p ^ ↑(Nat.factorization (exponent G)) p
  rcases eq_or_ne ((exponent G).factorization p) 0 with (h | h)
  -- ⊢ ∃ g, orderOf g = p ^ ↑(Nat.factorization (exponent G)) p
  · refine' ⟨1, by rw [h, pow_zero, orderOf_one]⟩
    -- 🎉 no goals
  have he : 0 < exponent G :=
    Ne.bot_lt fun ht => by
      rw [ht] at h
      apply h
      rw [bot_eq_zero, Nat.factorization_zero, Finsupp.zero_apply]
  rw [← Finsupp.mem_support_iff] at h
  -- ⊢ ∃ g, orderOf g = p ^ ↑(Nat.factorization (exponent G)) p
  obtain ⟨g, hg⟩ : ∃ g : G, g ^ (exponent G / p) ≠ 1 := by
    suffices key : ¬exponent G ∣ exponent G / p
    · simpa using mt (exponent_dvd_of_forall_pow_eq_one G (exponent G / p)) key
    exact fun hd =>
      hp.one_lt.not_le
        ((mul_le_iff_le_one_left he).mp <|
          Nat.le_of_dvd he <| Nat.mul_dvd_of_dvd_div (Nat.dvd_of_mem_factorization h) hd)
  obtain ⟨k, hk : exponent G = p ^ _ * k⟩ := Nat.ord_proj_dvd _ _
  -- ⊢ ∃ g, orderOf g = p ^ ↑(Nat.factorization (exponent G)) p
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.mp h)
  -- ⊢ ∃ g, orderOf g = p ^ ↑(Nat.factorization (exponent G)) p
  refine' ⟨g ^ k, _⟩
  -- ⊢ orderOf (g ^ k) = p ^ ↑(Nat.factorization (exponent G)) p
  rw [ht]
  -- ⊢ orderOf (g ^ k) = p ^ Nat.succ t
  apply orderOf_eq_prime_pow
  -- ⊢ ¬(g ^ k) ^ p ^ t = 1
  · rwa [hk, mul_comm, ht, pow_succ', ← mul_assoc, Nat.mul_div_cancel _ hp.pos, pow_mul] at hg
    -- 🎉 no goals
  · rw [← Nat.succ_eq_add_one, ← ht, ← pow_mul, mul_comm, ← hk]
    -- ⊢ g ^ exponent G = 1
    exact pow_exponent_eq_one g
    -- 🎉 no goals
#align nat.prime.exists_order_of_eq_pow_factorization_exponent Nat.Prime.exists_orderOf_eq_pow_factorization_exponent
#align nat.prime.exists_order_of_eq_pow_padic_val_nat_add_exponent Nat.Prime.exists_addOrderOf_eq_pow_padic_val_nat_add_exponent

variable {G}

@[to_additive]
theorem exponent_ne_zero_iff_range_orderOf_finite (h : ∀ g : G, 0 < orderOf g) :
    exponent G ≠ 0 ↔ (Set.range (orderOf : G → ℕ)).Finite := by
  refine' ⟨fun he => _, fun he => _⟩
  -- ⊢ Set.Finite (Set.range orderOf)
  · by_contra h
    -- ⊢ False
    obtain ⟨m, ⟨t, rfl⟩, het⟩ := Set.Infinite.exists_gt h (exponent G)
    -- ⊢ False
    exact pow_ne_one_of_lt_orderOf' he het (pow_exponent_eq_one t)
    -- 🎉 no goals
  · lift Set.range (orderOf (G := G)) to Finset ℕ using he with t ht
    -- ⊢ exponent G ≠ 0
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
    -- ⊢ g ^ Finset.prod t id = 1
    rw [pow_eq_mod_orderOf, Nat.mod_eq_zero_of_dvd, pow_zero g]
    -- ⊢ orderOf g ∣ Finset.prod t id
    apply Finset.dvd_prod_of_mem
    -- ⊢ Function.minimalPeriod (fun x => g * x) 1 ∈ t
    rw [← Finset.mem_coe, ht]
    -- ⊢ Function.minimalPeriod (fun x => g * x) 1 ∈ Set.range orderOf
    exact Set.mem_range_self g
    -- 🎉 no goals
#align monoid.exponent_ne_zero_iff_range_order_of_finite Monoid.exponent_ne_zero_iff_range_orderOf_finite
#align add_monoid.exponent_ne_zero_iff_range_order_of_finite AddMonoid.exponent_ne_zero_iff_range_addOrderOf_finite

@[to_additive]
theorem exponent_eq_zero_iff_range_orderOf_infinite (h : ∀ g : G, 0 < orderOf g) :
    exponent G = 0 ↔ (Set.range (orderOf : G → ℕ)).Infinite := by
  have := exponent_ne_zero_iff_range_orderOf_finite h
  -- ⊢ exponent G = 0 ↔ Set.Infinite (Set.range orderOf)
  rwa [Ne.def, not_iff_comm, Iff.comm] at this
  -- 🎉 no goals
#align monoid.exponent_eq_zero_iff_range_order_of_infinite Monoid.exponent_eq_zero_iff_range_orderOf_infinite
#align add_monoid.exponent_eq_zero_iff_range_order_of_infinite AddMonoid.exponent_eq_zero_iff_range_addOrderOf_infinite

@[to_additive lcm_addOrder_eq_exponent]
theorem lcm_order_eq_exponent [Fintype G] : (Finset.univ : Finset G).lcm orderOf = exponent G := by
  apply Nat.dvd_antisymm (lcm_orderOf_dvd_exponent G)
  -- ⊢ exponent G ∣ Finset.lcm Finset.univ orderOf
  refine' exponent_dvd_of_forall_pow_eq_one G _ fun g => _
  -- ⊢ g ^ Finset.lcm Finset.univ orderOf = 1
  obtain ⟨m, hm⟩ : orderOf g ∣ Finset.univ.lcm orderOf := Finset.dvd_lcm (Finset.mem_univ g)
  -- ⊢ g ^ Finset.lcm Finset.univ orderOf = 1
  rw [hm, pow_mul, pow_orderOf_eq_one, one_pow]
  -- 🎉 no goals
#align monoid.lcm_order_eq_exponent Monoid.lcm_order_eq_exponent
#align add_monoid.lcm_add_order_eq_exponent AddMonoid.lcm_addOrder_eq_exponent

end Monoid

section LeftCancelMonoid

variable [LeftCancelMonoid G]

@[to_additive]
theorem exponent_ne_zero_of_finite [Finite G] : exponent G ≠ 0 := by
  cases nonempty_fintype G
  -- ⊢ exponent G ≠ 0
  simpa [← lcm_order_eq_exponent, Finset.lcm_eq_zero_iff] using fun x => (orderOf_pos x).ne'
  -- 🎉 no goals
#align monoid.exponent_ne_zero_of_finite Monoid.exponent_ne_zero_of_finite
#align add_monoid.exponent_ne_zero_of_finite AddMonoid.exponent_ne_zero_of_finite

end LeftCancelMonoid

section CommMonoid

variable [CommMonoid G]

@[to_additive]
theorem exponent_eq_iSup_orderOf (h : ∀ g : G, 0 < orderOf g) :
    exponent G = ⨆ g : G, orderOf g := by
  rw [iSup]
  -- ⊢ exponent G = sSup (Set.range fun g => orderOf g)
  rcases eq_or_ne (exponent G) 0 with (he | he)
  -- ⊢ exponent G = sSup (Set.range fun g => orderOf g)
  · rw [he, Set.Infinite.Nat.sSup_eq_zero <| (exponent_eq_zero_iff_range_orderOf_infinite h).1 he]
    -- 🎉 no goals
  have hne : (Set.range (orderOf : G → ℕ)).Nonempty := ⟨1, 1, orderOf_one⟩
  -- ⊢ exponent G = sSup (Set.range fun g => orderOf g)
  have hfin : (Set.range (orderOf : G → ℕ)).Finite := by
    rwa [← exponent_ne_zero_iff_range_orderOf_finite h]
  obtain ⟨t, ht⟩ := hne.cSup_mem hfin
  -- ⊢ exponent G = sSup (Set.range fun g => orderOf g)
  apply Nat.dvd_antisymm _
  -- ⊢ sSup (Set.range fun g => orderOf g) ∣ exponent G
  · rw [← ht]
    -- ⊢ orderOf t ∣ exponent G
    apply order_dvd_exponent
    -- 🎉 no goals
  refine' Nat.dvd_of_factors_subperm he _
  -- ⊢ Nat.factors (exponent G) <+~ Nat.factors (sSup (Set.range fun g => orderOf g))
  rw [List.subperm_ext_iff]
  -- ⊢ ∀ (x : ℕ), x ∈ Nat.factors (exponent G) → List.count x (Nat.factors (exponen …
  by_contra' h
  -- ⊢ False
  obtain ⟨p, hp, hpe⟩ := h
  -- ⊢ False
  replace hp := Nat.prime_of_mem_factors hp
  -- ⊢ False
  simp only [Nat.factors_count_eq] at hpe
  -- ⊢ False
  set k := (orderOf t).factorization p with hk
  -- ⊢ False
  obtain ⟨g, hg⟩ := hp.exists_orderOf_eq_pow_factorization_exponent G
  -- ⊢ False
  suffices orderOf t < orderOf (t ^ p ^ k * g) by
    rw [ht] at this
    exact this.not_le (le_csSup hfin.bddAbove <| Set.mem_range_self _)
  have hpk : p ^ k ∣ orderOf t := Nat.ord_proj_dvd _ _
  -- ⊢ orderOf t < orderOf (t ^ p ^ k * g)
  have hpk' : orderOf (t ^ p ^ k) = orderOf t / p ^ k := by
    rw [orderOf_pow' t (pow_ne_zero k hp.ne_zero), Nat.gcd_eq_right hpk]
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_lt hpe
  -- ⊢ orderOf t < orderOf (t ^ p ^ k * g)
  have hcoprime : (orderOf (t ^ p ^ k)).coprime (orderOf g) := by
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
  -- ⊢ p ^ k ∣ orderOf t
  exact hpk
  -- 🎉 no goals
#align monoid.exponent_eq_supr_order_of Monoid.exponent_eq_iSup_orderOf
#align add_monoid.exponent_eq_supr_order_of AddMonoid.exponent_eq_iSup_addOrderOf

@[to_additive]
theorem exponent_eq_iSup_orderOf' :
    exponent G = if ∃ g : G, orderOf g = 0 then 0 else ⨆ g : G, orderOf g := by
  split_ifs with h
  -- ⊢ exponent G = 0
  · obtain ⟨g, hg⟩ := h
    -- ⊢ exponent G = 0
    exact exponent_eq_zero_of_order_zero hg
    -- 🎉 no goals
  · have := not_exists.mp h
    -- ⊢ exponent G = ⨆ (g : G), orderOf g
    exact exponent_eq_iSup_orderOf fun g => Ne.bot_lt <| this g
    -- 🎉 no goals
#align monoid.exponent_eq_supr_order_of' Monoid.exponent_eq_iSup_orderOf'
#align add_monoid.exponent_eq_supr_order_of' AddMonoid.exponent_eq_iSup_addOrderOf'

end CommMonoid

section CancelCommMonoid

variable [CancelCommMonoid G]

@[to_additive]
theorem exponent_eq_max'_orderOf [Fintype G] :
    exponent G = ((@Finset.univ G _).image orderOf).max' ⟨1, by simp⟩ := by
                                                                -- 🎉 no goals
  rw [← Finset.Nonempty.cSup_eq_max', Finset.coe_image, Finset.coe_univ, Set.image_univ, ← iSup]
  -- ⊢ exponent G = iSup orderOf
  exact exponent_eq_iSup_orderOf orderOf_pos
  -- 🎉 no goals
#align monoid.exponent_eq_max'_order_of Monoid.exponent_eq_max'_orderOf
#align add_monoid.exponent_eq_max'_order_of AddMonoid.exponent_eq_max'_addOrderOf

end CancelCommMonoid

end Monoid

section CommGroup

open Subgroup

open BigOperators

variable (G) [CommGroup G] [Group.FG G]

@[to_additive]
theorem card_dvd_exponent_pow_rank : Nat.card G ∣ Monoid.exponent G ^ Group.rank G := by
  obtain ⟨S, hS1, hS2⟩ := Group.rank_spec G
  -- ⊢ Nat.card G ∣ Monoid.exponent G ^ Group.rank G
  rw [← hS1, ← Fintype.card_coe, ← Finset.card_univ, ← Finset.prod_const]
  -- ⊢ Nat.card G ∣ ∏ _x : { x // x ∈ S }, Monoid.exponent G
  let f : (∀ g : S, zpowers (g : G)) →* G := noncommPiCoprod fun s t _ x y _ _ => mul_comm x _
  -- ⊢ Nat.card G ∣ ∏ _x : { x // x ∈ S }, Monoid.exponent G
  have hf : Function.Surjective f := by
    rw [← MonoidHom.range_top_iff_surjective, eq_top_iff, ← hS2, closure_le]
    exact fun g hg => ⟨Pi.mulSingle ⟨g, hg⟩ ⟨g, mem_zpowers g⟩, noncommPiCoprod_mulSingle _ _⟩
  replace hf := nat_card_dvd_of_surjective f hf
  -- ⊢ Nat.card G ∣ ∏ _x : { x // x ∈ S }, Monoid.exponent G
  rw [Nat.card_pi] at hf
  -- ⊢ Nat.card G ∣ ∏ _x : { x // x ∈ S }, Monoid.exponent G
  refine' hf.trans (Finset.prod_dvd_prod_of_dvd _ _ fun g _ => _)
  -- ⊢ Nat.card { x // x ∈ zpowers ↑g } ∣ Monoid.exponent G
  rw [← order_eq_card_zpowers']
  -- ⊢ orderOf ↑g ∣ Monoid.exponent G
  exact Monoid.order_dvd_exponent (g : G)
  -- 🎉 no goals
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

