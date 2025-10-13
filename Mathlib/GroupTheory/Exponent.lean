/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorization.LCM
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Peel

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

namespace Monoid

section Monoid

variable (G) [Monoid G]

/-- A predicate on a monoid saying that there is a positive integer `n` such that `g ^ n = 1`
for all `g`. -/
@[to_additive
/-- A predicate on an additive monoid saying that there is a positive integer `n` such that
`n • g = 0` for all `g`. -/]
def ExponentExists :=
  ∃ n, 0 < n ∧ ∀ g : G, g ^ n = 1

open scoped Classical in
/-- The exponent of a group is the smallest positive integer `n` such that `g ^ n = 1` for all
`g ∈ G` if it exists, otherwise it is zero by convention. -/
@[to_additive
/-- The exponent of an additive group is the smallest positive integer `n` such that
`n • g = 0` for all `g ∈ G` if it exists, otherwise it is zero by convention. -/]
noncomputable def exponent :=
  if h : ExponentExists G then Nat.find h else 0

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
  all_goals exact ⟨(op_injective <| · <| op ·), (unop_injective <| · <| unop ·)⟩

@[to_additive]
theorem ExponentExists.isOfFinOrder (h : ExponentExists G) {g : G} : IsOfFinOrder g :=
  isOfFinOrder_iff_pow_eq_one.mpr <| by peel 2 h; exact this g

@[to_additive]
theorem ExponentExists.orderOf_pos (h : ExponentExists G) (g : G) : 0 < orderOf g :=
  h.isOfFinOrder.orderOf_pos

@[to_additive]
theorem exponent_ne_zero : exponent G ≠ 0 ↔ ExponentExists G := by
  rw [exponent]
  split_ifs with h
  · simp [h]
  --if this isn't done this way, `to_additive` freaks
  · tauto

@[to_additive]
protected alias ⟨_, ExponentExists.exponent_ne_zero⟩ := exponent_ne_zero

@[to_additive]
theorem exponent_pos : 0 < exponent G ↔ ExponentExists G :=
  pos_iff_ne_zero.trans exponent_ne_zero

@[to_additive]
protected alias ⟨_, ExponentExists.exponent_pos⟩ := exponent_pos

@[to_additive]
theorem exponent_eq_zero_iff : exponent G = 0 ↔ ¬ExponentExists G :=
  exponent_ne_zero.not_right

@[to_additive exponent_eq_zero_addOrder_zero]
theorem exponent_eq_zero_of_order_zero {g : G} (hg : orderOf g = 0) : exponent G = 0 :=
  exponent_eq_zero_iff.mpr fun h ↦ h.orderOf_pos g |>.ne' hg

@[to_additive]
theorem exponent_eq_sInf :
    Monoid.exponent G = sInf {d : ℕ | 0 < d ∧ ∀ x : G, x ^ d = 1} := by
  by_cases h : Monoid.ExponentExists G
  · have h' : {d : ℕ | 0 < d ∧ ∀ x : G, x ^ d = 1}.Nonempty := h
    rw [Monoid.exponent, dif_pos h, Nat.sInf_def h']
    congr
  · have : {d | 0 < d ∧ ∀ (x : G), x ^ d = 1} = ∅ :=
      Set.eq_empty_of_forall_notMem fun n hn ↦ h ⟨n, hn⟩
    rw [Monoid.exponent_eq_zero_iff.mpr h, this, Nat.sInf_empty]

/-- The exponent is zero iff for all nonzero `n`, one can find a `g` such that `g ^ n ≠ 1`. -/
@[to_additive /-- The exponent is zero iff for all nonzero `n`, one can find a `g` such that
`n • g ≠ 0`. -/]
theorem exponent_eq_zero_iff_forall : exponent G = 0 ↔ ∀ n > 0, ∃ g : G, g ^ n ≠ 1 := by
  rw [exponent_eq_zero_iff, ExponentExists]
  push_neg
  rfl

@[to_additive exponent_nsmul_eq_zero]
theorem pow_exponent_eq_one (g : G) : g ^ exponent G = 1 := by
  classical
  by_cases h : ExponentExists G
  · simp_rw [exponent, dif_pos h]
    exact (Nat.find_spec h).2 g
  · simp_rw [exponent, dif_neg h, pow_zero]

@[to_additive]
theorem pow_eq_mod_exponent {n : ℕ} (g : G) : g ^ n = g ^ (n % exponent G) :=
  calc
    g ^ n = g ^ (n % exponent G + exponent G * (n / exponent G)) := by rw [Nat.mod_add_div]
    _ = g ^ (n % exponent G) := by simp [pow_add, pow_mul, pow_exponent_eq_one]

@[to_additive]
theorem exponent_pos_of_exists (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, g ^ n = 1) :
    0 < exponent G :=
  ExponentExists.exponent_pos ⟨n, hpos, hG⟩

@[to_additive]
theorem exponent_min' (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, g ^ n = 1) : exponent G ≤ n := by
  classical
  rw [exponent, dif_pos]
  · apply Nat.find_min'
    exact ⟨hpos, hG⟩
  · exact ⟨n, hpos, hG⟩

@[to_additive]
theorem exponent_min (m : ℕ) (hpos : 0 < m) (hm : m < exponent G) : ∃ g : G, g ^ m ≠ 1 := by
  by_contra! h
  have hcon : exponent G ≤ m := exponent_min' m hpos h
  omega

@[to_additive AddMonoid.exp_eq_one_iff]
theorem exp_eq_one_iff : exponent G = 1 ↔ Subsingleton G := by
  refine ⟨fun eq_one => ⟨fun a b => ?a_eq_b⟩, fun h => le_antisymm ?le ?ge⟩
  · rw [← pow_one a, ← pow_one b, ← eq_one, Monoid.pow_exponent_eq_one, Monoid.pow_exponent_eq_one]
  · apply exponent_min' _ Nat.one_pos
    simp [eq_iff_true_of_subsingleton]
  · apply Nat.succ_le_of_lt
    apply exponent_pos_of_exists 1 Nat.one_pos
    simp [eq_iff_true_of_subsingleton]

@[to_additive (attr := simp) AddMonoid.exp_eq_one_of_subsingleton]
theorem exp_eq_one_of_subsingleton [hs : Subsingleton G] : exponent G = 1 :=
  exp_eq_one_iff.mpr hs

@[to_additive addOrder_dvd_exponent]
theorem order_dvd_exponent (g : G) : orderOf g ∣ exponent G :=
  orderOf_dvd_of_pow_eq_one <| pow_exponent_eq_one g

@[to_additive]
theorem orderOf_le_exponent (h : ExponentExists G) (g : G) : orderOf g ≤ exponent G :=
  Nat.le_of_dvd h.exponent_pos (order_dvd_exponent g)

@[to_additive]
theorem exponent_dvd_iff_forall_pow_eq_one {n : ℕ} : exponent G ∣ n ↔ ∀ g : G, g ^ n = 1 := by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp
  constructor
  · intro h g
    rw [Nat.dvd_iff_mod_eq_zero] at h
    rw [pow_eq_mod_exponent, h, pow_zero]
  · intro hG
    by_contra h
    rw [Nat.dvd_iff_mod_eq_zero, ← Ne, ← pos_iff_ne_zero] at h
    have h₂ : n % exponent G < exponent G := Nat.mod_lt _ (exponent_pos_of_exists n hpos hG)
    have h₃ : exponent G ≤ n % exponent G := by
      apply exponent_min' _ h
      simp_rw [← pow_eq_mod_exponent]
      exact hG
    exact h₂.not_ge h₃

@[to_additive]
alias ⟨_, exponent_dvd_of_forall_pow_eq_one⟩ := exponent_dvd_iff_forall_pow_eq_one

@[to_additive]
theorem exponent_dvd {n : ℕ} : exponent G ∣ n ↔ ∀ g : G, orderOf g ∣ n := by
  simp_rw [exponent_dvd_iff_forall_pow_eq_one, orderOf_dvd_iff_pow_eq_one]

variable (G)

@[to_additive]
theorem lcm_orderOf_dvd_exponent [Fintype G] :
    (Finset.univ : Finset G).lcm orderOf ∣ exponent G := by
  apply Finset.lcm_dvd
  intro g _
  exact order_dvd_exponent g

@[to_additive exists_addOrderOf_eq_pow_padic_val_nat_add_exponent]
theorem _root_.Nat.Prime.exists_orderOf_eq_pow_factorization_exponent {p : ℕ} (hp : p.Prime) :
    ∃ g : G, orderOf g = p ^ (exponent G).factorization p := by
  haveI := Fact.mk hp
  rcases eq_or_ne ((exponent G).factorization p) 0 with (h | h)
  · refine ⟨1, by rw [h, pow_zero, orderOf_one]⟩
  have he : 0 < exponent G :=
    Ne.bot_lt fun ht => by
      rw [ht] at h
      apply h
      rw [bot_eq_zero, Nat.factorization_zero, Finsupp.zero_apply]
  rw [← Finsupp.mem_support_iff] at h
  obtain ⟨g, hg⟩ : ∃ g : G, g ^ (exponent G / p) ≠ 1 := by
    suffices key : ¬exponent G ∣ exponent G / p by
      rwa [exponent_dvd_iff_forall_pow_eq_one, not_forall] at key
    exact fun hd =>
      hp.one_lt.not_ge
        ((mul_le_iff_le_one_left he).mp <|
          Nat.le_of_dvd he <| Nat.mul_dvd_of_dvd_div (Nat.dvd_of_mem_primeFactors h) hd)
  obtain ⟨k, hk : exponent G = p ^ _ * k⟩ := Nat.ordProj_dvd _ _
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.mp h)
  refine ⟨g ^ k, ?_⟩
  rw [ht]
  apply orderOf_eq_prime_pow
  · rwa [hk, mul_comm, ht, pow_succ, ← mul_assoc, Nat.mul_div_cancel _ hp.pos, pow_mul] at hg
  · rw [← Nat.succ_eq_add_one, ← ht, ← pow_mul, mul_comm, ← hk]
    exact pow_exponent_eq_one g

variable {G} in
open Nat in
/-- If two commuting elements `x` and `y` of a monoid have order `n` and `m`, there is an element
of order `lcm n m`. The result actually gives an explicit (computable) element, written as the
product of a power of `x` and a power of `y`. See also the result below if you don't need the
explicit formula. -/
@[to_additive /-- If two commuting elements `x` and `y` of an additive monoid have order `n` and
`m`, there is an element of order `lcm n m`. The result actually gives an explicit (computable)
element, written as the sum of a multiple of `x` and a multiple of `y`. See also the result below
if you don't need the explicit formula. -/]
lemma _root_.Commute.orderOf_mul_pow_eq_lcm {x y : G} (h : Commute x y) (hx : orderOf x ≠ 0)
    (hy : orderOf y ≠ 0) :
    orderOf (x ^ (orderOf x / (factorizationLCMLeft (orderOf x) (orderOf y))) *
      y ^ (orderOf y / factorizationLCMRight (orderOf x) (orderOf y))) =
      Nat.lcm (orderOf x) (orderOf y) := by
  rw [(h.pow_pow _ _).orderOf_mul_eq_mul_orderOf_of_coprime]
  all_goals iterate 2 rw [orderOf_pow_orderOf_div]; try rw [Coprime]
  all_goals simp [factorizationLCMLeft_mul_factorizationLCMRight, factorizationLCMLeft_dvd_left,
    factorizationLCMRight_dvd_right, coprime_factorizationLCMLeft_factorizationLCMRight, hx, hy]

open Submonoid in
/-- If two commuting elements `x` and `y` of a monoid have order `n` and `m`, then there is an
element of order `lcm n m` that lies in the subgroup generated by `x` and `y`. -/
@[to_additive /-- If two commuting elements `x` and `y` of an additive monoid have order `n` and
`m`, then there is an element of order `lcm n m` that lies in the additive subgroup generated by `x`
and `y`. -/]
theorem _root_.Commute.exists_orderOf_eq_lcm {x y : G} (h : Commute x y) :
    ∃ z ∈ closure {x, y}, orderOf z = Nat.lcm (orderOf x) (orderOf y) := by
  by_cases hx : orderOf x = 0 <;> by_cases hy : orderOf y = 0
  · exact ⟨x, subset_closure (by simp), by simp [hx]⟩
  · exact ⟨x, subset_closure (by simp), by simp [hx]⟩
  · exact ⟨y, subset_closure (by simp), by simp [hy]⟩
  · exact ⟨_, mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _),
      h.orderOf_mul_pow_eq_lcm hx hy⟩

/-- A nontrivial monoid has prime exponent `p` if and only if every non-identity element has
order `p`. -/
@[to_additive]
lemma exponent_eq_prime_iff {G : Type*} [Monoid G] [Nontrivial G] {p : ℕ} (hp : p.Prime) :
    Monoid.exponent G = p ↔ ∀ g : G, g ≠ 1 → orderOf g = p := by
  refine ⟨fun hG g hg ↦ ?_, fun h ↦ dvd_antisymm ?_ ?_⟩
  · rw [Ne, ← orderOf_eq_one_iff] at hg
    exact Eq.symm <| (hp.dvd_iff_eq hg).mp <| hG ▸ Monoid.order_dvd_exponent g
  · rw [exponent_dvd]
    intro g
    by_cases hg : g = 1
    · simp [hg]
    · rw [h g hg]
  · obtain ⟨g, hg⟩ := exists_ne (1 : G)
    simpa [h g hg] using Monoid.order_dvd_exponent g

variable {G}

@[to_additive]
theorem exponent_ne_zero_iff_range_orderOf_finite (h : ∀ g : G, 0 < orderOf g) :
    exponent G ≠ 0 ↔ (Set.range (orderOf : G → ℕ)).Finite := by
  refine ⟨fun he => ?_, fun he => ?_⟩
  · by_contra h
    obtain ⟨m, ⟨t, rfl⟩, het⟩ := Set.Infinite.exists_gt h (exponent G)
    exact pow_ne_one_of_lt_orderOf he het (pow_exponent_eq_one t)
  · lift Set.range (orderOf (G := G)) to Finset ℕ using he with t ht
    have htpos : 0 < t.prod id := by
      refine Finset.prod_pos fun a ha => ?_
      rw [← Finset.mem_coe, ht] at ha
      obtain ⟨k, rfl⟩ := ha
      exact h k
    suffices exponent G ∣ t.prod id by
      intro h
      rw [h, zero_dvd_iff] at this
      exact htpos.ne' this
    rw [exponent_dvd]
    intro g
    apply Finset.dvd_prod_of_mem id (?_ : orderOf g ∈ _)
    rw [← Finset.mem_coe, ht]
    exact Set.mem_range_self g

@[to_additive]
theorem exponent_eq_zero_iff_range_orderOf_infinite (h : ∀ g : G, 0 < orderOf g) :
    exponent G = 0 ↔ (Set.range (orderOf : G → ℕ)).Infinite := by
  have := exponent_ne_zero_iff_range_orderOf_finite h
  rwa [Ne, not_iff_comm, Iff.comm] at this

@[to_additive]
theorem lcm_orderOf_eq_exponent [Fintype G] : (Finset.univ : Finset G).lcm orderOf = exponent G :=
  Nat.dvd_antisymm
    (lcm_orderOf_dvd_exponent G)
    (exponent_dvd.mpr fun g => Finset.dvd_lcm (Finset.mem_univ g))

variable {H : Type*} [Monoid H]

/--
If there exists an injective, multiplication-preserving map from `G` to `H`,
then the exponent of `G` divides the exponent of `H`.
-/
@[to_additive /-- If there exists an injective, addition-preserving map from `G` to `H`,
then the exponent of `G` divides the exponent of `H`. -/]
theorem exponent_dvd_of_monoidHom (e : G →* H) (e_inj : Function.Injective e) :
    Monoid.exponent G ∣ Monoid.exponent H :=
  exponent_dvd_of_forall_pow_eq_one fun g => e_inj (by
    rw [map_pow, pow_exponent_eq_one, map_one])

/--
If there exists a multiplication-preserving equivalence between `G` and `H`,
then the exponent of `G` is equal to the exponent of `H`.
-/
@[to_additive /-- If there exists a addition-preserving equivalence between `G` and `H`,
then the exponent of `G` is equal to the exponent of `H`. -/]
theorem exponent_eq_of_mulEquiv (e : G ≃* H) : Monoid.exponent G = Monoid.exponent H :=
  Nat.dvd_antisymm
    (exponent_dvd_of_monoidHom e e.injective)
    (exponent_dvd_of_monoidHom e.symm e.symm.injective)

end Monoid

section Submonoid

variable [Monoid G]

variable (G) in
@[to_additive (attr := simp)]
theorem _root_.Submonoid.exponent_top :
    Monoid.exponent (⊤ : Submonoid G) = Monoid.exponent G :=
  exponent_eq_of_mulEquiv Submonoid.topEquiv

@[to_additive]
theorem _root_.Submonoid.pow_exponent_eq_one {S : Submonoid G} {g : G} (g_in_s : g ∈ S) :
    g ^ (Monoid.exponent S) = 1 := by
  have := Monoid.pow_exponent_eq_one (⟨g, g_in_s⟩ : S)
  rwa [SubmonoidClass.mk_pow, ← OneMemClass.coe_eq_one] at this

end Submonoid

section LeftCancelMonoid

variable [LeftCancelMonoid G] [Finite G]

@[to_additive]
theorem ExponentExists.of_finite : ExponentExists G := by
  let _inst := Fintype.ofFinite G
  simp only [Monoid.ExponentExists]
  refine ⟨(Finset.univ : Finset G).lcm orderOf, ?_, fun g => ?_⟩
  · simpa [pos_iff_ne_zero, Finset.lcm_eq_zero_iff] using fun x => (_root_.orderOf_pos x).ne'
  · rw [← orderOf_dvd_iff_pow_eq_one, lcm_orderOf_eq_exponent]
    exact order_dvd_exponent g

@[to_additive]
theorem exponent_ne_zero_of_finite : exponent G ≠ 0 :=
  ExponentExists.of_finite.exponent_ne_zero

@[to_additive AddMonoid.one_lt_exponent]
lemma one_lt_exponent [Nontrivial G] : 1 < Monoid.exponent G := by
  rw [Nat.one_lt_iff_ne_zero_and_ne_one]
  exact ⟨exponent_ne_zero_of_finite, mt exp_eq_one_iff.mp (not_subsingleton G)⟩

@[to_additive]
instance neZero_exponent_of_finite : NeZero <| Monoid.exponent G :=
  ⟨Monoid.exponent_ne_zero_of_finite⟩

end LeftCancelMonoid

section CommMonoid

variable [CommMonoid G]

@[to_additive]
theorem exists_orderOf_eq_exponent (hG : ExponentExists G) : ∃ g : G, orderOf g = exponent G := by
  have he := hG.exponent_ne_zero
  have hne : (Set.range (orderOf : G → ℕ)).Nonempty := ⟨1, 1, orderOf_one⟩
  have hfin : (Set.range (orderOf : G → ℕ)).Finite := by
    rwa [← exponent_ne_zero_iff_range_orderOf_finite hG.orderOf_pos]
  obtain ⟨t, ht⟩ := hne.csSup_mem hfin
  use t
  apply Nat.dvd_antisymm (order_dvd_exponent _)
  refine Nat.dvd_of_primeFactorsList_subperm he ?_
  rw [List.subperm_ext_iff]
  by_contra! h
  obtain ⟨p, hp, hpe⟩ := h
  replace hp := Nat.prime_of_mem_primeFactorsList hp
  simp only [Nat.primeFactorsList_count_eq] at hpe
  set k := (orderOf t).factorization p with hk
  obtain ⟨g, hg⟩ := hp.exists_orderOf_eq_pow_factorization_exponent G
  suffices orderOf t < orderOf (t ^ p ^ k * g) by
    rw [ht] at this
    exact this.not_ge (le_csSup hfin.bddAbove <| Set.mem_range_self _)
  have hpk : p ^ k ∣ orderOf t := Nat.ordProj_dvd _ _
  have hpk' : orderOf (t ^ p ^ k) = orderOf t / p ^ k := by
    rw [orderOf_pow' t (pow_ne_zero k hp.ne_zero), Nat.gcd_eq_right hpk]
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_lt hpe
  have hcoprime : (orderOf (t ^ p ^ k)).Coprime (orderOf g) := by
    rw [hg, Nat.coprime_pow_right_iff (pos_of_gt hpe), Nat.coprime_comm]
    apply Or.resolve_right (Nat.coprime_or_dvd_of_prime hp _)
    nth_rw 1 [← pow_one p]
    have : 1 = (Nat.factorization (orderOf (t ^ p ^ k))) p + 1 := by
      rw [hpk', Nat.factorization_div hpk]
      simp [k, hp]
    rw [this]
    -- Porting note: convert made to_additive complain
    apply Nat.pow_succ_factorization_not_dvd (hG.orderOf_pos <| t ^ p ^ k).ne' hp
  rw [(Commute.all _ g).orderOf_mul_eq_mul_orderOf_of_coprime hcoprime, hpk',
    hg, ha, hk, pow_add, pow_add, pow_one, ← mul_assoc, ← mul_assoc,
    Nat.div_mul_cancel, mul_assoc, lt_mul_iff_one_lt_right <| hG.orderOf_pos t, ← pow_succ]
  · exact one_lt_pow₀ hp.one_lt a.succ_ne_zero
  · exact hpk

@[to_additive]
theorem exponent_eq_iSup_orderOf (h : ∀ g : G, 0 < orderOf g) :
    exponent G = ⨆ g : G, orderOf g := by
  rw [iSup]
  by_cases ExponentExists G
  case neg he =>
    rw [← exponent_eq_zero_iff] at he
    rw [he, Set.Infinite.Nat.sSup_eq_zero <| (exponent_eq_zero_iff_range_orderOf_infinite h).1 he]
  case pos he =>
    rw [csSup_eq_of_forall_le_of_forall_lt_exists_gt (Set.range_nonempty _)]
    · simp_rw [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
      exact orderOf_le_exponent he
    intro x hx
    obtain ⟨g, hg⟩ := exists_orderOf_eq_exponent he
    rw [← hg] at hx
    simp_rw [Set.mem_range, exists_exists_eq_and]
    exact ⟨g, hx⟩

open scoped Classical in
@[to_additive]
theorem exponent_eq_iSup_orderOf' :
    exponent G = if ∃ g : G, orderOf g = 0 then 0 else ⨆ g : G, orderOf g := by
  split_ifs with h
  · obtain ⟨g, hg⟩ := h
    exact exponent_eq_zero_of_order_zero hg
  · have := not_exists.mp h
    exact exponent_eq_iSup_orderOf fun g => Ne.bot_lt <| this g

end CommMonoid

section CancelCommMonoid

variable [CancelCommMonoid G]

@[to_additive]
theorem exponent_eq_max'_orderOf [Fintype G] :
    exponent G = ((@Finset.univ G _).image orderOf).max' ⟨1, by simp⟩ := by
  rw [← Finset.Nonempty.csSup_eq_max', Finset.coe_image, Finset.coe_univ, Set.image_univ, ← iSup]
  exact exponent_eq_iSup_orderOf orderOf_pos

end CancelCommMonoid

end Monoid

section Group

variable [Group G] {n m : ℤ}

@[to_additive]
theorem Group.exponent_dvd_card [Fintype G] : Monoid.exponent G ∣ Fintype.card G :=
  Monoid.exponent_dvd.mpr <| fun _ => orderOf_dvd_card

@[to_additive]
theorem Group.exponent_dvd_nat_card : Monoid.exponent G ∣ Nat.card G :=
  Monoid.exponent_dvd.mpr orderOf_dvd_natCard

@[to_additive]
theorem Subgroup.exponent_toSubmonoid (H : Subgroup G) :
    Monoid.exponent H.toSubmonoid = Monoid.exponent H :=
  Monoid.exponent_eq_of_mulEquiv (MulEquiv.subgroupCongr rfl)

@[to_additive (attr := simp)]
theorem Subgroup.exponent_top : Monoid.exponent (⊤ : Subgroup G) = Monoid.exponent G :=
  Monoid.exponent_eq_of_mulEquiv topEquiv

@[to_additive]
theorem Subgroup.pow_exponent_eq_one {H : Subgroup G} {g : G} (g_in_H : g ∈ H) :
    g ^ Monoid.exponent H = 1 := exponent_toSubmonoid H ▸ Submonoid.pow_exponent_eq_one g_in_H

@[to_additive]
theorem Group.exponent_dvd_iff_forall_zpow_eq_one :
    (Monoid.exponent G : ℤ) ∣ n ↔ ∀ g : G, g ^ n = 1 := by
  simp_rw [Int.natCast_dvd, Monoid.exponent_dvd_iff_forall_pow_eq_one, pow_natAbs_eq_one]

@[to_additive]
theorem Group.exponent_dvd_sub_iff_zpow_eq_zpow :
    (Monoid.exponent G : ℤ) ∣ n - m ↔ ∀ g : G, g ^ n = g ^ m := by
  simp_rw [Group.exponent_dvd_iff_forall_zpow_eq_one, zpow_sub, mul_inv_eq_one]

end Group

section PiProd

open Finset Monoid

@[to_additive]
theorem Monoid.exponent_pi_eq_zero {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)] {j : ι}
    (hj : exponent (M j) = 0) : exponent ((i : ι) → M i) = 0 := by
  classical
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
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun m₂ ↦ ?_
  obtain ⟨m₁, rfl⟩ := hf m₂
  rw [← map_pow, pow_exponent_eq_one, map_one]

/-- The exponent of finite product of monoids is the `Finset.lcm` of the exponents of the
constituent monoids. -/
@[to_additive /-- The exponent of finite product of additive monoids is the `Finset.lcm` of the
exponents of the constituent additive monoids. -/]
theorem Monoid.exponent_pi {ι : Type*} [Fintype ι] {M : ι → Type*} [∀ i, Monoid (M i)] :
    exponent ((i : ι) → M i) = lcm univ (exponent <| M ·) := by
  refine dvd_antisymm ?_ ?_
  · refine exponent_dvd_of_forall_pow_eq_one fun m ↦ ?_
    ext i
    rw [Pi.pow_apply, Pi.one_apply, ← orderOf_dvd_iff_pow_eq_one]
    apply dvd_trans (Monoid.order_dvd_exponent (m i))
    exact Finset.dvd_lcm (mem_univ i)
  · apply Finset.lcm_dvd fun i _ ↦ ?_
    exact MonoidHom.exponent_dvd (f := Pi.evalMonoidHom (M ·) i) (Function.surjective_eval i)

/-- The exponent of product of two monoids is the `lcm` of the exponents of the
individuaul monoids. -/
@[to_additive AddMonoid.exponent_prod /-- The exponent of product of two additive monoids is the
`lcm` of the exponents of the individuaul additive monoids. -/]
theorem Monoid.exponent_prod {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] :
    exponent (M₁ × M₂) = lcm (exponent M₁) (exponent M₂) := by
  refine dvd_antisymm ?_ (lcm_dvd ?_ ?_)
  · refine exponent_dvd_of_forall_pow_eq_one fun g ↦ ?_
    ext1
    · rw [Prod.pow_fst, Prod.fst_one, ← orderOf_dvd_iff_pow_eq_one]
      exact dvd_trans (Monoid.order_dvd_exponent (g.1)) <| dvd_lcm_left _ _
    · rw [Prod.pow_snd, Prod.snd_one, ← orderOf_dvd_iff_pow_eq_one]
      exact dvd_trans (Monoid.order_dvd_exponent (g.2)) <| dvd_lcm_right _ _
  · exact MonoidHom.exponent_dvd (f := MonoidHom.fst M₁ M₂) Prod.fst_surjective
  · exact MonoidHom.exponent_dvd (f := MonoidHom.snd M₁ M₂) Prod.snd_surjective

end PiProd

/-! # Properties of monoids with exponent two -/

section ExponentTwo

section Monoid

variable [Monoid G]

@[to_additive]
lemma orderOf_eq_two_iff (hG : Monoid.exponent G = 2) {x : G} :
    orderOf x = 2 ↔ x ≠ 1 :=
  ⟨by rintro hx rfl; norm_num at hx, orderOf_eq_prime (hG ▸ Monoid.pow_exponent_eq_one x)⟩

@[to_additive]
theorem Commute.of_orderOf_dvd_two [IsCancelMul G] (h : ∀ g : G, orderOf g ∣ 2) (a b : G) :
    Commute a b := by
  simp_rw [orderOf_dvd_iff_pow_eq_one] at h
  rw [commute_iff_eq, ← mul_right_inj a, ← mul_left_inj b]
  -- We avoid `group` here to minimize imports while low in the hierarchy;
  -- typically it would be better to invoke the tactic.
  calc
    a * (a * b) * b = a ^ 2 * b ^ 2 := by simp [pow_two, mul_assoc]
    _ = 1 := by rw [h, h, mul_one]
    _ = (a * b) ^ 2 := by rw [h]
    _ = a * (b * a) * b := by simp [pow_two, mul_assoc]

/-- In a cancellative monoid of exponent two, all elements commute. -/
@[to_additive]
lemma mul_comm_of_exponent_two [IsCancelMul G] (hG : Monoid.exponent G = 2) (a b : G) :
    a * b = b * a :=
  Commute.of_orderOf_dvd_two (fun g => hG ▸ Monoid.order_dvd_exponent g) a b

/-- Any cancellative monoid of exponent two is abelian. -/
@[to_additive /-- Any additive group of exponent two is abelian. -/]
abbrev commMonoidOfExponentTwo [IsCancelMul G] (hG : Monoid.exponent G = 2) : CommMonoid G where
  mul_comm := mul_comm_of_exponent_two hG

end Monoid

section Group

variable [Group G]
/-- In a group of exponent two, every element is its own inverse. -/
@[to_additive]
lemma inv_eq_self_of_exponent_two (hG : Monoid.exponent G = 2) (x : G) :
    x⁻¹ = x :=
  inv_eq_of_mul_eq_one_left <| pow_two (a := x) ▸ hG ▸ Monoid.pow_exponent_eq_one x

/-- If an element in a group has order two, then it is its own inverse. -/
@[to_additive]
lemma inv_eq_self_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) :
    x⁻¹ = x :=
  inv_eq_of_mul_eq_one_left <| pow_two (a := x) ▸ hx ▸ pow_orderOf_eq_one x

@[to_additive]
lemma mul_notMem_of_orderOf_eq_two {x y : G} (hx : orderOf x = 2)
    (hy : orderOf y = 2) (hxy : x ≠ y) : x * y ∉ ({x, y, 1} : Set G) := by
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff, mul_eq_left, mul_eq_right,
    mul_eq_one_iff_eq_inv, inv_eq_self_of_orderOf_eq_two hy, not_or]
  aesop

@[deprecated (since := "2025-05-23")]
alias add_not_mem_of_addOrderOf_eq_two := add_notMem_of_addOrderOf_eq_two

@[to_additive existing, deprecated (since := "2025-05-23")]
alias mul_not_mem_of_orderOf_eq_two := mul_notMem_of_orderOf_eq_two

@[to_additive]
lemma mul_notMem_of_exponent_two (h : Monoid.exponent G = 2) {x y : G}
    (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) : x * y ∉ ({x, y, 1} : Set G) :=
  mul_notMem_of_orderOf_eq_two (orderOf_eq_prime (h ▸ Monoid.pow_exponent_eq_one x) hx)
    (orderOf_eq_prime (h ▸ Monoid.pow_exponent_eq_one y) hy) hxy

@[deprecated (since := "2025-05-23")]
alias add_not_mem_of_exponent_two := add_notMem_of_exponent_two

@[to_additive existing, deprecated (since := "2025-05-23")]
alias mul_not_mem_of_exponent_two := mul_notMem_of_exponent_two

end Group

end ExponentTwo
