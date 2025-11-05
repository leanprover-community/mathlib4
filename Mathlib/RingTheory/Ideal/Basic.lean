/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.Algebra.Field.IsField
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Tactic.FinCases

/-!

# Ideals over a ring

This file contains an assortment of definitions and results for `Ideal R`,
the type of (left) ideals over a ring `R`.
Note that over commutative rings, left ideals and two-sided ideals are equivalent.

## Implementation notes

`Ideal R` is implemented using `Submodule R R`, where `•` is interpreted as `*`.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/


variable {ι α β F : Type*}

open Set Function

open Pointwise

section Semiring

namespace Ideal

variable {R : ι → Type*} [Π i, Semiring (R i)] (I J : Π i, Ideal (R i))

section Pi

/-- `Πᵢ Iᵢ` as an ideal of `Πᵢ Rᵢ`. -/
def pi : Ideal (Π i, R i) where
  carrier := { r | ∀ i, r i ∈ I i }
  zero_mem' i := (I i).zero_mem
  add_mem' ha hb i := (I i).add_mem (ha i) (hb i)
  smul_mem' a _b hb i := (I i).mul_mem_left (a i) (hb i)

theorem mem_pi (r : Π i, R i) : r ∈ pi I ↔ ∀ i, r i ∈ I i :=
  Iff.rfl

@[simp] theorem pi_span {r : Π i, R i} : pi (span {r ·}) = span {r} := by
  ext; simp_rw [mem_pi, mem_span_singleton', funext_iff, Classical.skolem, Pi.mul_def]

instance (priority := low) [∀ i, (I i).IsTwoSided] : (pi I).IsTwoSided :=
  ⟨fun _b hb i ↦ mul_mem_right _ _ (hb i)⟩

variable {I J}

theorem single_mem_pi [DecidableEq ι] {i : ι} {r : R i} (hr : r ∈ I i) : Pi.single i r ∈ pi I := by
  intro j
  obtain rfl | ne := eq_or_ne i j
  · simpa
  · simp [ne]

@[simp] theorem pi_le_pi_iff : pi I ≤ pi J ↔ I ≤ J where
  mp le i r hr := by classical simpa using le (single_mem_pi hr) i
  mpr le r hr i := le i (hr i)

end Pi

section Commute

variable {α : Type*} [Semiring α] (I : Ideal α) {a b : α}

theorem add_pow_mem_of_pow_mem_of_le_of_commute {m n k : ℕ}
    (ha : a ^ m ∈ I) (hb : b ^ n ∈ I) (hk : m + n ≤ k + 1)
    (hab : Commute a b) :
    (a + b) ^ k ∈ I := by
  simp_rw [hab.add_pow, ← Nat.cast_comm]
  apply I.sum_mem
  intro c _
  apply mul_mem_left
  by_cases h : m ≤ c
  · rw [hab.pow_pow]
    exact I.mul_mem_left _ (I.pow_mem_of_pow_mem ha h)
  · refine I.mul_mem_left _ (I.pow_mem_of_pow_mem hb ?_)
    cutsat

theorem add_pow_add_pred_mem_of_pow_mem_of_commute {m n : ℕ}
    (ha : a ^ m ∈ I) (hb : b ^ n ∈ I) (hab : Commute a b) :
    (a + b) ^ (m + n - 1) ∈ I :=
  I.add_pow_mem_of_pow_mem_of_le_of_commute ha hb (by rw [← Nat.sub_le_iff_le_add]) hab

end Commute

end Ideal

end Semiring

section CommSemiring

variable {a b : α}

-- A separate namespace definition is needed because the variables were historically in a different
-- order.
namespace Ideal

variable [CommSemiring α] (I : Ideal α)

theorem add_pow_mem_of_pow_mem_of_le {m n k : ℕ}
    (ha : a ^ m ∈ I) (hb : b ^ n ∈ I) (hk : m + n ≤ k + 1) :
    (a + b) ^ k ∈ I :=
  I.add_pow_mem_of_pow_mem_of_le_of_commute ha hb hk (Commute.all ..)

theorem add_pow_add_pred_mem_of_pow_mem {m n : ℕ}
    (ha : a ^ m ∈ I) (hb : b ^ n ∈ I) :
    (a + b) ^ (m + n - 1) ∈ I :=
  I.add_pow_add_pred_mem_of_pow_mem_of_commute ha hb (Commute.all ..)

theorem pow_multiset_sum_mem_span_pow [DecidableEq α] (s : Multiset α) (n : ℕ) :
    s.sum ^ (Multiset.card s * n + 1) ∈
    span ((s.map fun (x : α) ↦ x ^ (n + 1)).toFinset : Set α) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s hs => ?_
  simp only [Finset.coe_insert, Multiset.map_cons, Multiset.toFinset_cons, Multiset.sum_cons,
    Multiset.card_cons, add_pow]
  refine Submodule.sum_mem _ ?_
  intro c _hc
  rw [mem_span_insert]
  by_cases h : n + 1 ≤ c
  · refine ⟨a ^ (c - (n + 1)) * s.sum ^ ((Multiset.card s + 1) * n + 1 - c) *
      ((Multiset.card s + 1) * n + 1).choose c, 0, Submodule.zero_mem _, ?_⟩
    rw [mul_comm _ (a ^ (n + 1))]
    simp_rw [← mul_assoc]
    rw [← pow_add, add_zero, add_tsub_cancel_of_le h]
  · use 0
    simp_rw [zero_mul, zero_add]
    refine ⟨_, ?_, rfl⟩
    replace h : c ≤ n := Nat.lt_succ_iff.mp (not_le.mp h)
    have : (Multiset.card s + 1) * n + 1 - c = Multiset.card s * n + 1 + (n - c) := by
      rw [add_mul, one_mul, add_assoc, add_comm n 1, ← add_assoc, add_tsub_assoc_of_le h]
    rw [this, pow_add]
    simp_rw [mul_assoc, mul_comm (s.sum ^ (Multiset.card s * n + 1)), ← mul_assoc]
    exact mul_mem_left _ _ hs

theorem sum_pow_mem_span_pow {ι} (s : Finset ι) (f : ι → α) (n : ℕ) :
    (∑ i ∈ s, f i) ^ (s.card * n + 1) ∈ span ((fun i => f i ^ (n + 1)) '' s) := by
  classical
  simpa only [Multiset.card_map, Multiset.map_map, comp_apply, Multiset.toFinset_map,
    Finset.coe_image, Finset.val_toFinset] using pow_multiset_sum_mem_span_pow (s.1.map f) n

theorem span_pow_eq_top (s : Set α) (hs : span s = ⊤) (n : ℕ) :
    span ((fun (x : α) => x ^ n) '' s) = ⊤ := by
  rw [eq_top_iff_one]
  rcases n with - | n
  · obtain rfl | ⟨x, hx⟩ := eq_empty_or_nonempty s
    · rw [Set.image_empty, hs]
      trivial
    · exact subset_span ⟨_, hx, pow_zero _⟩
  rw [eq_top_iff_one, span, Finsupp.mem_span_iff_linearCombination] at hs
  rcases hs with ⟨f, hf⟩
  simp only [Finsupp.linearCombination, Finsupp.coe_lsum, Finsupp.sum, LinearMap.coe_smulRight,
    LinearMap.id_coe, id_eq, smul_eq_mul] at hf
  have := sum_pow_mem_span_pow f.support (fun a => f a * a) n
  rw [hf, one_pow] at this
  refine span_le.mpr ?_ this
  rintro _ hx
  simp_rw [Set.mem_image] at hx
  rcases hx with ⟨x, _, rfl⟩
  have : span ({(x : α) ^ (n + 1)} : Set α) ≤ span ((fun x : α => x ^ (n + 1)) '' s) := by
    rw [span_le, Set.singleton_subset_iff]
    exact subset_span ⟨x, x.prop, rfl⟩
  refine this ?_
  rw [mul_pow, mem_span_singleton]
  exact ⟨f x ^ (n + 1), mul_comm _ _⟩

theorem span_range_pow_eq_top (s : Set α) (hs : span s = ⊤) (n : s → ℕ) :
    span (Set.range fun x ↦ x.1 ^ n x) = ⊤ := by
  have ⟨t, hts, mem⟩ := Submodule.mem_span_finite_of_mem_span ((eq_top_iff_one _).mp hs)
  refine top_unique ((span_pow_eq_top _ ((eq_top_iff_one _).mpr mem) <|
    t.attach.sup fun x ↦ n ⟨x, hts x.2⟩).ge.trans <| span_le.mpr ?_)
  rintro _ ⟨x, hxt, rfl⟩
  rw [← Nat.sub_add_cancel (Finset.le_sup <| t.mem_attach ⟨x, hxt⟩)]
  simp_rw [pow_add]
  exact mul_mem_left _ _ (subset_span ⟨_, rfl⟩)

theorem prod_mem {ι : Type*} {f : ι → α} {s : Finset ι}
    (I : Ideal α) {i : ι} (hi : i ∈ s) (hfi : f i ∈ I) :
    ∏ i ∈ s, f i ∈ I := by
  classical
  rw [Finset.prod_eq_prod_diff_singleton_mul hi]
  exact Ideal.mul_mem_left _ _ hfi

end Ideal

end CommSemiring

section DivisionSemiring

variable {K : Type*} [DivisionSemiring K] (I : Ideal K)

namespace Ideal

variable (K) in
/-- A bijection between (left) ideals of a division ring and `{0, 1}`, sending `⊥` to `0`
and `⊤` to `1`. -/
def equivFinTwo [DecidableEq (Ideal K)] : Ideal K ≃ Fin 2 where
  toFun := fun I ↦ if I = ⊥ then 0 else 1
  invFun := ![⊥, ⊤]
  left_inv := fun I ↦ by rcases eq_bot_or_top I with rfl | rfl <;> simp
  right_inv := fun i ↦ by fin_cases i <;> simp

instance : Finite (Ideal K) := let _i := Classical.decEq (Ideal K); ⟨equivFinTwo K⟩

/-- Ideals of a `DivisionSemiring` are a simple order. Thanks to the way abbreviations work,
this automatically gives an `IsSimpleModule K` instance. -/
instance isSimpleOrder : IsSimpleOrder (Ideal K) :=
  ⟨eq_bot_or_top⟩

end Ideal

end DivisionSemiring

-- TODO: consider moving the lemmas below out of the `Ring` namespace since they are
-- about `CommSemiring`s.
namespace Ring

variable {R : Type*} [CommSemiring R]

theorem exists_not_isUnit_of_not_isField [Nontrivial R] (hf : ¬IsField R) :
    ∃ (x : R) (_hx : x ≠ (0 : R)), ¬IsUnit x := by
  have : ¬_ := fun h => hf ⟨exists_pair_ne R, mul_comm, h⟩
  simp_rw [isUnit_iff_exists_inv]
  push_neg at this ⊢
  obtain ⟨x, hx, not_unit⟩ := this
  exact ⟨x, hx, not_unit⟩

theorem not_isField_iff_exists_ideal_bot_lt_and_lt_top [Nontrivial R] :
    ¬IsField R ↔ ∃ I : Ideal R, ⊥ < I ∧ I < ⊤ := by
  constructor
  · intro h
    obtain ⟨x, nz, nu⟩ := exists_not_isUnit_of_not_isField h
    use Ideal.span {x}
    rw [bot_lt_iff_ne_bot, lt_top_iff_ne_top]
    exact ⟨mt Ideal.span_singleton_eq_bot.mp nz, mt Ideal.span_singleton_eq_top.mp nu⟩
  · rintro ⟨I, bot_lt, lt_top⟩ hf
    obtain ⟨x, mem, ne_zero⟩ := SetLike.exists_of_lt bot_lt
    rw [Submodule.mem_bot] at ne_zero
    obtain ⟨y, hy⟩ := hf.mul_inv_cancel ne_zero
    rw [lt_top_iff_ne_top, Ne, Ideal.eq_top_iff_one, ← hy] at lt_top
    exact lt_top (I.mul_mem_right _ mem)

theorem not_isField_iff_exists_prime [Nontrivial R] :
    ¬IsField R ↔ ∃ p : Ideal R, p ≠ ⊥ ∧ p.IsPrime :=
  not_isField_iff_exists_ideal_bot_lt_and_lt_top.trans
    ⟨fun ⟨I, bot_lt, lt_top⟩ =>
      let ⟨p, hp, le_p⟩ := I.exists_le_maximal (lt_top_iff_ne_top.mp lt_top)
      ⟨p, bot_lt_iff_ne_bot.mp (lt_of_lt_of_le bot_lt le_p), hp.isPrime⟩,
      fun ⟨p, ne_bot, Prime⟩ => ⟨p, bot_lt_iff_ne_bot.mpr ne_bot, lt_top_iff_ne_top.mpr Prime.1⟩⟩

/-- Also see `Ideal.isSimpleOrder` for the forward direction as an instance when `R` is a
division (semi)ring.

This result actually holds for all division semirings, but we lack the predicate to state it. -/
theorem isField_iff_isSimpleOrder_ideal : IsField R ↔ IsSimpleOrder (Ideal R) := by
  cases subsingleton_or_nontrivial R
  · exact
      ⟨fun h => (not_isField_of_subsingleton _ h).elim, fun h =>
        (false_of_nontrivial_of_subsingleton <| Ideal R).elim⟩
  rw [← not_iff_not, Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top, ← not_iff_not]
  push_neg
  simp_rw [lt_top_iff_ne_top, bot_lt_iff_ne_bot, ← or_iff_not_imp_left, not_ne_iff]
  exact ⟨fun h => ⟨h⟩, fun h => h.2⟩

/-- When a ring is not a field, the maximal ideals are nontrivial. -/
theorem ne_bot_of_isMaximal_of_not_isField [Nontrivial R] {M : Ideal R} (max : M.IsMaximal)
    (not_field : ¬IsField R) : M ≠ ⊥ := by
  rintro h
  rw [h] at max
  rcases max with ⟨⟨_h1, h2⟩⟩
  obtain ⟨I, hIbot, hItop⟩ := not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp not_field
  exact ne_of_lt hItop (h2 I hIbot)

end Ring

namespace Ideal

variable {R : Type*} [CommSemiring R] [Nontrivial R]

theorem bot_lt_of_maximal (M : Ideal R) [hm : M.IsMaximal] (non_field : ¬IsField R) : ⊥ < M := by
  rcases Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.1 non_field with ⟨I, Ibot, Itop⟩
  constructor; · simp
  intro mle
  apply lt_irrefl (⊤ : Ideal R)
  have : M = ⊥ := eq_bot_iff.mpr mle
  rw [← this] at Ibot
  rwa [hm.1.2 I Ibot] at Itop

end Ideal
