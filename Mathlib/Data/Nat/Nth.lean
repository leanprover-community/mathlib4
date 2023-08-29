/-
Copyright (c) 2021 Vladimir Goryachev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Goryachev, Kyle Miller, Scott Morrison, Eric Rodriguez
-/
import Mathlib.Data.Nat.Count
import Mathlib.Data.Set.Intervals.Monotone
import Mathlib.Order.OrderIsoNat

#align_import data.nat.nth from "leanprover-community/mathlib"@"7fdd4f3746cb059edfdb5d52cba98f66fce418c0"

/-!
# The `n`th Number Satisfying a Predicate

This file defines a function for "what is the `n`th number that satisifies a given predicate `p`",
and provides lemmas that deal with this function and its connection to `Nat.count`.

## Main definitions

* `Nat.nth p n`: The `n`-th natural `k` (zero-indexed) such that `p k`. If there is no
  such natural (that is, `p` is true for at most `n` naturals), then `Nat.nth p n = 0`.

## Main results

* `Nat.nth_eq_orderEmbOfFin`: For a fintely-often true `p`, gives the cardinality of the set of
  numbers satisfying `p` above particular values of `nth p`
* `Nat.gc_count_nth`: Establishes a Galois connection between `Nat.nth p` and `Nat.count p`.
* `Nat.nth_eq_orderIsoOfNat`: For an infinitely-ofter true predicate, `nth` agrees with the
  order-isomorphism of the subtype to the natural numbers.

There has been some discussion on the subject of whether both of `nth` and
`Nat.Subtype.orderIsoOfNat` should exist. See discussion
[here](https://github.com/leanprover-community/mathlib/pull/9457#pullrequestreview-767221180).
Future work should address how lemmas that use these should be written.

-/


open Finset

namespace Nat

variable (p : ℕ → Prop)

/-- Find the `n`-th natural number satisfying `p` (indexed from `0`, so `nth p 0` is the first
natural number satisfying `p`), or `0` if there is no such number. See also
`Subtype.orderIsoOfNat` for the order isomorphism with ℕ when `p` is infinitely often true. -/
noncomputable def nth (p : ℕ → Prop) (n : ℕ) : ℕ := by
  classical exact
    if h : Set.Finite (setOf p) then (h.toFinset.sort (· ≤ ·)).getD n 0
    else @Nat.Subtype.orderIsoOfNat (setOf p) (Set.Infinite.to_subtype h) n
#align nat.nth Nat.nth

variable {p}

/-!
### Lemmas about `Nat.nth` on a finite set
-/


theorem nth_of_card_le (hf : (setOf p).Finite) {n : ℕ} (hn : hf.toFinset.card ≤ n) : nth p n = 0 :=
  by rw [nth, dif_pos hf, List.getD_eq_default]; rwa [Finset.length_sort]
     -- ⊢ List.length (sort (fun x x_1 => x ≤ x_1) (Set.Finite.toFinset hf)) ≤ n
                                                 -- 🎉 no goals
#align nat.nth_of_card_le Nat.nth_of_card_le

theorem nth_eq_getD_sort (h : (setOf p).Finite) (n : ℕ) :
    nth p n = (h.toFinset.sort (· ≤ ·)).getD n 0 :=
  dif_pos h
#align nat.nth_eq_nthd_sort Nat.nth_eq_getD_sort

theorem nth_eq_orderEmbOfFin (hf : (setOf p).Finite) {n : ℕ} (hn : n < hf.toFinset.card) :
    nth p n = hf.toFinset.orderEmbOfFin rfl ⟨n, hn⟩ := by
  rw [nth_eq_getD_sort hf, Finset.orderEmbOfFin_apply, List.getD_eq_get]; rfl
  -- ⊢ List.get (sort (fun x x_1 => x ≤ x_1) (Set.Finite.toFinset hf)) { val := n,  …
                                                                          -- 🎉 no goals
#align nat.nth_eq_order_emb_of_fin Nat.nth_eq_orderEmbOfFin

theorem nth_strictMonoOn (hf : (setOf p).Finite) :
    StrictMonoOn (nth p) (Set.Iio hf.toFinset.card) := by
  rintro m (hm : m < _) n (hn : n < _) h
  -- ⊢ nth p m < nth p n
  simp only [nth_eq_orderEmbOfFin, *]
  -- ⊢ ↑(orderEmbOfFin (Set.Finite.toFinset (_ : Set.Finite (setOf p))) (_ : card ( …
  exact OrderEmbedding.strictMono _ h
  -- 🎉 no goals
#align nat.nth_strict_mono_on Nat.nth_strictMonoOn

theorem nth_lt_nth_of_lt_card (hf : (setOf p).Finite) {m n : ℕ} (h : m < n)
    (hn : n < hf.toFinset.card) : nth p m < nth p n :=
  nth_strictMonoOn hf (h.trans hn) hn h
#align nat.nth_lt_nth_of_lt_card Nat.nth_lt_nth_of_lt_card

theorem nth_le_nth_of_lt_card (hf : (setOf p).Finite) {m n : ℕ} (h : m ≤ n)
    (hn : n < hf.toFinset.card) : nth p m ≤ nth p n :=
  (nth_strictMonoOn hf).monotoneOn (h.trans_lt hn) hn h
#align nat.nth_le_nth_of_lt_card Nat.nth_le_nth_of_lt_card

theorem lt_of_nth_lt_nth_of_lt_card (hf : (setOf p).Finite) {m n : ℕ} (h : nth p m < nth p n)
    (hm : m < hf.toFinset.card) : m < n :=
  not_le.1 fun hle => h.not_le <| nth_le_nth_of_lt_card hf hle hm
#align nat.lt_of_nth_lt_nth_of_lt_card Nat.lt_of_nth_lt_nth_of_lt_card

theorem le_of_nth_le_nth_of_lt_card (hf : (setOf p).Finite) {m n : ℕ} (h : nth p m ≤ nth p n)
    (hm : m < hf.toFinset.card) : m ≤ n :=
  not_lt.1 fun hlt => h.not_lt <| nth_lt_nth_of_lt_card hf hlt hm
#align nat.le_of_nth_le_nth_of_lt_card Nat.le_of_nth_le_nth_of_lt_card

theorem nth_injOn (hf : (setOf p).Finite) : (Set.Iio hf.toFinset.card).InjOn (nth p) :=
  (nth_strictMonoOn hf).injOn
#align nat.nth_inj_on Nat.nth_injOn

theorem range_nth_of_finite (hf : (setOf p).Finite) : Set.range (nth p) = insert 0 (setOf p) := by
  simpa only [← nth_eq_getD_sort hf, mem_sort, Set.Finite.mem_toFinset]
    using Set.range_list_getD (hf.toFinset.sort (· ≤ ·)) 0
#align nat.range_nth_of_finite Nat.range_nth_of_finite

@[simp]
theorem image_nth_Iio_card (hf : (setOf p).Finite) : nth p '' Set.Iio hf.toFinset.card = setOf p :=
  calc
    nth p '' Set.Iio hf.toFinset.card = Set.range (hf.toFinset.orderEmbOfFin rfl) := by
      ext x
      -- ⊢ x ∈ nth p '' Set.Iio (card (Set.Finite.toFinset hf)) ↔ x ∈ Set.range ↑(order …
      simp only [Set.mem_image, Set.mem_range, Fin.exists_iff, ← nth_eq_orderEmbOfFin hf,
        Set.mem_Iio, exists_prop]
    _ = setOf p := by rw [range_orderEmbOfFin, Set.Finite.coe_toFinset]
                      -- 🎉 no goals
#align nat.image_nth_Iio_card Nat.image_nth_Iio_card

theorem nth_mem_of_lt_card {n : ℕ} (hf : (setOf p).Finite) (hlt : n < hf.toFinset.card) :
    p (nth p n) :=
  (image_nth_Iio_card hf).subset <| Set.mem_image_of_mem _ hlt
#align nat.nth_mem_of_lt_card Nat.nth_mem_of_lt_card

theorem exists_lt_card_finite_nth_eq (hf : (setOf p).Finite) {x} (h : p x) :
    ∃ n, n < hf.toFinset.card ∧ nth p n = x := by
  rwa [← @Set.mem_setOf_eq _ _ p, ← image_nth_Iio_card hf] at h
  -- 🎉 no goals
#align nat.exists_lt_card_finite_nth_eq Nat.exists_lt_card_finite_nth_eq

/-!
### Lemmas about `Nat.nth` on an infinite set
-/

/-- When `s` is an infinite set, `nth` agrees with `Nat.Subtype.orderIsoOfNat`. -/
theorem nth_apply_eq_orderIsoOfNat (hf : (setOf p).Infinite) (n : ℕ) :
    nth p n = @Nat.Subtype.orderIsoOfNat (setOf p) hf.to_subtype n := by rw [nth, dif_neg hf]
                                                                         -- 🎉 no goals
#align nat.nth_apply_eq_order_iso_of_nat Nat.nth_apply_eq_orderIsoOfNat

/-- When `s` is an infinite set, `nth` agrees with `Nat.Subtype.orderIsoOfNat`. -/
theorem nth_eq_orderIsoOfNat (hf : (setOf p).Infinite) :
    nth p = (↑) ∘ @Nat.Subtype.orderIsoOfNat (setOf p) hf.to_subtype :=
  funext <| nth_apply_eq_orderIsoOfNat hf
#align nat.nth_eq_order_iso_of_nat Nat.nth_eq_orderIsoOfNat

theorem nth_strictMono (hf : (setOf p).Infinite) : StrictMono (nth p) := by
  rw [nth_eq_orderIsoOfNat hf]
  -- ⊢ StrictMono (Subtype.val ∘ ↑(Subtype.orderIsoOfNat (setOf p)))
  exact (Subtype.strictMono_coe _).comp (OrderIso.strictMono _)
  -- 🎉 no goals
#align nat.nth_strict_mono Nat.nth_strictMono

theorem nth_injective (hf : (setOf p).Infinite) : Function.Injective (nth p) :=
  (nth_strictMono hf).injective
#align nat.nth_injective Nat.nth_injective

theorem nth_monotone (hf : (setOf p).Infinite) : Monotone (nth p) :=
  (nth_strictMono hf).monotone
#align nat.nth_monotone Nat.nth_monotone

theorem nth_lt_nth (hf : (setOf p).Infinite) {k n} : nth p k < nth p n ↔ k < n :=
  (nth_strictMono hf).lt_iff_lt
#align nat.nth_lt_nth Nat.nth_lt_nth

theorem nth_le_nth (hf : (setOf p).Infinite) {k n} : nth p k ≤ nth p n ↔ k ≤ n :=
  (nth_strictMono hf).le_iff_le
#align nat.nth_le_nth Nat.nth_le_nth

theorem range_nth_of_infinite (hf : (setOf p).Infinite) : Set.range (nth p) = setOf p := by
  rw [nth_eq_orderIsoOfNat hf]
  -- ⊢ Set.range (Subtype.val ∘ ↑(Subtype.orderIsoOfNat (setOf p))) = setOf p
  haveI := hf.to_subtype
  -- ⊢ Set.range (Subtype.val ∘ ↑(Subtype.orderIsoOfNat (setOf p))) = setOf p
  -- porting note: added `classical`; probably, Lean 3 found instance by unification
  classical exact Nat.Subtype.coe_comp_ofNat_range
  -- 🎉 no goals
#align nat.range_nth_of_infinite Nat.range_nth_of_infinite

theorem nth_mem_of_infinite (hf : (setOf p).Infinite) (n : ℕ) : p (nth p n) :=
  Set.range_subset_iff.1 (range_nth_of_infinite hf).le n
#align nat.nth_mem_of_infinite Nat.nth_mem_of_infinite

/-!
### Lemmas that work for finite and infinite sets
-/

theorem exists_lt_card_nth_eq {x} (h : p x) :
    ∃ n, (∀ hf : (setOf p).Finite, n < hf.toFinset.card) ∧ nth p n = x := by
  refine' (setOf p).finite_or_infinite.elim (fun hf => _) fun hf => _
  -- ⊢ ∃ n, (∀ (hf : Set.Finite (setOf p)), n < card (Set.Finite.toFinset hf)) ∧ nt …
  · rcases exists_lt_card_finite_nth_eq hf h with ⟨n, hn, hx⟩
    -- ⊢ ∃ n, (∀ (hf : Set.Finite (setOf p)), n < card (Set.Finite.toFinset hf)) ∧ nt …
    exact ⟨n, fun _ => hn, hx⟩
    -- 🎉 no goals
  · rw [← @Set.mem_setOf_eq _ _ p, ← range_nth_of_infinite hf] at h
    -- ⊢ ∃ n, (∀ (hf : Set.Finite (setOf p)), n < card (Set.Finite.toFinset hf)) ∧ nt …
    rcases h with ⟨n, hx⟩
    -- ⊢ ∃ n, (∀ (hf : Set.Finite (setOf p)), n < card (Set.Finite.toFinset hf)) ∧ nt …
    exact ⟨n, fun hf' => absurd hf' hf, hx⟩
    -- 🎉 no goals
#align nat.exists_lt_card_nth_eq Nat.exists_lt_card_nth_eq

theorem subset_range_nth : setOf p ⊆ Set.range (nth p) := fun x (hx : p x) =>
  let ⟨n, _, hn⟩ := exists_lt_card_nth_eq hx
  ⟨n, hn⟩
#align nat.subset_range_nth Nat.subset_range_nth

theorem range_nth_subset : Set.range (nth p) ⊆ insert 0 (setOf p) :=
  (setOf p).finite_or_infinite.elim (fun h => (range_nth_of_finite h).subset) fun h =>
    (range_nth_of_infinite h).trans_subset (Set.subset_insert _ _)
#align nat.range_nth_subset Nat.range_nth_subset

theorem nth_mem (n : ℕ) (h : ∀ hf : (setOf p).Finite, n < hf.toFinset.card) : p (nth p n) :=
  (setOf p).finite_or_infinite.elim (fun hf => nth_mem_of_lt_card hf (h hf)) fun h =>
    nth_mem_of_infinite h n
#align nat.nth_mem Nat.nth_mem

theorem nth_lt_nth' {m n : ℕ} (hlt : m < n) (h : ∀ hf : (setOf p).Finite, n < hf.toFinset.card) :
    nth p m < nth p n :=
  (setOf p).finite_or_infinite.elim (fun hf => nth_lt_nth_of_lt_card hf hlt (h _)) fun hf =>
    (nth_lt_nth hf).2 hlt
#align nat.nth_lt_nth' Nat.nth_lt_nth'

theorem nth_le_nth' {m n : ℕ} (hle : m ≤ n) (h : ∀ hf : (setOf p).Finite, n < hf.toFinset.card) :
    nth p m ≤ nth p n :=
  (setOf p).finite_or_infinite.elim (fun hf => nth_le_nth_of_lt_card hf hle (h _)) fun hf =>
    (nth_le_nth hf).2 hle
#align nat.nth_le_nth' Nat.nth_le_nth'

theorem le_nth {n : ℕ} (h : ∀ hf : (setOf p).Finite, n < hf.toFinset.card) : n ≤ nth p n :=
  (setOf p).finite_or_infinite.elim
    (fun hf => ((nth_strictMonoOn hf).mono <| Set.Iic_subset_Iio.2 (h _)).Iic_id_le _ le_rfl)
    fun hf => (nth_strictMono hf).id_le _
#align nat.le_nth Nat.le_nth

theorem isLeast_nth {n} (h : ∀ hf : (setOf p).Finite, n < hf.toFinset.card) :
    IsLeast {i | p i ∧ ∀ k < n, nth p k < i} (nth p n) :=
  ⟨⟨nth_mem n h, fun _k hk => nth_lt_nth' hk h⟩, fun _x hx =>
    let ⟨k, hk, hkx⟩ := exists_lt_card_nth_eq hx.1
    (lt_or_le k n).elim (fun hlt => absurd hkx (hx.2 _ hlt).ne) fun hle => hkx ▸ nth_le_nth' hle hk⟩
#align nat.is_least_nth Nat.isLeast_nth

theorem isLeast_nth_of_lt_card {n : ℕ} (hf : (setOf p).Finite) (hn : n < hf.toFinset.card) :
    IsLeast {i | p i ∧ ∀ k < n, nth p k < i} (nth p n) :=
  isLeast_nth fun _ => hn
#align nat.is_least_nth_of_lt_card Nat.isLeast_nth_of_lt_card

theorem isLeast_nth_of_infinite (hf : (setOf p).Infinite) (n : ℕ) :
    IsLeast {i | p i ∧ ∀ k < n, nth p k < i} (nth p n) :=
  isLeast_nth fun h => absurd h hf
#align nat.is_least_nth_of_infinite Nat.isLeast_nth_of_infinite

/-- An alternative recursive definition of `Nat.nth`: `Nat.nth s n` is the infimum of `x ∈ s` such
that `Nat.nth s k < x` for all `k < n`, if this set is nonempty. We do not assume that the set is
nonempty because we use the same "garbage value" `0` both for `sInf` on `ℕ` and for `Nat.nth s n`
for `n ≥ card s`. -/
theorem nth_eq_sInf (p : ℕ → Prop) (n : ℕ) : nth p n = sInf {x | p x ∧ ∀ k < n, nth p k < x} := by
  by_cases hn : ∀ hf : (setOf p).Finite, n < hf.toFinset.card
  -- ⊢ nth p n = sInf {x | p x ∧ ∀ (k : ℕ), k < n → nth p k < x}
  · exact (isLeast_nth hn).csInf_eq.symm
    -- 🎉 no goals
  · push_neg at hn
    -- ⊢ nth p n = sInf {x | p x ∧ ∀ (k : ℕ), k < n → nth p k < x}
    rcases hn with ⟨hf, hn⟩
    -- ⊢ nth p n = sInf {x | p x ∧ ∀ (k : ℕ), k < n → nth p k < x}
    rw [nth_of_card_le _ hn]
    -- ⊢ 0 = sInf {x | p x ∧ ∀ (k : ℕ), k < n → nth p k < x}
    refine' ((congr_arg sInf <| Set.eq_empty_of_forall_not_mem fun k hk => _).trans sInf_empty).symm
    -- ⊢ False
    rcases exists_lt_card_nth_eq hk.1 with ⟨k, hlt, rfl⟩
    -- ⊢ False
    exact (hk.2 _ ((hlt hf).trans_le hn)).false
    -- 🎉 no goals
#align nat.nth_eq_Inf Nat.nth_eq_sInf

theorem nth_zero : nth p 0 = sInf (setOf p) := by rw [nth_eq_sInf]; simp
                                                  -- ⊢ sInf {x | p x ∧ ∀ (k : ℕ), k < 0 → nth p k < x} = sInf (setOf p)
                                                                    -- 🎉 no goals
#align nat.nth_zero Nat.nth_zero

@[simp]
theorem nth_zero_of_zero (h : p 0) : nth p 0 = 0 := by simp [nth_zero, h]
                                                       -- 🎉 no goals
#align nat.nth_zero_of_zero Nat.nth_zero_of_zero

theorem nth_zero_of_exists [DecidablePred p] (h : ∃ n, p n) : nth p 0 = Nat.find h := by
  rw [nth_zero]; convert Nat.sInf_def h
  -- ⊢ sInf (setOf p) = Nat.find h
                 -- 🎉 no goals
#align nat.nth_zero_of_exists Nat.nth_zero_of_exists

theorem nth_eq_zero {n} :
    nth p n = 0 ↔ p 0 ∧ n = 0 ∨ ∃ hf : (setOf p).Finite, hf.toFinset.card ≤ n := by
  refine' ⟨fun h => _, _⟩
  -- ⊢ p 0 ∧ n = 0 ∨ ∃ hf, card (Set.Finite.toFinset hf) ≤ n
  · simp only [or_iff_not_imp_right, not_exists, not_le]
    -- ⊢ (∀ (x : Set.Finite (setOf p)), n < card (Set.Finite.toFinset x)) → p 0 ∧ n = 0
    exact fun hn => ⟨h ▸ nth_mem _ hn, nonpos_iff_eq_zero.1 <| h ▸ le_nth hn⟩
    -- 🎉 no goals
  · rintro (⟨h₀, rfl⟩ | ⟨hf, hle⟩)
    -- ⊢ nth p 0 = 0
    exacts [nth_zero_of_zero h₀, nth_of_card_le hf hle]
    -- 🎉 no goals
#align nat.nth_eq_zero Nat.nth_eq_zero

theorem nth_eq_zero_mono (h₀ : ¬p 0) {a b : ℕ} (hab : a ≤ b) (ha : nth p a = 0) : nth p b = 0 := by
  simp only [nth_eq_zero, h₀, false_and_iff, false_or_iff] at ha ⊢
  -- ⊢ ∃ hf, card (Set.Finite.toFinset hf) ≤ b
  exact ha.imp fun hf hle => hle.trans hab
  -- 🎉 no goals
#align nat.nth_eq_zero_mono Nat.nth_eq_zero_mono

theorem le_nth_of_lt_nth_succ {k a : ℕ} (h : a < nth p (k + 1)) (ha : p a) : a ≤ nth p k := by
  cases' (setOf p).finite_or_infinite with hf hf
  -- ⊢ a ≤ nth p k
  · rcases exists_lt_card_finite_nth_eq hf ha with ⟨n, hn, rfl⟩
    -- ⊢ nth p n ≤ nth p k
    cases' lt_or_le (k + 1) hf.toFinset.card with hk hk
    -- ⊢ nth p n ≤ nth p k
    · rwa [(nth_strictMonoOn hf).lt_iff_lt hn hk, lt_succ_iff,
        ← (nth_strictMonoOn hf).le_iff_le hn (k.lt_succ_self.trans hk)] at h
    · rw [nth_of_card_le _ hk] at h
      -- ⊢ nth p n ≤ nth p k
      exact absurd h (zero_le _).not_lt
      -- 🎉 no goals
  · rcases subset_range_nth ha with ⟨n, rfl⟩
    -- ⊢ nth p n ≤ nth p k
    rwa [nth_lt_nth hf, lt_succ_iff, ← nth_le_nth hf] at h
    -- 🎉 no goals
#align nat.le_nth_of_lt_nth_succ Nat.le_nth_of_lt_nth_succ

section Count

variable (p) [DecidablePred p]

@[simp]
theorem count_nth_zero : count p (nth p 0) = 0 := by
  rw [count_eq_card_filter_range, card_eq_zero, filter_eq_empty_iff, nth_zero]
  -- ⊢ ∀ (x : ℕ), x ∈ range (sInf (setOf p)) → ¬p x
  exact fun n h₁ h₂ => (mem_range.1 h₁).not_le (Nat.sInf_le h₂)
  -- 🎉 no goals
#align nat.count_nth_zero Nat.count_nth_zero

theorem filter_range_nth_subset_insert (k : ℕ) :
    (range (nth p (k + 1))).filter p ⊆ insert (nth p k) ((range (nth p k)).filter p) := by
  intro a ha
  -- ⊢ a ∈ insert (nth p k) (filter p (range (nth p k)))
  simp only [mem_insert, mem_filter, mem_range] at ha ⊢
  -- ⊢ a = nth p k ∨ a < nth p k ∧ p a
  exact (le_nth_of_lt_nth_succ ha.1 ha.2).eq_or_lt.imp_right fun h => ⟨h, ha.2⟩
  -- 🎉 no goals
#align nat.filter_range_nth_subset_insert Nat.filter_range_nth_subset_insert

variable {p}

theorem filter_range_nth_eq_insert {k : ℕ}
    (hlt : ∀ hf : (setOf p).Finite, k + 1 < hf.toFinset.card) :
    (range (nth p (k + 1))).filter p = insert (nth p k) ((range (nth p k)).filter p) := by
  refine' (filter_range_nth_subset_insert p k).antisymm fun a ha => _
  -- ⊢ a ∈ filter p (range (nth p (k + 1)))
  simp only [mem_insert, mem_filter, mem_range] at ha ⊢
  -- ⊢ a < nth p (k + 1) ∧ p a
  have : nth p k < nth p (k + 1) := nth_lt_nth' k.lt_succ_self hlt
  -- ⊢ a < nth p (k + 1) ∧ p a
  rcases ha with (rfl | ⟨hlt, hpa⟩)
  -- ⊢ nth p k < nth p (k + 1) ∧ p (nth p k)
  · exact ⟨this, nth_mem _ fun hf => k.lt_succ_self.trans (hlt hf)⟩
    -- 🎉 no goals
  · exact ⟨hlt.trans this, hpa⟩
    -- 🎉 no goals
#align nat.filter_range_nth_eq_insert Nat.filter_range_nth_eq_insert

theorem filter_range_nth_eq_insert_of_finite (hf : (setOf p).Finite) {k : ℕ}
    (hlt : k + 1 < hf.toFinset.card) :
    (range (nth p (k + 1))).filter p = insert (nth p k) ((range (nth p k)).filter p) :=
  filter_range_nth_eq_insert fun _ => hlt
#align nat.filter_range_nth_eq_insert_of_finite Nat.filter_range_nth_eq_insert_of_finite

theorem filter_range_nth_eq_insert_of_infinite (hp : (setOf p).Infinite) (k : ℕ) :
    (range (nth p (k + 1))).filter p = insert (nth p k) ((range (nth p k)).filter p) :=
  filter_range_nth_eq_insert fun hf => absurd hf hp
#align nat.filter_range_nth_eq_insert_of_infinite Nat.filter_range_nth_eq_insert_of_infinite

theorem count_nth {n : ℕ} (hn : ∀ hf : (setOf p).Finite, n < hf.toFinset.card) :
    count p (nth p n) = n := by
  induction' n with k ihk
  -- ⊢ count p (nth p zero) = zero
  · exact count_nth_zero _
    -- 🎉 no goals
  · rw [count_eq_card_filter_range, filter_range_nth_eq_insert hn, card_insert_of_not_mem, ←
      count_eq_card_filter_range, ihk fun hf => lt_of_succ_lt (hn hf)]
    simp
    -- 🎉 no goals
#align nat.count_nth Nat.count_nth

theorem count_nth_of_lt_card_finite {n : ℕ} (hp : (setOf p).Finite) (hlt : n < hp.toFinset.card) :
    count p (nth p n) = n :=
  count_nth fun _ => hlt
#align nat.count_nth_of_lt_card_finite Nat.count_nth_of_lt_card_finite

theorem count_nth_of_infinite (hp : (setOf p).Infinite) (n : ℕ) : count p (nth p n) = n :=
  count_nth fun hf => absurd hf hp
#align nat.count_nth_of_infinite Nat.count_nth_of_infinite

theorem count_nth_succ {n : ℕ} (hn : ∀ hf : (setOf p).Finite, n < hf.toFinset.card) :
    count p (nth p n + 1) = n + 1 := by rw [count_succ, count_nth hn, if_pos (nth_mem _ hn)]
                                        -- 🎉 no goals
#align nat.count_nth_succ Nat.count_nth_succ

@[simp]
theorem nth_count {n : ℕ} (hpn : p n) : nth p (count p n) = n :=
  have : ∀ hf : (setOf p).Finite, count p n < hf.toFinset.card := fun hf => count_lt_card hf hpn
  count_injective (nth_mem _ this) hpn (count_nth this)
#align nat.nth_count Nat.nth_count

theorem nth_lt_of_lt_count {n k : ℕ} (h : k < count p n) : nth p k < n := by
  refine' (count_monotone p).reflect_lt _
  -- ⊢ count p (nth p k) < count p n
  rwa [count_nth]
  -- ⊢ ∀ (hf : Set.Finite (setOf p)), k < card (Set.Finite.toFinset hf)
  exact fun hf => h.trans_le (count_le_card hf n)
  -- 🎉 no goals
#align nat.nth_lt_of_lt_count Nat.nth_lt_of_lt_count

theorem le_nth_of_count_le {n k : ℕ} (h : n ≤ nth p k) : count p n ≤ k :=
  not_lt.1 fun hlt => h.not_lt <| nth_lt_of_lt_count hlt
#align nat.le_nth_of_count_le Nat.le_nth_of_count_le

variable (p)

theorem nth_count_eq_sInf (n : ℕ) : nth p (count p n) = sInf {i : ℕ | p i ∧ n ≤ i} := by
  refine' (nth_eq_sInf _ _).trans (congr_arg sInf _)
  -- ⊢ {x | p x ∧ ∀ (k : ℕ), k < count p n → nth p k < x} = {i | p i ∧ n ≤ i}
  refine' Set.ext fun a => and_congr_right fun hpa => _
  -- ⊢ (∀ (k : ℕ), k < count p n → nth p k < a) ↔ n ≤ a
  refine' ⟨fun h => not_lt.1 fun ha => _, fun hn k hk => lt_of_lt_of_le (nth_lt_of_lt_count hk) hn⟩
  -- ⊢ False
  have hn : nth p (count p a) < a := h _ (count_strict_mono hpa ha)
  -- ⊢ False
  rwa [nth_count hpa, lt_self_iff_false] at hn
  -- 🎉 no goals
#align nat.nth_count_eq_Inf Nat.nth_count_eq_sInf

variable {p}

theorem le_nth_count' {n : ℕ} (hpn : ∃ k, p k ∧ n ≤ k) : n ≤ nth p (count p n) :=
  (le_csInf hpn fun _ => And.right).trans (nth_count_eq_sInf p n).ge
#align nat.le_nth_count' Nat.le_nth_count'

theorem le_nth_count (hp : (setOf p).Infinite) (n : ℕ) : n ≤ nth p (count p n) :=
  let ⟨m, hp, hn⟩ := hp.exists_gt n
  le_nth_count' ⟨m, hp, hn.le⟩
#align nat.le_nth_count Nat.le_nth_count

/-- If a predicate `p : ℕ → Prop` is true for infinitely many numbers, then `Nat.count p` and
`Nat.nth p` form a Galois insertion. -/
noncomputable def giCountNth (hp : (setOf p).Infinite) : GaloisInsertion (count p) (nth p) :=
  GaloisInsertion.monotoneIntro (nth_monotone hp) (count_monotone p) (le_nth_count hp)
    (count_nth_of_infinite hp)
#align nat.gi_count_nth Nat.giCountNth

theorem gc_count_nth (hp : (setOf p).Infinite) : GaloisConnection (count p) (nth p) :=
  (giCountNth hp).gc
#align nat.gc_count_nth Nat.gc_count_nth

theorem count_le_iff_le_nth (hp : (setOf p).Infinite) {a b : ℕ} : count p a ≤ b ↔ a ≤ nth p b :=
  gc_count_nth hp _ _
#align nat.count_le_iff_le_nth Nat.count_le_iff_le_nth

theorem lt_nth_iff_count_lt (hp : (setOf p).Infinite) {a b : ℕ} : a < count p b ↔ nth p a < b :=
  (gc_count_nth hp).lt_iff_lt
#align nat.lt_nth_iff_count_lt Nat.lt_nth_iff_count_lt

end Count

end Nat
