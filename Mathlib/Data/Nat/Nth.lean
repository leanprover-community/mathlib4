/-
Copyright (c) 2021 Vladimir Goryachev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Goryachev, Kyle Miller, Kim Morrison, Eric Rodriguez
-/
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.WellFounded
import Mathlib.Data.Finset.Sort

/-!
# The `n`th Number Satisfying a Predicate

This file defines a function for "what is the `n`th number that satisfies a given predicate `p`",
and provides lemmas that deal with this function and its connection to `Nat.count`.

## Main definitions

* `Nat.nth p n`: The `n`-th natural `k` (zero-indexed) such that `p k`. If there is no
  such natural (that is, `p` is true for at most `n` naturals), then `Nat.nth p n = 0`.

## Main results

* `Nat.nth_eq_orderEmbOfFin`: For a finitely-often true `p`, gives the cardinality of the set of
  numbers satisfying `p` above particular values of `nth p`
* `Nat.gc_count_nth`: Establishes a Galois connection between `Nat.nth p` and `Nat.count p`.
* `Nat.nth_eq_orderIsoOfNat`: For an infinitely-often true predicate, `nth` agrees with the
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
    if h : Set.Finite (setOf p) then h.toFinset.sort.getD n 0
    else @Nat.Subtype.orderIsoOfNat (setOf p) (Set.Infinite.to_subtype h) n

variable {p}

/-!
### Lemmas about `Nat.nth` on a finite set
-/


theorem nth_of_card_le (hf : (setOf p).Finite) {n : ℕ} (hn : #hf.toFinset ≤ n) :
    nth p n = 0 := by rw [nth, dif_pos hf, List.getD_eq_default]; rwa [Finset.length_sort]

theorem nth_eq_getD_sort (h : (setOf p).Finite) (n : ℕ) :
    nth p n = h.toFinset.sort.getD n 0 :=
  dif_pos h

theorem nth_eq_orderEmbOfFin (hf : (setOf p).Finite) {n : ℕ} (hn : n < #hf.toFinset) :
    nth p n = hf.toFinset.orderEmbOfFin rfl ⟨n, hn⟩ := by
  rw [nth_eq_getD_sort hf, Finset.orderEmbOfFin_apply, List.getD_eq_getElem, Fin.getElem_fin]

theorem nth_strictMonoOn (hf : (setOf p).Finite) :
    StrictMonoOn (nth p) (Set.Iio #hf.toFinset) := by
  rintro m (hm : m < _) n (hn : n < _) h
  simp only [nth_eq_orderEmbOfFin, *]
  exact OrderEmbedding.strictMono _ h

theorem nth_lt_nth_of_lt_card (hf : (setOf p).Finite) {m n : ℕ} (h : m < n)
    (hn : n < #hf.toFinset) : nth p m < nth p n :=
  nth_strictMonoOn hf (h.trans hn) hn h

theorem nth_le_nth_of_lt_card (hf : (setOf p).Finite) {m n : ℕ} (h : m ≤ n)
    (hn : n < #hf.toFinset) : nth p m ≤ nth p n :=
  (nth_strictMonoOn hf).monotoneOn (h.trans_lt hn) hn h

theorem lt_of_nth_lt_nth_of_lt_card (hf : (setOf p).Finite) {m n : ℕ} (h : nth p m < nth p n)
    (hm : m < #hf.toFinset) : m < n :=
  not_le.1 fun hle => h.not_ge <| nth_le_nth_of_lt_card hf hle hm

theorem le_of_nth_le_nth_of_lt_card (hf : (setOf p).Finite) {m n : ℕ} (h : nth p m ≤ nth p n)
    (hm : m < #hf.toFinset) : m ≤ n :=
  not_lt.1 fun hlt => h.not_gt <| nth_lt_nth_of_lt_card hf hlt hm

theorem nth_injOn (hf : (setOf p).Finite) : (Set.Iio #hf.toFinset).InjOn (nth p) :=
  (nth_strictMonoOn hf).injOn

theorem range_nth_of_finite (hf : (setOf p).Finite) : Set.range (nth p) = insert 0 (setOf p) := by
  simpa only [← List.getD_eq_getElem?_getD, ← nth_eq_getD_sort hf, mem_sort,
    Set.Finite.mem_toFinset] using Set.range_list_getD (hf.toFinset.sort (· ≤ ·)) 0

@[simp]
theorem image_nth_Iio_card (hf : (setOf p).Finite) : nth p '' Set.Iio #hf.toFinset = setOf p :=
  calc
    nth p '' Set.Iio #hf.toFinset = Set.range (hf.toFinset.orderEmbOfFin rfl) := by
      ext x
      simp only [Set.mem_image, Set.mem_range, Fin.exists_iff, ← nth_eq_orderEmbOfFin hf,
        Set.mem_Iio, exists_prop]
    _ = setOf p := by rw [range_orderEmbOfFin, Set.Finite.coe_toFinset]

theorem nth_mem_of_lt_card {n : ℕ} (hf : (setOf p).Finite) (hlt : n < #hf.toFinset) :
    p (nth p n) :=
  (image_nth_Iio_card hf).subset <| Set.mem_image_of_mem _ hlt

theorem exists_lt_card_finite_nth_eq (hf : (setOf p).Finite) {x} (h : p x) :
    ∃ n, n < #hf.toFinset ∧ nth p n = x := by
  rwa [← @Set.mem_setOf_eq _ _ p, ← image_nth_Iio_card hf] at h

/-!
### Lemmas about `Nat.nth` on an infinite set
-/

/-- When `s` is an infinite set, `nth` agrees with `Nat.Subtype.orderIsoOfNat`. -/
theorem nth_apply_eq_orderIsoOfNat (hf : (setOf p).Infinite) (n : ℕ) :
    nth p n = @Nat.Subtype.orderIsoOfNat (setOf p) hf.to_subtype n := by rw [nth, dif_neg hf]

/-- When `s` is an infinite set, `nth` agrees with `Nat.Subtype.orderIsoOfNat`. -/
theorem nth_eq_orderIsoOfNat (hf : (setOf p).Infinite) :
    nth p = (↑) ∘ @Nat.Subtype.orderIsoOfNat (setOf p) hf.to_subtype :=
  funext <| nth_apply_eq_orderIsoOfNat hf

theorem nth_strictMono (hf : (setOf p).Infinite) : StrictMono (nth p) := by
  rw [nth_eq_orderIsoOfNat hf]
  exact (Subtype.strictMono_coe _).comp (OrderIso.strictMono _)

theorem nth_injective (hf : (setOf p).Infinite) : Function.Injective (nth p) :=
  (nth_strictMono hf).injective

theorem nth_monotone (hf : (setOf p).Infinite) : Monotone (nth p) :=
  (nth_strictMono hf).monotone

theorem nth_lt_nth (hf : (setOf p).Infinite) {k n} : nth p k < nth p n ↔ k < n :=
  (nth_strictMono hf).lt_iff_lt

theorem nth_le_nth (hf : (setOf p).Infinite) {k n} : nth p k ≤ nth p n ↔ k ≤ n :=
  (nth_strictMono hf).le_iff_le

theorem range_nth_of_infinite (hf : (setOf p).Infinite) : Set.range (nth p) = setOf p := by
  rw [nth_eq_orderIsoOfNat hf]
  haveI := hf.to_subtype
  classical exact Nat.Subtype.coe_comp_ofNat_range

theorem nth_mem_of_infinite (hf : (setOf p).Infinite) (n : ℕ) : p (nth p n) :=
  Set.range_subset_iff.1 (range_nth_of_infinite hf).le n

/-!
### Lemmas that work for finite and infinite sets
-/

theorem exists_lt_card_nth_eq {x} (h : p x) :
    ∃ n, (∀ hf : (setOf p).Finite, n < #hf.toFinset) ∧ nth p n = x := by
  refine (setOf p).finite_or_infinite.elim (fun hf => ?_) fun hf => ?_
  · rcases exists_lt_card_finite_nth_eq hf h with ⟨n, hn, hx⟩
    exact ⟨n, fun _ => hn, hx⟩
  · rw [← @Set.mem_setOf_eq _ _ p, ← range_nth_of_infinite hf] at h
    rcases h with ⟨n, hx⟩
    exact ⟨n, fun hf' => absurd hf' hf, hx⟩

theorem subset_range_nth : setOf p ⊆ Set.range (nth p) := fun x (hx : p x) =>
  let ⟨n, _, hn⟩ := exists_lt_card_nth_eq hx
  ⟨n, hn⟩

theorem range_nth_subset : Set.range (nth p) ⊆ insert 0 (setOf p) :=
  (setOf p).finite_or_infinite.elim (fun h => (range_nth_of_finite h).subset) fun h =>
    (range_nth_of_infinite h).trans_subset (Set.subset_insert _ _)

theorem nth_mem (n : ℕ) (h : ∀ hf : (setOf p).Finite, n < #hf.toFinset) : p (nth p n) :=
  (setOf p).finite_or_infinite.elim (fun hf => nth_mem_of_lt_card hf (h hf)) fun h =>
    nth_mem_of_infinite h n

theorem nth_lt_nth' {m n : ℕ} (hlt : m < n) (h : ∀ hf : (setOf p).Finite, n < #hf.toFinset) :
    nth p m < nth p n :=
  (setOf p).finite_or_infinite.elim (fun hf => nth_lt_nth_of_lt_card hf hlt (h _)) fun hf =>
    (nth_lt_nth hf).2 hlt

theorem nth_le_nth' {m n : ℕ} (hle : m ≤ n) (h : ∀ hf : (setOf p).Finite, n < #hf.toFinset) :
    nth p m ≤ nth p n :=
  (setOf p).finite_or_infinite.elim (fun hf => nth_le_nth_of_lt_card hf hle (h _)) fun hf =>
    (nth_le_nth hf).2 hle

theorem le_nth {n : ℕ} (h : ∀ hf : (setOf p).Finite, n < #hf.toFinset) : n ≤ nth p n :=
  (setOf p).finite_or_infinite.elim
    (fun hf => ((nth_strictMonoOn hf).mono <| Set.Iic_subset_Iio.2 (h _)).Iic_id_le _ le_rfl)
    fun hf => (nth_strictMono hf).id_le _

theorem isLeast_nth {n} (h : ∀ hf : (setOf p).Finite, n < #hf.toFinset) :
    IsLeast {i | p i ∧ ∀ k < n, nth p k < i} (nth p n) :=
  ⟨⟨nth_mem n h, fun _k hk => nth_lt_nth' hk h⟩, fun _x hx =>
    let ⟨k, hk, hkx⟩ := exists_lt_card_nth_eq hx.1
    (lt_or_ge k n).elim (fun hlt => absurd hkx (hx.2 _ hlt).ne) fun hle => hkx ▸ nth_le_nth' hle hk⟩

theorem isLeast_nth_of_lt_card {n : ℕ} (hf : (setOf p).Finite) (hn : n < #hf.toFinset) :
    IsLeast {i | p i ∧ ∀ k < n, nth p k < i} (nth p n) :=
  isLeast_nth fun _ => hn

theorem isLeast_nth_of_infinite (hf : (setOf p).Infinite) (n : ℕ) :
    IsLeast {i | p i ∧ ∀ k < n, nth p k < i} (nth p n) :=
  isLeast_nth fun h => absurd h hf

/-- An alternative recursive definition of `Nat.nth`: `Nat.nth s n` is the infimum of `x ∈ s` such
that `Nat.nth s k < x` for all `k < n`, if this set is nonempty. We do not assume that the set is
nonempty because we use the same "garbage value" `0` both for `sInf` on `ℕ` and for `Nat.nth s n`
for `n ≥ #s`. -/
theorem nth_eq_sInf (p : ℕ → Prop) (n : ℕ) : nth p n = sInf {x | p x ∧ ∀ k < n, nth p k < x} := by
  by_cases hn : ∀ hf : (setOf p).Finite, n < #hf.toFinset
  · exact (isLeast_nth hn).csInf_eq.symm
  · push_neg at hn
    rcases hn with ⟨hf, hn⟩
    rw [nth_of_card_le _ hn]
    refine ((congr_arg sInf <| Set.eq_empty_of_forall_notMem fun k hk => ?_).trans sInf_empty).symm
    rcases exists_lt_card_nth_eq hk.1 with ⟨k, hlt, rfl⟩
    exact (hk.2 _ ((hlt hf).trans_le hn)).false

theorem nth_zero : nth p 0 = sInf (setOf p) := by rw [nth_eq_sInf]; simp

@[simp]
theorem nth_zero_of_zero (h : p 0) : nth p 0 = 0 := by simp [nth_zero, h]

theorem nth_zero_of_exists [DecidablePred p] (h : ∃ n, p n) : nth p 0 = Nat.find h := by
  rw [nth_zero]; convert Nat.sInf_def h

theorem nth_eq_zero {n} :
    nth p n = 0 ↔ p 0 ∧ n = 0 ∨ ∃ hf : (setOf p).Finite, #hf.toFinset ≤ n := by
  refine ⟨fun h => ?_, ?_⟩
  · simp only [or_iff_not_imp_right, not_exists, not_le]
    exact fun hn => ⟨h ▸ nth_mem _ hn, nonpos_iff_eq_zero.1 <| h ▸ le_nth hn⟩
  · rintro (⟨h₀, rfl⟩ | ⟨hf, hle⟩)
    exacts [nth_zero_of_zero h₀, nth_of_card_le hf hle]

lemma lt_card_toFinset_of_nth_ne_zero {n : ℕ} (h : nth p n ≠ 0) (hf : (setOf p).Finite) :
    n < #hf.toFinset := by
  simp only [ne_eq, nth_eq_zero, not_or, not_exists, not_le] at h
  exact h.2 hf

lemma nth_mem_of_ne_zero {n : ℕ} (h : nth p n ≠ 0) : p (Nat.nth p n) :=
  nth_mem n (lt_card_toFinset_of_nth_ne_zero h)

theorem nth_eq_zero_mono (h₀ : ¬p 0) {a b : ℕ} (hab : a ≤ b) (ha : nth p a = 0) : nth p b = 0 := by
  simp only [nth_eq_zero, h₀, false_and, false_or] at ha ⊢
  exact ha.imp fun hf hle => hle.trans hab

lemma nth_ne_zero_anti (h₀ : ¬p 0) {a b : ℕ} (hab : a ≤ b) (hb : nth p b ≠ 0) : nth p a ≠ 0 :=
  mt (nth_eq_zero_mono h₀ hab) hb

theorem le_nth_of_lt_nth_succ {k a : ℕ} (h : a < nth p (k + 1)) (ha : p a) : a ≤ nth p k := by
  rcases (setOf p).finite_or_infinite with hf | hf
  · rcases exists_lt_card_finite_nth_eq hf ha with ⟨n, hn, rfl⟩
    rcases lt_or_ge (k + 1) #hf.toFinset with hk | hk
    · rwa [(nth_strictMonoOn hf).lt_iff_lt hn hk, Nat.lt_succ_iff,
        ← (nth_strictMonoOn hf).le_iff_le hn (k.lt_succ_self.trans hk)] at h
    · rw [nth_of_card_le _ hk] at h
      exact absurd h (zero_le _).not_gt
  · rcases subset_range_nth ha with ⟨n, rfl⟩
    rwa [nth_lt_nth hf, Nat.lt_succ_iff, ← nth_le_nth hf] at h

lemma nth_mem_anti {a b : ℕ} (hab : a ≤ b) (h : p (nth p b)) : p (nth p a) := by
  by_cases h' : ∀ hf : (setOf p).Finite, a < #hf.toFinset
  · exact nth_mem a h'
  · simp only [not_forall, not_lt] at h'
    have h'b : ∃ hf : (setOf p).Finite, #hf.toFinset ≤ b := by
      rcases h' with ⟨hf, ha⟩
      exact ⟨hf, ha.trans hab⟩
    have ha0 : nth p a = 0 := by simp [nth_eq_zero, h']
    have hb0 : nth p b = 0 := by simp [nth_eq_zero, h'b]
    rw [ha0]
    rwa [hb0] at h

lemma nth_comp_of_strictMono {n : ℕ} {f : ℕ → ℕ} (hf : StrictMono f)
    (h0 : ∀ k, p k → k ∈ Set.range f) (h : ∀ hfi : (setOf p).Finite, n < hfi.toFinset.card) :
    f (nth (fun i ↦ p (f i)) n) = nth p n := by
  have hs {p' : ℕ → Prop} (h0p' : ∀ k, p' k → k ∈ Set.range f) :
      f '' {i | p' (f i)} = setOf p' := by
    ext i
    refine ⟨fun ⟨_, hi, h⟩ ↦ h ▸ hi, fun he ↦ ?_⟩
    rcases h0p' _ he with ⟨t, rfl⟩
    exact ⟨t, he, rfl⟩
  induction n using Nat.case_strong_induction_on
  case _ =>
    simp_rw [nth_zero]
    replace h := nth_mem _ h
    rw [← hs h0, ← hf.monotone.map_csInf]
    rcases h0 _ h with ⟨t, ht⟩
    exact ⟨t, Set.mem_setOf_eq ▸ ht ▸ h⟩
  case _ n ih =>
    repeat nth_rw 1 [nth_eq_sInf]
    have h0' : ∀ k', (p k' ∧ ∀ k < n + 1, nth p k < k') → k' ∈ Set.range f := fun _ h ↦ h0 _ h.1
    rw [← hs h0', ← hf.monotone.map_csInf]
    · convert rfl using 8 with k m' hm
      nth_rw 2 [← hf.lt_iff_lt]
      convert Iff.rfl using 2
      exact ih m' (Nat.lt_add_one_iff.mp hm) fun hfi ↦ hm.trans (h hfi)
    · rcases h0 _ (nth_mem _ h) with ⟨t, ht⟩
      exact ⟨t, ht ▸ (nth_mem _ h), fun _ hk ↦ ht ▸ nth_lt_nth' hk h⟩

lemma nth_add {m n : ℕ} (h0 : ∀ k < m, ¬p k) (h : nth p n ≠ 0) :
    nth (fun i ↦ p (i + m)) n + m = nth p n := by
  refine nth_comp_of_strictMono (strictMono_id.add_const m) (fun k hk ↦ ?_)
    (fun hf ↦ lt_card_toFinset_of_nth_ne_zero h hf)
  by_contra hn
  simp_rw [id_eq, Set.mem_range, eq_comm] at hn
  exact h0 _ (not_le.mp fun h ↦ hn (le_iff_exists_add'.mp h)) hk

lemma nth_add_eq_sub {m n : ℕ} (h0 : ∀ k < m, ¬p k) (h : nth p n ≠ 0) :
    nth (fun i ↦ p (i + m)) n = nth p n - m := by
  rw [← nth_add h0 h, Nat.add_sub_cancel]

lemma nth_add_one {n : ℕ} (h0 : ¬p 0) (h : nth p n ≠ 0) :
    nth (fun i ↦ p (i + 1)) n + 1 = nth p n :=
  nth_add (fun _ hk ↦ (lt_one_iff.1 hk ▸ h0)) h

lemma nth_add_one_eq_sub {n : ℕ} (h0 : ¬p 0) (h : nth p n ≠ 0) :
    nth (fun i ↦ p (i + 1)) n = nth p n - 1 :=
  nth_add_eq_sub (fun _ hk ↦ (lt_one_iff.1 hk ▸ h0)) h

section Count

variable (p) [DecidablePred p]

@[simp]
theorem count_nth_zero : count p (nth p 0) = 0 := by
  rw [count_eq_card_filter_range, card_eq_zero, filter_eq_empty_iff, nth_zero]
  exact fun n h₁ h₂ => (mem_range.1 h₁).not_ge (Nat.sInf_le h₂)

theorem filter_range_nth_subset_insert (k : ℕ) :
    {n ∈ range (nth p (k + 1)) | p n} ⊆ insert (nth p k) {n ∈ range (nth p k) | p n} := by
  intro a ha
  simp only [mem_insert, mem_filter, mem_range] at ha ⊢
  exact (le_nth_of_lt_nth_succ ha.1 ha.2).eq_or_lt.imp_right fun h => ⟨h, ha.2⟩

variable {p}

theorem filter_range_nth_eq_insert {k : ℕ}
    (hlt : ∀ hf : (setOf p).Finite, k + 1 < #hf.toFinset) :
    {n ∈ range (nth p (k + 1)) | p n} = insert (nth p k) {n ∈ range (nth p k) | p n} := by
  refine (filter_range_nth_subset_insert p k).antisymm fun a ha => ?_
  simp only [mem_insert, mem_filter, mem_range] at ha ⊢
  have : nth p k < nth p (k + 1) := nth_lt_nth' k.lt_succ_self hlt
  rcases ha with (rfl | ⟨hlt, hpa⟩)
  · exact ⟨this, nth_mem _ fun hf => k.lt_succ_self.trans (hlt hf)⟩
  · exact ⟨hlt.trans this, hpa⟩

theorem filter_range_nth_eq_insert_of_finite (hf : (setOf p).Finite) {k : ℕ}
    (hlt : k + 1 < #hf.toFinset) :
    {n ∈ range (nth p (k + 1)) | p n} = insert (nth p k) {n ∈ range (nth p k) | p n} :=
  filter_range_nth_eq_insert fun _ => hlt

theorem filter_range_nth_eq_insert_of_infinite (hp : (setOf p).Infinite) (k : ℕ) :
    {n ∈ range (nth p (k + 1)) | p n} = insert (nth p k) {n ∈ range (nth p k) | p n} :=
  filter_range_nth_eq_insert fun hf => absurd hf hp

theorem count_nth {n : ℕ} (hn : ∀ hf : (setOf p).Finite, n < #hf.toFinset) :
    count p (nth p n) = n := by
  induction n with
  | zero => exact count_nth_zero _
  | succ k ihk =>
    rw [count_eq_card_filter_range, filter_range_nth_eq_insert hn, card_insert_of_notMem,
      ← count_eq_card_filter_range, ihk fun hf => lt_of_succ_lt (hn hf)]
    simp

theorem count_nth_of_lt_card_finite {n : ℕ} (hp : (setOf p).Finite) (hlt : n < #hp.toFinset) :
    count p (nth p n) = n :=
  count_nth fun _ => hlt

theorem count_nth_of_infinite (hp : (setOf p).Infinite) (n : ℕ) : count p (nth p n) = n :=
  count_nth fun hf => absurd hf hp

theorem surjective_count_of_infinite_setOf (h : {n | p n}.Infinite) :
    Function.Surjective (Nat.count p) :=
  fun n => ⟨nth p n, count_nth_of_infinite h n⟩

theorem count_nth_succ {n : ℕ} (hn : ∀ hf : (setOf p).Finite, n < #hf.toFinset) :
    count p (nth p n + 1) = n + 1 := by rw [count_succ, count_nth hn, if_pos (nth_mem _ hn)]

lemma count_nth_succ_of_infinite (hp : (setOf p).Infinite) (n : ℕ) :
    count p (nth p n + 1) = n + 1 := by
  rw [count_succ, count_nth_of_infinite hp, if_pos (nth_mem_of_infinite hp _)]

@[simp]
theorem nth_count {n : ℕ} (hpn : p n) : nth p (count p n) = n :=
  have : ∀ hf : (setOf p).Finite, count p n < #hf.toFinset := fun hf => count_lt_card hf hpn
  count_injective (nth_mem _ this) hpn (count_nth this)

theorem nth_lt_of_lt_count {n k : ℕ} (h : k < count p n) : nth p k < n := by
  refine (count_monotone p).reflect_lt ?_
  rwa [count_nth]
  exact fun hf => h.trans_le (count_le_card hf n)

theorem le_nth_of_count_le {n k : ℕ} (h : n ≤ nth p k) : count p n ≤ k :=
  not_lt.1 fun hlt => h.not_gt <| nth_lt_of_lt_count hlt

protected theorem count_eq_zero (h : ∃ n, p n) {n : ℕ} : count p n = 0 ↔ n ≤ nth p 0 := by
  rw [nth_zero_of_exists h, le_find_iff h, Nat.count_iff_forall_not]

variable (p) in
theorem nth_count_eq_sInf (n : ℕ) : nth p (count p n) = sInf {i : ℕ | p i ∧ n ≤ i} := by
  refine (nth_eq_sInf _ _).trans (congr_arg sInf ?_)
  refine Set.ext fun a => and_congr_right fun hpa => ?_
  refine ⟨fun h => not_lt.1 fun ha => ?_, fun hn k hk => lt_of_lt_of_le (nth_lt_of_lt_count hk) hn⟩
  have hn : nth p (count p a) < a := h _ (count_strict_mono hpa ha)
  rwa [nth_count hpa, lt_self_iff_false] at hn

theorem le_nth_count' {n : ℕ} (hpn : ∃ k, p k ∧ n ≤ k) : n ≤ nth p (count p n) :=
  (le_csInf hpn fun _ => And.right).trans (nth_count_eq_sInf p n).ge

theorem le_nth_count (hp : (setOf p).Infinite) (n : ℕ) : n ≤ nth p (count p n) :=
  let ⟨m, hp, hn⟩ := hp.exists_gt n
  le_nth_count' ⟨m, hp, hn.le⟩

/-- If a predicate `p : ℕ → Prop` is true for infinitely many numbers, then `Nat.count p` and
`Nat.nth p` form a Galois insertion. -/
noncomputable def giCountNth (hp : (setOf p).Infinite) : GaloisInsertion (count p) (nth p) :=
  GaloisInsertion.monotoneIntro (nth_monotone hp) (count_monotone p) (le_nth_count hp)
    (count_nth_of_infinite hp)

theorem gc_count_nth (hp : (setOf p).Infinite) : GaloisConnection (count p) (nth p) :=
  (giCountNth hp).gc

theorem count_le_iff_le_nth (hp : (setOf p).Infinite) {a b : ℕ} : count p a ≤ b ↔ a ≤ nth p b :=
  gc_count_nth hp _ _

theorem lt_nth_iff_count_lt (hp : (setOf p).Infinite) {a b : ℕ} : a < count p b ↔ nth p a < b :=
  (gc_count_nth hp).lt_iff_lt

end Count

theorem nth_of_forall {n : ℕ} (hp : ∀ n' ≤ n, p n') : nth p n = n := by
  classical nth_rw 1 [← count_of_forall (hp · ·.le), nth_count (hp n le_rfl)]

@[simp] theorem nth_true (n : ℕ) : nth (fun _ ↦ True) n = n := nth_of_forall fun _ _ ↦ trivial

theorem nth_of_forall_not {n : ℕ} (hp : ∀ n' ≥ n, ¬p n') : nth p n = 0 := by
  have : setOf p ⊆ Finset.range n := by
    intro n' hn'
    contrapose! hp
    exact ⟨n', by simpa using hp, Set.mem_setOf.mp hn'⟩
  rw [nth_of_card_le ((finite_toSet _).subset this)]
  · refine (Finset.card_le_card ?_).trans_eq (Finset.card_range n)
    exact Set.Finite.toFinset_subset.mpr this

@[simp] theorem nth_false (n : ℕ) : nth (fun _ ↦ False) n = 0 := nth_of_forall_not fun _ _ ↦ id

end Nat
