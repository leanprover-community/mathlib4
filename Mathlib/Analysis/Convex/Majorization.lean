/-
Copyright (c) 2026 Marcin Bugaj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcin Bugaj
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.OrderDual
public import Mathlib.Data.Fin.SuccPredOrder
public import Mathlib.Order.SuccPred.Archimedean
public import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# Majorization

The majorization preorder on `Fin n → ℝ`. We say `a ≺ b` ("`a` is majorized by `b`") when the two
tuples have equal total sum and, after sorting both in decreasing order, every prefix sum of `a` is
bounded by the corresponding prefix sum of `b`.

## Main definitions

* `Majorizes a b` (notation `a ≺ b`): the majorization relation.
* `TTransform b a k l lambda` and `RelatedByTTransform b a`: a single T-transform (Robin Hood
  transfer) pulling the coordinates `a k > a l` toward each other while fixing their sum and the
  other coordinates.
* `discrepancy a b`: the number of coordinates at which `a` and `b` differ; the measure driving the
  T-transform decomposition.

## Main statements

* `Majorizes.refl`, `Majorizes.trans`, the `Trans` instance: `≺` is a preorder.
* `majorizes_iff_reflTransGen_relatedByTTransform`: `a ≺ b` iff the decreasing rearrangement of
  `a` is reachable from that of `b` by a finite chain of T-transforms (both directions).

## Notation

* `a ≺ b` : `Majorizes a b`.

## References

* [Marshall–Olkin–Arnold, *Inequalities: Theory of Majorization*][marshallOlkinArnold2011]
* [Hardy–Littlewood–Pólya, *Inequalities*][hardyLittlewoodPolya1952]

## Tags

majorization, T-transform, Robin Hood transfer
-/

@[expose] public section

namespace Majorization

open OrderDual Tuple Finset

variable {n : ℕ} {α : Type*} [LinearOrder α] (f : Fin n → α)

/-! ### Sorting into decreasing order and partial sums -/

/-- A permutation that sorts `f` into decreasing (antitone) order. -/
noncomputable def sortDesc : Equiv.Perm (Fin n) :=
  Tuple.sort (toDual ∘ f)

lemma antitone_comp_sortDesc : Antitone (f ∘ sortDesc f) := by
  have hmono : Monotone ((toDual ∘ f) ∘ Tuple.sort (toDual ∘ f)) := Tuple.monotone_sort _
  rw [Function.comp_assoc] at hmono
  exact monotone_toDual_comp_iff.mp hmono

/-- The prefix sum `∑_{x < i} (a ∘ σ) x` of `a` reindexed by the permutation `σ`. -/
noncomputable def partialSum (i : Fin n) (a : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ x < i, (a ∘ σ) x

/-! ### The majorization relation `≺` -/

/-- `a1` is majorized by `a2` (notation `a1 ≺ a2`): the two tuples have equal total sum, and
every prefix sum of the decreasing rearrangement of `a1` is at most the corresponding prefix sum
of `a2`. -/
structure Majorizes (a1 a2 : Fin n → ℝ) : Prop where
  /-- The two tuples have equal total sum. -/
  sum : ∑ x : Fin n, a1 x = ∑ x : Fin n, a2 x
  /-- Every prefix sum of the decreasing rearrangement of `a1` is at most that of `a2`. -/
  sums : ∀ i : Fin n, partialSum i a1 (sortDesc a1) ≤ partialSum i a2 (sortDesc a2)

@[inherit_doc] scoped infix:50 " ≺ " => Majorizes

private lemma partialSum_congr_of_antitone
    {a : Fin n → ℝ} {p1 p2 : Equiv.Perm (Fin n)}
    (h1 : Antitone (a ∘ p1)) (h2 : Antitone (a ∘ p2)) (i : Fin n) :
    partialSum i a p1 = partialSum i a p2 := by
  unfold partialSum
  rw [Tuple.unique_antitone h1 h2]

lemma sum_comp_perm {a : Fin n → ℝ} {σ : Equiv.Perm (Fin n)} :
    ∑ x, (a ∘ σ) x = ∑ x, a x := Equiv.sum_comp σ a

private lemma comp_perm_comp_sortDesc {σ : Equiv.Perm (Fin n)} :
    (f ∘ σ) ∘ (sortDesc (f ∘ ⇑σ)) = f ∘ (sortDesc f) := by
  have hcomp : f ∘ (σ * sortDesc (f ∘ σ)) = f ∘ (sortDesc f) :=
    Tuple.unique_antitone
      (by rw [Equiv.Perm.coe_mul, ← Function.comp_assoc]; exact antitone_comp_sortDesc (f ∘ ⇑σ))
      (antitone_comp_sortDesc f)
  rwa [Equiv.Perm.coe_mul, ← Function.comp_assoc] at hcomp

lemma partialSum_comp_perm {a : Fin n → ℝ} {σ : Equiv.Perm (Fin n)} {i : Fin n} :
    partialSum i (a ∘ σ) (sortDesc (a ∘ σ)) = partialSum i a (sortDesc a) := by
  unfold partialSum
  rw [comp_perm_comp_sortDesc]

lemma comp_perm_majorizes_iff {a b : Fin n → ℝ} {σ : Equiv.Perm (Fin n)} :
    a ∘ σ ≺ b ↔ a ≺ b := by
  constructor <;> rintro ⟨hsum, hsums⟩ <;>
    exact ⟨by simpa only [sum_comp_perm] using hsum,
           fun i ↦ by simpa only [partialSum_comp_perm] using hsums i⟩

lemma majorizes_comp_perm_iff {a b : Fin n → ℝ} {σ : Equiv.Perm (Fin n)} :
    a ≺ b ∘ σ ↔ a ≺ b := by
  constructor <;> rintro ⟨hsum, hsums⟩ <;>
    exact ⟨by simpa only [sum_comp_perm] using hsum,
           fun i ↦ by simpa only [partialSum_comp_perm] using hsums i⟩

lemma Majorizes.refl (a : Fin n → ℝ) : a ≺ a :=
  ⟨rfl, fun _ ↦ le_rfl⟩

lemma Majorizes.trans {a b c : Fin n → ℝ} (h1 : a ≺ b) (h2 : b ≺ c) : a ≺ c :=
  ⟨h1.sum.trans h2.sum, fun i ↦ (h1.sums i).trans (h2.sums i)⟩

instance : Trans (@Majorizes n) (@Majorizes n) (@Majorizes n) where
  trans := Majorizes.trans

/-! ### T-transforms and discrepancy -/

/-- `TTransform b a k l lambda`: `b` is a single T-transform (Robin Hood transfer) of `a` at
coordinates `k`, `l` with parameter `lambda ∈ (0, 1)`, pulling `a k > a l` toward each other while
fixing their sum and every other coordinate. -/
structure TTransform {n} (b a : Fin n → ℝ) (k l : Fin n) (lambda : ℝ) : Prop where
  /-- The transfer parameter lies strictly between `0` and `1`. -/
  lambda_0_1 : 0 < lambda ∧ lambda < 1
  /-- The coordinate `k` dominates the coordinate `l` in `a`. -/
  ak_gt_al : a k > a l
  /-- `b` agrees with `a` away from `k` and `l`. -/
  other_unchanged : ∀ (i : Fin n), i ≠ k ∧ i ≠ l → a i = b i
  /-- `b k` moves `a k` toward `a l` by a `lambda`-fraction of their gap. -/
  bk : b k = a k + (a l - a k) * lambda
  /-- `b l` moves `a l` toward `a k` by the same amount, keeping `b k + b l = a k + a l`. -/
  bl : b l = a l - (a l - a k) * lambda

/-- `b` is obtained from `a` by some single T-transform. -/
def RelatedByTTransform {n} (b a : Fin n → ℝ) : Prop :=
  ∃ k l : Fin n, ∃ lambda : ℝ, TTransform b a k l lambda

/-- The number of coordinates at which `a` and `b` differ. -/
noncomputable def discrepancy (a b : Fin n → ℝ) : Nat := #{i | a i ≠ b i}

lemma exists_sub_ne_zero_of_discrepancy_ne_zero {a b : Fin n → ℝ} :
  discrepancy a b ≠ 0 → ∃ k : Fin n, a k - b k ≠ 0 := by
  intro hd
  unfold discrepancy at hd
  obtain ⟨k, hk⟩ := Finset.card_ne_zero.mp hd
  exact ⟨k, sub_ne_zero.mpr (Finset.mem_filter.mp hk).2⟩

lemma discrepancy_comm {a b : Fin n → ℝ} : discrepancy a b = discrepancy b a := by
  unfold discrepancy
  congr 1
  ext i
  simp [ne_comm]

lemma discrepancy_zero_iff_eq {a b : Fin n → ℝ} : a = b ↔ discrepancy a b = 0 :=
  ⟨ fun hab ↦ by unfold discrepancy; simp [hab]
  , fun disc_zero ↦ by
      unfold discrepancy at disc_zero
      have hall_eq := Finset.card_filter_eq_zero_iff.mp disc_zero
      simp only [mem_univ, ne_eq, Decidable.not_not, forall_const] at hall_eq
      rw [funext_iff.mpr hall_eq]
  ⟩

/-! ### A single T-transform implies majorization -/

@[to_additive]
lemma prod_split_two {ι M} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    {k l : ι} (lnk : l ≠ k) (g : ι → M) :
    ∏ i, g i = (∏ i with i ≠ k ∧ i ≠ l, g i) * g l * g k := by
  rw [← Finset.prod_erase_mul Finset.univ g (Fintype.complete k),
      ← Finset.prod_erase_mul (Finset.univ.erase k) g
          (Finset.mem_erase.mpr ⟨lnk, Fintype.complete _⟩),
      show (Finset.univ.erase k).erase l = Finset.univ.filter (fun x ↦ x ≠ k ∧ x ≠ l) from by
        ext x; simp [Finset.mem_erase, and_comm]]

lemma sum_le_sum_Iio_of_antitone {a : Fin n → ℝ} {i : Fin n} {p : Finset (Fin n)}
    (antitone : Antitone a) (peqi : #p = i) : (∑ x ∈ p, a x) ≤ (∑ x < i, a x) := by
  let ai := a i
  rw [← Finset.sum_inter_add_sum_sdiff p (Iio i) (a ·),
      ← Finset.sum_inter_add_sum_sdiff (Iio i) p (a ·),
      Finset.inter_comm (Iio i) p]
  apply add_le_add_right
  have hextra_le : ∑ x ∈ p \ Iio i, a x ≤ #(p \ Iio i) * ai := by
    rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_Iio, not_lt] at hx
    exact antitone hx.2
  have hmissing_ge : #(Iio i \ p) * ai ≤ ∑ x ∈ Iio i \ p, a x := by
    rw [← nsmul_eq_mul]
    apply Finset.card_nsmul_le_sum
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_Iio] at hx
    exact antitone (le_of_lt hx.1)
  have hsame_count : #(Iio i \ p) = #(p \ Iio i) := by
    rw [Finset.card_sdiff, Finset.card_sdiff, peqi, Fin.card_Iio i, inter_comm]
  rw [hsame_count] at hmissing_ge
  exact hextra_le.trans hmissing_ge

lemma subset_sum_le_sum_greatest {n} {a : Fin n → ℝ} {i : Fin n} {t : Finset (Fin n)}
    (hs : #t = (i : Nat)) : (∑ x ∈ t, a x) ≤ (∑ x < i, (a ∘ sortDesc a) x) := by
    let preimg := image (sortDesc a).symm t
    have hcard : #preimg = #t := Finset.card_image_of_injective t (sortDesc a).symm.injective
    let sortA := sortDesc a
    have hinj : Set.InjOn sortA preimg := Set.injOn_of_injective sortA.injective
    have ht_image : t = image sortA preimg := by
      rw [Finset.image_image, Equiv.self_comp_symm, Finset.image_id]
    rw [ht_image, Finset.sum_image hinj]
    exact sum_le_sum_Iio_of_antitone (antitone_comp_sortDesc a) (hcard.trans hs)

private lemma exists_subset_sum_le_of_relatedByTTransform {n} {a b : Fin n → ℝ}
    {s : Finset (Fin n)} (t : RelatedByTTransform a b) :
    ∃ t : Finset (Fin n), #t = #s ∧ ∑ x ∈ s, a x ≤ ∑ x ∈ t, b x := by
  obtain ⟨k, l, lambda, ttransform⟩ := t
  obtain ⟨lambda_0_1, ak_gt_al, other_unchanged, bk, bl⟩ := ttransform
  by_cases hks : k ∈ s <;> by_cases hls : l ∈ s
  · refine ⟨s, by rfl, ?m⟩
    have l_ne_k : l ≠ k := fun h ↦ ne_of_gt ak_gt_al (congrArg b h).symm
    rw [←Finset.sum_erase_add s (a ·) hks]
    rw [←Finset.sum_erase_add s (b ·) hks]
    rw [←Finset.sum_erase_add (s.erase k) (a ·) (Finset.mem_erase.mpr ⟨l_ne_k, hls⟩)]
    rw [←Finset.sum_erase_add (s.erase k) (b ·) (Finset.mem_erase.mpr ⟨l_ne_k, hls⟩)]
    rw [ show (s.erase k).erase l = s.filter (fun x ↦ x ≠ k ∧ x ≠ l) from by
        ext x; simp only [Finset.mem_erase, Finset.mem_filter]; tauto]
    rw [ show ∑ x ∈ s with x ≠ k ∧ x ≠ l, b x = ∑ x ∈ s with x ≠ k ∧ x ≠ l, a x from
        Finset.sum_congr rfl fun x hx ↦ other_unchanged x (Finset.mem_filter.mp hx).2]
    rw [show ∑ x ∈ s with x ≠ k ∧ x ≠ l, a x + a l + a k =
        (∑ x ∈ s with x ≠ k ∧ x ≠ l, a x) + (a l + a k) from by linarith]
    rw [show ∑ x ∈ s with x ≠ k ∧ x ≠ l, a x + b l + b k =
        (∑ x ∈ s with x ≠ k ∧ x ≠ l, a x) + (b l + b k) from by linarith]
    rw [add_le_add_iff_left]
    rw [bk, bl]
    simp only [sub_add_add_cancel, le_refl]
  · refine ⟨s, rfl, ?_⟩
    rw [←Finset.sum_erase_add s (a ·) hks]
    rw [ show ∑ x ∈ s.erase k, a x = ∑ x ∈ s.erase k, b x from
        Finset.sum_congr rfl fun x hx ↦
          (other_unchanged x ⟨(Finset.mem_erase.mp hx).1,
            (Finset.mem_erase.mp hx).2.ne_of_notMem hls⟩).symm]
    rw [bk]
    rw [show ∑ x ∈ s.erase k, b x + (b k + (b l - b k) * lambda) =
        (∑ x ∈ s.erase k, b x + b k) + (b l - b k) * lambda from by linarith]
    rw [Finset.sum_erase_add s (b ·) hks]
    have hbl_bk_nonpos : (b l - b k) * lambda ≤ 0 := by nlinarith
    simp [hbl_bk_nonpos]
  · refine ⟨insert k (s.erase l), ?_, ?_⟩
    · have hcard_erase := Finset.card_erase_of_mem hls
      have hcard_insert :=
        Finset.card_insert_of_notMem (Finset.not_mem_subset (Finset.erase_subset l s) hks)
      rw [hcard_erase] at hcard_insert
      have hs_ne : #s ≠ 0 := Finset.card_ne_zero_of_mem hls
      rwa [show #s - 1 + 1 = #s from by omega] at hcard_insert
    · rw [←Finset.sum_erase_add s (a ·) hls]
      rw [ show ∑ x ∈ s.erase l, a x = ∑ x ∈ s.erase l, b x from
          Finset.sum_congr rfl fun x hx ↦
            (other_unchanged x ⟨(Finset.mem_erase.mp hx).2.ne_of_notMem hks,
              (Finset.mem_erase.mp hx).1⟩).symm]
      rw [bl]
      rw [←Finset.sum_erase_add (insert k (s.erase l)) (b ·) (Finset.mem_insert_self k (s.erase l))]
      rw [show (insert k (s.erase l)).erase k = s.erase l from
          Finset.erase_insert (Finset.not_mem_subset (Finset.erase_subset l s) hks)]
      rw [add_le_add_iff_left]
      nlinarith [lambda_0_1.1, lambda_0_1.2, ak_gt_al]
  · -- Neither `k` nor `l` lies in `s`, so `a` and `b` agree on all of `s`.
    refine ⟨s, rfl, le_of_eq (Finset.sum_congr rfl fun x hx ↦ ?_)⟩
    have hxk : x ≠ k := hx.ne_of_notMem hks
    have hxl : x ≠ l := hx.ne_of_notMem hls
    exact (other_unchanged x ⟨hxk, hxl⟩).symm

private lemma exists_subset_sum_eq_sortDesc_prefix {i : Fin n} {a : Fin n → ℝ} :
    ∃ t : Finset (Fin n), #t = i ∧ (∑ x < i, (a ∘ sortDesc a) x) = ∑ x ∈ t, a x :=
  ⟨image (sortDesc a) (Iio i),
    (card_image_of_injective (Iio i) (sortDesc a).injective).trans (Fin.card_Iio i),
    (sum_image (sortDesc a).injective.injOn).symm⟩

lemma partialSum_domination {n} i {a b : Fin n → ℝ}
  (t : RelatedByTTransform a b) : partialSum i a (sortDesc a) ≤ partialSum i b (sortDesc b) := by
  unfold partialSum
  obtain ⟨t1, teqi, to_rewrite⟩ := exists_subset_sum_eq_sortDesc_prefix (a := a) (i := i)
  obtain ⟨t2, teqs, to_rewrite2⟩ := exists_subset_sum_le_of_relatedByTTransform t (s := t1)
  rw [to_rewrite]
  exact calc (∑ x ∈ t1, a x)
        _ ≤ ∑ x ∈ t2, b x := to_rewrite2
        _ ≤ ∑ x < i, (b ∘ (sortDesc b)) x := subset_sum_le_sum_greatest (a := b) (teqs.trans teqi)

lemma majorizes_of_relatedByTTransform {a b : Fin n → ℝ} :
  RelatedByTTransform a b → a ≺ b := by
  rintro ⟨k, l, lambda, tt⟩
  have l_ne_k : l ≠ k := fun h ↦ ne_of_gt tt.ak_gt_al (congrArg b h).symm
  refine ⟨?_, fun i ↦ partialSum_domination i ⟨k, l, lambda, tt⟩⟩
  have hrest : (∑ i with i ≠ k ∧ i ≠ l, a i) = ∑ i with i ≠ k ∧ i ≠ l, b i :=
    Finset.sum_congr rfl fun x hx ↦ (tt.other_unchanged x (Finset.mem_filter.mp hx).2).symm
  rw [sum_split_two l_ne_k a, sum_split_two l_ne_k b, hrest, tt.bk, tt.bl]
  ring

lemma majorizes_of_reflTransGen_relatedByTTransform {a b : Fin n → ℝ}
  (r : Relation.ReflTransGen RelatedByTTransform a b) : a ≺ b := by
  induction r
  case refl => exact Majorizes.refl a
  case tail _ _ _ related_by_ttransform majorizes =>
    exact majorizes.trans (majorizes_of_relatedByTTransform related_by_ttransform)



/-! ### Majorization implies a chain of T-transforms -/

/-- For an antitone tuple, `partialSum` (defined via `sortDesc`) is just the prefix sum. -/
lemma partialSum_eq_of_antitone {g : Fin n → ℝ} (hg : Antitone g) (j : Fin n) :
    partialSum j g (sortDesc g) = ∑ x < j, g x := by
  rw [partialSum_congr_of_antitone (antitone_comp_sortDesc g) (p2 := 1) (by simpa using hg) j,
      partialSum]
  simp

private lemma tTransform_candidates {n} {a b : Fin n → ℝ} (ha : Antitone a) (hb : Antitone b)
  (majorizes : a ≺ b) (h : discrepancy a b ≠ 0) :
  ∃ k l : Fin n,
      k < l
    ∧ a k < b k
    ∧ a l > b l
    ∧ (∀ i : Fin n, i > k → i < l → a i = b i) := by
  -- The equal totals give `∑ (a - b) = 0`; with `a ≠ b` there is an index where `a` overtakes `b`.
  have a_b_diff_sum_eq_zero : ∑ i, (a i - b i) = 0 := by
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact majorizes.sum
  obtain ⟨some_l, pl⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero _ a_b_diff_sum_eq_zero
    (by simp only [mem_univ, ne_eq, true_and]; exact exists_sub_ne_zero_of_discrepancy_ne_zero h)
  simp only [mem_univ, sub_pos, true_and] at pl
  -- Majorization prefix sums, rewritten via antitonicity into honest prefix sums.
  have hpref : ∀ j : Fin n, ∑ x < j, a x ≤ ∑ x < j, b x := fun j ↦ by
    have hsums_j := majorizes.sums j
    rwa [partialSum_eq_of_antitone ha, partialSum_eq_of_antitone hb] at hsums_j
  -- `l` : the smallest index where `a` overtakes `b`; below it, minimality forces `a ≤ b`.
  -- (Extracted as an opaque index; keeping `min'` behind a `let` triggers `isDefEq` timeouts.)
  obtain ⟨l, hl_mem, hl_min⟩ :
      ∃ l : Fin n, a l > b l ∧ ∀ i, i < l → a i ≤ b i := by
    have hne : ({i | a i > b i} : Finset (Fin n)).Nonempty :=
      ⟨some_l, Finset.mem_filter.mpr ⟨mem_univ _, pl⟩⟩
    refine ⟨({i | a i > b i} : Finset (Fin n)).min' hne,
      (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2, fun i hil ↦ ?_⟩
    by_contra hgt
    exact absurd (Finset.min'_le ({i | a i > b i} : Finset (Fin n)) i
      (Finset.mem_filter.mpr ⟨mem_univ _, not_le.mp hgt⟩)) (not_le.mpr hil)
  -- `k` : the largest index below `l` with `a < b`; strictly between `k` and `l`, `a = b`.
  obtain ⟨k, hk_lt, hk_ab, hk_between⟩ :
      ∃ k : Fin n, k < l ∧ a k < b k ∧ ∀ i, k < i → i < l → a i = b i := by
    -- Nonemptiness: otherwise `a = b` below `l`, and the `l`-prefix sum contradicts `a l > b l`.
    have k_nonempty : ({i | i < l ∧ a i < b i} : Finset (Fin n)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hbelow : ∀ i, i < l → a i = b i := by
        intro i hil
        refine le_antisymm (hl_min i hil) (not_lt.mp fun hlt ↦ ?_)
        have hmem : i ∈ ({i | i < l ∧ a i < b i} : Finset (Fin n)) :=
          Finset.mem_filter.mpr ⟨mem_univ _, hil, hlt⟩
        rw [hempty] at hmem
        exact absurd hmem (Finset.notMem_empty i)
      have hsum_below : ∑ x < l, a x = ∑ x < l, b x :=
        Finset.sum_congr rfl fun i hi ↦ hbelow i (Finset.mem_Iio.mp hi)
      have hIic : ∑ x ∈ Finset.Iic l, a x ≤ ∑ x ∈ Finset.Iic l, b x := by
        by_cases hmax : IsMax l
        · have huniv : Finset.Iic l = Finset.univ := by
            ext x
            simp only [Finset.mem_Iic, mem_univ, iff_true]
            exact not_lt.mp fun hlt ↦ absurd (hmax hlt.le) (not_le.mpr hlt)
          rw [huniv]; exact le_of_eq majorizes.sum
        · have hset : Finset.Iio (Order.succ l) = Finset.Iic l := by
            ext x; rw [Finset.mem_Iio, Finset.mem_Iic, Order.lt_succ_iff_of_not_isMax hmax]
          have hpref_succ := hpref (Order.succ l)
          rwa [hset] at hpref_succ
      rw [show Finset.Iic l = insert l (Finset.Iio l) from (Finset.Iio_insert l).symm,
          Finset.sum_insert (by simp), Finset.sum_insert (by simp), hsum_below] at hIic
      exact absurd hl_mem (not_lt.mpr (by linarith))
    refine ⟨({i | i < l ∧ a i < b i} : Finset (Fin n)).max' k_nonempty, ?_, ?_,
      fun i hik hil ↦ ?_⟩
    · exact ((Finset.mem_filter.mp (Finset.max'_mem _ k_nonempty)).2).1
    · exact ((Finset.mem_filter.mp (Finset.max'_mem _ k_nonempty)).2).2
    · refine le_antisymm (hl_min i hil) (not_lt.mp fun hlt ↦ ?_)
      exact absurd (Finset.le_max' ({i | i < l ∧ a i < b i} : Finset (Fin n)) i
        (Finset.mem_filter.mpr ⟨mem_univ _, hil, hlt⟩)) (not_le.mpr hik)
  exact ⟨k, l, hk_lt, hk_ab, hl_mem, hk_between⟩

/-- One step of the T-transform decomposition: from `a ≺ b` (both antitone) with `a ≠ b`,
build a single T-transform `c` of `b` that is still majorized by `a`, is antitone, and is
strictly closer to `a` (measured by `discrepancy`). This is the non-recursive core; the
well-founded recursion lives in `reflTransGen_relatedByTTransform_of_majorizes`. -/
private lemma tTransform_step {a b : Fin n → ℝ} (ha : Antitone a) (hb : Antitone b)
    (majorizes : a ≺ b) (h : discrepancy a b ≠ 0) :
    ∃ c : Fin n → ℝ, RelatedByTTransform c b ∧ a ≺ c ∧ Antitone c ∧
      discrepancy a c < discrepancy a b := by
    obtain ⟨k, l, k_leq_l, a_k_leq_b_k, a_l_geq_b_k, equal_inbetween⟩ :=
      tTransform_candidates ha hb majorizes h
    have a_l_neq_b_l : a l ≠ b l := ne_of_gt a_l_geq_b_k
    have a_k_neq_b_k : a k ≠ b k := ne_of_lt a_k_leq_b_k
    let rho := (b k + b l) / 2
    let tau := (b k - b l) / 2
    let rho_a := (a k + a l) / 2
    let sigma := if rho < rho_a then a k - rho else rho - a l
    have sigma_lt_tau : sigma < tau := by
      by_cases h : rho < rho_a <;>
      (simp only [h, ↓reduceIte, sigma, rho, tau]; linarith[])
    have a_l_le_a_k : a l ≤ a k := ha (le_of_lt k_leq_l)
    have sigma_nonneg : sigma ≥ 0 := by
      by_cases h : rho < rho_a <;>
      (
        simp only [h, ↓reduceIte, ge_iff_le, sub_nonneg, sigma, rho]
        simp [rho, rho_a] at h
        linarith []
      )
    have knel : k ≠ l := ne_of_lt k_leq_l
    have bl_lt_bk : b l < b k := by linarith [a_l_le_a_k]
    have bl_bk_ne : b l - b k ≠ 0 := sub_ne_zero.mpr (ne_of_lt bl_lt_bk)
    have rho_add_tau : rho + tau = b k := by change (b k + b l) / 2 + (b k - b l) / 2 = b k; ring
    have rho_sub_tau : rho - tau = b l := by change (b k + b l) / 2 - (b k - b l) / 2 = b l; ring
    have tau_pos : 0 < tau := by linarith [rho_add_tau, rho_sub_tau, bl_lt_bk]
    let c : Fin n → ℝ := fun i ↦
      if i = k then rho + sigma else if i = l then rho - sigma else b i
    -- Values of `c` at `k`, `l`, and off `{k, l}`, plus the boundary estimates (shared by
    -- `hc : Antitone c` and `a ≺ c`).
    have hck : c k = rho + sigma := by simp only [c, ↓reduceIte]
    have hcl : c l = rho - sigma := by simp only [c, if_neg knel.symm, ↓reduceIte]
    have hci : ∀ m, m ≠ k → m ≠ l → c m = b m := by
      intro m hmk hml; simp only [c, if_neg hmk, if_neg hml]
    have ck_le_bk : c k ≤ b k := by rw [hck, ← rho_add_tau]; linarith [sigma_lt_tau]
    have bl_le_cl : b l ≤ c l := by rw [hcl, ← rho_sub_tau]; linarith [sigma_lt_tau]
    have cl_le_ck : c l ≤ c k := by rw [hck, hcl]; linarith [sigma_nonneg]
    have ak_le_ck : a k ≤ c k := by
      rw [hck]
      by_cases h : rho < rho_a <;>
        simp only [sigma, h, ↓reduceIte] <;> simp only [rho_a] at h <;>
        linarith [ha (le_of_lt k_leq_l)]
    have cl_le_al : c l ≤ a l := by
      rw [hcl]
      by_cases h : rho < rho_a <;>
        simp only [sigma, h, ↓reduceIte] <;> simp only [rho_a] at h <;>
        linarith [ha (le_of_lt k_leq_l)]
    have discrepancy_decreasing : discrepancy a c < discrepancy a b := by
      unfold discrepancy
      rw [Finset.card_filter, Finset.card_filter]
      rw [←Finset.sum_erase_add _ _ (Finset.mem_univ k)]
      rw [←Finset.sum_erase_add _ _ (Finset.mem_univ k)]
      rw [←Finset.sum_erase_add _ _ (Finset.mem_erase_of_ne_of_mem knel.symm (Finset.mem_univ l))]
      rw [←Finset.sum_erase_add _ _ (Finset.mem_erase_of_ne_of_mem knel.symm (Finset.mem_univ l))]
      rw [ show (Finset.univ.erase k).erase l = Finset.univ.filter (fun x ↦ x ≠ k ∧ x ≠ l) from by
           ext x; simp only [Finset.mem_erase, Finset.mem_filter]; tauto]
      rw [Finset.sum_congr
           (f := fun x ↦ if a x ≠ c x then 1 else 0)
           (g := fun x ↦ if a x ≠ b x then 1 else 0)
           rfl fun x e ↦ by
             obtain ⟨-, hxk, hxl⟩ := Finset.mem_filter.mp e
             rw [hci x hxk hxl]]
      rw [add_assoc, add_assoc]
      simp only [ne_eq, ite_not, add_lt_add_iff_left]
      by_cases h : rho < rho_a
      · have c_k_eq_a_k : c k = a k := by unfold c; simp[sigma, h]
        simp [c_k_eq_a_k, a_l_neq_b_l, a_k_neq_b_k]
        by_cases h : a l = c l <;> simp[h]
      · have c_l_eq_a_l : c l = a l := by unfold c; simp[knel.symm, sigma, h]
        simp [c_l_eq_a_l, a_l_neq_b_l, a_k_neq_b_k]
        by_cases h : a k = c k <;> simp[h]
    -- `c` is a single T-transform of `b`. Choosing lambda = (c k - b k)/(b l - b k) keeps the proof
    -- uniform across both `sigma` branches (we never unfold `sigma`; it stays an atom).
    have c_b_related_by_ttransform : RelatedByTTransform c b := by
      refine ⟨k, l, (rho + sigma - b k) / (b l - b k), ⟨?_, ?_⟩, bl_lt_bk, ?_, ?_, ?_⟩
      · exact div_pos_of_neg_of_neg (by linarith [sigma_lt_tau, rho_add_tau])
          (by linarith [bl_lt_bk])
      · exact div_lt_one_iff.mpr (Or.inr (Or.inr
          ⟨by linarith [bl_lt_bk], by linarith [sigma_nonneg, tau_pos, rho_sub_tau]⟩))
      · rintro i ⟨hik, hil⟩
        change b i = if i = k then rho + sigma else if i = l then rho - sigma else b i
        rw [if_neg hik, if_neg hil]
      · rw [mul_div_cancel₀ _ bl_bk_ne]
        change (if k = k then rho + sigma else if k = l then rho - sigma else b k)
              = b k + (rho + sigma - b k)
        rw [if_pos rfl]; ring
      · rw [mul_div_cancel₀ _ bl_bk_ne]
        change (if l = k then rho + sigma else if l = l then rho - sigma else b l)
              = b l - (rho + sigma - b k)
        rw [if_neg knel.symm, if_pos rfl]
        linarith [rho_add_tau, rho_sub_tau]
    have hc : Antitone c := by
      -- Textbook approach: for antitonicity on `Fin n` it suffices to check neighbours,
      -- `c (succ i) ≤ c i`. `c` differs from `b` only at `k`, `l`, so the only nontrivial
      -- transitions are those touching `k` or `l`; the rest is antitonicity of `b`.
      refine antitone_of_succ_le (fun i hi ↦ ?_)
      have hi_lt_succ : i < Order.succ i := (Order.lt_succ_iff_of_not_isMax hi).mpr le_rfl
      -- Explicit exhaustive 5-way split (no fall-through): the neighbour touches
      -- `k`, touches `l`, the index itself is `k`, is `l`, or both lie off `{k, l}`.
      have hcases : Order.succ i = k ∨ Order.succ i = l ∨
          (Order.succ i ≠ k ∧ Order.succ i ≠ l ∧ i = k) ∨
          (Order.succ i ≠ k ∧ Order.succ i ≠ l ∧ i = l) ∨
          (Order.succ i ≠ k ∧ Order.succ i ≠ l ∧ i ≠ k ∧ i ≠ l) := by tauto
      rcases hcases with hsk | hsl | ⟨hsk, hsl, rfl⟩ | ⟨hsk, hsl, rfl⟩ | ⟨hsk, hsl, hik, hil⟩
      · -- `succ i = k`, so `i < k`; off `{k, l}`, and `c k ≤ b k ≤ b i`.
        have hik : i < k := hsk ▸ hi_lt_succ
        rw [hsk, hci i (ne_of_lt hik) (ne_of_lt (hik.trans k_leq_l))]
        exact le_trans ck_le_bk (hb (le_of_lt hik))
      · -- `succ i = l`: either `i = k` (then `c l ≤ c k`),
        -- or `k < i < l` (via `equal_inbetween`).
        have hil : i < l := hsl ▸ hi_lt_succ
        rw [hsl]
        rcases eq_or_ne i k with rfl | hik
        · exact cl_le_ck
        · have hki : k < i :=
            lt_of_le_of_ne
              ((Order.lt_succ_iff_of_not_isMax hi).mp (hsl.symm ▸ k_leq_l)) (Ne.symm hik)
          rw [hci i hik (ne_of_lt hil), ← equal_inbetween i hki hil]
          exact le_trans cl_le_al (ha (le_of_lt hil))
      · -- `i = k`, `succ i < l`: `c (succ i) = a (succ i) ≤ a k ≤ c k`.
        have hsl' : Order.succ i < l := lt_of_le_of_ne (Order.succ_le_of_lt k_leq_l) hsl
        rw [hci (Order.succ i) hsk hsl, ← equal_inbetween (Order.succ i) hi_lt_succ hsl']
        exact le_trans (ha (le_of_lt hi_lt_succ)) ak_le_ck
      · -- `i = l`: `c (succ i) = b (succ i) ≤ b l ≤ c l`.
        rw [hci (Order.succ i) hsk hsl]
        exact le_trans (hb (le_of_lt hi_lt_succ)) bl_le_cl
      · -- `i` and `succ i` off `{k, l}`: plain antitonicity of `b`.
        rw [hci (Order.succ i) hsk hsl, hci i hik hil]
        exact hb (le_of_lt hi_lt_succ)
    have a_majorized_by_c : a ≺ c := by
      have hcb : c ≺ b := majorizes_of_relatedByTTransform c_b_related_by_ttransform
      refine ⟨majorizes.sum.trans hcb.sum.symm, fun i ↦ ?_⟩
      rw [partialSum_eq_of_antitone ha, partialSum_eq_of_antitone hc]
      have hab : ∀ j, ∑ x < j, a x ≤ ∑ x < j, b x := fun j ↦ by
        have := majorizes.sums j
        rwa [partialSum_eq_of_antitone ha, partialSum_eq_of_antitone hb] at this
      -- Flat 3-way split on the position of `i` relative to `k`, `l` (no nesting).
      rcases (by omega : i ≤ k ∨ (k < i ∧ i ≤ l) ∨ l < i) with hik | ⟨hik, hil⟩ | hil
      · -- i ≤ k : on `Iio i` we have `c = b`
        have heq : ∑ x < i, c x = ∑ x < i, b x :=
          Finset.sum_congr rfl fun x hx ↦ by
            have hxk : x < k := lt_of_lt_of_le (Finset.mem_Iio.mp hx) hik
            exact hci x (ne_of_lt hxk) (ne_of_lt (hxk.trans k_leq_l))
        rw [heq]; exact hab i
      · -- k < i ≤ l : `c = b` off `k`, and `a = b` on `(k, i)`
        have hk_mem : k ∈ Finset.Iio i := Finset.mem_Iio.mpr hik
        have hc_eq : ∑ x < i, c x = (∑ x < i, b x) + (c k - b k) := by
          rw [← Finset.sum_erase_add (Finset.Iio i) c hk_mem,
              ← Finset.sum_erase_add (Finset.Iio i) b hk_mem,
              Finset.sum_congr rfl (g := b) fun x hx ↦ by
                rw [Finset.mem_erase, Finset.mem_Iio] at hx
                exact hci x hx.1 (ne_of_lt (lt_of_lt_of_le hx.2 hil))]
          ring
        have hsplit : (∑ x < i, a x) - (∑ x < i, b x)
            = ((∑ x < k, a x) - (∑ x < k, b x)) + (a k - b k) := by
          rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
              ← Finset.sum_erase_add (Finset.Iio i) (fun x ↦ a x - b x) hk_mem]
          congr 1
          refine (Finset.sum_subset (fun x hx ↦ ?_) (fun x hx hx' ↦ ?_)).symm
          · rw [Finset.mem_erase, Finset.mem_Iio]
            exact ⟨ne_of_lt (Finset.mem_Iio.mp hx), (Finset.mem_Iio.mp hx).trans hik⟩
          · rw [Finset.mem_erase, Finset.mem_Iio] at hx
            rw [Finset.mem_Iio, not_lt] at hx'
            exact sub_eq_zero.mpr
              (equal_inbetween x (lt_of_le_of_ne hx' (Ne.symm hx.1)) (lt_of_lt_of_le hx.2 hil))
        rw [hc_eq]; linarith [hsplit, hab k, ak_le_ck]
      · -- i > l : the differences at `k` and `l` cancel (total sum preserved)
        have hk_mem : k ∈ Finset.Iio i := Finset.mem_Iio.mpr (k_leq_l.trans hil)
        have hl_mem : l ∈ (Finset.Iio i).erase k :=
          Finset.mem_erase.mpr ⟨knel.symm, Finset.mem_Iio.mpr hil⟩
        have hsum2 : c k + c l = b k + b l := by
          rw [hck, hcl]; linarith [rho_add_tau, rho_sub_tau]
        have hc_eq : ∑ x < i, c x = ∑ x < i, b x := by
          rw [← Finset.sum_erase_add (Finset.Iio i) c hk_mem,
              ← Finset.sum_erase_add (Finset.Iio i) b hk_mem,
              ← Finset.sum_erase_add ((Finset.Iio i).erase k) c hl_mem,
              ← Finset.sum_erase_add ((Finset.Iio i).erase k) b hl_mem,
              Finset.sum_congr rfl (g := b) fun x hx ↦ by
                rw [Finset.mem_erase, Finset.mem_erase] at hx
                exact hci x hx.2.1 hx.1]
          linarith [hsum2]
        rw [hc_eq]; exact hab i
    exact ⟨c, c_b_related_by_ttransform, a_majorized_by_c, hc, discrepancy_decreasing⟩

/-- `a ≺ b` (both antitone) implies `a` is reachable from `b` by a finite chain of
T-transforms. Decreasing recursion on `discrepancy a b`, one step supplied by
`tTransform_step`. -/
lemma reflTransGen_relatedByTTransform_of_majorizes
  {a b : Fin n → ℝ} (ha : Antitone a) (hb : Antitone b) (majorizes : a ≺ b) :
  Relation.ReflTransGen RelatedByTTransform a b := by
  if h : discrepancy a b = 0 then
    have := discrepancy_zero_iff_eq.mpr h
    rw [this]
  else
    obtain ⟨c, hcb, hac, hcAnti, hlt⟩ := tTransform_step ha hb majorizes h
    exact Relation.ReflTransGen.tail
      (reflTransGen_relatedByTTransform_of_majorizes ha hcAnti hac) hcb
  termination_by discrepancy a b

/-- Majorization characterised by T-transforms: `a ≺ b` iff the decreasing rearrangement of `a`
is reachable from that of `b` by a finite chain of T-transforms. -/
lemma majorizes_iff_reflTransGen_relatedByTTransform {a b : Fin n → ℝ} :
  a ≺ b ↔ Relation.ReflTransGen RelatedByTTransform (a ∘ sortDesc a) (b ∘ sortDesc b) :=
    ⟨ by
        have hchain := reflTransGen_relatedByTTransform_of_majorizes
          (antitone_comp_sortDesc a) (antitone_comp_sortDesc b)
        rw [show (a ∘ sortDesc a ≺ b ∘ sortDesc b) = (a ≺ b) from
              propext (comp_perm_majorizes_iff.trans majorizes_comp_perm_iff)] at hchain
        exact hchain
    , fun h ↦ (comp_perm_majorizes_iff.trans majorizes_comp_perm_iff).mp
        (majorizes_of_reflTransGen_relatedByTTransform h)
    ⟩

end Majorization
