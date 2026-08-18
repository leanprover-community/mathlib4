/-
Copyright (c) 2026 Marcin Bugaj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcin Bugaj
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.OrderDual
public import Mathlib.Data.Fin.SuccPredOrder
public import Mathlib.Order.SuccPred.Archimedean
public import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# Majorization

The majorization preorder on `ι → M` for a finite type `ι` and an ordered additive commutative
monoid `M` (`AddCommMonoid`, `LinearOrder`, `IsOrderedAddMonoid`; e.g. `ℝ`, `ℚ`, `ℝ≥0`, `ℝ≥0∞`). We
say `a ≺ b` ("`a` is majorized by `b`") when the two tuples have equal total sum and, for every `k`,
the maximal sum over `k`-element subsets of the coordinates of `a` is at most that of `b`.

This is classical (Hardy–Littlewood–Pólya / Schur) majorization: the order lives on the *values* of
`a` and `b` (needed to form `maxSubsetSum`), while the index `ι` need only be finite. Hence `≺` is
permutation-invariant (`comp_perm_majorizes_iff`, `majorizes_comp_perm_iff`). In particular it is
**not** first-order stochastic dominance — the pointwise comparison of the cumulative sums
`∑_{i ≤ t} a i` along a linearly ordered index — which is a genuinely different order.

The T-transform theory (`RelatedByTTransform`, the decomposition theorem) additionally needs
subtraction and division, so it lives over an ordered field `K` (`Field`, `LinearOrder`,
`IsStrictOrderedRing`; e.g. `ℝ`, `ℚ`).

## Main definitions

* `Majorizes a b` (notation `a ≺ b`): the majorization relation on `ι → M`, via `maxSubsetSum`.
* `TStep ι K` and `tTransform a s`: the data of a single T-transform (`k`, `l`, `t`) and its action
  on a vector — pull `s.k`, `s.l` toward each other by an `s.t`-fraction of their gap, fixing the
  rest.
* `RelatedByTTransform b a`: `b = tTransform a s` for some valid step `s` (a single Robin Hood
  transfer); a `List (TStep ι K)` records an explicit sequence of them.
* `majorizesTStepList`: from `a ≺ b`, the explicit `List (TStep …)` (as data) carrying sorted `b` to
  sorted `a`, bundled with its correctness — the `(a, b, proof) ↦ (list, proof)` function.
* `discrepancy a b`: the number of coordinates at which `a` and `b` differ; the measure driving the
  T-transform decomposition.

## Main statements

* `Majorizes.refl`, `Majorizes.trans`, the `Trans` instance: `≺` is a preorder.
* `majorizes_iff_descPrefixSum`: `a ≺ b` iff, after transporting to `Fin (card ι)`, the two tuples
  have equal total sum and every descending prefix sum of `a` is bounded by that of `b`.
* `majorizes_iff_reflTransGen_relatedByTTransform`: `a ≺ b` iff the decreasing rearrangement of `a`
  is reachable from that of `b` by a finite chain of T-transforms.
* `majorizes_exists_tStepList`: `a ≺ b` yields an explicit valid `List (TStep …)` taking the
  sorted `b` to the sorted `a`, keeping each step's `k, l, t` as data.

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
variable {M : Type*} [AddCommMonoid M] [LinearOrder M] [IsOrderedAddMonoid M]
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Sorting into decreasing order and partial sums -/

/-- A permutation that sorts `f` into decreasing (antitone) order. -/
def sortDesc : Equiv.Perm (Fin n) :=
  Tuple.sort (toDual ∘ f)

lemma antitone_comp_sortDesc : Antitone (f ∘ sortDesc f) := by
  have hmono : Monotone ((toDual ∘ f) ∘ Tuple.sort (toDual ∘ f)) := Tuple.monotone_sort _
  rw [Function.comp_assoc] at hmono
  exact monotone_toDual_comp_iff.mp hmono

/-- The prefix sum `∑_{x < i} (a ∘ σ) x` of `a` reindexed by the permutation `σ`. -/
noncomputable def partialSum (i : Fin n) (a : Fin n → M) (σ : Equiv.Perm (Fin n)) : M :=
  ∑ x < i, (a ∘ σ) x

/-- The `i`-th descending prefix sum of `a`: the sum of its `i` largest coordinates, obtained as the
prefix sum of `a` after sorting into decreasing order. -/
noncomputable def descPrefixSum (i : Fin n) (a : Fin n → M) : M := partialSum i a (sortDesc a)

/-- The maximal sum over `i`-element subsets of the coordinates of `a` (equivalently, the sum of its
`i` largest coordinates). -/
noncomputable def maxSubsetSum
  {ι} [Fintype ι] (i : Fin (Fintype.card ι)) (a : ι → M) : M :=
  (Finset.univ.powersetCard i).sup'
    (Finset.powersetCard_nonempty.mpr (by rw [Finset.card_univ]; exact i.isLt.le))
    (fun s => ∑ idx ∈ s, a idx)

/-! ### The majorization relation `≺` -/

/-- `a1` is majorized by `a2` (notation `a1 ≺ a2`): the two tuples have equal total sum, and
every prefix sum of the decreasing rearrangement of `a1` is at most the corresponding prefix sum
of `a2`. -/
private structure MajorizesFin (a1 a2 : Fin n → M) : Prop where
  /-- The two tuples have equal total sum. -/
  sum : ∑ x : Fin n, a1 x = ∑ x : Fin n, a2 x
  /-- Every prefix sum of the decreasing rearrangement of `a1` is at most that of `a2`. -/
  sums : ∀ i : Fin n, descPrefixSum i a1 ≤ descPrefixSum i a2

/-- `a1` is majorized by `a2` (notation `a1 ≺ a2`): the two tuples have equal total sum, and for
every `i` the maximal sum over `i`-element subsets of `a1` is at most that of `a2`.

The order is on the values, not the index, so `≺` is permutation-invariant; it is *not* stochastic
dominance (pointwise comparison of cumulative sums along an ordered index). -/
structure Majorizes {ι} [Fintype ι] (a1 a2 : ι → M) : Prop where
  /-- The two tuples have equal total sum. -/
  sum : ∑ x : ι, a1 x = ∑ x : ι, a2 x
  /-- For every `i`, the maximal sum over `i`-element subsets of `a1` is at most that of `a2`. -/
  sums : ∀ i : Fin (Fintype.card ι), maxSubsetSum i a1 ≤ maxSubsetSum i a2

@[inherit_doc] scoped infix:50 " ≺ " => Majorizes

omit [IsOrderedAddMonoid M] in
private lemma partialSum_congr_of_antitone
    {a : Fin n → M} {p1 p2 : Equiv.Perm (Fin n)}
    (h1 : Antitone (a ∘ p1)) (h2 : Antitone (a ∘ p2)) (i : Fin n) :
    partialSum i a p1 = partialSum i a p2 := by
  unfold partialSum
  rw [Tuple.unique_antitone h1 h2]

omit [LinearOrder M] [IsOrderedAddMonoid M] in
private lemma sum_comp_perm {a : Fin n → M} {σ : Equiv.Perm (Fin n)} :
    ∑ x, (a ∘ σ) x = ∑ x, a x := Equiv.sum_comp σ a

private lemma comp_perm_comp_sortDesc {σ : Equiv.Perm (Fin n)} :
    (f ∘ σ) ∘ (sortDesc (f ∘ ⇑σ)) = f ∘ (sortDesc f) := by
  have hcomp : f ∘ (σ * sortDesc (f ∘ σ)) = f ∘ (sortDesc f) :=
    Tuple.unique_antitone
      (by rw [Equiv.Perm.coe_mul, ← Function.comp_assoc]; exact antitone_comp_sortDesc (f ∘ ⇑σ))
      (antitone_comp_sortDesc f)
  rwa [Equiv.Perm.coe_mul, ← Function.comp_assoc] at hcomp

omit [IsOrderedAddMonoid M] in
private lemma partialSum_comp_perm {a : Fin n → M} {σ : Equiv.Perm (Fin n)} {i : Fin n} :
    partialSum i (a ∘ σ) (sortDesc (a ∘ σ)) = partialSum i a (sortDesc a) := by
  unfold partialSum
  rw [comp_perm_comp_sortDesc]

omit [IsOrderedAddMonoid M] in
private lemma comp_perm_majorizesFin_iff {a b : Fin n → M} {σ : Equiv.Perm (Fin n)} :
    MajorizesFin (a ∘ σ) b ↔ MajorizesFin a b := by
  constructor <;> rintro ⟨hsum, hsums⟩ <;>
    exact ⟨by simpa only [sum_comp_perm] using hsum,
           fun i ↦ by simpa only [descPrefixSum, partialSum_comp_perm] using hsums i⟩

omit [IsOrderedAddMonoid M] in
private lemma majorizesFin_comp_perm_iff {a b : Fin n → M} {σ : Equiv.Perm (Fin n)} :
    MajorizesFin a (b ∘ σ) ↔ MajorizesFin a b := by
  constructor <;> rintro ⟨hsum, hsums⟩ <;>
    exact ⟨by simpa only [sum_comp_perm] using hsum,
           fun i ↦ by simpa only [descPrefixSum, partialSum_comp_perm] using hsums i⟩

omit [IsOrderedAddMonoid M] in
private lemma MajorizesFin.refl (a : Fin n → M) : MajorizesFin a a :=
  ⟨rfl, fun _ ↦ le_rfl⟩

omit [IsOrderedAddMonoid M] in
private lemma MajorizesFin.trans {a b c : Fin n → M}
    (h1 : MajorizesFin a b) (h2 : MajorizesFin b c) : MajorizesFin a c :=
  ⟨h1.sum.trans h2.sum, fun i ↦ (h1.sums i).trans (h2.sums i)⟩

private instance :
    Trans (MajorizesFin (n := n) (M := M)) (MajorizesFin (n := n) (M := M))
      (MajorizesFin (n := n) (M := M)) where
  trans := MajorizesFin.trans

/-! ### T-transforms and discrepancy -/

/-- The data of a single T-transform: the two coordinates and the transfer parameter. This
`Type`-level record is what we track in an explicit sequence, as opposed to the proof-irrelevant
`RelatedByTTransform`. -/
structure TStep (ι K : Type*) where
  /-- The coordinate whose value decreases. -/
  k : ι
  /-- The coordinate whose value increases. -/
  l : ι
  /-- The transfer parameter (in `(0, 1)` when the step is valid). -/
  t : K

/-- The vector obtained from `a` by the single T-transform `s`: pull `s.k`, `s.l` toward each other
by an `s.t`-fraction of their gap, fixing the other coordinates. The argument order `(a, s)` matches
`List.foldl`. -/
def tTransform {ι : Type*} [DecidableEq ι] (a : ι → K) (s : TStep ι K) : ι → K :=
  fun i => if i = s.k then a s.k + (a s.l - a s.k) * s.t
           else if i = s.l then a s.l - (a s.l - a s.k) * s.t
           else a i

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] lemma tTransform_apply_k {ι : Type*} [DecidableEq ι] (a : ι → K) (s : TStep ι K) :
    tTransform a s s.k = a s.k + (a s.l - a s.k) * s.t := by
  simp only [tTransform, ↓reduceIte]

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma tTransform_apply_l {ι : Type*} [DecidableEq ι] (a : ι → K) {s : TStep ι K}
    (hkl : s.k ≠ s.l) : tTransform a s s.l = a s.l - (a s.l - a s.k) * s.t := by
  simp only [tTransform]
  rw [ite_eq_right (Ne.symm hkl)]
  simp only [↓reduceIte]

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma tTransform_apply_of_ne {ι : Type*} [DecidableEq ι] (a : ι → K) {s : TStep ι K} {i : ι}
    (hik : i ≠ s.k) (hil : i ≠ s.l) : tTransform a s i = a i := by
  simp only [tTransform]
  rw [ite_eq_right hik, ite_eq_right hil]

/-- The step `s` is valid at `a`: the parameter lies in `(0, 1)` and `a s.l < a s.k`. -/
def TStep.Valid {ι : Type*} (s : TStep ι K) (a : ι → K) : Prop :=
  0 < s.t ∧ s.t < 1 ∧ a s.l < a s.k

/-- `b` is obtained from `a` by a single T-transform (Robin Hood transfer): some valid step `s`
carries `a` to `b`, i.e. `b = tTransform a s`. -/
def RelatedByTTransform {ι : Type*} [DecidableEq ι] (b a : ι → K) : Prop :=
  ∃ s : TStep ι K, s.Valid a ∧ b = tTransform a s

/-- Apply a list of steps to `a`, left to right. -/
def applyChain {ι : Type*} [DecidableEq ι] (a : ι → K) (steps : List (TStep ι K)) : ι → K :=
  steps.foldl tTransform a

/-- Every step of the list is valid at the vector reached just before it. -/
def ValidChain {ι : Type*} [DecidableEq ι] (a : ι → K) : List (TStep ι K) → Prop
  | []        => True
  | s :: rest => s.Valid a ∧ ValidChain (tTransform a s) rest

/-- The number of coordinates at which `a` and `b` differ. -/
def discrepancy {ι : Type*} [Fintype ι] (a b : ι → K) : Nat := #{i | a i ≠ b i}

omit [IsStrictOrderedRing K] in
private lemma exists_sub_ne_zero_of_discrepancy_ne_zero {a b : Fin n → K} :
  discrepancy a b ≠ 0 → ∃ k : Fin n, a k - b k ≠ 0 := by
  intro hd
  unfold discrepancy at hd
  obtain ⟨k, hk⟩ := Finset.card_ne_zero.mp hd
  exact ⟨k, sub_ne_zero.mpr (Finset.mem_filter.mp hk).2⟩

omit [Field K] [IsStrictOrderedRing K] in
private lemma discrepancy_zero_iff_eq {a b : Fin n → K} : a = b ↔ discrepancy a b = 0 :=
  ⟨ fun hab ↦ by unfold discrepancy; simp [hab]
  , fun disc_zero ↦ by
      unfold discrepancy at disc_zero
      have hall_eq := Finset.card_filter_eq_zero_iff.mp disc_zero
      simp only [mem_univ, ne_eq, Decidable.not_not, forall_const] at hall_eq
      rw [funext_iff.mpr hall_eq]
  ⟩

/-! ### A single T-transform implies majorization -/

@[to_additive]
private lemma prod_split_two {ι M} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    {k l : ι} (lnk : l ≠ k) (g : ι → M) :
    ∏ i, g i = (∏ i with i ≠ k ∧ i ≠ l, g i) * g l * g k := by
  rw [← Finset.prod_erase_mul Finset.univ g (Fintype.complete k),
      ← Finset.prod_erase_mul (Finset.univ.erase k) g
          (Finset.mem_erase.mpr ⟨lnk, Fintype.complete _⟩),
      show (Finset.univ.erase k).erase l = Finset.univ.filter (fun x ↦ x ≠ k ∧ x ≠ l) from by
        ext x; simp [Finset.mem_erase, and_comm]]

private lemma sum_le_sum_Iio_of_antitone {a : Fin n → M} {i : Fin n} {p : Finset (Fin n)}
    (antitone : Antitone a) (peqi : #p = i) : (∑ x ∈ p, a x) ≤ (∑ x < i, a x) := by
  let ai := a i
  rw [← Finset.sum_inter_add_sum_sdiff p (Iio i) (a ·),
      ← Finset.sum_inter_add_sum_sdiff (Iio i) p (a ·),
      Finset.inter_comm (Iio i) p]
  apply add_le_add_right
  have hextra_le : ∑ x ∈ p \ Iio i, a x ≤ #(p \ Iio i) • ai := by
    apply Finset.sum_le_card_nsmul
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_Iio, not_lt] at hx
    exact antitone hx.2
  have hmissing_ge : #(Iio i \ p) • ai ≤ ∑ x ∈ Iio i \ p, a x := by
    apply Finset.card_nsmul_le_sum
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_Iio] at hx
    exact antitone (le_of_lt hx.1)
  have hsame_count : #(Iio i \ p) = #(p \ Iio i) := by
    rw [Finset.card_sdiff, Finset.card_sdiff, peqi, Fin.card_Iio i, inter_comm]
  rw [hsame_count] at hmissing_ge
  exact hextra_le.trans hmissing_ge

private lemma subset_sum_le_sum_greatest {n} {a : Fin n → M} {i : Fin n} {t : Finset (Fin n)}
    (hs : #t = (i : Nat)) : (∑ x ∈ t, a x) ≤ (∑ x < i, (a ∘ sortDesc a) x) := by
    let preimg := image (sortDesc a).symm t
    have hcard : #preimg = #t := Finset.card_image_of_injective t (sortDesc a).symm.injective
    let sortA := sortDesc a
    have hinj : Set.InjOn sortA preimg := Set.injOn_of_injective sortA.injective
    have ht_image : t = image sortA preimg := by
      rw [Finset.image_image, Equiv.self_comp_symm, Finset.image_id]
    rw [ht_image, Finset.sum_image hinj]
    exact sum_le_sum_Iio_of_antitone (antitone_comp_sortDesc a) (hcard.trans hs)

omit [IsOrderedAddMonoid M] in
private lemma sum_image_sortDesc_Iio {n} {a : Fin n → M} {i : Fin n} {t : Finset (Fin n)}
    (ht : t = (Finset.Iio i).image (sortDesc a)) :
    (∑ x ∈ t, a x) = ∑ x < i, (a ∘ sortDesc a) x := by
  rw [ht]
  simp only [coe_Iio, EmbeddingLike.apply_eq_iff_eq, implies_true, Set.injOn_of_eq_iff_eq,
    sum_image, Function.comp_apply]

/-- The maximal sum over `i`-element subsets is attained by the `i` greatest coordinates: it equals
the sum over the image of `Iio i` under the decreasing sort. -/
private lemma sup'_powersetCard_eq_sum_image_sortDesc {n} (a : Fin n → M) (i : Fin n) :
    (Finset.univ.powersetCard i).sup'
        (Finset.powersetCard_nonempty.mpr
          (by rw [Finset.card_univ, Fintype.card_fin]; exact i.isLt.le))
        (fun s => ∑ idx ∈ s, a idx)
      = ∑ x ∈ (Finset.Iio i).image (sortDesc a), a x := by
  set t₀ := (Finset.Iio i).image (sortDesc a) with ht₀
  have hcard : #t₀ = (i : ℕ) := by
    rw [ht₀, Finset.card_image_of_injective _ (sortDesc a).injective, Fin.card_Iio]
  apply le_antisymm
  · apply Finset.sup'_le
    intro u hu
    have hu_card : #u = (i : ℕ) := (Finset.mem_powersetCard.mp hu).2
    calc ∑ x ∈ u, a x
        ≤ ∑ x < i, (a ∘ sortDesc a) x := subset_sum_le_sum_greatest hu_card
      _ = ∑ x ∈ t₀, a x := (sum_image_sortDesc_Iio ht₀).symm
  · exact Finset.le_sup' (fun s => ∑ idx ∈ s, a idx)
      (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩)

omit [IsOrderedAddMonoid M] in
private lemma sup'_powersetCard_comp {ι κ} [Fintype ι] [Fintype κ]
    (f : ι → M) (e : ι ≃ κ) (k : ℕ)
    (hι : (Finset.univ.powersetCard k : Finset (Finset ι)).Nonempty)
    (hκ : (Finset.univ.powersetCard k : Finset (Finset κ)).Nonempty) :
    (Finset.univ.powersetCard k).sup' hι (fun s => ∑ x ∈ s, f x)
      = (Finset.univ.powersetCard k).sup' hκ (fun s => ∑ x ∈ s, f (e.symm x)) := by
  have hfin : (Finset.univ.powersetCard k : Finset (Finset κ))
      = (Finset.univ.powersetCard k : Finset (Finset ι)).map
          (Finset.mapEmbedding e.toEmbedding).toEmbedding := by
    rw [← Finset.map_univ_equiv e, Finset.powersetCard_map]
  rw [Finset.sup'_congr hκ hfin fun _ _ => rfl, Finset.sup'_map]
  refine Finset.sup'_congr hι rfl fun s _ => ?_
  simp [Finset.mapEmbedding_apply, Finset.sum_map]

omit [IsOrderedAddMonoid M] in
private lemma maxSubsetSum_comp_symm {ι} [Fintype ι] (e : ι ≃ Fin (Fintype.card ι))
    (a : ι → M) (i : Fin (Fintype.card ι)) :
    maxSubsetSum i a = (Finset.univ.powersetCard i).sup'
        (Finset.powersetCard_nonempty.mpr
          (by rw [Finset.card_univ, Fintype.card_fin]; exact i.isLt.le))
        (fun s => ∑ idx ∈ s, (a ∘ e.symm) idx) := by
  unfold maxSubsetSum
  exact sup'_powersetCard_comp a e _ _ _

private lemma maxSubsetSum_eq_descPrefixSum_comp_symm {ι} [Fintype ι]
    (i : Fin (Fintype.card ι)) (a : ι → M) (equiv : ι ≃ Fin (Fintype.card ι)) :
    maxSubsetSum i a = descPrefixSum i (a ∘ equiv.symm) := by
  rw [maxSubsetSum_comp_symm equiv a i, sup'_powersetCard_eq_sum_image_sortDesc]
  exact sum_image_sortDesc_Iio rfl

/-- Bridge to the sorted world:
`Majorizes a b` holds iff the two vectors, transported to `Fin (card ι)` along `e`,
satisfy the `Fin`-level majorization relation `MajorizesFin`.
This reduces every `Majorizes` question to the `Fin n` T-transform theory. -/
private lemma majorizes_iff_majorizesFin_comp_symm {ι} [Fintype ι] (e : ι ≃ Fin (Fintype.card ι))
    (a b : ι → M) : Majorizes a b ↔ MajorizesFin (a ∘ e.symm) (b ∘ e.symm) := by
  constructor
  · rintro ⟨hsum, hsums⟩
    refine ⟨by simpa only [Function.comp_apply, Equiv.sum_comp] using hsum, fun i => ?_⟩
    rw [← maxSubsetSum_eq_descPrefixSum_comp_symm i a e,
        ← maxSubsetSum_eq_descPrefixSum_comp_symm i b e]
    exact hsums i
  · rintro ⟨hsum, hsums⟩
    refine ⟨by simpa only [Function.comp_apply, Equiv.sum_comp] using hsum, fun i => ?_⟩
    rw [maxSubsetSum_eq_descPrefixSum_comp_symm i a e,
        maxSubsetSum_eq_descPrefixSum_comp_symm i b e]
    exact hsums i

lemma majorizes_iff_descPrefixSum {ι} [Fintype ι] (e : ι ≃ Fin (Fintype.card ι)) (a b : ι → M) :
    Majorizes a b ↔ (∑ x, a x = ∑ x, b x) ∧
      ∀ i, descPrefixSum i (a ∘ e.symm) ≤ descPrefixSum i (b ∘ e.symm) :=
  (majorizes_iff_majorizesFin_comp_symm e a b).trans
    ⟨fun h => ⟨by simpa only [Function.comp_apply, Equiv.sum_comp] using h.sum, h.sums⟩,
     fun h => ⟨by simpa only [Function.comp_apply, Equiv.sum_comp] using h.1, h.2⟩⟩

omit [IsOrderedAddMonoid M] in
lemma Majorizes.refl {ι} [Fintype ι] (a : ι → M) : Majorizes a a :=
  ⟨rfl, fun _ => le_rfl⟩

omit [IsOrderedAddMonoid M] in
lemma Majorizes.trans {ι} [Fintype ι] {a b c : ι → M}
    (h1 : Majorizes a b) (h2 : Majorizes b c) : Majorizes a c :=
  ⟨h1.sum.trans h2.sum, fun i => (h1.sums i).trans (h2.sums i)⟩

instance {ι} [Fintype ι] :
    Trans (Majorizes (ι := ι) (M := M)) (Majorizes (ι := ι) (M := M))
      (Majorizes (ι := ι) (M := M)) where
  trans := Majorizes.trans

omit [IsOrderedAddMonoid M] in
lemma maxSubsetSum_comp_equiv {ι} [Fintype ι] (σ : ι ≃ ι) (a : ι → M)
    (i : Fin (Fintype.card ι)) : maxSubsetSum i (a ∘ σ) = maxSubsetSum i a := by
  unfold maxSubsetSum
  exact (sup'_powersetCard_comp a σ.symm _ _ _).symm

omit [IsOrderedAddMonoid M] in
lemma comp_perm_majorizes_iff {ι} [Fintype ι] {a b : ι → M} {σ : Equiv.Perm ι} :
    Majorizes (a ∘ σ) b ↔ Majorizes a b := by
  constructor <;> rintro ⟨hsum, hsums⟩ <;>
    exact ⟨by simpa [Equiv.sum_comp] using hsum,
           fun i => by simpa [maxSubsetSum_comp_equiv] using hsums i⟩

omit [IsOrderedAddMonoid M] in
lemma majorizes_comp_perm_iff {ι} [Fintype ι] {a b : ι → M} {σ : Equiv.Perm ι} :
    Majorizes a (b ∘ σ) ↔ Majorizes a b := by
  constructor <;> rintro ⟨hsum, hsums⟩ <;>
    exact ⟨by simpa [Equiv.sum_comp] using hsum,
           fun i => by simpa [maxSubsetSum_comp_equiv] using hsums i⟩

private lemma exists_subset_sum_le_of_relatedByTTransform {n} {a b : Fin n → K}
    {s : Finset (Fin n)} (t : RelatedByTTransform a b) :
    ∃ t : Finset (Fin n), #t = #s ∧ ∑ x ∈ s, a x ≤ ∑ x ∈ t, b x := by
  obtain ⟨s', hvalid, heq⟩ := t
  obtain ⟨k, l, lambda⟩ := s'
  obtain ⟨ht0, ht1, ak_gt_al⟩ := hvalid
  have hkl : k ≠ l := by rintro rfl; exact absurd ak_gt_al (lt_irrefl _)
  have lambda_0_1 : 0 < lambda ∧ lambda < 1 := ⟨ht0, ht1⟩
  have bk : a k = b k + (b l - b k) * lambda := by rw [heq, tTransform_apply_k]
  have bl : a l = b l - (b l - b k) * lambda := by rw [heq, tTransform_apply_l b hkl]
  have other_unchanged : ∀ i, i ≠ k ∧ i ≠ l → b i = a i := fun i hi => by
    rw [heq, tTransform_apply_of_ne b hi.1 hi.2]
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

omit [IsStrictOrderedRing K] in
private lemma exists_subset_sum_eq_sortDesc_prefix {i : Fin n} {a : Fin n → K} :
    ∃ t : Finset (Fin n), #t = i ∧ (∑ x < i, (a ∘ sortDesc a) x) = ∑ x ∈ t, a x :=
  ⟨image (sortDesc a) (Iio i),
    (card_image_of_injective (Iio i) (sortDesc a).injective).trans (Fin.card_Iio i),
    (sum_image (sortDesc a).injective.injOn).symm⟩

private lemma partialSum_domination {n} i {a b : Fin n → K}
  (t : RelatedByTTransform a b) : partialSum i a (sortDesc a) ≤ partialSum i b (sortDesc b) := by
  unfold partialSum
  obtain ⟨t1, teqi, to_rewrite⟩ := exists_subset_sum_eq_sortDesc_prefix (a := a) (i := i)
  obtain ⟨t2, teqs, to_rewrite2⟩ := exists_subset_sum_le_of_relatedByTTransform t (s := t1)
  rw [to_rewrite]
  exact calc (∑ x ∈ t1, a x)
        _ ≤ ∑ x ∈ t2, b x := to_rewrite2
        _ ≤ ∑ x < i, (b ∘ (sortDesc b)) x := subset_sum_le_sum_greatest (a := b) (teqs.trans teqi)

private lemma majorizesFin_of_relatedByTTransform {a b : Fin n → K} :
  RelatedByTTransform a b → MajorizesFin a b := by
  rintro ⟨s, hvalid, heq⟩
  obtain ⟨ht0, ht1, ak_gt_al⟩ := hvalid
  have hkl : s.k ≠ s.l := by rintro h; rw [h] at ak_gt_al; exact absurd ak_gt_al (lt_irrefl _)
  have l_ne_k : s.l ≠ s.k := hkl.symm
  have bk : a s.k = b s.k + (b s.l - b s.k) * s.t := by rw [heq, tTransform_apply_k]
  have bl : a s.l = b s.l - (b s.l - b s.k) * s.t := by rw [heq, tTransform_apply_l b hkl]
  have other_unchanged : ∀ i, i ≠ s.k ∧ i ≠ s.l → b i = a i := fun i hi => by
    rw [heq, tTransform_apply_of_ne b hi.1 hi.2]
  refine ⟨?_, fun i ↦ partialSum_domination i ⟨s, ⟨ht0, ht1, ak_gt_al⟩, heq⟩⟩
  have hrest : (∑ i with i ≠ s.k ∧ i ≠ s.l, a i) = ∑ i with i ≠ s.k ∧ i ≠ s.l, b i :=
    Finset.sum_congr rfl fun x hx ↦ (other_unchanged x (Finset.mem_filter.mp hx).2).symm
  rw [sum_split_two l_ne_k a, sum_split_two l_ne_k b, hrest, bk, bl]
  ring

private lemma majorizesFin_of_reflTransGen_relatedByTTransform {a b : Fin n → K}
  (r : Relation.ReflTransGen RelatedByTTransform a b) : MajorizesFin a b := by
  induction r
  case refl => exact MajorizesFin.refl a
  case tail _ _ _ related_by_ttransform majorizes =>
    exact majorizes.trans (majorizesFin_of_relatedByTTransform related_by_ttransform)



/-! ### Majorization implies a chain of T-transforms -/

omit [IsStrictOrderedRing K] in
/-- For an antitone tuple, `partialSum` (defined via `sortDesc`) is just the prefix sum. -/
private lemma partialSum_eq_of_antitone {g : Fin n → K} (hg : Antitone g) (j : Fin n) :
    partialSum j g (sortDesc g) = ∑ x < j, g x := by
  rw [partialSum_congr_of_antitone (antitone_comp_sortDesc g) (p2 := 1) (by simpa using hg) j,
      partialSum]
  simp

/-- The two coordinates chosen by one decomposition step, returned as **data** (not `∃`) together
with the properties that make them a valid T-transform site. Returning `k`, `l` in `Type` is what
lets the step sequence be built as an explicit list. -/
private structure TCandidate {n} (a b : Fin n → K) : Type _ where
  /-- The larger-index endpoint of the transfer. -/
  k : Fin n
  /-- The smaller-index (in value: overtaking) endpoint. -/
  l : Fin n
  /-- `k` precedes `l`. -/
  k_lt_l : k < l
  /-- At `k`, `a` is strictly below `b`. -/
  ak_lt_bk : a k < b k
  /-- At `l`, `a` is strictly above `b`. -/
  al_gt_bl : a l > b l
  /-- Between `k` and `l`, `a` and `b` agree. -/
  between : ∀ i : Fin n, k < i → i < l → a i = b i

/-- The decomposition step's coordinate choice, as data: `k` is the greatest index below `l` where
`a < b`, `l` the least index where `a > b`. All the existence reasoning stays in the `Prop`-valued
subproofs (nonemptiness), so `k`, `l` come out in `Type`. -/
private def tTransform_candidates {n} {a b : Fin n → K} (ha : Antitone a) (hb : Antitone b)
    (majorizes : MajorizesFin a b) (h : discrepancy a b ≠ 0) : TCandidate a b := by
  -- The equal totals give `∑ (a - b) = 0`; with `a ≠ b` there is an index where `a` overtakes `b`.
  have a_b_diff_sum_eq_zero : ∑ i, (a i - b i) = 0 := by
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact majorizes.sum
  -- Majorization prefix sums, rewritten via antitonicity into honest prefix sums.
  have hpref : ∀ j : Fin n, ∑ x < j, a x ≤ ∑ x < j, b x := fun j ↦ by
    have hsums_j := majorizes.sums j
    unfold descPrefixSum at hsums_j
    rwa [partialSum_eq_of_antitone ha, partialSum_eq_of_antitone hb] at hsums_j
  -- Nonemptiness of the "overtake" set (this is where the classical existence lives, in `Prop`).
  have hne_l : ({i | a i > b i} : Finset (Fin n)).Nonempty := by
    obtain ⟨some_l, pl⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero _ a_b_diff_sum_eq_zero
      (by simp only [mem_univ, ne_eq, true_and]; exact exists_sub_ne_zero_of_discrepancy_ne_zero h)
    simp only [mem_univ, sub_pos, true_and] at pl
    exact ⟨some_l, Finset.mem_filter.mpr ⟨mem_univ _, pl⟩⟩
  -- `l` : the smallest index where `a` overtakes `b` (DATA, via `set`).
  set l := ({i | a i > b i} : Finset (Fin n)).min' hne_l with hl_def
  have hl_mem : a l > b l := (Finset.mem_filter.mp (Finset.min'_mem _ hne_l)).2
  have hl_min : ∀ i, i < l → a i ≤ b i := fun i hil ↦ by
    by_contra hgt
    exact absurd (Finset.min'_le ({i | a i > b i} : Finset (Fin n)) i
      (Finset.mem_filter.mpr ⟨mem_univ _, not_le.mp hgt⟩)) (not_le.mpr hil)
  -- Nonemptiness of the `k`-set: otherwise `a = b` below `l`, contradicting the `l`-prefix sum.
  have hne_k : ({i | i < l ∧ a i < b i} : Finset (Fin n)).Nonempty := by
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
  -- `k` : the largest index below `l` with `a < b` (DATA, via `set`).
  set k := ({i | i < l ∧ a i < b i} : Finset (Fin n)).max' hne_k with hk_def
  refine ⟨k, l, ?_, ?_, hl_mem, fun i hik hil ↦ ?_⟩
  · exact ((Finset.mem_filter.mp (Finset.max'_mem _ hne_k)).2).1
  · exact ((Finset.mem_filter.mp (Finset.max'_mem _ hne_k)).2).2
  · refine le_antisymm (hl_min i hil) (not_lt.mp fun hlt ↦ ?_)
    exact absurd (Finset.le_max' ({i | i < l ∧ a i < b i} : Finset (Fin n)) i
      (Finset.mem_filter.mpr ⟨mem_univ _, hil, hlt⟩)) (not_le.mpr hik)

/-- The data produced by one decomposition step: the `TStep` `s`, plus proofs that it is valid at
`b`, keeps `a`-majorization, stays antitone, and strictly decreases `discrepancy`. -/
private structure TStepResult {n} (a b : Fin n → K) : Type _ where
  /-- The step. -/
  s : TStep (Fin n) K
  /-- The step is valid at `b`. -/
  valid : s.Valid b
  /-- The transformed vector is still majorized by `a`. -/
  maj : MajorizesFin a (tTransform b s)
  /-- The transformed vector is antitone. -/
  anti : Antitone (tTransform b s)
  /-- The transformed vector is strictly closer to `a`. -/
  discr : discrepancy a (tTransform b s) < discrepancy a b

/-- One step of the T-transform decomposition, returned as data: from `a ≺ b` (both antitone) with
`a ≠ b`, produce the `TStep` carrying `b` one step toward `a` (still `a`-majorized, antitone, and
strictly closer in `discrepancy`). Non-recursive core; the recursion lives in `tStepList`. -/
private def tTransform_step {a b : Fin n → K} (ha : Antitone a) (hb : Antitone b)
    (majorizes : MajorizesFin a b) (h : discrepancy a b ≠ 0) : TStepResult a b := by
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
    let c : Fin n → K := fun i ↦
      if i = k then rho + sigma else if i = l then rho - sigma else b i
    -- Values of `c` at `k`, `l`, and off `{k, l}`, plus the boundary estimates (shared by
    -- `hc : Antitone c` and `a ≺ c`).
    have hck : c k = rho + sigma := by simp only [c, ↓reduceIte]
    have hcl : c l = rho - sigma := by simp only [c, ite_eq_right knel.symm, ↓reduceIte]
    have hci : ∀ m, m ≠ k → m ≠ l → c m = b m := by
      intro m hmk hml; simp only [c, ite_eq_right hmk, ite_eq_right hml]
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
    -- The step data: `k`, `l`, and the transfer parameter `t = (rho + sigma - b k) / (b l - b k)`,
    -- chosen so that `c = tTransform b s` uniformly across both `sigma` branches (we never unfold
    -- `sigma`; it stays an atom).
    let s : TStep (Fin n) K := ⟨k, l, (rho + sigma - b k) / (b l - b k)⟩
    have hvalid : s.Valid b :=
      ⟨div_pos_of_neg_of_neg (by linarith [sigma_lt_tau, rho_add_tau]) (by linarith [bl_lt_bk]),
       div_lt_one_iff.mpr (Or.inr (Or.inr
         ⟨by linarith [bl_lt_bk], by linarith [sigma_nonneg, tau_pos, rho_sub_tau]⟩)),
       bl_lt_bk⟩
    have hcs : c = tTransform b s := by
      funext i
      by_cases hik : i = k
      · subst hik
        rw [tTransform_apply_k, hck, mul_div_cancel₀ _ bl_bk_ne]; ring
      · by_cases hil : i = l
        · subst hil
          rw [tTransform_apply_l b knel, hcl, mul_div_cancel₀ _ bl_bk_ne]
          linarith [rho_add_tau, rho_sub_tau]
        · rw [tTransform_apply_of_ne b hik hil]; exact hci i hik hil
    have c_b_related_by_ttransform : RelatedByTTransform c b := ⟨s, hvalid, hcs⟩
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
    have a_majorized_by_c : MajorizesFin a c := by
      have hcb : MajorizesFin c b := majorizesFin_of_relatedByTTransform c_b_related_by_ttransform
      refine ⟨majorizes.sum.trans hcb.sum.symm, fun i ↦ ?_⟩
      unfold descPrefixSum
      rw [partialSum_eq_of_antitone ha, partialSum_eq_of_antitone hc]
      have hab : ∀ j, ∑ x < j, a x ≤ ∑ x < j, b x := fun j ↦ by
        have := majorizes.sums j
        unfold descPrefixSum at this
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
    exact ⟨s, hvalid, hcs ▸ a_majorized_by_c, hcs ▸ hc, hcs ▸ discrepancy_decreasing⟩

/-- The explicit list of T-transform steps carrying `b` to `a`, **as data**, bundled with its
correctness: it is a valid chain, folding it over `b` yields `a`, and its length is at most
`discrepancy a b`. Well-founded recursion on `discrepancy a b`, one step from `tTransform_step`. -/
private def tStepList {a b : Fin n → K}
    (ha : Antitone a) (hb : Antitone b) (majorizes : MajorizesFin a b) :
    {steps : List (TStep (Fin n) K) //
      ValidChain b steps ∧ applyChain b steps = a ∧ steps.length ≤ discrepancy a b} := by
  if h : discrepancy a b = 0 then
    refine ⟨[], trivial, ?_, Nat.zero_le _⟩
    simp only [applyChain, List.foldl_nil]
    exact (discrepancy_zero_iff_eq.mpr h).symm
  else
    let r := tTransform_step ha hb majorizes h
    obtain ⟨steps, hvc, hac, hlen⟩ := tStepList ha r.anti r.maj
    have hd := r.discr
    refine ⟨r.s :: steps, ⟨r.valid, hvc⟩,
      by simpa only [applyChain, List.foldl_cons] using hac, ?_⟩
    simp only [List.length_cons]
    omega
  termination_by discrepancy a b
  decreasing_by exact r.discr

/-- `∃`-form of `tStepList`, forgetting the list back into a proposition. -/
private lemma exists_tStepList_of_majorizesFin {a b : Fin n → K}
    (ha : Antitone a) (hb : Antitone b) (majorizes : MajorizesFin a b) :
    ∃ steps : List (TStep (Fin n) K), ValidChain b steps ∧ applyChain b steps = a ∧
      steps.length ≤ discrepancy a b :=
  ⟨(tStepList ha hb majorizes).1, (tStepList ha hb majorizes).2⟩

omit [IsStrictOrderedRing K] in
/-- A valid list of T-transform steps carrying `b` to `a` gives the `ReflTransGen` chain. -/
private lemma reflTransGen_of_tStepList {ι : Type*} [DecidableEq ι] {a b : ι → K}
    {steps : List (TStep ι K)} (hv : ValidChain b steps) (he : applyChain b steps = a) :
    Relation.ReflTransGen RelatedByTTransform a b := by
  induction steps generalizing b with
  | nil => simp only [applyChain, List.foldl_nil] at he; subst he; exact .refl
  | cons s rest ih =>
      obtain ⟨hvs, hvrest⟩ := hv
      exact (ih hvrest (by simpa only [applyChain, List.foldl_cons] using he)).tail
        ⟨s, hvs, rfl⟩

/-- `a ≺ b` (both antitone) implies `a` is reachable from `b` by a finite chain of
T-transforms. Corollary of `exists_tStepList_of_majorizesFin` via `reflTransGen_of_tStepList`. -/
private lemma reflTransGen_relatedByTTransform_of_majorizesFin
  {a b : Fin n → K} (ha : Antitone a) (hb : Antitone b) (majorizes : MajorizesFin a b) :
  Relation.ReflTransGen RelatedByTTransform a b := by
  obtain ⟨steps, hv, he, _⟩ := exists_tStepList_of_majorizesFin ha hb majorizes
  exact reflTransGen_of_tStepList hv he

/-- Majorization characterised by T-transforms: `a ≺ b` iff the decreasing rearrangement of `a`
is reachable from that of `b` by a finite chain of T-transforms. -/
private lemma majorizesFin_iff_reflTransGen_relatedByTTransform {a b : Fin n → K} :
  MajorizesFin a b ↔ Relation.ReflTransGen RelatedByTTransform (a ∘ sortDesc a) (b ∘ sortDesc b) :=
    ⟨ by
        have hchain := reflTransGen_relatedByTTransform_of_majorizesFin
          (antitone_comp_sortDesc a) (antitone_comp_sortDesc b)
        rw [show (MajorizesFin (a ∘ sortDesc a) (b ∘ sortDesc b)) = (MajorizesFin a b) from
              propext (comp_perm_majorizesFin_iff.trans majorizesFin_comp_perm_iff)] at hchain
        exact hchain
    , fun h ↦ (comp_perm_majorizesFin_iff.trans majorizesFin_comp_perm_iff).mp
        (majorizesFin_of_reflTransGen_relatedByTTransform h)
    ⟩

/-- Majorization (`Fintype` version) characterised by T-transforms: `Majorizes a b` iff the
decreasing rearrangement of `a` (transported to `Fin (card ι)` along `e`) is reachable from that
of `b` by a finite chain of T-transforms. Derived from the `Fin n` theorem via the bridge. -/
lemma majorizes_iff_reflTransGen_relatedByTTransform {ι} [Fintype ι]
    (e : ι ≃ Fin (Fintype.card ι)) (a b : ι → K) :
    Majorizes a b ↔ Relation.ReflTransGen RelatedByTTransform
      ((a ∘ e.symm) ∘ sortDesc (a ∘ e.symm)) ((b ∘ e.symm) ∘ sortDesc (b ∘ e.symm)) :=
  (majorizes_iff_majorizesFin_comp_symm e a b).trans
    majorizesFin_iff_reflTransGen_relatedByTTransform

/-- Explicit T-transform sequence (`Fintype` version), **as data**: `a ≺ b` yields the concrete
`List (TStep …)` carrying the decreasing rearrangement of `b` to that of `a` (transported to
`Fin (card ι)` along `e`), bundled with the proof that it is a valid chain whose fold sends `b↓` to
`a↓`. This is the data-returning core — one function taking `a`, `b` and a majorization proof and
returning the step list together with its correctness. Unlike
`majorizes_iff_reflTransGen_relatedByTTransform`, it keeps the parameters `k, l, t` of every step as
data. -/
@[no_expose] def majorizesTStepList {ι} [Fintype ι] (e : ι ≃ Fin (Fintype.card ι))
    (a b : ι → K) (h : Majorizes a b) :
    {steps : List (TStep (Fin (Fintype.card ι)) K) //
      ValidChain ((b ∘ e.symm) ∘ sortDesc (b ∘ e.symm)) steps ∧
      applyChain ((b ∘ e.symm) ∘ sortDesc (b ∘ e.symm)) steps
        = (a ∘ e.symm) ∘ sortDesc (a ∘ e.symm)} :=
  let maj : MajorizesFin (a ∘ e.symm) (b ∘ e.symm) :=
    (majorizes_iff_majorizesFin_comp_symm e a b).mp h
  let maj' : MajorizesFin ((a ∘ e.symm) ∘ sortDesc (a ∘ e.symm))
      ((b ∘ e.symm) ∘ sortDesc (b ∘ e.symm)) :=
    (comp_perm_majorizesFin_iff.trans majorizesFin_comp_perm_iff).mpr maj
  let r := tStepList (antitone_comp_sortDesc _) (antitone_comp_sortDesc _) maj'
  ⟨r.1, r.2.1, r.2.2.1⟩

/-- `∃`-form of `majorizesTStepList`. -/
lemma majorizes_exists_tStepList {ι} [Fintype ι] (e : ι ≃ Fin (Fintype.card ι))
    (a b : ι → K) (h : Majorizes a b) :
    ∃ steps : List (TStep (Fin (Fintype.card ι)) K),
      ValidChain ((b ∘ e.symm) ∘ sortDesc (b ∘ e.symm)) steps ∧
      applyChain ((b ∘ e.symm) ∘ sortDesc (b ∘ e.symm)) steps
        = (a ∘ e.symm) ∘ sortDesc (a ∘ e.symm) :=
  ⟨(majorizesTStepList e a b h).1, (majorizesTStepList e a b h).2⟩

end Majorization
