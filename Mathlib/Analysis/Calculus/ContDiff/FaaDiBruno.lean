/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Data.Finite.Card
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Faa di Bruno formula

The Faa di Bruno formula gives the iterated derivative of `g ∘ f` in terms of those of
`g` and `f`. It is expressed in terms of partitions `I` of `{0, ..., n-1}`. For such a
partition, denote by `k` its number of parts, write the parts as `I₀, ..., Iₖ₋₁` ordered so
that `max I₀ < ... < max Iₖ₋₁`, and let `iₘ` be the number of elements of `Iₘ`. Then
`D^n (g ∘ f) (x) (v₀, ..., vₙ₋₁) =
  ∑_{I partition of {0, ..., n-1}}
    D^k g (f x) (D^{i₀} f (x) (v_{I₀}), ..., D^{iₖ₋₁} f (x) (v_{Iₖ₋₁}))`
where by `v_{Iₘ}` we mean the vectors `vᵢ` with indices in `Iₘ`, i.e., the composition of `v`
with the increasing embedding of `Fin iₘ` into `Fin n` with range `Iₘ`.

For instance, for `n = 2`, there are 2 partitions of `{0, 1}`, given by `{0}, {1}` and `{0, 1}`,
and therefore
`D^2(g ∘ f) (x) (v₀, v₁) = D^2 g (f x) (Df (x) v₀, Df (x) v₁) + Dg (f x) (D^2f (x) (v₀, v₁))`.

The formula is straightforward to prove by induction, as differentiating
`D^k g (f x) (D^{i₀} f (x) (v_{I₀}), ..., D^{iₖ₋₁} f (x) (v_{Iₖ₋₁}))` gives a sum
with `k + 1` terms where one differentiates either `D^k g (f x)`, or one of the `D^{iₘ} f (x)`,
amounting to adding to the partition `I` either a new atom `{-1}` to its left, or extending `Iₘ`
by adding `-1` to it. In this way, one obtains bijectively all partitions of `{-1, ..., n}`,
and the proof can go on (up to relabelling).

The main difficulty is to write things down in a precise language, namely to write
`D^k g (f x) (D^{i₀} f (x) (v_{I₀}), ..., D^{iₖ₋₁} f (x) (v_{Iₖ₋₁}))` as a continuous multilinear
map of the `vᵢ`. For this, instead of working with partitions of `{0, ..., n-1}` and ordering their
parts, we work with partitions in which the ordering is part of the data -- this is equivalent,
but much more convenient to implement. We call these `OrderedFinpartition n`.

Note that the implementation of `OrderedFinpartition` is very specific to the Faa di Bruno formula:
as testified by the formula above, what matters is really the embedding of the parts in `Fin n`,
and moreover the parts have to be ordered by `max I₀ < ... < max Iₖ₋₁` for the formula to hold
in the general case where the iterated differential might not be symmetric. The defeqs with respect
to `Fin.cons` are also important when doing the induction. For this reason, we do not expect this
class to be useful beyond the Faa di Bruno formula, which is why it is in this file instead
of a dedicated file in the `Combinatorics` folder.

## Main results

Given `c : OrderedFinpartition n` and two formal multilinear series `q` and `p`, we
define `c.compAlongOrderedFinpartition q p` as an `n`-multilinear map given by the formula above,
i.e., `(v₁, ..., vₙ) ↦ qₖ (p_{i₁} (v_{I₁}), ..., p_{iₖ} (v_{Iₖ}))`.

Then, we define `q.taylorComp p` as a formal multilinear series whose `n`-th term is
the sum of `c.compAlongOrderedFinpartition q p` over all ordered finpartitions of size `n`.

Finally, we prove in `HasFTaylorSeriesUptoOn.comp` that, if two functions `g` and `f` have Taylor
series up to `n` given by `q` and `p`, then `g ∘ f` also has a Taylor series,
given by `q.taylorComp p`.

## Implementation

A first technical difficulty is to implement the extension process of `OrderedFinpartition`
corresponding to adding a new atom, or appending an atom to an existing part, and defining the
associated increasing parameterizations that show up in the definition
of `compAlongOrderedFinpartition`.

Then, one has to show that the ordered finpartitions thus
obtained give exactly all ordered finpartitions of order `n+1`. For this, we define the inverse
process (shrinking a finpartition of `n+1` by erasing `0`, either as an atom or from the part
that contains it), and we show that these processes are inverse to each other, yielding an
equivalence between `(c : OrderedFinpartition n) × Option (Fin c.length)`
and `OrderedFinpartition (n + 1)`. This equivalence shows up prominently in the inductive proof
of Faa di Bruno formula to identify the sums that show up.
-/

noncomputable section

open Set Fin Filter Function

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {s : Set E} {t : Set F}
  {q : F → FormalMultilinearSeries 𝕜 F G} {p : E → FormalMultilinearSeries 𝕜 E F}

/-- A partition of `Fin n` into finitely many nonempty subsets, given by the increasing
parameterization of these subsets. We order the subsets by increasing greatest element.
This definition is tailored-made for the Faa di Bruno formula, and probably not useful elsewhere,
because of the specific parameterization by `Fin n` and the peculiar ordering. -/
@[ext]
structure OrderedFinpartition (n : ℕ) where
  /-- The number of parts in the partition -/
  length : ℕ
  /-- The size of each part -/
  partSize : Fin length → ℕ
  partSize_pos : ∀ m, 0 < partSize m
  /-- The increasing parameterization of each part -/
  emb : ∀ m, (Fin (partSize m)) → Fin n
  emb_strictMono : ∀ m, StrictMono (emb m)
  /-- The parts are ordered by increasing greatest element. -/
  parts_strictMono :
    StrictMono fun m ↦ emb m ⟨partSize m - 1, Nat.sub_one_lt_of_lt (partSize_pos m)⟩
  /-- The parts are disjoint -/
  disjoint : PairwiseDisjoint univ fun m ↦ range (emb m)
  /-- The parts cover everything -/
  cover x : ∃ m, x ∈ range (emb m)
  deriving DecidableEq

namespace OrderedFinpartition

/-! ### Basic API for ordered finpartitions -/

/-- The ordered finpartition of `Fin n` into singletons. -/
@[simps -fullyApplied]
def atomic (n : ℕ) : OrderedFinpartition n where
  length := n
  partSize _ :=  1
  partSize_pos _ := _root_.zero_lt_one
  emb m _ := m
  emb_strictMono _ := Subsingleton.strictMono _
  parts_strictMono := strictMono_id
  disjoint _ _ _ _ h := by simpa using h
  cover m := by simp

variable {n : ℕ} (c : OrderedFinpartition n)

instance : Inhabited (OrderedFinpartition n) := ⟨atomic n⟩

@[simp]
theorem default_eq : (default : OrderedFinpartition n) = atomic n := rfl

lemma length_le : c.length ≤ n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ c.parts_strictMono.injective

lemma partSize_le (m : Fin c.length) : c.partSize m ≤ n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (c.emb_strictMono m).injective

/-- Embedding of ordered finpartitions in a sigma type. The sigma type on the right is quite big,
but this is enough to get finiteness of ordered finpartitions. -/
def embSigma (n : ℕ) : OrderedFinpartition n →
    (Σ (l : Fin (n + 1)), Σ (p : Fin l → Fin (n + 1)), Π (i : Fin l), (Fin (p i) → Fin n)) :=
  fun c ↦ ⟨⟨c.length, Order.lt_add_one_iff.mpr c.length_le⟩,
    fun m ↦ ⟨c.partSize m, Order.lt_add_one_iff.mpr (c.partSize_le m)⟩, fun j ↦ c.emb j⟩

lemma injective_embSigma (n : ℕ) : Injective (embSigma n) := by
  rintro ⟨plength, psize, -, pemb, -, -, -, -⟩ ⟨qlength, qsize, -, qemb, -, -, -, -⟩
  intro hpq
  simp_all only [Sigma.mk.inj_iff, true_and, mk.injEq, Fin.mk.injEq, embSigma]
  have : plength = qlength := hpq.1
  subst this
  simp_all only [Sigma.mk.inj_iff, heq_eq_eq, true_and, and_true]
  ext i
  exact mk.inj_iff.mp (congr_fun hpq.1 i)

/- The best proof would probably to establish the bijection with Finpartitions, but we opt
for a direct argument, embedding `OrderedPartition n` in a type which is obviously finite. -/
noncomputable instance : Fintype (OrderedFinpartition n) :=
  Fintype.ofInjective _ (injective_embSigma n)

instance instUniqueZero : Unique (OrderedFinpartition 0) := by
  have : Subsingleton (OrderedFinpartition 0) :=
    Fintype.card_le_one_iff_subsingleton.mp (Fintype.card_le_of_injective _ (injective_embSigma 0))
  exact Unique.mk' (OrderedFinpartition 0)

lemma exists_inverse {n : ℕ} (c : OrderedFinpartition n) (j : Fin n) :
    ∃ p : Σ m, Fin (c.partSize m), c.emb p.1 p.2 = j := by
  rcases c.cover j with ⟨m, r, hmr⟩
  exact ⟨⟨m, r⟩, hmr⟩

lemma emb_injective : Injective (fun (p : Σ m, Fin (c.partSize m)) ↦ c.emb p.1 p.2) := by
  rintro ⟨m, r⟩ ⟨m', r'⟩ (h : c.emb m r = c.emb m' r')
  have : m = m' := by
    contrapose! h
    have A : Disjoint (range (c.emb m)) (range (c.emb m')) :=
      c.disjoint (mem_univ m) (mem_univ m') h
    apply disjoint_iff_forall_ne.1 A (mem_range_self r) (mem_range_self r')
  subst this
  simpa using (c.emb_strictMono m).injective h

lemma emb_ne_emb_of_ne {i j : Fin c.length} {a : Fin (c.partSize i)} {b : Fin (c.partSize j)}
    (h : i ≠ j) : c.emb i a ≠ c.emb j b :=
  c.emb_injective.ne (a₁ := ⟨i, a⟩) (a₂ := ⟨j, b⟩) (by simp [h])

/-- Given `j : Fin n`, the index of the part to which it belongs. -/
noncomputable def index (j : Fin n) : Fin c.length :=
  (c.exists_inverse j).choose.1

/-- The inverse of `c.emb` for `c : OrderedFinpartition`. It maps `j : Fin n` to the point in
`Fin (c.partSize (c.index j))` which is mapped back to `j` by `c.emb (c.index j)`. -/
noncomputable def invEmbedding (j : Fin n) :
    Fin (c.partSize (c.index j)) := (c.exists_inverse j).choose.2

@[simp] lemma emb_invEmbedding (j : Fin n) :
    c.emb (c.index j) (c.invEmbedding j) = j :=
  (c.exists_inverse j).choose_spec

/-- An ordered finpartition gives an equivalence between `Fin n` and the disjoint union of the
parts, each of them parameterized by `Fin (c.partSize i)`. -/
noncomputable def equivSigma : ((i : Fin c.length) × Fin (c.partSize i)) ≃ Fin n where
  toFun p := c.emb p.1 p.2
  invFun i := ⟨c.index i, c.invEmbedding i⟩
  right_inv _ := by simp
  left_inv _ := by apply c.emb_injective; simp

@[to_additive] lemma prod_sigma_eq_prod {α : Type*} [CommMonoid α] (v : Fin n → α) :
    ∏ (m : Fin c.length), ∏ (r : Fin (c.partSize m)), v (c.emb m r) = ∏ i, v i := by
  rw [Finset.prod_sigma']
  exact Fintype.prod_equiv c.equivSigma _ _ (fun p ↦ rfl)

lemma length_pos (h : 0 < n) : 0 < c.length := Nat.zero_lt_of_lt (c.index ⟨0, h⟩).2

lemma neZero_length [NeZero n] (c : OrderedFinpartition n) : NeZero c.length :=
  ⟨(c.length_pos pos').ne'⟩

lemma neZero_partSize (c : OrderedFinpartition n) (i : Fin c.length) : NeZero (c.partSize i) :=
  .of_pos (c.partSize_pos i)

attribute [local instance] neZero_length neZero_partSize

instance instUniqueOne : Unique (OrderedFinpartition 1) where
  uniq c := by
    have h₁ : c.length = 1 := le_antisymm c.length_le (c.length_pos Nat.zero_lt_one)
    have h₂ (i) : c.partSize i = 1 := le_antisymm (c.partSize_le _) (c.partSize_pos _)
    have h₃ (i j) : c.emb i j = 0 := Subsingleton.elim _ _
    rcases c with ⟨length, partSize, _, emb, _, _, _, _⟩
    subst h₁
    obtain rfl : partSize = fun _ ↦ 1 := funext h₂
    simpa [OrderedFinpartition.ext_iff, funext_iff, Fin.forall_fin_one] using h₃ _ _

lemma emb_zero [NeZero n] : c.emb (c.index 0) 0 = 0 := by
  apply le_antisymm _ (Fin.zero_le _)
  conv_rhs => rw [← c.emb_invEmbedding 0]
  apply (c.emb_strictMono _).monotone (Fin.zero_le _)

lemma partSize_eq_one_of_range_emb_eq_singleton
    (c : OrderedFinpartition n) {i : Fin c.length} {j : Fin n}
    (hc : range (c.emb i) = {j}) :
    c.partSize i = 1 := by
  have : Fintype.card (range (c.emb i)) = Fintype.card (Fin (c.partSize i)) :=
    card_range_of_injective (c.emb_strictMono i).injective
  simpa [hc] using this.symm

/-- If the left-most part is not `{0}`, then the part containing `0` has at least two elements:
either because it's the left-most part, and then it's not just `0` by assumption, or because it's
not the left-most part and then, by increasingness of maximal elements in parts, it contains
a positive element. -/
lemma one_lt_partSize_index_zero (c : OrderedFinpartition (n + 1)) (hc : range (c.emb 0) ≠ {0}) :
    1 < c.partSize (c.index 0) := by
  have : c.partSize (c.index 0) = Nat.card (range (c.emb (c.index 0))) := by
    rw [Nat.card_range_of_injective (c.emb_strictMono _).injective]; simp
  rw [this]
  rcases eq_or_ne (c.index 0) 0 with h | h
  · rw [← h] at hc
    have : {0} ⊂ range (c.emb (c.index 0)) := by
      apply ssubset_of_subset_of_ne ?_ hc.symm
      simpa only [singleton_subset_iff, mem_range] using ⟨0, emb_zero c⟩
    simpa using Set.Finite.card_lt_card (finite_range _) this
  · apply one_lt_two.trans_le
    have : {c.emb (c.index 0) 0,
        c.emb (c.index 0) ⟨c.partSize (c.index 0) - 1, Nat.sub_one_lt_of_lt (c.partSize_pos _)⟩}
          ⊆ range (c.emb (c.index 0)) := by simp [insert_subset]
    simp only [emb_zero] at this
    convert Nat.card_mono Subtype.finite this
    simp only [Nat.card_eq_fintype_card, Fintype.card_ofFinset, toFinset_singleton]
    apply (Finset.card_pair ?_).symm
    exact ((Fin.zero_le _).trans_lt (c.parts_strictMono ((pos_iff_ne_zero' (c.index 0)).mpr h))).ne

/-!
### Extending and shrinking ordered finpartitions

We show how an ordered finpartition can be extended to the left, either by adding a new atomic
part (in `extendLeft`) or adding the new element to an existing part (in `extendMiddle`).
Conversely, one can shrink a finpartition by deleting the element to the left, with a different
behavior if it was an atomic part (in `eraseLeft`, in which case the number of parts decreases by
one) or if it belonged to a non-atomic part (in `eraseMiddle`, in which case the number of parts
stays the same).

These operations are inverse to each other, giving rise to an equivalence between
`((c : OrderedFinpartition n) × Option (Fin c.length))` and `OrderedFinpartition (n + 1)`
called `OrderedFinPartition.extendEquiv`.
-/

/-- Extend an ordered partition of `n` entries, by adding a new singleton part to the left. -/
@[simps -fullyApplied length partSize]
def extendLeft (c : OrderedFinpartition n) : OrderedFinpartition (n + 1) where
  length := c.length + 1
  partSize := Fin.cons 1 c.partSize
  partSize_pos := Fin.cases (by simp) (by simp [c.partSize_pos])
  emb := Fin.cases (fun _ ↦ 0) (fun m ↦ Fin.succ ∘ c.emb m)
  emb_strictMono := by
    refine Fin.cases ?_ (fun i ↦ ?_)
    · exact @Subsingleton.strictMono _ _ _ _ (by simp; infer_instance) _
    · exact strictMono_succ.comp (c.emb_strictMono i)
  parts_strictMono i j hij := by
    induction j using Fin.induction with
    | zero => simp at hij
    | succ j => induction i using Fin.induction with
      | zero => simp
      | succ i =>
        simp only [cons_succ, cases_succ, comp_apply, succ_lt_succ_iff]
        exact c.parts_strictMono (by simpa using hij)
  disjoint i hi j hj hij := by
    wlog h : j < i generalizing i j
    · exact .symm
        (this j (mem_univ j) i (mem_univ i) hij.symm (lt_of_le_of_ne (le_of_not_gt h) hij))
    induction i using Fin.induction with
    | zero => simp at h
    | succ i =>
      induction j using Fin.induction with
      | zero =>
        simp only [onFun, cases_succ, cases_zero]
        apply Set.disjoint_iff_forall_ne.2
        simp only [mem_range, comp_apply, exists_prop', cons_zero, ne_eq, and_imp,
          Nonempty.forall, forall_const, forall_eq', forall_exists_index, forall_apply_eq_imp_iff]
        exact fun _ ↦ succ_ne_zero _
      | succ j =>
        simp only [onFun, cases_succ]
        apply Set.disjoint_iff_forall_ne.2
        simp only [mem_range, comp_apply, ne_eq, forall_exists_index, forall_apply_eq_imp_iff,
          succ_inj]
        intro a b
        apply c.emb_ne_emb_of_ne (by simpa using hij)
  cover := by
    refine Fin.cases ?_ (fun i ↦ ?_)
    · simp only [mem_range]
      exact ⟨0, ⟨0, by simp⟩, by simp⟩
    · simp only [mem_range]
      exact ⟨Fin.succ (c.index i), Fin.cast (by simp) (c.invEmbedding i), by simp⟩

@[simp] lemma range_extendLeft_zero (c : OrderedFinpartition n) :
    range (c.extendLeft.emb 0) = {0} := by
  simp only [extendLeft, cases_zero]
  apply @range_const _ _ (by simp; infer_instance)

/-- Extend an ordered partition of `n` entries, by adding to the `i`-th part a new point to the
left. -/
@[simps -fullyApplied length partSize]
def extendMiddle (c : OrderedFinpartition n) (k : Fin c.length) : OrderedFinpartition (n + 1) where
  length := c.length
  partSize := update c.partSize k (c.partSize k + 1)
  partSize_pos m := by
    rcases eq_or_ne m k with rfl | hm
    · simp
    · simpa [hm] using c.partSize_pos m
  emb := by
    intro m
    by_cases h : m = k
    · have : update c.partSize k (c.partSize k + 1) m = c.partSize k + 1 := by rw [h]; simp
      exact Fin.cases 0 (succ ∘ c.emb k) ∘ Fin.cast this
    · have : update c.partSize k (c.partSize k + 1) m = c.partSize m := by simp [h]
      exact succ ∘ c.emb m ∘ Fin.cast this
  emb_strictMono := by
    intro m
    rcases eq_or_ne m k with rfl | hm
    · suffices ∀ (a' b' : Fin (c.partSize m + 1)), a' < b' →
          (cases (motive := fun _ ↦ Fin (n + 1)) 0 (succ ∘ c.emb m)) a' <
          (cases (motive := fun _ ↦ Fin (n + 1)) 0 (succ ∘ c.emb m)) b' by
        simp only [↓reduceDIte]
        intro a b hab
        exact this _ _ hab
      intro a' b' h'
      induction b' using Fin.induction with
      | zero => simp at h'
      | succ b =>
        induction a' using Fin.induction with
        | zero => simp
        | succ a' =>
          simp only [cases_succ, comp_apply, succ_lt_succ_iff]
          exact c.emb_strictMono m (by simpa using h')
    · simp only [hm, ↓reduceDIte]
      exact strictMono_succ.comp ((c.emb_strictMono m).comp (by exact fun ⦃a b⦄ h ↦ h))
  parts_strictMono := by
    convert strictMono_succ.comp c.parts_strictMono with m
    rcases eq_or_ne m k with rfl | hm
    · simp only [↓reduceDIte, update_self, add_tsub_cancel_right, comp_apply, cast_mk]
      let a : Fin (c.partSize m + 1) := ⟨c.partSize m, lt_add_one (c.partSize m)⟩
      let b : Fin (c.partSize m) := ⟨c.partSize m - 1, Nat.sub_one_lt_of_lt (c.partSize_pos m)⟩
      change (cases (motive := fun _ ↦ Fin (n + 1)) 0 (succ ∘ c.emb m)) a = succ (c.emb m b)
      have : a = succ b := by
        simpa [a, b, succ] using (Nat.sub_eq_iff_eq_add (c.partSize_pos m)).mp rfl
      simp [this]
    · simp [hm]
  disjoint i hi j hj hij := by
    wlog h : i ≠ k generalizing i j
    · apply Disjoint.symm
        (this j (mem_univ j) i (mem_univ i) hij.symm ?_)
      simp only [ne_eq, Decidable.not_not] at h
      simpa [h] using hij.symm
    rcases eq_or_ne j k with rfl | hj
    · simp only [onFun, ↓reduceDIte]
      suffices ∀ (a' : Fin (c.partSize i)) (b' : Fin (c.partSize j + 1)),
          succ (c.emb i a') ≠ cases (motive := fun _ ↦ Fin (n + 1)) 0 (succ ∘ c.emb j) b' by
        apply Set.disjoint_iff_forall_ne.2
        simp only [hij, ↓reduceDIte, mem_range, comp_apply, ne_eq, forall_exists_index,
          forall_apply_eq_imp_iff]
        intro a b
        apply this
      intro a' b'
      induction b' using Fin.induction with
      | zero => simp
      | succ b' =>
        simp only [cases_succ, comp_apply, ne_eq, succ_inj]
        apply c.emb_ne_emb_of_ne hij
    · simp only [onFun, h, ↓reduceDIte, hj]
      apply Set.disjoint_iff_forall_ne.2
      simp only [mem_range, comp_apply, ne_eq, forall_exists_index, forall_apply_eq_imp_iff,
        succ_inj]
      intro a b
      apply c.emb_ne_emb_of_ne hij
  cover := by
    refine Fin.cases ?_ (fun i ↦ ?_)
    · simp only [mem_range]
      exact ⟨k, ⟨0, by simp⟩, by simp⟩
    · simp only [mem_range]
      rcases eq_or_ne (c.index i) k with rfl | hi
      · have A : update c.partSize (c.index i) (c.partSize (c.index i) + 1) (c.index i) =
          c.partSize (c.index i) + 1 := by simp
        exact ⟨c.index i, (succ (c.invEmbedding i)).cast A.symm, by simp⟩
      · have A : update c.partSize k (c.partSize k + 1) (c.index i) = c.partSize (c.index i) := by
          simp [hi]
        exact ⟨c.index i, (c.invEmbedding i).cast A.symm, by simp [hi]⟩

lemma index_extendMiddle_zero (c : OrderedFinpartition n) (i : Fin c.length) :
    (c.extendMiddle i).index 0 = i := by
  have : (c.extendMiddle i).emb i 0 = 0 := by simp [extendMiddle]
  conv_rhs at this => rw [← (c.extendMiddle i).emb_invEmbedding 0]
  contrapose! this
  exact (c.extendMiddle i).emb_ne_emb_of_ne (Ne.symm this)

lemma range_emb_extendMiddle_ne_singleton_zero (c : OrderedFinpartition n) (i j : Fin c.length) :
    range ((c.extendMiddle i).emb j) ≠ {0} := by
  intro h
  rcases eq_or_ne j i with rfl | hij
  · have : Fin.succ (c.emb j 0) ∈ ({0} : Set (Fin n.succ)) := by
      rw [← h]
      simp only [Nat.succ_eq_add_one, mem_range]
      have A : (c.extendMiddle j).partSize j = c.partSize j + 1 := by simp [extendMiddle]
      refine ⟨Fin.cast A.symm (succ 0), ?_⟩
      simp only [extendMiddle, ↓reduceDIte, comp_apply, Fin.cast_cast, cast_eq_self, cases_succ]
    simp only [mem_singleton_iff] at this
    exact Fin.succ_ne_zero _ this
  · have : (c.extendMiddle i).emb j 0 ∈ range ((c.extendMiddle i).emb j) :=
      mem_range_self 0
    rw [h] at this
    simp only [extendMiddle, hij, ↓reduceDIte, comp_apply, cast_zero, mem_singleton_iff] at this
    exact Fin.succ_ne_zero _ this

/-- Extend an ordered partition of `n` entries, by adding singleton to the left or appending it
to one of the existing part. -/
def extend (c : OrderedFinpartition n) (i : Option (Fin c.length)) : OrderedFinpartition (n + 1) :=
  match i with
  | none => c.extendLeft
  | some i => c.extendMiddle i

@[simp] lemma extend_none (c : OrderedFinpartition n) : c.extend none = c.extendLeft := rfl

@[simp]
lemma extend_some (c : OrderedFinpartition n) (i : Fin c.length) : c.extend i = c.extendMiddle i :=
  rfl

/-- Given an ordered finpartition of `n+1`, with a leftmost atom equal to `{0}`, remove this
atom to form an ordered finpartition of `n`. -/
def eraseLeft (c : OrderedFinpartition (n + 1)) (hc : range (c.emb 0) = {0}) :
    OrderedFinpartition n where
  length := c.length - 1
  partSize := by
    have : c.length - 1 + 1 = c.length := Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))
    exact fun i ↦ c.partSize (Fin.cast this (succ i))
  partSize_pos i := c.partSize_pos _
  emb i j := by
    have : c.length - 1 + 1 = c.length := Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))
    refine Fin.pred (c.emb (Fin.cast this (succ i)) j) ?_
    have := c.disjoint (mem_univ (Fin.cast this (succ i))) (mem_univ 0) (ne_of_beq_false rfl)
    exact Set.disjoint_iff_forall_ne.1 this (by simp) (by simp only [mem_singleton_iff, hc])
  emb_strictMono i a b hab := by
    simp only [pred_lt_pred_iff, Nat.succ_eq_add_one]
    apply c.emb_strictMono _ hab
  parts_strictMono := by
    intro i j hij
    simp only [pred_lt_pred_iff, Nat.succ_eq_add_one]
    apply c.parts_strictMono (cast_strictMono _ (strictMono_succ hij))
  disjoint i _ j _ hij := by
    apply Set.disjoint_iff_forall_ne.2
    simp only [mem_range, ne_eq, forall_exists_index, forall_apply_eq_imp_iff, pred_inj]
    intro a b
    exact c.emb_ne_emb_of_ne ((cast_injective _).ne (by simpa using hij))
  cover x := by
    simp only [mem_range]
    obtain ⟨i, j, hij⟩ : ∃ (i : Fin c.length), ∃ (j : Fin (c.partSize i)), c.emb i j = succ x :=
      ⟨c.index (succ x), c.invEmbedding (succ x), by simp⟩
    have A : c.length = c.length - 1 + 1 :=
      (Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))).symm
    have i_ne : i ≠ 0 := by
      intro h
      have : succ x ∈ range (c.emb i) := by rw [← hij]; apply mem_range_self
      rw [h, hc, mem_singleton_iff] at this
      exact Fin.succ_ne_zero _ this
    refine ⟨pred (Fin.cast A i) (by simpa using i_ne), Fin.cast (by simp) j, ?_⟩
    have : x = pred (succ x) (succ_ne_zero x) := rfl
    rw [this]
    congr
    rw [← hij]
    congr 1
    · simp
    · simp [Fin.heq_ext_iff]

/-- Given an ordered finpartition of `n+1`, with a leftmost atom different from `{0}`, remove `{0}`
from the atom that contains it, to form an ordered finpartition of `n`. -/
def eraseMiddle (c : OrderedFinpartition (n + 1)) (hc : range (c.emb 0) ≠ {0}) :
    OrderedFinpartition n where
  length := c.length
  partSize := update c.partSize (c.index 0) (c.partSize (c.index 0) - 1)
  partSize_pos i := by
    rcases eq_or_ne i (c.index 0) with rfl | hi
    · simpa using c.one_lt_partSize_index_zero hc
    · simp only [ne_eq, hi, not_false_eq_true, update_of_ne]
      exact c.partSize_pos i
  emb i j := by
    by_cases h : i = c.index 0
    · refine Fin.pred (c.emb i (Fin.cast ?_ (succ j))) ?_
      · rw [h]
        simpa using Nat.sub_add_cancel (c.partSize_pos (c.index 0))
      · have : 0 ≤ c.emb i 0 := Fin.zero_le _
        exact (this.trans_lt (c.emb_strictMono _ (succ_pos _))).ne'
    · refine Fin.pred (c.emb i (Fin.cast ?_ j)) ?_
      · simp [h]
      · conv_rhs => rw [← c.emb_invEmbedding 0]
        exact c.emb_ne_emb_of_ne h
  emb_strictMono i a b hab := by
    rcases eq_or_ne i (c.index 0) with rfl | hi
    · simp only [↓reduceDIte, Nat.succ_eq_add_one, pred_lt_pred_iff]
      exact (c.emb_strictMono _).comp (cast_strictMono _) (by simpa using hab)
    · simp only [hi, ↓reduceDIte, pred_lt_pred_iff, Nat.succ_eq_add_one]
      exact (c.emb_strictMono _).comp (cast_strictMono _) hab
  parts_strictMono i j hij := by
    simp only [Fin.lt_iff_val_lt_val]
    rw [← Nat.add_lt_add_iff_right (k := 1)]
    convert Fin.lt_iff_val_lt_val.1 (c.parts_strictMono hij)
    · rcases eq_or_ne i (c.index 0) with rfl | hi
      · simp only [↓reduceDIte, update_self, succ_mk, cast_mk, coe_pred]
        have A := c.one_lt_partSize_index_zero hc
        rw [Nat.sub_add_cancel]
        · congr; omega
        · rw [Order.one_le_iff_pos]
          conv_lhs => rw [show (0 : ℕ) = c.emb (c.index 0) 0 by simp [emb_zero]]
          rw [← lt_iff_val_lt_val]
          apply c.emb_strictMono
          simp [lt_iff_val_lt_val]
      · simp only [hi, ↓reduceDIte, ne_eq, not_false_eq_true, update_of_ne, cast_mk, coe_pred]
        apply Nat.sub_add_cancel
        have : c.emb i ⟨c.partSize i - 1, Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩
            ≠ c.emb (c.index 0) 0 := c.emb_ne_emb_of_ne hi
        simp only [c.emb_zero, ne_eq, ← val_eq_val, val_zero] at this
        omega
    · rcases eq_or_ne j (c.index 0) with rfl | hj
      · simp only [↓reduceDIte, update_self, succ_mk, cast_mk, coe_pred]
        have A := c.one_lt_partSize_index_zero hc
        rw [Nat.sub_add_cancel]
        · congr; omega
        · rw [Order.one_le_iff_pos]
          conv_lhs => rw [show (0 : ℕ) = c.emb (c.index 0) 0 by simp [emb_zero]]
          rw [← lt_iff_val_lt_val]
          apply c.emb_strictMono
          simp [lt_iff_val_lt_val]
      · simp only [hj, ↓reduceDIte, ne_eq, not_false_eq_true, update_of_ne, cast_mk, coe_pred]
        apply Nat.sub_add_cancel
        have : c.emb j ⟨c.partSize j - 1, Nat.sub_one_lt_of_lt (c.partSize_pos j)⟩
            ≠ c.emb (c.index 0) 0 := c.emb_ne_emb_of_ne hj
        simp only [c.emb_zero, ne_eq, ← val_eq_val, val_zero] at this
        omega
  disjoint i _ j _ hij := by
    wlog h : i ≠ c.index 0 generalizing i j
    · apply Disjoint.symm
        (this j (mem_univ j) i (mem_univ i) hij.symm ?_)
      simp only [ne_eq, Decidable.not_not] at h
      simpa [h] using hij.symm
    rcases eq_or_ne j (c.index 0) with rfl | hj
    · simp only [onFun, hij, ↓reduceDIte]
      apply Set.disjoint_iff_forall_ne.2
      simp only [mem_range, ne_eq, forall_exists_index, forall_apply_eq_imp_iff, pred_inj]
      intro a b
      exact c.emb_ne_emb_of_ne hij
    · simp only [onFun, h, ↓reduceDIte, hj]
      apply Set.disjoint_iff_forall_ne.2
      simp only [mem_range, ne_eq, forall_exists_index, forall_apply_eq_imp_iff, pred_inj]
      intro a b
      exact c.emb_ne_emb_of_ne hij
  cover x := by
    simp only [mem_range]
    obtain ⟨i, j, hij⟩ : ∃ (i : Fin c.length), ∃ (j : Fin (c.partSize i)), c.emb i j = succ x :=
      ⟨c.index (succ x), c.invEmbedding (succ x), by simp⟩
    rcases eq_or_ne i (c.index 0) with rfl | hi
    · refine ⟨c.index 0, ?_⟩
      have j_ne : j ≠ 0 := by
        rintro rfl
        simp only [c.emb_zero] at hij
        exact (Fin.succ_ne_zero _).symm hij
      have je_ne' : (j : ℕ) ≠ 0 := by simpa
      simp only [↓reduceDIte]
      have A : c.partSize (c.index 0) - 1 + 1 = c.partSize (c.index 0) :=
        Nat.sub_add_cancel (c.partSize_pos _)
      have B : update c.partSize (c.index 0) (c.partSize (c.index 0) - 1) (c.index 0) =
        c.partSize (c.index 0) - 1 := by simp
      refine ⟨Fin.cast B.symm (pred (Fin.cast A.symm j) ?_), ?_⟩
      · simpa using j_ne
      · have : x = pred (succ x) (succ_ne_zero x) := rfl
        rw [this]
        simp only [pred_inj, ← hij]
        congr 1
        rw [← val_eq_val]
        simp only [coe_cast, val_succ, coe_pred]
        omega
    · have A : update c.partSize (c.index 0) (c.partSize (c.index 0) - 1) i = c.partSize i := by
        simp [hi]
      exact ⟨i, Fin.cast A.symm j, by simp [hi, hij]⟩

open Classical in
/-- Extending the ordered partitions of `Fin n` bijects with the ordered partitions
of `Fin (n+1)`. -/
@[simps apply]
def extendEquiv (n : ℕ) :
    ((c : OrderedFinpartition n) × Option (Fin c.length)) ≃ OrderedFinpartition (n + 1) where
  toFun c := c.1.extend c.2
  invFun c := if h : range (c.emb 0) = {0} then ⟨c.eraseLeft h, none⟩ else
    ⟨c.eraseMiddle h, some (c.index 0)⟩
  left_inv := by
    rintro ⟨c, o⟩
    match o with
    | none =>
      simp only [extend, range_extendLeft_zero, ↓reduceDIte, Sigma.mk.inj_iff, heq_eq_eq,
        and_true]
      rfl
    | some i =>
      simp only [extend, range_emb_extendMiddle_ne_singleton_zero, ↓reduceDIte,
        Sigma.mk.inj_iff, heq_eq_eq, and_true, eraseMiddle,
        index_extendMiddle_zero]
      ext
      · rfl
      · simp only [heq_eq_eq, index_extendMiddle_zero]
        ext j
        rcases eq_or_ne i j with rfl | hij
        · simp [extendMiddle]
        · simp [hij.symm, extendMiddle]
      · refine HEq.symm (hfunext rfl ?_)
        simp only [heq_eq_eq, forall_eq']
        intro a
        rcases eq_or_ne a i with rfl | hij
        · refine (Fin.heq_fun_iff ?_).mpr ?_
          · rw [index_extendMiddle_zero]
            simp [extendMiddle]
          · simp [extendMiddle]
        · refine (Fin.heq_fun_iff ?_).mpr ?_
          · rw [index_extendMiddle_zero]
            simp [extendMiddle]
          · simp [extendMiddle, hij]
  right_inv c := by
    by_cases h : range (c.emb 0) = {0}
    · have A : c.length - 1 + 1 = c.length := Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))
      dsimp only
      rw [dif_pos h]
      simp only [extend, extendLeft, eraseLeft]
      ext
      · exact A
      · refine (Fin.heq_fun_iff A).mpr (fun i ↦ ?_)
        induction i using Fin.induction with
        | zero => change 1 = c.partSize 0; simp [c.partSize_eq_one_of_range_emb_eq_singleton h]
        | succ i => simp only [cons_succ, val_succ]; rfl
      · refine hfunext (congrArg Fin A) ?_
        simp only
        intro i i' h'
        have : i' = Fin.cast A i := eq_of_val_eq (by apply val_eq_val_of_heq h'.symm)
        subst this
        refine (Fin.heq_fun_iff ?_).mpr ?_
        · induction i using Fin.induction with
          | zero => simp [c.partSize_eq_one_of_range_emb_eq_singleton h]
          | succ i => simp
        · intro j
          induction i using Fin.induction with
          | zero =>
            simp only [cases_zero, cast_zero, val_eq_zero]
            exact (apply_eq_of_range_eq_singleton h _).symm
          | succ i => simp
    · dsimp only
      rw [dif_neg h]
      have B : c.partSize (c.index 0) - 1 + 1 = c.partSize (c.index 0) :=
        Nat.sub_add_cancel (c.partSize_pos (c.index 0))
      simp only [extend, extendMiddle, eraseMiddle, ↓reduceDIte]
      ext
      · rfl
      · simp only [update_self, update_idem, heq_eq_eq, update_eq_self_iff, B]
      · refine hfunext rfl ?_
        simp only [heq_eq_eq, forall_eq']
        intro i
        refine ((Fin.heq_fun_iff ?_).mpr ?_).symm
        · simp only [update_self, B, update_idem, update_eq_self]
        · intro j
          rcases eq_or_ne i (c.index 0) with rfl | hi
          · simp only [↓reduceDIte, comp_apply]
            rcases eq_or_ne j 0 with rfl | hj
            · simpa using c.emb_zero
            · let j' := Fin.pred (j.cast B.symm) (by simpa using hj)
              have : j = (succ j').cast B := by simp [j']
              simp only [this, coe_cast, val_succ, cast_mk, cases_succ', comp_apply, succ_mk,
                succ_pred]
              rfl
          · simp [hi]

/-! ### Applying ordered finpartitions to multilinear maps -/

/-- Given a formal multilinear series `p`, an ordered partition `c` of `n` and the index `i` of a
block of `c`, we may define a function on `Fin n → E` by picking the variables in the `i`-th block
of `n`, and applying the corresponding coefficient of `p` to these variables. This function is
called `p.applyOrderedFinpartition c v i` for `v : Fin n → E` and `i : Fin c.k`. -/
def applyOrderedFinpartition (p : ∀ (i : Fin c.length), E [×c.partSize i]→L[𝕜] F) :
    (Fin n → E) → Fin c.length → F :=
  fun v m ↦ p m (v ∘ c.emb m)

lemma applyOrderedFinpartition_apply (p : ∀ (i : Fin c.length), E [×c.partSize i]→L[𝕜] F)
    (v : Fin n → E) :
    c.applyOrderedFinpartition p v = (fun m ↦ p m (v ∘ c.emb m)) := rfl

theorem norm_applyOrderedFinpartition_le (p : ∀ (i : Fin c.length), E [×c.partSize i]→L[𝕜] F)
    (v : Fin n → E) (m : Fin c.length) :
    ‖c.applyOrderedFinpartition p v m‖ ≤ ‖p m‖ * ∏ i : Fin (c.partSize m), ‖v (c.emb m i)‖ :=
  (p m).le_opNorm _

/-- Technical lemma stating how `c.applyOrderedFinpartition` commutes with updating variables. This
will be the key point to show that functions constructed from `applyOrderedFinpartition` retain
multilinearity. -/
theorem applyOrderedFinpartition_update_right
    (p : ∀ (i : Fin c.length), E [×c.partSize i]→L[𝕜] F)
    (j : Fin n) (v : Fin n → E) (z : E) :
    c.applyOrderedFinpartition p (update v j z) =
      update (c.applyOrderedFinpartition p v) (c.index j)
        (p (c.index j)
          (Function.update (v ∘ c.emb (c.index j)) (c.invEmbedding j) z)) := by
  ext m
  by_cases h : m = c.index j
  · rw [h]
    simp only [applyOrderedFinpartition, update_self]
    congr
    rw [← Function.update_comp_eq_of_injective]
    · simp
    · exact (c.emb_strictMono (c.index j)).injective
  · simp only [applyOrderedFinpartition, ne_eq, h, not_false_eq_true,
      update_of_ne]
    congr 1
    apply Function.update_comp_eq_of_notMem_range
    have A : Disjoint (range (c.emb m)) (range (c.emb (c.index j))) :=
      c.disjoint (mem_univ m) (mem_univ (c.index j)) h
    have : j ∈ range (c.emb (c.index j)) := mem_range.2 ⟨c.invEmbedding j, by simp⟩
    exact Set.disjoint_right.1 A this

theorem applyOrderedFinpartition_update_left (p : ∀ (i : Fin c.length), E [×c.partSize i]→L[𝕜] F)
    (m : Fin c.length) (v : Fin n → E) (q : E [×c.partSize m]→L[𝕜] F) :
    c.applyOrderedFinpartition (update p m q) v
      = update (c.applyOrderedFinpartition p v) m (q (v ∘ c.emb m)) := by
  ext d
  by_cases h : d = m
  · rw [h]
    simp [applyOrderedFinpartition]
  · simp [h, applyOrderedFinpartition]

/-- Given a an ordered finite partition `c` of `n`, a continuous multilinear map `f` in `c.length`
variables, and for each `m` a continuous multilinear map `p m` in `c.partSize m` variables,
one can form a continuous multilinear map in `n`
variables by applying `p m` to each part of the partition, and then
applying `f` to the resulting vector. It is called `c.compAlongOrderedFinpartition f p`. -/
def compAlongOrderedFinpartition (f : F [×c.length]→L[𝕜] G) (p : ∀ i, E [×c.partSize i]→L[𝕜] F) :
    E[×n]→L[𝕜] G where
  toMultilinearMap :=
    MultilinearMap.mk' (fun v ↦ f (c.applyOrderedFinpartition p v))
      (fun v i x y ↦ by
        simp only [applyOrderedFinpartition_update_right,
          ContinuousMultilinearMap.map_update_add])
      (fun v i c x ↦ by
        simp only [applyOrderedFinpartition_update_right,
          ContinuousMultilinearMap.map_update_smul])
  cont := by
    apply f.cont.comp
    change Continuous (fun v m ↦ p m (v ∘ c.emb m))
    fun_prop

@[simp] lemma compAlongOrderFinpartition_apply (f : F [×c.length]→L[𝕜] G)
    (p : ∀ i, E [×c.partSize i]→L[𝕜] F) (v : Fin n → E) :
    c.compAlongOrderedFinpartition f p v = f (c.applyOrderedFinpartition p v) := rfl

theorem norm_compAlongOrderedFinpartition_le (f : F [×c.length]→L[𝕜] G)
    (p : ∀ i, E [×c.partSize i]→L[𝕜] F) :
    ‖c.compAlongOrderedFinpartition f p‖ ≤ ‖f‖ * ∏ i, ‖p i‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v ↦ ?_
  rw [compAlongOrderFinpartition_apply, mul_assoc, ← c.prod_sigma_eq_prod,
    ← Finset.prod_mul_distrib]
  exact f.le_opNorm_mul_prod_of_le <| c.norm_applyOrderedFinpartition_le _ _

/-- Bundled version of `compAlongOrderedFinpartition`, depending linearly on `f`
and multilinearly on `p`. -/
@[simps! apply_apply]
def compAlongOrderedFinpartitionₗ :
    (F [×c.length]→L[𝕜] G) →ₗ[𝕜]
      MultilinearMap 𝕜 (fun i : Fin c.length ↦ E[×c.partSize i]→L[𝕜] F) (E[×n]→L[𝕜] G) where
  toFun f :=
    MultilinearMap.mk' (fun p ↦ c.compAlongOrderedFinpartition f p)
      (fun p m q q' ↦ by
        ext v
        simp [applyOrderedFinpartition_update_left])
      (fun p m a q ↦ by
        ext v
        simp [applyOrderedFinpartition_update_left])
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (𝕜 E F G) in
/-- Bundled version of `compAlongOrderedFinpartition`, depending continuously linearly on `f`
and continuously multilinearly on `p`. -/
noncomputable def compAlongOrderedFinpartitionL :
    (F [×c.length]→L[𝕜] G) →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun i ↦ E[×c.partSize i]→L[𝕜] F) (E[×n]→L[𝕜] G) := by
  refine MultilinearMap.mkContinuousLinear c.compAlongOrderedFinpartitionₗ 1 fun f p ↦ ?_
  simp only [one_mul, compAlongOrderedFinpartitionₗ_apply_apply]
  apply norm_compAlongOrderedFinpartition_le

@[simp] lemma compAlongOrderedFinpartitionL_apply (f : F [×c.length]→L[𝕜] G)
    (p : ∀ (i : Fin c.length), E [×c.partSize i]→L[𝕜] F) :
    c.compAlongOrderedFinpartitionL 𝕜 E F G f p = c.compAlongOrderedFinpartition f p := rfl

theorem norm_compAlongOrderedFinpartitionL_le :
    ‖c.compAlongOrderedFinpartitionL 𝕜 E F G‖ ≤ 1 :=
  MultilinearMap.mkContinuousLinear_norm_le _ zero_le_one _

end OrderedFinpartition

/-! ### The Faa di Bruno formula -/

namespace FormalMultilinearSeries

/-- Given two formal multilinear series `q` and `p` and a composition `c` of `n`, one may
form a continuous multilinear map in `n` variables by applying the right coefficient of `p` to each
block of the composition, and then applying `q c.length` to the resulting vector. It is
called `q.compAlongComposition p c`. -/
def compAlongOrderedFinpartition {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition n) :
    E [×n]→L[𝕜] G :=
  c.compAlongOrderedFinpartition (q c.length) (fun m ↦ p (c.partSize m))

@[simp]
theorem compAlongOrderedFinpartition_apply {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition n) (v : Fin n → E) :
    (q.compAlongOrderedFinpartition p c) v =
      q c.length (c.applyOrderedFinpartition (fun m ↦ (p (c.partSize m))) v) :=
  rfl

/-- Taylor formal composition of two formal multilinear series. The `n`-th coefficient in the
composition is defined to be the sum of `q.compAlongOrderedFinpartition p c` over all
ordered partitions of `n`.
In other words, this term (as a multilinear function applied to `v₀, ..., vₙ₋₁`) is
`∑'_{k} ∑'_{I₀ ⊔ ... ⊔ Iₖ₋₁ = {0, ..., n-1}} qₖ (p_{i₀} (...), ..., p_{iₖ₋₁} (...))`, where
`iₘ` is the size of `Iₘ` and one puts all variables of `Iₘ` as arguments to `p_{iₘ}`, in
increasing order. The sets `I₀, ..., Iₖ₋₁` are ordered so that `max I₀ < max I₁ < ... < max Iₖ₋₁`.

This definition is chosen so that the `n`-th derivative of `g ∘ f` is the Taylor composition of
the iterated derivatives of `g` and of `f`.

Not to be confused with another notion of composition for formal multilinear series, called just
`FormalMultilinearSeries.comp`, appearing in the composition of analytic functions.
-/
protected noncomputable def taylorComp
    (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 E G :=
  fun n ↦ ∑ c : OrderedFinpartition n, q.compAlongOrderedFinpartition p c

end FormalMultilinearSeries

theorem analyticOn_taylorComp
    (hq : ∀ (n : ℕ), AnalyticOn 𝕜 (fun x ↦ q x n) t)
    (hp : ∀ n, AnalyticOn 𝕜 (fun x ↦ p x n) s) {f : E → F}
    (hf : AnalyticOn 𝕜 f s) (h : MapsTo f s t) (n : ℕ) :
    AnalyticOn 𝕜 (fun x ↦ (q (f x)).taylorComp (p x) n) s := by
  apply Finset.analyticOn_fun_sum _ (fun c _ ↦ ?_)
  let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
  change AnalyticOn 𝕜
    ((fun p ↦ B p.1 p.2) ∘ (fun x ↦ (q (f x) c.length, fun m ↦ p x (c.partSize m)))) s
  apply B.analyticOnNhd_uncurry_of_multilinear.comp_analyticOn ?_ (mapsTo_univ _ _)
  apply AnalyticOn.prod
  · exact (hq c.length).comp hf h
  · exact AnalyticOn.pi (fun i ↦ hp _)

open OrderedFinpartition

/-- Composing two formal multilinear series `q` and `p` along an ordered partition extended by a
new atom to the left corresponds to applying `p 1` on the first coordinates, and the initial
ordered partition on the other coordinates.
This is one of the terms that appears when differentiating in the Faa di Bruno
formula, going from step `m` to step `m + 1`. -/
private lemma faaDiBruno_aux1 {m : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition m) :
    (q.compAlongOrderedFinpartition p (c.extend none)).curryLeft =
    ((c.compAlongOrderedFinpartitionL 𝕜 E F G).flipMultilinear fun i ↦ p (c.partSize i)).comp
      ((q (c.length + 1)).curryLeft.comp ((continuousMultilinearCurryFin1 𝕜 E F) (p 1))) := by
  ext e v
  simp only [Nat.succ_eq_add_one, OrderedFinpartition.extend, extendLeft,
    ContinuousMultilinearMap.curryLeft_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply, applyOrderedFinpartition_apply,
    ContinuousLinearMap.coe_comp', comp_apply, continuousMultilinearCurryFin1_apply,
    Matrix.zero_empty, ContinuousLinearMap.flipMultilinear_apply_apply,
    compAlongOrderedFinpartitionL_apply, compAlongOrderFinpartition_apply]
  congr
  ext j
  exact Fin.cases rfl (fun i ↦ rfl) j

/-- Composing a formal multilinear series with an ordered partition extended by adding a left point
to an already existing atom of index `i` corresponds to updating the `i`th block,
using `p (c.partSize i + 1)` instead of `p (c.partSize i)` there.
This is one of the terms that appears when differentiating in the Faa di Bruno
formula, going from step `m` to step `m + 1`. -/
private lemma faaDiBruno_aux2 {m : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition m) (i : Fin c.length) :
    (q.compAlongOrderedFinpartition p (c.extend (some i))).curryLeft =
    ((c.compAlongOrderedFinpartitionL 𝕜 E F G (q c.length)).toContinuousLinearMap
      (fun i ↦ p (c.partSize i)) i).comp (p (c.partSize i + 1)).curryLeft := by
  ext e v
  simp? [OrderedFinpartition.extend, extendMiddle, applyOrderedFinpartition_apply] says
    simp only [Nat.succ_eq_add_one, OrderedFinpartition.extend, extendMiddle,
      ContinuousMultilinearMap.curryLeft_apply,
      FormalMultilinearSeries.compAlongOrderedFinpartition_apply, applyOrderedFinpartition_apply,
      ContinuousLinearMap.coe_comp', comp_apply,
      ContinuousMultilinearMap.toContinuousLinearMap_apply, compAlongOrderedFinpartitionL_apply,
      compAlongOrderFinpartition_apply]
  congr
  ext j
  rcases eq_or_ne j i with rfl | hij
  · simp only [↓reduceDIte, update_self, ContinuousMultilinearMap.curryLeft_apply,
      Nat.succ_eq_add_one]
    apply FormalMultilinearSeries.congr _ (by simp)
    intro a ha h'a
    match a with
    | 0 => simp
    | a + 1 => simp [cons]
  · simp only [hij, ↓reduceDIte, ne_eq, not_false_eq_true, update_of_ne]
    apply FormalMultilinearSeries.congr _ (by simp [hij])
    simp

/-- *Faa di Bruno* formula: If two functions `g` and `f` have Taylor series up to `n` given by
`q` and `p`, then `g ∘ f` also has a Taylor series, given by `q.taylorComp p`. -/
theorem HasFTaylorSeriesUpToOn.comp {n : WithTop ℕ∞} {g : F → G} {f : E → F}
    (hg : HasFTaylorSeriesUpToOn n g q t) (hf : HasFTaylorSeriesUpToOn n f p s) (h : MapsTo f s t) :
    HasFTaylorSeriesUpToOn n (g ∘ f) (fun x ↦ (q (f x)).taylorComp (p x)) s := by
  /- One has to check that the `m+1`-th term is the derivative of the `m`-th term. The `m`-th term
  is a sum, that one can differentiate term by term. Each term is a linear map into continuous
  multilinear maps, applied to parts of `p` and `q`. One knows how to differentiate such a map,
  thanks to `HasFDerivWithinAt.linear_multilinear_comp`. The terms that show up are matched, using
  `faaDiBruno_aux1` and `faaDiBruno_aux2`, with terms of the same form at order `m+1`. Then, one
  needs to check that one gets each term once and exactly once, which is given by the bijection
  `OrderedFinpartition.extendEquiv m`. -/
  classical
  constructor
  · intro x hx
    simp [FormalMultilinearSeries.taylorComp, default, HasFTaylorSeriesUpToOn.zero_eq' hg (h hx)]
  · intro m hm x hx
    have A (c : OrderedFinpartition m) :
      HasFDerivWithinAt (fun x ↦ (q (f x)).compAlongOrderedFinpartition (p x) c)
        (∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x := by
      let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
      change HasFDerivWithinAt (fun y ↦ B (q (f y) c.length) (fun i ↦ p y (c.partSize i)))
        (∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x
      have cm : (c.length : WithTop ℕ∞) ≤ m := mod_cast OrderedFinpartition.length_le c
      have cp i : (c.partSize i : WithTop ℕ∞) ≤ m := by
        exact_mod_cast OrderedFinpartition.partSize_le c i
      have I i : HasFDerivWithinAt (fun x ↦ p x (c.partSize i))
          (p x (c.partSize i).succ).curryLeft s x :=
        hf.fderivWithin (c.partSize i) ((cp i).trans_lt hm) x hx
      have J : HasFDerivWithinAt (fun x ↦ q x c.length) (q (f x) c.length.succ).curryLeft
        t (f x) := hg.fderivWithin c.length (cm.trans_lt hm) (f x) (h hx)
      have K : HasFDerivWithinAt f ((continuousMultilinearCurryFin1 𝕜 E F) (p x 1)) s x :=
        hf.hasFDerivWithinAt (le_trans (mod_cast Nat.le_add_left 1 m)
          (ENat.add_one_natCast_le_withTop_of_lt hm)) hx
      convert HasFDerivWithinAt.linear_multilinear_comp (J.comp x K h) I B
      simp only [B, Nat.succ_eq_add_one, Fintype.sum_option, comp_apply, faaDiBruno_aux1,
        faaDiBruno_aux2]
    have B : HasFDerivWithinAt (fun x ↦ (q (f x)).taylorComp (p x) m)
        (∑ c : OrderedFinpartition m, ∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x :=
      HasFDerivWithinAt.fun_sum (fun c _ ↦ A c)
    suffices ∑ c : OrderedFinpartition m, ∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)) =
        (q (f x)).taylorComp (p x) (m + 1) by
      rw [← this]
      convert B
      ext v
      simp only [Nat.succ_eq_add_one, Fintype.sum_option, ContinuousMultilinearMap.curryLeft_apply,
        ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.add_apply,
        FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ContinuousLinearMap.coe_sum',
        Finset.sum_apply, ContinuousLinearMap.add_apply]
    rw [Finset.sum_sigma']
    exact Fintype.sum_equiv (OrderedFinpartition.extendEquiv m) _ _ (fun p ↦ rfl)
  · intro m hm
    apply continuousOn_finset_sum _ (fun c _ ↦ ?_)
    let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
    change ContinuousOn
      ((fun p ↦ B p.1 p.2) ∘ (fun x ↦ (q (f x) c.length, fun i ↦ p x (c.partSize i)))) s
    apply B.continuous_uncurry_of_multilinear.comp_continuousOn (ContinuousOn.prodMk ?_ ?_)
    · have : (c.length : WithTop ℕ∞) ≤ m := mod_cast OrderedFinpartition.length_le c
      exact (hg.cont c.length (this.trans hm)).comp hf.continuousOn h
    · apply continuousOn_pi.2 (fun i ↦ ?_)
      have : (c.partSize i : WithTop ℕ∞) ≤ m := by
        exact_mod_cast OrderedFinpartition.partSize_le c i
      exact hf.cont _ (this.trans hm)
