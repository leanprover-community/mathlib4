/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Subsingleton


#align_import combinatorics.composition from "leanprover-community/mathlib"@"92ca63f0fb391a9ca5f22d2409a6080e786d99f7"

/-!
# Compositions

A composition of a natural number `n` is a decomposition `n = i₀ + ... + i_{k-1}` of `n` into a sum
of positive integers. Combinatorially, it corresponds to a decomposition of `{0, ..., n-1}` into
non-empty blocks of consecutive integers, where the `iⱼ` are the lengths of the blocks.
This notion is closely related to that of a partition of `n`, but in a composition of `n` the
order of the `iⱼ`s matters.

We implement two different structures covering these two viewpoints on compositions. The first
one, made of a list of positive integers summing to `n`, is the main one and is called
`Composition n`. The second one is useful for combinatorial arguments (for instance to show that
the number of compositions of `n` is `2^(n-1)`). It is given by a subset of `{0, ..., n}`
containing `0` and `n`, where the elements of the subset (other than `n`) correspond to the leftmost
points of each block. The main API is built on `Composition n`, and we provide an equivalence
between the two types.

## Main functions

* `c : Composition n` is a structure, made of a list of integers which are all positive and
  add up to `n`.
* `composition_card` states that the cardinality of `Composition n` is exactly
  `2^(n-1)`, which is proved by constructing an equiv with `CompositionAsSet n` (see below), which
  is itself in bijection with the subsets of `Fin (n-1)` (this holds even for `n = 0`, where `-` is
  nat subtraction).

Let `c : Composition n` be a composition of `n`. Then
* `c.blocks` is the list of blocks in `c`.
* `c.length` is the number of blocks in the composition.
* `c.blocks_fun : Fin c.length → ℕ` is the realization of `c.blocks` as a function on
  `Fin c.length`. This is the main object when using compositions to understand the composition of
    analytic functions.
* `c.sizeUpTo : ℕ → ℕ` is the sum of the size of the blocks up to `i`.;
* `c.embedding i : Fin (c.blocks_fun i) → Fin n` is the increasing embedding of the `i`-th block in
  `Fin n`;
* `c.index j`, for `j : Fin n`, is the index of the block containing `j`.

* `Composition.ones n` is the composition of `n` made of ones, i.e., `[1, ..., 1]`.
* `Composition.single n (hn : 0 < n)` is the composition of `n` made of a single block of size `n`.

Compositions can also be used to split lists. Let `l` be a list of length `n` and `c` a composition
of `n`.
* `l.splitWrtComposition c` is a list of lists, made of the slices of `l` corresponding to the
  blocks of `c`.
* `join_splitWrtComposition` states that splitting a list and then joining it gives back the
  original list.
* `joinSplitWrtComposition_join` states that joining a list of lists, and then splitting it back
  according to the right composition, gives back the original list of lists.

We turn to the second viewpoint on compositions, that we realize as a finset of `Fin (n+1)`.
`c : CompositionAsSet n` is a structure made of a finset of `Fin (n+1)` called `c.boundaries`
and proofs that it contains `0` and `n`. (Taking a finset of `Fin n` containing `0` would not
make sense in the edge case `n = 0`, while the previous description works in all cases).
The elements of this set (other than `n`) correspond to leftmost points of blocks.
Thus, there is an equiv between `Composition n` and `CompositionAsSet n`. We
only construct basic API on `CompositionAsSet` (notably `c.length` and `c.blocks`) to be able
to construct this equiv, called `compositionEquiv n`. Since there is a straightforward equiv
between `CompositionAsSet n` and finsets of `{1, ..., n-1}` (obtained by removing `0` and `n`
from a `CompositionAsSet` and called `compositionAsSetEquiv n`), we deduce that
`CompositionAsSet n` and `Composition n` are both fintypes of cardinality `2^(n - 1)`
(see `compositionAsSet_card` and `composition_card`).

## Implementation details

The main motivation for this structure and its API is in the construction of the composition of
formal multilinear series, and the proof that the composition of analytic functions is analytic.

The representation of a composition as a list is very handy as lists are very flexible and already
have a well-developed API.

## Tags

Composition, partition

## References

<https://en.wikipedia.org/wiki/Composition_(combinatorics)>
-/


open List

variable {n : ℕ}

/-- A composition of `n` is a list of positive integers summing to `n`. -/
@[ext]
structure Composition (n : ℕ) where
  /-- List of positive integers summing to `n`-/
  blocks : List ℕ
  /-- Proof of positivity for `blocks`-/
  blocks_pos : ∀ {i}, i ∈ blocks → 0 < i
  /-- Proof that `blocks` sums to `n`-/
  blocks_sum : blocks.sum = n
#align composition Composition

/-- Combinatorial viewpoint on a composition of `n`, by seeing it as non-empty blocks of
consecutive integers in `{0, ..., n-1}`. We register every block by its left end-point, yielding
a finset containing `0`. As this does not make sense for `n = 0`, we add `n` to this finset, and
get a finset of `{0, ..., n}` containing `0` and `n`. This is the data in the structure
`CompositionAsSet n`. -/
@[ext]
structure CompositionAsSet (n : ℕ) where
  /-- Combinatorial viewpoint on a composition of `n` as consecutive integers `{0, ..., n-1}`-/
  boundaries : Finset (Fin n.succ)
  /-- Proof that `0` is a member of `boundaries`-/
  zero_mem : (0 : Fin n.succ) ∈ boundaries
  /-- Last element of the composition-/
  getLast_mem : Fin.last n ∈ boundaries
#align composition_as_set CompositionAsSet

instance {n : ℕ} : Inhabited (CompositionAsSet n) :=
  ⟨⟨Finset.univ, Finset.mem_univ _, Finset.mem_univ _⟩⟩

/-!
### Compositions

A composition of an integer `n` is a decomposition `n = i₀ + ... + i_{k-1}` of `n` into a sum of
positive integers.
-/


namespace Composition

variable (c : Composition n)

instance (n : ℕ) : ToString (Composition n) :=
  ⟨fun c => toString c.blocks⟩

/-- The length of a composition, i.e., the number of blocks in the composition. -/
abbrev length : ℕ :=
  c.blocks.length
#align composition.length Composition.length

theorem blocks_length : c.blocks.length = c.length :=
  rfl
#align composition.blocks_length Composition.blocks_length

/-- The blocks of a composition, seen as a function on `Fin c.length`. When composing analytic
functions using compositions, this is the main player. -/
def blocksFun : Fin c.length → ℕ := c.blocks.get
#align composition.blocks_fun Composition.blocksFun

theorem ofFn_blocksFun : ofFn c.blocksFun = c.blocks :=
  ofFn_get _
#align composition.of_fn_blocks_fun Composition.ofFn_blocksFun

theorem sum_blocksFun : ∑ i, c.blocksFun i = n := by
  conv_rhs => rw [← c.blocks_sum, ← ofFn_blocksFun, sum_ofFn]
#align composition.sum_blocks_fun Composition.sum_blocksFun

theorem blocksFun_mem_blocks (i : Fin c.length) : c.blocksFun i ∈ c.blocks :=
  get_mem _ _ _
#align composition.blocks_fun_mem_blocks Composition.blocksFun_mem_blocks

@[simp]
theorem one_le_blocks {i : ℕ} (h : i ∈ c.blocks) : 1 ≤ i :=
  c.blocks_pos h
#align composition.one_le_blocks Composition.one_le_blocks

@[simp]
theorem one_le_blocks' {i : ℕ} (h : i < c.length) : 1 ≤ c.blocks.get ⟨i, h⟩ :=
  c.one_le_blocks (get_mem (blocks c) i h)
#align composition.one_le_blocks' Composition.one_le_blocks'

@[simp]
theorem blocks_pos' (i : ℕ) (h : i < c.length) : 0 < c.blocks.get ⟨i, h⟩ :=
  c.one_le_blocks' h
#align composition.blocks_pos' Composition.blocks_pos'

theorem one_le_blocksFun (i : Fin c.length) : 1 ≤ c.blocksFun i :=
  c.one_le_blocks (c.blocksFun_mem_blocks i)
#align composition.one_le_blocks_fun Composition.one_le_blocksFun

theorem length_le : c.length ≤ n := by
  conv_rhs => rw [← c.blocks_sum]
  exact length_le_sum_of_one_le _ fun i hi => c.one_le_blocks hi
#align composition.length_le Composition.length_le

theorem length_pos_of_pos (h : 0 < n) : 0 < c.length := by
  apply length_pos_of_sum_pos
  convert h
  exact c.blocks_sum
#align composition.length_pos_of_pos Composition.length_pos_of_pos

/-- The sum of the sizes of the blocks in a composition up to `i`. -/
def sizeUpTo (i : ℕ) : ℕ :=
  (c.blocks.take i).sum
#align composition.size_up_to Composition.sizeUpTo

@[simp]
theorem sizeUpTo_zero : c.sizeUpTo 0 = 0 := by simp [sizeUpTo]
#align composition.size_up_to_zero Composition.sizeUpTo_zero

theorem sizeUpTo_ofLength_le (i : ℕ) (h : c.length ≤ i) : c.sizeUpTo i = n := by
  dsimp [sizeUpTo]
  convert c.blocks_sum
  exact take_all_of_le h
#align composition.size_up_to_of_length_le Composition.sizeUpTo_ofLength_le

@[simp]
theorem sizeUpTo_length : c.sizeUpTo c.length = n :=
  c.sizeUpTo_ofLength_le c.length le_rfl
#align composition.size_up_to_length Composition.sizeUpTo_length

theorem sizeUpTo_le (i : ℕ) : c.sizeUpTo i ≤ n := by
  conv_rhs => rw [← c.blocks_sum, ← sum_take_add_sum_drop _ i]
  exact Nat.le_add_right _ _
#align composition.size_up_to_le Composition.sizeUpTo_le

theorem sizeUpTo_succ {i : ℕ} (h : i < c.length) :
    c.sizeUpTo (i + 1) = c.sizeUpTo i + c.blocks.get ⟨i, h⟩ := by
  simp only [sizeUpTo]
  rw [sum_take_succ _ _ h]
#align composition.size_up_to_succ Composition.sizeUpTo_succ

theorem sizeUpTo_succ' (i : Fin c.length) :
    c.sizeUpTo ((i : ℕ) + 1) = c.sizeUpTo i + c.blocksFun i :=
  c.sizeUpTo_succ i.2
#align composition.size_up_to_succ' Composition.sizeUpTo_succ'

theorem sizeUpTo_strict_mono {i : ℕ} (h : i < c.length) : c.sizeUpTo i < c.sizeUpTo (i + 1) := by
  rw [c.sizeUpTo_succ h]
  simp
#align composition.size_up_to_strict_mono Composition.sizeUpTo_strict_mono

theorem monotone_sizeUpTo : Monotone c.sizeUpTo :=
  monotone_sum_take _
#align composition.monotone_size_up_to Composition.monotone_sizeUpTo

/-- The `i`-th boundary of a composition, i.e., the leftmost point of the `i`-th block. We include
a virtual point at the right of the last block, to make for a nice equiv with
`CompositionAsSet n`. -/
def boundary : Fin (c.length + 1) ↪o Fin (n + 1) :=
  (OrderEmbedding.ofStrictMono fun i => ⟨c.sizeUpTo i, Nat.lt_succ_of_le (c.sizeUpTo_le i)⟩) <|
    Fin.strictMono_iff_lt_succ.2 fun ⟨_, hi⟩ => c.sizeUpTo_strict_mono hi
#align composition.boundary Composition.boundary

@[simp]
theorem boundary_zero : c.boundary 0 = 0 := by simp [boundary, Fin.ext_iff]
#align composition.boundary_zero Composition.boundary_zero

@[simp]
theorem boundary_last : c.boundary (Fin.last c.length) = Fin.last n := by
  simp [boundary, Fin.ext_iff]
#align composition.boundary_last Composition.boundary_last

/-- The boundaries of a composition, i.e., the leftmost point of all the blocks. We include
a virtual point at the right of the last block, to make for a nice equiv with
`CompositionAsSet n`. -/
def boundaries : Finset (Fin (n + 1)) :=
  Finset.univ.map c.boundary.toEmbedding
#align composition.boundaries Composition.boundaries

theorem card_boundaries_eq_succ_length : c.boundaries.card = c.length + 1 := by simp [boundaries]
#align composition.card_boundaries_eq_succ_length Composition.card_boundaries_eq_succ_length

/-- To `c : Composition n`, one can associate a `CompositionAsSet n` by registering the leftmost
point of each block, and adding a virtual point at the right of the last block. -/
def toCompositionAsSet : CompositionAsSet n where
  boundaries := c.boundaries
  zero_mem := by
    simp only [boundaries, Finset.mem_univ, exists_prop_of_true, Finset.mem_map]
    exact ⟨0, And.intro True.intro rfl⟩
  getLast_mem := by
    simp only [boundaries, Finset.mem_univ, exists_prop_of_true, Finset.mem_map]
    exact ⟨Fin.last c.length, And.intro True.intro c.boundary_last⟩
#align composition.to_composition_as_set Composition.toCompositionAsSet

/-- The canonical increasing bijection between `Fin (c.length + 1)` and `c.boundaries` is
exactly `c.boundary`. -/
theorem orderEmbOfFin_boundaries :
    c.boundaries.orderEmbOfFin c.card_boundaries_eq_succ_length = c.boundary := by
  refine (Finset.orderEmbOfFin_unique' _ ?_).symm
  exact fun i => (Finset.mem_map' _).2 (Finset.mem_univ _)
#align composition.order_emb_of_fin_boundaries Composition.orderEmbOfFin_boundaries

/-- Embedding the `i`-th block of a composition (identified with `Fin (c.blocks_fun i)`) into
`Fin n` at the relevant position. -/
def embedding (i : Fin c.length) : Fin (c.blocksFun i) ↪o Fin n :=
  (Fin.natAddOrderEmb <| c.sizeUpTo i).trans <| Fin.castLEOrderEmb <|
    calc
      c.sizeUpTo i + c.blocksFun i = c.sizeUpTo (i + 1) := (c.sizeUpTo_succ _).symm
      _ ≤ c.sizeUpTo c.length := monotone_sum_take _ i.2
      _ = n := c.sizeUpTo_length
#align composition.embedding Composition.embedding

@[simp]
theorem coe_embedding (i : Fin c.length) (j : Fin (c.blocksFun i)) :
    (c.embedding i j : ℕ) = c.sizeUpTo i + j :=
  rfl
#align composition.coe_embedding Composition.coe_embedding

/-- `index_exists` asserts there is some `i` with `j < c.size_up_to (i+1)`.
In the next definition `index` we use `Nat.find` to produce the minimal such index.
-/
theorem index_exists {j : ℕ} (h : j < n) : ∃ i : ℕ, j < c.sizeUpTo (i + 1) ∧ i < c.length := by
  have n_pos : 0 < n := lt_of_le_of_lt (zero_le j) h
  have : 0 < c.blocks.sum := by rwa [← c.blocks_sum] at n_pos
  have length_pos : 0 < c.blocks.length := length_pos_of_sum_pos (blocks c) this
  refine ⟨c.length - 1, ?_, Nat.pred_lt (ne_of_gt length_pos)⟩
  have : c.length - 1 + 1 = c.length := Nat.succ_pred_eq_of_pos length_pos
  simp [this, h]
#align composition.index_exists Composition.index_exists

/-- `c.index j` is the index of the block in the composition `c` containing `j`. -/
def index (j : Fin n) : Fin c.length :=
  ⟨Nat.find (c.index_exists j.2), (Nat.find_spec (c.index_exists j.2)).2⟩
#align composition.index Composition.index

theorem lt_sizeUpTo_index_succ (j : Fin n) : (j : ℕ) < c.sizeUpTo (c.index j).succ :=
  (Nat.find_spec (c.index_exists j.2)).1
#align composition.lt_size_up_to_index_succ Composition.lt_sizeUpTo_index_succ

theorem sizeUpTo_index_le (j : Fin n) : c.sizeUpTo (c.index j) ≤ j := by
  by_contra H
  set i := c.index j
  push_neg at H
  have i_pos : (0 : ℕ) < i := by
    by_contra! i_pos
    revert H
    simp [nonpos_iff_eq_zero.1 i_pos, c.sizeUpTo_zero]
  let i₁ := (i : ℕ).pred
  have i₁_lt_i : i₁ < i := Nat.pred_lt (ne_of_gt i_pos)
  have i₁_succ : i₁ + 1 = i := Nat.succ_pred_eq_of_pos i_pos
  have := Nat.find_min (c.index_exists j.2) i₁_lt_i
  simp [lt_trans i₁_lt_i (c.index j).2, i₁_succ] at this
  exact Nat.lt_le_asymm H this
#align composition.size_up_to_index_le Composition.sizeUpTo_index_le

/-- Mapping an element `j` of `Fin n` to the element in the block containing it, identified with
`Fin (c.blocks_fun (c.index j))` through the canonical increasing bijection. -/
def invEmbedding (j : Fin n) : Fin (c.blocksFun (c.index j)) :=
  ⟨j - c.sizeUpTo (c.index j), by
    rw [tsub_lt_iff_right, add_comm, ← sizeUpTo_succ']
    · exact lt_sizeUpTo_index_succ _ _
    · exact sizeUpTo_index_le _ _⟩
#align composition.inv_embedding Composition.invEmbedding

@[simp]
theorem coe_invEmbedding (j : Fin n) : (c.invEmbedding j : ℕ) = j - c.sizeUpTo (c.index j) :=
  rfl
#align composition.coe_inv_embedding Composition.coe_invEmbedding

theorem embedding_comp_inv (j : Fin n) : c.embedding (c.index j) (c.invEmbedding j) = j := by
  rw [Fin.ext_iff]
  apply add_tsub_cancel_of_le (c.sizeUpTo_index_le j)
#align composition.embedding_comp_inv Composition.embedding_comp_inv

theorem mem_range_embedding_iff {j : Fin n} {i : Fin c.length} :
    j ∈ Set.range (c.embedding i) ↔ c.sizeUpTo i ≤ j ∧ (j : ℕ) < c.sizeUpTo (i : ℕ).succ := by
  constructor
  · intro h
    rcases Set.mem_range.2 h with ⟨k, hk⟩
    rw [Fin.ext_iff] at hk
    dsimp at hk
    rw [← hk]
    simp [sizeUpTo_succ', k.is_lt]
  · intro h
    apply Set.mem_range.2
    refine ⟨⟨j - c.sizeUpTo i, ?_⟩, ?_⟩
    · rw [tsub_lt_iff_left, ← sizeUpTo_succ']
      · exact h.2
      · exact h.1
    · rw [Fin.ext_iff]
      exact add_tsub_cancel_of_le h.1
#align composition.mem_range_embedding_iff Composition.mem_range_embedding_iff

/-- The embeddings of different blocks of a composition are disjoint. -/
theorem disjoint_range {i₁ i₂ : Fin c.length} (h : i₁ ≠ i₂) :
    Disjoint (Set.range (c.embedding i₁)) (Set.range (c.embedding i₂)) := by
  classical
    wlog h' : i₁ < i₂
    · exact (this c h.symm (h.lt_or_lt.resolve_left h')).symm
    by_contra d
    obtain ⟨x, hx₁, hx₂⟩ :
      ∃ x : Fin n, x ∈ Set.range (c.embedding i₁) ∧ x ∈ Set.range (c.embedding i₂) :=
      Set.not_disjoint_iff.1 d
    have A : (i₁ : ℕ).succ ≤ i₂ := Nat.succ_le_of_lt h'
    apply lt_irrefl (x : ℕ)
    calc
      (x : ℕ) < c.sizeUpTo (i₁ : ℕ).succ := (c.mem_range_embedding_iff.1 hx₁).2
      _ ≤ c.sizeUpTo (i₂ : ℕ) := monotone_sum_take _ A
      _ ≤ x := (c.mem_range_embedding_iff.1 hx₂).1
#align composition.disjoint_range Composition.disjoint_range

theorem mem_range_embedding (j : Fin n) : j ∈ Set.range (c.embedding (c.index j)) := by
  have : c.embedding (c.index j) (c.invEmbedding j) ∈ Set.range (c.embedding (c.index j)) :=
    Set.mem_range_self _
  rwa [c.embedding_comp_inv j] at this
#align composition.mem_range_embedding Composition.mem_range_embedding

theorem mem_range_embedding_iff' {j : Fin n} {i : Fin c.length} :
    j ∈ Set.range (c.embedding i) ↔ i = c.index j := by
  constructor
  · rw [← not_imp_not]
    intro h
    exact Set.disjoint_right.1 (c.disjoint_range h) (c.mem_range_embedding j)
  · intro h
    rw [h]
    exact c.mem_range_embedding j
#align composition.mem_range_embedding_iff' Composition.mem_range_embedding_iff'

theorem index_embedding (i : Fin c.length) (j : Fin (c.blocksFun i)) :
    c.index (c.embedding i j) = i := by
  symm
  rw [← mem_range_embedding_iff']
  apply Set.mem_range_self
#align composition.index_embedding Composition.index_embedding

theorem invEmbedding_comp (i : Fin c.length) (j : Fin (c.blocksFun i)) :
    (c.invEmbedding (c.embedding i j) : ℕ) = j := by
  simp_rw [coe_invEmbedding, index_embedding, coe_embedding, add_tsub_cancel_left]
#align composition.inv_embedding_comp Composition.invEmbedding_comp

/-- Equivalence between the disjoint union of the blocks (each of them seen as
`Fin (c.blocks_fun i)`) with `Fin n`. -/
def blocksFinEquiv : (Σi : Fin c.length, Fin (c.blocksFun i)) ≃ Fin n where
  toFun x := c.embedding x.1 x.2
  invFun j := ⟨c.index j, c.invEmbedding j⟩
  left_inv x := by
    rcases x with ⟨i, y⟩
    dsimp
    congr; · exact c.index_embedding _ _
    rw [Fin.heq_ext_iff]
    · exact c.invEmbedding_comp _ _
    · rw [c.index_embedding]
  right_inv j := c.embedding_comp_inv j
#align composition.blocks_fin_equiv Composition.blocksFinEquiv

theorem blocksFun_congr {n₁ n₂ : ℕ} (c₁ : Composition n₁) (c₂ : Composition n₂) (i₁ : Fin c₁.length)
    (i₂ : Fin c₂.length) (hn : n₁ = n₂) (hc : c₁.blocks = c₂.blocks) (hi : (i₁ : ℕ) = i₂) :
    c₁.blocksFun i₁ = c₂.blocksFun i₂ := by
  cases hn
  rw [← Composition.ext_iff] at hc
  cases hc
  congr
  rwa [Fin.ext_iff]
#align composition.blocks_fun_congr Composition.blocksFun_congr

/-- Two compositions (possibly of different integers) coincide if and only if they have the
same sequence of blocks. -/
theorem sigma_eq_iff_blocks_eq {c : Σn, Composition n} {c' : Σn, Composition n} :
    c = c' ↔ c.2.blocks = c'.2.blocks := by
  refine ⟨fun H => by rw [H], fun H => ?_⟩
  rcases c with ⟨n, c⟩
  rcases c' with ⟨n', c'⟩
  have : n = n' := by rw [← c.blocks_sum, ← c'.blocks_sum, H]
  induction this
  congr
  ext1
  exact H
#align composition.sigma_eq_iff_blocks_eq Composition.sigma_eq_iff_blocks_eq

/-! ### The composition `Composition.ones` -/


/-- The composition made of blocks all of size `1`. -/
def ones (n : ℕ) : Composition n :=
  ⟨replicate n (1 : ℕ), fun {i} hi => by simp [List.eq_of_mem_replicate hi], by simp⟩
#align composition.ones Composition.ones

instance {n : ℕ} : Inhabited (Composition n) :=
  ⟨Composition.ones n⟩

@[simp]
theorem ones_length (n : ℕ) : (ones n).length = n :=
  List.length_replicate n 1
#align composition.ones_length Composition.ones_length

@[simp]
theorem ones_blocks (n : ℕ) : (ones n).blocks = replicate n (1 : ℕ) :=
  rfl
#align composition.ones_blocks Composition.ones_blocks

@[simp]
theorem ones_blocksFun (n : ℕ) (i : Fin (ones n).length) : (ones n).blocksFun i = 1 := by
  simp only [blocksFun, ones, blocks, i.2, List.get_replicate]
#align composition.ones_blocks_fun Composition.ones_blocksFun

@[simp]
theorem ones_sizeUpTo (n : ℕ) (i : ℕ) : (ones n).sizeUpTo i = min i n := by
  simp [sizeUpTo, ones_blocks, take_replicate]
#align composition.ones_size_up_to Composition.ones_sizeUpTo

@[simp]
theorem ones_embedding (i : Fin (ones n).length) (h : 0 < (ones n).blocksFun i) :
    (ones n).embedding i ⟨0, h⟩ = ⟨i, lt_of_lt_of_le i.2 (ones n).length_le⟩ := by
  ext
  simpa using i.2.le
#align composition.ones_embedding Composition.ones_embedding

theorem eq_ones_iff {c : Composition n} : c = ones n ↔ ∀ i ∈ c.blocks, i = 1 := by
  constructor
  · rintro rfl
    exact fun i => eq_of_mem_replicate
  · intro H
    ext1
    have A : c.blocks = replicate c.blocks.length 1 := eq_replicate_of_mem H
    have : c.blocks.length = n := by
      conv_rhs => rw [← c.blocks_sum, A]
      simp
    rw [A, this, ones_blocks]
#align composition.eq_ones_iff Composition.eq_ones_iff

theorem ne_ones_iff {c : Composition n} : c ≠ ones n ↔ ∃ i ∈ c.blocks, 1 < i := by
  refine (not_congr eq_ones_iff).trans ?_
  have : ∀ j ∈ c.blocks, j = 1 ↔ j ≤ 1 := fun j hj => by simp [le_antisymm_iff, c.one_le_blocks hj]
  simp (config := { contextual := true }) [this]
#align composition.ne_ones_iff Composition.ne_ones_iff

theorem eq_ones_iff_length {c : Composition n} : c = ones n ↔ c.length = n := by
  constructor
  · rintro rfl
    exact ones_length n
  · contrapose
    intro H length_n
    apply lt_irrefl n
    calc
      n = ∑ i : Fin c.length, 1 := by simp [length_n]
      _ < ∑ i : Fin c.length, c.blocksFun i := by
        {
        obtain ⟨i, hi, i_blocks⟩ : ∃ i ∈ c.blocks, 1 < i := ne_ones_iff.1 H
        rw [← ofFn_blocksFun, mem_ofFn c.blocksFun, Set.mem_range] at hi
        obtain ⟨j : Fin c.length, hj : c.blocksFun j = i⟩ := hi
        rw [← hj] at i_blocks
        exact Finset.sum_lt_sum (fun i _ => one_le_blocksFun c i) ⟨j, Finset.mem_univ _, i_blocks⟩
        }
      _ = n := c.sum_blocksFun
#align composition.eq_ones_iff_length Composition.eq_ones_iff_length

theorem eq_ones_iff_le_length {c : Composition n} : c = ones n ↔ n ≤ c.length := by
  simp [eq_ones_iff_length, le_antisymm_iff, c.length_le]
#align composition.eq_ones_iff_le_length Composition.eq_ones_iff_le_length

/-! ### The composition `Composition.single` -/

/-- The composition made of a single block of size `n`. -/
def single (n : ℕ) (h : 0 < n) : Composition n :=
  ⟨[n], by simp [h], by simp⟩
#align composition.single Composition.single

@[simp]
theorem single_length {n : ℕ} (h : 0 < n) : (single n h).length = 1 :=
  rfl
#align composition.single_length Composition.single_length

@[simp]
theorem single_blocks {n : ℕ} (h : 0 < n) : (single n h).blocks = [n] :=
  rfl
#align composition.single_blocks Composition.single_blocks

@[simp]
theorem single_blocksFun {n : ℕ} (h : 0 < n) (i : Fin (single n h).length) :
    (single n h).blocksFun i = n := by simp [blocksFun, single, blocks, i.2]
#align composition.single_blocks_fun Composition.single_blocksFun

@[simp]
theorem single_embedding {n : ℕ} (h : 0 < n) (i : Fin n) :
    ((single n h).embedding (0 : Fin 1)) i = i := by
  ext
  simp
#align composition.single_embedding Composition.single_embedding

theorem eq_single_iff_length {n : ℕ} (h : 0 < n) {c : Composition n} :
    c = single n h ↔ c.length = 1 := by
  constructor
  · intro H
    rw [H]
    exact single_length h
  · intro H
    ext1
    have A : c.blocks.length = 1 := H ▸ c.blocks_length
    have B : c.blocks.sum = n := c.blocks_sum
    rw [eq_cons_of_length_one A] at B ⊢
    simpa [single_blocks] using B
#align composition.eq_single_iff_length Composition.eq_single_iff_length

theorem ne_single_iff {n : ℕ} (hn : 0 < n) {c : Composition n} :
    c ≠ single n hn ↔ ∀ i, c.blocksFun i < n := by
  rw [← not_iff_not]
  push_neg
  constructor
  · rintro rfl
    exact ⟨⟨0, by simp⟩, by simp⟩
  · rintro ⟨i, hi⟩
    rw [eq_single_iff_length]
    have : ∀ j : Fin c.length, j = i := by
      intro j
      by_contra ji
      apply lt_irrefl (∑ k, c.blocksFun k)
      calc
        ∑ k, c.blocksFun k ≤ c.blocksFun i := by simp only [c.sum_blocksFun, hi]
        _ < ∑ k, c.blocksFun k :=
          Finset.single_lt_sum ji (Finset.mem_univ _) (Finset.mem_univ _) (c.one_le_blocksFun j)
            fun _ _ _ => zero_le _

    simpa using Fintype.card_eq_one_of_forall_eq this
#align composition.ne_single_iff Composition.ne_single_iff

end Composition

/-!
### Splitting a list

Given a list of length `n` and a composition `c` of `n`, one can split `l` into `c.length` sublists
of respective lengths `c.blocks_fun 0`, ..., `c.blocks_fun (c.length-1)`. This is inverse to the
join operation.
-/


namespace List

variable {α : Type*}

/-- Auxiliary for `List.splitWrtComposition`. -/
def splitWrtCompositionAux : List α → List ℕ → List (List α)
  | _, [] => []
  | l, n::ns =>
    let (l₁, l₂) := l.splitAt n
    l₁::splitWrtCompositionAux l₂ ns
#align list.split_wrt_composition_aux List.splitWrtCompositionAux

/-- Given a list of length `n` and a composition `[i₁, ..., iₖ]` of `n`, split `l` into a list of
`k` lists corresponding to the blocks of the composition, of respective lengths `i₁`, ..., `iₖ`.
This makes sense mostly when `n = l.length`, but this is not necessary for the definition. -/
def splitWrtComposition (l : List α) (c : Composition n) : List (List α) :=
  splitWrtCompositionAux l c.blocks
#align list.split_wrt_composition List.splitWrtComposition

-- Porting note: can't refer to subeqn in Lean 4 this way, and seems to definitionally simp
--attribute [local simp] splitWrtCompositionAux.equations._eqn_1

@[local simp]
theorem splitWrtCompositionAux_cons (l : List α) (n ns) :
    l.splitWrtCompositionAux (n::ns) = take n l::(drop n l).splitWrtCompositionAux ns := by
  simp [splitWrtCompositionAux]
#align list.split_wrt_composition_aux_cons List.splitWrtCompositionAux_cons

theorem length_splitWrtCompositionAux (l : List α) (ns) :
    length (l.splitWrtCompositionAux ns) = ns.length := by
    induction ns generalizing l
    · simp [splitWrtCompositionAux, *]
    · simp [*]
#align list.length_split_wrt_composition_aux List.length_splitWrtCompositionAux

/-- When one splits a list along a composition `c`, the number of sublists thus created is
`c.length`. -/
@[simp]
theorem length_splitWrtComposition (l : List α) (c : Composition n) :
    length (l.splitWrtComposition c) = c.length :=
  length_splitWrtCompositionAux _ _
#align list.length_split_wrt_composition List.length_splitWrtComposition


theorem map_length_splitWrtCompositionAux {ns : List ℕ} :
    ∀ {l : List α}, ns.sum ≤ l.length → map length (l.splitWrtCompositionAux ns) = ns := by
  induction' ns with n ns IH <;> intro l h <;> simp at h
  · simp [splitWrtCompositionAux]
  have := le_trans (Nat.le_add_right _ _) h
  simp only [splitWrtCompositionAux_cons, this]; dsimp
  rw [length_take, IH] <;> simp [length_drop]
  · assumption
  · exact le_tsub_of_add_le_left h
#align list.map_length_split_wrt_composition_aux List.map_length_splitWrtCompositionAux

/-- When one splits a list along a composition `c`, the lengths of the sublists thus created are
given by the block sizes in `c`. -/
theorem map_length_splitWrtComposition (l : List α) (c : Composition l.length) :
    map length (l.splitWrtComposition c) = c.blocks :=
  map_length_splitWrtCompositionAux (le_of_eq c.blocks_sum)
#align list.map_length_split_wrt_composition List.map_length_splitWrtComposition

theorem length_pos_of_mem_splitWrtComposition {l l' : List α} {c : Composition l.length}
    (h : l' ∈ l.splitWrtComposition c) : 0 < length l' := by
  have : l'.length ∈ (l.splitWrtComposition c).map List.length :=
    List.mem_map_of_mem List.length h
  rw [map_length_splitWrtComposition] at this
  exact c.blocks_pos this
#align list.length_pos_of_mem_split_wrt_composition List.length_pos_of_mem_splitWrtComposition

theorem sum_take_map_length_splitWrtComposition (l : List α) (c : Composition l.length) (i : ℕ) :
    (((l.splitWrtComposition c).map length).take i).sum = c.sizeUpTo i := by
  congr
  exact map_length_splitWrtComposition l c
#align list.sum_take_map_length_split_wrt_composition List.sum_take_map_length_splitWrtComposition

theorem get_splitWrtCompositionAux (l : List α) (ns : List ℕ) {i : ℕ} (hi) :
    (l.splitWrtCompositionAux ns).get ⟨i, hi⟩  =
      (l.take (ns.take (i + 1)).sum).drop (ns.take i).sum := by
  induction' ns with n ns IH generalizing l i
  · cases hi
  cases' i with i
  · rw [Nat.add_zero, List.take_zero, sum_nil]
    simpa using get_mk_zero hi
  · simp only [splitWrtCompositionAux, get_cons_succ, IH, take,
        sum_cons, Nat.add_eq, add_zero, splitAt_eq_take_drop, drop_take, drop_drop]
    rw [add_comm (sum _) n, Nat.add_sub_add_left]
#align list.nth_le_split_wrt_composition_aux List.get_splitWrtCompositionAux

/-- The `i`-th sublist in the splitting of a list `l` along a composition `c`, is the slice of `l`
between the indices `c.sizeUpTo i` and `c.sizeUpTo (i+1)`, i.e., the indices in the `i`-th
block of the composition. -/
theorem get_splitWrtComposition' (l : List α) (c : Composition n) {i : ℕ}
    (hi : i < (l.splitWrtComposition c).length) :
    (l.splitWrtComposition c).get ⟨i, hi⟩ = (l.take (c.sizeUpTo (i + 1))).drop (c.sizeUpTo i) :=
  get_splitWrtCompositionAux _ _ _
#align list.nth_le_split_wrt_composition List.get_splitWrtComposition'

-- Porting note: restatement of `get_splitWrtComposition`
theorem get_splitWrtComposition (l : List α) (c : Composition n)
    (i : Fin (l.splitWrtComposition c).length) :
    get (l.splitWrtComposition c) i = (l.take (c.sizeUpTo (i + 1))).drop (c.sizeUpTo i) :=
  get_splitWrtComposition' _ _ _

theorem join_splitWrtCompositionAux {ns : List ℕ} :
    ∀ {l : List α}, ns.sum = l.length → (l.splitWrtCompositionAux ns).join = l := by
  induction' ns with n ns IH <;> intro l h <;> simp at h
  · exact (length_eq_zero.1 h.symm).symm
  simp only [splitWrtCompositionAux_cons]; dsimp
  rw [IH]
  · simp
  · rw [length_drop, ← h, add_tsub_cancel_left]
#align list.join_split_wrt_composition_aux List.join_splitWrtCompositionAux

/-- If one splits a list along a composition, and then joins the sublists, one gets back the
original list. -/
@[simp]
theorem join_splitWrtComposition (l : List α) (c : Composition l.length) :
    (l.splitWrtComposition c).join = l :=
  join_splitWrtCompositionAux c.blocks_sum
#align list.join_split_wrt_composition List.join_splitWrtComposition

/-- If one joins a list of lists and then splits the join along the right composition, one gets
back the original list of lists. -/
@[simp]
theorem splitWrtComposition_join (L : List (List α)) (c : Composition L.join.length)
    (h : map length L = c.blocks) : splitWrtComposition (join L) c = L := by
  simp only [eq_self_iff_true, and_self_iff, eq_iff_join_eq, join_splitWrtComposition,
    map_length_splitWrtComposition, h]
#align list.split_wrt_composition_join List.splitWrtComposition_join

end List

/-!
### Compositions as sets

Combinatorial viewpoints on compositions, seen as finite subsets of `Fin (n+1)` containing `0` and
`n`, where the points of the set (other than `n`) correspond to the leftmost points of each block.
-/


/-- Bijection between compositions of `n` and subsets of `{0, ..., n-2}`, defined by
considering the restriction of the subset to `{1, ..., n-1}` and shifting to the left by one. -/
def compositionAsSetEquiv (n : ℕ) : CompositionAsSet n ≃ Finset (Fin (n - 1)) where
  toFun c :=
    { i : Fin (n - 1) |
        (⟨1 + (i : ℕ), by
              apply (add_lt_add_left i.is_lt 1).trans_le
              rw [Nat.succ_eq_add_one, add_comm]
              exact add_le_add (Nat.sub_le n 1) (le_refl 1)⟩ :
            Fin n.succ) ∈
          c.boundaries }.toFinset
  invFun s :=
    { boundaries :=
        { i : Fin n.succ |
            i = 0 ∨ i = Fin.last n ∨ ∃ (j : Fin (n - 1)) (_hj : j ∈ s), (i : ℕ) = j + 1 }.toFinset
      zero_mem := by simp
      getLast_mem := by simp }
  left_inv := by
    intro c
    ext i
    simp only [add_comm, Set.toFinset_setOf, Finset.mem_univ,
     forall_true_left, Finset.mem_filter, true_and, exists_prop]
    constructor
    · rintro (rfl | rfl | ⟨j, hj1, hj2⟩)
      · exact c.zero_mem
      · exact c.getLast_mem
      · convert hj1
    · simp only [or_iff_not_imp_left]
      intro i_mem i_ne_zero i_ne_last
      simp? [Fin.ext_iff] at i_ne_zero i_ne_last says
        simp only [Nat.succ_eq_add_one, Fin.ext_iff, Fin.val_zero, Fin.val_last]
          at i_ne_zero i_ne_last
      have A : (1 + (i - 1) : ℕ) = (i : ℕ) := by
        rw [add_comm]
        exact Nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr i_ne_zero)
      refine ⟨⟨i - 1, ?_⟩, ?_, ?_⟩
      · have : (i : ℕ) < n + 1 := i.2
        simp? [Nat.lt_succ_iff_lt_or_eq, i_ne_last] at this says
          simp only [Nat.succ_eq_add_one, Nat.lt_succ_iff_lt_or_eq, i_ne_last, or_false] at this
        exact Nat.pred_lt_pred i_ne_zero this
      · convert i_mem
        simp only [ge_iff_le]
        rwa [add_comm]
      · simp only [ge_iff_le]
        symm
        rwa [add_comm]
  right_inv := by
    intro s
    ext i
    have : 1 + (i : ℕ) ≠ n := by
      apply ne_of_lt
      convert add_lt_add_left i.is_lt 1
      rw [add_comm]
      apply (Nat.succ_pred_eq_of_pos _).symm
      exact (zero_le i.val).trans_lt (i.2.trans_le (Nat.sub_le n 1))
    simp only [add_comm, Fin.ext_iff, Fin.val_zero, Fin.val_last, exists_prop, Set.toFinset_setOf,
      Finset.mem_univ, forall_true_left, Finset.mem_filter, add_eq_zero_iff, and_false,
      add_left_inj, false_or, true_and]
    erw [Set.mem_setOf_eq]
    simp [this, false_or_iff, add_right_inj, add_eq_zero_iff, one_ne_zero, false_and_iff,
      Fin.val_mk]
    constructor
    · intro h
      cases' h with n h
      · rw [add_comm] at this
        contradiction
      · cases' h with w h; cases' h with h₁ h₂
        rw [← Fin.ext_iff] at h₂
        rwa [h₂]
    · intro h
      apply Or.inr
      use i, h
#align composition_as_set_equiv compositionAsSetEquiv

instance compositionAsSetFintype (n : ℕ) : Fintype (CompositionAsSet n) :=
  Fintype.ofEquiv _ (compositionAsSetEquiv n).symm
#align composition_as_set_fintype compositionAsSetFintype

theorem compositionAsSet_card (n : ℕ) : Fintype.card (CompositionAsSet n) = 2 ^ (n - 1) := by
  have : Fintype.card (Finset (Fin (n - 1))) = 2 ^ (n - 1) := by simp
  rw [← this]
  exact Fintype.card_congr (compositionAsSetEquiv n)
#align composition_as_set_card compositionAsSet_card

namespace CompositionAsSet

variable (c : CompositionAsSet n)

theorem boundaries_nonempty : c.boundaries.Nonempty :=
  ⟨0, c.zero_mem⟩
#align composition_as_set.boundaries_nonempty CompositionAsSet.boundaries_nonempty

theorem card_boundaries_pos : 0 < Finset.card c.boundaries :=
  Finset.card_pos.mpr c.boundaries_nonempty
#align composition_as_set.card_boundaries_pos CompositionAsSet.card_boundaries_pos

/-- Number of blocks in a `CompositionAsSet`. -/
def length : ℕ :=
  Finset.card c.boundaries - 1
#align composition_as_set.length CompositionAsSet.length

theorem card_boundaries_eq_succ_length : c.boundaries.card = c.length + 1 :=
  (tsub_eq_iff_eq_add_of_le (Nat.succ_le_of_lt c.card_boundaries_pos)).mp rfl
#align composition_as_set.card_boundaries_eq_succ_length CompositionAsSet.card_boundaries_eq_succ_length

theorem length_lt_card_boundaries : c.length < c.boundaries.card := by
  rw [c.card_boundaries_eq_succ_length]
  exact lt_add_one _
#align composition_as_set.length_lt_card_boundaries CompositionAsSet.length_lt_card_boundaries

theorem lt_length (i : Fin c.length) : (i : ℕ) + 1 < c.boundaries.card :=
  lt_tsub_iff_right.mp i.2
#align composition_as_set.lt_length CompositionAsSet.lt_length

theorem lt_length' (i : Fin c.length) : (i : ℕ) < c.boundaries.card :=
  lt_of_le_of_lt (Nat.le_succ i) (c.lt_length i)
#align composition_as_set.lt_length' CompositionAsSet.lt_length'

/-- Canonical increasing bijection from `Fin c.boundaries.card` to `c.boundaries`. -/
def boundary : Fin c.boundaries.card ↪o Fin (n + 1) :=
  c.boundaries.orderEmbOfFin rfl
#align composition_as_set.boundary CompositionAsSet.boundary

@[simp]
theorem boundary_zero : (c.boundary ⟨0, c.card_boundaries_pos⟩ : Fin (n + 1)) = 0 := by
  rw [boundary, Finset.orderEmbOfFin_zero rfl c.card_boundaries_pos]
  exact le_antisymm (Finset.min'_le _ _ c.zero_mem) (Fin.zero_le _)
#align composition_as_set.boundary_zero CompositionAsSet.boundary_zero

@[simp]
theorem boundary_length : c.boundary ⟨c.length, c.length_lt_card_boundaries⟩ = Fin.last n := by
  convert Finset.orderEmbOfFin_last rfl c.card_boundaries_pos
  exact le_antisymm (Finset.le_max' _ _ c.getLast_mem) (Fin.le_last _)
#align composition_as_set.boundary_length CompositionAsSet.boundary_length

/-- Size of the `i`-th block in a `CompositionAsSet`, seen as a function on `Fin c.length`. -/
def blocksFun (i : Fin c.length) : ℕ :=
  c.boundary ⟨(i : ℕ) + 1, c.lt_length i⟩ - c.boundary ⟨i, c.lt_length' i⟩
#align composition_as_set.blocks_fun CompositionAsSet.blocksFun

theorem blocksFun_pos (i : Fin c.length) : 0 < c.blocksFun i :=
  haveI : (⟨i, c.lt_length' i⟩ : Fin c.boundaries.card) < ⟨i + 1, c.lt_length i⟩ :=
    Nat.lt_succ_self _
  lt_tsub_iff_left.mpr ((c.boundaries.orderEmbOfFin rfl).strictMono this)
#align composition_as_set.blocks_fun_pos CompositionAsSet.blocksFun_pos

/-- List of the sizes of the blocks in a `CompositionAsSet`. -/
def blocks (c : CompositionAsSet n) : List ℕ :=
  ofFn c.blocksFun
#align composition_as_set.blocks CompositionAsSet.blocks

@[simp]
theorem blocks_length : c.blocks.length = c.length :=
  length_ofFn _
#align composition_as_set.blocks_length CompositionAsSet.blocks_length

theorem blocks_partial_sum {i : ℕ} (h : i < c.boundaries.card) :
    (c.blocks.take i).sum = c.boundary ⟨i, h⟩ := by
  induction' i with i IH
  · simp
  have A : i < c.blocks.length := by
    rw [c.card_boundaries_eq_succ_length] at h
    simp [blocks, Nat.lt_of_succ_lt_succ h]
  have B : i < c.boundaries.card := lt_of_lt_of_le A (by simp [blocks, length, Nat.sub_le])
  rw [sum_take_succ _ _ A, IH B]
  simp [blocks, blocksFun, get_ofFn]
#align composition_as_set.blocks_partial_sum CompositionAsSet.blocks_partial_sum

theorem mem_boundaries_iff_exists_blocks_sum_take_eq {j : Fin (n + 1)} :
    j ∈ c.boundaries ↔ ∃ i < c.boundaries.card, (c.blocks.take i).sum = j := by
  constructor
  · intro hj
    rcases (c.boundaries.orderIsoOfFin rfl).surjective ⟨j, hj⟩ with ⟨i, hi⟩
    rw [Subtype.ext_iff, Subtype.coe_mk] at hi
    refine ⟨i.1, i.2, ?_⟩
    dsimp at hi
    rw [← hi, c.blocks_partial_sum i.2]
    rfl
  · rintro ⟨i, hi, H⟩
    convert (c.boundaries.orderIsoOfFin rfl ⟨i, hi⟩).2
    have : c.boundary ⟨i, hi⟩ = j := by rwa [Fin.ext_iff, ← c.blocks_partial_sum hi]
    exact this.symm
#align composition_as_set.mem_boundaries_iff_exists_blocks_sum_take_eq CompositionAsSet.mem_boundaries_iff_exists_blocks_sum_take_eq

theorem blocks_sum : c.blocks.sum = n := by
  have : c.blocks.take c.length = c.blocks := take_all_of_le (by simp [blocks])
  rw [← this, c.blocks_partial_sum c.length_lt_card_boundaries, c.boundary_length]
  rfl
#align composition_as_set.blocks_sum CompositionAsSet.blocks_sum

/-- Associating a `Composition n` to a `CompositionAsSet n`, by registering the sizes of the
blocks as a list of positive integers. -/
def toComposition : Composition n where
  blocks := c.blocks
  blocks_pos := by simp only [blocks, forall_mem_ofFn_iff, blocksFun_pos c, forall_true_iff]
  blocks_sum := c.blocks_sum
#align composition_as_set.to_composition CompositionAsSet.toComposition

end CompositionAsSet

/-!
### Equivalence between compositions and compositions as sets

In this section, we explain how to go back and forth between a `Composition` and a
`CompositionAsSet`, by showing that their `blocks` and `length` and `boundaries` correspond to
each other, and construct an equivalence between them called `compositionEquiv`.
-/


@[simp]
theorem Composition.toCompositionAsSet_length (c : Composition n) :
    c.toCompositionAsSet.length = c.length := by
  simp [Composition.toCompositionAsSet, CompositionAsSet.length, c.card_boundaries_eq_succ_length]
#align composition.to_composition_as_set_length Composition.toCompositionAsSet_length

@[simp]
theorem CompositionAsSet.toComposition_length (c : CompositionAsSet n) :
    c.toComposition.length = c.length := by
  simp [CompositionAsSet.toComposition, Composition.length, Composition.blocks]
#align composition_as_set.to_composition_length CompositionAsSet.toComposition_length

@[simp]
theorem Composition.toCompositionAsSet_blocks (c : Composition n) :
    c.toCompositionAsSet.blocks = c.blocks := by
  let d := c.toCompositionAsSet
  change d.blocks = c.blocks
  have length_eq : d.blocks.length = c.blocks.length := by simp [d, blocks_length]
  suffices H : ∀ i ≤ d.blocks.length, (d.blocks.take i).sum = (c.blocks.take i).sum from
    eq_of_sum_take_eq length_eq H
  intro i hi
  have i_lt : i < d.boundaries.card := by
    -- Porting note: relied on `convert` unfolding definitions, switched to using a `simpa`
    simpa [CompositionAsSet.blocks, length_ofFn, Nat.succ_eq_add_one,
      d.card_boundaries_eq_succ_length] using Nat.lt_succ_iff.2 hi
  have i_lt' : i < c.boundaries.card := i_lt
  have i_lt'' : i < c.length + 1 := by rwa [c.card_boundaries_eq_succ_length] at i_lt'
  have A :
    d.boundaries.orderEmbOfFin rfl ⟨i, i_lt⟩ =
      c.boundaries.orderEmbOfFin c.card_boundaries_eq_succ_length ⟨i, i_lt''⟩ :=
    rfl
  have B : c.sizeUpTo i = c.boundary ⟨i, i_lt''⟩ := rfl
  rw [d.blocks_partial_sum i_lt, CompositionAsSet.boundary, ← Composition.sizeUpTo, B, A,
    c.orderEmbOfFin_boundaries]
#align composition.to_composition_as_set_blocks Composition.toCompositionAsSet_blocks

@[simp]
theorem CompositionAsSet.toComposition_blocks (c : CompositionAsSet n) :
    c.toComposition.blocks = c.blocks :=
  rfl
#align composition_as_set.to_composition_blocks CompositionAsSet.toComposition_blocks

@[simp]
theorem CompositionAsSet.toComposition_boundaries (c : CompositionAsSet n) :
    c.toComposition.boundaries = c.boundaries := by
  ext j
  simp only [c.mem_boundaries_iff_exists_blocks_sum_take_eq, Composition.boundaries, Finset.mem_map]
  constructor
  · rintro ⟨i, _, hi⟩
    refine ⟨i.1, ?_, ?_⟩
    · simpa [c.card_boundaries_eq_succ_length] using i.2
    · simp [Composition.boundary, Composition.sizeUpTo, ← hi]
  · rintro ⟨i, i_lt, hi⟩
    refine ⟨i, by simp, ?_⟩
    rw [c.card_boundaries_eq_succ_length] at i_lt
    simp [Composition.boundary, Nat.mod_eq_of_lt i_lt, Composition.sizeUpTo, hi]
#align composition_as_set.to_composition_boundaries CompositionAsSet.toComposition_boundaries

@[simp]
theorem Composition.toCompositionAsSet_boundaries (c : Composition n) :
    c.toCompositionAsSet.boundaries = c.boundaries :=
  rfl
#align composition.to_composition_as_set_boundaries Composition.toCompositionAsSet_boundaries

/-- Equivalence between `Composition n` and `CompositionAsSet n`. -/
def compositionEquiv (n : ℕ) : Composition n ≃ CompositionAsSet n where
  toFun c := c.toCompositionAsSet
  invFun c := c.toComposition
  left_inv c := by
    ext1
    exact c.toCompositionAsSet_blocks
  right_inv c := by
    ext1
    exact c.toComposition_boundaries
#align composition_equiv compositionEquiv

instance compositionFintype (n : ℕ) : Fintype (Composition n) :=
  Fintype.ofEquiv _ (compositionEquiv n).symm
#align composition_fintype compositionFintype

theorem composition_card (n : ℕ) : Fintype.card (Composition n) = 2 ^ (n - 1) := by
  rw [← compositionAsSet_card n]
  exact Fintype.card_congr (compositionEquiv n)
#align composition_card composition_card
