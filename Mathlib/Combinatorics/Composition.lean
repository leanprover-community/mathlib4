/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Fin

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

open BigOperators

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
@[reducible]
def length : ℕ :=
  c.blocks.length
#align composition.length Composition.length

theorem blocks_length : c.blocks.length = c.length :=
  rfl
#align composition.blocks_length Composition.blocks_length

-- porting note: TODO, refactor to `List.get`
set_option linter.deprecated false in
/-- The blocks of a composition, seen as a function on `Fin c.length`. When composing analytic
functions using compositions, this is the main player. -/
def blocksFun : Fin c.length → ℕ := fun i => nthLe c.blocks i i.2
#align composition.blocks_fun Composition.blocksFun

-- porting note: TODO, refactor to `List.get`
set_option linter.deprecated false in
theorem ofFn_blocksFun : ofFn c.blocksFun = c.blocks :=
  ofFn_nthLe _
#align composition.of_fn_blocks_fun Composition.ofFn_blocksFun

theorem sum_blocksFun : ∑ i, c.blocksFun i = n := by
  conv_rhs => rw [← c.blocks_sum, ← ofFn_blocksFun, sum_ofFn]
  -- 🎉 no goals
#align composition.sum_blocks_fun Composition.sum_blocksFun

-- porting note: TODO, refactor to `List.get`
set_option linter.deprecated false in
theorem blocksFun_mem_blocks (i : Fin c.length) : c.blocksFun i ∈ c.blocks :=
  nthLe_mem _ _ _
#align composition.blocks_fun_mem_blocks Composition.blocksFun_mem_blocks

@[simp]
theorem one_le_blocks {i : ℕ} (h : i ∈ c.blocks) : 1 ≤ i :=
  c.blocks_pos h
#align composition.one_le_blocks Composition.one_le_blocks

-- porting note: TODO, refactor to `List.get`
set_option linter.deprecated false in
@[simp]
theorem one_le_blocks' {i : ℕ} (h : i < c.length) : 1 ≤ nthLe c.blocks i h :=
  c.one_le_blocks (nthLe_mem (blocks c) i h)
#align composition.one_le_blocks' Composition.one_le_blocks'

-- porting note: TODO, refactor to `List.get`
set_option linter.deprecated false in
@[simp]
theorem blocks_pos' (i : ℕ) (h : i < c.length) : 0 < nthLe c.blocks i h :=
  c.one_le_blocks' h
#align composition.blocks_pos' Composition.blocks_pos'

theorem one_le_blocksFun (i : Fin c.length) : 1 ≤ c.blocksFun i :=
  c.one_le_blocks (c.blocksFun_mem_blocks i)
#align composition.one_le_blocks_fun Composition.one_le_blocksFun

theorem length_le : c.length ≤ n := by
  conv_rhs => rw [← c.blocks_sum]
  -- ⊢ length c ≤ sum c.blocks
  exact length_le_sum_of_one_le _ fun i hi => c.one_le_blocks hi
  -- 🎉 no goals
#align composition.length_le Composition.length_le

theorem length_pos_of_pos (h : 0 < n) : 0 < c.length := by
  apply length_pos_of_sum_pos
  -- ⊢ 0 < sum c.blocks
  convert h
  -- ⊢ sum c.blocks = n
  exact c.blocks_sum
  -- 🎉 no goals
#align composition.length_pos_of_pos Composition.length_pos_of_pos

/-- The sum of the sizes of the blocks in a composition up to `i`. -/
def sizeUpTo (i : ℕ) : ℕ :=
  (c.blocks.take i).sum
#align composition.size_up_to Composition.sizeUpTo

@[simp]
theorem sizeUpTo_zero : c.sizeUpTo 0 = 0 := by simp [sizeUpTo]
                                               -- 🎉 no goals
#align composition.size_up_to_zero Composition.sizeUpTo_zero

theorem sizeUpTo_ofLength_le (i : ℕ) (h : c.length ≤ i) : c.sizeUpTo i = n := by
  dsimp [sizeUpTo]
  -- ⊢ sum (take i c.blocks) = n
  convert c.blocks_sum
  -- ⊢ take i c.blocks = c.blocks
  exact take_all_of_le h
  -- 🎉 no goals
#align composition.size_up_to_of_length_le Composition.sizeUpTo_ofLength_le

@[simp]
theorem sizeUpTo_length : c.sizeUpTo c.length = n :=
  c.sizeUpTo_ofLength_le c.length le_rfl
#align composition.size_up_to_length Composition.sizeUpTo_length

theorem sizeUpTo_le (i : ℕ) : c.sizeUpTo i ≤ n := by
  conv_rhs => rw [← c.blocks_sum, ← sum_take_add_sum_drop _ i]
  -- ⊢ sizeUpTo c i ≤ sum (take i c.blocks) + sum (drop i c.blocks)
  exact Nat.le_add_right _ _
  -- 🎉 no goals
#align composition.size_up_to_le Composition.sizeUpTo_le

theorem sizeUpTo_succ {i : ℕ} (h : i < c.length) :
    c.sizeUpTo (i + 1) = c.sizeUpTo i + c.blocks.nthLe i h := by
  simp only [sizeUpTo]
  -- ⊢ sum (take (i + 1) c.blocks) = sum (take i c.blocks) + nthLe c.blocks i h
  rw [sum_take_succ _ _ h]
  -- 🎉 no goals
#align composition.size_up_to_succ Composition.sizeUpTo_succ

theorem sizeUpTo_succ' (i : Fin c.length) :
    c.sizeUpTo ((i : ℕ) + 1) = c.sizeUpTo i + c.blocksFun i :=
  c.sizeUpTo_succ i.2
#align composition.size_up_to_succ' Composition.sizeUpTo_succ'

theorem sizeUpTo_strict_mono {i : ℕ} (h : i < c.length) : c.sizeUpTo i < c.sizeUpTo (i + 1) := by
  rw [c.sizeUpTo_succ h]
  -- ⊢ sizeUpTo c i < sizeUpTo c i + nthLe c.blocks i h
  simp
  -- 🎉 no goals
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
                                               -- 🎉 no goals
#align composition.boundary_zero Composition.boundary_zero

@[simp]
theorem boundary_last : c.boundary (Fin.last c.length) = Fin.last n := by
  simp [boundary, Fin.ext_iff]
  -- 🎉 no goals
#align composition.boundary_last Composition.boundary_last

/-- The boundaries of a composition, i.e., the leftmost point of all the blocks. We include
a virtual point at the right of the last block, to make for a nice equiv with
`CompositionAsSet n`. -/
def boundaries : Finset (Fin (n + 1)) :=
  Finset.univ.map c.boundary.toEmbedding
#align composition.boundaries Composition.boundaries

theorem card_boundaries_eq_succ_length : c.boundaries.card = c.length + 1 := by simp [boundaries]
                                                                                -- 🎉 no goals
#align composition.card_boundaries_eq_succ_length Composition.card_boundaries_eq_succ_length

/-- To `c : Composition n`, one can associate a `CompositionAsSet n` by registering the leftmost
point of each block, and adding a virtual point at the right of the last block. -/
def toCompositionAsSet : CompositionAsSet n
    where
  boundaries := c.boundaries
  zero_mem := by
    simp only [boundaries, Finset.mem_univ, exists_prop_of_true, Finset.mem_map]
    -- ⊢ ∃ a, True ∧ ↑(boundary c).toEmbedding a = 0
    exact ⟨0, And.intro True.intro rfl⟩
    -- 🎉 no goals
  getLast_mem := by
    simp only [boundaries, Finset.mem_univ, exists_prop_of_true, Finset.mem_map]
    -- ⊢ ∃ a, True ∧ ↑(boundary c).toEmbedding a = Fin.last n
    exact ⟨Fin.last c.length, And.intro True.intro c.boundary_last⟩
    -- 🎉 no goals
#align composition.to_composition_as_set Composition.toCompositionAsSet

/-- The canonical increasing bijection between `Fin (c.length + 1)` and `c.boundaries` is
exactly `c.boundary`. -/
theorem orderEmbOfFin_boundaries :
    c.boundaries.orderEmbOfFin c.card_boundaries_eq_succ_length = c.boundary := by
  refine' (Finset.orderEmbOfFin_unique' _ _).symm
  -- ⊢ ∀ (x : Fin (length c + 1)), ↑(boundary c) x ∈ boundaries c
  exact fun i => (Finset.mem_map' _).2 (Finset.mem_univ _)
  -- 🎉 no goals
#align composition.order_emb_of_fin_boundaries Composition.orderEmbOfFin_boundaries

/-- Embedding the `i`-th block of a composition (identified with `Fin (c.blocks_fun i)`) into
`Fin n` at the relevant position. -/
def embedding (i : Fin c.length) : Fin (c.blocksFun i) ↪o Fin n :=
  (Fin.natAddEmb <| c.sizeUpTo i).trans <|
    Fin.castLEEmb <|
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
In the next definition `index` we use `nat.find` to produce the minimal such index.
-/
theorem index_exists {j : ℕ} (h : j < n) : ∃ i : ℕ, j < c.sizeUpTo i.succ ∧ i < c.length := by
  have n_pos : 0 < n := lt_of_le_of_lt (zero_le j) h
  -- ⊢ ∃ i, j < sizeUpTo c (Nat.succ i) ∧ i < length c
  have : 0 < c.blocks.sum := by rwa [← c.blocks_sum] at n_pos
  -- ⊢ ∃ i, j < sizeUpTo c (Nat.succ i) ∧ i < length c
  have length_pos : 0 < c.blocks.length := length_pos_of_sum_pos (blocks c) this
  -- ⊢ ∃ i, j < sizeUpTo c (Nat.succ i) ∧ i < length c
  refine' ⟨c.length.pred, _, Nat.pred_lt (ne_of_gt length_pos)⟩
  -- ⊢ j < sizeUpTo c (Nat.succ (Nat.pred (length c)))
  have : c.length.pred.succ = c.length := Nat.succ_pred_eq_of_pos length_pos
  -- ⊢ j < sizeUpTo c (Nat.succ (Nat.pred (length c)))
  simp [this, h]
  -- 🎉 no goals
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
  -- ⊢ False
  set i := c.index j
  -- ⊢ False
  push_neg at H
  -- ⊢ False
  have i_pos : (0 : ℕ) < i := by
    by_contra' i_pos
    revert H
    simp [nonpos_iff_eq_zero.1 i_pos, c.sizeUpTo_zero]
  let i₁ := (i : ℕ).pred
  -- ⊢ False
  have i₁_lt_i : i₁ < i := Nat.pred_lt (ne_of_gt i_pos)
  -- ⊢ False
  have i₁_succ : i₁.succ = i := Nat.succ_pred_eq_of_pos i_pos
  -- ⊢ False
  have := Nat.find_min (c.index_exists j.2) i₁_lt_i
  -- ⊢ False
  simp [lt_trans i₁_lt_i (c.index j).2, i₁_succ] at this
  -- ⊢ False
  exact Nat.lt_le_antisymm H this
  -- 🎉 no goals
#align composition.size_up_to_index_le Composition.sizeUpTo_index_le

/-- Mapping an element `j` of `Fin n` to the element in the block containing it, identified with
`Fin (c.blocks_fun (c.index j))` through the canonical increasing bijection. -/
def invEmbedding (j : Fin n) : Fin (c.blocksFun (c.index j)) :=
  ⟨j - c.sizeUpTo (c.index j), by
    rw [tsub_lt_iff_right, add_comm, ← sizeUpTo_succ']
    -- ⊢ ↑j < sizeUpTo c (↑(index c j) + 1)
    · exact lt_sizeUpTo_index_succ _ _
      -- 🎉 no goals
    · exact sizeUpTo_index_le _ _⟩
      -- 🎉 no goals
#align composition.inv_embedding Composition.invEmbedding

@[simp]
theorem coe_invEmbedding (j : Fin n) : (c.invEmbedding j : ℕ) = j - c.sizeUpTo (c.index j) :=
  rfl
#align composition.coe_inv_embedding Composition.coe_invEmbedding

theorem embedding_comp_inv (j : Fin n) : c.embedding (c.index j) (c.invEmbedding j) = j := by
  rw [Fin.ext_iff]
  -- ⊢ ↑(↑(embedding c (index c j)) (invEmbedding c j)) = ↑j
  apply add_tsub_cancel_of_le (c.sizeUpTo_index_le j)
  -- 🎉 no goals
#align composition.embedding_comp_inv Composition.embedding_comp_inv

theorem mem_range_embedding_iff {j : Fin n} {i : Fin c.length} :
    j ∈ Set.range (c.embedding i) ↔ c.sizeUpTo i ≤ j ∧ (j : ℕ) < c.sizeUpTo (i : ℕ).succ := by
  constructor
  -- ⊢ j ∈ Set.range ↑(embedding c i) → sizeUpTo c ↑i ≤ ↑j ∧ ↑j < sizeUpTo c (Nat.s …
  · intro h
    -- ⊢ sizeUpTo c ↑i ≤ ↑j ∧ ↑j < sizeUpTo c (Nat.succ ↑i)
    rcases Set.mem_range.2 h with ⟨k, hk⟩
    -- ⊢ sizeUpTo c ↑i ≤ ↑j ∧ ↑j < sizeUpTo c (Nat.succ ↑i)
    rw [Fin.ext_iff] at hk
    -- ⊢ sizeUpTo c ↑i ≤ ↑j ∧ ↑j < sizeUpTo c (Nat.succ ↑i)
    dsimp at hk
    -- ⊢ sizeUpTo c ↑i ≤ ↑j ∧ ↑j < sizeUpTo c (Nat.succ ↑i)
    rw [← hk]
    -- ⊢ sizeUpTo c ↑i ≤ sizeUpTo c ↑i + ↑k ∧ sizeUpTo c ↑i + ↑k < sizeUpTo c (Nat.su …
    simp [sizeUpTo_succ', k.is_lt]
    -- 🎉 no goals
  · intro h
    -- ⊢ j ∈ Set.range ↑(embedding c i)
    apply Set.mem_range.2
    -- ⊢ ∃ y, ↑(embedding c i) y = j
    refine' ⟨⟨j - c.sizeUpTo i, _⟩, _⟩
    -- ⊢ ↑j - sizeUpTo c ↑i < blocksFun c i
    · rw [tsub_lt_iff_left, ← sizeUpTo_succ']
      -- ⊢ ↑j < sizeUpTo c (↑i + 1)
      · exact h.2
        -- 🎉 no goals
      · exact h.1
        -- 🎉 no goals
    · rw [Fin.ext_iff]
      -- ⊢ ↑(↑(embedding c i) { val := ↑j - sizeUpTo c ↑i, isLt := (_ : ↑j - sizeUpTo c …
      exact add_tsub_cancel_of_le h.1
      -- 🎉 no goals
#align composition.mem_range_embedding_iff Composition.mem_range_embedding_iff

/-- The embeddings of different blocks of a composition are disjoint. -/
theorem disjoint_range {i₁ i₂ : Fin c.length} (h : i₁ ≠ i₂) :
    Disjoint (Set.range (c.embedding i₁)) (Set.range (c.embedding i₂)) := by
  classical
    wlog h' : i₁ < i₂
    exact (this c h.symm (h.lt_or_lt.resolve_left h')).symm
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
  -- porting note: previously `rwa` closed
  rw [c.embedding_comp_inv j] at this
  -- ⊢ j ∈ Set.range ↑(embedding c (index c j))
  assumption
  -- 🎉 no goals
#align composition.mem_range_embedding Composition.mem_range_embedding

theorem mem_range_embedding_iff' {j : Fin n} {i : Fin c.length} :
    j ∈ Set.range (c.embedding i) ↔ i = c.index j := by
  constructor
  -- ⊢ j ∈ Set.range ↑(embedding c i) → i = index c j
  · rw [← not_imp_not]
    -- ⊢ ¬i = index c j → ¬j ∈ Set.range ↑(embedding c i)
    intro h
    -- ⊢ ¬j ∈ Set.range ↑(embedding c i)
    exact Set.disjoint_right.1 (c.disjoint_range h) (c.mem_range_embedding j)
    -- 🎉 no goals
  · intro h
    -- ⊢ j ∈ Set.range ↑(embedding c i)
    rw [h]
    -- ⊢ j ∈ Set.range ↑(embedding c (index c j))
    exact c.mem_range_embedding j
    -- 🎉 no goals
#align composition.mem_range_embedding_iff' Composition.mem_range_embedding_iff'

theorem index_embedding (i : Fin c.length) (j : Fin (c.blocksFun i)) :
    c.index (c.embedding i j) = i := by
  symm
  -- ⊢ i = index c (↑(embedding c i) j)
  rw [← mem_range_embedding_iff']
  -- ⊢ ↑(embedding c i) j ∈ Set.range ↑(embedding c i)
  apply Set.mem_range_self
  -- 🎉 no goals
#align composition.index_embedding Composition.index_embedding

theorem invEmbedding_comp (i : Fin c.length) (j : Fin (c.blocksFun i)) :
    (c.invEmbedding (c.embedding i j) : ℕ) = j := by
  simp_rw [coe_invEmbedding, index_embedding, coe_embedding, add_tsub_cancel_left]
  -- 🎉 no goals
#align composition.inv_embedding_comp Composition.invEmbedding_comp

/-- Equivalence between the disjoint union of the blocks (each of them seen as
`Fin (c.blocks_fun i)`) with `Fin n`. -/
def blocksFinEquiv : (Σi : Fin c.length, Fin (c.blocksFun i)) ≃ Fin n
    where
  toFun x := c.embedding x.1 x.2
  invFun j := ⟨c.index j, c.invEmbedding j⟩
  left_inv x := by
    rcases x with ⟨i, y⟩
    -- ⊢ (fun j => { fst := index c j, snd := invEmbedding c j }) ((fun x => ↑(embedd …
    dsimp
    -- ⊢ { fst := index c (↑(embedding c i) y), snd := invEmbedding c (↑(embedding c  …
    congr; · exact c.index_embedding _ _
    -- ⊢ index c (↑(embedding c i) y) = i
             -- 🎉 no goals
    rw [Fin.heq_ext_iff]
    -- ⊢ ↑(invEmbedding c (↑(embedding c i) y)) = ↑y
    · exact c.invEmbedding_comp _ _
      -- 🎉 no goals
    · rw [c.index_embedding]
      -- 🎉 no goals
  right_inv j := c.embedding_comp_inv j
#align composition.blocks_fin_equiv Composition.blocksFinEquiv

theorem blocksFun_congr {n₁ n₂ : ℕ} (c₁ : Composition n₁) (c₂ : Composition n₂) (i₁ : Fin c₁.length)
    (i₂ : Fin c₂.length) (hn : n₁ = n₂) (hc : c₁.blocks = c₂.blocks) (hi : (i₁ : ℕ) = i₂) :
    c₁.blocksFun i₁ = c₂.blocksFun i₂ := by
  cases hn
  -- ⊢ blocksFun c₁ i₁ = blocksFun c₂ i₂
  rw [← Composition.ext_iff] at hc
  -- ⊢ blocksFun c₁ i₁ = blocksFun c₂ i₂
  cases hc
  -- ⊢ blocksFun c₁ i₁ = blocksFun c₁ i₂
  congr
  -- ⊢ i₁ = i₂
  rwa [Fin.ext_iff]
  -- 🎉 no goals
#align composition.blocks_fun_congr Composition.blocksFun_congr

/-- Two compositions (possibly of different integers) coincide if and only if they have the
same sequence of blocks. -/
theorem sigma_eq_iff_blocks_eq {c : Σn, Composition n} {c' : Σn, Composition n} :
    c = c' ↔ c.2.blocks = c'.2.blocks := by
  refine' ⟨fun H => by rw [H], fun H => _⟩
  -- ⊢ c = c'
  rcases c with ⟨n, c⟩
  -- ⊢ { fst := n, snd := c } = c'
  rcases c' with ⟨n', c'⟩
  -- ⊢ { fst := n, snd := c } = { fst := n', snd := c' }
  have : n = n' := by rw [← c.blocks_sum, ← c'.blocks_sum, H]
  -- ⊢ { fst := n, snd := c } = { fst := n', snd := c' }
  induction this
  -- ⊢ { fst := n, snd := c } = { fst := n, snd := c' }
  congr
  -- ⊢ c = c'
  ext1
  -- ⊢ c.blocks = c'.blocks
  exact H
  -- 🎉 no goals
#align composition.sigma_eq_iff_blocks_eq Composition.sigma_eq_iff_blocks_eq

/-! ### The composition `Composition.ones` -/


/-- The composition made of blocks all of size `1`. -/
def ones (n : ℕ) : Composition n :=
  ⟨replicate n (1 : ℕ), fun {i} hi => by simp [List.eq_of_mem_replicate hi], by simp⟩
                                         -- 🎉 no goals
                                                                                -- 🎉 no goals
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

-- porting note: TODO, refactor to `List.get`
set_option linter.deprecated false in
@[simp]
theorem ones_blocksFun (n : ℕ) (i : Fin (ones n).length) : (ones n).blocksFun i = 1 := by
  simp only [blocksFun, ones, blocks, i.2, List.nthLe_replicate]
  -- 🎉 no goals
#align composition.ones_blocks_fun Composition.ones_blocksFun

@[simp]
theorem ones_sizeUpTo (n : ℕ) (i : ℕ) : (ones n).sizeUpTo i = min i n := by
  simp [sizeUpTo, ones_blocks, take_replicate]
  -- 🎉 no goals
#align composition.ones_size_up_to Composition.ones_sizeUpTo

@[simp]
theorem ones_embedding (i : Fin (ones n).length) (h : 0 < (ones n).blocksFun i) :
    (ones n).embedding i ⟨0, h⟩ = ⟨i, lt_of_lt_of_le i.2 (ones n).length_le⟩ := by
  ext
  -- ⊢ ↑(↑(embedding (ones n) i) { val := 0, isLt := h }) = ↑{ val := ↑i, isLt := ( …
  simpa using i.2.le
  -- 🎉 no goals
#align composition.ones_embedding Composition.ones_embedding

theorem eq_ones_iff {c : Composition n} : c = ones n ↔ ∀ i ∈ c.blocks, i = 1 := by
  constructor
  -- ⊢ c = ones n → ∀ (i : ℕ), i ∈ c.blocks → i = 1
  · rintro rfl
    -- ⊢ ∀ (i : ℕ), i ∈ (ones n).blocks → i = 1
    exact fun i => eq_of_mem_replicate
    -- 🎉 no goals
  · intro H
    -- ⊢ c = ones n
    ext1
    -- ⊢ c.blocks = (ones n).blocks
    have A : c.blocks = replicate c.blocks.length 1 := eq_replicate_of_mem H
    -- ⊢ c.blocks = (ones n).blocks
    have : c.blocks.length = n := by
      conv_rhs => rw [← c.blocks_sum, A]
      simp
    rw [A, this, ones_blocks]
    -- 🎉 no goals
#align composition.eq_ones_iff Composition.eq_ones_iff

theorem ne_ones_iff {c : Composition n} : c ≠ ones n ↔ ∃ i ∈ c.blocks, 1 < i := by
  refine' (not_congr eq_ones_iff).trans _
  -- ⊢ (¬∀ (i : ℕ), i ∈ c.blocks → i = 1) ↔ ∃ i, i ∈ c.blocks ∧ 1 < i
  have : ∀ j ∈ c.blocks, j = 1 ↔ j ≤ 1 := fun j hj => by simp [le_antisymm_iff, c.one_le_blocks hj]
  -- ⊢ (¬∀ (i : ℕ), i ∈ c.blocks → i = 1) ↔ ∃ i, i ∈ c.blocks ∧ 1 < i
  simp (config := { contextual := true }) [this]
  -- 🎉 no goals
#align composition.ne_ones_iff Composition.ne_ones_iff

theorem eq_ones_iff_length {c : Composition n} : c = ones n ↔ c.length = n := by
  constructor
  -- ⊢ c = ones n → length c = n
  · rintro rfl
    -- ⊢ length (ones n) = n
    exact ones_length n
    -- 🎉 no goals
  · contrapose
    -- ⊢ ¬c = ones n → ¬length c = n
    intro H length_n
    -- ⊢ False
    apply lt_irrefl n
    -- ⊢ n < n
    calc
      n = ∑ i : Fin c.length, 1 := by simp [length_n]
      _ < ∑ i : Fin c.length, c.blocksFun i := by
        {
        obtain ⟨i, hi, i_blocks⟩ : ∃ i ∈ c.blocks, 1 < i := ne_ones_iff.1 H
        rw [← ofFn_blocksFun, mem_ofFn c.blocksFun, Set.mem_range] at hi
        obtain ⟨j : Fin c.length, hj : c.blocksFun j = i⟩ := hi
        rw [← hj] at i_blocks
        exact Finset.sum_lt_sum (fun i _ => by simp [blocksFun]) ⟨j, Finset.mem_univ _, i_blocks⟩
        }
      _ = n := c.sum_blocksFun
#align composition.eq_ones_iff_length Composition.eq_ones_iff_length

theorem eq_ones_iff_le_length {c : Composition n} : c = ones n ↔ n ≤ c.length := by
  simp [eq_ones_iff_length, le_antisymm_iff, c.length_le]
  -- 🎉 no goals
#align composition.eq_ones_iff_le_length Composition.eq_ones_iff_le_length

/-! ### The composition `Composition.single` -/

/-- The composition made of a single block of size `n`. -/
def single (n : ℕ) (h : 0 < n) : Composition n :=
  ⟨[n], by simp [h], by simp⟩
           -- 🎉 no goals
                        -- 🎉 no goals
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
                                       -- 🎉 no goals
#align composition.single_blocks_fun Composition.single_blocksFun

@[simp]
theorem single_embedding {n : ℕ} (h : 0 < n) (i : Fin n) :
    ((single n h).embedding (0 : Fin 1)) i = i := by
  ext
  -- ⊢ ↑(↑(embedding (single n h) 0) i) = ↑i
  simp
  -- 🎉 no goals
#align composition.single_embedding Composition.single_embedding

theorem eq_single_iff_length {n : ℕ} (h : 0 < n) {c : Composition n} :
    c = single n h ↔ c.length = 1 := by
  constructor
  -- ⊢ c = single n h → length c = 1
  · intro H
    -- ⊢ length c = 1
    rw [H]
    -- ⊢ length (single n h) = 1
    exact single_length h
    -- 🎉 no goals
  · intro H
    -- ⊢ c = single n h
    ext1
    -- ⊢ c.blocks = (single n h).blocks
    have A : c.blocks.length = 1 := H ▸ c.blocks_length
    -- ⊢ c.blocks = (single n h).blocks
    have B : c.blocks.sum = n := c.blocks_sum
    -- ⊢ c.blocks = (single n h).blocks
    rw [eq_cons_of_length_one A] at B ⊢
    -- ⊢ [nthLe c.blocks 0 (_ : 0 < List.length c.blocks)] = (single n h).blocks
    simpa [single_blocks] using B
    -- 🎉 no goals
#align composition.eq_single_iff_length Composition.eq_single_iff_length

theorem ne_single_iff {n : ℕ} (hn : 0 < n) {c : Composition n} :
    c ≠ single n hn ↔ ∀ i, c.blocksFun i < n := by
  rw [← not_iff_not]
  -- ⊢ ¬c ≠ single n hn ↔ ¬∀ (i : Fin (length c)), blocksFun c i < n
  push_neg
  -- ⊢ c = single n hn ↔ ∃ i, n ≤ blocksFun c i
  constructor
  -- ⊢ c = single n hn → ∃ i, n ≤ blocksFun c i
  · rintro rfl
    -- ⊢ ∃ i, n ≤ blocksFun (single n hn) i
    exact ⟨⟨0, by simp⟩, by simp⟩
    -- 🎉 no goals
  · rintro ⟨i, hi⟩
    -- ⊢ c = single n hn
    rw [eq_single_iff_length]
    -- ⊢ length c = 1
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
    -- 🎉 no goals
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

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
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

-- porting note: can't refer to subeqn in Lean 4 this way, and seems to definitionally simp
--attribute [local simp] splitWrtCompositionAux.equations._eqn_1

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[local simp]
theorem splitWrtCompositionAux_cons (l : List α) (n ns) :
    l.splitWrtCompositionAux (n::ns) = take n l::(drop n l).splitWrtCompositionAux ns := by
  simp [splitWrtCompositionAux]
  -- 🎉 no goals
#align list.split_wrt_composition_aux_cons List.splitWrtCompositionAux_cons

theorem length_splitWrtCompositionAux (l : List α) (ns) :
    length (l.splitWrtCompositionAux ns) = ns.length := by
    induction ns generalizing l
    -- ⊢ length (splitWrtCompositionAux l []) = length []
    · simp [splitWrtCompositionAux, *]
      -- 🎉 no goals
    · simp [*]
      -- 🎉 no goals
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
  -- ⊢ ∀ {l : List α}, sum [] ≤ length l → map length (splitWrtCompositionAux l []) …
                                 -- ⊢ map length (splitWrtCompositionAux l []) = []
                                 -- ⊢ map length (splitWrtCompositionAux l (n :: ns)) = n :: ns
                                               -- ⊢ map length (splitWrtCompositionAux l []) = []
                                               -- ⊢ map length (splitWrtCompositionAux l (n :: ns)) = n :: ns
  · simp
    -- 🎉 no goals
  have := le_trans (Nat.le_add_right _ _) h
  -- ⊢ map length (splitWrtCompositionAux l (n :: ns)) = n :: ns
  simp only [splitWrtCompositionAux_cons, this]; dsimp
  -- ⊢ map length (take n l :: splitWrtCompositionAux (drop n l) ns) = n :: ns
                                                 -- ⊢ length (take n l) :: map length (splitWrtCompositionAux (drop n l) ns) = n : …
  rw [length_take, IH] <;> simp [length_drop]
  -- ⊢ min n (length l) :: ns = n :: ns
                           -- ⊢ n ≤ length l
                           -- ⊢ sum ns ≤ length l - n
  · assumption
    -- 🎉 no goals
  · exact le_tsub_of_add_le_left h
    -- 🎉 no goals
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
  -- ⊢ 0 < length l'
  exact c.blocks_pos this
  -- 🎉 no goals
#align list.length_pos_of_mem_split_wrt_composition List.length_pos_of_mem_splitWrtComposition

theorem sum_take_map_length_splitWrtComposition (l : List α) (c : Composition l.length) (i : ℕ) :
    (((l.splitWrtComposition c).map length).take i).sum = c.sizeUpTo i := by
  congr
  -- ⊢ map length (splitWrtComposition l c) = c.blocks
  exact map_length_splitWrtComposition l c
  -- 🎉 no goals
#align list.sum_take_map_length_split_wrt_composition List.sum_take_map_length_splitWrtComposition

-- porting note: TODO, refactor to `List.get`
set_option linter.deprecated false in
theorem nthLe_splitWrtCompositionAux (l : List α) (ns : List ℕ) {i : ℕ} (hi) :
    nthLe (l.splitWrtCompositionAux ns) i hi =
      (l.take (ns.take (i + 1)).sum).drop (ns.take i).sum := by
  induction' ns with n ns IH generalizing l i
  -- ⊢ nthLe (splitWrtCompositionAux l []) i hi = drop (sum (take i [])) (take (sum …
  · cases hi
    -- 🎉 no goals
  cases' i with i
  -- ⊢ nthLe (splitWrtCompositionAux l (n :: ns)) Nat.zero hi = drop (sum (take Nat …
  · rw [Nat.add_zero, List.take_zero, sum_nil, nthLe_zero]; dsimp
    -- ⊢ head! (splitWrtCompositionAux l (n :: ns)) = drop 0 (take (sum (take 1 (n :: …
                                                            -- ⊢ head! (splitWrtCompositionAux l (n :: ns)) = take (sum [n]) l
    simp only [splitWrtCompositionAux_cons, head!, sum, foldl, zero_add]
    -- 🎉 no goals
  · simp only [splitWrtCompositionAux_cons, take, sum_cons,
      Nat.add_eq, add_zero, gt_iff_lt, nthLe_cons, IH]; dsimp
                                                        -- ⊢ drop (sum (take (Nat.succ i - 1) ns)) (take (sum (take (Nat.succ i - 1 + 1)  …
    rw [Nat.succ_sub_succ_eq_sub, ←Nat.succ_eq_add_one,tsub_zero]
    -- ⊢ drop (sum (take i ns)) (take (sum (take (Nat.succ i) ns)) (drop n l)) = drop …
    simp only [← drop_take, drop_drop]
    -- ⊢ drop (sum (take i ns) + n) (take (n + sum (take (Nat.succ i) ns)) l) = drop  …
    rw [add_comm]
    -- 🎉 no goals
#align list.nth_le_split_wrt_composition_aux List.nthLe_splitWrtCompositionAux

-- porting note: TODO, refactor to `List.get`
set_option linter.deprecated false in
/-- The `i`-th sublist in the splitting of a list `l` along a composition `c`, is the slice of `l`
between the indices `c.sizeUpTo i` and `c.sizeUpTo (i+1)`, i.e., the indices in the `i`-th
block of the composition. -/
theorem nthLe_splitWrtComposition (l : List α) (c : Composition n) {i : ℕ}
    (hi : i < (l.splitWrtComposition c).length) :
    nthLe (l.splitWrtComposition c) i hi = (l.take (c.sizeUpTo (i + 1))).drop (c.sizeUpTo i) :=
  nthLe_splitWrtCompositionAux _ _ _
#align list.nth_le_split_wrt_composition List.nthLe_splitWrtComposition

-- porting note: restatement of `nthLe_splitWrtComposition`
theorem get_splitWrtComposition (l : List α) (c : Composition n)
    (i : Fin (l.splitWrtComposition c).length) :
    get (l.splitWrtComposition c) i = (l.take (c.sizeUpTo (i + 1))).drop (c.sizeUpTo i) :=
  nthLe_splitWrtComposition _ _ _

theorem join_splitWrtCompositionAux {ns : List ℕ} :
    ∀ {l : List α}, ns.sum = l.length → (l.splitWrtCompositionAux ns).join = l := by
  induction' ns with n ns IH <;> intro l h <;> simp at h
  -- ⊢ ∀ {l : List α}, sum [] = length l → join (splitWrtCompositionAux l []) = l
                                 -- ⊢ join (splitWrtCompositionAux l []) = l
                                 -- ⊢ join (splitWrtCompositionAux l (n :: ns)) = l
                                               -- ⊢ join (splitWrtCompositionAux l []) = l
                                               -- ⊢ join (splitWrtCompositionAux l (n :: ns)) = l
  · exact (length_eq_zero.1 h.symm).symm
    -- 🎉 no goals
  simp only [splitWrtCompositionAux_cons]; dsimp
  -- ⊢ join (take n l :: splitWrtCompositionAux (drop n l) ns) = l
                                           -- ⊢ take n l ++ join (splitWrtCompositionAux (drop n l) ns) = l
  rw [IH]
  -- ⊢ take n l ++ drop n l = l
  · simp
    -- 🎉 no goals
  · rw [length_drop, ← h, add_tsub_cancel_left]
    -- 🎉 no goals
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
def compositionAsSetEquiv (n : ℕ) : CompositionAsSet n ≃ Finset (Fin (n - 1))
    where
  toFun c :=
    { i : Fin (n - 1) |
        (⟨1 + (i : ℕ), by
              apply (add_lt_add_left i.is_lt 1).trans_le
              -- ⊢ 1 + (n - 1) ≤ Nat.succ n
              rw [Nat.succ_eq_add_one, add_comm]
              -- ⊢ n - 1 + 1 ≤ n + 1
              exact add_le_add (Nat.sub_le n 1) (le_refl 1)⟩ :
              -- 🎉 no goals
            Fin n.succ) ∈
          c.boundaries }.toFinset
  invFun s :=
    { boundaries :=
        { i : Fin n.succ |
            i = 0 ∨ i = Fin.last n ∨ ∃ (j : Fin (n - 1)) (_hj : j ∈ s), (i : ℕ) = j + 1 }.toFinset
      zero_mem := by simp
                     -- 🎉 no goals
      getLast_mem := by simp }
                        -- 🎉 no goals
  left_inv := by
    intro c
    -- ⊢ (fun s => { boundaries := Set.toFinset {i | i = 0 ∨ i = Fin.last n ∨ ∃ j _hj …
    ext i
    -- ⊢ i ∈ ((fun s => { boundaries := Set.toFinset {i | i = 0 ∨ i = Fin.last n ∨ ∃  …
    simp only [add_comm, Set.toFinset_setOf, Finset.mem_univ,
     forall_true_left, Finset.mem_filter, true_and, exists_prop]
    constructor
    -- ⊢ (i = 0 ∨ i = Fin.last n ∨ ∃ j, { val := ↑j + 1, isLt := (_ : ↑j + 1 < Nat.su …
    · rintro (rfl | rfl | ⟨j, hj1, hj2⟩)
      · exact c.zero_mem
        -- 🎉 no goals
      · exact c.getLast_mem
        -- 🎉 no goals
      · convert hj1
        -- 🎉 no goals
    · simp only [or_iff_not_imp_left]
      -- ⊢ i ∈ c.boundaries → ¬i = 0 → ¬i = Fin.last n → ∃ j, { val := ↑j + 1, isLt :=  …
      intro i_mem i_ne_zero i_ne_last
      -- ⊢ ∃ j, { val := ↑j + 1, isLt := (_ : ↑j + 1 < Nat.succ n) } ∈ c.boundaries ∧ ↑ …
      simp [Fin.ext_iff] at i_ne_zero i_ne_last
      -- ⊢ ∃ j, { val := ↑j + 1, isLt := (_ : ↑j + 1 < Nat.succ n) } ∈ c.boundaries ∧ ↑ …
      have A : (1 + (i - 1) : ℕ) = (i : ℕ) := by
        rw [add_comm]
        exact Nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr i_ne_zero)
      refine' ⟨⟨i - 1, _⟩, _, _⟩
      · have : (i : ℕ) < n + 1 := i.2
        -- ⊢ ↑i - 1 < n - 1
        simp [Nat.lt_succ_iff_lt_or_eq, i_ne_last] at this
        -- ⊢ ↑i - 1 < n - 1
        exact Nat.pred_lt_pred i_ne_zero this
        -- 🎉 no goals
      · convert i_mem
        -- ⊢ ↑{ val := ↑i - 1, isLt := (_ : Nat.pred (Nat.sub (↑i) 0) < Nat.pred (Nat.sub …
        simp only [ge_iff_le]
        -- ⊢ ↑i - 1 + 1 = ↑i
        rwa [add_comm]
        -- 🎉 no goals
      · simp only [ge_iff_le]
        -- ⊢ ↑i = ↑i - 1 + 1
        symm
        -- ⊢ ↑i - 1 + 1 = ↑i
        rwa [add_comm]
        -- 🎉 no goals
  right_inv := by
    intro s
    -- ⊢ (fun c => Set.toFinset {i | { val := 1 + ↑i, isLt := (_ : 1 + ↑i < Nat.succ  …
    ext i
    -- ⊢ i ∈ (fun c => Set.toFinset {i | { val := 1 + ↑i, isLt := (_ : 1 + ↑i < Nat.s …
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
    -- ⊢ (↑i + 1 = n ∨ ∃ j, j ∈ s ∧ ↑i = ↑j) ↔ i ∈ s.val
    simp [this, false_or_iff, add_right_inj, add_eq_zero_iff, one_ne_zero, false_and_iff,
      Fin.val_mk]
    constructor
    -- ⊢ (↑i + 1 = n ∨ ∃ j, j ∈ s ∧ ↑i = ↑j) → i ∈ s
    · intro h
      -- ⊢ i ∈ s
      cases' h with n h
      -- ⊢ i ∈ s
      · rw [add_comm] at this
        -- ⊢ i ∈ s
        contradiction
        -- 🎉 no goals
      · cases' h with w h; cases' h with h₁ h₂
        -- ⊢ i ∈ s
                           -- ⊢ i ∈ s
        rw [←Fin.ext_iff] at h₂
        -- ⊢ i ∈ s
        rwa [h₂]
        -- 🎉 no goals
    · intro h
      -- ⊢ ↑i + 1 = n ∨ ∃ j, j ∈ s ∧ ↑i = ↑j
      apply Or.inr
      -- ⊢ ∃ j, j ∈ s ∧ ↑i = ↑j
      use i, h
      -- 🎉 no goals
#align composition_as_set_equiv compositionAsSetEquiv

instance compositionAsSetFintype (n : ℕ) : Fintype (CompositionAsSet n) :=
  Fintype.ofEquiv _ (compositionAsSetEquiv n).symm
#align composition_as_set_fintype compositionAsSetFintype

theorem compositionAsSet_card (n : ℕ) : Fintype.card (CompositionAsSet n) = 2 ^ (n - 1) := by
  have : Fintype.card (Finset (Fin (n - 1))) = 2 ^ (n - 1) := by simp
  -- ⊢ Fintype.card (CompositionAsSet n) = 2 ^ (n - 1)
  rw [← this]
  -- ⊢ Fintype.card (CompositionAsSet n) = Fintype.card (Finset (Fin (n - 1)))
  exact Fintype.card_congr (compositionAsSetEquiv n)
  -- 🎉 no goals
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
  -- ⊢ length c < length c + 1
  exact lt_add_one _
  -- 🎉 no goals
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
  -- ⊢ Finset.min' c.boundaries (_ : Finset.Nonempty c.boundaries) = 0
  exact le_antisymm (Finset.min'_le _ _ c.zero_mem) (Fin.zero_le _)
  -- 🎉 no goals
#align composition_as_set.boundary_zero CompositionAsSet.boundary_zero

@[simp]
theorem boundary_length : c.boundary ⟨c.length, c.length_lt_card_boundaries⟩ = Fin.last n := by
  convert Finset.orderEmbOfFin_last rfl c.card_boundaries_pos
  -- ⊢ Fin.last n = Finset.max' c.boundaries (_ : Finset.Nonempty c.boundaries)
  exact le_antisymm (Finset.le_max' _ _ c.getLast_mem) (Fin.le_last _)
  -- 🎉 no goals
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

-- porting note: TODO, refactor to `List.get`
set_option linter.deprecated false in
theorem blocks_partial_sum {i : ℕ} (h : i < c.boundaries.card) :
    (c.blocks.take i).sum = c.boundary ⟨i, h⟩ := by
  induction' i with i IH
  -- ⊢ sum (take Nat.zero (blocks c)) = ↑(↑(boundary c) { val := Nat.zero, isLt :=  …
  · simp
    -- 🎉 no goals
  have A : i < c.blocks.length := by
    rw [c.card_boundaries_eq_succ_length] at h
    simp [blocks, Nat.lt_of_succ_lt_succ h]
  have B : i < c.boundaries.card := lt_of_lt_of_le A (by simp [blocks, length, Nat.sub_le])
  -- ⊢ sum (take (Nat.succ i) (blocks c)) = ↑(↑(boundary c) { val := Nat.succ i, is …
  rw [sum_take_succ _ _ A, IH B]
  -- ⊢ ↑(↑(boundary c) { val := i, isLt := B }) + nthLe (blocks c) i A = ↑(↑(bounda …
  simp only [blocks, blocksFun, nthLe_ofFn']
  -- ⊢ ↑(↑(boundary c) { val := i, isLt := B }) + (↑(↑(boundary c) { val := i + 1,  …
  apply add_tsub_cancel_of_le
  -- ⊢ ↑(↑(boundary c) { val := i, isLt := B }) ≤ ↑(↑(boundary c) { val := i + 1, i …
  simp
  -- 🎉 no goals
#align composition_as_set.blocks_partial_sum CompositionAsSet.blocks_partial_sum

theorem mem_boundaries_iff_exists_blocks_sum_take_eq {j : Fin (n + 1)} :
    j ∈ c.boundaries ↔ ∃ i < c.boundaries.card, (c.blocks.take i).sum = j := by
  constructor
  -- ⊢ j ∈ c.boundaries → ∃ i, i < Finset.card c.boundaries ∧ sum (take i (blocks c …
  · intro hj
    -- ⊢ ∃ i, i < Finset.card c.boundaries ∧ sum (take i (blocks c)) = ↑j
    rcases(c.boundaries.orderIsoOfFin rfl).surjective ⟨j, hj⟩ with ⟨i, hi⟩
    -- ⊢ ∃ i, i < Finset.card c.boundaries ∧ sum (take i (blocks c)) = ↑j
    rw [Subtype.ext_iff, Subtype.coe_mk] at hi
    -- ⊢ ∃ i, i < Finset.card c.boundaries ∧ sum (take i (blocks c)) = ↑j
    refine' ⟨i.1, i.2, _⟩
    -- ⊢ sum (take (↑i) (blocks c)) = ↑j
    dsimp at hi
    -- ⊢ sum (take (↑i) (blocks c)) = ↑j
    rw [← hi, c.blocks_partial_sum i.2]
    -- ⊢ ↑(↑(boundary c) { val := ↑i, isLt := (_ : ↑i < Finset.card c.boundaries) })  …
    rfl
    -- 🎉 no goals
  · rintro ⟨i, hi, H⟩
    -- ⊢ j ∈ c.boundaries
    convert (c.boundaries.orderIsoOfFin rfl ⟨i, hi⟩).2
    -- ⊢ j = ↑(↑(Finset.orderIsoOfFin c.boundaries (_ : Finset.card c.boundaries = Fi …
    have : c.boundary ⟨i, hi⟩ = j := by rwa [Fin.ext_iff, ← c.blocks_partial_sum hi]
    -- ⊢ j = ↑(↑(Finset.orderIsoOfFin c.boundaries (_ : Finset.card c.boundaries = Fi …
    exact this.symm
    -- 🎉 no goals
#align composition_as_set.mem_boundaries_iff_exists_blocks_sum_take_eq CompositionAsSet.mem_boundaries_iff_exists_blocks_sum_take_eq

theorem blocks_sum : c.blocks.sum = n := by
  have : c.blocks.take c.length = c.blocks := take_all_of_le (by simp [blocks])
  -- ⊢ sum (blocks c) = n
  rw [← this, c.blocks_partial_sum c.length_lt_card_boundaries, c.boundary_length]
  -- ⊢ ↑(Fin.last n) = n
  rfl
  -- 🎉 no goals
#align composition_as_set.blocks_sum CompositionAsSet.blocks_sum

/-- Associating a `Composition n` to a `CompositionAsSet n`, by registering the sizes of the
blocks as a list of positive integers. -/
def toComposition : Composition n where
  blocks := c.blocks
  blocks_pos := by simp only [blocks, forall_mem_ofFn_iff, blocksFun_pos c, forall_true_iff]
                   -- 🎉 no goals
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
  -- 🎉 no goals
#align composition.to_composition_as_set_length Composition.toCompositionAsSet_length

@[simp]
theorem CompositionAsSet.toComposition_length (c : CompositionAsSet n) :
    c.toComposition.length = c.length := by
  simp [CompositionAsSet.toComposition, Composition.length, Composition.blocks]
  -- 🎉 no goals
#align composition_as_set.to_composition_length CompositionAsSet.toComposition_length

@[simp]
theorem Composition.toCompositionAsSet_blocks (c : Composition n) :
    c.toCompositionAsSet.blocks = c.blocks := by
  let d := c.toCompositionAsSet
  -- ⊢ CompositionAsSet.blocks (toCompositionAsSet c) = c.blocks
  change d.blocks = c.blocks
  -- ⊢ CompositionAsSet.blocks d = c.blocks
  have length_eq : d.blocks.length = c.blocks.length := by
    convert c.toCompositionAsSet_length
    simp [CompositionAsSet.blocks]
  suffices H : ∀ i ≤ d.blocks.length, (d.blocks.take i).sum = (c.blocks.take i).sum
  -- ⊢ CompositionAsSet.blocks d = c.blocks
  exact eq_of_sum_take_eq length_eq H
  -- ⊢ ∀ (i : ℕ), i ≤ List.length (CompositionAsSet.blocks d) → sum (take i (Compos …
  intro i hi
  -- ⊢ sum (take i (CompositionAsSet.blocks d)) = sum (take i c.blocks)
  have i_lt : i < d.boundaries.card := by
    -- porting note: relied on `convert` unfolding definitions, switched to using a `simpa`
    simpa [CompositionAsSet.blocks, length_ofFn, Nat.succ_eq_add_one,
      d.card_boundaries_eq_succ_length] using Nat.lt_succ_iff.2 hi
  have i_lt' : i < c.boundaries.card := i_lt
  -- ⊢ sum (take i (CompositionAsSet.blocks d)) = sum (take i c.blocks)
  have i_lt'' : i < c.length + 1 := by rwa [c.card_boundaries_eq_succ_length] at i_lt'
  -- ⊢ sum (take i (CompositionAsSet.blocks d)) = sum (take i c.blocks)
  have A :
    d.boundaries.orderEmbOfFin rfl ⟨i, i_lt⟩ =
      c.boundaries.orderEmbOfFin c.card_boundaries_eq_succ_length ⟨i, i_lt''⟩ :=
    rfl
  have B : c.sizeUpTo i = c.boundary ⟨i, i_lt''⟩ := rfl
  -- ⊢ sum (take i (CompositionAsSet.blocks d)) = sum (take i c.blocks)
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
  -- ⊢ j ∈ Composition.boundaries (toComposition c) ↔ j ∈ c.boundaries
  simp only [c.mem_boundaries_iff_exists_blocks_sum_take_eq, Composition.boundaries, Finset.mem_map]
  -- ⊢ (∃ a, a ∈ Finset.univ ∧ ↑(Composition.boundary (toComposition c)).toEmbeddin …
  constructor
  -- ⊢ (∃ a, a ∈ Finset.univ ∧ ↑(Composition.boundary (toComposition c)).toEmbeddin …
  · rintro ⟨i, _, hi⟩
    -- ⊢ ∃ i, i < Finset.card c.boundaries ∧ sum (take i (blocks c)) = ↑j
    refine' ⟨i.1, _, _⟩
    -- ⊢ ↑i < Finset.card c.boundaries
    simpa [c.card_boundaries_eq_succ_length] using i.2
    -- ⊢ sum (take (↑i) (blocks c)) = ↑j
    simp [Composition.boundary, Composition.sizeUpTo, ← hi]
    -- 🎉 no goals
  · rintro ⟨i, i_lt, hi⟩
    -- ⊢ ∃ a, a ∈ Finset.univ ∧ ↑(Composition.boundary (toComposition c)).toEmbedding …
    refine' ⟨i, by simp, _⟩
    -- ⊢ ↑(Composition.boundary (toComposition c)).toEmbedding ↑i = j
    rw [c.card_boundaries_eq_succ_length] at i_lt
    -- ⊢ ↑(Composition.boundary (toComposition c)).toEmbedding ↑i = j
    simp [Composition.boundary, Nat.mod_eq_of_lt i_lt, Composition.sizeUpTo, hi]
    -- 🎉 no goals
#align composition_as_set.to_composition_boundaries CompositionAsSet.toComposition_boundaries

@[simp]
theorem Composition.toCompositionAsSet_boundaries (c : Composition n) :
    c.toCompositionAsSet.boundaries = c.boundaries :=
  rfl
#align composition.to_composition_as_set_boundaries Composition.toCompositionAsSet_boundaries

/-- Equivalence between `Composition n` and `CompositionAsSet n`. -/
def compositionEquiv (n : ℕ) : Composition n ≃ CompositionAsSet n
    where
  toFun c := c.toCompositionAsSet
  invFun c := c.toComposition
  left_inv c := by
    ext1
    -- ⊢ ((fun c => CompositionAsSet.toComposition c) ((fun c => Composition.toCompos …
    exact c.toCompositionAsSet_blocks
    -- 🎉 no goals
  right_inv c := by
    ext1
    -- ⊢ ((fun c => Composition.toCompositionAsSet c) ((fun c => CompositionAsSet.toC …
    exact c.toComposition_boundaries
    -- 🎉 no goals
#align composition_equiv compositionEquiv

instance compositionFintype (n : ℕ) : Fintype (Composition n) :=
  Fintype.ofEquiv _ (compositionEquiv n).symm
#align composition_fintype compositionFintype

theorem composition_card (n : ℕ) : Fintype.card (Composition n) = 2 ^ (n - 1) := by
  rw [← compositionAsSet_card n]
  -- ⊢ Fintype.card (Composition n) = Fintype.card (CompositionAsSet n)
  exact Fintype.card_congr (compositionEquiv n)
  -- 🎉 no goals
#align composition_card composition_card
