/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort

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
* `c.blocksFun : Fin c.length → ℕ` is the realization of `c.blocks` as a function on
  `Fin c.length`. This is the main object when using compositions to understand the composition of
    analytic functions.
* `c.sizeUpTo : ℕ → ℕ` is the sum of the size of the blocks up to `i`.;
* `c.embedding i : Fin (c.blocksFun i) → Fin n` is the increasing embedding of the `i`-th block in
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
* `splitWrtComposition_join` states that joining a list of lists, and then splitting it back
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

assert_not_exists Field

open List

variable {n : ℕ}

/-- A composition of `n` is a list of positive integers summing to `n`. -/
@[ext]
structure Composition (n : ℕ) where
  /-- List of positive integers summing to `n` -/
  blocks : List ℕ
  /-- Proof of positivity for `blocks` -/
  blocks_pos : ∀ {i}, i ∈ blocks → 0 < i
  /-- Proof that `blocks` sums to `n` -/
  blocks_sum : blocks.sum = n
  deriving DecidableEq

attribute [simp] Composition.blocks_sum

/-- Combinatorial viewpoint on a composition of `n`, by seeing it as non-empty blocks of
consecutive integers in `{0, ..., n-1}`. We register every block by its left end-point, yielding
a finset containing `0`. As this does not make sense for `n = 0`, we add `n` to this finset, and
get a finset of `{0, ..., n}` containing `0` and `n`. This is the data in the structure
`CompositionAsSet n`. -/
@[ext]
structure CompositionAsSet (n : ℕ) where
  /-- Combinatorial viewpoint on a composition of `n` as consecutive integers `{0, ..., n-1}` -/
  boundaries : Finset (Fin n.succ)
  /-- Proof that `0` is a member of `boundaries` -/
  zero_mem : (0 : Fin n.succ) ∈ boundaries
  /-- Last element of the composition -/
  getLast_mem : Fin.last n ∈ boundaries
  deriving DecidableEq

instance {n : ℕ} : Inhabited (CompositionAsSet n) :=
  ⟨⟨Finset.univ, Finset.mem_univ _, Finset.mem_univ _⟩⟩

attribute [simp] CompositionAsSet.zero_mem CompositionAsSet.getLast_mem

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

theorem blocks_length : c.blocks.length = c.length :=
  rfl

/-- The blocks of a composition, seen as a function on `Fin c.length`. When composing analytic
functions using compositions, this is the main player. -/
def blocksFun : Fin c.length → ℕ := c.blocks.get

@[simp]
theorem ofFn_blocksFun : ofFn c.blocksFun = c.blocks :=
  ofFn_get _

@[simp]
theorem sum_blocksFun : ∑ i, c.blocksFun i = n := by
  conv_rhs => rw [← c.blocks_sum, ← ofFn_blocksFun, sum_ofFn]

@[simp]
theorem blocksFun_mem_blocks (i : Fin c.length) : c.blocksFun i ∈ c.blocks :=
  get_mem _ _

theorem one_le_blocks {i : ℕ} (h : i ∈ c.blocks) : 1 ≤ i :=
  c.blocks_pos h

theorem blocks_le {i : ℕ} (h : i ∈ c.blocks) : i ≤ n := by
  rw [← c.blocks_sum]
  exact List.le_sum_of_mem h

@[simp]
theorem one_le_blocks' {i : ℕ} (h : i < c.length) : 1 ≤ c.blocks[i] :=
  c.one_le_blocks (get_mem (blocks c) _)

@[simp]
theorem blocks_pos' (i : ℕ) (h : i < c.length) : 0 < c.blocks[i] :=
  c.one_le_blocks' h

@[simp]
theorem one_le_blocksFun (i : Fin c.length) : 1 ≤ c.blocksFun i :=
  c.one_le_blocks (c.blocksFun_mem_blocks i)

@[simp]
theorem blocksFun_le {n} (c : Composition n) (i : Fin c.length) :
    c.blocksFun i ≤ n :=
  c.blocks_le <| getElem_mem _

@[simp]
theorem length_le : c.length ≤ n := by
  conv_rhs => rw [← c.blocks_sum]
  exact length_le_sum_of_one_le _ fun i hi => c.one_le_blocks hi

@[simp]
theorem blocks_eq_nil : c.blocks = [] ↔ n = 0 := by
  constructor
  · intro h
    simpa using congr(List.sum $h)
  · rintro rfl
    rw [← length_eq_zero_iff, ← nonpos_iff_eq_zero]
    exact c.length_le

protected theorem length_eq_zero : c.length = 0 ↔ n = 0 := by
  simp

@[simp]
theorem length_pos_iff : 0 < c.length ↔ 0 < n := by
  simp [pos_iff_ne_zero]

alias ⟨_, length_pos_of_pos⟩ := length_pos_iff

/-- The sum of the sizes of the blocks in a composition up to `i`. -/
def sizeUpTo (i : ℕ) : ℕ :=
  (c.blocks.take i).sum

@[simp]
theorem sizeUpTo_zero : c.sizeUpTo 0 = 0 := by simp [sizeUpTo]

theorem sizeUpTo_ofLength_le (i : ℕ) (h : c.length ≤ i) : c.sizeUpTo i = n := by
  dsimp [sizeUpTo]
  convert c.blocks_sum
  exact take_of_length_le h

@[simp]
theorem sizeUpTo_length : c.sizeUpTo c.length = n :=
  c.sizeUpTo_ofLength_le c.length le_rfl

theorem sizeUpTo_le (i : ℕ) : c.sizeUpTo i ≤ n := by
  conv_rhs => rw [← c.blocks_sum, ← sum_take_add_sum_drop _ i]
  exact Nat.le_add_right _ _

theorem sizeUpTo_succ {i : ℕ} (h : i < c.length) :
    c.sizeUpTo (i + 1) = c.sizeUpTo i + c.blocks[i] := by
  simp only [sizeUpTo]
  rw [sum_take_succ _ _ h]

theorem sizeUpTo_succ' (i : Fin c.length) :
    c.sizeUpTo ((i : ℕ) + 1) = c.sizeUpTo i + c.blocksFun i :=
  c.sizeUpTo_succ i.2

theorem sizeUpTo_strict_mono {i : ℕ} (h : i < c.length) : c.sizeUpTo i < c.sizeUpTo (i + 1) := by
  rw [c.sizeUpTo_succ h]
  simp

theorem monotone_sizeUpTo : Monotone c.sizeUpTo :=
  monotone_sum_take _

/-- The `i`-th boundary of a composition, i.e., the leftmost point of the `i`-th block. We include
a virtual point at the right of the last block, to make for a nice equiv with
`CompositionAsSet n`. -/
def boundary : Fin (c.length + 1) ↪o Fin (n + 1) :=
  (OrderEmbedding.ofStrictMono fun i => ⟨c.sizeUpTo i, Nat.lt_succ_of_le (c.sizeUpTo_le i)⟩) <|
    Fin.strictMono_iff_lt_succ.2 fun ⟨_, hi⟩ => c.sizeUpTo_strict_mono hi

@[simp]
theorem boundary_zero : c.boundary 0 = 0 := by simp [boundary]

@[simp]
theorem boundary_last : c.boundary (Fin.last c.length) = Fin.last n := by
  simp [boundary, Fin.ext_iff]

/-- The boundaries of a composition, i.e., the leftmost point of all the blocks. We include
a virtual point at the right of the last block, to make for a nice equiv with
`CompositionAsSet n`. -/
def boundaries : Finset (Fin (n + 1)) :=
  Finset.univ.map c.boundary.toEmbedding

theorem card_boundaries_eq_succ_length : c.boundaries.card = c.length + 1 := by simp [boundaries]

/-- To `c : Composition n`, one can associate a `CompositionAsSet n` by registering the leftmost
point of each block, and adding a virtual point at the right of the last block. -/
def toCompositionAsSet : CompositionAsSet n where
  boundaries := c.boundaries
  zero_mem := by
    simp only [boundaries, Finset.mem_univ, Finset.mem_map]
    exact ⟨0, And.intro True.intro rfl⟩
  getLast_mem := by
    simp only [boundaries, Finset.mem_univ, Finset.mem_map]
    exact ⟨Fin.last c.length, And.intro True.intro c.boundary_last⟩

/-- The canonical increasing bijection between `Fin (c.length + 1)` and `c.boundaries` is
exactly `c.boundary`. -/
theorem orderEmbOfFin_boundaries :
    c.boundaries.orderEmbOfFin c.card_boundaries_eq_succ_length = c.boundary := by
  refine (Finset.orderEmbOfFin_unique' _ ?_).symm
  exact fun i => (Finset.mem_map' _).2 (Finset.mem_univ _)

/-- Embedding the `i`-th block of a composition (identified with `Fin (c.blocksFun i)`) into
`Fin n` at the relevant position. -/
def embedding (i : Fin c.length) : Fin (c.blocksFun i) ↪o Fin n :=
  (Fin.natAddOrderEmb <| c.sizeUpTo i).trans <| Fin.castLEOrderEmb <|
    calc
      c.sizeUpTo i + c.blocksFun i = c.sizeUpTo (i + 1) := (c.sizeUpTo_succ i.2).symm
      _ ≤ c.sizeUpTo c.length := monotone_sum_take _ i.2
      _ = n := c.sizeUpTo_length

@[simp]
theorem coe_embedding (i : Fin c.length) (j : Fin (c.blocksFun i)) :
    (c.embedding i j : ℕ) = c.sizeUpTo i + j :=
  rfl

/-- `index_exists` asserts there is some `i` with `j < c.sizeUpTo (i+1)`.
In the next definition `index` we use `Nat.find` to produce the minimal such index.
-/
theorem index_exists {j : ℕ} (h : j < n) : ∃ i : ℕ, j < c.sizeUpTo (i + 1) ∧ i < c.length := by
  have n_pos : 0 < n := lt_of_le_of_lt (zero_le j) h
  have : 0 < c.blocks.sum := by rwa [← c.blocks_sum] at n_pos
  have length_pos : 0 < c.blocks.length := length_pos_of_sum_pos (blocks c) this
  refine ⟨c.length - 1, ?_, Nat.pred_lt (ne_of_gt length_pos)⟩
  have : c.length - 1 + 1 = c.length := Nat.succ_pred_eq_of_pos length_pos
  simp [this, h]

/-- `c.index j` is the index of the block in the composition `c` containing `j`. -/
def index (j : Fin n) : Fin c.length :=
  ⟨Nat.find (c.index_exists j.2), (Nat.find_spec (c.index_exists j.2)).2⟩

theorem lt_sizeUpTo_index_succ (j : Fin n) : (j : ℕ) < c.sizeUpTo (c.index j).succ :=
  (Nat.find_spec (c.index_exists j.2)).1

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
  simp_all [lt_trans i₁_lt_i (c.index j).2]

/-- Mapping an element `j` of `Fin n` to the element in the block containing it, identified with
`Fin (c.blocksFun (c.index j))` through the canonical increasing bijection. -/
def invEmbedding (j : Fin n) : Fin (c.blocksFun (c.index j)) :=
  ⟨j - c.sizeUpTo (c.index j), by
    rw [tsub_lt_iff_right, add_comm, ← sizeUpTo_succ']
    · exact lt_sizeUpTo_index_succ _ _
    · exact sizeUpTo_index_le _ _⟩

@[simp]
theorem coe_invEmbedding (j : Fin n) : (c.invEmbedding j : ℕ) = j - c.sizeUpTo (c.index j) :=
  rfl

@[simp]
theorem embedding_comp_inv (j : Fin n) : c.embedding (c.index j) (c.invEmbedding j) = j := by
  rw [Fin.ext_iff]
  apply add_tsub_cancel_of_le (c.sizeUpTo_index_le j)

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

/-- The embeddings of different blocks of a composition are disjoint. -/
theorem disjoint_range {i₁ i₂ : Fin c.length} (h : i₁ ≠ i₂) :
    Disjoint (Set.range (c.embedding i₁)) (Set.range (c.embedding i₂)) := by
  classical
    wlog h' : i₁ < i₂
    · exact (this c h.symm (h.lt_or_gt.resolve_left h')).symm
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

theorem mem_range_embedding (j : Fin n) : j ∈ Set.range (c.embedding (c.index j)) := by
  have : c.embedding (c.index j) (c.invEmbedding j) ∈ Set.range (c.embedding (c.index j)) :=
    Set.mem_range_self _
  rwa [c.embedding_comp_inv j] at this

theorem mem_range_embedding_iff' {j : Fin n} {i : Fin c.length} :
    j ∈ Set.range (c.embedding i) ↔ i = c.index j := by
  constructor
  · rw [← not_imp_not]
    intro h
    exact Set.disjoint_right.1 (c.disjoint_range h) (c.mem_range_embedding j)
  · intro h
    rw [h]
    exact c.mem_range_embedding j

@[simp]
theorem index_embedding (i : Fin c.length) (j : Fin (c.blocksFun i)) :
    c.index (c.embedding i j) = i := by
  symm
  rw [← mem_range_embedding_iff']
  apply Set.mem_range_self

theorem invEmbedding_comp (i : Fin c.length) (j : Fin (c.blocksFun i)) :
    (c.invEmbedding (c.embedding i j) : ℕ) = j := by
  simp_rw [coe_invEmbedding, index_embedding, coe_embedding, add_tsub_cancel_left]

/-- Equivalence between the disjoint union of the blocks (each of them seen as
`Fin (c.blocksFun i)`) with `Fin n`. -/
def blocksFinEquiv : (Σ i : Fin c.length, Fin (c.blocksFun i)) ≃ Fin n where
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

theorem blocksFun_congr {n₁ n₂ : ℕ} (c₁ : Composition n₁) (c₂ : Composition n₂) (i₁ : Fin c₁.length)
    (i₂ : Fin c₂.length) (hn : n₁ = n₂) (hc : c₁.blocks = c₂.blocks) (hi : (i₁ : ℕ) = i₂) :
    c₁.blocksFun i₁ = c₂.blocksFun i₂ := by
  cases hn
  rw [← Composition.ext_iff] at hc
  cases hc
  congr
  rwa [Fin.ext_iff]

/-- Two compositions (possibly of different integers) coincide if and only if they have the
same sequence of blocks. -/
theorem sigma_eq_iff_blocks_eq {c : Σ n, Composition n} {c' : Σ n, Composition n} :
    c = c' ↔ c.2.blocks = c'.2.blocks := by
  refine ⟨fun H => by rw [H], fun H => ?_⟩
  rcases c with ⟨n, c⟩
  rcases c' with ⟨n', c'⟩
  have : n = n' := by rw [← c.blocks_sum, ← c'.blocks_sum, H]
  induction this
  congr
  ext1
  exact H

/-! ### The composition `Composition.ones` -/


/-- The composition made of blocks all of size `1`. -/
def ones (n : ℕ) : Composition n :=
  ⟨replicate n (1 : ℕ), fun {i} hi => by simp [List.eq_of_mem_replicate hi], by simp⟩

instance {n : ℕ} : Inhabited (Composition n) :=
  ⟨Composition.ones n⟩

@[simp]
theorem ones_length (n : ℕ) : (ones n).length = n :=
  List.length_replicate

@[simp]
theorem ones_blocks (n : ℕ) : (ones n).blocks = replicate n (1 : ℕ) :=
  rfl

@[simp]
theorem ones_blocksFun (n : ℕ) (i : Fin (ones n).length) : (ones n).blocksFun i = 1 := by
  simp only [blocksFun, ones, get_eq_getElem, getElem_replicate]

@[simp]
theorem ones_sizeUpTo (n : ℕ) (i : ℕ) : (ones n).sizeUpTo i = min i n := by
  simp [sizeUpTo, ones_blocks, take_replicate]

@[simp]
theorem ones_embedding (i : Fin (ones n).length) (h : 0 < (ones n).blocksFun i) :
    (ones n).embedding i ⟨0, h⟩ = ⟨i, lt_of_lt_of_le i.2 (ones n).length_le⟩ := by
  ext
  simpa using i.2.le

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

theorem ne_ones_iff {c : Composition n} : c ≠ ones n ↔ ∃ i ∈ c.blocks, 1 < i := by
  refine (not_congr eq_ones_iff).trans ?_
  have : ∀ j ∈ c.blocks, j = 1 ↔ j ≤ 1 := fun j hj => by simp [le_antisymm_iff, c.one_le_blocks hj]
  simp +contextual [this]

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
        rw [← ofFn_blocksFun, mem_ofFn' c.blocksFun, Set.mem_range] at hi
        obtain ⟨j : Fin c.length, hj : c.blocksFun j = i⟩ := hi
        rw [← hj] at i_blocks
        exact Finset.sum_lt_sum (fun i _ => one_le_blocksFun c i) ⟨j, Finset.mem_univ _, i_blocks⟩
        }
      _ = n := c.sum_blocksFun

theorem eq_ones_iff_le_length {c : Composition n} : c = ones n ↔ n ≤ c.length := by
  simp [eq_ones_iff_length, le_antisymm_iff, c.length_le]

/-! ### The composition `Composition.single` -/

/-- The composition made of a single block of size `n`. -/
def single (n : ℕ) (h : 0 < n) : Composition n :=
  ⟨[n], by simp [h], by simp⟩

@[simp]
theorem single_length {n : ℕ} (h : 0 < n) : (single n h).length = 1 :=
  rfl

@[simp]
theorem single_blocks {n : ℕ} (h : 0 < n) : (single n h).blocks = [n] :=
  rfl

@[simp]
theorem single_blocksFun {n : ℕ} (h : 0 < n) (i : Fin (single n h).length) :
    (single n h).blocksFun i = n := by simp [blocksFun, single]

@[simp]
theorem single_embedding {n : ℕ} (h : 0 < n) (i : Fin n) :
    ((single n h).embedding (0 : Fin 1)) i = i := by
  ext
  simp

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

variable {m : ℕ}

/-- Change `n` in `(c : Composition n)` to a propositionally equal value. -/
@[simps]
protected def cast (c : Composition m) (hmn : m = n) : Composition n where
  __ := c
  blocks_sum := c.blocks_sum.trans hmn

@[simp]
theorem cast_rfl (c : Composition n) : c.cast rfl = c := rfl

theorem cast_heq (c : Composition m) (hmn : m = n) : c.cast hmn ≍ c := by subst m; rfl

theorem cast_eq_cast (c : Composition m) (hmn : m = n) :
    c.cast hmn = cast (hmn ▸ rfl) c := by
  subst m
  rfl

/-- Append two compositions to get a composition of the sum of numbers. -/
@[simps]
def append (c₁ : Composition m) (c₂ : Composition n) : Composition (m + n) where
  blocks := c₁.blocks ++ c₂.blocks
  blocks_pos := by
    intro i hi
    rw [mem_append] at hi
    exact hi.elim c₁.blocks_pos c₂.blocks_pos
  blocks_sum := by simp

/-- Reverse the order of blocks in a composition. -/
@[simps]
def reverse (c : Composition n) : Composition n where
  blocks := c.blocks.reverse
  blocks_pos hi := c.blocks_pos (mem_reverse.mp hi)
  blocks_sum := by simp [List.sum_reverse]

@[simp]
lemma reverse_reverse (c : Composition n) : c.reverse.reverse = c :=
  Composition.ext <| List.reverse_reverse _

lemma reverse_involutive : Function.Involutive (@reverse n) := reverse_reverse
lemma reverse_bijective : Function.Bijective (@reverse n) := reverse_involutive.bijective
lemma reverse_injective : Function.Injective (@reverse n) := reverse_involutive.injective
lemma reverse_surjective : Function.Surjective (@reverse n) := reverse_involutive.surjective

@[simp]
lemma reverse_inj {c₁ c₂ : Composition n} : c₁.reverse = c₂.reverse ↔ c₁ = c₂ :=
  reverse_injective.eq_iff

@[simp]
lemma reverse_ones : (ones n).reverse = ones n := by ext1; simp

@[simp]
lemma reverse_single (hn : 0 < n) : (single n hn).reverse = single n hn := by ext1; simp

@[simp]
lemma reverse_eq_ones {c : Composition n} : c.reverse = ones n ↔ c = ones n :=
  reverse_injective.eq_iff' reverse_ones

@[simp]
lemma reverse_eq_single {hn : 0 < n} {c : Composition n} :
    c.reverse = single n hn ↔ c = single n hn :=
  reverse_injective.eq_iff' <| reverse_single _

lemma reverse_append (c₁ : Composition m) (c₂ : Composition n) :
    reverse (append c₁ c₂) = (append c₂.reverse c₁.reverse).cast (add_comm _ _) :=
  Composition.ext <| by simp

/-- Induction (recursion) principle on `c : Composition _`
that corresponds to the usual induction on the list of blocks of `c`. -/
@[elab_as_elim]
def recOnSingleAppend {motive : ∀ n, Composition n → Sort*} {n : ℕ} (c : Composition n)
    (zero : motive 0 (ones 0))
    (single_append : ∀ k n c, motive n c →
      motive (k + 1 + n) (append (single (k + 1) k.succ_pos) c)) :
    motive n c :=
  match n, c with
  | _, ⟨blocks, blocks_pos, rfl⟩ =>
    match blocks with
    | [] => zero
    | 0 :: _ => by simp at blocks_pos
    | (k + 1) :: l =>
      single_append k l.sum ⟨l, fun hi ↦ blocks_pos <| mem_cons_of_mem _ hi, rfl⟩ <|
        recOnSingleAppend _ zero single_append
  decreasing_by simp

/-- Induction (recursion) principle on `c : Composition _`
that corresponds to the reverse induction on the list of blocks of `c`. -/
@[elab_as_elim]
def recOnAppendSingle {motive : ∀ n, Composition n → Sort*} {n : ℕ} (c : Composition n)
    (zero : motive 0 (ones 0))
    (append_single : ∀ k n c, motive n c →
      motive (n + (k + 1)) (append c (single (k + 1) k.succ_pos))) :
    motive n c :=
  reverse_reverse c ▸ c.reverse.recOnSingleAppend zero fun k n c ih ↦ by
    convert append_single k n c.reverse ih using 1
    · apply add_comm
    · rw [reverse_append, reverse_single]
      apply cast_heq

end Composition

/-!
### Splitting a list

Given a list of length `n` and a composition `c` of `n`, one can split `l` into `c.length` sublists
of respective lengths `c.blocksFun 0`, ..., `c.blocksFun (c.length-1)`. This is inverse to the
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

/-- Given a list of length `n` and a composition `[i₁, ..., iₖ]` of `n`, split `l` into a list of
`k` lists corresponding to the blocks of the composition, of respective lengths `i₁`, ..., `iₖ`.
This makes sense mostly when `n = l.length`, but this is not necessary for the definition. -/
def splitWrtComposition (l : List α) (c : Composition n) : List (List α) :=
  splitWrtCompositionAux l c.blocks

@[local simp]
theorem splitWrtCompositionAux_cons (l : List α) (n ns) :
    l.splitWrtCompositionAux (n::ns) = take n l::(drop n l).splitWrtCompositionAux ns := by
  simp [splitWrtCompositionAux]

theorem length_splitWrtCompositionAux (l : List α) (ns) :
    length (l.splitWrtCompositionAux ns) = ns.length := by
    induction ns generalizing l
    · simp [splitWrtCompositionAux, *]
    · simp [*]

/-- When one splits a list along a composition `c`, the number of sublists thus created is
`c.length`. -/
@[simp]
theorem length_splitWrtComposition (l : List α) (c : Composition n) :
    length (l.splitWrtComposition c) = c.length :=
  length_splitWrtCompositionAux _ _


theorem map_length_splitWrtCompositionAux {ns : List ℕ} :
    ∀ {l : List α}, ns.sum ≤ l.length → map length (l.splitWrtCompositionAux ns) = ns := by
  induction ns with
  | nil => simp [splitWrtCompositionAux]
  | cons n ns IH => grind [splitWrtCompositionAux_cons]

/-- When one splits a list along a composition `c`, the lengths of the sublists thus created are
given by the block sizes in `c`. -/
theorem map_length_splitWrtComposition (l : List α) (c : Composition l.length) :
    map length (l.splitWrtComposition c) = c.blocks :=
  map_length_splitWrtCompositionAux (le_of_eq c.blocks_sum)

theorem length_pos_of_mem_splitWrtComposition {l l' : List α} {c : Composition l.length}
    (h : l' ∈ l.splitWrtComposition c) : 0 < length l' := by
  have : l'.length ∈ (l.splitWrtComposition c).map List.length :=
    List.mem_map_of_mem h
  rw [map_length_splitWrtComposition] at this
  exact c.blocks_pos this

theorem sum_take_map_length_splitWrtComposition (l : List α) (c : Composition l.length) (i : ℕ) :
    (((l.splitWrtComposition c).map length).take i).sum = c.sizeUpTo i := by
  congr
  exact map_length_splitWrtComposition l c

theorem getElem_splitWrtCompositionAux (l : List α) (ns : List ℕ) {i : ℕ}
    (hi : i < (l.splitWrtCompositionAux ns).length) :
    (l.splitWrtCompositionAux ns)[i] =
      (l.take (ns.take (i + 1)).sum).drop (ns.take i).sum := by
  induction ns generalizing l i with
  | nil => cases hi
  | cons n ns IH =>
    rcases i with - | i
    · simp
    · simp only [splitWrtCompositionAux, getElem_cons_succ, IH, take,
          sum_cons, splitAt_eq, drop_take, drop_drop]
      rw [Nat.add_sub_add_left]

/-- The `i`-th sublist in the splitting of a list `l` along a composition `c`, is the slice of `l`
between the indices `c.sizeUpTo i` and `c.sizeUpTo (i+1)`, i.e., the indices in the `i`-th
block of the composition. -/
theorem getElem_splitWrtComposition' (l : List α) (c : Composition n) {i : ℕ}
    (hi : i < (l.splitWrtComposition c).length) :
    (l.splitWrtComposition c)[i] = (l.take (c.sizeUpTo (i + 1))).drop (c.sizeUpTo i) :=
  getElem_splitWrtCompositionAux _ _ hi

theorem getElem_splitWrtComposition (l : List α) (c : Composition n)
    (i : Nat) (h : i < (l.splitWrtComposition c).length) :
    (l.splitWrtComposition c)[i] = (l.take (c.sizeUpTo (i + 1))).drop (c.sizeUpTo i) :=
  getElem_splitWrtComposition' _ _ h

theorem flatten_splitWrtCompositionAux {ns : List ℕ} :
    ∀ {l : List α}, ns.sum = l.length → (l.splitWrtCompositionAux ns).flatten = l := by
  induction ns with
  | nil => exact fun h ↦ (length_eq_zero_iff.1 h.symm).symm
  | cons n ns IH =>
    intro l h; rw [sum_cons] at h
    simp only [splitWrtCompositionAux_cons]; dsimp
    rw [IH]
    · simp
    · rw [length_drop, ← h, add_tsub_cancel_left]

/-- If one splits a list along a composition, and then flattens the sublists, one gets back the
original list. -/
@[simp]
theorem flatten_splitWrtComposition (l : List α) (c : Composition l.length) :
    (l.splitWrtComposition c).flatten = l :=
  flatten_splitWrtCompositionAux c.blocks_sum

/-- If one joins a list of lists and then splits the flattening along the right composition,
one gets back the original list of lists. -/
@[simp]
theorem splitWrtComposition_flatten (L : List (List α)) (c : Composition L.flatten.length)
    (h : map length L = c.blocks) : splitWrtComposition (flatten L) c = L := by
  simp only [and_self_iff, eq_iff_flatten_eq, flatten_splitWrtComposition,
    map_length_splitWrtComposition, h]

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
        (⟨1 + (i : ℕ), by omega⟩ : Fin n.succ) ∈ c.boundaries }.toFinset
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
     Finset.mem_filter, true_and, exists_prop]
    constructor
    · rintro (rfl | rfl | ⟨j, hj1, hj2⟩)
      · exact c.zero_mem
      · exact c.getLast_mem
      · convert hj1
    · simp only [or_iff_not_imp_left, ← ne_eq, ← Fin.exists_succ_eq]
      rintro i_mem ⟨j, rfl⟩ i_ne_last
      rcases Nat.exists_add_one_eq.mpr j.pos with ⟨n, rfl⟩
      obtain ⟨k, rfl⟩ : ∃ k : Fin n, k.castSucc = j := by
        simpa [Fin.exists_castSucc_eq] using i_ne_last
      use k
      simpa using i_mem
  right_inv := by
    intro s
    ext i
    have : (i : ℕ) + 1 ≠ n := by
      apply ne_of_lt
      convert add_lt_add_right i.is_lt 1
      apply (Nat.succ_pred_eq_of_pos _).symm
      exact Nat.lt_of_lt_pred (Fin.pos i)
    simp_rw [add_comm, Fin.ext_iff, Fin.val_zero, Fin.val_last, exists_prop, Set.toFinset_setOf,
      Finset.mem_filter_univ, reduceCtorEq, this, false_or, add_left_inj, ← Fin.ext_iff,
      exists_eq_right']

instance compositionAsSetFintype (n : ℕ) : Fintype (CompositionAsSet n) :=
  Fintype.ofEquiv _ (compositionAsSetEquiv n).symm

theorem compositionAsSet_card (n : ℕ) : Fintype.card (CompositionAsSet n) = 2 ^ (n - 1) := by
  have : Fintype.card (Finset (Fin (n - 1))) = 2 ^ (n - 1) := by simp
  rw [← this]
  exact Fintype.card_congr (compositionAsSetEquiv n)

namespace CompositionAsSet

variable (c : CompositionAsSet n)

theorem boundaries_nonempty : c.boundaries.Nonempty :=
  ⟨0, c.zero_mem⟩

theorem card_boundaries_pos : 0 < Finset.card c.boundaries :=
  Finset.card_pos.mpr c.boundaries_nonempty

/-- Number of blocks in a `CompositionAsSet`. -/
def length : ℕ :=
  Finset.card c.boundaries - 1

theorem card_boundaries_eq_succ_length : c.boundaries.card = c.length + 1 :=
  (tsub_eq_iff_eq_add_of_le (Nat.succ_le_of_lt c.card_boundaries_pos)).mp rfl

theorem length_lt_card_boundaries : c.length < c.boundaries.card := by
  rw [c.card_boundaries_eq_succ_length]
  exact Nat.lt_add_one _

theorem lt_length (i : Fin c.length) : (i : ℕ) + 1 < c.boundaries.card :=
  lt_tsub_iff_right.mp i.2

theorem lt_length' (i : Fin c.length) : (i : ℕ) < c.boundaries.card :=
  lt_of_le_of_lt (Nat.le_succ i) (c.lt_length i)

/-- Canonical increasing bijection from `Fin c.boundaries.card` to `c.boundaries`. -/
def boundary : Fin c.boundaries.card ↪o Fin (n + 1) :=
  c.boundaries.orderEmbOfFin rfl

@[simp]
theorem boundary_zero : (c.boundary ⟨0, c.card_boundaries_pos⟩ : Fin (n + 1)) = 0 := by
  rw [boundary, Finset.orderEmbOfFin_zero rfl c.card_boundaries_pos]
  exact le_antisymm (Finset.min'_le _ _ c.zero_mem) (Fin.zero_le _)

@[simp]
theorem boundary_length : c.boundary ⟨c.length, c.length_lt_card_boundaries⟩ = Fin.last n := by
  convert Finset.orderEmbOfFin_last rfl c.card_boundaries_pos
  exact le_antisymm (Finset.le_max' _ _ c.getLast_mem) (Fin.le_last _)

/-- Size of the `i`-th block in a `CompositionAsSet`, seen as a function on `Fin c.length`. -/
def blocksFun (i : Fin c.length) : ℕ :=
  c.boundary ⟨(i : ℕ) + 1, c.lt_length i⟩ - c.boundary ⟨i, c.lt_length' i⟩

theorem blocksFun_pos (i : Fin c.length) : 0 < c.blocksFun i :=
  haveI : (⟨i, c.lt_length' i⟩ : Fin c.boundaries.card) < ⟨i + 1, c.lt_length i⟩ :=
    Nat.lt_succ_self _
  lt_tsub_iff_left.mpr ((c.boundaries.orderEmbOfFin rfl).strictMono this)

/-- List of the sizes of the blocks in a `CompositionAsSet`. -/
def blocks (c : CompositionAsSet n) : List ℕ :=
  ofFn c.blocksFun

@[simp]
theorem blocks_length : c.blocks.length = c.length :=
  length_ofFn

theorem blocks_partial_sum {i : ℕ} (h : i < c.boundaries.card) :
    (c.blocks.take i).sum = c.boundary ⟨i, h⟩ := by
  induction i with
  | zero => simp
  | succ i IH =>
    have A : i < c.blocks.length := by
      rw [c.card_boundaries_eq_succ_length] at h
      simp [blocks, Nat.lt_of_succ_lt_succ h]
    have B : i < c.boundaries.card := lt_of_lt_of_le A (by simp [blocks, length])
    rw [sum_take_succ _ _ A, IH B]
    simp [blocks, blocksFun]

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

theorem blocks_sum : c.blocks.sum = n := by
  have : c.blocks.take c.length = c.blocks := take_of_length_le (by simp [blocks])
  rw [← this, c.blocks_partial_sum c.length_lt_card_boundaries, c.boundary_length]
  rfl

/-- Associating a `Composition n` to a `CompositionAsSet n`, by registering the sizes of the
blocks as a list of positive integers. -/
def toComposition : Composition n where
  blocks := c.blocks
  blocks_pos := by simp only [blocks, forall_mem_ofFn_iff, blocksFun_pos c, forall_true_iff]
  blocks_sum := c.blocks_sum

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

@[simp]
theorem CompositionAsSet.toComposition_length (c : CompositionAsSet n) :
    c.toComposition.length = c.length := by
  simp [CompositionAsSet.toComposition, Composition.length]

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
    simpa [CompositionAsSet.blocks, length_ofFn,
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

@[simp]
theorem CompositionAsSet.toComposition_blocks (c : CompositionAsSet n) :
    c.toComposition.blocks = c.blocks :=
  rfl

@[simp]
theorem CompositionAsSet.toComposition_boundaries (c : CompositionAsSet n) :
    c.toComposition.boundaries = c.boundaries := by
  ext ⟨j, hj⟩
  simp [c.mem_boundaries_iff_exists_blocks_sum_take_eq, Composition.boundaries,
    c.card_boundaries_eq_succ_length, Composition.boundary, Composition.sizeUpTo, Fin.exists_iff]

@[simp]
theorem Composition.toCompositionAsSet_boundaries (c : Composition n) :
    c.toCompositionAsSet.boundaries = c.boundaries :=
  rfl

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

instance compositionFintype (n : ℕ) : Fintype (Composition n) :=
  Fintype.ofEquiv _ (compositionEquiv n).symm

theorem composition_card (n : ℕ) : Fintype.card (Composition n) = 2 ^ (n - 1) := by
  rw [← compositionAsSet_card n]
  exact Fintype.card_congr (compositionEquiv n)
