/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot, Yury Kudryashov
-/
import Mathlib.Topology.Defs.Filter

open Set Filter
open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The sequential closure of a set `s : Set X` in a topological space `X` is the set of all `a : X`
which arise as limit of sequences in `s`. Note that the sequential closure of a set is not
guaranteed to be sequentially closed. -/
def seqClosure (s : Set X) : Set X :=
  { a | ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ Tendsto x atTop (𝓝 a) }
#align seq_closure seqClosure

/-- A set `s` is sequentially closed if for any converging sequence `x n` of elements of `s`, the
limit belongs to `s` as well. Note that the sequential closure of a set is not guaranteed to be
sequentially closed. -/
def IsSeqClosed (s : Set X) : Prop :=
  ∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, (∀ n, x n ∈ s) → Tendsto x atTop (𝓝 p) → p ∈ s
#align is_seq_closed IsSeqClosed

/-- A function between topological spaces is sequentially continuous if it commutes with limit of
 convergent sequences. -/
def SeqContinuous (f : X → Y) : Prop :=
  ∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, Tendsto x atTop (𝓝 p) → Tendsto (f ∘ x) atTop (𝓝 (f p))
#align seq_continuous SeqContinuous

/-- A set `s` is sequentially compact if every sequence taking values in `s` has a
converging subsequence. -/
def IsSeqCompact (s : Set X) :=
  ∀ ⦃x : ℕ → X⦄, (∀ n, x n ∈ s) → ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)
#align is_seq_compact IsSeqCompact

variable (X)

/-- A space `X` is sequentially compact if every sequence in `X` has a
converging subsequence. -/
@[mk_iff]
class SeqCompactSpace : Prop where
  seq_compact_univ : IsSeqCompact (univ : Set X)
#align seq_compact_space SeqCompactSpace
#align seq_compact_space_iff seqCompactSpace_iff

export SeqCompactSpace (seq_compact_univ)

/-- A topological space is called a *Fréchet-Urysohn space*, if the sequential closure of any set
is equal to its closure. Since one of the inclusions is trivial, we require only the non-trivial one
in the definition. -/
class FrechetUrysohnSpace : Prop where
  closure_subset_seqClosure : ∀ s : Set X, closure s ⊆ seqClosure s
#align frechet_urysohn_space FrechetUrysohnSpace

/-- A topological space is said to be a *sequential space* if any sequentially closed set in this
space is closed. This condition is weaker than being a Fréchet-Urysohn space. -/
class SequentialSpace : Prop where
  isClosed_of_seq : ∀ s : Set X, IsSeqClosed s → IsClosed s
#align sequential_space SequentialSpace

variable {X}

/-- In a sequential space, a sequentially closed set is closed. -/
protected theorem IsSeqClosed.isClosed [SequentialSpace X] {s : Set X} (hs : IsSeqClosed s) :
    IsClosed s :=
  SequentialSpace.isClosed_of_seq s hs
#align is_seq_closed.is_closed IsSeqClosed.isClosed
