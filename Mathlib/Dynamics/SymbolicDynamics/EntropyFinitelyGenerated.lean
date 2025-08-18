/-
Copyright (c) 2025 S. Gangloff. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: S. Gangloff
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fin.VecNotation

import Mathlib.Dynamics.SymbolicDynamics.Basic2

/-!
# Entropy for subshifts via finite shape systems

This file defines a limsup-style **topological entropy** for subshifts over a (multiplicative)
group `G`, measured along a chosen sequence of **finite shapes**. The interface is intentionally
lightweight: we parameterize entropy by a family `F : ℕ → Finset G` with nonempty shapes,
and we also package such families into a small record `WordMetricShapes` intended to model
word-metric balls for a finitely generated group.

The file also provides convenient specializations for `ℤ` and `ℤ^d`, using the standard
segments `[-n,n]` and boxes `[-n,n]^d` (transported to a multiplicative group via
`Multiplicative` to match the right-action convention).

## Main definitions

* `limsupAtTop` : `limsup` of a real sequence along `atTop` (as an `sInf` of eventual upper bounds).
* `entropyAlong X F hF` : entropy of a subshift `X : Subshift A G` along finite shapes
  `F : ℕ → Finset G` with `hF : ∀ n, 0 < (F n).card`, defined as
`limsup ( log (patternCountOn X (F n) + 1) / |F n| )`.

The `+ 1` inside the logarithm avoids `log 0`.

* `WordMetricShapes` : a minimal record consisting of
- `S : Finset G` (a chosen finite generating set, for documentation),
- `F : ℕ → Finset G` (the shapes, e.g. Cayley balls),
- `F_pos : ∀ n, 0 < (F n).card`.
It is purposely small; further axioms (monotonicity, invariance, …) can be added later.

* `entropy_word Y shapes` : entropy of a subshift `Y` along a `WordMetricShapes` family.

## Specializations

* `IntShapes.seg` and `IntShapes.shapesZ` give shapes on `Multiplicative ℤ` corresponding to
the segments `[-n,n]`. `IntShapes.entropy_Z` is the associated entropy.

* `ZdShapes.box` and `ZdShapes.boxMul` give the boxes `[-n,n]^d` on `ℤ^d` and their image in
`Multiplicative (ℤ^d)`. `ZdShapes.shapesZd` and `ZdShapes.entropy_Zd` are the corresponding
shape system and entropy.

## Mathematical remarks

* On **amenable** groups, taking a **Følner sequence** of shapes makes the entropy value
canonical: the limsup is a limit and does not depend on the chosen Følner sequence
(Ornstein–Weiss). This file does not assume amenability; the shape family is an input.

* For general groups, the value may depend on the chosen shapes/generators; hence the API
keeps the shapes explicit.

## Conventions

* We use a **right** action for shifts on configurations: `(shift g x) h = x (h * g)`.
The `ℤ`/`ℤ^d` specializations use `Multiplicative` to align additive intuition with this
right-action convention.

* Counting of patterns on a finite shape uses `patternCountOn` from the basic group-generic
symbolic dynamics file; discreteness/finite-alphabet assumptions are imported there.
-/

noncomputable section
open Set Topology Filter

namespace SymbolicDynamics
namespace FullShift

/-! ## Language on finite shapes -/

variable {A G : Type*}
variable [Group G] [DecidableEq G]
variable [TopologicalSpace A]
variable [DiscreteTopology A]
variable [Fintype A] [DecidableEq A] [Inhabited A]

/-! ## Entropy along arbitrary finite shapes -/

/-- `limsup` along `atTop` as the infimum of eventual upper bounds. -/
noncomputable def limsupAtTop (u : ℕ → ℝ) : ℝ :=
  sInf { L : ℝ | ∀ᶠ n in atTop, u n ≤ L }

/-- Entropy of a subshift `X` along a sequence of finite shapes `F` with nonempty shapes. -/
noncomputable def entropyAlong (X : Subshift A G)
    (F : ℕ → Finset G) (_ : ∀ n, 0 < (F n).card) : ℝ :=
  limsupAtTop (fun n =>
    Real.log (patternCountOn (A:=A) (G:=G) X (F n) + 1) / ((F n).card : ℝ))

/-! ## Word-metric style shape systems for finitely generated groups -/

/-- A minimal interface for a word-metric shape system (e.g. Cayley balls).
We keep only what we need for `entropy_word`: a sequence of finite shapes and their
nonemptiness. More axioms (monotonicity, invariance properties) can be added later. -/
structure WordMetricShapes (G : Type*) [Group G] [DecidableEq G] where
  (S : Finset G)              -- chosen finite generating set (intended symmetric)
  (F : ℕ → Finset G)          -- shapes, e.g. word-metric balls
  (F_pos : ∀ n, 0 < (F n).card) -- nonempty shapes

/-- Entropy of a subshift along a given word-metric shape system. -/
noncomputable def entropy_word [DecidableEq G]
    (Y : Subshift A G) (shapes : WordMetricShapes G) : ℝ :=
  entropyAlong (A:=A) (G:=G) Y shapes.F shapes.F_pos

/-! ## Specializations: `ℤ` and `ℤ^d` -/

namespace IntShapes
/-- Segments `[-n,n]` as shapes in `Multiplicative ℤ`. -/
def seg (n : ℕ) : Finset (Multiplicative ℤ) :=
    (Finset.Icc (-(n : ℤ)) (n : ℤ)).image Multiplicative.ofAdd

lemma seg_card_pos (n : ℕ) : 0 < (seg n).card := by
    classical
    have h0 : (0 : ℤ) ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      have h1 : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      have h2 : -(n : ℤ) ≤ 0 := by simp [neg_nonpos.mpr h1]
      simp [Finset.mem_Icc]
    refine Finset.card_pos.mpr ?_
    exact ⟨Multiplicative.ofAdd 0, Finset.mem_image.mpr ⟨0, h0, rfl⟩⟩

/-- Word-metric style shapes for `ℤ`. -/
def shapesZ : WordMetricShapes (Multiplicative ℤ) :=
  { S      := {Multiplicative.ofAdd (1 : ℤ), Multiplicative.ofAdd (-1 : ℤ)}
  , F      := seg
  , F_pos  := seg_card_pos }

/-- Entropy on `ℤ` with standard segments. -/
noncomputable def entropy_Z (Y : Subshift A (Multiplicative ℤ)) : ℝ :=
    entropy_word (A:=A) (G:=Multiplicative ℤ) Y shapesZ
end IntShapes

namespace ZdShapes

variable {d : ℕ}

/-- The lattice `ℤ^d` as functions `Fin d → ℤ`. -/
abbrev Zd (d : ℕ) := Fin d → ℤ


def box (d : ℕ) (n : ℕ) : Finset (Zd d) :=
    Fintype.piFinset (fun _ => Finset.Icc (-(n : ℤ)) (n : ℤ))

/-- Boxes transported to the multiplicative copy to fit the generic `G`. -/
def boxMul (d : ℕ) (n : ℕ) : Finset (Multiplicative (Zd d)) :=
    (box d n).image Multiplicative.ofAdd

lemma box_card_pos (d n : ℕ) : 0 < (box d n).card := by
    classical
    have hcoord : ∀ i : Fin d, (0 : ℤ) ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      intro i
      have h1 : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      have h2 : -(n : ℤ) ≤ 0 := by simp [neg_nonpos.mpr h1]
      simp [Finset.mem_Icc]
    have h0 : (fun _ : Fin d => (0 : ℤ)) ∈ box d n := Fintype.mem_piFinset.mpr hcoord
    exact Finset.card_pos.mpr ⟨_, h0⟩

lemma boxMul_card_pos (d n : ℕ) : 0 < (boxMul d n).card := by
    classical
    rcases Finset.card_pos.mp (box_card_pos d n) with ⟨z, hz⟩
    refine Finset.card_pos.mpr ?_
    exact ⟨Multiplicative.ofAdd z, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩

/-- Word-metric style shapes for `ℤ^d` using boxes. -/
def shapesZd (d : ℕ) : WordMetricShapes (Multiplicative (Zd d)) :=
  { S      :=
      -- ±e_j generators (not used by `entropy_word`, included for completeness)
      (Finset.univ.image (fun j : Fin d => Multiplicative.ofAdd
          (fun k => if k = j then (1 : ℤ) else 0))) ∪
      (Finset.univ.image (fun j : Fin d => Multiplicative.ofAdd
          (fun k => if k = j then (-1 : ℤ) else 0)))
  , F      := fun n => boxMul d n
  , F_pos  := boxMul_card_pos d }

/-- Entropy on `ℤ^d` with standard boxes. -/
noncomputable def entropy_Zd (Y : Subshift A (Multiplicative (Zd d))) : ℝ :=
    entropy_word (A:=A) (G:=Multiplicative (Zd d)) Y (shapesZd d)
end ZdShapes

end FullShift
end SymbolicDynamics
