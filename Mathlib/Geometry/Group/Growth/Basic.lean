/-
Copyright (c) 2026 Ezequiel Souza dos Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezequiel Souza dos Santos
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Geometry.Group.WordMetric

import Mathlib.Data.Set.Finite.List

/-!
# Growth function of a finitely generated group

The growth of a group `G` with respect to a generating family `P` is the function sending `n` to
the number of elements of word length at most `n`.

## Main definitions

* `Group.Generators.wordBall`: the closed ball of radius `n` in the word metric.
* `Group.Generators.growth`: the growth function `n ↦ #(wordBall n)`.
* `Function.GrowthDominates`: `f` dominates `g` if `g n ≤ C * f (α * n)` for some `C, α`.
* `Function.GrowthEquivalent`: mutual domination of two functions.
* `Function.HasPolynomialGrowth`: `f` is dominated by `n ↦ (n + 1)^d` for some `d`.
* `Function.HasExponentialGrowth`: `f` dominates `n ↦ 2^n`.

## Implementation notes

* `wordBall` is defined via `wordLength`, so it is compatible with the existing word metric API.
* When the index type is finite, `wordBall n` is a finite set, hence `growth n` is the actual
  cardinality.
* Growth comparison uses natural coefficients, which is enough for cardinalities. Open the `Growth`
  locale for the notations `f ⪰ᵍ g` and `f ∼ᵍ g`.

## Tags

growth of groups, word ball, geometric group theory
-/

@[expose] public section

open Set

/-- `f` dominates `g` (written `f ⪰ᵍ g`) if `g` is bounded by a rescaling of `f`. -/
def Function.GrowthDominates (f g : ℕ → ℕ) : Prop :=
  ∃ C α : ℕ, ∀ n, g n ≤ C * f (α * n)

/-- Two functions are growth-equivalent (written `f ∼ᵍ g`) if each dominates the other. -/
def Function.GrowthEquivalent (f g : ℕ → ℕ) : Prop :=
  f.GrowthDominates g ∧ g.GrowthDominates f

@[inherit_doc Function.GrowthDominates]
scoped[Growth] infix:50 " ⪰ᵍ " => Function.GrowthDominates

@[inherit_doc Function.GrowthEquivalent]
scoped[Growth] infix:50 " ∼ᵍ " => Function.GrowthEquivalent

namespace Function

lemma GrowthDominates.refl (f : ℕ → ℕ) : f.GrowthDominates f :=
  ⟨1, 1, by simp⟩

lemma GrowthDominates.trans {f g h : ℕ → ℕ} (hfg : f.GrowthDominates g)
    (hgh : g.GrowthDominates h) : f.GrowthDominates h := by
  obtain ⟨C₁, α₁, h₁⟩ := hfg
  obtain ⟨C₂, α₂, h₂⟩ := hgh
  refine ⟨C₂ * C₁, α₁ * α₂, fun n ↦ ?_⟩
  grw [h₂ n, h₁ (α₂ * n), mul_assoc, mul_assoc]

lemma GrowthEquivalent.refl (f : ℕ → ℕ) : f.GrowthEquivalent f :=
  ⟨.refl f, .refl f⟩

lemma GrowthEquivalent.symm {f g : ℕ → ℕ} (h : f.GrowthEquivalent g) : g.GrowthEquivalent f :=
  ⟨h.2, h.1⟩

lemma GrowthEquivalent.trans {f g h : ℕ → ℕ} (hfg : f.GrowthEquivalent g)
    (hgh : g.GrowthEquivalent h) : f.GrowthEquivalent h :=
  ⟨hfg.1.trans hgh.1, hgh.2.trans hfg.2⟩

lemma GrowthEquivalent.equivalence : Equivalence GrowthEquivalent :=
  ⟨GrowthEquivalent.refl, GrowthEquivalent.symm, GrowthEquivalent.trans⟩

/-- `f` has polynomial growth if it is dominated by `n ↦ (n + 1) ^ d` for some `d`.
We use `n + 1` so that the bound is positive at `n = 0`. -/
def HasPolynomialGrowth (f : ℕ → ℕ) : Prop :=
  ∃ d : ℕ, (fun n ↦ (n + 1) ^ d).GrowthDominates f

/-- `f` has exponential growth if it dominates `n ↦ 2 ^ n`. -/
def HasExponentialGrowth (f : ℕ → ℕ) : Prop :=
  f.GrowthDominates (2 ^ ·)

lemma HasPolynomialGrowth.of_growthDominates {f g : ℕ → ℕ} (hf : f.HasPolynomialGrowth)
    (hfg : f.GrowthDominates g) : g.HasPolynomialGrowth :=
  hf.imp fun _ hd ↦ hd.trans hfg

lemma HasPolynomialGrowth.of_growthEquivalent {f g : ℕ → ℕ} (h : f.GrowthEquivalent g)
    (hf : f.HasPolynomialGrowth) : g.HasPolynomialGrowth :=
  hf.of_growthDominates h.1

lemma HasExponentialGrowth.of_growthDominates {f g : ℕ → ℕ} (hf : f.HasExponentialGrowth)
    (hgf : g.GrowthDominates f) : g.HasExponentialGrowth :=
  hgf.trans hf

lemma HasExponentialGrowth.of_growthEquivalent {f g : ℕ → ℕ} (h : f.GrowthEquivalent g)
    (hf : f.HasExponentialGrowth) : g.HasExponentialGrowth :=
  hf.of_growthDominates h.2

end Function

namespace Group.Generators

variable {G ι : Type*} [Group G] (P : Group.Generators G ι)

/-- The closed ball of radius `n` in the word metric: elements of word length at most `n`. -/
@[to_additive /-- The closed ball of radius `n` in the word metric: elements of word length at most
`n`. -/]
def wordBall (n : ℕ) : Set G := {g | P.wordLength g ≤ n}

@[to_additive (attr := simp)]
lemma mem_wordBall {n : ℕ} {g : G} : g ∈ P.wordBall n ↔ P.wordLength g ≤ n :=
  Iff.rfl

@[to_additive]
lemma wordBall_eq_image (n : ℕ) :
    P.wordBall n = P.wordProd '' {l : List (ι × Bool) | l.length ≤ n} := by
  ext g
  simp [mem_image, P.wordLength_le_iff]

@[to_additive]
lemma one_mem_wordBall (n : ℕ) : 1 ∈ P.wordBall n := by
  simp

@[to_additive (attr := simp)]
lemma wordBall_zero : P.wordBall 0 = {1} := by
  ext g
  simp [wordLength_eq_zero_iff]

/-- If the generating family is finite, then the word ball of any finite radius is finite. -/
@[to_additive /-- If the generating family is finite, then the word ball of any finite radius is
finite. -/]
lemma finite_wordBall [Finite ι] (n : ℕ) : (P.wordBall n).Finite := by
  rw [wordBall_eq_image]
  exact (List.finite_length_le (ι × Bool) n).image _

/-- The growth function of `G` with respect to the generating family `P`: the number of elements
of word length at most `n`. -/
@[to_additive /-- The growth function of `G` with respect to the generating family `P`: the number
of elements of word length at most `n`. -/]
noncomputable def growth (n : ℕ) : ℕ := (P.wordBall n).ncard

@[to_additive]
lemma growth_eq_ncard (n : ℕ) : P.growth n = (P.wordBall n).ncard :=
  rfl

@[to_additive (attr := simp)]
lemma growth_zero : P.growth 0 = 1 := by
  simp [growth]

/-- A generating family has polynomial growth if its growth function does. -/
@[to_additive /-- A generating family has polynomial growth if its growth function does. -/]
def HasPolynomialGrowth : Prop := Function.HasPolynomialGrowth P.growth

/-- A generating family has exponential growth if its growth function does. -/
@[to_additive /-- A generating family has exponential growth if its growth function does. -/]
def HasExponentialGrowth : Prop := Function.HasExponentialGrowth P.growth

end Group.Generators
