/-
Copyright (c) 2026 Ezequiel Souza dos Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezequiel Souza dos Santos
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Geometry.Group.WordMetric

import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Finite.Range

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
* `Function.HasSuperpolynomialGrowth`: `f` eventually exceeds every polynomial.
* `Function.HasSubexponentialGrowth`: `log f n / n → 0`, stated with natural numbers.
* `Function.HasIntermediateGrowth`: superpolynomial and subexponential growth.
* `Group.Generators.growth_growthEquivalent`: the growth function is independent of the
  finite generating family, up to `GrowthEquivalent`.

## Implementation notes

* `wordBall` is defined via `wordLength`, so it is compatible with the existing word metric API.
* When the index type is finite, `wordBall n` is a finite set, hence `growth n` is the actual
  cardinality.
* Growth comparison uses natural coefficients, which is enough for cardinalities. Open the `Growth`
  locale for the notations `f ≽ᵍ g` and `f ∼ᵍ g`.

## Tags

growth of groups, word ball, geometric group theory
-/

@[expose] public section

open Set

/-- `f` dominates `g` (written `f ≽ᵍ g`) if `g` is bounded by a rescaling of `f`. -/
def Function.GrowthDominates (f g : ℕ → ℕ) : Prop :=
  ∃ C α : ℕ, ∀ n, g n ≤ C * f (α * n)

/-- Two functions are growth-equivalent (written `f ∼ᵍ g`) if each dominates the other. -/
def Function.GrowthEquivalent (f g : ℕ → ℕ) : Prop :=
  f.GrowthDominates g ∧ g.GrowthDominates f

@[inherit_doc Function.GrowthDominates]
scoped[Growth] infix:50 " ≽ᵍ " => Function.GrowthDominates

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

/-- `f` has superpolynomial growth if it eventually exceeds every polynomial bound. -/
def HasSuperpolynomialGrowth (f : ℕ → ℕ) : Prop :=
  ∀ d : ℕ, ∃ n₀, ∀ n ≥ n₀, (n + 1) ^ d < f n

/-- `f` has subexponential growth if `log (f n) / n → 0`. Equivalently, for every `k`
we have `f n ^ k ≤ 2 ^ n` for all sufficiently large `n`. -/
def HasSubexponentialGrowth (f : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ n₀, ∀ n ≥ n₀, f n ^ k ≤ 2 ^ n

/-- `f` has intermediate growth if it is both superpolynomial and subexponential. -/
def HasIntermediateGrowth (f : ℕ → ℕ) : Prop :=
  f.HasSuperpolynomialGrowth ∧ f.HasSubexponentialGrowth

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

variable {G ι ι' : Type*} [Group G] (P : Group.Generators G ι)

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

@[to_additive]
lemma wordLength_wordProd_le_mul {Q : Group.Generators G ι'} {α : ℕ}
    (hα : ∀ j, P.wordLength (Q.val j) ≤ α) (l : List (ι' × Bool)) :
    P.wordLength (Q.wordProd l) ≤ α * l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rcases x with ⟨j, b⟩
    have hj : P.wordLength (cond b (Q.val j) (Q.val j)⁻¹) ≤ α := by
      cases b <;> simpa [wordLength_inv] using hα j
    calc
      P.wordLength (Q.wordProd ((j, b) :: l))
          = P.wordLength (cond b (Q.val j) (Q.val j)⁻¹ * Q.wordProd l) := by
            rw [wordProd_cons]
      _ ≤ P.wordLength (cond b (Q.val j) (Q.val j)⁻¹) + P.wordLength (Q.wordProd l) :=
            P.wordLength_mul_le _ _
      _ ≤ α + α * l.length := Nat.add_le_add hj ih
      _ = α * ((j, b) :: l).length := by simp [Nat.mul_succ, Nat.add_comm]

/-- Any two finite generating families yield comparable word lengths. -/
@[to_additive /-- Any two finite generating families yield comparable word lengths. -/]
lemma exists_mul_le_wordLength [Finite ι'] (Q : Group.Generators G ι') :
    ∃ α, ∀ g, P.wordLength g ≤ α * Q.wordLength g := by
  obtain ⟨α, hα⟩ := (finite_range fun j : ι' ↦ P.wordLength (Q.val j)).bddAbove
  refine ⟨α, fun g ↦ ?_⟩
  obtain ⟨l, hl, rfl⟩ := Q.exists_isGeodesic g
  simpa [hl.eq] using P.wordLength_wordProd_le_mul (fun j ↦ hα ⟨j, rfl⟩) l

/-- The growth function of a finite generating family dominates that of any other finite
generating family. -/
@[to_additive /-- The growth function of a finite generating family dominates that of any other
finite generating family. -/]
lemma growthDominates_growth [Finite ι] [Finite ι'] (Q : Group.Generators G ι') :
    P.growth.GrowthDominates Q.growth := by
  obtain ⟨α, hα⟩ := P.exists_mul_le_wordLength Q
  refine ⟨1, α, fun n ↦ ?_⟩
  rw [one_mul]
  refine ncard_le_ncard (fun g hg ↦ ?_) (P.finite_wordBall (α * n))
  exact (hα g).trans (Nat.mul_le_mul_left α hg)

/-- The growth of a finitely generated group is independent of the finite generating family. -/
@[to_additive /-- The growth of a finitely generated group is independent of the finite generating
family. -/]
theorem growth_growthEquivalent [Finite ι] [Finite ι'] (Q : Group.Generators G ι') :
    P.growth.GrowthEquivalent Q.growth :=
  ⟨P.growthDominates_growth Q, Q.growthDominates_growth P⟩

/-- A generating family has polynomial growth if its growth function does. -/
@[to_additive /-- A generating family has polynomial growth if its growth function does. -/]
def HasPolynomialGrowth : Prop := Function.HasPolynomialGrowth P.growth

/-- A generating family has exponential growth if its growth function does. -/
@[to_additive /-- A generating family has exponential growth if its growth function does. -/]
def HasExponentialGrowth : Prop := Function.HasExponentialGrowth P.growth

/-- A generating family has superpolynomial growth if its growth function does. -/
@[to_additive /-- A generating family has superpolynomial growth if its growth function does. -/]
def HasSuperpolynomialGrowth : Prop := Function.HasSuperpolynomialGrowth P.growth

/-- A generating family has subexponential growth if its growth function does. -/
@[to_additive /-- A generating family has subexponential growth if its growth function does. -/]
def HasSubexponentialGrowth : Prop := Function.HasSubexponentialGrowth P.growth

/-- A generating family has intermediate growth if its growth function does. -/
@[to_additive /-- A generating family has intermediate growth if its growth function does. -/]
def HasIntermediateGrowth : Prop := Function.HasIntermediateGrowth P.growth

end Group.Generators
