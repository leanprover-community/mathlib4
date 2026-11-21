/-
Copyright (c) 2026 Ezequiel Souza dos Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezequiel Souza dos Santos
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Geometry.Group.WordMetric

import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Finite.Range
import Mathlib.Order.Lattice.Nat

/-!
# Growth function of a finitely generated group

The growth of a group `G` with respect to a generating family `P` is the function sending `n` to
the number of elements of word length at most `n`.

## Main definitions

* `Group.Generators.wordBall`: the closed ball of radius `n` in the word metric.
* `Group.Generators.growth`: the growth function `n ↦ #(wordBall n)`.
* `Function.GrowthDominates`: `f` dominates `g` if `g n ≤ C * f (α * n)` for some `C, α`.
* `Function.GrowthEquivalent`: mutual domination of two functions.
* `Group.Generators.growth_growthEquivalent`: the growth function is independent of the
  finite generating family, up to `GrowthEquivalent`.

## Implementation notes

* `wordBall` is defined via `wordLength`, so it is compatible with the existing word metric API.
* When the index type is finite, `wordBall n` is a finite set, hence `growth n` is the actual
  cardinality.
* Growth comparison uses a multiplicative constant and a linear rescaling of the argument. Open
  the `Growth` locale for the notations `f ≽ᵍ g` and `f ∼ᵍ g`.

## Tags

growth of groups, word ball, geometric group theory
-/

@[expose] public section

open Set

namespace Function

/-- `f` dominates `g` (written `f ≽ᵍ g`) if `g` is bounded by a constant multiple of a
rescaling of `f`. -/
def GrowthDominates (f g : ℕ → ℕ) : Prop :=
  ∃ C α : ℕ, ∀ n, g n ≤ C * f (α * n)

/-- Two functions are growth-equivalent (written `f ∼ᵍ g`) if each dominates the other. -/
def GrowthEquivalent (f g : ℕ → ℕ) : Prop :=
  f.GrowthDominates g ∧ g.GrowthDominates f

namespace GrowthDominates

lemma refl (f : ℕ → ℕ) : f.GrowthDominates f :=
  ⟨1, 1, by simp⟩

lemma trans {f g h : ℕ → ℕ} (hfg : f.GrowthDominates g)
    (hgh : g.GrowthDominates h) : f.GrowthDominates h := by
  obtain ⟨C₁, α₁, h₁⟩ := hfg
  obtain ⟨C₂, α₂, h₂⟩ := hgh
  refine ⟨C₂ * C₁, α₁ * α₂, fun n ↦ ?_⟩
  grw [h₂ n, h₁ (α₂ * n), mul_assoc, mul_assoc]

end GrowthDominates

namespace GrowthEquivalent

lemma refl (f : ℕ → ℕ) : f.GrowthEquivalent f :=
  ⟨.refl f, .refl f⟩

lemma symm {f g : ℕ → ℕ} (h : f.GrowthEquivalent g) : g.GrowthEquivalent f :=
  ⟨h.2, h.1⟩

lemma trans {f g h : ℕ → ℕ} (hfg : f.GrowthEquivalent g)
    (hgh : g.GrowthEquivalent h) : f.GrowthEquivalent h :=
  ⟨hfg.1.trans hgh.1, hgh.2.trans hfg.2⟩

end GrowthEquivalent

end Function

@[inherit_doc Function.GrowthDominates]
scoped[Growth] infix:50 " ≽ᵍ " => Function.GrowthDominates

@[inherit_doc Function.GrowthEquivalent]
scoped[Growth] infix:50 " ∼ᵍ " => Function.GrowthEquivalent

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
  simp [P.wordLength_le_iff]

@[to_additive]
lemma one_mem_wordBall (n : ℕ) : 1 ∈ P.wordBall n := by
  simp

@[to_additive (attr := simp)]
lemma wordBall_zero : P.wordBall 0 = {1} := by
  ext g
  simp

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
  simp [growth_eq_ncard]

@[to_additive]
lemma monotone_growth [Finite ι] : Monotone P.growth := by
  intro m n hmn
  refine ncard_le_ncard (fun g hg ↦ ?_) (P.finite_wordBall n)
  exact hg.trans hmn

@[to_additive]
lemma exists_one_lt_growth [Infinite G] [Finite ι] : ∃ n, 1 < P.growth n := by
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  refine ⟨P.wordLength g, ?_⟩
  have hsubset : ({1, g} : Set G) ⊆ P.wordBall (P.wordLength g) := by
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact P.one_mem_wordBall _
    · simp [wordBall]
  have : 2 ≤ ({1, g} : Set G).ncard := by
    rw [ncard_insert_of_notMem (by simp [hg.symm]), ncard_singleton]
  exact lt_of_lt_of_le (by decide : 1 < 2)
    (this.trans (ncard_le_ncard hsubset (P.finite_wordBall _)))

/-- The growth function of an infinite finitely generated group is unbounded. -/
@[to_additive]
lemma exists_lt_growth [Infinite G] [Finite ι] (N : ℕ) : ∃ n, N < P.growth n := by
  by_contra! h
  have hr : (Set.range P.growth).Nonempty := ⟨P.growth 0, 0, rfl⟩
  have hf : (Set.range P.growth).Finite :=
    (Set.finite_Iic N).subset fun x hx ↦ by
      obtain ⟨n, rfl⟩ := hx
      exact h n
  obtain ⟨n, hn⟩ : ∃ n, P.growth n = sSup (Set.range P.growth) := by
    have : sSup (Set.range P.growth) ∈ Set.range P.growth := Nat.sSup_mem hr hf.bddAbove
    simpa [Set.mem_range] using this
  have hEq : ∀ m ≥ n, P.wordBall m = P.wordBall n := by
    intro m hm
    refine (eq_of_subset_of_ncard_le (fun g hg ↦ (hg : P.wordLength g ≤ n).trans hm)
      ?_ (P.finite_wordBall m)).symm
    have hle : P.growth m ≤ P.growth n := by
      rw [hn]
      exact le_csSup hf.bddAbove ⟨m, rfl⟩
    have hge : P.growth n ≤ P.growth m := P.monotone_growth hm
    simpa [growth] using (hle.antisymm hge).le
  have huniv : (Set.univ : Set G) = P.wordBall n := by
    ext g
    constructor
    · intro _
      by_cases hg : P.wordLength g ≤ n
      · exact hg
      · have : g ∈ P.wordBall (P.wordLength g) := by simp [wordBall]
        rwa [hEq _ (le_of_not_ge hg)] at this
    · intro; trivial
  have hfin : (Set.univ : Set G).Finite := huniv ▸ P.finite_wordBall n
  exact hfin.not_infinite Set.infinite_univ

@[to_additive]
lemma wordLength_le_mul {Q : Group.Generators G ι'} {α : ℕ}
    (hα : ∀ j, P.wordLength (Q.val j) ≤ α) (g : G) :
    P.wordLength g ≤ α * Q.wordLength g := by
  obtain ⟨l, hl, rfl⟩ := Q.exists_isGeodesic g
  rw [hl.eq]
  clear hl
  induction l with
  | nil => simp
  | cons x l ih =>
    grw [← List.singleton_append, wordProd_append, wordLength_mul_le, ih, List.length_append]
    rcases x with ⟨j, _ | _⟩ <;> simpa [mul_one_add] using hα j

/-- Any two finite generating families yield comparable word lengths. -/
@[to_additive /-- Any two finite generating families yield comparable word lengths. -/]
lemma exists_mul_le_wordLength [Finite ι'] (Q : Group.Generators G ι') :
    ∃ α, ∀ g, P.wordLength g ≤ α * Q.wordLength g := by
  obtain ⟨α, hα⟩ := Finite.exists_le fun j ↦ P.wordLength (Q.val j)
  exact ⟨α, wordLength_le_mul P hα⟩

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
  rw [mem_wordBall] at hg ⊢
  grw [hα, hg]

/-- The growth of a finitely generated group is independent of the finite generating family. -/
@[to_additive /-- The growth of a finitely generated group is independent of the finite generating
family. -/]
theorem growth_growthEquivalent [Finite ι] [Finite ι'] (Q : Group.Generators G ι') :
    P.growth.GrowthEquivalent Q.growth :=
  ⟨P.growthDominates_growth Q, Q.growthDominates_growth P⟩

end Group.Generators
