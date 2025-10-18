/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Finsupp.Basic
import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# Conical combinations

A conical combination is a finite linear combination with nonnegative coefficients,
which in the current file is expressed using `Finsupp.linearCombination`. This file contains
various basic results about conical combinations and their closure properties.
Conical combinations naturally define pointed cones (convex cones that include zero).
We prove some results about the (extensional) equivalence
of PointedCone.span and conical combinations.

## Basic lemmas about conical combinations

* `conicalCombination_zero`: zero can be expressed as a conical combination
* `conicalCombination_generator`: an element of the generator set is itself a conical combination
* `conicalCombination_smul`: a scalar multiple of a conical combination is a conical combination
* `conicalCombination_add`: the sum of two conical combinations is a conical combination

## Main results

* `mem_span_iff_conicalCombination`: Any x ∈ PointedCone.span R s are expressible as conical
  combinations from s.
* `span_eq_setOf_conicalCombination`: PointedCone.span R s is equal to the set of
all conical combinations from s.
* `conicalCombination_of_subset_mem`: A pointed cone contains all conical combinations from
  an arbitrary subset.
* `span_minimal`: `PointedCone.span R s` is contained in any pointed cone containing `s`
* `span_eq_sInf`: `PointedCone.span R s` equals the infimum of all pointed cones containing `s`
* `of_conicalCombination`: generates a PointedCone from a set closed under two-element conical
  combinations
* `conicalCombination_mem`: a pointed cone contains all two element conical combinations

## Notation

 - no special notation defined

## Implementation notes

* This could be implemented as Fin n, Finset, and Finsupp. Finsupp seems to be a reasonable
  compromise between abstraction and ease of manipulation.
* The expression
`∃ f : s →₀ R, (∀ v, 0 ≤ f v) ∧ x = Finsupp.linearCombination R (Subtype.val : s → E) f`:
states that the vector `x` can be expressed as a finite conical combination
(i.e., a finite linear combination of with nonnegative coefficients)
of elements from the set `s` (of vectors), with nonnegative scalar
coefficients f vᵢ from `R` (indexed by vᵢ ∈ s).


## References

 - https://en.wikipedia.org/wiki/Conical_combination
 - Leonard et al. - Geometry of convex sets

-/

variable (R : Type*) [Semiring R] [PartialOrder R]
variable {E : Type*} [AddCommMonoid E] [Module R E]
namespace ConicalCombination
section ConicalCombinationSection

/-- Zero can be expressed as a conical combination -/
theorem conicalCombination_zero (s : Set E) :
    ∃ f : s →₀ R, (∀ v, 0 ≤ f v) ∧
      0 = Finsupp.linearCombination R (Subtype.val : s → E) f :=
  ⟨0, fun _ => le_refl 0, by simp⟩

variable [IsOrderedRing R]

/-- The individual elements of a generator set are themselves trivial conical combinations. -/
theorem conicalCombination_generator {s : Set E} {v : E} (h_mem : v ∈ s) :
    ∃ f : s →₀ R, (∀ v, 0 ≤ f v) ∧
      v = Finsupp.linearCombination R (Subtype.val : s → E) f := by
  refine ⟨Finsupp.single ⟨v, h_mem⟩ 1, fun w => ?_, by simp [Finsupp.linearCombination_single]⟩
  rcases eq_or_ne w ⟨v, h_mem⟩ with rfl | h
  · simp
  · simp [h]

/-- A scalar multiple of a conical combination is a conical combination. -/
theorem conicalCombination_smul (s : Set E) (c : R) (h : 0 ≤ c) (v : E)
    (h_conicalcomb : ∃ f : s →₀ R, (∀ v, 0 ≤ f v) ∧
      v = Finsupp.linearCombination R (Subtype.val : s → E) f) :
    ∃ f : s →₀ R, (∀ v, 0 ≤ f v) ∧
      c • v = Finsupp.linearCombination R (Subtype.val : s → E) f := by
  rcases h_conicalcomb with ⟨f, hf_nonneg, rfl⟩
  exact ⟨c • f, fun w => mul_nonneg h (hf_nonneg w), by simp⟩

/-- Adding two conical combinations produces a new conical combination. -/
theorem conicalCombination_add (s : Set E) (x₁ x₂ : E)
    (h₁ : ∃ f : s →₀ R, (∀ v, 0 ≤ f v) ∧
      x₁ = Finsupp.linearCombination R (Subtype.val : s → E) f)
    (h₂ : ∃ f : s →₀ R, (∀ v, 0 ≤ f v) ∧
      x₂ = Finsupp.linearCombination R (Subtype.val : s → E) f) :
    ∃ f : s →₀ R, (∀ v, 0 ≤ f v) ∧
      x₁ + x₂ = Finsupp.linearCombination R (Subtype.val : s → E) f := by
  obtain ⟨f₁, hf₁_nonneg, hf₁_eq⟩ := h₁
  obtain ⟨f₂, hf₂_nonneg, hf₂_eq⟩ := h₂
  use f₁ + f₂
  constructor
  · intro v
    simp only [Finsupp.add_apply]
    exact add_nonneg (hf₁_nonneg v) (hf₂_nonneg v)
  · rw [hf₁_eq, hf₂_eq, ← map_add]

end ConicalCombinationSection
end ConicalCombination

/- The following deals results about the (extensional) equivalence
of PointedCone.span and conical combinations. -/

namespace PointedCone
open ConicalCombination

section PointedConeSection
variable [IsOrderedRing R]

/-- Elements of PointedCone.span R s are expressible as conical combination of elements from s. -/
theorem mem_span_iff_conicalCombination (s : Set E) (x : E) :
    x ∈ PointedCone.span R s ↔
      ∃ f : s →₀ R, (∀ v, 0 ≤ f v) ∧
        x = (Finsupp.linearCombination R (Subtype.val : s → E)) f := by
  constructor
  · -- if in the span then equal to nonnegative linear combination of elements of `s`.
    intro hx
    rw [Finsupp.mem_span_iff_linearCombination] at hx
    rcases hx with ⟨l, rfl⟩
    refine ⟨l.mapRange (↑) (by simp), (fun v => (l v).property), ?_⟩
    simp [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index]
  · -- nonnegative linear combinations are in the span.
    rintro ⟨f, hf_nonneg, rfl⟩
    rw [Finsupp.linearCombination_apply]
    apply AddSubmonoid.sum_mem
    intro v hv
    exact (PointedCone.span R s).smul_mem' ⟨f v, hf_nonneg v⟩ (PointedCone.subset_span v.property)

/-- Corollary: The PointedCone.span equals the set of all conical combinations. -/
theorem span_eq_setOf_conicalCombination (s : Set E) :
    (PointedCone.span R s : Set E) =
      {x | ∃ f : s →₀ R, (∀ v, 0 ≤ f v) ∧
        x = (Finsupp.linearCombination R (Subtype.val : s → E)) f} :=
  Set.ext fun x => mem_span_iff_conicalCombination R s x

/-- A pointed cone contains all conical combinations of elements from arbitrary subset. -/
theorem conicalCombination_of_subset_mem (C : PointedCone R E) (s : Set E) (hs : s ⊆ C.carrier)
    (f : s →₀ R) (h_nonneg : ∀ v, 0 ≤ f v) :
    Finsupp.linearCombination R (Subtype.val : s → E) f ∈ C := by
  rw [Finsupp.linearCombination_apply]
  apply AddSubmonoid.sum_mem
  intro v hv
  exact C.smul_mem' ⟨f v, h_nonneg v⟩ (hs v.property)

/-- PointedCone.span R s is contained in any pointed cone C that contains s. -/
theorem span_minimal (C : PointedCone R E) (s : Set E) (hs : s ⊆ C.carrier) :
    (PointedCone.span R s : Set E) ⊆ C.carrier := by
  intro x hx
  have h := (mem_span_iff_conicalCombination R s x).mp hx
  obtain ⟨f, hf_nonneg, hf_eq⟩ := h
  rw [hf_eq]
  exact conicalCombination_of_subset_mem R C s hs f hf_nonneg

/-- Corollary: `PointedCone.span R s` is equal to the infimum of all pointed cones containing s. -/
theorem span_eq_sInf (s : Set E) :
    PointedCone.span R s = sInf {C : PointedCone R E | s ⊆ C.carrier} := by
  rfl

/-- Construct a pointed cone from closure under two-element conical combinations.
I.e., a nonempty set closed under two-element conical combinations is a pointed cone. -/
def of_conicalCombination {E : Type*} [AddCommMonoid E] [Module R E]
    (C : Set E) (h_nonempty : C.Nonempty)
    (h_conecomb : ∀ (x : E), x ∈ C → ∀ (y : E), y ∈ C → ∀ (a b : R),
      0 ≤ a → 0 ≤ b → a • x + b • y ∈ C) :
    PointedCone R E where
  carrier := C
  zero_mem' := by
    obtain ⟨x, hx⟩ := h_nonempty
    simpa [zero_smul, add_zero] using h_conecomb x hx x hx 0 0 (le_refl _) (le_refl _)
  add_mem' := by
    intro x y hx hy
    simpa [one_smul] using h_conecomb x hx y hy 1 1 zero_le_one zero_le_one
  smul_mem' := by
    intro c x hx
    have := h_conecomb x hx x hx (c : R) 0 c.property (le_refl 0)
    simp_all

/-- A pointed cone contains all two-element conical combinations. -/
theorem conicalCombination_mem (T : PointedCone R E) {x y : E}
    (hx : x ∈ T.carrier) (hy : y ∈ T.carrier) {a b : R}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • x + b • y ∈ T.carrier :=
  T.add_mem' (T.smul_mem' ⟨a, ha⟩ hx) (T.smul_mem' ⟨b, hb⟩ hy)

end PointedConeSection
end PointedCone
