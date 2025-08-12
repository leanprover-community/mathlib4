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

A conical combination is characterized by nonnegative coefficients. This file contains
various basic results about conical combinations and their closure properties.
Conical combinations naturally define pointed cones (convex cones that include zero).

## Main definitions

* `IsConicalCombination R s x`: `x` can be expressed as a conical combination
  of elements from the set `s`, with nonnegative coefficients from `R`.

## Basic lemmas about conical combinations

* `conicalCombination_zero`: zero can be expressed as a conical combination
* `conicalCombination_generator`: an element of the generator set is itself a conical combination
* `conicalCombination_smul`: a scalar multiple of a conical combination is a conical combination
* `conicalCombination_add`: the sum of two conical combinations is a conical combination

## Main results

* `mem_span_iff_conicalCombination`: `x ∈ PointedCone.span R s ↔ IsConicalCombination R s x`
* `span_eq_setOf_conicalCombination`: `PointedCone.span R s = {x | IsConicalCombination R s x}`
* `conicalCombination_mem`: A pointed cone contains all conical combinations from any given subset.
* `span_minimal`: `PointedCone.span R s` is contained in any pointed cone containing `s`
* `span_eq_sInf`: `PointedCone.span R s` equals the infimum of all pointed cones containing `s`
* `pointedCone_iff_forall_nonneg`: a set is a pointed cone iff it is nonempty
and contains all two element conical combinations

## Notation

 - no special notation defined

## Implementation notes

 - This could be implemented as Fin n, Finset, and Finsupp. Finsupp seems to be a reasonable
  compromise between abstraction and ease of manipulation.

## References

 - https://en.wikipedia.org/wiki/Conical_combination
 - Leonard et al. - Geometry of convex sets

-/

variable (R : Type*) [Semiring R] [PartialOrder R]
variable {E : Type*} [AddCommMonoid E] [Module R E]
namespace ConicalCombination
section ConicalCombinationSection

/-- Predicate stating that an element can be expressed as a conical combination using elements
 from the set s. A conical combination is characterized by nonnegative coefficients. -/
def IsConicalCombination (s : Set E) (x : E) : Prop :=
  ∃ f : s →₀ R,
    (∀ v, 0 ≤ f v) ∧
      x = (Finsupp.linearCombination R (Subtype.val : s → E)) f

/-- Zero can be expressed as a conical combination -/
theorem conicalCombination_zero (s : Set E) : IsConicalCombination R s 0 :=
  ⟨0, fun _ => le_refl 0, by simp⟩

variable [IsOrderedRing R]

/-- The individual elements of a generator set are themselves trivial conical combinations. -/
theorem conicalCombination_generator {s : Set E} {v : E} (h_mem : v ∈ s) :
    IsConicalCombination R s v := by classical
  exact ⟨Finsupp.single ⟨v, h_mem⟩ 1,
    fun w => by
      simp only [Finsupp.single_apply]
      split_ifs <;> [exact zero_le_one; exact le_refl 0],
    by simp [Finsupp.linearCombination_single]⟩

/-- A scalar multiple of a conical combination is a conical combination. -/
theorem conicalCombination_smul (s : Set E) (c : R) (h : 0 ≤ c) (v : E)
    (h_conicalcomb : IsConicalCombination R s v) : IsConicalCombination R s (c • v) := by
  rcases h_conicalcomb with ⟨f, hf_nonneg, rfl⟩
  exact ⟨c • f, fun w => mul_nonneg h (hf_nonneg w), by simp⟩

/-- Adding two conical combinations produces a new conical combination. -/
theorem conicalCombination_add (s : Set E) (x₁ x₂ : E)
    (h₁ : IsConicalCombination R s x₁) (h₂ : IsConicalCombination R s x₂) :
    IsConicalCombination R s (x₁ + x₂) := by
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

--the following deals with conical hull and pointed cones
namespace PointedCone
open ConicalCombination

section PointedConeSection
variable [IsOrderedRing R]

/-- 'IsPointedCone' - Predicate stating that a subset C of a monoid E with an R-module
structure is a pointed cone. -/
def IsPointedCone (C : Set E) : Prop :=
  ∃ (T : PointedCone R E), (T.carrier = C)

/-- Membership in PointedCone.span is equivalent to being a conical combination. -/
theorem mem_span_iff_conicalCombination (s : Set E) (x : E) :
    x ∈ PointedCone.span R s ↔ IsConicalCombination R s x := by
  constructor
  · intro hx
    rw [Finsupp.mem_span_iff_linearCombination] at hx
    rcases hx with ⟨l, rfl⟩
    refine ⟨l.mapRange (↑) (by simp), (fun v => (l v).property), ?_⟩
    classical
    simp [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index]
  · rintro ⟨f, hf_nonneg, rfl⟩
    classical
    rw [Finsupp.linearCombination_apply]
    apply AddSubmonoid.sum_mem
    intro v hv
    exact (PointedCone.span R s).smul_mem' ⟨f v, hf_nonneg v⟩ (PointedCone.subset_span v.property)

/-- Corollary: The PointedCone.span equals the set of all conical combinations. -/
theorem span_eq_setOf_conicalCombination (s : Set E) :
    (PointedCone.span R s : Set E) = {x | IsConicalCombination R s x} := by
  ext x
  exact mem_span_iff_conicalCombination R s x

/-- A pointed cone contains all conical combinations of elements from any given subset. -/
theorem conicalCombination_mem (s : Set E) (f : s →₀ R) (h_nonneg : ∀ v, 0 ≤ f v)
    (C : PointedCone R E) (hs : s ⊆ C.carrier) :
    (Finsupp.linearCombination R (Subtype.val : s → E)) f ∈ C := by
  rw [Finsupp.linearCombination_apply]
  apply AddSubmonoid.sum_mem
  intro v hv
  exact C.smul_mem' ⟨f v, h_nonneg v⟩ (hs v.property)

/-- PointedCone.span R s is contained in any pointed cone C that contains s. -/
theorem span_minimal (s : Set E) (C : PointedCone R E) (hs : s ⊆ C.carrier) :
    (PointedCone.span R s : Set E) ⊆ C.carrier := by
  intro x hx
  have := (mem_span_iff_conicalCombination R s x).mp hx
  obtain ⟨f, hf_nonneg, hf_eq⟩ := this
  rw [hf_eq]
  exact conicalCombination_mem R s f hf_nonneg C hs

/-- PointedCone.span R s is equal to the infimum of all pointed cones containing s.
This characterizes span as the smallest pointed cone containing s. -/
theorem span_eq_sInf (s : Set E) :
    PointedCone.span R s = sInf {C : PointedCone R E | s ⊆ C.carrier} := by
  apply le_antisymm
  · -- span R s ≤ sInf {C | s ⊆ C}
    apply le_sInf
    intro C hC
    exact span_minimal R s C hC
  · -- sInf {C | s ⊆ C} ≤ span R s
    apply sInf_le
    exact PointedCone.subset_span

/-- C is a pointed cone iff C is nonempty and contains all two element conical combinations.
This characterization of pointed cones is convenient in some proofs -/
theorem pointedCone_iff_forall_nonneg {E : Type*} [AddCommMonoid E] [Module R E]
    (C : Set E) : IsPointedCone R C ↔
      C.Nonempty ∧ ∀ (x : E), x ∈ C → ∀ (y : E), y ∈ C → ∀ (a b : R),
      0 ≤ a → 0 ≤ b → a • x + b • y ∈ C where
  mp := by -- IsPointedCone → forall_nonneg
    rintro ⟨T, rfl⟩
    constructor
    · exact ⟨0, T.zero_mem'⟩
    · rintro x hx y hy a b ha hb
      exact T.add_mem' (T.smul_mem' ⟨a, ha⟩ hx) (T.smul_mem' ⟨b, hb⟩ hy)
  mpr := by -- forall_nonneg → IsPointedCone
    rintro ⟨h1, h2⟩
    use {
      carrier := C,
      zero_mem' := by
        obtain ⟨x, hx⟩ := h1
        simpa [zero_smul, add_zero] using h2 x hx x hx 0 0 (le_refl _) (le_refl _),
      add_mem' := by
        intro x y hx hy
        simpa [one_smul] using h2 x hx y hy 1 1 zero_le_one zero_le_one,
      smul_mem' := by
        intro c x hx
        have := h2 x hx x hx (c : R) 0 c.property (le_refl 0)
        simp_all
    }

end PointedConeSection
end PointedCone
