/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.RingTheory.Localization.Defs

/-!
# Integer elements of a localization

## Main definitions

* `IsLocalization.IsInteger` is a predicate stating that `x : S` is in the image of `R`

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type*} [CommSemiring R] {M : Submonoid R} {S : Type*} [CommSemiring S]
variable [Algebra R S] {P : Type*} [CommSemiring P]

open Function

namespace IsLocalization

section

variable (R)

-- TODO: define a subalgebra of `IsInteger`s
/-- Given `a : S`, `S` a localization of `R`, `IsInteger R a` iff `a` is in the image of
the localization map from `R` to `S`. -/
def IsInteger (a : S) : Prop :=
  a ∈ (algebraMap R S).rangeS

end

theorem isInteger_zero : IsInteger R (0 : S) :=
  Subsemiring.zero_mem _

theorem isInteger_one : IsInteger R (1 : S) :=
  Subsemiring.one_mem _

theorem isInteger_add {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInteger R (a + b) :=
  Subsemiring.add_mem _ ha hb

theorem isInteger_mul {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInteger R (a * b) :=
  Subsemiring.mul_mem _ ha hb

theorem isInteger_smul {a : R} {b : S} (hb : IsInteger R b) : IsInteger R (a • b) := by
  rcases hb with ⟨b', hb⟩
  use a * b'
  rw [← hb, (algebraMap R S).map_mul, Algebra.smul_def]

variable (M)
variable [IsLocalization M S]

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the right, matching the argument order in `LocalizationMap.surj`.
-/
theorem exists_integer_multiple' (a : S) : ∃ b : M, IsInteger R (a * algebraMap R S b) :=
  let ⟨⟨Num, denom⟩, h⟩ := IsLocalization.surj _ a
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the left, matching the argument order in the `SMul` instance.
-/
theorem exists_integer_multiple (a : S) : ∃ b : M, IsInteger R ((b : R) • a) := by
  simp_rw [Algebra.smul_def, mul_comm _ a]
  apply exists_integer_multiple'

/-- We can clear the denominators of a `Finset`-indexed family of fractions. -/
theorem exist_integer_multiples {ι : Type*} (s : Finset ι) (f : ι → S) :
    ∃ b : M, ∀ i ∈ s, IsLocalization.IsInteger R ((b : R) • f i) := by
  haveI := Classical.propDecidable
  refine ⟨∏ i ∈ s, (sec M (f i)).2, fun i hi => ⟨?_, ?_⟩⟩
  · exact (∏ j ∈ s.erase i, (sec M (f j)).2) * (sec M (f i)).1
  rw [RingHom.map_mul, sec_spec', ← mul_assoc, ← (algebraMap R S).map_mul, ← Algebra.smul_def]
  congr 2
  refine _root_.trans ?_ (map_prod (Submonoid.subtype M) _ _).symm
  rw [mul_comm,Submonoid.coe_finset_prod,
    -- Porting note: explicitly supplied `f`
    ← Finset.prod_insert (f := fun i => ((sec M (f i)).snd : R)) (s.notMem_erase i),
    Finset.insert_erase hi]
  rfl

/-- We can clear the denominators of a finite indexed family of fractions. -/
theorem exist_integer_multiples_of_finite {ι : Type*} [Finite ι] (f : ι → S) :
    ∃ b : M, ∀ i, IsLocalization.IsInteger R ((b : R) • f i) := by
  cases nonempty_fintype ι
  obtain ⟨b, hb⟩ := exist_integer_multiples M Finset.univ f
  exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩

/-- We can clear the denominators of a finite set of fractions. -/
theorem exist_integer_multiples_of_finset (s : Finset S) :
    ∃ b : M, ∀ a ∈ s, IsInteger R ((b : R) • a) :=
  exist_integer_multiples M s id

/-- A choice of a common multiple of the denominators of a `Finset`-indexed family of fractions. -/
noncomputable def commonDenom {ι : Type*} (s : Finset ι) (f : ι → S) : M :=
  (exist_integer_multiples M s f).choose

/-- The numerator of a fraction after clearing the denominators
of a `Finset`-indexed family of fractions. -/
noncomputable def integerMultiple {ι : Type*} (s : Finset ι) (f : ι → S) (i : s) : R :=
  ((exist_integer_multiples M s f).choose_spec i i.prop).choose

@[simp]
theorem map_integerMultiple {ι : Type*} (s : Finset ι) (f : ι → S) (i : s) :
    algebraMap R S (integerMultiple M s f i) = commonDenom M s f • f i :=
  ((exist_integer_multiples M s f).choose_spec _ i.prop).choose_spec

/-- A choice of a common multiple of the denominators of a finite set of fractions. -/
noncomputable def commonDenomOfFinset (s : Finset S) : M :=
  commonDenom M s id

/-- The finset of numerators after clearing the denominators of a finite set of fractions. -/
noncomputable def finsetIntegerMultiple [DecidableEq R] (s : Finset S) : Finset R :=
  s.attach.image fun t => integerMultiple M s id t

open Pointwise

theorem finsetIntegerMultiple_image [DecidableEq R] (s : Finset S) :
    algebraMap R S '' finsetIntegerMultiple M s = commonDenomOfFinset M s • (s : Set S) := by
  delta finsetIntegerMultiple commonDenom
  rw [Finset.coe_image]
  ext
  constructor
  · rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩
    rw [map_integerMultiple]
    exact Set.mem_image_of_mem _ x.prop
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, hx⟩, s.mem_attach _, rfl⟩, map_integerMultiple M s id _⟩

end IsLocalization
