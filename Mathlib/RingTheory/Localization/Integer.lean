/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.RingTheory.Localization.Basic

#align_import ring_theory.localization.integer from "leanprover-community/mathlib"@"9556784a5b84697562e9c6acb40500d4a82e675a"

/-!
# Integer elements of a localization

## Main definitions

 * `IsLocalization.IsInteger` is a predicate stating that `x : S` is in the image of `R`

## Implementation notes

See `RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type*} [CommRing R] {M : Submonoid R} {S : Type*} [CommRing S]

variable [Algebra R S] {P : Type*} [CommRing P]

open Function

open BigOperators

namespace IsLocalization

section

variable (R)

-- TODO: define a subalgebra of `IsInteger`s
/-- Given `a : S`, `S` a localization of `R`, `IsInteger R a` iff `a` is in the image of
the localization map from `R` to `S`. -/
def IsInteger (a : S) : Prop :=
  a ∈ (algebraMap R S).range
#align is_localization.is_integer IsLocalization.IsInteger

end

theorem isInteger_zero : IsInteger R (0 : S) :=
  Subring.zero_mem _
#align is_localization.is_integer_zero IsLocalization.isInteger_zero

theorem isInteger_one : IsInteger R (1 : S) :=
  Subring.one_mem _
#align is_localization.is_integer_one IsLocalization.isInteger_one

theorem isInteger_add {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInteger R (a + b) :=
  Subring.add_mem _ ha hb
#align is_localization.is_integer_add IsLocalization.isInteger_add

theorem isInteger_mul {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInteger R (a * b) :=
  Subring.mul_mem _ ha hb
#align is_localization.is_integer_mul IsLocalization.isInteger_mul

theorem isInteger_smul {a : R} {b : S} (hb : IsInteger R b) : IsInteger R (a • b) := by
  rcases hb with ⟨b', hb⟩
  -- ⊢ IsInteger R (a • b)
  use a * b'
  -- ⊢ ↑(algebraMap R S) (a * b') = a • b
  rw [← hb, (algebraMap R S).map_mul, Algebra.smul_def]
  -- 🎉 no goals
#align is_localization.is_integer_smul IsLocalization.isInteger_smul

variable (M)
variable [IsLocalization M S]

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the right, matching the argument order in `LocalizationMap.surj`.
-/
theorem exists_integer_multiple' (a : S) : ∃ b : M, IsInteger R (a * algebraMap R S b) :=
  let ⟨⟨Num, denom⟩, h⟩ := IsLocalization.surj _ a
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩
#align is_localization.exists_integer_multiple' IsLocalization.exists_integer_multiple'

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the left, matching the argument order in the `SMul` instance.
-/
theorem exists_integer_multiple (a : S) : ∃ b : M, IsInteger R ((b : R) • a) := by
  simp_rw [Algebra.smul_def, mul_comm _ a]
  -- ⊢ ∃ b, IsInteger R (a * ↑(algebraMap R S) ↑b)
  apply exists_integer_multiple'
  -- 🎉 no goals
#align is_localization.exists_integer_multiple IsLocalization.exists_integer_multiple

/-- We can clear the denominators of a `Finset`-indexed family of fractions. -/
theorem exist_integer_multiples {ι : Type*} (s : Finset ι) (f : ι → S) :
    ∃ b : M, ∀ i ∈ s, IsLocalization.IsInteger R ((b : R) • f i) := by
  haveI := Classical.propDecidable
  -- ⊢ ∃ b, ∀ (i : ι), i ∈ s → IsInteger R (↑b • f i)
  refine' ⟨∏ i in s, (sec M (f i)).2, fun i hi => ⟨_, _⟩⟩
  -- ⊢ R
  · exact (∏ j in s.erase i, (sec M (f j)).2) * (sec M (f i)).1
    -- 🎉 no goals
  rw [RingHom.map_mul, sec_spec', ← mul_assoc, ← (algebraMap R S).map_mul, ← Algebra.smul_def]
  -- ⊢ (↑(∏ j in Finset.erase s i, (sec M (f j)).snd) * ↑(sec M (f i)).snd) • f i = …
  congr 2
  -- ⊢ ↑(∏ j in Finset.erase s i, (sec M (f j)).snd) * ↑(sec M (f i)).snd = ↑(∏ i i …
  refine' _root_.trans _ ((Submonoid.subtype M).map_prod _ _).symm
  -- ⊢ ↑(∏ j in Finset.erase s i, (sec M (f j)).snd) * ↑(sec M (f i)).snd = ∏ x in  …
  rw [mul_comm,Submonoid.coe_finset_prod,
    -- Porting note: explicitly supplied `f`
    ← Finset.prod_insert (f := fun i => ((sec M (f i)).snd : R)) (s.not_mem_erase i),
    Finset.insert_erase hi]
  rfl
  -- 🎉 no goals
#align is_localization.exist_integer_multiples IsLocalization.exist_integer_multiples

/-- We can clear the denominators of a finite indexed family of fractions. -/
theorem exist_integer_multiples_of_finite {ι : Type*} [Finite ι] (f : ι → S) :
    ∃ b : M, ∀ i, IsLocalization.IsInteger R ((b : R) • f i) := by
  cases nonempty_fintype ι
  -- ⊢ ∃ b, ∀ (i : ι), IsInteger R (↑b • f i)
  obtain ⟨b, hb⟩ := exist_integer_multiples M Finset.univ f
  -- ⊢ ∃ b, ∀ (i : ι), IsInteger R (↑b • f i)
  exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩
  -- 🎉 no goals
#align is_localization.exist_integer_multiples_of_finite IsLocalization.exist_integer_multiples_of_finite

/-- We can clear the denominators of a finite set of fractions. -/
theorem exist_integer_multiples_of_finset (s : Finset S) :
    ∃ b : M, ∀ a ∈ s, IsInteger R ((b : R) • a) :=
  exist_integer_multiples M s id
#align is_localization.exist_integer_multiples_of_finset IsLocalization.exist_integer_multiples_of_finset

/-- A choice of a common multiple of the denominators of a `Finset`-indexed family of fractions. -/
noncomputable def commonDenom {ι : Type*} (s : Finset ι) (f : ι → S) : M :=
  (exist_integer_multiples M s f).choose
#align is_localization.common_denom IsLocalization.commonDenom

/-- The numerator of a fraction after clearing the denominators
of a `Finset`-indexed family of fractions. -/
noncomputable def integerMultiple {ι : Type*} (s : Finset ι) (f : ι → S) (i : s) : R :=
  ((exist_integer_multiples M s f).choose_spec i i.prop).choose
#align is_localization.integer_multiple IsLocalization.integerMultiple

@[simp]
theorem map_integerMultiple {ι : Type*} (s : Finset ι) (f : ι → S) (i : s) :
    algebraMap R S (integerMultiple M s f i) = commonDenom M s f • f i :=
  ((exist_integer_multiples M s f).choose_spec _ i.prop).choose_spec
#align is_localization.map_integer_multiple IsLocalization.map_integerMultiple

/-- A choice of a common multiple of the denominators of a finite set of fractions. -/
noncomputable def commonDenomOfFinset (s : Finset S) : M :=
  commonDenom M s id
#align is_localization.common_denom_of_finset IsLocalization.commonDenomOfFinset

/-- The finset of numerators after clearing the denominators of a finite set of fractions. -/
noncomputable def finsetIntegerMultiple [DecidableEq R] (s : Finset S) : Finset R :=
  s.attach.image fun t => integerMultiple M s id t
#align is_localization.finset_integer_multiple IsLocalization.finsetIntegerMultiple

open Pointwise

theorem finsetIntegerMultiple_image [DecidableEq R] (s : Finset S) :
    algebraMap R S '' finsetIntegerMultiple M s = commonDenomOfFinset M s • (s : Set S) := by
  delta finsetIntegerMultiple commonDenom
  -- ⊢ ↑(algebraMap R S) '' ↑(Finset.image (fun t => integerMultiple M s id t) (Fin …
  rw [Finset.coe_image]
  -- ⊢ ↑(algebraMap R S) '' ((fun t => integerMultiple M s id t) '' ↑(Finset.attach …
  ext
  -- ⊢ x✝ ∈ ↑(algebraMap R S) '' ((fun t => integerMultiple M s id t) '' ↑(Finset.a …
  constructor
  -- ⊢ x✝ ∈ ↑(algebraMap R S) '' ((fun t => integerMultiple M s id t) '' ↑(Finset.a …
  · rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩
    -- ⊢ ↑(algebraMap R S) ((fun t => integerMultiple M s id t) x) ∈ commonDenomOfFin …
    rw [map_integerMultiple]
    -- ⊢ commonDenom M s id • id ↑x ∈ commonDenomOfFinset M s • ↑s
    exact Set.mem_image_of_mem _ x.prop
    -- 🎉 no goals
  · rintro ⟨x, hx, rfl⟩
    -- ⊢ (fun x => ↑(Submonoid.subtype M) (commonDenomOfFinset M s) • x) x ∈ ↑(algebr …
    exact ⟨_, ⟨⟨x, hx⟩, s.mem_attach _, rfl⟩, map_integerMultiple M s id _⟩
    -- 🎉 no goals
#align is_localization.finset_integer_multiple_image IsLocalization.finsetIntegerMultiple_image

end IsLocalization
