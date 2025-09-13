/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Data.ENat.Lattice
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
/-!
# The Global Dimension of a Ring
-/

--set_option pp.universes true

universe u v

variable (R : Type u) [CommRing R]

open CategoryTheory IsLocalRing RingTheory.Sequence

def HasGlobalDimensionLE (n : ℕ) : Prop :=
  ∀ (M : ModuleCat.{v} R), HasProjectiveDimensionLE M n

noncomputable def globalDimension : ℕ∞ :=
  sInf (({(n : ℕ) | HasGlobalDimensionLE.{u, v} R n}).image WithTop.some)

lemma HasGlobalDimensionLE_iff (n : ℕ) : HasGlobalDimensionLE R n ↔ globalDimension R ≤ n := by
  sorry

section ProjectiveDimension

variable {C : Type u} [Category.{v, u} C] [Abelian C]

--projectiveDimension should be `-∞` when `X = 0`

noncomputable def projectiveDimension (X : C) : WithBot ℕ∞ :=
  sInf {n : WithBot ℕ∞ | ∀ (i : ℕ), n < i → HasProjectiveDimensionLT X i}

noncomputable def nonnegProjectiveDimension (X : C) : ℕ∞ :=
  sInf (({(n : ℕ) | HasProjectiveDimensionLT X n}).image WithTop.some)

lemma projectiveDimension_eq_of_iso (X Y : C) (e : X ≅ Y) :
    projectiveDimension X = projectiveDimension Y := by
  sorry

lemma projectiveDimension_le_iff (X : C) (n : ℕ) : projectiveDimension X ≤ n ↔
    HasProjectiveDimensionLE X n := by
  sorry

lemma projectiveDimension_eq_bot_iff (X : C) : projectiveDimension X = ⊥ ↔
    Limits.IsZero X := by
  sorry

lemma projectiveDimension_eq_nonnegProjectiveDimension_of_not_zero (X : C) (h : ¬ Limits.IsZero X) :
    nonnegProjectiveDimension X = projectiveDimension X :=  by
  sorry

lemma projectiveDimension_ne_top_iff (X : C) : projectiveDimension X ≠ ⊤ ↔
    ∃ n, HasProjectiveDimensionLE X n := by
  sorry

lemma nonnegProjectiveDimension_ne_top_iff (X : C) : nonnegProjectiveDimension X ≠ ⊤ ↔
    ∃ n, HasProjectiveDimensionLE X n := by
  sorry

end ProjectiveDimension
