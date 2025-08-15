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

lemma projectiveDimension_le_iff (X : C) (n : ℕ) : projectiveDimension X ≤ n ↔
    HasProjectiveDimensionLE X n := by
  sorry

end ProjectiveDimension

variable [IsNoetherianRing R]

/-
[IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
HasProjectiveDimensionLE M n ↔ Subsingleton (Tor M (R ⧸ maximalIdeal R) (n + 1))
-/

lemma projectiveDimension_eq_iSup_localizedModule (M : ModuleCat.{v} R) [Module.Finite R M] :
    projectiveDimension M = ⨆ (p : MaximalSpectrum R), projectiveDimension
    (ModuleCat.of (Localization.AtPrime p.1) (LocalizedModule.AtPrime p.1 M)) := by
  sorry

lemma globalDimension_eq_iSup_loclization : globalDimension R =
    ⨆ (p : MaximalSpectrum R), globalDimension (Localization.AtPrime p.1) := by
  sorry

/-lemma globalDimensionLE_iff_Tor [IsLocalRing R] :
HasGlobalDimensionLE R n ↔ Subsingleton (Tor (ResidueField R) (ResidueField R) (n + 1))
-/

lemma globalDimension_eq_projectiveDimension_residueField [IsLocalRing R] :
    globalDimension R = projectiveDimension (ModuleCat.of R (ResidueField R)) := by
  sorry

lemma projectiveDimension_quotSMulTop [IsLocalRing R] (M : ModuleCat.{v} R) [Module.Finite R M]
    (x : R) (mem : x ∈ maximalIdeal R) (reg : IsSMulRegular M x) :
    projectiveDimension M = projectiveDimension (ModuleCat.of R (QuotSMulTop x M)) + 1 := by
  sorry

lemma projectiveDimension_quotient_regular_sequence [IsLocalRing R] (M : ModuleCat.{v} R)
    [Module.Finite R M] (rs : List R) (mem : ∀ x ∈ rs, x ∈ maximalIdeal R) (reg : IsRegular M rs) :
    projectiveDimension M = projectiveDimension
    (ModuleCat.of R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))) + rs.length := by
  sorry
