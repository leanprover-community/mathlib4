/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.FiniteFreeResolution.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.LocalRing.Module

/-!
This file proves that a module over a local noetherian ring has a finite free resolution if its
projective dimension is finite.
-/

public section

universe u v

open CategoryTheory

namespace Module

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
  (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem HasFiniteFreeResolutionOfLength.of_hasProjectiveDimensionLE (n : ℕ)
    [HasProjectiveDimensionLE (ModuleCat.of R M) n] : HasFiniteFreeResolutionOfLength R M n := by
  induction n generalizing M with
  | zero =>
      have : Projective R M := (IsProjective.iff_projective M).2 <|
        projective_iff_hasProjectiveDimensionLT_one.2 inferInstance
      have : Free R M := free_of_flat_of_isLocalRing
      exact HasFiniteFreeResolutionOfLength.zero M
  | succ n ih =>
      rcases exists_finite_presentation R M with ⟨P, _, _, _, _, f, hfs⟩
      have : HasProjectiveDimensionLE (ModuleCat.of R f.ker) n :=
        (LinearMap.shortExact_shortComplexKer hfs).hasProjectiveDimensionLT_X₁ (n + 1)
          inferInstance inferInstance
      exact (ih (LinearMap.ker f)).succ' (LinearMap.ker f).subtype f f.ker.subtype_injective hfs
        (LinearMap.exact_subtype_ker_map f)

variable {R M} in
/-- Let `M` be an module over a local noetherian ring `R`. Then `M` has a finite free resolution
if its projective dimension is finite. -/
theorem HasFiniteFreeResolution.of_projectiveDimension_ne_top
    (h : projectiveDimension (ModuleCat.of R M) ≠ ⊤) : HasFiniteFreeResolution R M :=
  let ⟨n, _⟩ := (CategoryTheory.projectiveDimension_ne_top_iff (ModuleCat.of R M)).1 h
  ⟨n, HasFiniteFreeResolutionOfLength.of_hasProjectiveDimensionLE R M n⟩

end Module
