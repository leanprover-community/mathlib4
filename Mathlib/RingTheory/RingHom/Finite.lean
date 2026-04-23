/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Localization.Integer
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!

# The meta properties of finite ring homomorphisms.

## Main results

Let `R` be a commutative ring, `S` is an `R`-algebra, `M` be a submonoid of `R`.

* `finite_localizationPreserves` : If `S` is a finite `R`-algebra, then `S' = M⁻¹S` is a
  finite `R' = M⁻¹R`-algebra.
* `finite_ofLocalizationSpan` : `S` is a finite `R`-algebra if there exists
  a set `{ r }` that spans `R` such that `Sᵣ` is a finite `Rᵣ`-algebra.

-/

@[expose] public section


namespace RingHom

open scoped TensorProduct

open TensorProduct Algebra.TensorProduct

theorem finite_stableUnderComposition : StableUnderComposition @Finite := by
  introv R hf hg
  exact hg.comp hf

theorem finite_respectsIso : RespectsIso @Finite := by
  apply finite_stableUnderComposition.respectsIso
  intros
  exact Finite.of_surjective _ (RingEquiv.toEquiv _).surjective

lemma finite_containsIdentities : ContainsIdentities @Finite := Finite.id

theorem finite_isStableUnderBaseChange : IsStableUnderBaseChange @Finite := by
  refine IsStableUnderBaseChange.mk finite_respectsIso ?_
  simp only [finite_algebraMap]
  intros
  infer_instance

end RingHom

open scoped Pointwise

universe u

variable {R S : Type*} [CommRing R] [CommRing S] (M : Submonoid R) (f : R →+* S)
variable (R' S' : Type*) [CommRing R'] [CommRing S']
variable [Algebra R R'] [Algebra S S']

/-- If `S` is a finite `R`-algebra, then `S' = M⁻¹S` is a finite `R' = M⁻¹R`-algebra. -/
theorem RingHom.finite_localizationPreserves : RingHom.LocalizationPreserves @RingHom.Finite := by
  introv R hf
  letI := f.toAlgebra
  letI := ((algebraMap S S').comp f).toAlgebra
  let f' : R' →+* S' := IsLocalization.map S' f (Submonoid.le_comap_map M)
  letI := f'.toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.map_comp M.le_comap_map).symm
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) S' := by
    rwa [Algebra.algebraMapSubmonoid, RingHom.algebraMap_toAlgebra]
  have : Module.Finite R S := hf
  exact .of_isLocalization R S M

theorem RingHom.localization_away_map_finite (R S R' S' : Type u) [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R R'] (f : R →+* S) [Algebra S S']
    (r : R) [IsLocalization.Away r R']
    [IsLocalization.Away (f r) S'] (hf : f.Finite) : (IsLocalization.Away.map R' S' f r).Finite :=
  finite_localizationPreserves.away f r _ _ hf

/-- `S` is a finite `R`-algebra if there exists a set `{ r }` that
  spans `R` such that `Sᵣ` is a finite `Rᵣ`-algebra. -/
theorem RingHom.finite_ofLocalizationSpan : RingHom.OfLocalizationSpan @RingHom.Finite := by
  classical
  rw [RingHom.ofLocalizationSpan_iff_finite]
  introv R hs H
  -- We first setup the instances
  letI := f.toAlgebra
  letI := fun r : s => (Localization.awayMap f r).toAlgebra
  have (r : s) : IsLocalization ((Submonoid.powers (r : R)).map (algebraMap R S))
      (Localization.Away (f r)) := by
    rw [Submonoid.map_powers]; exact Localization.isLocalization
  haveI : ∀ r : s, IsScalarTower R (Localization.Away (r : R)) (Localization.Away (f r)) :=
    fun r => IsScalarTower.of_algebraMap_eq'
      (IsLocalization.map_comp (Submonoid.powers (r : R)).le_comap_map).symm
  -- By the hypothesis, we may find a finite generating set for each `Sᵣ`. This set can then be
  -- lifted into `R` by multiplying a sufficiently large power of `r`. I claim that the union of
  -- these generates `S`.
  constructor
  replace H := fun r => (H r).1
  choose s₁ s₂ using H
  let sf := fun x : s => IsLocalization.finsetIntegerMultiple (Submonoid.powers (f x)) (s₁ x)
  use s.attach.biUnion sf
  rw [Submodule.span_attach_biUnion, eq_top_iff]
  -- It suffices to show that `r ^ n • x ∈ span T` for each `r : s`, since `{ r ^ n }` spans `R`.
  -- This then follows from the fact that each `x : R` is a linear combination of the generating set
  -- of `Sᵣ`. By multiplying a sufficiently large power of `r`, we can cancel out the `r`s in the
  -- denominators of both the generating set and the coefficients.
  rintro x -
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (s : Set R) hs _ _
  intro r
  obtain ⟨⟨_, n₁, rfl⟩, hn₁⟩ :=
    multiple_mem_span_of_mem_localization_span (Submonoid.powers (r : R))
      (Localization.Away (r : R)) (s₁ r : Set (Localization.Away (f r))) (algebraMap S _ x)
      (by rw [s₂ r]; trivial)
  dsimp only at hn₁
  rw [Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S, ← map_mul] at hn₁
  obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ :=
    IsLocalization.smul_mem_finsetIntegerMultiple_span (Submonoid.powers (r : R))
      (Localization.Away (f r)) _ (s₁ r) hn₁
  rw [Submonoid.smul_def, ← Algebra.smul_def, smul_smul, ← pow_add] at hn₂
  simp_rw [Submonoid.map_powers] at hn₂
  use n₂ + n₁
  exact le_iSup (fun x : s => Submodule.span R (sf x : Set S)) r hn₂
