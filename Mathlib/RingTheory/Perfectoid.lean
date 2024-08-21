/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import Mathlib.RingTheory.Perfection
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Perfectoid Rings and Perfectoid Fields
-/

open Valuation Valued Function NNReal CategoryTheory

-- `RankOne or NNReal?`
-- class PerfectoidField (K : Type*) {Γ : outParam Type*} [Field K]
--     [LinearOrderedCommGroupWithZero Γ]
--     [vK : Valued K Γ] [vK.v.RankOne] [CompleteSpace K] where
class PerfectoidField (K : Type*) [Field K]
    [val : Valued K ℝ≥0] [CompleteSpace K] where -- `Valued inside or outside the structure?`
  p : ℕ -- `p inside or outside the structure?`
  p_prime : Nat.Prime p
  exists_p_mem_span_pow_p : ∃ π : 𝒪[K], ¬ IsUnit π ∧ (p : 𝒪[K]) ∈ Ideal.span {π ^ p}
  exist_p_th_root : ∀ x : 𝒪[K]⧸Ideal.span {(p : 𝒪[K])},
      ∃ y : 𝒪[K]⧸Ideal.span {(p : 𝒪[K])} , x = y ^ p
      -- Surjective <| frobenius (𝒪[K]⧸Ideal.span {(p : 𝒪[K])}) p

section Facts
instance primePerfectoidFieldP (K : Type*) [Field K]
    [Valued K ℝ≥0] [CompleteSpace K]
    [perf : PerfectoidField K] : Fact (Nat.Prime (PerfectoidField.p K)) := ⟨perf.p_prime⟩
-- `Should I write Fact instance?`

instance primePerfectoidFieldValuationPNeOne (K : Type*) [Field K]
    [vK: Valued K ℝ≥0] [CompleteSpace K]
    [perf : PerfectoidField K] : Fact (vK.v (PerfectoidField.p K) ≠ 1) := sorry

end Facts

variable (K : Type*) {Γ : outParam Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    [vK : Valued K ℝ≥0] [CompleteSpace K] [perf : PerfectoidField K]

#synth Fact (Nat.Prime (PerfectoidField.p K))

-- `Should I define a PerfectoidField.Tilt?`
-- This is not a proposition I need to proof in order to prove the final theorem.
theorem PerfectoidField.isAlgClosed_iff_isAlgClosed_tilt (K : Type*) {Γ : outParam Type*}
    [Field K] [LinearOrderedCommGroupWithZero Γ]
    [vK : Valued K ℝ≥0] [CompleteSpace K] [perf : PerfectoidField K] :
    IsAlgClosed K ↔ IsAlgClosed (Tilt K vK.v 𝒪[K] (integer.integers vK.v) perf.p) := sorry

def PerfectoidField.ofFiniteDimensional (K L : Type*) [Field K]
    [vK : Valued K ℝ≥0] [CompleteSpace K] [PerfectoidField K] [Field L]
    [Algebra K L] [FiniteDimensional K L] : @PerfectoidField L _ sorry sorry := sorry
    -- this can be a theorem if p is moved outside the perfectoid

section FiniteExts


-- `How to define the category of finite extensions?`
-- `It depends on how to recover the Galois group from this category?`
-- 1. subfields of algebraic closure
-- 2. all fields inside some type universe
--    (CategoryTheory.Bundled Field, CategoryTheory.BundledHom),
--    then use CategoryTheory.Over and CategoryTheory.FullSubcategory
-- 3. first define a structure FiniteExtensionOverK and its boundled hom,
--    then use CategoryTheory.Bundled.
-- 3 is easiest but not so aligned to mathlib style??
def FiniteExtension (K : Type*) [Field K] : Type* := sorry

instance FiniteExtension.category (K : Type*) [Field K] : Category (FiniteExtension K) := sorry

end FiniteExts

-- `How to define the category of perfectoid fields over K?`
-- CategoryTheory.Over
-- 2. the category of all perfectoid fields then use CategoryTheory.Over?
-- 3. first define a structure FiniteExtensionOverK and its boundled hom,
--    then use CategoryTheory.Bundled.
def PerfectoidFieldOver (K : Type*) [Field K]: Type* := sorry

instance PerfectoidFieldOver.category (K : Type*) [Field K] :
    Category (PerfectoidFieldOver K) := sorry

def PerfectoidField.TiltingFunctor : (PerfectoidFieldOver K) ⥤
    (PerfectoidFieldOver (Tilt K vK.v 𝒪[K] (integer.integers vK.v) perf.p)) := sorry

def PerfectoidField.TiltingFinExt : FiniteExtension K ≌
    FiniteExtension (Tilt K vK.v 𝒪[K] (integer.integers vK.v) perf.p) := sorry
