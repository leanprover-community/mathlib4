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

-- `Valuation is not a part of information it only require the topology comes from a valuation`

class PerfectoidField (p : outParam ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [val : Valued K ℝ≥0] extends CompleteSpace K : Prop
    where -- `Valued inside or outside the structure?`
  exists_p_mem_span_pow_p : ∃ π : 𝒪[K], ¬ IsUnit π ∧ (p : 𝒪[K]) ∈ Ideal.span {π ^ p}
  exist_p_th_root : ∀ x : 𝒪[K]⧸Ideal.span {(p : 𝒪[K])},
      ∃ y : 𝒪[K]⧸Ideal.span {(p : 𝒪[K])} , x = y ^ p
      -- Surjective <| frobenius (𝒪[K]⧸Ideal.span {(p : 𝒪[K])}) p
-- definition of module

namespace PerfectoidField

variable (p : outParam ℕ) [Fact (p.Prime)] (K : Type*) {Γ : outParam Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] [vK : Valued K ℝ≥0] [CompleteSpace K]
    [perf : PerfectoidField p K]

theorem val_p_lt_1 : vK.v p < 1 := sorry

#check Module

def Tilt := @_root_.Tilt K _ vK.v 𝒪[K] _ _ (integer.integers vK.v) p _ ⟨ne_of_lt <| val_p_lt_1 p K⟩

noncomputable instance : Field (Tilt p K) := inferInstanceAs <|
    Field (@_root_.Tilt K _ vK.v 𝒪[K] _ _ (integer.integers vK.v) p _ ⟨ne_of_lt <| val_p_lt_1 p K⟩)
-- C_p =

variable (K : Type*) {Γ : outParam Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    [vK : Valued K ℝ≥0] [CompleteSpace K] [perf : PerfectoidField p K]

-- `Should I define a PerfectoidField.Tilt?`
-- This is not a proposition I need to proof in order to prove the final theorem.
theorem PerfectoidField.isAlgClosed_iff_isAlgClosed_tilt (K : Type*) {Γ : outParam Type*}
    [Field K] [LinearOrderedCommGroupWithZero Γ]
    [vK : Valued K ℝ≥0] [CompleteSpace K] [perf : PerfectoidField p K] :
    -- IsAlgClosed K ↔ IsAlgClosed (_root_.Tilt K vK.v 𝒪[K] (integer.integers vK.v) p ) := sorry
    IsAlgClosed K ↔ IsAlgClosed (Tilt p K) := sorry

def valuedRankOneValuationFiniteDimensional (K L : Type*) [Field K]
    [vK : Valued K ℝ≥0] [CompleteSpace K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    Valued L ℝ≥0 := sorry

-- `In the case L has is an extension of K complete with respect to a rank one valuation, L has a`
-- `unique extension of valuation. But it cannot be an instance`

instance ofFiniteDimensional (K L : Type*) [Field K]
    [vK : Valued K ℝ≥0] [CompleteSpace K] [PerfectoidField p K] [Field L]
    [Algebra K L] [FiniteDimensional K L] :
    @PerfectoidField p _ L _ (valuedRankOneValuationFiniteDimensional K L) := sorry

section FiniteExts


-- `How to define the category of finite extensions?`
-- `It depends on how to recover the Galois group from this category?`
-- 1. subfields of algebraic closure
-- 2. all fields inside some type universe
--    (CategoryTheory.Bundled Field, CategoryTheory.BundledHom),
--    then use CategoryTheory.Over and CategoryTheory.FullSubcategory
-- 3. first define a structure FiniteExtensionOver K and its boundled hom,
--    then use CategoryTheory.Bundled.
-- 3 is easiest but not so aligned to mathlib style??
-- connect
def FiniteExtension (K : Type*) [Field K] : Type* := sorry

instance FiniteExtension.category (K : Type*) [Field K] : Category (FiniteExtension K) := sorry

end FiniteExts

-- `How to define the category of perfectoid fields over K?`
-- CategoryTheory.Over
-- 2. the category of all perfectoid fields then use CategoryTheory.Over?
-- 3. first define a structure perfectoid fields K and its boundled hom,
--    then use CategoryTheory.Bundled.

def PerfFieldCat := CategoryTheory.Bundled (PerfectoidField p) -- topological field only + some prop

def PerfectoidFieldOver (K : Type*) [Field K]: Type* := sorry

instance PerfectoidFieldOver.category (K : Type*) [Field K] :
    Category (PerfectoidFieldOver K) := sorry

def PerfectoidField.TiltingFunctor : (PerfectoidFieldOver K) ⥤
    (PerfectoidFieldOver (Tilt K vK.v 𝒪[K] (integer.integers vK.v) perf.p)) := sorry

def PerfectoidField.TiltingFinExt : FiniteExtension K ≌
    FiniteExtension (Tilt K vK.v 𝒪[K] (integer.integers vK.v) perf.p) := sorry
