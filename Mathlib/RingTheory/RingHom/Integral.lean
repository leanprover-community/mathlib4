/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!

# The meta properties of integral ring homomorphisms.

-/

public section


namespace RingHom

open scoped TensorProduct

open TensorProduct Algebra.TensorProduct

theorem isIntegral_stableUnderComposition : StableUnderComposition fun f => f.IsIntegral := by
  introv R hf hg; exact hf.trans _ _ hg

theorem isIntegral_respectsIso : RespectsIso fun f => f.IsIntegral := by
  apply isIntegral_stableUnderComposition.respectsIso
  introv x
  rw [← e.apply_symm_apply x]
  apply RingHom.isIntegralElem_map

theorem isIntegral_isStableUnderBaseChange : IsStableUnderBaseChange fun f => f.IsIntegral := by
  refine IsStableUnderBaseChange.mk isIntegral_respectsIso ?_
  introv int
  rw [algebraMap_isIntegral_iff] at int ⊢
  infer_instance

open Polynomial in
/-- `S` is an integral `R`-algebra if there exists a set `{ r }` that
  spans `R` such that each `Sᵣ` is an integral `Rᵣ`-algebra. -/
theorem isIntegral_ofLocalizationSpan :
    OfLocalizationSpan (RingHom.IsIntegral ·) := by
  introv R hs H r
  letI := f.toAlgebra
  change r ∈ (integralClosure R S).toSubmodule
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ s hs
  rintro ⟨t, ht⟩
  letI := (Localization.awayMap f t).toAlgebra
  haveI : IsScalarTower R (Localization.Away t) (Localization.Away (f t)) := .of_algebraMap_eq'
    (IsLocalization.lift_comp _).symm
  have : _root_.IsIntegral (Localization.Away t) (algebraMap S (Localization.Away (f t)) r) :=
    H ⟨t, ht⟩ (algebraMap _ _ r)
  obtain ⟨⟨_, n, rfl⟩, p, hp, hp'⟩ := this.exists_multiple_integral_of_isLocalization (.powers t)
  rw [IsScalarTower.algebraMap_eq R S, Submonoid.smul_def, Algebra.smul_def,
    IsScalarTower.algebraMap_apply R S, ← map_mul, ← hom_eval₂,
    IsLocalization.map_eq_zero_iff (.powers (f t))] at hp'
  obtain ⟨⟨x, m, (rfl : algebraMap R S t ^ m = x)⟩, e⟩ := hp'
  by_cases hp' : 1 ≤ p.natDegree; swap
  · obtain rfl : p = 1 := eq_one_of_monic_natDegree_zero hp (by lia)
    exact ⟨m, by simp [Algebra.smul_def, show algebraMap R S t ^ m = 0 by simpa using e]⟩
  refine ⟨m + n, p.scaleRoots (t ^ m), (monic_scaleRoots_iff _).mpr hp, ?_⟩
  have := p.scaleRoots_eval₂_mul (algebraMap R S) (t ^ n • r) (t ^ m)
  simp only [pow_add, ← Algebra.smul_def, mul_smul, ← map_pow] at e this ⊢
  rw [this, ← tsub_add_cancel_of_le hp', pow_succ, mul_smul, e, smul_zero]

end RingHom
