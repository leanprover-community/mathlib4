/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Restricted
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Order.Filter.Cofinite

/-!
# Univariate restricted power series

`IsRestricted` : We say a univariate power series over a normed ring `R` is restricted for a
real number `c` if `‖coeff t f‖ * c i ^ t i → 0` under the cofinite filter.

-/

@[expose] public section
namespace PowerSeries

open Filter
open scoped Topology Pointwise

variable {R : Type*} [NormedRing R] (c : ℝ) (f : PowerSeries R)

/-- Predicate for when `f` is a restricted power series. -/
abbrev IsRestricted :=
  MvPowerSeries.IsRestricted (σ := Unit) (fun _ ↦ c) f

private lemma isRestricted_comp_uniqueEquiv :
    (fun (t : Unit →₀ ℕ) ↦ ‖MvPowerSeries.coeff t f‖ * t.prod (fun _ x ↦ c ^ x)) =
    (fun (n : ℕ) ↦ ‖coeff n f‖ * c ^ n) ∘ Finsupp.uniqueEquiv () := by
  funext t
  simp only [Function.comp_apply, Finsupp.uniqueEquiv_apply, PUnit.default_eq_unit,
    Finsupp.prod_pow, Finset.univ_unique, Finset.prod_singleton, coeff,
    show (Finsupp.single () (t ())) = t by grind]

lemma isRestricted_iff : IsRestricted c f ↔
    Tendsto (fun (t : ℕ) ↦ ‖coeff t f‖ * c ^ t) cofinite (𝓝 0) := by
  rw [IsRestricted, MvPowerSeries.IsRestricted, isRestricted_comp_uniqueEquiv]
  exact ⟨fun H ↦ (H.comp (Finsupp.uniqueEquiv ()).symm.injective.tendsto_cofinite).congr fun n ↦
    by simp, fun H ↦ H.comp (Finsupp.uniqueEquiv ()).injective.tendsto_cofinite⟩

lemma isRestricted_iff' : IsRestricted c f ↔
    Tendsto (fun (t : ℕ) ↦ ‖coeff t f‖ * c ^ t) atTop (𝓝 0) := by
  simp_rw [isRestricted_iff, Nat.cofinite_eq_atTop]

@[simp]
lemma isRestricted_abs_iff : IsRestricted |c| f ↔ IsRestricted c f :=
  MvPowerSeries.isRestricted_abs_iff (fun _ ↦ c) f

lemma isRestricted_zero : IsRestricted c (0 : PowerSeries R) :=
 MvPowerSeries.isRestricted_zero (fun _ ↦ c)

lemma isRestricted_monomial (n : ℕ) (a : R) : IsRestricted c (monomial n a) :=
  MvPowerSeries.isRestricted_monomial (fun _ ↦ c) ((Finsupp.single () n)) a

lemma isRestricted_one : IsRestricted c (1 : PowerSeries R) :=
  MvPowerSeries.isRestricted_monomial (fun _ ↦ c) 0 1

lemma isRestricted_C (a : R) : IsRestricted c (C a) :=
  MvPowerSeries.isRestricted_C (fun _ ↦ c) a

variable {f} in
lemma isRestricted.add {g : PowerSeries R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f + g) :=
  MvPowerSeries.isRestricted.add (fun _ ↦ c) hf hg

variable {f} in
lemma isRestricted.neg (hf : IsRestricted c f) : IsRestricted c (-f) :=
  MvPowerSeries.isRestricted.neg (fun _ ↦ c) hf

lemma isRestricted.mul [IsUltrametricDist R] (c : ℝ) {f g : PowerSeries R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) : IsRestricted c (f * g) :=
  MvPowerSeries.isRestricted.mul (fun _ ↦ c) hf hg

namespace IsRestricted

/-- Restricted power series as an additive subgroup of `PowerSeries R`. -/
def addSubgroup (c : ℝ) : AddSubgroup (PowerSeries R) :=
  MvPowerSeries.IsRestricted.addSubgroup (fun _ ↦ c)

variable [IsUltrametricDist R]

/-- Restricted power series as an subring of `PowerSeries R`. -/
def subring (c : ℝ) :  Subring (PowerSeries R) :=
  MvPowerSeries.IsRestricted.subring (fun _ ↦ c)

end PowerSeries.IsRestricted
