/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.calculus.formal_multilinear_series
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.Multilinear

/-!
# Formal multilinear series

In this file we define `formal_multilinear_series 𝕜 E F` to be a family of `n`-multilinear maps for
all `n`, designed to model the sequence of derivatives of a function. In other files we use this
notion to define `C^n` functions (called `cont_diff` in `mathlib`) and analytic functions.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

## Tags

multilinear, formal series
-/


noncomputable section

open Set Fin

open Topology

variable {𝕜 𝕜' E F G : Type _}

section

variable [CommRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]
  [ContinuousConstSMul 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [TopologicalAddGroup F] [ContinuousConstSMul 𝕜 F] [AddCommGroup G] [Module 𝕜 G]
  [TopologicalSpace G] [TopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]

/-- A formal multilinear series over a field `𝕜`, from `E` to `F`, is given by a family of
multilinear maps from `E^n` to `F` for all `n`. -/
@[nolint unused_arguments]
def FormalMultilinearSeries (𝕜 : Type _) (E : Type _) (F : Type _) [Ring 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [TopologicalAddGroup F]
    [ContinuousConstSMul 𝕜 F] :=
  ∀ n : ℕ, E[×n]→L[𝕜] F deriving AddCommGroup
#align formal_multilinear_series FormalMultilinearSeries

instance : Inhabited (FormalMultilinearSeries 𝕜 E F) :=
  ⟨0⟩

section Module

/- `derive` is not able to find the module structure, probably because Lean is confused by the
dependent types. We register it explicitly. -/
instance : Module 𝕜 (FormalMultilinearSeries 𝕜 E F) :=
  by
  letI : ∀ n, Module 𝕜 (ContinuousMultilinearMap 𝕜 (fun i : Fin n => E) F) := fun n => by
    infer_instance
  refine' Pi.module _ _ _

end Module

namespace FormalMultilinearSeries

protected theorem ext_iff {p q : FormalMultilinearSeries 𝕜 E F} : p = q ↔ ∀ n, p n = q n :=
  Function.funext_iff
#align formal_multilinear_series.ext_iff FormalMultilinearSeries.ext_iff

protected theorem ne_iff {p q : FormalMultilinearSeries 𝕜 E F} : p ≠ q ↔ ∃ n, p n ≠ q n :=
  Function.ne_iff
#align formal_multilinear_series.ne_iff FormalMultilinearSeries.ne_iff

/-- Killing the zeroth coefficient in a formal multilinear series -/
def removeZero (p : FormalMultilinearSeries 𝕜 E F) : FormalMultilinearSeries 𝕜 E F
  | 0 => 0
  | n + 1 => p (n + 1)
#align formal_multilinear_series.remove_zero FormalMultilinearSeries.removeZero

@[simp]
theorem removeZero_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) : p.removeZero 0 = 0 :=
  rfl
#align formal_multilinear_series.remove_zero_coeff_zero FormalMultilinearSeries.removeZero_coeff_zero

@[simp]
theorem removeZero_coeff_succ (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) :
    p.removeZero (n + 1) = p (n + 1) :=
  rfl
#align formal_multilinear_series.remove_zero_coeff_succ FormalMultilinearSeries.removeZero_coeff_succ

theorem removeZero_of_pos (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (h : 0 < n) :
    p.removeZero n = p n := by
  rw [← Nat.succ_pred_eq_of_pos h]
  rfl
#align formal_multilinear_series.remove_zero_of_pos FormalMultilinearSeries.removeZero_of_pos

/-- Convenience congruence lemma stating in a dependent setting that, if the arguments to a formal
multilinear series are equal, then the values are also equal. -/
theorem congr (p : FormalMultilinearSeries 𝕜 E F) {m n : ℕ} {v : Fin m → E} {w : Fin n → E}
    (h1 : m = n) (h2 : ∀ (i : ℕ) (him : i < m) (hin : i < n), v ⟨i, him⟩ = w ⟨i, hin⟩) :
    p m v = p n w := by
  cases h1
  congr with ⟨i, hi⟩
  exact h2 i hi hi
#align formal_multilinear_series.congr FormalMultilinearSeries.congr

/-- Composing each term `pₙ` in a formal multilinear series with `(u, ..., u)` where `u` is a fixed
continuous linear map, gives a new formal multilinear series `p.comp_continuous_linear_map u`. -/
def compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) :
    FormalMultilinearSeries 𝕜 E G := fun n => (p n).compContinuousLinearMap fun i : Fin n => u
#align formal_multilinear_series.comp_continuous_linear_map FormalMultilinearSeries.compContinuousLinearMap

@[simp]
theorem compContinuousLinearMap_apply (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) (n : ℕ)
    (v : Fin n → E) : (p.compContinuousLinearMap u) n v = p n (u ∘ v) :=
  rfl
#align formal_multilinear_series.comp_continuous_linear_map_apply FormalMultilinearSeries.compContinuousLinearMap_apply

variable (𝕜) [CommRing 𝕜'] [SMul 𝕜 𝕜']

variable [Module 𝕜' E] [ContinuousConstSMul 𝕜' E] [IsScalarTower 𝕜 𝕜' E]

variable [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [IsScalarTower 𝕜 𝕜' F]

/-- Reinterpret a formal `𝕜'`-multilinear series as a formal `𝕜`-multilinear series. -/
@[simp]
protected def restrictScalars (p : FormalMultilinearSeries 𝕜' E F) :
    FormalMultilinearSeries 𝕜 E F := fun n => (p n).restrictScalars 𝕜
#align formal_multilinear_series.restrict_scalars FormalMultilinearSeries.restrictScalars

end FormalMultilinearSeries

end

namespace FormalMultilinearSeries

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable (p : FormalMultilinearSeries 𝕜 E F)

/-- Forgetting the zeroth term in a formal multilinear series, and interpreting the following terms
as multilinear maps into `E →L[𝕜] F`. If `p` corresponds to the Taylor series of a function, then
`p.shift` is the Taylor series of the derivative of the function. -/
def shift : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F) := fun n => (p n.succ).curryRight
#align formal_multilinear_series.shift FormalMultilinearSeries.shift

/-- Adding a zeroth term to a formal multilinear series taking values in `E →L[𝕜] F`. This
corresponds to starting from a Taylor series for the derivative of a function, and building a Taylor
series for the function itself. -/
def unshift (q : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)) (z : F) : FormalMultilinearSeries 𝕜 E F
  | 0 => (continuousMultilinearCurryFin0 𝕜 E F).symm z
  | n + 1 => continuousMultilinearCurryRightEquiv' 𝕜 n E F (q n)
#align formal_multilinear_series.unshift FormalMultilinearSeries.unshift

end FormalMultilinearSeries

namespace ContinuousLinearMap

variable [CommRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]
  [ContinuousConstSMul 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [TopologicalAddGroup F] [ContinuousConstSMul 𝕜 F] [AddCommGroup G] [Module 𝕜 G]
  [TopologicalSpace G] [TopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]

/-- Composing each term `pₙ` in a formal multilinear series with a continuous linear map `f` on the
left gives a new formal multilinear series `f.comp_formal_multilinear_series p` whose general term
is `f ∘ pₙ`. -/
def compFormalMultilinearSeries (f : F →L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 E G := fun n => f.compContinuousMultilinearMap (p n)
#align continuous_linear_map.comp_formal_multilinear_series ContinuousLinearMap.compFormalMultilinearSeries

@[simp]
theorem compFormalMultilinearSeries_apply (f : F →L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F)
    (n : ℕ) : (f.compFormalMultilinearSeries p) n = f.compContinuousMultilinearMap (p n) :=
  rfl
#align continuous_linear_map.comp_formal_multilinear_series_apply ContinuousLinearMap.compFormalMultilinearSeries_apply

theorem compFormalMultilinearSeries_apply' (f : F →L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F)
    (n : ℕ) (v : Fin n → E) : (f.compFormalMultilinearSeries p) n v = f (p n v) :=
  rfl
#align continuous_linear_map.comp_formal_multilinear_series_apply' ContinuousLinearMap.compFormalMultilinearSeries_apply'

end ContinuousLinearMap

namespace FormalMultilinearSeries

section Order

variable [CommRing 𝕜] {n : ℕ} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [TopologicalAddGroup E] [ContinuousConstSMul 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
  {p : FormalMultilinearSeries 𝕜 E F}

/-- The index of the first non-zero coefficient in `p` (or `0` if all coefficients are zero). This
  is the order of the isolated zero of an analytic function `f` at a point if `p` is the Taylor
  series of `f` at that point. -/
noncomputable def order (p : FormalMultilinearSeries 𝕜 E F) : ℕ :=
  sInf { n | p n ≠ 0 }
#align formal_multilinear_series.order FormalMultilinearSeries.order

@[simp]
theorem order_zero : (0 : FormalMultilinearSeries 𝕜 E F).order = 0 := by simp [order]
#align formal_multilinear_series.order_zero FormalMultilinearSeries.order_zero

theorem ne_zero_of_order_ne_zero (hp : p.order ≠ 0) : p ≠ 0 := fun h => by simpa [h] using hp
#align formal_multilinear_series.ne_zero_of_order_ne_zero FormalMultilinearSeries.ne_zero_of_order_ne_zero

theorem order_eq_find [DecidablePred fun n => p n ≠ 0] (hp : ∃ n, p n ≠ 0) :
    p.order = Nat.find hp := by simp [order, Inf, hp]
#align formal_multilinear_series.order_eq_find FormalMultilinearSeries.order_eq_find

theorem order_eq_find' [DecidablePred fun n => p n ≠ 0] (hp : p ≠ 0) :
    p.order = Nat.find (FormalMultilinearSeries.ne_iff.mp hp) :=
  order_eq_find _
#align formal_multilinear_series.order_eq_find' FormalMultilinearSeries.order_eq_find'

theorem order_eq_zero_iff (hp : p ≠ 0) : p.order = 0 ↔ p 0 ≠ 0 := by
  classical
    have : ∃ n, p n ≠ 0 := formal_multilinear_series.ne_iff.mp hp
    simp [order_eq_find this, hp]
#align formal_multilinear_series.order_eq_zero_iff FormalMultilinearSeries.order_eq_zero_iff

theorem order_eq_zero_iff' : p.order = 0 ↔ p = 0 ∨ p 0 ≠ 0 := by
  by_cases h : p = 0 <;> simp [h, order_eq_zero_iff]
#align formal_multilinear_series.order_eq_zero_iff' FormalMultilinearSeries.order_eq_zero_iff'

theorem apply_order_ne_zero (hp : p ≠ 0) : p p.order ≠ 0 := by
  classical
    let h := formal_multilinear_series.ne_iff.mp hp
    exact (order_eq_find h).symm ▸ Nat.find_spec h
#align formal_multilinear_series.apply_order_ne_zero FormalMultilinearSeries.apply_order_ne_zero

theorem apply_order_ne_zero' (hp : p.order ≠ 0) : p p.order ≠ 0 :=
  apply_order_ne_zero (ne_zero_of_order_ne_zero hp)
#align formal_multilinear_series.apply_order_ne_zero' FormalMultilinearSeries.apply_order_ne_zero'

theorem apply_eq_zero_of_lt_order (hp : n < p.order) : p n = 0 :=
  by
  by_cases p = 0
  · simp [h]
  ·
    classical
      rw [order_eq_find' h] at hp
      simpa using Nat.find_min _ hp
#align formal_multilinear_series.apply_eq_zero_of_lt_order FormalMultilinearSeries.apply_eq_zero_of_lt_order

end Order

section Coef

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {s : E}
  {p : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 → E} {n : ℕ} {z z₀ : 𝕜} {y : Fin n → 𝕜}

open BigOperators

/-- The `n`th coefficient of `p` when seen as a power series. -/
def coeff (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) : E :=
  p n 1
#align formal_multilinear_series.coeff FormalMultilinearSeries.coeff

theorem mkPiField_coeff_eq (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) :
    ContinuousMultilinearMap.mkPiField 𝕜 (Fin n) (p.coeff n) = p n :=
  (p n).mkPiField_apply_one_eq_self
#align formal_multilinear_series.mk_pi_field_coeff_eq FormalMultilinearSeries.mkPiField_coeff_eq

@[simp]
theorem apply_eq_prod_smul_coeff : p n y = (∏ i, y i) • p.coeff n :=
  by
  convert(p n).toMultilinearMap.map_smul_univ y 1
  funext <;> simp only [Pi.one_apply, Algebra.id.smul_eq_mul, mul_one]
#align formal_multilinear_series.apply_eq_prod_smul_coeff FormalMultilinearSeries.apply_eq_prod_smul_coeff

theorem coeff_eq_zero : p.coeff n = 0 ↔ p n = 0 := by
  rw [← mk_pi_field_coeff_eq p, ContinuousMultilinearMap.mkPiField_eq_zero_iff]
#align formal_multilinear_series.coeff_eq_zero FormalMultilinearSeries.coeff_eq_zero

@[simp]
theorem apply_eq_pow_smul_coeff : (p n fun _ => z) = z ^ n • p.coeff n := by simp
#align formal_multilinear_series.apply_eq_pow_smul_coeff FormalMultilinearSeries.apply_eq_pow_smul_coeff

@[simp]
theorem norm_apply_eq_norm_coef : ‖p n‖ = ‖coeff p n‖ := by
  rw [← mk_pi_field_coeff_eq p, ContinuousMultilinearMap.norm_mkPiField]
#align formal_multilinear_series.norm_apply_eq_norm_coef FormalMultilinearSeries.norm_apply_eq_norm_coef

end Coef

section Fslope

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : FormalMultilinearSeries 𝕜 𝕜 E} {n : ℕ}

/-- The formal counterpart of `dslope`, corresponding to the expansion of `(f z - f 0) / z`. If `f`
has `p` as a power series, then `dslope f` has `fslope p` as a power series. -/
noncomputable def fslope (p : FormalMultilinearSeries 𝕜 𝕜 E) : FormalMultilinearSeries 𝕜 𝕜 E :=
  fun n => (p (n + 1)).curryLeft 1
#align formal_multilinear_series.fslope FormalMultilinearSeries.fslope

@[simp]
theorem coeff_fslope : p.fslope.coeff n = p.coeff (n + 1) :=
  by
  have : @Fin.cons n (fun _ => 𝕜) 1 (1 : Fin n → 𝕜) = 1 := Fin.cons_self_tail 1
  simp only [fslope, coeff, ContinuousMultilinearMap.curryLeft_apply, this]
#align formal_multilinear_series.coeff_fslope FormalMultilinearSeries.coeff_fslope

@[simp]
theorem coeff_iterate_fslope (k n : ℕ) : ((fslope^[k]) p).coeff n = p.coeff (n + k) := by
  induction' k with k ih generalizing p <;> first |rfl|simpa [ih]
#align formal_multilinear_series.coeff_iterate_fslope FormalMultilinearSeries.coeff_iterate_fslope

end Fslope

end FormalMultilinearSeries

section Const

/-- The formal multilinear series where all terms of positive degree are equal to zero, and the term
of degree zero is `c`. It is the power series expansion of the constant function equal to `c`
everywhere. -/
def constFormalMultilinearSeries (𝕜 : Type _) [NontriviallyNormedField 𝕜] (E : Type _)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ContinuousConstSMul 𝕜 E] [TopologicalAddGroup E]
    {F : Type _} [NormedAddCommGroup F] [TopologicalAddGroup F] [NormedSpace 𝕜 F]
    [ContinuousConstSMul 𝕜 F] (c : F) : FormalMultilinearSeries 𝕜 E F
  | 0 => ContinuousMultilinearMap.curry0 _ _ c
  | _ => 0
#align const_formal_multilinear_series constFormalMultilinearSeries

@[simp]
theorem constFormalMultilinearSeries_apply [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {c : F} {n : ℕ} (hn : n ≠ 0) :
    constFormalMultilinearSeries 𝕜 E c n = 0 :=
  Nat.casesOn n (fun hn => (hn rfl).elim) (fun _ _ => rfl) hn
#align const_formal_multilinear_series_apply constFormalMultilinearSeries_apply

end Const

