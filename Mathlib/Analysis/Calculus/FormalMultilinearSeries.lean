/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.NormedSpace.Multilinear.Curry

#align_import analysis.calculus.formal_multilinear_series from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Formal multilinear series

In this file we define `FormalMultilinearSeries 𝕜 E F` to be a family of `n`-multilinear maps for
all `n`, designed to model the sequence of derivatives of a function. In other files we use this
notion to define `C^n` functions (called `contDiff` in `mathlib`) and analytic functions.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

## Tags

multilinear, formal series
-/


noncomputable section

open Set Fin Topology

-- Porting note: added explicit universes to fix compile
universe u u' v w x
variable {𝕜 : Type u} {𝕜' : Type u'} {E : Type v} {F : Type w} {G : Type x}

section

variable [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]
  [ContinuousConstSMul 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [TopologicalAddGroup F] [ContinuousConstSMul 𝕜 F] [AddCommGroup G] [Module 𝕜 G]
  [TopologicalSpace G] [TopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]

/-- A formal multilinear series over a field `𝕜`, from `E` to `F`, is given by a family of
multilinear maps from `E^n` to `F` for all `n`. -/
@[nolint unusedArguments]
def FormalMultilinearSeries (𝕜 : Type*) (E : Type*) (F : Type*) [Ring 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [TopologicalAddGroup F]
    [ContinuousConstSMul 𝕜 F] :=
  ∀ n : ℕ, E[×n]→L[𝕜] F
#align formal_multilinear_series FormalMultilinearSeries

-- Porting note: was `deriving`
instance : AddCommGroup (FormalMultilinearSeries 𝕜 E F) :=
  inferInstanceAs <| AddCommGroup <| ∀ n : ℕ, E[×n]→L[𝕜] F

instance : Inhabited (FormalMultilinearSeries 𝕜 E F) :=
  ⟨0⟩

section Module

instance (𝕜') [Semiring 𝕜'] [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [SMulCommClass 𝕜 𝕜' F] :
    Module 𝕜' (FormalMultilinearSeries 𝕜 E F) :=
  inferInstanceAs <| Module 𝕜' <| ∀ n : ℕ, E[×n]→L[𝕜] F

end Module

namespace FormalMultilinearSeries

@[simp] -- Porting note (#10756): new theorem; was not needed in Lean 3
theorem zero_apply (n : ℕ) : (0 : FormalMultilinearSeries 𝕜 E F) n = 0 := rfl

@[simp] -- Porting note (#10756): new theorem; was not needed in Lean 3
theorem neg_apply (f : FormalMultilinearSeries 𝕜 E F) (n : ℕ) : (-f) n = - f n := rfl

@[ext] -- Porting note (#10756): new theorem
protected theorem ext {p q : FormalMultilinearSeries 𝕜 E F} (h : ∀ n, p n = q n) : p = q :=
  funext h

protected theorem ext_iff {p q : FormalMultilinearSeries 𝕜 E F} : p = q ↔ ∀ n, p n = q n :=
  Function.funext_iff
#align formal_multilinear_series.ext_iff FormalMultilinearSeries.ext_iff

protected theorem ne_iff {p q : FormalMultilinearSeries 𝕜 E F} : p ≠ q ↔ ∃ n, p n ≠ q n :=
  Function.ne_iff
#align formal_multilinear_series.ne_iff FormalMultilinearSeries.ne_iff

/-- Cartesian product of two formal multilinear series (with the same field `𝕜` and the same source
space, but possibly different target spaces). -/
def prod (p : FormalMultilinearSeries 𝕜 E F) (q : FormalMultilinearSeries 𝕜 E G) :
    FormalMultilinearSeries 𝕜 E (F × G)
  | n => (p n).prod (q n)

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
  subst n
  congr with ⟨i, hi⟩
  exact h2 i hi hi
#align formal_multilinear_series.congr FormalMultilinearSeries.congr

/-- Composing each term `pₙ` in a formal multilinear series with `(u, ..., u)` where `u` is a fixed
continuous linear map, gives a new formal multilinear series `p.compContinuousLinearMap u`. -/
def compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) :
    FormalMultilinearSeries 𝕜 E G := fun n => (p n).compContinuousLinearMap fun _ : Fin n => u
#align formal_multilinear_series.comp_continuous_linear_map FormalMultilinearSeries.compContinuousLinearMap

@[simp]
theorem compContinuousLinearMap_apply (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) (n : ℕ)
    (v : Fin n → E) : (p.compContinuousLinearMap u) n v = p n (u ∘ v) :=
  rfl
#align formal_multilinear_series.comp_continuous_linear_map_apply FormalMultilinearSeries.compContinuousLinearMap_apply

variable (𝕜) [Ring 𝕜'] [SMul 𝕜 𝕜']
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
as multilinear maps into `E →L[𝕜] F`. If `p` is the Taylor series (`HasFTaylorSeriesUpTo`) of a
function, then `p.shift` is the Taylor series of the derivative of the function. Note that the
`p.sum` of a Taylor series `p` does not give the original function; for a formal multilinear
series that sums to the derivative of `p.sum`, see `HasFPowerSeriesOnBall.fderiv`. -/
def shift : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F) := fun n => (p n.succ).curryRight
#align formal_multilinear_series.shift FormalMultilinearSeries.shift

/-- Adding a zeroth term to a formal multilinear series taking values in `E →L[𝕜] F`. This
corresponds to starting from a Taylor series (`HasFTaylorSeriesUpTo`) for the derivative of a
function, and building a Taylor series for the function itself. -/
def unshift (q : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)) (z : F) : FormalMultilinearSeries 𝕜 E F
  | 0 => (continuousMultilinearCurryFin0 𝕜 E F).symm z
  | n + 1 => -- Porting note: added type hint here and explicit universes to fix compile
    (continuousMultilinearCurryRightEquiv' 𝕜 n E F :
      (E [×n]→L[𝕜] E →L[𝕜] F) → (E [×n.succ]→L[𝕜] F)) (q n)
#align formal_multilinear_series.unshift FormalMultilinearSeries.unshift

end FormalMultilinearSeries

section

variable [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]
  [ContinuousConstSMul 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [TopologicalAddGroup F] [ContinuousConstSMul 𝕜 F] [AddCommGroup G] [Module 𝕜 G]
  [TopologicalSpace G] [TopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]

namespace ContinuousLinearMap

/-- Composing each term `pₙ` in a formal multilinear series with a continuous linear map `f` on the
left gives a new formal multilinear series `f.compFormalMultilinearSeries p` whose general term
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

namespace ContinuousMultilinearMap

variable {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [∀ i, TopologicalSpace (E i)] [∀ i, TopologicalAddGroup (E i)]
  [∀ i, ContinuousConstSMul 𝕜 (E i)] [Fintype ι] (f : ContinuousMultilinearMap 𝕜 E F)

/-- Realize a ContinuousMultilinearMap on `∀ i : ι, E i` as the evaluation of a
FormalMultilinearSeries by choosing an arbitrary identification `ι ≃ Fin (Fintype.card ι)`. -/
noncomputable def toFormalMultilinearSeries : FormalMultilinearSeries 𝕜 (∀ i, E i) F :=
  fun n ↦ if h : Fintype.card ι = n then
    (f.compContinuousLinearMap .proj).domDomCongr (Fintype.equivFinOfCardEq h)
  else 0

end ContinuousMultilinearMap

end

namespace FormalMultilinearSeries

section Order

variable [Ring 𝕜] {n : ℕ} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
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

theorem ne_zero_of_order_ne_zero (hp : p.order ≠ 0) : p ≠ 0 := fun h => by simp [h] at hp
#align formal_multilinear_series.ne_zero_of_order_ne_zero FormalMultilinearSeries.ne_zero_of_order_ne_zero

theorem order_eq_find [DecidablePred fun n => p n ≠ 0] (hp : ∃ n, p n ≠ 0) :
    p.order = Nat.find hp := by convert Nat.sInf_def hp
#align formal_multilinear_series.order_eq_find FormalMultilinearSeries.order_eq_find

theorem order_eq_find' [DecidablePred fun n => p n ≠ 0] (hp : p ≠ 0) :
    p.order = Nat.find (FormalMultilinearSeries.ne_iff.mp hp) :=
  order_eq_find _
#align formal_multilinear_series.order_eq_find' FormalMultilinearSeries.order_eq_find'

theorem order_eq_zero_iff' : p.order = 0 ↔ p = 0 ∨ p 0 ≠ 0 := by
  simpa [order, Nat.sInf_eq_zero, FormalMultilinearSeries.ext_iff, eq_empty_iff_forall_not_mem]
    using or_comm
#align formal_multilinear_series.order_eq_zero_iff' FormalMultilinearSeries.order_eq_zero_iff'

theorem order_eq_zero_iff (hp : p ≠ 0) : p.order = 0 ↔ p 0 ≠ 0 := by
  simp [order_eq_zero_iff', hp]
#align formal_multilinear_series.order_eq_zero_iff FormalMultilinearSeries.order_eq_zero_iff

theorem apply_order_ne_zero (hp : p ≠ 0) : p p.order ≠ 0 :=
  Nat.sInf_mem (FormalMultilinearSeries.ne_iff.1 hp)
#align formal_multilinear_series.apply_order_ne_zero FormalMultilinearSeries.apply_order_ne_zero

theorem apply_order_ne_zero' (hp : p.order ≠ 0) : p p.order ≠ 0 :=
  apply_order_ne_zero (ne_zero_of_order_ne_zero hp)
#align formal_multilinear_series.apply_order_ne_zero' FormalMultilinearSeries.apply_order_ne_zero'

theorem apply_eq_zero_of_lt_order (hp : n < p.order) : p n = 0 :=
  by_contra <| Nat.not_mem_of_lt_sInf hp
#align formal_multilinear_series.apply_eq_zero_of_lt_order FormalMultilinearSeries.apply_eq_zero_of_lt_order

end Order

section Coef

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {s : E}
  {p : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 → E} {n : ℕ} {z z₀ : 𝕜} {y : Fin n → 𝕜}

/-- The `n`th coefficient of `p` when seen as a power series. -/
def coeff (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) : E :=
  p n 1
#align formal_multilinear_series.coeff FormalMultilinearSeries.coeff

theorem mkPiRing_coeff_eq (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) :
    ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (p.coeff n) = p n :=
  (p n).mkPiRing_apply_one_eq_self
#align formal_multilinear_series.mk_pi_field_coeff_eq FormalMultilinearSeries.mkPiRing_coeff_eq

@[simp]
theorem apply_eq_prod_smul_coeff : p n y = (∏ i, y i) • p.coeff n := by
  convert (p n).toMultilinearMap.map_smul_univ y 1
  simp only [Pi.one_apply, Algebra.id.smul_eq_mul, mul_one]
#align formal_multilinear_series.apply_eq_prod_smul_coeff FormalMultilinearSeries.apply_eq_prod_smul_coeff

theorem coeff_eq_zero : p.coeff n = 0 ↔ p n = 0 := by
  rw [← mkPiRing_coeff_eq p, ContinuousMultilinearMap.mkPiRing_eq_zero_iff]
#align formal_multilinear_series.coeff_eq_zero FormalMultilinearSeries.coeff_eq_zero

theorem apply_eq_pow_smul_coeff : (p n fun _ => z) = z ^ n • p.coeff n := by simp
#align formal_multilinear_series.apply_eq_pow_smul_coeff FormalMultilinearSeries.apply_eq_pow_smul_coeff

@[simp]
theorem norm_apply_eq_norm_coef : ‖p n‖ = ‖coeff p n‖ := by
  rw [← mkPiRing_coeff_eq p, ContinuousMultilinearMap.norm_mkPiRing]
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
theorem coeff_fslope : p.fslope.coeff n = p.coeff (n + 1) := by
  simp only [fslope, coeff, ContinuousMultilinearMap.curryLeft_apply]
  congr 1
  exact Fin.cons_self_tail 1
#align formal_multilinear_series.coeff_fslope FormalMultilinearSeries.coeff_fslope

@[simp]
theorem coeff_iterate_fslope (k n : ℕ) : (fslope^[k] p).coeff n = p.coeff (n + k) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih => simp [ih, add_assoc]
#align formal_multilinear_series.coeff_iterate_fslope FormalMultilinearSeries.coeff_iterate_fslope

end Fslope

end FormalMultilinearSeries

section Const

/-- The formal multilinear series where all terms of positive degree are equal to zero, and the term
of degree zero is `c`. It is the power series expansion of the constant function equal to `c`
everywhere. -/
def constFormalMultilinearSeries (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ContinuousConstSMul 𝕜 E] [TopologicalAddGroup E]
    {F : Type*} [NormedAddCommGroup F] [TopologicalAddGroup F] [NormedSpace 𝕜 F]
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

section Linear

variable [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace ContinuousLinearMap

/-- Formal power series of a continuous linear map `f : E →L[𝕜] F` at `x : E`:
`f y = f x + f (y - x)`. -/
def fpowerSeries (f : E →L[𝕜] F) (x : E) : FormalMultilinearSeries 𝕜 E F
  | 0 => ContinuousMultilinearMap.curry0 𝕜 _ (f x)
  | 1 => (continuousMultilinearCurryFin1 𝕜 E F).symm f
  | _ => 0
#align continuous_linear_map.fpower_series ContinuousLinearMap.fpowerSeries

theorem fpowerSeries_apply_zero (f : E →L[𝕜] F) (x : E) :
    f.fpowerSeries x 0 = ContinuousMultilinearMap.curry0 𝕜 _ (f x) :=
  rfl

theorem fpowerSeries_apply_one (f : E →L[𝕜] F) (x : E) :
    f.fpowerSeries x 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm f :=
  rfl

theorem fpowerSeries_apply_add_two (f : E →L[𝕜] F) (x : E) (n : ℕ) : f.fpowerSeries x (n + 2) = 0 :=
  rfl
#align continuous_linear_map.fpower_series_apply_add_two ContinuousLinearMap.fpowerSeries_apply_add_two

attribute
  [eqns fpowerSeries_apply_zero fpowerSeries_apply_one fpowerSeries_apply_add_two] fpowerSeries
attribute [simp] fpowerSeries

end ContinuousLinearMap

end Linear
