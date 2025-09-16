/-
Copyright (c) 2022 Cuma Kökmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cuma Kökmen, Yury Kudryashov
-/
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Fin.Tuple
import Mathlib.Util.Superscript

/-!
# Integral over a torus in `ℂⁿ`

In this file we define the integral of a function `f : ℂⁿ → E` over a torus
`{z : ℂⁿ | ∀ i, z i ∈ Metric.sphere (c i) (R i)}`. In order to do this, we define
`torusMap (c : ℂⁿ) (R θ : ℝⁿ)` to be the point in `ℂⁿ` given by $z_k=c_k+R_ke^{θ_ki}$,
where $i$ is the imaginary unit, then define `torusIntegral f c R` as the integral over
the cube $[0, (fun _ ↦ 2π)] = \{θ\|∀ k, 0 ≤ θ_k ≤ 2π\}$ of the Jacobian of the
`torusMap` multiplied by `f (torusMap c R θ)`.

We also define a predicate saying that `f ∘ torusMap c R` is integrable on the cube
`[0, (fun _ ↦ 2π)]`.

## Main definitions

* `torusMap c R`: the generalized multidimensional exponential map from `ℝⁿ` to `ℂⁿ` that sends
  $θ=(θ_0,…,θ_{n-1})$ to $z=(z_0,…,z_{n-1})$, where $z_k= c_k + R_ke^{θ_k i}$;

* `TorusIntegrable f c R`: a function `f : ℂⁿ → E` is integrable over the generalized torus
  with center `c : ℂⁿ` and radius `R : ℝⁿ` if `f ∘ torusMap c R` is integrable on the
  closed cube `Icc (0 : ℝⁿ) (fun _ ↦ 2 * π)`;

* `torusIntegral f c R`: the integral of a function `f : ℂⁿ → E` over a torus with
  center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ` defined as
  $\iiint_{[0, 2 * π]} (∏_{k = 1}^{n} i R_k e^{θ_k * i}) • f (c + Re^{θ_k i})\,dθ_0…dθ_{k-1}$.

## Main statements

* `torusIntegral_dim0`, `torusIntegral_dim1`, `torusIntegral_succ`: formulas for `torusIntegral`
  in cases of dimension `0`, `1`, and `n + 1`.

## Notation

- `ℝ⁰`, `ℝ¹`, `ℝⁿ`, `ℝⁿ⁺¹`: local notation for `Fin 0 → ℝ`, `Fin 1 → ℝ`, `Fin n → ℝ`, and
  `Fin (n + 1) → ℝ`, respectively;
- `ℂ⁰`, `ℂ¹`, `ℂⁿ`, `ℂⁿ⁺¹`: local notation for `Fin 0 → ℂ`, `Fin 1 → ℂ`, `Fin n → ℂ`, and
  `Fin (n + 1) → ℂ`, respectively;
- `∯ z in T(c, R), f z`: notation for `torusIntegral f c R`;
- `∮ z in C(c, R), f z`: notation for `circleIntegral f c R`, defined elsewhere;
- `∏ k, f k`: notation for `Finset.prod`, defined elsewhere;
- `π`: notation for `Real.pi`, defined elsewhere.

## Tags

integral, torus
-/


variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E]

noncomputable section

open Complex Set MeasureTheory Function Filter TopologicalSpace
open Mathlib.Tactic (superscriptTerm)

open scoped Real

local syntax:arg term:max noWs superscriptTerm : term
local macro_rules | `($t:term$n:superscript) => `(Fin $n → $t)

/-!
### `torusMap`, a parametrization of a torus
-/

/-- The n dimensional exponential map $θ_i ↦ c + R e^{θ_i*I}, θ ∈ ℝⁿ$ representing
a torus in `ℂⁿ` with center `c ∈ ℂⁿ` and generalized radius `R ∈ ℝⁿ`, so we can adjust
it to every n axis. -/
def torusMap (c : ℂⁿ) (R : ℝⁿ) : ℝⁿ → ℂⁿ := fun θ i => c i + R i * exp (θ i * I)

theorem torusMap_sub_center (c : ℂⁿ) (R : ℝⁿ) (θ : ℝⁿ) : torusMap c R θ - c = torusMap 0 R θ := by
  ext1 i; simp [torusMap]

theorem torusMap_eq_center_iff {c : ℂⁿ} {R : ℝⁿ} {θ : ℝⁿ} : torusMap c R θ = c ↔ R = 0 := by
  simp [funext_iff, torusMap, exp_ne_zero]

@[simp]
theorem torusMap_zero_radius (c : ℂⁿ) : torusMap c 0 = const ℝⁿ c :=
  funext fun _ ↦ torusMap_eq_center_iff.2 rfl

/-!
### Integrability of a function on a generalized torus
-/

/-- A function `f : ℂⁿ → E` is integrable on the generalized torus if the function
`f ∘ torusMap c R θ` is integrable on `Icc (0 : ℝⁿ) (fun _ ↦ 2 * π)`. -/
def TorusIntegrable (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) : Prop :=
  IntegrableOn (fun θ : ℝⁿ => f (torusMap c R θ)) (Icc (0 : ℝⁿ) fun _ => 2 * π) volume

namespace TorusIntegrable

variable {f g : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ}

/-- Constant functions are torus integrable -/
theorem torusIntegrable_const (a : E) (c : ℂⁿ) (R : ℝⁿ) : TorusIntegrable (fun _ => a) c R := by
  simp [TorusIntegrable, measure_Icc_lt_top]

/-- If `f` is torus integrable then `-f` is torus integrable. -/
protected nonrec theorem neg (hf : TorusIntegrable f c R) : TorusIntegrable (-f) c R := hf.neg

/-- If `f` and `g` are two torus integrable functions, then so is `f + g`. -/
protected nonrec theorem add (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    TorusIntegrable (f + g) c R :=
  hf.add hg

/-- If `f` and `g` are two torus integrable functions, then so is `f - g`. -/
protected nonrec theorem sub (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    TorusIntegrable (f - g) c R :=
  hf.sub hg

theorem torusIntegrable_zero_radius {f : ℂⁿ → E} {c : ℂⁿ} : TorusIntegrable f c 0 := by
  rw [TorusIntegrable, torusMap_zero_radius]
  apply torusIntegrable_const (f c) c 0

/-- The function given in the definition of `torusIntegral` is integrable. -/
theorem function_integrable [NormedSpace ℂ E] (hf : TorusIntegrable f c R) :
    IntegrableOn (fun θ : ℝⁿ => (∏ i, R i * exp (θ i * I) * I : ℂ) • f (torusMap c R θ))
      (Icc (0 : ℝⁿ) fun _ => 2 * π) volume := by
  refine (hf.norm.const_mul (∏ i, |R i|)).mono' ?_ ?_
  · refine (Continuous.aestronglyMeasurable ?_).smul hf.1; fun_prop
  simp [norm_smul]

end TorusIntegrable

variable [NormedSpace ℂ E] {f g : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ}

/-- The integral over a generalized torus with center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ`, defined
as the `•`-product of the derivative of `torusMap` and `f (torusMap c R θ)` -/
def torusIntegral (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) :=
  ∫ θ : ℝⁿ in Icc (0 : ℝⁿ) fun _ => 2 * π, (∏ i, R i * exp (θ i * I) * I : ℂ) • f (torusMap c R θ)

@[inherit_doc torusIntegral]
notation3 "∯ " (...) " in " "T(" c ", " R ")" ", " r:(scoped f => torusIntegral f c R) => r

theorem torusIntegral_radius_zero (hn : n ≠ 0) (f : ℂⁿ → E) (c : ℂⁿ) :
    (∯ x in T(c, 0), f x) = 0 := by
  simp only [torusIntegral, Pi.zero_apply, ofReal_zero, zero_mul, Fin.prod_const,
    zero_pow hn, zero_smul, integral_zero]

theorem torusIntegral_neg (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) :
    (∯ x in T(c, R), -f x) = -∯ x in T(c, R), f x := by simp [torusIntegral, integral_neg]

theorem torusIntegral_add (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    (∯ x in T(c, R), f x + g x) = (∯ x in T(c, R), f x) + ∯ x in T(c, R), g x := by
  simpa only [torusIntegral, smul_add, Pi.add_apply] using
    integral_add hf.function_integrable hg.function_integrable

theorem torusIntegral_sub (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    (∯ x in T(c, R), f x - g x) = (∯ x in T(c, R), f x) - ∯ x in T(c, R), g x := by
  simpa only [sub_eq_add_neg, ← torusIntegral_neg] using torusIntegral_add hf hg.neg

theorem torusIntegral_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass 𝕜 ℂ E] (a : 𝕜)
    (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) : (∯ x in T(c, R), a • f x) = a • ∯ x in T(c, R), f x := by
  simp only [torusIntegral, integral_smul, ← smul_comm a (_ : ℂ) (_ : E)]

theorem torusIntegral_const_mul (a : ℂ) (f : ℂⁿ → ℂ) (c : ℂⁿ) (R : ℝⁿ) :
    (∯ x in T(c, R), a * f x) = a * ∯ x in T(c, R), f x :=
  torusIntegral_smul a f c R

/-- If for all `θ : ℝⁿ`, `‖f (torusMap c R θ)‖` is less than or equal to a constant `C : ℝ`, then
`‖∯ x in T(c, R), f x‖` is less than or equal to `(2 * π)^n * (∏ i, |R i|) * C` -/
theorem norm_torusIntegral_le_of_norm_le_const {C : ℝ} (hf : ∀ θ, ‖f (torusMap c R θ)‖ ≤ C) :
    ‖∯ x in T(c, R), f x‖ ≤ ((2 * π) ^ (n : ℕ) * ∏ i, |R i|) * C :=
  calc
    ‖∯ x in T(c, R), f x‖ ≤ (∏ i, |R i|) * C * (volume (Icc (0 : ℝⁿ) fun _ => 2 * π)).toReal :=
      norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top fun θ _ =>
        calc
          ‖(∏ i : Fin n, R i * exp (θ i * I) * I : ℂ) • f (torusMap c R θ)‖ =
              (∏ i : Fin n, |R i|) * ‖f (torusMap c R θ)‖ := by simp [norm_smul]
          _ ≤ (∏ i : Fin n, |R i|) * C := mul_le_mul_of_nonneg_left (hf _) <| by positivity
    _ = ((2 * π) ^ (n : ℕ) * ∏ i, |R i|) * C := by
      simp only [Pi.zero_def, Real.volume_Icc_pi_toReal fun _ => Real.two_pi_pos.le, sub_zero,
        Fin.prod_const, mul_assoc, mul_comm ((2 * π) ^ (n : ℕ))]

@[simp]
theorem torusIntegral_dim0 [CompleteSpace E]
    (f : ℂ⁰ → E) (c : ℂ⁰) (R : ℝ⁰) : (∯ x in T(c, R), f x) = f c := by
  simp only [torusIntegral, Fin.prod_univ_zero, one_smul,
    Subsingleton.elim (fun _ : Fin 0 => 2 * π) 0, Icc_self, Measure.restrict_singleton, volume_pi,
    integral_dirac, Measure.pi_of_empty (fun _ : Fin 0 ↦ volume) 0,
    Measure.dirac_apply_of_mem (mem_singleton _), Subsingleton.elim (torusMap c R 0) c]

/-- In dimension one, `torusIntegral` is the same as `circleIntegral`
(up to the natural equivalence between `ℂ` and `Fin 1 → ℂ`). -/
theorem torusIntegral_dim1 (f : ℂ¹ → E) (c : ℂ¹) (R : ℝ¹) :
    (∯ x in T(c, R), f x) = ∮ z in C(c 0, R 0), f fun _ => z := by
  have H₁ : (((MeasurableEquiv.funUnique _ _).symm) ⁻¹' Icc 0 fun _ => 2 * π) = Icc 0 (2 * π) :=
    (OrderIso.funUnique (Fin 1) ℝ).symm.preimage_Icc _ _
  have H₂ : torusMap c R = fun θ _ ↦ circleMap (c 0) (R 0) (θ 0) := by
    ext θ i : 2
    rw [Subsingleton.elim i 0]; rfl
  rw [torusIntegral, circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le,
    Measure.restrict_congr_set Ioc_ae_eq_Icc,
    ← ((volume_preserving_funUnique (Fin 1) ℝ).symm _).setIntegral_preimage_emb
      (MeasurableEquiv.measurableEmbedding _), H₁, H₂]
  simp [circleMap_zero]

/-- Recurrent formula for `torusIntegral`, see also `torusIntegral_succ`. -/
theorem torusIntegral_succAbove
    {f : ℂⁿ⁺¹ → E} {c : ℂⁿ⁺¹} {R : ℝⁿ⁺¹} (hf : TorusIntegrable f c R)
    (i : Fin (n + 1)) :
    (∯ x in T(c, R), f x) =
      ∮ x in C(c i, R i), ∯ y in T(c ∘ i.succAbove, R ∘ i.succAbove), f (i.insertNth x y) := by
  set e : ℝ × ℝⁿ ≃ᵐ ℝⁿ⁺¹ := (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have heπ : (e ⁻¹' Icc 0 fun _ => 2 * π) = Icc 0 (2 * π) ×ˢ Icc (0 : ℝⁿ) fun _ => 2 * π :=
    ((Fin.insertNthOrderIso (fun _ => ℝ) i).preimage_Icc _ _).trans (Icc_prod_eq _ _)
  rw [torusIntegral, ← hem.map_eq, setIntegral_map_equiv, heπ, Measure.volume_eq_prod,
    setIntegral_prod, circleIntegral_def_Icc]
  · refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    simp +unfoldPartialApp only [e, torusIntegral, ← integral_smul,
      deriv_circleMap, i.prod_univ_succAbove _, smul_smul, torusMap, circleMap_zero]
    refine setIntegral_congr_fun measurableSet_Icc fun Θ _ => ?_
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, i.insertNth_apply_same,
      i.insertNth_apply_succAbove, (· ∘ ·), Fin.insertNthEquiv, Equiv.coe_fn_mk]
    congr 2
    simp only [funext_iff, i.forall_iff_succAbove, circleMap, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove, imp_true_iff, and_self_iff]
  · have := hf.function_integrable
    rwa [← hem.integrableOn_comp_preimage e.measurableEmbedding, heπ] at this

/-- Recurrent formula for `torusIntegral`, see also `torusIntegral_succAbove`. -/
theorem torusIntegral_succ
    {f : ℂⁿ⁺¹ → E} {c : ℂⁿ⁺¹} {R : ℝⁿ⁺¹} (hf : TorusIntegrable f c R) :
    (∯ x in T(c, R), f x) =
      ∮ x in C(c 0, R 0), ∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ), f (Fin.cons x y) := by
  simpa using torusIntegral_succAbove hf 0
