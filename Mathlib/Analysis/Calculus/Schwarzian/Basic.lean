/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Schwarzian derivative

In this file we define the Schwarzian derivative of a $C^3$ function at a point as
$$ S(f)()=\frac{2f'''(x)f'(x) - 3(f''(x))^2}{2f'(x)^2}. $$
-/

open scoped Filter BigOperators Topology
open Set Function

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

@[irreducible]
noncomputable def schwarzianWithin (f : 𝕜 → 𝕜) (s : Set 𝕜) (x : 𝕜) : 𝕜 :=
  (2 * iteratedDerivWithin 3 f s x * derivWithin f s x -
    3 * iteratedDerivWithin 2 f s x ^ 2) / (2 * derivWithin f s x ^ 2)

-- TODO: fix notation so that parentheses aren't required
scoped[Schwarzian] notation3 "𝓢[" s "] " f:100 => schwarzianWithin f s
open Schwarzian

noncomputable def schwarzian (f : 𝕜 → 𝕜) (x : 𝕜) : 𝕜 := (𝓢[univ] f) x

scoped[Schwarzian] notation3 "𝓢" => schwarzian

lemma schwarzian_def (f : 𝕜 → 𝕜) : 𝓢 f = fun x ↦
    (2 * iteratedDeriv 3 f x * deriv f x - 3 * iteratedDeriv 2 f x ^ 2) / (2 * deriv f x ^ 2) := by
  ext x
  simp [schwarzian, schwarzianWithin, iteratedDerivWithin_univ, derivWithin_univ]

lemma schwarzianWithin_const_apply (c : 𝕜) (s : Set 𝕜) (x : 𝕜) :
    schwarzianWithin (fun _ ↦ c) s x = 0 := by
  simp [schwarzianWithin]

lemma schwarzian_const_apply (c x : 𝕜) : 𝓢 (fun _ ↦ c) x = 0 :=
  schwarzianWithin_const_apply ..

@[simp]
lemma schwarzianWithin_const (c : 𝕜) : schwarzianWithin (fun _ ↦ c) = 0 := by
  ext
  apply schwarzianWithin_const_apply

@[simp]
lemma schwarzian_const (c : 𝕜) : 𝓢 (fun _ ↦ c) = 0 := funext <| schwarzian_const_apply c

@[simp] -- TODO: drop `[OfNat 𝕜 n]`
lemma schwarzianWithin_ofNat (n : ℕ) [OfNat 𝕜 n] : schwarzianWithin (ofNat(n) : 𝕜 → 𝕜) = 0 :=
  schwarzianWithin_const _

@[simp]
lemma schwarzian_ofNat (n : ℕ) [OfNat 𝕜 n] : 𝓢 (ofNat(n) : 𝕜 → 𝕜) = 0 :=
  schwarzian_const _

lemma schwarzian_const_mul_apply (c x : 𝕜) : 𝓢 (c * ·) x = 0 := by
  simp [schwarzian_def, iteratedDeriv_eq_iterate, deriv_const_mul_field' (v := (·))]

lemma schwarzian_id_apply (x : 𝕜) : 𝓢 id x = 0 := by
  simpa using schwarzian_const_mul_apply 1 x

@[simp] lemma schwarzian_id : 𝓢 (id : 𝕜 → 𝕜) = 0 := funext schwarzian_id_apply

@[simp] lemma schwarzian_id' : 𝓢 (· : 𝕜 → 𝕜) = 0 := schwarzian_id

@[simp]
lemma schwarzian_fun_add_const (f : 𝕜 → 𝕜) (c : 𝕜) : 𝓢 (f · + c) = 𝓢 f := by
  simp [schwarzian_def, iteratedDeriv_eq_iterate]

@[simp]
lemma schwarzian_const_add_fun (f : 𝕜 → 𝕜) (c : 𝕜) : 𝓢 (c + f ·) = 𝓢 f := by
  simpa only [add_comm] using schwarzian_fun_add_const f c

@[simp]
lemma schwarzian_const_add (c : 𝕜) : 𝓢 (c + ·) = 0 := by
  rw [schwarzian_const_add_fun, schwarzian_id'] -- TODO: `simp` fails to use this lemma; why?

lemma schwarzian_zpow_apply {m : ℤ} (hm : (m : 𝕜) ≠ 0) (x : 𝕜) :
    𝓢 (· ^ m) x = - (m ^ 2 - 1) / (2 * x ^ 2) := by
  have hm' : m ≠ 0 := ne_of_apply_ne (Int.cast (R := 𝕜)) <| by simpa
  simp? [schwarzian_def, deriv_zpow, iteratedDeriv_eq_iterate, Finset.prod_range_succ] says
    simp only [schwarzian_def, iteratedDeriv_eq_iterate, iter_deriv_zpow', Finset.prod_range_succ,
      Finset.range_one, Finset.prod_singleton, Nat.cast_zero, sub_zero, Nat.cast_one,
      Nat.cast_ofNat, deriv_zpow, neg_sub]
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne m 1 with rfl | hm₁
    · simp
    · simp [zero_zpow (m - 1) (by omega)]
  · rcases eq_or_ne (2 : 𝕜) 0 with h2 | h2
    · simp [h2]
    · field_simp (disch := simp [*, zpow_eq_zero_iff]) [zpow_sub₀ hx, zpow_ofNat]
      ring

@[simp]
lemma schwarzian_zpow {m : ℤ} (hm : (m : 𝕜) ≠ 0):
    𝓢 (· ^ m : 𝕜 → 𝕜) = fun x : 𝕜 ↦ - (m ^ 2 - 1) / (2 * x ^ 2) :=
  funext <| schwarzian_zpow_apply hm

@[simp]
lemma schwarzian_pow {m : ℕ} (hm : (m : 𝕜) ≠ 0) :
    𝓢 (· ^ m : 𝕜 → 𝕜) = fun x : 𝕜 ↦ - (m ^ 2 - 1) / (2 * x ^ 2) := by
  simpa using schwarzian_zpow (𝕜 := 𝕜) (m := m) (mod_cast hm)

@[simp]
lemma schwarzian_inv [CharZero 𝕜] : 𝓢 (·⁻¹ : 𝕜 → 𝕜) = 0 := by
  simpa using schwarzian_zpow (𝕜 := 𝕜) (m := -1) (by simp)

lemma schwarzian_comp_apply {f g : 𝕜 → 𝕜} {x : 𝕜} (hf : ContDiffAt 𝕜 3 f (g x))
    (hf₀ : deriv f (g x) ≠ 0) (hg : ContDiffAt 𝕜 3 g x) :
    𝓢 (f ∘ g) x = (𝓢 f (g x)) * deriv g x ^ 2 + 𝓢 g x := by
  simp only [schwarzian_def]
  rw [iteratedDeriv_comp_three hf hg, iteratedDeriv_comp_two, deriv_comp]
  · rcases eq_or_ne (deriv g x) 0 with hg₀ | hg₀
    · simp [hg₀]
    · rcases eq_or_ne (2 : 𝕜) 0 with h2 | h2
      · simp [h2]
      · field_simp; ring
  · exact hf.differentiableAt <| by decide
  · exact hg.differentiableAt <| by decide
  · exact hf.of_le <| by decide
  · exact hg.of_le <| by decide

-- TODO: move
lemma DifferentiableAt.iterate' {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : E → E} {x : E} {n : ℕ} (h : ∀ k < n, DifferentiableAt 𝕜 f (f^[k] x)) :
    DifferentiableAt 𝕜 (f^[n]) x := by
  induction n with
  | zero => simp
  | succ n ihn =>
    rw [iterate_succ']
    exact (h n n.lt_succ_self).comp _ <| ihn fun k hk ↦ h k <| hk.trans n.lt_succ_self

-- TODO: move
lemma deriv_iterate_apply {f : 𝕜 → 𝕜} {x : 𝕜} {n : ℕ}
    (h : ∀ k < n, DifferentiableAt 𝕜 f (f^[k] x)) :
    deriv (f^[n]) x = ∏ k ∈ .range n, deriv f (f^[k] x) := by
  induction n with
  | zero => simp
  | succ n ihn =>
    rw [Nat.forall_lt_succ_right] at h
    rw [iterate_succ', deriv_comp _ h.2 (.iterate' h.1), ihn h.1, Finset.prod_range_succ, mul_comm]

lemma deriv_iterate_eq_pow {f : 𝕜 → 𝕜} {x : 𝕜} {n : ℕ} (h : DifferentiableAt 𝕜 f x)
    (hx : IsFixedPt f x) : deriv (f^[n]) x = deriv f x ^ n := by
  rw [deriv_iterate_apply] <;> simp [(hx.iterate _).eq, h]

lemma ContDiffAt.iterate {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : E → E} {x : E} {m : WithTop ℕ∞} {n : ℕ} (h : ∀ k < n, ContDiffAt 𝕜 m f (f^[k] x)) :
    ContDiffAt 𝕜 m (f^[n]) x := by
  induction n with
  | zero => simp [contDiffAt_id]
  | succ n ihn =>
    rw [iterate_succ']
    exact (h n n.lt_succ_self).comp _ <| ihn fun k hk ↦ h k <| hk.trans n.lt_succ_self

lemma schwarzian_iterate_apply {f : 𝕜 → 𝕜} {x : 𝕜} {n : ℕ}
    (hcontDiff : ∀ k < n, ContDiffAt 𝕜 3 f (f^[k] x))
    (hf₀ : ∀ k > 0, k < n → deriv f (f^[k] x) ≠ 0) :
    𝓢 (f^[n]) x = ∑ k ∈ .range n, (𝓢 f (f^[k] x)) * ∏ j ∈ .range k, deriv f (f^[j] x) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ihn =>
    rcases eq_or_ne n 0 with rfl | hn₀
    · simp
    simp only [Nat.forall_lt_succ_right, @forall_swap (_ > 0) (_ < _)] at hcontDiff hf₀
    rw [iterate_succ', schwarzian_comp_apply, Finset.sum_range_succ, ihn, add_comm,
      deriv_iterate_apply, Finset.prod_pow]
    · exact fun k hk ↦ (hcontDiff.1 k hk).differentiableAt <| by decide
    · exact hcontDiff.1
    · exact fun k hk₀ hkn ↦ hf₀.1 k hkn hk₀
    · exact hcontDiff.2
    · exact hf₀.2 (Nat.pos_of_ne_zero hn₀)
    · exact .iterate hcontDiff.1
