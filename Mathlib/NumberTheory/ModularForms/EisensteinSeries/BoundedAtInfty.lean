/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.MDifferentiable
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ZetaFunction

/-!
# Boundedness of Eisenstein series

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are bounded at infinity.
-/

noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane Set Filter Function Complex Manifold Matrix

open scoped Topology BigOperators Nat Classical MatrixGroups

namespace EisensteinSeries

lemma eis_bound (k : ℤ) (hk : 3 ≤ k) (z : ℍ) :
    ∀ (b : Fin 2 → ℤ), Complex.abs (eisSummand k b z) ≤
    1 / r z ^ k * (max (Int.natAbs (b 0) : ℝ) (Int.natAbs (b 1)) ^ k)⁻¹ := by
  have hk0 : 0 ≤ k := by omega
  lift k to ℕ using hk0
  intro b
  have := eis_is_bounded_on_box (k := k) (max (b 0).natAbs (b 1).natAbs) z b (Int.ofNat_zero_le k)
    (by simp)
  conv =>
    enter [2]
    rw [mul_comm]
  simp only [eisSummand, Fin.isValue, zpow_natCast, one_div, map_inv₀, map_pow, ge_iff_le, map_pow,
    Nat.cast_max, _root_.mul_inv_rev] at *
  exact this

lemma summable_lem (k : ℤ) (hk : 3 ≤ k) (z : ℍ) : Summable fun (x : Fin 2 → ℤ) =>
    Complex.abs (eisSummand k x z) := by
  apply (summable_upper_bound hk z).of_nonneg_of_le (fun _ => Complex.abs.nonneg _)
    (eis_bound k hk z)


variable {γ : Type*} [OrderedAddCommGroup γ] [UniformSpace γ] [UniformAddGroup γ]
  [OrderClosedTopology γ ] [ CompleteSpace γ]

lemma tsum_subtype_le {α : Type*} (f : α → γ) (β : Set α) (h : ∀ a : α, 0 ≤ f a)
    (hf : Summable f) : (∑' (b : β), f b) ≤ (∑' (a : α), f a) := by
  apply tsum_le_tsum_of_inj _ (Subtype.coe_injective) (by simp [h]) (by simp) (by apply hf.subtype)
  apply hf

lemma abs_le_tsum_abs (N : ℕ) (a : Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k) (z : ℍ):
    Complex.abs ((((eisensteinSeries a k))) z) ≤ ∑' (x : Fin 2 → ℤ),
      Complex.abs (eisSummand k x z) := by
  simp_rw [← Complex.norm_eq_abs, eisensteinSeries]
  apply le_trans (norm_tsum_le_tsum_norm ?_) (tsum_subtype_le (fun (x : Fin 2 → ℤ) =>
      ‖(eisSummand k x z)‖) _ (fun _ => norm_nonneg _) (summable_lem k hk z))
  apply (summable_lem k hk z).subtype

theorem upp_half_translation_N (z : ℍ) (N : ℕ) (hn : 0 < N) :
    ∃ n : ℤ, ModularGroup.T ^ (N * n) • z ∈ verticalStrip N z.im := by
  let n := Int.floor (z.re/N)
  use -n
  rw [modular_T_zpow_smul z (N * -n)]
  refine ⟨?_, (by simp only [mul_neg, Int.cast_neg, Int.cast_mul, Int.cast_natCast, vadd_im,
    le_refl])⟩
  have h : (N * (-n : ℝ) +ᵥ z).re = -N * Int.floor (z.re / N) + z.re := by
    simp only [Int.cast_natCast, mul_neg, vadd_re, neg_mul]
  norm_cast at *
  rw [h, add_comm]
  simp only [neg_mul, Int.cast_neg, Int.cast_mul, Int.cast_natCast, ge_iff_le]
  have hnn : (0 : ℝ) < (N : ℝ) := by norm_cast at *
  have h2 : z.re + -(N * n) =  z.re - n * N := by ring
  rw [h2, abs_eq_self.2 (Int.sub_floor_div_mul_nonneg (z.re : ℝ) hnn)]
  apply (Int.sub_floor_div_mul_lt (z.re : ℝ) hnn).le


lemma T_pow_N_mem_Gamma (N M: ℤ) (hNM : N ∣ M) :
    (ModularGroup.T ^ M) ∈ _root_.Gamma (Int.natAbs N) := by
  simp only [Gamma_mem, Fin.isValue, ModularGroup.coe_T_zpow, of_apply, cons_val', cons_val_zero,
    empty_val', cons_val_fin_one, Int.cast_one, cons_val_one, head_cons, head_fin_const,
    Int.cast_zero, and_self, and_true, true_and]
  refine Iff.mpr (ZMod.intCast_zmod_eq_zero_iff_dvd M (Int.natAbs N)) ?_
  simp only [Int.natCast_natAbs, abs_dvd, hNM]

theorem lvl_N_periodic (N : ℕ) (k : ℤ) (f : SlashInvariantForm (Gamma N) k) :
    ∀ (z : ℍ) (n : ℤ), f (((ModularGroup.T ^ (N * n)) ) • z) = f z := by
  intro z n
  have Hn := (T_pow_N_mem_Gamma N (N * n) (by simp))
  simp only [zpow_natCast, Int.natAbs_ofNat] at Hn
  convert (SlashInvariantForm.slash_action_eqn' k (Gamma N) f ⟨((ModularGroup.T ^ (N * n))), Hn⟩ z)
  unfold SpecialLinearGroup.coeToGL
  simp only [Fin.isValue, ModularGroup.coe_T_zpow (N * n), of_apply, cons_val', cons_val_zero,
    empty_val', cons_val_fin_one, cons_val_one, head_fin_const, Int.cast_zero, zero_mul, head_cons,
    Int.cast_one, zero_add, one_zpow, one_mul]

lemma verticalStrip_mem_le (A B B': ℝ) (hbb : B ≤ B') :
  verticalStrip A B' ⊆ verticalStrip A B := by
  simp only [verticalStrip, setOf_subset_setOf, and_imp]
  intro z ha hb
  simp only [ha, true_and]
  apply le_trans hbb hb

theorem eisensteinSeries_IsBoundedAtImInfty (N : ℕ+) (a : Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k)
    (A : SL(2, ℤ)) : IsBoundedAtImInfty ((eisensteinSeries_SIF a k).toFun ∣[(k : ℤ)] A) := by
    simp_rw [UpperHalfPlane.bounded_mem, eisensteinSeries_SIF] at *
    refine ⟨∑'(x : Fin 2 → ℤ),
      (1 / r (⟨⟨N, 2⟩, by simp⟩) ^ k) * ((max (x 0).natAbs (x 1).natAbs : ℝ) ^ k)⁻¹, 2, ?_⟩
    intro z hz
    obtain ⟨n, hn⟩ := (upp_half_translation_N z N (by simp))
    rw [eisensteinSeries_slash_apply, ← eisensteinSeries_SIF_apply,
      ← lvl_N_periodic N k (eisensteinSeries_SIF (a ᵥ* A) k) z n]
    let Z := ((ModularGroup.T ^ ((N : ℤ) * n))) • z
    apply le_trans (abs_le_tsum_abs N _ _ hk (Z))
    apply tsum_le_tsum
    · intro x
      apply le_trans ((eis_bound k hk Z x))
      simp only [one_div, Fin.isValue]
      gcongr
      · apply zpow_pos_of_pos (r_pos _)
      · have hk0 : 0 ≤ k := by linarith
        lift k to ℕ using hk0
        push_cast
        apply pow_le_pow_left (r_pos _).le
        apply r_lower_bound_on_strip (A := N) (B := 2)
            (z:= ⟨Z, (verticalStrip_mem_le (N : ℕ) 2 z.im hz) hn⟩)
    · apply (summable_upper_bound hk Z).of_nonneg_of_le (fun _ => Complex.abs.nonneg _)
        (eis_bound k hk Z)
    · apply summable_upper_bound hk
