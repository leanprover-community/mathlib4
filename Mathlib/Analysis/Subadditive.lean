/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Convergence of subadditive sequences

A subadditive sequence `u : ℕ → ℝ` is a sequence satisfying `u (m + n) ≤ u m + u n` for all `m, n`.
We define this notion as `Subadditive u`, and prove in `Subadditive.tendsto_lim` that, if `u n / n`
is bounded below, then it converges to a limit (that we denote by `Subadditive.lim` for
convenience). This result is known as Fekete's lemma in the literature.

## TODO

Define a bundled `SubadditiveHom`, use it.
-/

@[expose] public section

noncomputable section

open Set Filter Topology

/-- A sequence is submultiplicative if it satisfies the inequality `u (m + n) ≤ u m * u n`
for all `m, n`. -/
@[to_additive Subadditive /-- A sequence is subadditive if it satisfies the inequality
`u (m + n) ≤ u m + u n` for all `m, n`. -/]
def Submultiplicative {α β : Type*} [Add α] [Mul β] [LE β] (u : α → β) : Prop :=
  ∀ m n, u (m + n) ≤ u m * u n

namespace Submultiplicative

variable {u : ℕ → ℝ} (h : Submultiplicative u)

/-- The limit of the nth roots of a submultiplicative sequence. The fact that the nth roots indeed
converge to this limit is given in `Submultiplicative.tendsto_lim`. -/
protected def lim (_h : Submultiplicative u) :=
  sInf ((fun n : ℕ ↦ u n ^ (n : ℝ)⁻¹) '' Ici 1)

theorem lim_le_rpow (hbdd : ∀ n, 0 ≤ u n) {n : ℕ} (hn : n ≠ 0) : h.lim ≤ u n ^ (n : ℝ)⁻¹ := by
  refine csInf_le ⟨0, ?_⟩ ⟨n, hn.pos, rfl⟩
  rintro - ⟨n, hn, rfl⟩
  exact Real.rpow_nonneg (hbdd n) n⁻¹

include h in
theorem apply_mul_add_le (k n r) (hbdd : 0 ≤ u n) : u (k * n + r) ≤ u n ^ k * u r := by
  induction k with
  | zero => simp
  | succ k IH => grw [add_one_mul, add_right_comm, h (k * n + r) n, IH, mul_right_comm, pow_succ]

include h in
theorem eventually_rpow_lt_of_rpow_lt (hbdd : ∀ k, 0 ≤ u k) {L : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hL : u n ^ (n : ℝ)⁻¹ < L) : ∀ᶠ p in atTop, u p ^ (p : ℝ)⁻¹ < L := by
  /- It suffices to prove the statement for each arithmetic progression `(n * · + r)`. -/
  refine .atTop_of_arithmetic hn fun r hrn ↦ ?_
  /- `(u n ^ x * u r) ^ (x * n + r)⁻¹` tends to `u n ^ n⁻¹ < L`, hence
  `(u n ^ x * u r) ^ (x * n + r)⁻¹ < L` for sufficiently large `x`. -/
  by_cases hur : u r = 0
  · replace hur (m : ℕ) (hrm : r ≤ m) : u m = 0 := by grind [le_antisymm, h r (m - r)]
    refine (eventually_ne_atTop 0).mono fun m hm ↦ ?_
    rw [hur n hrn.le, Real.zero_rpow (by simpa)] at hL
    rwa [hur (n * m + r) (r.le_add_left (n * m)), Real.zero_rpow] at ⊢
    rw [ne_eq, inv_eq_zero, Nat.cast_eq_zero, Nat.add_eq_zero_iff, mul_eq_zero]
    grind
  have A : Tendsto (fun x : ℝ ↦ (u n * u r ^ x⁻¹) ^ (n + r / x)⁻¹) atTop _ :=
    (Real.continuousAt_rpow _ (by simp [hn.pos])).tendsto.comp <|
      (((((Real.continuous_const_rpow hur).tendsto' 0 1 (u r).rpow_zero).comp
        tendsto_inv_atTop_zero).const_mul (u n)).prodMk_nhds
          ((tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).inv₀ (by simpa)))
  have B : Tendsto (fun x : ℝ ↦ (u n ^ x * u r) ^ (x * n + r)⁻¹) atTop (𝓝 (u n ^ (n : ℝ)⁻¹)) := by
    rw [mul_one, add_zero] at A
    refine A.congr' <| (eventually_ne_atTop 0).mono fun x hx ↦ ?_
    rw [add_div' _ _ _ hx, inv_div, div_eq_mul_inv, Real.rpow_mul (by bound),
      Real.mul_rpow (hbdd n) (by bound), Real.rpow_inv_rpow (hbdd r) hx, mul_comm _ x]
  refine ((B.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hL)).mono fun k hk ↦ ?_
  grw [mul_comm, h.apply_mul_add_le k n r (hbdd n)]
  · simpa using hk
  · exact hbdd (k * n +r)

/-- Fekete's lemma for nonnegative submultiplicative sequences:
The nth roots of a submultiplicative sequence converge. -/
theorem tendsto_lim (hbdd : ∀ n, 0 ≤ u n) : Tendsto (fun n ↦ u n ^ (n : ℝ)⁻¹) atTop (𝓝 h.lim) := by
  refine tendsto_order.mpr ⟨fun l hl ↦ ?_, fun L hL ↦ ?_⟩
  · exact (eventually_ne_atTop 0).mono fun n hn ↦ hl.trans_le (h.lim_le_rpow hbdd hn)
  · obtain ⟨n, npos, hn⟩ : ∃ n : ℕ, 0 < n ∧ u n ^ (n : ℝ)⁻¹ < L := by
      obtain ⟨-, ⟨n, hn, rfl⟩, xL⟩ := exists_lt_of_csInf_lt (by simp) hL
      exact ⟨n, hn, xL⟩
    exact h.eventually_rpow_lt_of_rpow_lt hbdd npos.ne' hn

end Submultiplicative

namespace Subadditive

variable {u : ℕ → ℝ} (h : Subadditive u)

/-- The limit of a bounded-below subadditive sequence. The fact that the sequence indeed tends to
this limit is given in `Subadditive.tendsto_lim` -/
@[nolint unusedArguments, irreducible]
protected def lim (_h : Subadditive u) :=
  sInf ((fun n : ℕ => u n / n) '' Ici 1)

@[deprecated "No longer needed." (since := "2026-08-20")]
theorem lim_le_div (hbdd : BddBelow (range fun n => u n / n)) {n : ℕ} (hn : n ≠ 0) :
    h.lim ≤ u n / n := by
  rw [Subadditive.lim]
  exact csInf_le (hbdd.mono <| image_subset_range _ _) ⟨n, hn.bot_lt, rfl⟩

include h in
@[deprecated "No longer needed." (since := "2026-08-20")]
theorem apply_mul_add_le (k n r) : u (k * n + r) ≤ k * u n + u r := by
  induction k with
  | zero => simp only [Nat.cast_zero, zero_mul, zero_add]; rfl
  | succ k IH =>
    calc
      u ((k + 1) * n + r) = u (n + (k * n + r)) := by congr 1; ring
      _ ≤ u n + u (k * n + r) := h _ _
      _ ≤ u n + (k * u n + u r) := by grw [IH]
      _ = (k + 1 : ℕ) * u n + u r := by simp; ring

include h in
@[deprecated "No longer needed." (since := "2026-08-20")]
theorem eventually_div_lt_of_div_lt {L : ℝ} {n : ℕ} (hn : n ≠ 0) (hL : u n / n < L) :
    ∀ᶠ p in atTop, u p / p < L := by
  /- It suffices to prove the statement for each arithmetic progression `(n * · + r)`. -/
  refine .atTop_of_arithmetic hn fun r _ => ?_
  /- `(k * u n + u r) / (k * n + r)` tends to `u n / n < L`, hence
  `(k * u n + u r) / (k * n + r) < L` for sufficiently large `k`. -/
  have A : Tendsto (fun x : ℝ => (u n + u r / x) / (n + r / x)) atTop (𝓝 ((u n + 0) / (n + 0))) :=
    (tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop tendsto_id).div
      (tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop tendsto_id) <| by simpa
  have B : Tendsto (fun x => (x * u n + u r) / (x * n + r)) atTop (𝓝 (u n / n)) := by
    rw [add_zero, add_zero] at A
    refine A.congr' <| (eventually_ne_atTop 0).mono fun x hx => ?_
    simp only [add_div' _ _ _ hx, div_div_div_cancel_right₀ hx, mul_comm]
  refine ((B.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hL)).mono fun k hk => ?_
  /- Finally, we use an upper estimate on `u (k * n + r)` to get an estimate on
  `u (k * n + r) / (k * n + r)`. -/
  rw [mul_comm]
  refine lt_of_le_of_lt ?_ hk
  simp only [(· ∘ ·), ← Nat.cast_add, ← Nat.cast_mul]
  gcongr
  apply h.apply_mul_add_le

include h in
theorem submultiplicative_exp : Submultiplicative fun n ↦ (u n).exp :=
  fun a b ↦ (Real.exp_le_exp_of_le (h a b)).trans_eq  (Real.exp_add (u a) (u b))

/-- Fekete's lemma: a subadditive sequence which is bounded below converges. -/
theorem tendsto_lim (hbdd : BddBelow (range fun n => u n / n)) :
    Tendsto (fun n => u n / n) atTop (𝓝 h.lim) := by
  have h0 n : (u n).exp ^ (n : ℝ)⁻¹ = (u n / n).exp := by rw [← Real.exp_mul, div_eq_mul_inv]
  have key := h.submultiplicative_exp.tendsto_lim (by bound)
  suffices h.lim.exp = h.submultiplicative_exp.lim by
    rw [← this] at key
    exact (key.congr h0).of_tendsto_comp (g := Real.exp) (by simp)
  let : Inhabited (Ioi (0 : ℝ)) := ⟨1, by simp⟩
  let : ConditionallyCompleteLinearOrder (Ioi (0 : ℝ)) :=
    ordConnectedSubsetConditionallyCompleteLinearOrder (Ioi (0 : ℝ))
  simp_rw [Subadditive.lim, Submultiplicative.lim, h0]
  rw [Real.exp_monotone.map_csInf_of_continuousAt Real.continuous_exp.continuousAt
    Nonempty.of_subtype (hbdd.mono (image_subset_range _ _)), Set.image_image]

end Subadditive
