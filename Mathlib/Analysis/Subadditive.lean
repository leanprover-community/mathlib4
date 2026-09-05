/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

open Set Filter

open scoped Topology

/-- A sequence is submultiplicative if it satisfies the inequality `u (m + n) ≤ u m * u n`
for all `m, n`. -/
@[to_additive Subadditive /-- A sequence is subadditive if it satisfies the inequality
`u (m + n) ≤ u m + u n` for all `m, n`. -/]
def Submultiplicative {α β : Type*} [Add α] [Mul β] [LE β] (u : α → β) : Prop :=
  ∀ m n, u (m + n) ≤ u m * u n

namespace Subadditive

variable {u : ℕ → ℝ} (h : Subadditive u)

/-- The limit of a bounded-below subadditive sequence. The fact that the sequence indeed tends to
this limit is given in `Subadditive.tendsto_lim` -/
@[nolint unusedArguments, irreducible]
protected def lim (_h : Subadditive u) :=
  sInf ((fun n : ℕ => u n / n) '' Ici 1)

theorem lim_le_div (hbdd : BddBelow (range fun n => u n / n)) {n : ℕ} (hn : n ≠ 0) :
    h.lim ≤ u n / n := by
  rw [Subadditive.lim]
  exact csInf_le (hbdd.mono <| image_subset_range _ _) ⟨n, hn.bot_lt, rfl⟩

include h in
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

/-- Fekete's lemma: a subadditive sequence which is bounded below converges. -/
theorem tendsto_lim (hbdd : BddBelow (range fun n => u n / n)) :
    Tendsto (fun n => u n / n) atTop (𝓝 h.lim) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun L hL => ?_⟩
  · refine eventually_atTop.2
      ⟨1, fun n hn => hl.trans_le (h.lim_le_div hbdd (zero_lt_one.trans_le hn).ne')⟩
  · obtain ⟨n, npos, hn⟩ : ∃ n : ℕ, 0 < n ∧ u n / n < L := by
      rw [Subadditive.lim] at hL
      rcases exists_lt_of_csInf_lt (by simp) hL with ⟨x, hx, xL⟩
      rcases (mem_image _ _ _).1 hx with ⟨n, hn, rfl⟩
      exact ⟨n, zero_lt_one.trans_le hn, xL⟩
    exact h.eventually_div_lt_of_div_lt npos.ne' hn

include h in
theorem tendsto_atBot (hbdd : ¬ BddBelow (range fun n ↦ u n / n)) :
    Tendsto (fun n ↦ u n / n) atTop atBot := by
  simp_rw [tendsto_atTop_atBot, ← eventually_atTop]
  intro L
  obtain ⟨-, ⟨n, rfl⟩, hn⟩ := not_bddBelow_iff.mp hbdd (min L 0)
  by_cases hn0 : n = 0
  · simp [hn0] at hn
  · exact (eventually_div_lt_of_div_lt h hn0 hn).mono (by grind)

end Subadditive

namespace Submultiplicative

variable {u : ℕ → ℝ} (h : Submultiplicative u)

/-- The limit of the nth roots of a submultiplicative sequence. The fact that the nth roots indeed
converge to this limit is given in `Submultiplicative.tendsto_lim`. -/
protected def lim (_h : Submultiplicative u) :=
  sInf ((fun n : ℕ ↦ u n ^ (n : ℝ)⁻¹) '' Ici 1)

/-- Fekete's lemma for nonnegative submultiplicative sequences:
The nth roots of a submultiplicative sequence converge. -/
theorem tendsto_lim (hbdd : ∀ n, 0 ≤ u n) : Tendsto (fun n ↦ u n ^ (n : ℝ)⁻¹) atTop (𝓝 h.lim) := by
  by_cases! hu : ∃ n, u n ≤ 0
  · obtain ⟨n, hu⟩ := hu
    replace hu m (hm : m ≥ n) : u m = 0 := by grind [le_antisymm, h n (m - n)]
    have h0 : n + 1 ≠ (0 : ℝ) := by grind
    have h1 : h.lim = 0 := by
      rw [Submultiplicative.lim]
      refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ⟨0, n + 1, by simp, by simp [hu, h0]⟩ ?_
        fun _ _ ↦ ⟨u (n + 1) ^ (n + 1 : ℝ)⁻¹, ⟨n + 1, by simp⟩, by simpa [hu, h0]⟩
      rintro - ⟨n, hn, rfl⟩
      positivity [hbdd n]
    apply tendsto_nhds_of_eventually_eq
    rw [eventually_atTop, h1]
    refine ⟨n + 1, fun m hm ↦ ?_⟩
    simp [hu m (by grind), show m ≠ 0 by grind]
  · have key : Subadditive fun n ↦ (u n).log :=
      fun a b ↦ (Real.log_le_log (hu (a + b)) (h a b)).trans_eq (Real.log_mul (hu a).ne' (hu b).ne')
    have h0 n : u n ^ (n : ℝ)⁻¹ = ((u n).log / n).exp := by
      rw [Real.rpow_def_of_pos (hu n), Real.exp_eq_exp, div_eq_mul_inv]
    simp_rw [h0]
    by_cases h' : BddBelow (range fun n ↦ (u n).log / n)
    · suffices h.lim = key.lim.exp by
        rw [this]
        exact Real.continuous_exp.continuousAt.tendsto.comp (key.tendsto_lim h')
      let : Inhabited (Ioi (0 : ℝ)) := ⟨1, by simp⟩
      let : ConditionallyCompleteLinearOrder (Ioi (0 : ℝ)) :=
        ordConnectedSubsetConditionallyCompleteLinearOrder (Ioi (0 : ℝ))
      simp_rw [Subadditive.lim, Submultiplicative.lim, h0]
      rw [Real.exp_monotone.map_csInf_of_continuousAt Real.continuous_exp.continuousAt
        Nonempty.of_subtype (h'.mono (image_subset_range _ _)), Set.image_image]
    · suffices h.lim = 0 by
        rw [this]
        exact Real.tendsto_exp_atBot.comp (key.tendsto_atBot h')
      simp_rw [Submultiplicative.lim, h0]
      apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt Nonempty.of_subtype
      · rintro - ⟨n, hn, rfl⟩
        positivity
      · intro ε hε
        obtain ⟨-, ⟨n, rfl⟩, hn⟩ := (not_bddBelow_iff.mp h') (min 0 ε.log)
        refine exists_mem_image.mpr ⟨n, (lt_inf_iff.mp hn).imp ?_ (Real.lt_log_iff_exp_lt hε).mp⟩
        contrapose!
        simp +contextual

end Submultiplicative
