import Mathlib.Tactic.Tendsto.Multiseries.Operations.Pow

open Filter Asymptotics

namespace TendstoTactic

namespace PreMS

open LazySeries Stream' Seq

noncomputable def npowSeriesFrom (n : ℕ) (acc : ℝ) (k : ℕ) : LazySeries :=
  let g : (ℝ × ℕ) → Option (ℝ × (ℝ × ℕ)) := fun (acc, m) =>
    if m ≤ n then
      some (acc, (acc * (n - m) / (m + 1), m + 1))
    else
      none
  Seq.corec g (acc, k)

noncomputable def npowSeries (n : ℕ) : LazySeries :=
  npowSeriesFrom n 1 0

theorem npowSeriesFrom_eq_cons {n : ℕ} {acc : ℝ} {k : ℕ} (h : k ≤ n) :
    npowSeriesFrom n acc k = Seq.cons acc (npowSeriesFrom n (acc * (n - k) / (k + 1)) (k + 1)) := by
  unfold npowSeriesFrom
  nth_rw 1 [corec_cons]
  simpa

theorem npowSeriesFrom_eq_nil {n : ℕ} {acc : ℝ} {k : ℕ} (h : n < k) :
    npowSeriesFrom n acc k = .nil := by
  unfold npowSeriesFrom
  nth_rw 1 [corec_nil]
  simpa

theorem powSeries_eq_npowSeries {n : ℕ} : powSeries n = (npowSeries n).append zeros := by
  simp [powSeries, npowSeries]
  sorry
  -- let motive : LazySeries → LazySeries → Prop := fun x y =>
  --   ∃ acc m,
  --   x = powSeriesFrom (↑n) acc m ∧ y = (npowSeriesFrom n acc m).append zeros
  -- apply Eq.coind motive
  -- · simp [motive]
  --   use 1, 0
  -- intro x y ih
  -- left
  -- simp only [motive] at ih ⊢
  -- obtain ⟨acc, m, hx, hy⟩ := ih
  -- subst hx hy
  -- by_cases h_mn : m ≤ n
  -- · use ?_, ?_, ?_
  --   rw [npowSeriesFrom_eq_cons h_mn, powSeriesFrom_eq_cons]
  --   constructor
  --   · exact Eq.refl _
  --   constructor
  --   · simp
  --     exact Eq.refl _
  --   use ?_, ?_
  --   constructor
  --   · exact Eq.refl _
  --   rfl
  -- · use ?_, ?_, ?_
  --   rw [npowSeriesFrom_eq_nil (by linarith), powSeriesFrom_eq_cons, nil_append]
  --   constructor
  --   · exact Eq.refl _
  --   constructor
  --   ·

noncomputable def npow {basis : Basis} (ms : PreMS basis) (n : ℕ) : PreMS basis :=
  match basis with
  | [] => ms^n
  | List.cons _ _ =>
    match destruct ms with
    | none =>
      if n = 0 then
        one _
      else
        .nil
    | some ((exp, coef), tl) => mulMonomial
      ((npowSeries n).apply (mulMonomial tl coef.inv (-exp))) (coef.npow n) (exp * n)

-- copypaste from `pow_WellOrdered`
theorem npow_WellOrdered {basis : Basis} {ms : PreMS basis} {n : ℕ}
    (h_wo : ms.WellOrdered) : (ms.npow n).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    cases' ms with exp coef tl
    · simp [npow]
      split_ifs
      · apply one_WellOrdered
      · apply WellOrdered.nil
    · obtain ⟨h_coef, h_comp, h_tl⟩ := WellOrdered_cons h_wo
      simp [npow]
      apply mulMonomial_WellOrdered
      · apply apply_WellOrdered
        · apply mulMonomial_WellOrdered
          · exact h_tl
          · apply inv_WellOrdered
            exact h_coef
        · simp
          generalize leadingExp tl = w at *
          cases w with
          | bot => simp [Ne.bot_lt']
          | coe => simpa [← WithBot.coe_add] using h_comp
      · apply npow_WellOrdered
        exact h_coef

theorem npow_Approximates {basis : Basis} {F : ℝ → ℝ} {ms : PreMS basis} {n : ℕ}
    (h_basis : WellFormedBasis basis) (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates F) (h_trimmed : ms.Trimmed) :
    (ms.npow n).Approximates (F^n) := by
  cases basis with
  | nil =>
    unfold npow
    simp only [Approximates] at *
    eta_expand
    simp
    apply EventuallyEq.pow_const h_approx
  | cons basis_hd basis_tl =>
    cases' ms with exp coef tl
    · apply Approximates_nil at h_approx
      simp [npow]
      split_ifs with h
      · rw [h]
        simp
        exact one_Approximates h_basis
      apply Approximates.nil
      apply h_approx.mono
      intro t ht
      simp
      exact ⟨ht, h⟩
    · simp [npow]
      sorry
      -- apply trim_zeros_Approximates



end PreMS

end TendstoTactic
