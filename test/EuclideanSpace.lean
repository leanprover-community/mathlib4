import Mathlib.Analysis.InnerProductSpace.PiL2

#guard_expr !ₑ[] = (WithLp.equiv 2 (∀ _ : Fin 0, _)).symm ![]
#guard_expr !ₑ[1, 2, 3] = (WithLp.equiv 2 (∀ _ : Fin 3, ℕ)).symm ![1, 2, 3]
#guard_expr !ₑ[1, 2, (3 : ℝ)] = (WithLp.equiv 2 (∀ _ : Fin 3, ℝ)).symm ![1, 2, 3]

/-- info: !ₑ[1, 2, 3] : WithLp 2 (Fin 3 → ℕ) -/
#guard_msgs in
#check !ₑ[1, 2, 3]

set_option pp.mvars false in
/-- info: !ₑ[] : WithLp 2 (Fin 0 → ?_) -/
#guard_msgs in
#check !ₑ[]
