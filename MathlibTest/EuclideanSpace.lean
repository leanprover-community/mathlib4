import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.commandStart false

#guard_expr !₂[] = WithLp.toLp 2 (V := ∀ _ : Fin 0, _) ![]
#guard_expr !₂[1, 2, 3] = WithLp.toLp 2 (V := ∀ _ : Fin 3, ℕ) ![1, 2, 3]
#guard_expr !₁[1, 2, (3 : ℝ)] = WithLp.toLp 1 (V := ∀ _ : Fin 3, ℝ) ![1, 2, 3]

section delaborator

/-- info: !₂[1, 2, 3] : WithLp 2 (Fin 3 → ℕ) -/
#guard_msgs in
#check !₂[1, 2, 3]

set_option pp.mvars false in
/-- info: !₀[] : WithLp 0 (Fin 0 → ?_) -/
#guard_msgs in
#check !₀[]

section var
variable {p : ENNReal}
/-- info: WithLp.toLp p ![1, 2, 3] : WithLp p (Fin 3 → ℕ) -/
#guard_msgs in#check !ₚ[1, 2, 3]
end var

section tombstoned_var
/- Here the `p` in the subscript is shadowed by a later p; so even if we do
make the delaborator less conservative, it should not fire here since `✝` cannot
be subscripted. -/
variable {p : ENNReal} {x} (hx : x = !ₚ[1, 2, 3]) (p : True)
/-- info: hx : x = WithLp.toLp p✝ ![1, 2, 3] -/
#guard_msgs in #check hx
end tombstoned_var

end delaborator
