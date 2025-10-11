import Mathlib.Data.Matrix.Auto

open Matrix


variable (α : Type u) (A : Matrix (Fin _) (Fin _) α) in
/-- info: A = !![A 0 0, A 0 1, A 0 2; A 1 0, A 1 1, A 1 2] : Prop -/
#guard_msgs in
#check type_of% (fin_eta% 2 3 A : A = of ![![A 0 0, A 0 1, A 0 2], ![A 1 0, A 1 1, A 1 2]])

variable (α : Type u) (A : Matrix (Fin _) (Fin _) α) in
/-- info: A = !![A 0 0, A 0 1, A 0 2; A 1 0, A 1 1, A 1 2] : Prop -/
#guard_msgs in
#check type_of% (fin_eta% _ _ A : A = of ![![A 0 0, A 0 1, A 0 2], ![A 1 0, A 1 1, A 1 2]])

example (A : Matrix (Fin 2) (Fin 3) ℕ) :
    A = !![A 0 0, A 0 1, A 0 2; A 1 0, A 1 1, A 1 2] := by
  conv_lhs => rw [fin_eta% _ _ A]

example : true := by
  let B : Matrix (Fin 20) (Fin 20) ℕ := 0
  have := fin_eta% _ _ B
  have : B = B := by rw [this]
  trivial

/--
info: ∀ {α : Type u_1} [inst_1 : Mul α] [inst_2 : AddCommMonoid α] (a₀₀ a₀₁ a₁₀ a₁₁ b₀₀ b₀₁ b₁₀ b₁₁ : α),
  !![a₀₀, a₀₁; a₁₀, a₁₁] * !![b₀₀, b₀₁; b₁₀, b₁₁] =
    !![a₀₀ * b₀₀ + a₀₁ * b₁₀, a₀₀ * b₀₁ + a₀₁ * b₁₁; a₁₀ * b₀₀ + a₁₁ * b₁₀, a₁₀ * b₀₁ + a₁₁ * b₁₁] : Prop
-/
#guard_msgs in
#check type_of% (of_mul_of_fin% 2 2 2)

example {α} [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
    !![a₁₁, a₁₂;
      a₂₁, a₂₂] * !![b₁₁, b₁₂;
                      b₂₁, b₂₂] = !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
                                    a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] :=
  by rw [of_mul_of_fin% 2 2 2]
