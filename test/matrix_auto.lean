import Mathlib.Data.Matrix.Auto

open Matrix


variable (α : Type u) (A : Matrix (Fin _) (Fin _) α) in
#check (fin_eta% 2 3 A : A = of ![![A 0 0, A 0 1, A 0 2], ![A 1 0, A 1 1, A 1 2]])

variable (α : Type u) (A : Matrix (Fin _) (Fin _) α) in
#check (fin_eta% _ _ A : A = of ![![A 0 0, A 0 1, A 0 2], ![A 1 0, A 1 1, A 1 2]])

example (A : Matrix (Fin 2) (Fin 3) ℕ) : A = 0 := by
  rw [fin_eta% _ _ A]
  dsimp
  sorry

example : true := by
  let B : Matrix (Fin 20) (Fin 20) ℕ := 0
  have := fin_eta% _ _ B
  have : B = B := by rw [this]
  trivial

example {α} [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
    !![a₁₁, a₁₂;
      a₂₁, a₂₂] ⬝ !![b₁₁, b₁₂;
                      b₂₁, b₂₂] = !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
                                    a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] :=
  by rw [of_mul_of_fin% 2 2 2]
