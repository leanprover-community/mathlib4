module

public import Mathlib.Algebra.Ring.SumsOfSquares

example {G : Type*} [CommGroup G] {a b c d e : G} (ha : IsSquare a) {n : ℕ} {k : ℤ} (hk : Even k) :
    IsSquare <| a * (b * b) / (c ^ 2) * (d ^ k) * (e ^ (2 * n)) := by grind

example {G : Type*} [AddCommGroup G] {a b c d e : G} (ha : Even a) {n : ℕ} {k : ℤ} (hk : Even k) :
    Even <| a + (b + b) - 2 • c + k • d + (n + n) • e := by grind

example {R : Type*} [Ring R] {a b c : R} {f : Fin 5 → R} (ha : IsSquare a) {n : ℕ} (hk : Even n) :
    IsSumSq <| a + b * b + c ^ n + ∑ i : Fin 5, f i ^ 2 := by grind (ematch := 7)
