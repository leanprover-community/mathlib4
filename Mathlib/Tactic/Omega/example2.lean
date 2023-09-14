import Std.Data.Range.Lemmas
import Std.Data.List.Lemmas

def sum (n : Nat) := Id.run do
  let mut r := 0
  for i in [0:n] do
    r := r + i
  return r

theorem sum_eq (n : Nat) : sum (n + 1) = n*(n+1)/2 := by
  suffices ∀ l i acc r, l + i = n → i * (i + 1) = 2 * acc →
      Id.run (forIn (List.range' (i+1) l) acc fun i r => .yield (r + i)) = r →
      n * (n + 1) = 2 * r by
    rw [sum]
    simp [Std.Range.forIn_eq_forIn_range', Std.Range.numElems_step_1]
    refine (Nat.div_eq_of_eq_mul_right (by decide) ?_).symm
    exact this _ _ _ _ (by rfl) (by rfl) rfl
  intro l i acc r e ih hr
  induction l generalizing i acc
  · simp [← e, ih, ← hr, forIn, Id.run]; simp [List.range']
  · next l IH =>
    rw [Nat.succ_add] at e
    refine IH i.succ _ e ?_ hr
    rw [Nat.mul_add 2, ← ih, ← Nat.add_mul, Nat.mul_comm]
