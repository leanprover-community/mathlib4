
namespace Nat

protected theorem sub_sub : ∀ (n m k : Nat), n - m - k = n - (m + k)
| n, m, 0        => by rw [Nat.add_zero, Nat.sub_zero]
| n, m, (succ k) => by rw [add_succ, sub_succ, sub_succ, Nat.sub_sub n m k]

protected theorem add_sub_add_right : ∀ (n k m : Nat), (n + k) - (m + k) = n - m
| n, 0,      m => by rw [Nat.add_zero, Nat.add_zero]
| n, succ k, m => by rw [add_succ, add_succ, succ_sub_succ, Nat.add_sub_add_right n k m]

protected theorem sub_add_cancel : {a b : Nat} → a ≤ b → b - a + a = b
| 0, b, _ => rfl
| a+1, b+1, h => congrArg Nat.succ $ show (b + 1) - (a + 1) + a = b by
  rw [Nat.add_comm  a, ← Nat.sub_sub]
  exact Nat.sub_add_cancel h

protected theorem lt_of_not_le {a b : Nat} (h : ¬ a ≤ b) : b < a :=
  match Nat.ltOrGe b a with | Or.inl h' => h' | Or.inr h' => nomatch h h'

protected theorem lt_add_of_pos_right {n k : Nat} (h : 0 < k) : n < n + k :=
Nat.addLtAddLeft h n

protected theorem lt_of_add_lt_add_right {a b c : Nat} (h : a + b < c + b) : a < c :=
  Nat.lt_of_not_le fun h' => Nat.notLeOfGt h (Nat.addLeAddRight h' _)

protected theorem sub_pos_of_lt {m n : Nat} (h : m < n) : 0 < n - m := by
  apply Nat.lt_of_add_lt_add_right (b := m)
  rw [Nat.zero_add, Nat.sub_add_cancel (Nat.leOfLt h)]; exact h

protected theorem sub_lt_sub_left : ∀ {k m n : Nat} (H : k < m) (h : k < n), m - n < m - k
| 0, m+1, n+1, _, _ => by rw [Nat.add_sub_add_right]; exact lt_succ_of_le (Nat.subLe _ _)
| k+1, m+1, n+1, h1, h2 => by
  rw [Nat.add_sub_add_right, Nat.add_sub_add_right]
  exact Nat.sub_lt_sub_left h1 h2

/-- A well-ordered relation for "upwards" induction on the natural numbers up to some bound `ub`. -/
def Up (ub a i : Nat) := i < a ∧ i < ub

theorem Up.next {ub i} (h : i < ub) : Up ub (i+1) i := ⟨Nat.ltSuccSelf _, h⟩

theorem Up.WF (ub) : WellFounded (Up ub) :=
  Subrelation.wf (h₂ := measureWf (ub - .)) @fun a i ⟨ia, iu⟩ => Nat.sub_lt_sub_left iu ia

end Nat
