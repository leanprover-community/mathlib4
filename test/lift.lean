import Mathlib.Tactic.Lift
import Mathlib.Tactic.PermuteGoals
import Mathlib.Tactic.Coe
import Mathlib.Init.Set
import Mathlib.Order.Basic

/-! Some tests of the `lift` tactic. -/

example (n : ℤ) (hn : 0 ≤ n) : 0 ≤ n + 1 := by
  lift n to ℕ
  guard_target =ₛ 0 ≤ n
  swap; guard_target =ₛ 0 ≤ (n : Int) + 1; swap
  · exact hn
  · exact Int.le_add_one hn

example (n : ℤ) (hn : 0 ≤ n) : 0 ≤ n + 1 := by
  lift n to ℕ using hn
  guard_target =ₛ 0 ≤ (n : Int) + 1
  exact Int.le_add_one (Int.ofNat_zero_le _)

example (n : ℤ) (hn : 0 ≤ n) : 0 ≤ n + 1 := by
  have hn' := hn
  lift n to ℕ using hn with k hk
  guard_target =ₛ 0 ≤ (k : Int) + 1
  guard_hyp hk : (k : Int) = n
  exact Int.le_add_one hn'

example (n : ℤ) (hn : 0 ≤ n) : 0 ≤ n + 1 := by
  have hn' := hn
  lift n to ℕ using hn with k
  guard_target =ₛ 0 ≤ (k : Int) + 1
  exact Int.le_add_one hn'

example (n : ℤ) (hn : 0 ≤ n) : 0 ≤ n + 1 := by
  lift n to ℕ using hn with k hk hn'
  guard_target =ₛ 0 ≤ (k : Int) + 1
  guard_hyp hk : (k : Int) = n
  guard_hyp hn' : 0 ≤ (k : Int)
  exact Int.le_add_one hn'

example (n : ℤ) (hn : 0 ≤ n) : 0 ≤ n + 1 := by
  lift n to ℕ using hn with k hk hn
  guard_target =ₛ 0 ≤ (k : Int) + 1
  guard_hyp hn : 0 ≤ (k : Int)
  exact Int.le_add_one hn

example (n : ℤ) (hn : 0 ≤ n) : 0 ≤ n + 1 := by
  lift n to ℕ using hn with k rfl hn
  guard_target =ₛ 0 ≤ (k : Int) + 1
  guard_hyp hn : 0 ≤ (k : Int)
  exact Int.le_add_one hn

example (n : ℤ) (hn : 0 ≤ n) : 0 ≤ n + 1 := by
  have hn' := hn
  lift n to ℕ using hn with k rfl
  guard_target =ₛ 0 ≤ (k : Int) + 1
  exact Int.le_add_one hn'

example (n : ℤ) (hn : 0 ≤ n) : 0 ≤ n + 1 := by
  -- Should fail because we didn't provide a variable name when lifting an expression
  fail_if_success lift n + 1 to ℕ using (Int.le_add_one hn)
  -- Now it should succeed
  lift n + 1 to ℕ using (Int.le_add_one hn) with k hk
  exact of_decide_eq_true rfl

-- test lift of functions
example (α : Type _) (f : α → ℤ) (hf : ∀ a, 0 ≤ f a) (hf' : ∀ a, f a < 1) (a : α) :
    0 ≤ 2 * f a := by
  lift f to α → ℕ using hf
  guard_target =ₛ (0 : ℤ) ≤ 2 * (fun i : α ↦ (f i : ℤ)) a
  guard_hyp hf' : ∀ a, ((fun i : α ↦ (f i : ℤ)) a) < 1
  constructor

example (α : Type _) (f : α → ℤ) (hf : ∀ a, 0 ≤ f a) (hf' : ∀ a, f a < 1) (a : α) :
    0 ≤ 2 * f a := by
  lift f to α → ℕ using hf with g hg
  guard_target =ₛ 0 ≤ 2 * (g a : Int)
  guard_hyp hg : (fun i => (g i : Int)) = f
  constructor

example (n m k x : ℤ) (hn : 0 < n) (hk : 0 ≤ k + n) (h : k + n = 2 + x)
    (hans : k + n = m + x) (hans2 : 0 ≤ m) : k + n = m + x := by
  lift n to ℕ using le_of_lt hn
  guard_target =ₛ k + ↑n = m + x; guard_hyp hn : (0 : ℤ) < ↑n
  lift m to ℕ
  guard_target =ₛ 0 ≤ m; swap; guard_target =ₛ k + ↑n = ↑m + x
  --tactic.num_goals >>= λ n, guard (n = 2),
  lift (k + n) to ℕ using hk with l hl
  exact hans
  exact hans2

-- fail gracefully when the lifted variable is a local definition
example (h : False) : let n : ℤ := 3; n = 3 := by
  intro n
  fail_if_success lift n to ℕ
  exfalso; exact h

instance canLift_unit : CanLift Unit Unit id (fun _ ↦ true) := ⟨fun x _ ↦ ⟨x, rfl⟩⟩

example (n : ℤ) (hn : 0 < n) : True := by
  fail_if_success lift n to ℕ using hn
  fail_if_success lift (n : Option ℤ) to ℕ
  trivial

 example (n : ℤ) : ℕ := by
  fail_if_success lift n to ℕ
  exact 0

instance canLift_subtype (R : Type _) (s : Set R) : CanLift R {x // x ∈ s} ((↑) : {x // x ∈ s} → R) (fun x => x ∈ s) :=
{ prf := fun x hx => ⟨⟨x, hx⟩, rfl⟩ }

example {R : Type _} {P : R → Prop} (x : R) (hx : P x) : P x := by
  lift x to {x // P x} using hx with y hy hx
  guard_target =ₛ P y
  guard_hyp hy : y = x
  exact hx

 example (n : ℤ) (h_ans : n = 5) (hn : 0 ≤ 1 * n) : n = 5 := by
  lift n to ℕ using by { simpa [Int.one_mul] using hn } with k hk
  guard_target =ₛ (k : Int) = 5
  guard_hyp hk : k = n
  guard_hyp hn : 0 ≤ 1 * (k : Int)
  guard_hyp h_ans : (k : Int) = 5
  exact h_ans

 example (n : ℤ) (h_ans : n = 5) (hn : 0 ≤ 1 * n) : n = 5 := by
  lift n to ℕ using by { simpa [Int.one_mul] using hn } with k hk h_orig
  guard_target =ₛ (k : Int) = 5
  guard_hyp hk : k = n
  guard_hyp hn : 0 ≤ 1 * (k : Int)
  guard_hyp h_ans : (k : Int) = 5
  exact h_ans
