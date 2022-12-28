import Mathlib.Tactic.Lift
import Mathlib.Tactic.PermuteGoals
import Mathlib.Tactic.Coe
import Mathlib.Init.Set
import Mathlib.Order.Basic

/-! Some tests of the `lift` tactic. -/
example (n m k x z u : ℤ) (hn : 0 < n) (hk : 0 ≤ k + n) (hu : 0 ≤ u)
    (h : k + n = 2 + x) : k + n = m + x := by
  lift n to ℕ using le_of_lt hn
  guard_target =ₛ k + ↑n = m + x; guard_hyp hn : (0 : ℤ) < ↑n
  lift m to ℕ
  guard_target =ₛ 0 ≤ m; swap; guard_target =ₛ k + ↑n = ↑m + x
  --tactic.num_goals >>= λ n, guard (n = 2),
  lift (k + n) to ℕ using hk with l hl
  sorry
  sorry

  -- guard_hyp l : ℕ; guard_hyp hl : ↑l = k + ↑n; guard_target =ₛ ↑l = ↑m + x
    -- --   tactic.success_if_fail (tactic.get_local `hk),
    -- lift x to ℕ with y hy
    -- swap; guard_hyp y : ℕ; guard_hyp hy : ↑y = x; guard_target =ₛ ↑l = ↑m + x; swap
    -- lift z to ℕ with w
    -- swap; guard_hyp w : ℕ; swap -- tactic.success_if_fail (tactic.get_local `z), tactic.swap,
    -- lift u to ℕ using hu with u rfl hu
    -- guard_hyp hu : (0 : ℤ) ≤ ↑u
    -- all_goals { exfalso; assumption }

-- test lift of functions
example (α : Type _) (f : α → ℤ) (hf : ∀ a, 0 ≤ f a) (hf' : ∀ a, f a < 1) (a : α) :
    0 ≤ 2 * f a := by
· lift f to α → ℕ using hf
  guard_target =ₛ (0 : ℤ) ≤ 2 * (fun i : α ↦ (f i : ℤ)) a
  guard_hyp hf' : ∀ a, ((fun i : α ↦ (f i : ℤ)) a) < 1
  constructor

-- fail gracefully when the lifted variable is a local definition
example (h : False) : let n : ℤ := 3; n = 3 := by
  intro n
  fail_if_success lift n to ℕ
  exfalso; exact h

instance can_lift_unit : CanLift Unit Unit id (fun _ ↦ true) := ⟨fun x _ ↦ ⟨x, rfl⟩⟩

example (n : ℤ) (hn : 0 < n) : True := by
  fail_if_success lift n to ℕ using hn
  fail_if_success lift (n : Option ℤ) to ℕ
  trivial

 example (n : ℤ) : ℕ := by
  fail_if_success lift n to ℕ
  exact 0

instance can_lift_subtype (R : Type _) (s : Set R) : CanLift R {x // x ∈ s} ((↑) : {x // x ∈ s} → R) (fun x => x ∈ s) :=
{ prf := fun x hx => ⟨⟨x, hx⟩, rfl⟩ }

example {R : Type _} {P : R → Prop} (x : R) (hx : P x) : P x := by
  lift x to {x // P x} using hx with y hy
  exact hx

example (n : ℤ) (hn : 0 ≤ n) : 0 ≤ n := by
  lift n to ℕ; exact hn
  exact hn

example (n : ℤ) (hn : 0 ≤ n) : True := by
  lift n to ℕ using hn
  trivial

--example (n : ℤ) (hn : n ≥ 0) : True := by
--  --lift n to ℕ using GE.ge.le _
--  lift n to ℕ using GE.ge.le _
--  trivial

 example (n : ℤ) (h_ans : n = 5) (hn : 0 ≤ 1 * n) : n = 5 := by
  lift n to ℕ using by { simpa [Int.one_mul] using hn } with k hk
  exact h_ans

-- example (n : ℤ) (hn : 0 ≤ n ↔ true) : true :=
-- begin
--   lift n to ℕ using by { simp [hn] } with k, -- the braces are not optional here
--   trivial
-- end
