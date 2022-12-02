import Mathlib.Tactic.Lift
import Mathlib.Tactic.PermuteGoals

/-! Some tests of the `lift` tactic. -/
example (n m k x z u : ℤ) (hn : 0 < n) (hk : 0 ≤ k + n) (hu : 0 ≤ u)
  (h : k + n = 2 + x) (f : False) :
  k + n = m + x := by
· lift n to ℕ using le_of_lt hn
  guard_target =ₛ k + ↑n = m + x; guard_hyp hn : (0 : ℤ) < ↑n
  lift m to ℕ
  sorry
  -- guard_target =ₛ 0 ≤ m; swap; guard_target =ₛ k + ↑n = ↑m + x
  -- --   tactic.num_goals >>= λ n, guard (n = 2),
  -- lift (k + n) to ℕ using hk with l hl
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
-- example : let n : ℤ := 3; n = n := by
-- · intro n
--   success_if_fail_with_msg { lift n to ℕ }
--     ("Cannot substitute variable n, it is a local definition. " ++
--     "If you really want to do this, use `clear_value` first."),
--   refl

instance can_lift_unit : CanLift Unit Unit id (fun _ ↦ true) := ⟨fun x _ ↦ ⟨x, rfl⟩⟩

/- test error messages -/
-- example (n : ℤ) (hn : 0 < n) : true :=
-- begin
--   success_if_fail_with_msg {lift n to ℕ using hn} ("lift tactic failed.\n" ++
--     "invalid type ascription, term has type\n  0 < n\nbut is expected to have type\n  0 ≤ n"),
--   success_if_fail_with_msg {lift (n : option ℤ) to ℕ}
--     ("Failed to find a lift from option ℤ to ℕ. " ++
--     "Provide an instance of\n  can_lift (option ℤ) ℕ ?m_1 ?m_2"),
--   trivial
-- end

-- example (n : ℤ) : ℕ :=
-- begin
--   success_if_fail_with_msg {lift n to ℕ}
--     "lift tactic failed. Tactic is only applicable when the target is a proposition.",
--   exact 0
-- end

-- instance can_lift_set (R : Type*) (s : set R) : can_lift R s coe (λ x, x ∈ s) :=
-- { prf := λ x hx, ⟨⟨x, hx⟩, rfl⟩ }

-- example {R : Type*} {P : R → Prop} (x : R) (hx : P x) : true :=
-- by { lift x to {x // P x} using hx with y, trivial }

-- /-! Test that `lift` elaborates `s` as a type, not as a set. -/
-- example {R : Type*} {s : set R} (x : R) (hx : x ∈ s) : true :=
-- by { lift x to s using hx with y, trivial }

-- example (n : ℤ) (hn : 0 ≤ n) : True :=
-- by { lift n to ℕ; exact hn; trivial }

-- example (n : ℤ) (hn : 0 ≤ n) : true :=
-- by { lift n to ℕ using hn, trivial }

-- example (n : ℤ) (hn : n ≥ 0) : true :=
-- by { lift n to ℕ using ge.le _, trivial, guard_target (n ≥ 0), exact hn }

-- example (n : ℤ) (hn : 0 ≤ 1 * n) : true :=
-- begin
--   lift n to ℕ using by { simpa [int.one_mul] using hn } with k,
--   -- the above braces are optional, but it would be bad style to remove them (see next example)
--   guard_hyp hn : 0 ≤ 1 * ((k : ℕ) : ℤ),
--   trivial
-- end

-- example (n : ℤ) (hn : 0 ≤ n ↔ true) : true :=
-- begin
--   lift n to ℕ using by { simp [hn] } with k, -- the braces are not optional here
--   trivial
-- end
