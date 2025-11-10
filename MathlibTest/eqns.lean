import Mathlib.Tactic.Eqns
def transpose {m n} (A : m → n → Nat) : n → m → Nat
  | i, j => A j i

theorem transpose_apply {m n} (A : m → n → Nat) (i j) : transpose A i j = A j i := rfl

attribute [eqns transpose_apply] transpose

theorem transpose_const {m n} (c : Nat) :
    transpose (fun (_i : m) (_j : n) => c) = fun _j _i => c := by
  fail_if_success {rw [transpose]}
  fail_if_success {simp [transpose]}
  funext i j -- the rw below does not work without this line
  rw [transpose]

def t : Nat := 0 + 1

theorem t_def : t = 1 := rfl
-- this rw causes lean to generate equations itself for t before the user can register them
theorem t_def' : t = 1 := by rw [t]

-- We used to test that this generated an error,
-- but with asynchronous elaboration, it now longer does!
-- `eqns` still seems to work (via `irreducible_def`) as expected,
-- so for now we just comment out the test...
-- #guard_msgs(error) in
-- attribute [eqns t_def] t

/--
warning: declaration uses 'sorry'
-/
#guard_msgs in
-- the above should error as the above equation would not have changed the output of the below
example (n : Nat) : t = n := by
  rw [t]
  admit
