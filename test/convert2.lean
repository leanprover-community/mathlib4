import Mathlib.Data.List.Defs
import Mathlib.Data.Nat.Basic

-- Prior to #7945 this failed with `(kernel) declaration has metavariables '_example'`.
-- There is in fact an internal error being suppressed here, that is reported only with
-- `set_option trace.congr! true`
example (h : False) (_h₁ : ((List.range 128).map (fun _ => 0)).sum = 0) : 0 ∣ 1 := by
  apply Nat.dvd_of_mul_dvd_mul_left Nat.zero_lt_one
  convert Nat.dvd_mul_left 0 1
  all_goals contradiction
