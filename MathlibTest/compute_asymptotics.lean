import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.ComputeAsymptotics

private axiom test_sorry : ∀ {α}, α

open Real Filter Topology Asymptotics

example :
    let f := fun (x : ℝ) ↦ x;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ -x;
    Tendsto f atTop atBot := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x + x;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ (-x) + x;
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ (-x) * x;
    Tendsto f atTop atBot := by
  compute_asymptotics

example :
    let f := fun (_ : ℝ) ↦ (42 : ℝ);
    Tendsto f atTop (𝓝 42) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ -2 * x;
    Tendsto f atTop atBot := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x * 2;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ 0 * x;
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x * 0;
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ (-x) + x + x + (-x);
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ (-x) + 2 * x + (-x);
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x - x;
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ 11 * x*x*x  +  12 * x*x  +  x  +  1;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ 1 + x + x*x + x*x*x + x*x*x*x - x - x*x - x*x*x - x*x*x*x;
    Tendsto f atTop (𝓝 1) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x⁻¹;
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ 1/x;
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ 1/(1 + x);
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ (4 * x)/(3 + 2 * x);
    Tendsto f atTop (𝓝 2) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x/(1 + x);
    Tendsto f atTop (𝓝 1) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x*x/(1 + x);
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ (( - 6  *  x  *  x  *  x)  +  ((2  *  x  *  x)  +  ((1)  *  ((4  *  x)  -  ( - 2  *  x)))))  *  ((( - 6  *  x)  -  ( - 2))  /  ((8  *  x)  *  ( - 9  *  x  *  x  *  x)));
    Tendsto f atTop (𝓝 (-1/2)) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x ^ (1 / 2 : ℝ) / (x ^ (1 / 3 : ℝ) + x ^ (-1 / 3 : ℝ) + 18);
    Tendsto f atTop atTop := by
  compute_asymptotics

section log

example :
    let f := fun (x : ℝ) ↦ log x;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x + log x;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ -x + log x;
    Tendsto f atTop atBot := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ log x - log x;
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ log (x + x);
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ log (x + x⁻¹);
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ log (2 + x - x);
    Tendsto f atTop (𝓝 (log 2)) := by
  have : 0 < log 2 := log_pos (by simp)
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ log (x⁻¹);
    Tendsto f atTop atBot := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x + log (x⁻¹);
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ log x - log (log x);
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ log x - log (x ^ 2);
    Tendsto f atTop atBot := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ log (1 + x⁻¹) * x;
    Tendsto f atTop (𝓝 1) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ log (1 + x) / x;
    Tendsto f (𝓝[>] 0) (𝓝 1) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ (log (1 + x) - x) / x;
    Tendsto f (𝓝[>] 0) (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ (log (1 + x) - x) / (x ^ 2);
    Tendsto f (𝓝[>] 0) (𝓝 (-1/2)) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ (x * log x) / x;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ (log x) ^ (1/2 : ℝ);
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ log x / x ^ (1/2 : ℝ);
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

end log

section exp

example :
    let f := fun (x : ℝ) ↦ exp (x⁻¹);
    Tendsto f atTop (𝓝 1) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ exp x - x;
    Tendsto f (𝓝[≠] 0) (𝓝 1) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ exp ((1 + x⁻¹) * x);
    Tendsto f (𝓝[≠] 0) (𝓝 (exp 1)) := by
  have : 0 < exp 1 := exp_pos 1
  compute_asymptotics

-- almost the second remarkable limit
example :
    let f := fun (x : ℝ) ↦ exp (log (1 + x⁻¹) * x);
    Tendsto f atTop (𝓝 (exp 1)) := by
  have : 0 < exp 1 := exp_pos 1
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ exp x;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ exp x / exp x;
    Tendsto f atTop (𝓝 1) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ exp (x ^ 2) / log x;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ exp (x ^ 2) - exp x;
    Tendsto f atTop atTop := by
  compute_asymptotics

set_option maxHeartbeats 0 in
example :
    let f := fun (x : ℝ) ↦ exp (x ^ 2) / exp x;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ exp (exp x) / exp x;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ exp (2 * x) - exp x;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ exp (2 * x) - exp x * exp x;
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ (log (exp (2 * x) - exp (x))) * x⁻¹;
    Tendsto f atTop (𝓝 2) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ exp (-x);
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ exp (-log x) * x;
    Tendsto f atTop (𝓝 1) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ exp (exp x - exp (-x)) / exp (exp x)
    Tendsto f atTop (𝓝 1) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ exp (log x) - x
    Tendsto f atTop (𝓝 0):= by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ exp (exp x) / exp (x ^ 2);
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ exp x - exp (x ^ 3) + exp (x ^ 2)
    Tendsto f atTop atBot:= by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ exp (1 / (1 + x) - 1 / (1 + x))
    Tendsto f atTop (𝓝 1):= by
  compute_asymptotics

end exp

section pow_fun

-- the second remarkable limit
example :
    let f := fun (x : ℝ) ↦ (1 + x⁻¹) ^ x;
    Tendsto f atTop (𝓝 (exp 1)) := by
  compute_asymptotics

end pow_fun

example :
    let f := fun (x : ℝ) ↦ x ^ (-Real.pi);
    Tendsto f atTop (𝓝 0) := by
  have : 0 < Real.pi := Real.pi_pos
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x ^ (-1 : ℝ) - 1/x;
    Tendsto f (𝓝[>] 0) (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x ^ (1 : ℕ) - (1/x)⁻¹;
    Tendsto f (𝓝[>] 0) (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x ^ (-1 : ℤ) - 1/x;
    Tendsto f (𝓝[<] 0) (𝓝 0) := by
  compute_asymptotics

/--
error: The tactic proved that the function fun x => x ^ (-1) - 1 / x tends to 𝓝 0, not atTop.
-/
#guard_msgs in
example :
    let f := fun (x : ℝ) ↦ x ^ (-1 : ℝ) - 1/x;
    Tendsto f (𝓝[>] 0) atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ (1 + x) ^ (Real.pi) / (3 + 2 * x ^ (314/100 : ℝ))
    Tendsto f atTop atTop := by
  have : 3141592 / 1000000 < Real.pi := by convert Real.pi_gt_d6; norm_num
  compute_asymptotics

section Variables

example (a : ℝ) (h : 0 < a) :
    let f := fun (x : ℝ) ↦ a * x;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ Real.pi * x;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ 1 / (1 + Real.pi * x) - 1 / (1 + 3 * x);
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x / (1 + Real.pi * x) - x / (1 + 3 * x);
    Tendsto f atTop (𝓝 (1 / Real.pi - 1/3)) := by
  have : 3141592 / 1000000 < Real.pi := by convert Real.pi_gt_d6; norm_num
  have : Real.pi⁻¹ < 1/3 := by
    rw [inv_lt_comm₀] <;> linarith
  compute_asymptotics
  rfl

example (a b : ℝ) (h : a < b) :
    let f := fun (x : ℝ) ↦ (x + 3) ^ a / x ^ b;
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

end Variables

section DifferentFilters

example :
    let f := fun (x : ℝ) ↦ x/(1 + x);
    Tendsto f atTop (𝓝 1) := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ 1/x;
    Tendsto f (𝓝[>] 0) atTop := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ 1/x;
    Tendsto f (𝓝[<] 0) atBot := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ 1/(x * x);
    Tendsto f (𝓝[≠] 0) atTop := by
  compute_asymptotics

example (a : ℝ) :
    let f := fun (_ : ℝ) ↦ (1 : ℝ);
    Tendsto f (𝓝[≠] 0) (𝓝 a) := by
  compute_asymptotics
  -- there must be exactly one goal
  guard_target = 1 = a
  exact test_sorry

end DifferentFilters

section LandauNotation

example :
    let f := fun (x : ℝ) ↦ exp x;
    let g := fun (x : ℝ) ↦ x ^ x;
    f =o[atTop] g := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x;
    let g := fun (x : ℝ) ↦ x ^ x;
    f =o[𝓝[>] 0] g := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ (1 + x⁻¹) ^ x;
    let g := fun (x : ℝ) ↦ x / (x + 1);
    f =O[atTop] g := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x;
    let g := fun (x : ℝ) ↦ log (exp x + x ^ 420);
    f ~[atTop] g := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ √x;
    let g := fun (x : ℝ) ↦ x;
    f =o[atTop] g := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ √(x ^ 2 + 1);
    let g := fun (x : ℝ) ↦ Real.log (Real.exp (2 * x));
    f =Θ[atTop] g := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x * (-3 * x - 5);
    let g := fun (x : ℝ) ↦ (x ^ 2 + √x);
    IsBigOWith 4 atTop f g := by
  compute_asymptotics

end LandauNotation

section DifferentDomainsCodomains

example :
    Tendsto (fun (x : ℕ) ↦ ((x + 2) / (x + 3) : ℝ)) atTop (𝓝 1) := by
  compute_asymptotics

example :
    Tendsto (fun (x : ℤ) ↦ ((x + 2) / (x + 3) : ℝ)) atTop (𝓝 1) := by
  compute_asymptotics

example :
    Tendsto (fun (x : ℚ) ↦ ((x + 2) / (x + 3) : ℝ)) atTop (𝓝 1) := by
  compute_asymptotics

example :
    Tendsto (fun (x : ℕ) ↦ x ^ 2) atTop atTop := by
  compute_asymptotics

example :
    Tendsto (fun (x : ℤ) ↦ -x ^ 2) atTop atBot := by
  compute_asymptotics

example :
    Tendsto (fun (x : ℚ) ↦ (x + 2) / (x + 3)) atTop (𝓝 1) := by
  compute_asymptotics

example :
    (fun (n : ℕ) ↦ (n : ℚ)) =o[atTop] (fun (n : ℕ) ↦ (n ^ 2 - n : ℤ)) := by
  compute_asymptotics

example :
    (fun (n : ℕ) ↦ (n : ℚ)) =O[atTop] (fun (n : ℕ) ↦ (- n : ℤ)) := by
  compute_asymptotics

example :
    (fun (n : ℕ) ↦ (n ^ 3 : ℚ) / (n + 1 : ℚ)) ~[atTop] (fun (n : ℕ) ↦ (n ^ 2 - n : ℤ)) := by
  compute_asymptotics

end DifferentDomainsCodomains

-- example from the paper. It's used in the proof of Akkra-Bazzi theorem.
example (p b ε : ℝ) (hb1 : 0 < b) (hb2 : b < 1) (hε : 0 < ε) :
  let f := fun (x : ℝ) ↦
    (1 - 1 / (b * (log x) ^ (1 + ε))) ^ p *
    (1 + 1 / log (b * x + x / (log x) ^ (1 + ε)) ^ (ε / 2)) -
    (1 + 1 / (log x) ^ (ε / 2));
  Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun x ↦ x * ((log x + 1)⁻¹ - (log x + 1)⁻¹);
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

section Gruntz

-- 8.1
set_option maxHeartbeats 0 in
example :
    let f := fun (x : ℝ) ↦ exp x * (exp (x⁻¹) - exp (x⁻¹ - exp (-x)))
    Tendsto f atTop (𝓝 1) := by
  compute_asymptotics

-- 8.2
set_option maxHeartbeats 0 in
example :
    let f := fun (x : ℝ) ↦
      exp x * (exp (x⁻¹ + exp (-x) + exp (-x^2)) - exp (x⁻¹ - exp (- exp x)))
    Tendsto f atTop (𝓝 1) := by
  compute_asymptotics

-- 8.3
set_option maxHeartbeats 0 in
example :
    let f := fun (x : ℝ) ↦
      exp (exp (x - exp (-x)) / (1 - x⁻¹)) - exp (exp x)
    Tendsto f atTop atTop := by
  compute_asymptotics

-- -- 8.4: todo statement
-- set_option maxHeartbeats 0 in
-- example :
--     let f := fun (x : ℝ) ↦
--       exp (exp x / (1 - x⁻¹))
--         - exp (exp x / (1 - x⁻¹ - log x - log x))
--     Tendsto f atTop atBot := by
--   compute_asymptotics

-- 8.5
set_option maxHeartbeats 0 in
example :
    let f := fun (x : ℝ) ↦
      exp (exp (exp (x + exp (-x)))) / exp (exp (exp x))
    Tendsto f atTop atTop := by
  compute_asymptotics

-- 8.6
set_option maxHeartbeats 0 in
example :
    let f := fun (x : ℝ) ↦
      exp (exp (exp x)) / exp (exp (exp (x - exp (- exp x))))
    Tendsto f atTop atTop := by
  compute_asymptotics

-- 8.7
set_option maxHeartbeats 0 in
example :
    let f := fun (x : ℝ) ↦
      exp (exp (exp x)) / exp (exp (exp (x - exp (- exp (exp x)))))
    Tendsto f atTop (𝓝 1) := by
  compute_asymptotics

-- 8.8
set_option maxHeartbeats 0 in
example :
    let f := fun (x : ℝ) ↦
      exp (exp x) / exp (exp (x - exp (- exp (exp x))))
    Tendsto f atTop (𝓝 1) := by
  compute_asymptotics

-- 8.10
set_option maxHeartbeats 0 in
example :
    let f := fun (x : ℝ) ↦
      x * log x * (log (x * exp x - x^2)) ^ 2
        / log (log (x^2 + 2 * exp (exp (3 * x ^ 3 * log x))))
    Tendsto f atTop (𝓝 (1 / 3 : ℝ)) := by
  compute_asymptotics

-- 8.11
set_option maxHeartbeats 0 in
example :
    let f := fun (x : ℝ) ↦
      (exp (x * exp (-x)
        / (exp (-x) + exp (- 2 * x ^ 2 / (x + 1))))
        - exp x) / x
    Tendsto f atTop (𝓝 (-exp 2)) := by
  compute_asymptotics

-- 8.12
example :
  let f := fun (x : ℝ) ↦ ((3 : ℝ) ^ x + (5 : ℝ) ^ x) ^ (x⁻¹);
    Tendsto f atTop (𝓝 5) := by
  have : 1 < log 5 / log 3 := by
    rw [one_lt_div (by positivity)]
    apply Real.strictMonoOn_log (by simp) (by simp) (by norm_num)
  compute_asymptotics
  rw [exp_log]
  norm_num

-- 8.20
set_option maxHeartbeats 0 in
example :
    let f := fun (x : ℝ) ↦
      exp
        (log (log (x + exp (log x * log (log x))))
          / log (log (log (exp x + x + log x))))
    Tendsto f atTop (𝓝 (exp 1)) := by
  compute_asymptotics

end Gruntz

-- TODO: don't ask for unused argument
set_option linter.unusedVariables false in
example (x₀ : ℝ) (h : 0 < x₀) :
    Tendsto (fun (x : ℝ) ↦ (exp (x₀ + x) - exp x₀) / x) (𝓝[≠] 0) (𝓝 (exp x₀)) := by
  compute_asymptotics

/--
error: Function must me in the form fun x ↦ ...
Calling `eta_expand` before `compute asymptotics might help.
-/
#guard_msgs in
example : Tendsto exp atTop atTop := by
  compute_asymptotics

/--
error: proveTendstoInf proved that the function fun x => id x / id (x ^ 2) tends to finite limit: 𝓝 0
-/
#guard_msgs in
example :
    let f := fun (x : ℝ) ↦ x;
    let g := fun (x : ℝ) ↦ x ^ 2;
    g =o[atTop] f := by
  compute_asymptotics

example :
    let f := fun (x : ℝ) ↦ x;
    Tendsto f atTop atTop := by
  compute_limit (fun x ↦ x) at atTop with h
  exact h
