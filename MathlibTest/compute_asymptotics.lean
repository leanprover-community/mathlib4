import Mathlib.Tactic.ComputeAsymptotics.Main
import Mathlib.Data.Real.Pi.Bounds

open Filter Topology Asymptotics

example :
  let f := fun (y : ℝ) ↦ y;
  Tendsto f atTop atTop := by
  simp
  compute_asymptotics

example :
  let f := fun (y : ℝ) ↦ -y;
  Tendsto f atTop atBot := by
  simp
  compute_asymptotics

example :
  let f := fun (y : ℝ) ↦ y + y;
  Tendsto f atTop atTop := by
  simp
  compute_asymptotics

example :
  let f := fun (y : ℝ) ↦ (-y) + y;
  Tendsto f atTop (nhds 0) := by
  simp only
  compute_asymptotics

example :
  let f := fun (y : ℝ) ↦ (-y) * y;
  Tendsto f atTop atBot := by
  simp only
  compute_asymptotics

example :
  let f := fun (_ : ℝ) ↦ (42 : ℝ);
  Tendsto f atTop (nhds 42) := by
  simp only
  compute_asymptotics

example :
  let f := fun (y : ℝ) ↦ -2 * y;
  Tendsto f atTop atBot := by
  simp only
  compute_asymptotics

example :
  let f := fun (y : ℝ) ↦ y * 2;
  Tendsto f atTop atTop := by
  simp only
  compute_asymptotics

example :
  let f := fun (y : ℝ) ↦ 0 * y;
  Tendsto f atTop (nhds 0) := by
  simp only
  compute_asymptotics

example :
  let f := fun (y : ℝ) ↦ y * 0;
  Tendsto f atTop (nhds 0) := by
  simp only
  compute_asymptotics

example :
  let f := fun (y : ℝ) ↦ (-y) + y + y + (-y);
  Tendsto f atTop (nhds 0) := by
  simp only
  compute_asymptotics

example :
  let f := fun (y : ℝ) ↦ (-y) + 2 * y + (-y);
  Tendsto f atTop (nhds 0) := by
  simp only
  compute_asymptotics

example :
  let f := fun (y : ℝ) ↦ y - y;
  Tendsto f atTop (nhds 0) := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ 11 * x*x*x  +  12 * x*x  +  x  +  1;
  Tendsto f atTop atTop := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ 1 + x + x*x + x*x*x + x*x*x*x - x - x*x - x*x*x - x*x*x*x;
  Tendsto f atTop (nhds 1) := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ x⁻¹;
  Tendsto f atTop (nhds 0) := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ 1/x;
  Tendsto f atTop (nhds 0) := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ 1/(1 + x);
  Tendsto f atTop (nhds 0) := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ (4 * x)/(3 + 2 * x);
  Tendsto f atTop (nhds 2) := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ x/(1 + x);
  Tendsto f atTop (nhds 1) := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ x*x/(1 + x);
  Tendsto f atTop atTop := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ (( - 6  *  x  *  x  *  x)  +  ((2  *  x  *  x)  +  ((1)  *  ((4  *  x)  -  ( - 2  *  x)))))  *  ((( - 6  *  x)  -  ( - 2))  /  ((8  *  x)  *  ( - 9  *  x  *  x  *  x)));
  Tendsto f atTop (nhds (-1/2)) := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ x^(1/2 : ℝ) / (x^(1/3 : ℝ) + x^(-1/3 : ℝ) + 18);
  Tendsto f atTop atTop := by
  simp only
  compute_asymptotics

section log

example :
    let f := fun (y : ℝ) ↦ Real.log y;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ y + Real.log y;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ -y + Real.log y;
    Tendsto f atTop atBot := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.log y - Real.log y;
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.log (y + y);
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.log (y + y⁻¹);
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.log (2 + y - y);
    Tendsto f atTop (𝓝 (Real.log 2)) := by
  have : 0 < Real.log 2 := Real.log_pos (by simp)
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.log (y⁻¹);
    Tendsto f atTop atBot := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ y + Real.log (y⁻¹);
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.log y - Real.log (Real.log y);
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.log y - Real.log (y^2);
    Tendsto f atTop atBot := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.log (1 + y⁻¹) * y;
    Tendsto f atTop (𝓝 1) := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.log (1 + y) / y;
    Tendsto f (𝓝[>] 0) (𝓝 1) := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ (Real.log (1 + y) - y) / y;
    Tendsto f (𝓝[>] 0) (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ (Real.log (1 + y) - y) / (y^2);
    Tendsto f (𝓝[>] 0) (𝓝 (-1/2)) := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ (y * Real.log y) / y;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ (Real.log y)^(1/2 : ℝ);
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.log y / y^(1/2 : ℝ);
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

end log

section exp

example :
    let f := fun (y : ℝ) ↦ Real.exp (y⁻¹);
    Tendsto f atTop (𝓝 1) := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp y - y;
    Tendsto f (𝓝[≠] 0) (𝓝 1) := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp ((1 + y⁻¹) * y);
    Tendsto f (𝓝[≠] 0) (𝓝 (Real.exp 1)) := by
  have : 0 < Real.exp 1 := Real.exp_pos 1
  compute_asymptotics

-- almost the second remarkable limit
example :
    let f := fun (y : ℝ) ↦ Real.exp (Real.log (1 + y⁻¹) * y);
    Tendsto f atTop (𝓝 (Real.exp 1)) := by
  have : 0 < Real.exp 1 := Real.exp_pos 1
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp y;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp y / Real.exp y;
    Tendsto f atTop (𝓝 1) := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp (y^2) / Real.log y;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp (y^2) - Real.exp y;
    Tendsto f atTop atTop := by
  compute_asymptotics

set_option maxHeartbeats 0 in
example :
    let f := fun (y : ℝ) ↦ Real.exp (y^2) / Real.exp y;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp (Real.exp y) / Real.exp y;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp (2 * y) - Real.exp y;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp (2 * y) - Real.exp y * Real.exp y;
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ (Real.log (Real.exp (2 * y) - Real.exp (y))) * y⁻¹;
    Tendsto f atTop (𝓝 2) := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp (-y);
    Tendsto f atTop (𝓝 0) := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp (-Real.log y) * y;
    Tendsto f atTop (𝓝 1) := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp (Real.exp y - Real.exp (-y)) / Real.exp (Real.exp y)
    Tendsto f atTop (𝓝 1) := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp (Real.log y) - y
    Tendsto f atTop (𝓝 0):= by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp (Real.exp y) / Real.exp (y^2);
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp y - Real.exp (y^3) + Real.exp (y^2)
    Tendsto f atTop atBot:= by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp (1 / (1 + y) - 1 / (1 + y))
    Tendsto f atTop (𝓝 1):= by
  compute_asymptotics

end exp

section pow_fun

-- the second remarkable limit
example :
    let f := fun (y : ℝ) ↦ (1 + y⁻¹) ^ y;
    Tendsto f atTop (𝓝 (Real.exp 1)) := by
  have : 0 < Real.exp 1 := Real.exp_pos 1
  compute_asymptotics

end pow_fun

example :
  let f := fun (x : ℝ) ↦ x^(-Real.pi);
  Tendsto f atTop (nhds 0) := by
  simp only
  have : 0 < Real.pi := Real.pi_pos
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ x^(-1 : ℝ) - 1/x;
  Tendsto f (𝓝[>] 0) (𝓝 0) := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ x^(1 : ℕ) - (1/x)⁻¹;
  Tendsto f (𝓝[>] 0) (𝓝 0) := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ x^(-1 : ℤ) - 1/x;
  Tendsto f (𝓝[<] 0) (𝓝 0) := by
  simp only
  compute_asymptotics

/--
error: The tactic proved that the function fun x => x ^ (-1) - 1 / x tends to 𝓝 0, not atTop.
-/
#guard_msgs in
example :
  let f := fun (x : ℝ) ↦ x^(-1 : ℝ) - 1/x;
  Tendsto f (𝓝[>] 0) atTop := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ (1 + x)^(Real.pi) / (3 + 2*x^(314/100 : ℝ))
  Tendsto f atTop atTop := by
  simp only
  have : 3141592 / 1000000 < Real.pi := by convert Real.pi_gt_d6; norm_num
  compute_asymptotics

section Variables

example (a : ℝ) (h : 0 < a) :
  let f := fun (x : ℝ) ↦ a * x;
  Tendsto f atTop atTop := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ Real.pi * x;
  Tendsto f atTop atTop := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ 1 / (1 + Real.pi * x) - 1 / (1 + 3 * x);
  Tendsto f atTop (nhds 0) := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ x / (1 + Real.pi * x) - x / (1 + 3 * x);
  Tendsto f atTop (nhds (1 / Real.pi - 1/3)) := by
  simp only
  have : 3141592 / 1000000 < Real.pi := by convert Real.pi_gt_d6; norm_num
  have : Real.pi⁻¹ < 1/3 := by
    rw [inv_lt_comm₀] <;> try linarith
    simp; linarith
  compute_asymptotics
  rfl

example (a b : ℝ) (h : a < b) :
  let f := fun (x : ℝ) ↦ (x + 3)^a / x^b;
  Tendsto f atTop (nhds 0) := by
  simp only
  compute_asymptotics

end Variables

section DifferentFilters

example :
  let f := fun (x : ℝ) ↦ x/(1 + x);
  Tendsto f atTop (nhds 1) := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ 1/x;
  Tendsto f (𝓝[>] 0) atTop := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ 1/x;
  Tendsto f (𝓝[<] 0) atBot := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ 1/(x * x);
  Tendsto f (𝓝[≠] 0) atTop := by
  simp only
  compute_asymptotics

example (a : ℝ) :
    let f := fun (y : ℝ) ↦ (1 : ℝ);
    Tendsto f (𝓝[≠] 0) (𝓝 a) := by
  compute_asymptotics
  sorry

end DifferentFilters

section ONotation

example :
  let f := fun (y : ℝ) ↦ y;
  let g := fun (y : ℝ) ↦ y^2;
  f =o[atTop] g := by
  simp
  compute_asymptotics

example :
  let f := fun (y : ℝ) ↦ y;
  let g := fun (y : ℝ) ↦ y^2;
  g =o[𝓝[>] 0] f := by
  simp
  compute_asymptotics

example :
  let f := fun (y : ℝ) ↦ y;
  let g := fun (y : ℝ) ↦ y^2;
  f =O[atTop] g := by
  simp
  compute_asymptotics

example :
  let f := fun (y : ℝ) ↦ y;
  let g := fun (y : ℝ) ↦ y + Real.log y;
  f ~[atTop] g := by
  simp
  compute_asymptotics

end ONotation

-- example from the paper. It's used in the proof of Akkra-Bazzi theorem.
open Real in
example (p b ε : ℝ) (hb1 : 0 < b) (hb2 : b < 1) (hε : 0 < ε) :
  let f := fun (x : ℝ) ↦
    (1 - 1 / (b * (log x)^(1 + ε)))^p *
    (1 + 1 / log (b * x + x / (log x)^(1 + ε))^(ε / 2)) -
    (1 + 1 / (log x)^(ε / 2));
  Tendsto f atTop (𝓝 0) := by
  intro f
  dsimp only [f]
  compute_asymptotics

section Gruntz

open Real

-- 8.1

-- TODO
-- example :
--     let f := fun (x : ℝ) ↦ exp x * (exp (x⁻¹) - exp (x⁻¹ - exp (-x)))
--     Tendsto f atTop (𝓝 1) := by
--   compute_asymptotics

-- 8.5
-- set_option maxHeartbeats 0 in
-- example :
--     let f := fun (x : ℝ) ↦ exp (exp (exp (x + exp (-x)))) / exp (exp (exp x))
--     Tendsto f atTop (𝓝 1) := by
--   compute_asymptotics

-- 8.12
example :
  let f := fun (x : ℝ) ↦ ((3 : ℝ) ^ x + (5 : ℝ) ^ x) ^ (x⁻¹);
    Tendsto f atTop (𝓝 5) := by
  have : 1 < log 5 / log 3 := by
    rw [one_lt_div (by positivity)]
    apply Real.strictMonoOn_log (by simp) (by simp) (by norm_num)
  compute_asymptotics
  field_simp
  rw [Real.exp_log]
  norm_num

end Gruntz

/--
error: Function must me in the form fun x ↦ ...
Calling `eta_expand` before `compute asymptotics might help.
-/
#guard_msgs in
example : Tendsto Real.exp atTop atTop := by
  compute_asymptotics

/--
error: proveTendstoInf proved that the function fun x => x / x ^ 2 tends to finite limit: 𝓝 0 -/
#guard_msgs in
example :
  let f := fun (y : ℝ) ↦ y;
  let g := fun (y : ℝ) ↦ y^2;
  g =o[atTop] f := by
  simp
  compute_asymptotics
