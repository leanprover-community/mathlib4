import Mathlib.Tactic.Tendsto.Main

open Filter

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
  let f := fun (y : ℝ) ↦ (42 : ℝ);
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
  let f := fun (x : ℝ) ↦ 1 + x + x*x + x*x*x + x*x*x*x + (-1) * x  + (-1) * x*x  + (-1) * x*x*x  + (-1) * x*x*x*x;
  Tendsto f atTop (nhds 1) := by
  simp only
  compute_asymptotics
