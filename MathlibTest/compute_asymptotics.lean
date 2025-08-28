import Mathlib.Tactic.Tendsto.Main

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Pi.Bounds

section ElimDestruct

open Stream'.Seq TendstoTactic ElimDestruct

def basis : List (ℝ → ℝ) := [fun (x : ℝ) ↦ x]
theorem basis_wo : WellFormedBasis basis := by
  simp [WellFormedBasis, basis]
  exact fun ⦃U⦄ a => a

theorem zero_aux : 0 < basis.length := by simp [basis]

def ms_const : PreMS [id] := PreMS.const [id] 42

def ms_monom : PreMS [id] := PreMS.monomial [id] 0

def ms_nil : PreMS [id] := PreMS.nil

def ms_cons : PreMS [id] := PreMS.cons (1, 1) .nil -- x monomial

def ms_cons2 : PreMS [id] := PreMS.cons (2, 1) ms_cons -- x^2 + x

example : destruct ms_nil = .none := by
  unfold ms_nil
  elim_destruct

example : destruct ms_cons = .some ((1, 1), ms_nil) := by
  unfold ms_cons ms_nil
  elim_destruct

example : destruct (ms_nil.neg) = .none := by
  unfold ms_nil
  elim_destruct

example : destruct (ms_nil.add ms_nil) = .none := by
  unfold ms_nil
  elim_destruct

example : destruct (ms_nil.add ms_cons) = .some ((1, 1), ms_nil) := by
  unfold ms_nil ms_cons
  elim_destruct

example : destruct (ms_cons.add ms_nil) = .some ((1, 1), ms_nil) := by
  unfold ms_nil ms_cons
  elim_destruct

example : destruct (ms_cons.add ms_cons) = .some ((1, 2), .nil) := by
  unfold ms_cons
  elim_destruct
  sorry -- it's ok we don't need tail

example : destruct (ms_cons.add ms_cons2) = .some ((2, 1), .nil) := by
  unfold ms_cons ms_cons2
  elim_destruct
  sorry -- it's ok we don't need tail

example : destruct (ms_nil.mul ms_nil) = .none := by
  unfold ms_nil
  elim_destruct

example : destruct (ms_nil.mul ms_cons) = .none := by
  unfold ms_nil ms_cons
  elim_destruct

example : destruct (ms_cons.mul ms_nil) = .none := by
  unfold ms_nil ms_cons
  elim_destruct

example : destruct (ms_cons.mul ms_cons) = .some ((2, 1), .nil) := by
  unfold ms_cons
  elim_destruct
  sorry -- it's ok we don't need tail

example : destruct ms_monom = .some ((1, 1), @PreMS.nil id []) := by
  unfold ms_monom
  elim_destruct
  -- elim_destruct

example :
    let ms_monom2 : PreMS [id, id] := PreMS.monomial [id, id] 1;
    destruct ms_monom2 = .some ((0, PreMS.monomial [id] 0), @PreMS.nil id [id]) := by
  intro ms_monom2
  unfold ms_monom2
  elim_destruct

example : destruct ms_const = .some ((0, 42), .nil) := by
  unfold ms_const
  elim_destruct
  rfl

example : destruct (PreMS.mul ms_const ms_cons)  = .some ((0, 42), .nil) := by
  unfold ms_const ms_cons
  elim_destruct
  sorry -- OK

example : destruct (PreMS.add (PreMS.add ms_cons.neg ms_cons) ms_cons) = .none := by
  unfold ms_cons
  elim_destruct
  sorry -- OK

example :
    let ms_zero : PreMS [id] := PreMS.const [id] 0;
    destruct (PreMS.mul ms_cons ms_zero) = .none := by
  intro ms_zero
  unfold ms_zero ms_cons
  elim_destruct
  sorry -- OK

example : destruct (PreMS.invSeries.apply ms_nil) = .none := by
  unfold ms_nil
  elim_destruct
  sorry -- OK

example : destruct (ms_nil.inv) = .none := by
  unfold ms_nil
  simp only [elimDestruct]

example : destruct (ms_cons.inv) = .none := by
  unfold ms_cons
  elim_destruct
  sorry -- OK

example : (if (1 : ℝ) < (3/2 : ℝ) then 1 else 0) = 1 := by
  norm_num1
  simp only [↓reduceIte]

example : destruct (TendstoTactic.PreMS.updateBasis
    (TendstoTactic.BasisExtension.insert (Real.log ∘ fun x => x) TendstoTactic.BasisExtension.nil) 1) =
    some ((0, PreMS.updateBasis BasisExtension.nil 1), nil) := by
  simp [PreMS_const]

-- #check updateBasis'_const

-- example : True := by
--   have : Stream'.Seq.destruct
--     (TendstoTactic.PreMS.updateBasis'
--       (TendstoTactic.BasisExtension.insert (Real.log ∘ fun x => x) TendstoTactic.BasisExtension.nil) 1) =
--       ?_ := by
--     elim_destruct
--     -- sorry
--     -- norm_num1
--     -- rw [updateBasis'_const]
--     -- first | simp only [elimDestruct, PreMS_const] | simp only [↓reduceIte, PreMS_const] | simp only [LogBasis.insertLastLog]
--   sorry


end ElimDestruct

open Filter Topology

example :
  let f := fun (y : ℝ) ↦ y;
  Tendsto f atTop atTop := by
  simp
  compute_asymptotics

--- exp testing

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
    let f := fun (y : ℝ) ↦ Real.exp y;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp (y^2) / Real.log y;
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.log y - Real.log (Real.log y);
    Tendsto f atTop atTop := by
  compute_asymptotics

example :
    let f := fun (y : ℝ) ↦ Real.exp (y^2) - Real.exp y;
    Tendsto f atTop atTop := by
  compute_asymptotics

set_option maxHeartbeats 0 in
lemma lol :
    let f := fun (y : ℝ) ↦ Real.exp (y^2) / Real.exp y;
    Tendsto f atTop atTop := by
  compute_asymptotics

#print axioms lol

-- set_option maxHeartbeats 0 in
-- example :
--     let f := fun (y : ℝ) ↦ Real.exp (Real.exp y) / Real.exp y;
--     Tendsto f atTop atTop := by
--   compute_asymptotics

-- set_option trace.profiler true in
-- set_option maxHeartbeats 0 in
-- example :
--     let f := fun (y : ℝ) ↦ Real.exp (Real.exp y) / Real.exp (y^2);
--     Tendsto f atTop atTop := by
--   compute_asymptotics

-- set_option maxHeartbeats 0 in
-- example :
--     let f := fun (y : ℝ) ↦ Real.exp (Real.log y) - y
--     Tendsto f atTop (𝓝 0):= by
--   compute_asymptotics

--- end exp testing

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
  let f : ℝ → ℝ := fun (x : ℝ) ↦ (( - 6  *  x  *  x  *  x)  +  ((2  *  x  *  x)  +  ((1)  *  ((4  *  x)  -  ( - 2  *  x)))))  *  ((( - 6  *  x)  -  ( - 2))  /  ((8  *  x)  *  ( - 9  *  x  *  x  *  x)));
  Tendsto f atTop (nhds (-(1/2))) := by
  simp only
  compute_asymptotics

example :
  let f : ℝ → ℝ := fun (x : ℝ) ↦ (( - 6  *  x  *  x  *  x)  +  ((2  *  x  *  x)  +  ((1)  *  ((4  *  x)  -  ( - 2  *  x)))))  *  ((( - 6  *  x)  -  ( - 2))  /  ((8  *  x)  *  ( - 9  *  x  *  x  *  x)));
  Tendsto f atTop (nhds (-1/2)) := by
  simp only
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ x^(1/2 : ℝ) / (x^(1/3 : ℝ) + x^(-1/3 : ℝ) + 18);
  Tendsto f atTop atTop := by
  simp only
  compute_asymptotics


---- log testing

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
  have : 0 < Real.log 2 := by sorry
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

lemma lel :
    let f := fun (y : ℝ) ↦ (Real.log (1 + y) - y) / (y^2);
    Tendsto f (𝓝[>] 0) (𝓝 (-1/2)) := by
  compute_asymptotics

#print axioms lel

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

--- end log testing

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

-- TODO: add guard_msg
-- example :
--   let f := fun (x : ℝ) ↦ x^(-1 : ℝ) - 1/x;
--   Tendsto f (𝓝[>] 0) atTop := by
--   simp only
--   compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ (1 + x)^(Real.pi) / (3 + 2*x^(314/100 : ℝ))
  Tendsto f atTop atTop := by
  simp only
  have : 0 < Real.pi := Real.pi_pos
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
  have : 0 < Real.pi := Real.pi_pos
  compute_asymptotics

example :
  let f := fun (x : ℝ) ↦ 1 / (1 + Real.pi * x) - 1 / (1 + 3 * x);
  Tendsto f atTop (nhds 0) := by
  simp only
  have : 0 < Real.pi := Real.pi_pos
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

-- TODO: why two goals?
-- example :
--     let f := fun (y : ℝ) ↦ (1 : ℝ);
--     Tendsto f (𝓝[≠] 0) (𝓝 2) := by
--   compute_asymptotics
--   all_goals sorry

end DifferentFilters
