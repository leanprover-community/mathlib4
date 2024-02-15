import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul


variable (a b c : ℝ) (ha : a ≠ 0)


/--
info: HasFDerivAt.mul (hasFDerivAt_id' a)
  (hasFDerivAt_id' a) : HasFDerivAt (fun y => y * y) (a • ContinuousLinearMap.id ℝ ℝ + a • ContinuousLinearMap.id ℝ ℝ) a
-/
#guard_msgs in
#check (((by fun_prop) : @HasFDerivAt ℝ _ _ _ _ _ _ _ (fun x : ℝ => x * x) _ a))

/--
info: hasFDerivAt_inv' ha : HasFDerivAt Inv.inv (-((ContinuousLinearMap.mulLeftRight ℝ ℝ) a⁻¹) a⁻¹) a
-/
#guard_msgs in
#check ((by fun_prop (disch:=assumption)) : (@HasFDerivAt ℝ _ _ _ _ _ _ _ (fun x : ℝ => x⁻¹) _ a))


variable (ha' : a*a + 1 ≠ 0)

/--
info: HasFDerivAt.mul (HasFDerivAt.add_const (hasFDerivAt_id' a) 3)
  (HasFDerivAt.comp' a (hasFDerivAt_inv' ha')
    (HasFDerivAt.add_const (HasFDerivAt.mul (hasFDerivAt_id' a) (hasFDerivAt_id' a))
      1)) : HasFDerivAt (fun y => (y + 3) * (y * y + 1)⁻¹)
  ((a + 3) •
      ContinuousLinearMap.comp (-((ContinuousLinearMap.mulLeftRight ℝ ℝ) (a * a + 1)⁻¹) (a * a + 1)⁻¹)
        (a • ContinuousLinearMap.id ℝ ℝ + a • ContinuousLinearMap.id ℝ ℝ) +
    (a * a + 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
  a
-/
#guard_msgs in
#check ((by fun_prop (disch:=assumption)) : (@HasFDerivAt ℝ _ _ _ _ _ _ _ (fun x : ℝ => (x+3)*(x*x + 1)⁻¹) _ a))

  --
