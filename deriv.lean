import Mathlib

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ} {x : 𝕜} {s : Set 𝕜} {f g : 𝕜 → F}
  {R : Type*} [DistribSMul R F] [inst : SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]
  -- * `𝕝`: division semiring. (Addition in `𝕝` is not used, so the results would work with a
  -- `GroupWithZero` if we had a `DistribSMulWithZero` typeclass.)
  {𝕝 : Type*} [DivisionSemiring 𝕝] [Module 𝕝 F] [SMulCommClass 𝕜 𝕝 F] [ContinuousConstSMul 𝕝 F]
  -- * `𝔸`: normed `𝕜`-algebra.

lemma iteratedFDerivWithin_comp_neg' (a : 𝕜) : iteratedFDerivWithin 𝕜 n (fun x ↦ f (-x)) s a
    = (-1 : 𝕜) ^ n • iteratedFDerivWithin 𝕜 n f (-s) (-a) := by
  induction n generalizing a with
  | zero => simp [iteratedFDerivWithin]
  | succ n ih =>
    have ih' : iteratedFDerivWithin 𝕜 n (fun x => f (-x)) s
      = fun a ↦ (-1 : 𝕜) ^ n • iteratedFDerivWithin 𝕜 n f (-s) (-a) := by
      ext b
      rw [ih b]
    rw [iteratedFDerivWithin_succ_eq_comp_left, iteratedFDerivWithin_succ_eq_comp_left,
      Function.comp_apply, Function.comp_apply, ih', ← Pi.smul_def,
      fderivWithin_const_smul_field' ((-1 : 𝕜) ^ n)
      (f := fun a ↦ iteratedFDerivWithin 𝕜 n f (-s) (-a)), fderivWithin_comp_neg a,
      ← neg_one_smul 𝕜 (fderivWithin 𝕜 _ (-s) (-a)), ← mul_smul _ (-1), ← pow_succ (-1) n, map_smul]
