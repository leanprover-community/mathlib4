import Lean 

import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import Mathlib.Tactic.DataSynth.Elab
import Mathlib.Tactic.DataSynth.Attr


section MissingTheorems
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem hasFDerivAt_id' (x : E) :
    HasFDerivAt (fun x => x) (ContinuousLinearMap.id 𝕜 E) x := hasFDerivAt_id x

theorem HasFDerivAt.fun_comp
    {f : E → F} {f' : E →L[𝕜] F} {g : F → G} {g' : F →L[𝕜] G} {x : E}
    (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : 
    HasFDerivAt (fun x => g (f x)) (g'.comp f') x :=
  HasFDerivAtFilter.comp x hg hf hf.continuousAt

open ContinuousLinearMap in
theorem HasFDerivAt.div_const (c : E → 𝕜) {c'} (x : E) (hc : HasFDerivAt c c' x) (d : 𝕜) :
    HasFDerivAt (𝕜:=𝕜) (fun x => c x / d) (smulRight c' (d⁻¹)) x := by
  sorry

open ContinuousLinearMap in
theorem HasFDerivAt.fun_div
    (c d : E → 𝕜) (x : E) {c' d'}
    (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x) (hx : d x ≠ 0) :
    HasFDerivAt (𝕜:=𝕜) (fun y => c y / d y) 
      (smulRight ((smulRight c' (d x) - smulRight d' (c x))) ((d x ^ 2)⁻¹)) x := by
  sorry


end MissingTheorems

attribute [data_synth out f'] HasFDerivAt

attribute [data_synth]
  hasFDerivAt_id
  hasFDerivAt_id'
  HasFDerivAt.fun_add
  HasFDerivAt.fun_sub
  HasFDerivAt.fun_mul
  hasFDerivAt_inv
  hasFDerivAt_exp
  HasFDerivAt.exp
  HasFDerivAt.sin
  HasFDerivAt.cos
  hasFDerivAt_inv
  HasFDerivAt.div_const
  HasFDerivAt.fun_div
  HasFDerivAt.prod
  HasFDerivAt.fst
  HasFDerivAt.snd
