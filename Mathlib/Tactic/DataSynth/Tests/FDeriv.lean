import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul

import Mathlib.Tactic.DataSynth.Elab
import Mathlib.Tactic.DataSynth.Attr

section missing
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

end missing

attribute [data_synth out f'] HasFDerivAt

attribute [data_synth] 
  hasFDerivAt_id
  hasFDerivAt_id'
  hasFDerivAt_const
  HasFDerivAt.comp
  HasFDerivAt.fun_comp
  HasFDerivAt.fun_add
  HasFDerivAt.fun_sub
  HasFDerivAt.fun_mul

set_option pp.proofs false 
variable (x₀ : ℝ)
  (f : ℝ → ℝ) (f' : ℝ → (ℝ →L[ℝ] ℝ)) (hf : ∀ x, HasFDerivAt f (f' x) x)
  (g : ℝ → ℝ) (g' : ℝ → (ℝ →L[ℝ] ℝ)) (hg : ∀ x, HasFDerivAt g (g' x) x)

set_option trace.Meta.Tactic.data_synth true 

#check
 (by data_synth :
  HasFDerivAt (𝕜:=ℝ) (fun x : ℝ => x) _ x₀)

#check
 (by data_synth (disch:=skip) (norm:=simp [smul_smul,←add_smul]) :
  HasFDerivAt (𝕜:=ℝ) (fun x : ℝ => x*x*x+x) _ x₀)

#check
 (by data_synth (disch:=skip) (norm:=simp) :
  HasFDerivAt (𝕜:=ℝ) (fun x : ℝ => x*3) _ x₀)

#check
 (by data_synth (disch:=skip) (norm:=simp) :
  HasFDerivAt (𝕜:=ℝ) (fun x : ℝ => (3:ℝ)*x) _ x₀)

#check
 (by data_synth :
  HasFDerivAt (𝕜:=ℝ) f _ x₀)

#check
 (by data_synth :
  HasFDerivAt (𝕜:=ℝ) (fun x => f (f (f x))) _ x₀)
