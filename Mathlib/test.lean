
import Mathlib

set_option trace.Meta.synthInstance true
--set_option trace.Meta.synthPending true
--set_option trace.Meta.synthInstance.newAnswer true

variable (𝕜 E : Type) [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

#synth NormedSpace 𝕜 E
#synth NormedSpace 𝕜 (E →L[𝕜] E)
#synth NormedSpace 𝕜 (E →L[𝕜] E →L[𝕜] E)
#synth NormedSpace 𝕜 (E →L[𝕜] E →L[𝕜] E →L[𝕜] E)
#synth  SeminormedAddCommGroup (E →L[𝕜] E →L[𝕜] E →L[𝕜] E →L[𝕜] E) -- fails

#exit

class SeminormedAddCommGroup (E : Type) : Prop

class NontriviallyNormedField (𝕜 : Type) : Prop

class NormedSpace (𝕜 E : Type) [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] : Prop

structure LinearMap (𝕜 E F : Type) [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :=
  toFun : E → F

notation:25 M " →L[" R "] " M₂ => LinearMap R M M₂

instance (𝕜 E F : Type) [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    SeminormedAddCommGroup (E →L[𝕜] F) where

instance (𝕜 E F : Type) [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    NormedSpace 𝕜 (E →L[𝕜] F) where

variable (𝕜 E : Type) [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

#synth NormedSpace 𝕜 E
#synth NormedSpace 𝕜 (E →L[𝕜] E)
#synth NormedSpace 𝕜 (E →L[𝕜] E →L[𝕜] E)
#synth NormedSpace 𝕜 (E →L[𝕜] E →L[𝕜] E →L[𝕜] E)

#synth NormedSpace 𝕜 (E →L[𝕜] E →L[𝕜] E →L[𝕜] E →L[𝕜] E)
