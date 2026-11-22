/-
Copyright (c) 2026 Pavel Zorin-Kranich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pavel Zorin-Kranich
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Norm and completeness on the order dual

The order dual inherits the normed space structure and completeness of the original space.
-/

public section

namespace OrderDual

instance instNormedSpace {𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] : NormedSpace 𝕜 Eᵒᵈ := inferInstanceAs (NormedSpace 𝕜 E)

instance instCompleteSpace {E : Type*} [UniformSpace E] [CompleteSpace E] :
    CompleteSpace Eᵒᵈ := inferInstanceAs (CompleteSpace E)

end OrderDual
