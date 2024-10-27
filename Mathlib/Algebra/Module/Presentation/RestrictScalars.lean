/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.Presentation.Basic

/-!
# Presentation of the restriction of scalars

-/


namespace Module

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (M : Type*)
  [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
  (rM : Relations B) (pM : Presentation M rM)
  {rB : Relations A} (pB : Presentation B rB)

namespace Relation

structure RestrictScalarsData where
  lift (g : rB.G) (r : rM.R) : rB.G × rM.G →₀ A
  linearCombination_lift (g : rB.G) (r : rM.R) :
    Finsupp.linearCombination A (fun (⟨b, m⟩ : rB.G × rM.G) ↦
      Finsupp.single m (pB.solution.var b)) (lift g r) = rM.relation r

namespace RestrictScalarsData

variable {rM} {pB} (data : RestrictScalarsData rM pB)

@[simps]
noncomputable def restrictsScalars : Relations A where
  G := rB.G × rM.G
  R := Sum (rB.R × rM.G) (rB.G × rM.R)
  relation := fun x ↦ match x with
    | Sum.inl ⟨r, g⟩ => Finsupp.embDomain (Function.Embedding.sectl rB.G g) (rB.relation r)
    | Sum.inr ⟨g, r⟩ => data.lift g r

end RestrictScalarsData

end Relation

namespace Presentation

variable {rM}
variable (data : Relation.RestrictScalarsData rM pB)

def restrictScalarsSolution : data.restrictsScalars.Solution M where
  var := fun ⟨b, m⟩ ↦ pB.solution.var b • pM.solution.var m
  relation := by
    rintro (⟨r, g⟩ | ⟨g, r⟩)
    · dsimp
      sorry
    · dsimp
      sorry

end Presentation

end Module
