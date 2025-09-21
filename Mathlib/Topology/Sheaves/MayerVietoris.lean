/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# Mayer-Vietoris squares

Given two open subsets `U` and `V` of a topological space `T`,
we construct the associated Mayer-Vietoris square:
```
U ⊓ V --->   U
  |          |
  v          v
  V   ---> U ⊔ V
```

-/

universe u

namespace Opens

open CategoryTheory Limits TopologicalSpace

variable {T : Type u} [TopologicalSpace T]

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- A square consisting of opens `X₂ ⊓ X₃`, `X₂`, `X₃` and `X₂ ⊔ X₃` is
a Mayer-Vietoris square. -/
@[simps! toSquare]
noncomputable def mayerVietorisSquare' (sq : Square (Opens T))
    (h₄ : sq.X₄ = sq.X₂ ⊔ sq.X₃) (h₁ : sq.X₁ = sq.X₂ ⊓ sq.X₃) :
    (Opens.grothendieckTopology T).MayerVietorisSquare :=
  GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback
    (J := (Opens.grothendieckTopology T)) sq
    (Square.IsPullback.mk _ (by
      refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
      · intro s
        apply homOfLE
        rw [h₁, le_inf_iff]
        exact ⟨leOfHom s.fst, leOfHom s.snd⟩
      all_goals intros; apply Subsingleton.elim))
    (fun x hx ↦ by
      rw [h₄] at hx
      obtain (hx | hx) := hx
      · exact ⟨_, _, ⟨Sieve.ofArrows_mk _ _ WalkingPair.left, hx⟩⟩
      · exact ⟨_, _, ⟨Sieve.ofArrows_mk _ _ WalkingPair.right, hx⟩⟩)

/-- The Mayer-Vietoris square attached to two open subsets
of a topological space. -/
@[simps!]
noncomputable def mayerVietorisSquare (U V : Opens T) :
    (Opens.grothendieckTopology T).MayerVietorisSquare :=
  mayerVietorisSquare'
    { X₁ := U ⊓ V
      X₂ := U
      X₃ := V
      X₄ := U ⊔ V
      f₁₂ := homOfLE inf_le_left
      f₁₃ := homOfLE inf_le_right
      f₂₄ := homOfLE le_sup_left
      f₃₄ := homOfLE le_sup_right
      fac := Subsingleton.elim _ _ } rfl rfl

end Opens
