/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Topology.Sets.Opens
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Opens and Over categories

In this file, given a topological space `X`, and `U : Opens X`,
we show that the category `Over U` (whose objects are the
`V : Opens X` equipped with a morphism `V ⟶ U`) is equivalent
to the category `Opens U`.

## TODO
* show that both functors of the equivalence `overEquivalence U` are continuous and
induce an equivalence between `Sheaf ((Opens.grothendieckTopology X).over U) A`
and `Sheaf (Opens.grothendieckTopology U) A` for any category `A`.

-/

universe u

open CategoryTheory Topology

namespace TopologicalSpace

variable {X : Type u} [TopologicalSpace X] (U : Opens X)

namespace Opens

/-- If `X` is a topological space and `U : Opens X`,
then the category `Over U` is equivalent to `Opens ↥U`. -/
@[simps!]
def overEquivalence : Over U ≌ Opens ↥U where
  functor.obj V := ⟨_, IsOpen.preimage (continuous_subtype_val) V.left.isOpen⟩
  functor.map f := homOfLE (Set.preimage_mono (f := Subtype.val) (leOfHom f.left))
  inverse.obj W :=
    Over.mk (Y := ⟨_, (U.isOpenEmbedding'.isOpen_iff_image_isOpen).1 W.isOpen⟩)
      (homOfLE (fun _ _ ↦ by aesop))
  inverse.map f := Over.homMk (homOfLE (Set.image_mono (leOfHom f)))
  unitIso := NatIso.ofComponents (fun V ↦ Over.isoMk (eqToIso (by
    ext x
    dsimp
    simp only [SetLike.mem_coe, Set.mem_image, Set.mem_preimage,
      Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right, iff_self_and]
    apply leOfHom V.hom)))
  counitIso := NatIso.ofComponents (fun V ↦ eqToIso (by aesop))

end Opens

end TopologicalSpace
