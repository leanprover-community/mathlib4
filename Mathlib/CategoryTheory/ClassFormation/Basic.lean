/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib
public import Mathlib.CategoryTheory.Galois.Equivalence
public import Mathlib.CategoryTheory.Sites.Coherent.RegularTopology

/-!
# ...

-/

public section

universe w v u

open CategoryTheory Limits

namespace Action

variable {V : Type*} {FV : V → V → Type*} {CV : V → Type*}
  [∀ {X Y : V}, FunLike (FV X Y) (CV X) (CV Y)]
  [Category* V] [ConcreteCategory V FV]
   {G : Type*} [Monoid G]

variable (V) in
def trivialOnSet (S : Set G) : ObjectProperty (Action V G) :=
  fun X ↦ ∀ s ∈ S, X.ρ s = 1

set_option backward.isDefEq.respectTransparency false in
instance (J : Type*) [Category* J] [HasLimitsOfShape J V] (S : Set G) :
    (trivialOnSet V S).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    intro g hg
    exact (isLimitOfPreserves (Action.forget _ _) p.isLimit).hom_ext
      (fun j ↦ by simp [dsimp% (p.π.app j).comm g, dsimp% p.prop_diag_obj j g hg])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (J : Type*) [Category* J] [HasColimitsOfShape J V] (S : Set G) :
    (trivialOnSet V S).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    intro g hg
    exact (isColimitOfPreserves (Action.forget _ _) p.isColimit).hom_ext (fun j ↦ by
      simp [← dsimp% (p.ι.app j).comm g, dsimp% p.prop_diag_obj j g hg])

section

variable [HasForget₂ V TopCat] [TopologicalSpace G]
variable (V G) in
abbrev isContinuous : ObjectProperty (Action V G) := IsContinuous

instance : (isContinuous V G).IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) := sorry

instance : (isContinuous V G).IsClosedUnderLimitsOfShape WalkingCospan := sorry

instance (ι : Type*) [Finite ι] :
    (isContinuous V G).IsClosedUnderColimitsOfShape (Discrete ι) := sorry

end

end Action

namespace ContAction

open scoped FintypeCatDiscrete

variable (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

instance : PreGaloisCategory (ContAction FintypeCat.{w} G) where
  monoInducesIsoOnDirectSummand := sorry
  hasFiniteCoproducts := ⟨inferInstance⟩
  hasQuotientsByFiniteGroups := sorry

end ContAction

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

variable (C) in
abbrev PreGaloisCategory.isConnected : ObjectProperty C :=
  IsConnected

open PreGaloisCategory

namespace PreGaloisCategory

variable (F : C ⥤ FintypeCat.{w}) [GaloisCategory C] [FiberFunctor F]

#check (functorToContAction F)

#synth TopologicalSpace (Aut F)

#check ContAction
end PreGaloisCategory

namespace GaloisCategory

instance : Preregular (isConnected C).FullSubcategory where
  exists_fac := sorry

#check functorToContAction

abbrev grothendieckTopologyConnected :
    GrothendieckTopology (isConnected C).FullSubcategory :=
  regularTopology _

end GaloisCategory

end CategoryTheory
