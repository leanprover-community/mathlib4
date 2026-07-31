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
  [HasForget₂ V TopCat] {G : Type*} [Monoid G] [TopologicalSpace G]

variable (V G) in
abbrev isContinuous : ObjectProperty (Action V G) := IsContinuous

instance : (isContinuous V G).IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) := sorry

instance : (isContinuous V G).IsClosedUnderLimitsOfShape WalkingCospan := sorry

instance (ι : Type*) [Finite ι] :
    (isContinuous V G).IsClosedUnderColimitsOfShape (Discrete ι) := sorry

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
