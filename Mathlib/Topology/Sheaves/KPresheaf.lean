/-
Copyright (c) 2026 Yannis Monbru-Carcelero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yannis Monbru Carcelero
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompleteLattice.MulticoequalizerDiagram
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Sets.BaseChangeNhds

/-!
# KPresheaves on a topological space

We define `TopCat.KPresheaf A X` simply as `(Compacts X)ᵒᵖ ⥤ A`,
and inherit the category structure with natural transformations as morphisms.

We define constructions that will allow to state the condition of being a K-sheaf.

We also define the pushforward of a presheaf by a proper map.

-/
@[expose] public section

universe w v u

open Topology CategoryTheory TopologicalSpace Opposite Limits

variable {A : Type u} [Category.{v} A] {X : TopCat.{w}}

namespace TopCat

variable (A X) in
/-- The category of `A`-valued K-presheaves on a (bundled) topological space `X` -/
abbrev KPresheaf : Type max u v w := (Compacts X)ᵒᵖ ⥤ A

namespace KPresheaf

/-- If `P` is a K-presheaf, and `K` a compact subset then `P.obj (op K)` is equipped with a
structure of cocone over the diagram defined by the `P.obj (op L)` for `L` a compact
neighbourhood of `K` -/
@[simps, implicit_reducible]
def coconeOfCompacts (P : KPresheaf A X) (K : Compacts X) :
    Cocone ((Set.mono_coe K.compactNhds).functor.op ⋙ P) where
  pt := P.obj (op K)
  ι.app K' := P.map <| opHomOfLE (Compacts.subset_of_mem_compactNhds K'.unop.prop)
  ι.naturality _ _ _ := by
    dsimp
    rw [← P.map_comp, Category.comp_id]
    rfl

/-- For `P` a K-presheaf, and `K` a compact subset then `P.obj (op K)` is equipped with a
structure of cocone over the diagram defined by the `P.obj (op (closure (U : Set X))`
for `U` an open neighbourhood of `K` -/
@[simps!, implicit_reducible]
def coconeOfClosureOfOpens (P : KPresheaf A X) (K : Compacts X) :=
  Cocone.whisker K.openRcNhdsToCompactNhds_mono.functor.op <| P.coconeOfCompacts K

variable [T2Space X]

/-- For `K` a compact and `P` a K-presheaf verifying the third axiom of K-sheaves, this is
a recipe to build maps from `P.obj (op K)` by only using the open relatively
compact neighbourhoods and not all the compacts neighbourhoods. -/
@[no_expose]
noncomputable def descOfOpenClosure (P : KPresheaf A X) (K : Compacts X)
    (h : (IsColimit (P.coconeOfCompacts K))) {Z : A}
    (ι : K.openRcNhdsToCompactNhds_mono.functor.op ⋙ (Set.mono_coe _).functor.op ⋙ P ⟶
      (Functor.const _).obj Z) :
    P.obj (op K) ⟶ Z :=
  ((Functor.Final.isColimitWhiskerEquiv
    K.openRcNhdsToCompactNhds_mono.functor.op _).symm h).desc (Cocone.mk _ ι)

@[reassoc (attr := simp)]
lemma map_comp_descOfOpenClosure (P : KPresheaf A X) {K : Compacts X} (V : K.openRcNhds)
    (h : (IsColimit (P.coconeOfCompacts K))) {Z : A}
    (ι : K.openRcNhdsToCompactNhds_mono.functor.op ⋙ (Set.mono_coe _).functor.op ⋙ P ⟶
      (Functor.const _).obj Z) :
    dsimp% P.map (op (homOfLE (V.property.2.trans subset_closure))) ≫ P.descOfOpenClosure K h ι =
      ι.app (op V) :=
  ((Functor.Final.isColimitWhiskerEquiv
    K.openRcNhdsToCompactNhds_mono.functor.op _).symm h).fac (Cocone.mk _ ι) (op V)

@[ext]
lemma hom_ext_of_isColimit_coconeOfCompacts (P : KPresheaf A X) {K : Compacts X}
    (h : IsColimit (P.coconeOfCompacts K))
    {W : A} {f f' : P.obj (op K) ⟶ W}
    (w : ∀ V, dsimp% (P.coconeOfClosureOfOpens K).ι.app V ≫ f =
      (P.coconeOfClosureOfOpens K).ι.app V ≫ f') :
    f = f' :=
  ((Functor.Final.isColimitWhiskerEquiv K.openRcNhdsToCompactNhds_mono.functor.op
    _).symm h).hom_ext w

/-- The pushforward by a proper map as a functor over K-presheaves -/
@[simps!, implicit_reducible]
def pushforward {Y : TopCat.{w}} (f : X ⟶ Y) (pf : IsProperMap f) :
    KPresheaf A X ⥤ KPresheaf A Y :=
  (Functor.whiskeringLeft _ _ _).obj (Compacts.properPreimage_mono pf).functor.op

end KPresheaf

end TopCat
