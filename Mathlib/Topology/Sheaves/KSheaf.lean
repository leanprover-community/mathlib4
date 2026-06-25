/-
Copyright (c) 2026 Yannis Monbru-Carcelero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yannis Monbru Carcelero
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompleteLattice.MulticoequalizerDiagram
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Sets.BaseChangeNhds
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Ksheaves

We define K-sheaves on a T2 topological space with value in an arbitrary category.

One may expect this notion to come from sheaves on a site of compact subset of a topological space
but there is no coresponding Grothendieck topology on compact subsets, in particular
because the `nonempty_isColimit_coconeOfCompacts` condition can't be expressed as a
limit condition.
-/

@[expose] public section

universe w v u

open Topology CategoryTheory TopologicalSpace Opposite Limits

variable {A : Type u} [Category.{v} A] {X : TopCat.{w}}

namespace TopCat

variable (A X) in
/-- The category of `A`-valued presheaves on a (bundled) topological space `X`. -/
def KPresheaf : Type max u v w := (Compacts X)ᵒᵖ ⥤ A

instance : Category (KPresheaf.{w, v, u} A X) :=
  inferInstanceAs (Category ((Compacts X)ᵒᵖ ⥤ A : Type max u v w))

namespace KPresheaf

@[simp]
theorem id_app (P : KPresheaf A X) (K : (Compacts X)ᵒᵖ) : NatTrans.app (𝟙 P) K = 𝟙 _ := rfl

@[simp]
theorem comp_app (P Q R : KPresheaf A X) (K : (Compacts X)ᵒᵖ) (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).app K = f.app K ≫ g.app K := rfl

@[ext]
lemma ext (P Q : KPresheaf A X) (f g : P ⟶ Q) (w : ∀ K : Compacts X, f.app (op K) = g.app (op K)) :
    f = g := by
  apply NatTrans.ext
  ext K
  induction K with | _ K => ?_
  apply w

/--
The pushforward of a KPresheaf by a proper map -/
def pushforwardObj {Y : TopCat.{w}} {f : X ⟶ Y} (pf : IsProperMap f.hom') (F : KPresheaf A X) :
    (KPresheaf A Y) := ((Functor.whiskeringLeft _ _ _ ).obj
  (Compacts.properPreimage_mono pf).functor.op).obj F

/--
The pushforward by a proper map as a functor over KPresheaves -/
def pushforward {Y : TopCat.{w}} {f : X ⟶ Y} (pf : IsProperMap f.hom') :
    KPresheaf A X ⥤ KPresheaf A Y where
  obj := pushforwardObj pf
  map := ((Functor.whiskeringLeft _ _ _ ).obj
  (Compacts.properPreimage_mono pf).functor.op).map

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- If P is a KPresheaf, and K a compact subset then P(K) is equiped with a
structure of cocone over the diagramm defined by the P(L) for L a compact
neighbourhood of K -/
@[simps]
def coconeOfCompacts (P : KPresheaf A X) (K : Compacts X) :
    Cocone ((Subtype.mono_coe K.compactNhds).functor.op ⋙ P) where
  pt := P.obj (op K)
  ι.app K' := P.map (homOfLE (Compacts.subset_of_mem_compactNhds K'.unop.prop)).op
  ι.naturality _ _ _ := by
    dsimp
    rw [← P.map_comp, Category.comp_id]
    rfl
/-- For P a KPresheaf, and K a compact subset then P(K) is equiped with a
structure of cocone over the diagramm defined by the P(closure U) for U an open
neighbourhood of K -/
def coconeOfClosureOfOpens (P : KPresheaf A X) (K : Compacts X) :=
  Cocone.whisker K.mono_oRcNhds_to_compactNhds.functor.op <| P.coconeOfCompacts K

variable [T2Space X]

set_option backward.isDefEq.respectTransparency false in
/--
For`K`a compact and `P`a KPresheaf verifying the third axiom of KSheaves, this is
a recipi to build maps from `P.obj(op K)` by only using the open relatively
comapct neighbourhoods and not all the compacts neighbourhoods. -/
noncomputable def mapOfOpenClosure (P : KPresheaf A X) (K : Compacts X)
    (h : (IsColimit (P.coconeOfCompacts K))) {G : (K.openRcNhds)ᵒᵖ ⥤ A} (t : Cocone G)
    (α : (K.mono_oRcNhds_to_compactNhds.functor.op ⋙ (Subtype.mono_coe _).functor.op ⋙ P) ⟶ G) :
    P.obj (op K) ⟶ t.pt :=
  ((Functor.Final.isColimitWhiskerEquiv _ _).invFun h ).map t α

set_option backward.isDefEq.respectTransparency false in
@[ext]
lemma hom_K_ext (P : KPresheaf A X) {K : Compacts X} (h : (IsColimit (P.coconeOfCompacts K)))
    {W : A} {f f' : P.obj (op K) ⟶ W}
    (w : ∀ V, (P.coconeOfClosureOfOpens K).ι.app V ≫ f = (P.coconeOfClosureOfOpens K).ι.app V ≫ f')
    : f = f' :=
  ((Functor.Final.isColimitWhiskerEquiv _ _).invFun h ).hom_ext w

/-- The Ksheaf condition. It's a generalisation of the one of J.Pardon that
corespond to the one of J.Lurie in the case of usual categories.

There is no coresponding Grothendieck topology on compact subsets, in particular
because the nonempty_isColimit_coconeOfCompacts condition can't be expressed as a
limit condition. -/
structure IsKSheaf (P : KPresheaf A X) : Prop where
  nonempty_isTerminal : Nonempty (IsTerminal (P.obj (op ⊥)))
  isPullback {K₁ K₂ K₃ K₄ : Compacts X} (h : Lattice.BicartSq K₁ K₂ K₃ K₄) :
    IsPullback (P.map ((homOfLE h.le₂₄).op)) (P.map ((homOfLE h.le₃₄).op))
      (P.map ((homOfLE h.le₁₂).op)) (P.map ((homOfLE h.le₁₃).op))
  nonempty_isColimit_coconeOfCompacts (K : Compacts X) :
      Nonempty (IsColimit (P.coconeOfCompacts K))

end KPresheaf

variable [T2Space X]

variable (X A) in
/-- The category of Ksheaves taking values in `A` on a T2Space. -/
abbrev KSheaf := ObjectProperty.FullSubcategory (KPresheaf.IsKSheaf (X := X) (A := A))

namespace KSheaf

set_option backward.isDefEq.respectTransparency false in
/--
For`K`a compact and `P`a KSheaf, this is a recipi to build maps from
`P.obj(op K)` by only using the open relatively comapct neighbourhoods and not
all the compacts neighbourhoods. -/
noncomputable def mapOfOpenClosure (P : KSheaf A X) (K : Compacts X) {G : (K.openRcNhds)ᵒᵖ ⥤ A}
    (t : Cocone G)
    (α : (K.mono_oRcNhds_to_compactNhds.functor.op ⋙ (Subtype.mono_coe _).functor.op ⋙ P.obj) ⟶ G) :
    P.obj.obj (op K) ⟶ t.pt :=
  ((Functor.Final.isColimitWhiskerEquiv _ _).invFun
  (Classical.choice <| P.property.nonempty_isColimit_coconeOfCompacts K) ).map t α

set_option backward.isDefEq.respectTransparency false in
@[ext]
lemma hom_K_ext (P : KSheaf A X) {K : Compacts X} {W : A} {f f' : P.obj.obj (op K) ⟶ W}
    (w : ∀ V, (P.obj.coconeOfClosureOfOpens K).ι.app V ≫ f =
    (P.obj.coconeOfClosureOfOpens K).ι.app V ≫ f') : f = f' :=
  ((Functor.Final.isColimitWhiskerEquiv _ _).invFun
  (Classical.choice <| P.property.nonempty_isColimit_coconeOfCompacts K)).hom_ext w

open Compacts

variable {Y : TopCat.{w}} [T2Space Y] [LocallyCompactSpace Y] {f : X ⟶ Y}
    (pf : IsProperMap f.hom') (F : KSheaf A X)

lemma isKSheafPushforwardObj : (F.obj.pushforwardObj pf).IsKSheaf where
  nonempty_isTerminal := by
    exact F.property.nonempty_isTerminal
  isPullback h:=
    F.property.isPullback <|
    Lattice.BicartSq.pushforward h (properPreimage pf)
    (fun _ _ ↦ Compacts.ext rfl) (fun _ _ ↦ Compacts.ext rfl)
  nonempty_isColimit_coconeOfCompacts K :=
    Nonempty.intro <|
    (Functor.Final.isColimitWhiskerEquiv ((nhdsMap_mono pf K).functor.op)
      _ ).invFun
    (Classical.choice (F.property.nonempty_isColimit_coconeOfCompacts (properPreimage pf K)))

variable {Y : TopCat.{w}} [T2Space Y] [LocallyCompactSpace Y] {f : X ⟶ Y}
    (pf : IsProperMap f.hom')

/--
The pushforward of a Ksheaf by a proper map as a sheaf -/
def pushforwardObj (F : KSheaf A X) : (KSheaf A Y) := ⟨_, F.isKSheafPushforwardObj pf⟩

/--
The pushforward of a KSheaf as a functor -/
def pushforward : KSheaf A X ⥤ KSheaf A Y :=
  ObjectProperty.lift _
  (ObjectProperty.ι KPresheaf.IsKSheaf ⋙ (KPresheaf.pushforward pf))
  (fun F ↦ F.isKSheafPushforwardObj pf)

end KSheaf

end TopCat
