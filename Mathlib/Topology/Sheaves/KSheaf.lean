/-
Copyright (c) 2026 Yannis Monbru-Carcelero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yannis Monbru Carcelero
-/
module

public import Mathlib.Topology.Sheaves.KPresheaf

/-!
# K-sheaves

We define K-sheaves on `X` a T2 topological space with value in an arbitrary category `A`.

This coresponds to the presheaves `F : KPresheaf A X` such that:
- `F.obj (∅)` is terminal.
- For any two compacts subsets `K₁` and `K₂` of `X`, `F.obj (K₁ ∪ K₂)` is the pullback
  of `F.obj K₁` and `F.obj K₂` over `F.obj (K₁ ∩ K₂)`.
- For any compact subset `K` of `X`, `F.obj K` is the colimit of the `F.obj L` for all the compacts
  subsets `L` of `X` such that `K` is in the interior of `L`.

The category of K-sheaves is a topos, because it is equivalent to the category of sheaves over `X`
(TODO Yannis Monbru Carcelero), but the condition that `K`-presheaves need to verify to
be `K`-sheaves is *not* expressed as the sheaf condition for a Grothendieck topology on
compact sets. Indeed, two of three conditions do involve limits, but the third
`nonempty_isColimit_coconeOfCompact` involves colimits.

## References

*[J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli
spaces of pseudo-holomorphic curves*, Section A.1][Pardon2016]
*[Jacob Lurie, *Higher Topos Theory*, Section 1.1.5][LurieHTT]
-/

@[expose] public section

universe w v u

open Topology CategoryTheory TopologicalSpace Opposite Limits

variable {A : Type u} [Category.{v} A] {X : TopCat.{w}} [T2Space X]

namespace TopCat

/-- The K-sheaf condition. It's a generalisation of the one of J.Pardon (definition A.1.4) that
  correspond to the one of J.Lurie (definition 7.3.4.1) in the case of usual categories.
-/
structure KPresheaf.IsKSheaf (P : KPresheaf A X) : Prop where
  nonempty_isTerminal : Nonempty (IsTerminal (P.obj (op ⊥)))
  isPullback {K₁ K₂ K₃ K₄ : Compacts X} (h : Lattice.BicartSq K₁ K₂ K₃ K₄) :
    IsPullback (P.map <| opHomOfLE h.le₂₄) (P.map <| opHomOfLE h.le₃₄)
      (P.map <| opHomOfLE h.le₁₂) (P.map <| opHomOfLE h.le₁₃)
  nonempty_isColimit_coconeOfCompacts (K : Compacts X) :
      Nonempty (IsColimit (P.coconeOfCompacts K))

variable (A X) in
/-- The object property of being a K-sheaf -/
abbrev KPresheaf.isKSheaf : ObjectProperty (KPresheaf A X) := IsKSheaf

variable (A X) in
/-- The category of K-sheaves taking values in `A` on a T2-Space. -/
abbrev KSheaf := (KPresheaf.isKSheaf A X).FullSubcategory

instance : (KPresheaf.isKSheaf A X).IsClosedUnderIsomorphisms where
  of_iso e h :=
    { nonempty_isTerminal := ⟨h.nonempty_isTerminal.some.ofIso (e.app _)⟩
      isPullback sq :=
        (h.isPullback sq).of_iso (e.app _) (e.app _) (e.app _) (e.app _)
          (by cat_disch) (by cat_disch) (by cat_disch) (by cat_disch)
      nonempty_isColimit_coconeOfCompacts K :=
        ⟨(IsColimit.equivOfNatIsoOfIso (Functor.isoWhiskerLeft _ e) _ _
            (by exact Cocone.ext (e.app _)))
          (h.nonempty_isColimit_coconeOfCompacts K).some⟩ }

namespace KSheaf

/-- If `P` is a K-sheaf, this is the evidence that for any `K` a compact subset of `X`,
 `P.obj.coconeOfCompacts K` is a colimit cocone
-/
@[no_expose]
noncomputable def isColimit (P : KSheaf A X) (K : Compacts X) :
    IsColimit (P.obj.coconeOfCompacts K) :=
  (P.property.nonempty_isColimit_coconeOfCompacts K).some

/-- For `K` a compact and `P` a K-sheaf, this is a recipe to build maps from
`P.obj (op K)` by only using the open relatively compact neighbourhoods and not
all the compacts neighbourhoods. -/
noncomputable def descOfOpenClosure (P : KSheaf A X) (K : Compacts X) {Z : A}
    (ι : K.openRcNhdsToCompactNhds_mono.functor.op ⋙ (Set.mono_coe _).functor.op ⋙ P.obj ⟶
      (Functor.const _).obj Z) :
    P.obj.obj (op K) ⟶ Z := P.obj.descOfOpenClosure K (P.isColimit K) ι

@[ext]
lemma hom_ext_of_compacts (P : KSheaf A X) {K : Compacts X} {W : A} {f f' : P.obj.obj (op K) ⟶ W}
    (w : ∀ V, dsimp% (P.obj.coconeOfClosureOfOpens K).ι.app V ≫ f =
    (P.obj.coconeOfClosureOfOpens K).ι.app V ≫ f') : f = f' :=
  KPresheaf.hom_ext_of_isColimit_coconeOfCompacts _ (P.isColimit K) w

open Compacts KPresheaf

variable {Y : TopCat.{w}} [T2Space Y] [LocallyCompactSpace Y] {f : X ⟶ Y}
    (pf : IsProperMap f) (F : KSheaf A X)

lemma isKSheaf_pushforward_obj : ((pushforward f pf).obj F.obj).IsKSheaf where
  nonempty_isTerminal := F.property.nonempty_isTerminal
  isPullback h :=
    F.property.isPullback <|
    Lattice.BicartSq.map h <| {
      toFun := properPreimage pf
      map_sup' := by aesop
      map_inf' := by aesop }
  nonempty_isColimit_coconeOfCompacts K :=
    ⟨(Functor.Final.isColimitWhiskerEquiv ((baseChangeCompactNhdsByProperPreimage_mono
       pf K).functor.op) _).symm (F.isColimit (properPreimage pf K))⟩

variable {Y : TopCat.{w}} [T2Space Y] [LocallyCompactSpace Y] (f : X ⟶ Y)
    (pf : IsProperMap f)

/-- The pushforward of a K-presheaf as a functor -/
@[simps!, implicit_reducible]
def pushforward : KSheaf A X ⥤ KSheaf A Y :=
  ObjectProperty.lift _
    (ObjectProperty.ι KPresheaf.IsKSheaf ⋙ (KPresheaf.pushforward f pf))
    (fun F ↦ F.isKSheaf_pushforward_obj pf)

/-- The isomorphism between the pushforwad of identity and the identity functor -/
def pushforwardId [LocallyCompactSpace X] :
    pushforward (𝟙 X) isProperMap_id ≅ 𝟭 (KSheaf A X) := Iso.refl _

/-- The isomorphism between the pushforwad of a composition and the composition of pushforwards -/
def pushforwardComp {Z : TopCat.{w}} [T2Space Z] [LocallyCompactSpace Z] {g : Y ⟶ Z}
    (pg : IsProperMap g) :
    pushforward (A := A) f pf ⋙ pushforward g pg ≅
    pushforward (f ≫ g) (pg.comp pf) := Iso.refl _

end KSheaf

end TopCat
