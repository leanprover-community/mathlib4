/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Preservation of pointwise left Kan extensions by external products

We prove that if a functor `H' : D' ⥤ V` is a pointwise left Kan extension of
`H : D ⥤ V` along `L : D ⥤ D'`, and if `K : E ⥤ V` is any functor such that
for any `e : E`, the functor `tensorRight (K.obj e)` commutes with colimits of
shape `CostructuredArrow L d`, then the functor `H' ⊠ K` is a pointwise left Kan extension
of `H ⊠ K` along `L.prod (𝟭 E)`.

We also prove a similar criterion to establish that `K ⊠ H'` is a pointwise left Kan
extension of `K ⊠ H` along `(𝟭 E).prod L`.
-/

@[expose] public section
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.MonoidalCategory.ExternalProduct

noncomputable section
open scoped Prod

variable {V : Type u₁} [Category.{v₁} V] [MonoidalCategory V]
  {D : Type u₂} {D' : Type u₃} {E : Type u₄}
  [Category.{v₂} D] [Category.{v₃} D'] [Category.{v₄} E]
  {H : D ⥤ V} {L : D ⥤ D'} (H' : D' ⥤ V) (α : H ⟶ L ⋙ H') (K : E ⥤ V)

/-- Given an extension `α : H ⟶ L ⋙ H'`, this is the canonical extension
`H ⊠ K ⟶ L.prod (𝟭 E) ⋙ H' ⊠ K` it induces through bifunctoriality of the external product. -/
abbrev extensionUnitLeft : H ⊠ K ⟶ L.prod (𝟭 E) ⋙ H' ⊠ K :=
    (externalProductBifunctor D E V).map (α ×ₘ K.leftUnitor.inv)

/-- Given an extension `α : H ⟶ L ⋙ H'`, this is the canonical extension
`K ⊠ H ⟶ (𝟭 E).prod L ⋙ K ⊠ H'` it induces through bifunctoriality of the external product. -/
abbrev extensionUnitRight : K ⊠ H ⟶ (𝟭 E).prod L ⋙ K ⊠ H' :=
    (externalProductBifunctor E D V).map (K.leftUnitor.inv ×ₘ α)

set_option backward.defeqAttrib.useBackward true in
/-- If `H' : D' ⥤ V` is a pointwise left Kan extension along `L : D ⥤ D'` at `(d : D')`
and if tensoring right with an object preserves colimits in `V`,
then `H' ⊠ K : D' × E ⥤ V` is a pointwise left Kan extension along `L × (𝟭 E)` at `(d, e)`
for every `e : E`. -/
def isPointwiseLeftKanExtensionAtExtensionUnitLeft
    (d : D') (P : (Functor.LeftExtension.mk H' α).IsPointwiseLeftKanExtensionAt d) (e : E)
    [Limits.PreservesColimitsOfShape (CostructuredArrow L d) (tensorRight <| K.obj e)] :
    Functor.LeftExtension.mk (H' ⊠ K) (extensionUnitLeft H' α K) |>.IsPointwiseLeftKanExtensionAt
      (d, e) := by
  set cone := Functor.LeftExtension.mk (H' ⊠ K) (extensionUnitLeft H' α K) |>.coconeAt (d, e)
  let equiv := CostructuredArrow.prodEquivalence L (𝟭 E) d e |>.symm
  apply Limits.IsColimit.ofWhiskerEquivalence equiv
  let I : CostructuredArrow L d ⥤ (CostructuredArrow L d) × CostructuredArrow (𝟭 E) e :=
    -- this definition makes it easier to prove finality of I
    (prod.rightUnitorEquivalence (CostructuredArrow L d)).inverse ⋙
      (𝟭 _).prod (Functor.fromPUnit.{0} <| .mk <| 𝟙 _)
  letI : I.Final := by
    letI : Functor.fromPUnit.{0} (.mk (𝟙 e) : CostructuredArrow (𝟭 E) e) |>.Final :=
      Functor.final_fromPUnit_of_isTerminal <| CostructuredArrow.mkIdTerminal (S := 𝟭 E) (Y := e)
    apply Iff.mp <| Functor.final_iff_final_comp
      (F := (prod.rightUnitorEquivalence <| CostructuredArrow L d).inverse)
      (G := (𝟭 _).prod <| Functor.fromPUnit.{0} (.mk (𝟙 e) : CostructuredArrow (𝟭 E) e))
    infer_instance
  apply Functor.Final.isColimitWhiskerEquiv I (Limits.Cocone.whisker equiv.functor cone) |>.toFun
  -- through all the equivalences above, the new cocone we consider is in fact
  -- `tensorRight (K.obj e)|>.mapCocone <| (Functor.LeftExtension.mk H' α).coconeAt d`
  let diag_iso :
      (CostructuredArrow.proj L d ⋙ H) ⋙ tensorRight (K.obj e) ≅
      I ⋙ equiv.functor ⋙ CostructuredArrow.proj (L.prod <| 𝟭 E) (d, e) ⋙ H ⊠ K :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  apply Limits.IsColimit.equivOfNatIsoOfIso diag_iso
    (d := Limits.Cocone.whisker I (Limits.Cocone.whisker equiv.functor cone))
    (c := tensorRight (K.obj e) |>.mapCocone <| (Functor.LeftExtension.mk H' α).coconeAt d)
    (Limits.Cocone.ext <| .refl _) |>.toFun
  exact Limits.PreservesColimit.preserves (F := tensorRight <| K.obj e) P |>.some

/-- If `H' : D' ⥤ V` is a pointwise left Kan extension along `L : D ⥤ D'`,
and if tensoring right with an object preserves colimits in `V`
then `H' ⊠ K : D' × E ⥤ V` is a pointwise left Kan extension along `L × (𝟭 E)`. -/
def isPointwiseLeftKanExtensionExtensionUnitLeft
    [∀ d : D', ∀ e : E,
      Limits.PreservesColimitsOfShape (CostructuredArrow L d) (tensorRight <| K.obj e)]
    (P : (Functor.LeftExtension.mk H' α).IsPointwiseLeftKanExtension) :
    Functor.LeftExtension.mk (H' ⊠ K) (extensionUnitLeft H' α K) |>.IsPointwiseLeftKanExtension :=
  fun ⟨d, e⟩ ↦ isPointwiseLeftKanExtensionAtExtensionUnitLeft H' α K d (P d) e

set_option backward.defeqAttrib.useBackward true in
/-- If `H' : D' ⥤ V` is a pointwise left Kan extension along `L : D ⥤ D'` at `d : D'` and
if tensoring left with an object preserves colimits in `V`,
then `K ⊠ H' : D' × E ⥤ V` is a pointwise left Kan extension along `(𝟭 E) × L` at `(e, d)` for
every `e`. -/
def isPointwiseLeftKanExtensionAtExtensionUnitRight
    (d : D') (P : (Functor.LeftExtension.mk H' α).IsPointwiseLeftKanExtensionAt d) (e : E)
    [Limits.PreservesColimitsOfShape (CostructuredArrow L d) (tensorLeft <| K.obj e)] :
    (Functor.LeftExtension.mk (K ⊠ H')
      (extensionUnitRight H' α K)).IsPointwiseLeftKanExtensionAt (e, d) := by
  set cone := Functor.LeftExtension.mk (K ⊠ H')
    (extensionUnitRight H' α K) |>.coconeAt (e, d)
  let equiv := CostructuredArrow.prodEquivalence (𝟭 E) L e d |>.symm
  apply Limits.IsColimit.ofWhiskerEquivalence equiv
  let I : CostructuredArrow L d ⥤ CostructuredArrow (𝟭 E) e × CostructuredArrow L d :=
    -- this definition makes it easier to prove finality of I
    (prod.leftUnitorEquivalence <| CostructuredArrow L d).inverse ⋙
      (Functor.fromPUnit.{0} <| .mk <| 𝟙 _).prod (𝟭 _)
  letI : I.Final := by
    letI : Functor.fromPUnit.{0} (.mk (𝟙 e) : CostructuredArrow (𝟭 E) e) |>.Final :=
      Functor.final_fromPUnit_of_isTerminal <| CostructuredArrow.mkIdTerminal (S := 𝟭 E) (Y := e)
    apply Iff.mp <| Functor.final_iff_final_comp
      (F := (prod.leftUnitorEquivalence <| CostructuredArrow L d).inverse)
      (G := Functor.fromPUnit.{0} (.mk (𝟙 e) : CostructuredArrow (𝟭 E) e) |>.prod <| 𝟭 _)
    infer_instance
  apply Functor.Final.isColimitWhiskerEquiv I (Limits.Cocone.whisker equiv.functor cone) |>.toFun
  -- through all the equivalences above, the new cocone we consider is in fact
  -- `(tensorLeft <| K.obj e).mapCocone <| (Functor.LeftExtension.mk H' α).coconeAt d`
  let diag_iso :
      (CostructuredArrow.proj L d ⋙ H) ⋙ tensorLeft (K.obj e) ≅
      I ⋙ equiv.functor ⋙ CostructuredArrow.proj (𝟭 E |>.prod L) (e, d) ⋙ K ⊠ H :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  apply Limits.IsColimit.equivOfNatIsoOfIso diag_iso
    (d := Limits.Cocone.whisker I <| Limits.Cocone.whisker equiv.functor cone)
    (c := (tensorLeft <| K.obj e).mapCocone <| (Functor.LeftExtension.mk H' α).coconeAt d)
    (Limits.Cocone.ext <| .refl _) |>.toFun
  exact Limits.PreservesColimit.preserves (F := tensorLeft <| K.obj e) P |>.some

/-- If `H' : D' ⥤ V` is a pointwise left Kan extension along `L : D ⥤ D'` and
if tensoring left with an object preserves colimits in `V`,
then `K ⊠ H' : D' × E ⥤ V` is a pointwise left Kan extension along `(𝟭 E) × L`. -/
def isPointwiseLeftKanExtensionExtensionUnitRight
    [∀ d : D', ∀ e : E,
      Limits.PreservesColimitsOfShape (CostructuredArrow L d) (tensorLeft <| K.obj e)]
    (P : Functor.LeftExtension.mk H' α |>.IsPointwiseLeftKanExtension) :
    Functor.LeftExtension.mk (K ⊠ H') (extensionUnitRight H' α K) |>.IsPointwiseLeftKanExtension :=
  fun ⟨e, d⟩ ↦ isPointwiseLeftKanExtensionAtExtensionUnitRight H' α K d (P d) e

end

end CategoryTheory.MonoidalCategory.ExternalProduct
