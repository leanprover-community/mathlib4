/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Functoriality of the symmetry of equivalences

Using the calculus of mates in `Mathlib.CategoryTheory.Adjunction.Mates`, we prove that passing
to the symmetric equivalence defines an equivalence between `C ≌ D` and `(D ≌ C)ᵒᵖ`,
and provides the definition of the functor that takes an equivalence to its inverse.

## Main definitions
- `Equivalence.symmEquiv C D`: the equivalence `(C ≌ D) ≌ (D ≌ C)ᵒᵖ` obtained by
  taking `Equivalence.symm` on objects, and `conjugateEquiv` on maps.
- `Equivalence.inverseFunctor C D`: The functor `(C ≌ D) ⥤ (D ⥤ C)ᵒᵖ` sending an equivalence
  `e` to the functor `e.inverse`.
- `congrLeftFunctor C D E`: the functor (C ≌ D) ⥤ ((C ⥤ E) ≌ (D ⥤ E))ᵒᵖ that applies
  `Equivalence.congrLeft` on objects, and whiskers left by `conjugateEquiv` on maps.

-/

namespace CategoryTheory

open CategoryTheory.Functor NatIso Category

namespace Equivalence

variable (C : Type*) [Category C] (D : Type*) [Category D]

/-- The forward functor of the equivalence `(C ≌ D) ≌ (D ≌ C)ᵒᵖ`. -/
@[simps]
def symmEquivFunctor : (C ≌ D) ⥤ (D ≌ C)ᵒᵖ where
  obj e := Opposite.op e.symm
  map {e f} α := (mkHom <| conjugateEquiv f.toAdjunction e.toAdjunction <| asNatTrans α).op
  map_comp _ _ := Quiver.Hom.unop_inj (by cat_disch)

/-- The inverse functor of the equivalence `(C ≌ D) ≌ (D ≌ C)ᵒᵖ`. -/
@[simps!]
def symmEquivInverse : (D ≌ C)ᵒᵖ ⥤ (C ≌ D) :=
  Functor.leftOp
    { obj e := Opposite.op e.symm
      map {e f} α := Quiver.Hom.op <| mkHom <|
        conjugateEquiv e.symm.toAdjunction f.symm.toAdjunction |>.invFun <| asNatTrans α
      map_comp _ _ := Quiver.Hom.unop_inj (by cat_disch) }

/-- Taking the symmetric of an equivalence induces an equivalence of categories
`(C ≌ D) ≌ (D ≌ C)ᵒᵖ`. -/
@[simps]
def symmEquiv : (C ≌ D) ≌ (D ≌ C)ᵒᵖ where
  functor := symmEquivFunctor _ _
  inverse := symmEquivInverse _ _
  counitIso :=
    NatIso.ofComponents (fun e ↦ Iso.op <| Iso.refl _) <| fun _ ↦
      (by simp [symm, symmEquivInverse])
  unitIso :=
    NatIso.ofComponents (fun e ↦ Iso.refl _) <| fun _ ↦ by
      ext c
      simp [symm, symmEquivInverse]
  functor_unitIso_comp X := by
    simp [symm, symmEquivInverse]

/-- The `inverse` functor that sends a functor to its inverse. -/
@[simps!]
def inverseFunctor : (C ≌ D) ⥤ (D ⥤ C)ᵒᵖ :=
  (symmEquiv C D).functor ⋙ (Functor.op <| functorFunctor D C)

variable {C D}

/-- The `inverse` functor sends an equivalence to its inverse. -/
@[simps!]
def inverseFunctorObjIso (e : C ≌ D) :
    (inverseFunctor C D).obj e ≅ Opposite.op e.inverse := Iso.refl _

/-- We can compare the way we obtain a natural isomorphism `e.inverse ≅ f.inverse` from
an isomorphism `e ≌ f` via `inverseFunctor` with the way we get one through
`Iso.isoInverseOfIsoFunctor`. -/
lemma inverseFunctorMapIso_symm_eq_isoInverseOfIsoFunctor {e f : C ≌ D} (α : e ≅ f) :
    Iso.unop ((inverseFunctor C D).mapIso α.symm) =
    Iso.isoInverseOfIsoFunctor ((functorFunctor _ _).mapIso α) := by
  cat_disch

/-- An "unopped" version of the equivalence `inverseFunctorObj'. -/
@[simps!]
def inverseFunctorObj' (e : C ≌ D) :
    Opposite.unop ((inverseFunctor C D).obj e) ≅ e.inverse :=
  Iso.refl _

variable (C D) in
/-- Promoting `Equivalence.congrLeft` to a functor. -/
@[simps!]
def congrLeftFunctor (E : Type*) [Category E] : (C ≌ D) ⥤ ((C ⥤ E) ≌ (D ⥤ E))ᵒᵖ :=
  Functor.rightOp
    { obj f := f.unop.congrLeft
      map {e f} α := mkHom <| (whiskeringLeft _ _ _).map <|
        conjugateEquiv e.unop.toAdjunction f.unop.toAdjunction <| asNatTrans <|
          Quiver.Hom.unop α
      map_comp _ _ := by
        ext
        simp [← map_comp] }

end Equivalence

end CategoryTheory
