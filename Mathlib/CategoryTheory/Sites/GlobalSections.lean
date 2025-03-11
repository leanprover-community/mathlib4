/-
Copyright (c) 2025 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Global sections of sheaves
In this file we define a global sections functor `Sheaf.Γ : Sheaf J A ⥤ A` and show that it
is isomorphic to several other constructions when they exist, most notably evaluation of sheaves
on a terminal object and `Functor.sectionsFunctor`.

## Main definitions / results
* `Sheaf.Γ J A`: the global sections functor `Sheaf J A ⥤ A`, defined as taking each sheaf to
  the limit of its underlying presheaf in `A`.
* `constantSheafΓAdj J A`: the adjunction between the constant sheaf functor and `Sheaf.Γ J A`.
* `Sheaf.ΓNatIsoSheafSections J A hT`: on sites with a terminal object `T`, `Sheaf.Γ J A` is
  isomorphic to the functor evaluating sheaves at `T`.
* `Sheaf.ΓNatIsoSectionsFunctor J`: for sheaves of types, `Sheaf.Γ J A` is isomorphic to the
  functor taking each sheaf to the type of sections of its underlying presheaf in the sense of
  `Functor.sections`.
* `Sheaf.ΓNatIsoCoyonedaObj J`: for sheaves of types, `Sheaf.Γ J A` is isomorphic to the
  coyoneda embedding of the terminal sheaf, i.e. the functor sending each sheaf `F` to the type
  of morphisms from the terminal sheaf to `F`.
-/

universe u v w u₂ v₂

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u₂) [Category.{v₂} A]

/-- The global sections functor `Γ`, taking sheaves valued in `A` to its global sections in `A`.
It is given here as a limit instead of evaluation on a terminal object of `C`; this has the
advantage of not requiring `C` to have a terminal object, but the disadvantage of requiring `A`
to have limits of shape `Cᵒᵖ`. -/
noncomputable def Sheaf.Γ [HasLimitsOfShape Cᵒᵖ A] : Sheaf J A ⥤ A :=
  sheafToPresheaf J A ⋙ lim

/-- The constant sheaf functor is left-adjoint to the global sections functor when both exist. -/
noncomputable def constantSheafΓAdj [HasWeakSheafify J A] [HasLimitsOfShape Cᵒᵖ A] :
    constantSheaf J A ⊣ Γ J A :=
  constLimAdj.comp (sheafificationAdjunction J A)

instance [HasWeakSheafify J A] [HasLimitsOfShape Cᵒᵖ A] : (constantSheaf J A).IsLeftAdjoint :=
  ⟨Γ J A, ⟨constantSheafΓAdj J A⟩⟩

instance [HasWeakSheafify J A] [HasLimitsOfShape Cᵒᵖ A] : (Γ J A).IsRightAdjoint :=
  ⟨constantSheaf J A, ⟨constantSheafΓAdj J A⟩⟩

/-- For functors `F : C ⥤ Type _`, `F.sections` is naturally isomorphic to the type `⊤_ _ ⟶ F`
of natural transformations from the terminal functor to `F`. -/
noncomputable def sectionsFunctorNatIsoCoyoneda :
    Functor.sectionsFunctor.{v,max u w} C ≅ coyoneda.obj (op (⊤_ _)) :=
  let _ : ∀ X, Unique ((⊤_ C ⥤ Type max u w).obj X) := fun X ↦ (terminalObjIso X).toEquiv.unique
  NatIso.ofComponents fun F ↦ {
      hom s := { app X := fun _ ↦ s.1 X }
      inv s := ⟨fun X ↦ s.app X default, fun f ↦
        (congrFun (s.naturality f).symm _).trans <| congrArg (s.app _) <| Unique.eq_default _⟩
      inv_hom_id := funext fun s ↦ by
        dsimp; ext X x; simp [Unique.eq_default x]
  }

/-- When `C` has a terminal object, the global sections functor is isomorphic to the functor
of sections on that object. -/
noncomputable def Sheaf.ΓNatIsoSheafSections [HasLimitsOfShape Cᵒᵖ A] {T : C}
    (hT : IsTerminal T) : Γ J A ≅ (sheafSections J A).obj (op T) := by
  refine (isoWhiskerLeft _ ?_).trans <| (sheafSectionsNatIsoEvaluation J A).symm
  refine @asIso _ _ _ _ { app := fun F ↦ limit.π _ _ } ?_
  have hT' := initialOpOfTerminal hT
  exact (NatTrans.isIso_iff_isIso_app _).2 <| fun F ↦ isIso_π_of_isInitial hT' F

/-- For sheaves of types, the global sections functor is isomorphic to the sections functor
on presheaves. -/
noncomputable def Sheaf.ΓNatIsoSectionsFunctor :
    Γ J (Type max u w) ≅ sheafToPresheaf J _ ⋙ Functor.sectionsFunctor _ :=
  isoWhiskerLeft _ <| Types.limNatIsoSectionsFunctor

/-- For sheaves of types, the global sections functor is isomorphic to the covariant hom
functor of the terminal sheaf. -/
noncomputable def Sheaf.ΓNatIsoCoyonedaObj :
    Γ J (Type max u w) ≅ coyoneda.obj (op (⊤_ _)) := by
  refine (ΓNatIsoSectionsFunctor J).trans ?_
  refine (isoWhiskerLeft _ sectionsFunctorNatIsoCoyoneda).trans ?_
  let e : (⊤_ Sheaf J _).val ≅ ⊤_ Cᵒᵖ ⥤ Type max u w :=
    (terminalIsoIsTerminal (terminalIsTerminal.isTerminalObj (sheafToPresheaf J _) _)).symm
  refine (isoWhiskerLeft _ <| coyoneda.mapIso e.op).trans ?_
  exact NatIso.ofComponents fun _ ↦ Sheaf.homEquiv.toIso.symm

end CategoryTheory
