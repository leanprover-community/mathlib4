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
* `HasGlobalSectionsFunctor J A`: typeclass stating that the constant sheaf functor `A ⥤ Sheaf J A`
  has a right-adjoint.
* `Sheaf.Γ J A`: the global sections functor `Sheaf J A ⥤ A`, defined as the right-adjoint of the
  constant sheaf functor, whenever that exists.
* `constantSheafΓAdj J A`: the adjunction between the constant sheaf functor and `Sheaf.Γ J A`.
* `Sheaf.ΓNatIsoSheafSections J A hT`: on sites with a terminal object `T`, `Sheaf.Γ J A` exists and
  is isomorphic to the functor evaluating sheaves at `T`.
* `Sheaf.ΓNatIsoLim J A`: when `A` has limits of shape `Cᵒᵖ`, `Sheaf.Γ J A` exists and is isomorphic
  to the functor taking each sheaf to the limit of its underlying presheaf.
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
  (A : Type u₂) [Category.{v₂} A] [HasWeakSheafify J A]

/-- Typeclass stating that the constant sheaf functor has a right adjoint. This right adjoint will
then be called the global sections functor and written `Sheaf.Γ`. -/
abbrev HasGlobalSectionsFunctor := (constantSheaf J A).IsLeftAdjoint

/-- We define the global sections functor as the right-adjoint of the constant sheaf functor
whenever it exists. -/
noncomputable def Sheaf.Γ [HasGlobalSectionsFunctor J A] : Sheaf J A ⥤ A :=
  (constantSheaf J A).rightAdjoint

/-- The constant sheaf functor is by definition left-adjoint to the global sections functor. -/
noncomputable def constantSheafΓAdj [HasGlobalSectionsFunctor J A] :
    constantSheaf J A ⊣ Γ J A :=
  Adjunction.ofIsLeftAdjoint (constantSheaf J A)

instance [HasGlobalSectionsFunctor J A] : (Γ J A).IsRightAdjoint := by
  unfold Γ; infer_instance

/-- Sites with a terminal object admit a global sections functor. -/
instance hasGlobalSectionsFunctor_of_hasTerminal [HasTerminal C] :
    HasGlobalSectionsFunctor J A :=
  ⟨_, ⟨constantSheafAdj J A terminalIsTerminal⟩⟩

/-- On sites with a terminal object, the global sections functor is isomorphic to the functor
of sections on that object. -/
noncomputable def Sheaf.ΓNatIsoSheafSections [HasTerminal C] {T : C} (hT : IsTerminal T) :
    Γ J A ≅ (sheafSections J A).obj (op T) :=
  (constantSheafΓAdj J A).rightAdjointUniq (constantSheafAdj J A hT)

/-- Every site `C` admits a global sections functor for `A`-valued sheaves when `A` has limits of
shape `Cᵒᵖ`. -/
instance hasGlobalSectionsFunctor_of_hasLimitsOfShape [HasLimitsOfShape Cᵒᵖ A] :
    HasGlobalSectionsFunctor J A :=
  ⟨sheafToPresheaf J A ⋙ lim, ⟨constLimAdj.comp (sheafificationAdjunction J A)⟩⟩

/-- Global sections of sheaves are naturally isomorphic to the limits of the underlying presheaves,
provided those exist. -/
noncomputable def Sheaf.ΓNatIsoLim [HasLimitsOfShape Cᵒᵖ A] :
    Γ J A ≅ sheafToPresheaf J A ⋙ lim :=
  (constantSheafΓAdj J A).rightAdjointUniq (constLimAdj.comp (sheafificationAdjunction J A))

-- this is currently needed to obtain the instance `HasSheafify J (Type max u v)`.
attribute [local instance] CategoryTheory.Types.instConcreteCategory
attribute [local instance] CategoryTheory.Types.instFunLike

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

/-- For sheaves of types, the global sections functor is isomorphic to the sections functor
on presheaves. -/
noncomputable def Sheaf.ΓNatIsoSectionsFunctor :
    Γ J (Type max u v) ≅ sheafToPresheaf J _ ⋙ Functor.sectionsFunctor _ :=
  (ΓNatIsoLim J _).trans (isoWhiskerLeft _ Types.limNatIsoSectionsFunctor)

/-- For sheaves of types, the global sections functor is isomorphic to the covariant hom
functor of the terminal sheaf. -/
noncomputable def Sheaf.ΓNatIsoCoyoneda :
    Γ J (Type max u v) ≅ coyoneda.obj (op (⊤_ _)) := by
  refine (ΓNatIsoSectionsFunctor J).trans ?_
  refine (isoWhiskerLeft _ sectionsFunctorNatIsoCoyoneda).trans ?_
  let e : (⊤_ Sheaf J _).val ≅ ⊤_ Cᵒᵖ ⥤ Type max u v :=
    (terminalIsoIsTerminal (terminalIsTerminal.isTerminalObj (sheafToPresheaf J _) _)).symm
  refine (isoWhiskerLeft _ <| coyoneda.mapIso e.op).trans ?_
  exact NatIso.ofComponents fun _ ↦ Sheaf.homEquiv.toIso.symm

end CategoryTheory
