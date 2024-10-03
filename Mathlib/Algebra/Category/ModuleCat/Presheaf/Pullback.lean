/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.CategoryTheory.Elements

/-!
# Pullback of presheaves of modules

Let `F : C ⥤ D` be a functor, `R : Dᵒᵖ ⥤ RingCat` and `S : Cᵒᵖ ⥤ RingCat` be presheaves
of rings, and `φ : S ⟶ F.op ⋙ R` be a morphism of presheaves of rings,
we introduce the pullback functor `pullback : PresheafOfModules S ⥤ PresheafOfModules R`
as the left adjoint of `pushforward : PresheafOfModules R ⥤ PresheafOfModules S`.
The existence of this left adjoint functor is obtained under suitable universe assumptions (TODO).

-/

universe v v₁ v₂ u₁ u₂ u


-- to be moved
namespace CategoryTheory

open Limits

namespace Functor

open Opposite

-- universes could be generalized if `(Co)representable` was made more general
variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D] (F : D ⥤ C)

def leftAdjointDefinitionSet : Set C :=
  { X : C | Corepresentable (F ⋙ coyoneda.obj (op X)) }

lemma mem_leftAdjointDefinitionSet_iff (X : C) :
    X ∈ F.leftAdjointDefinitionSet ↔ Corepresentable (F ⋙ coyoneda.obj (op X)) := by rfl

namespace leftAdjointDefinitionSet

variable {F}

lemma isRightAdjoint (h : F.leftAdjointDefinitionSet = ⊤) : F.IsRightAdjoint := by
  replace h : ∀ X, Corepresentable (F ⋙ coyoneda.obj (op X)) := fun X ↦ by
    simp only [← mem_leftAdjointDefinitionSet_iff, h, Set.top_eq_univ, Set.mem_univ]
  exact (Adjunction.adjunctionOfEquivLeft
    (fun X Y ↦ ((coreprW (F ⋙ coyoneda.obj (op X))).app Y).toEquiv)
    (fun X Y Y' g f ↦ (by simp [coreprW_hom_app]))).isRightAdjoint

lemma mem_of_isColimit {J : Type*} [Category J] {R : J ⥤ C} {c : Cocone R}
    (hc : IsColimit c) (h : ∀ (j : J), R.obj j ∈ F.leftAdjointDefinitionSet) :
    c.pt ∈ F.leftAdjointDefinitionSet := by
  sorry

lemma colimit_mem {J : Type*} [Category J] (R : J ⥤ C) [HasColimit R]
    (h : ∀ (j : J), R.obj j ∈ F.leftAdjointDefinitionSet) :
    colimit R ∈ F.leftAdjointDefinitionSet :=
  mem_of_isColimit (colimit.isColimit R) h

end leftAdjointDefinitionSet

end Functor

end CategoryTheory

open CategoryTheory Limits Opposite

namespace PresheafOfModules

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

variable [(pushforward.{v} φ).IsRightAdjoint]

/-- The pullback functor `PresheafOfModules S ⥤ PresheafOfModules R` induced by
a morphism of presheaves of rings `S ⟶ F.op ⋙ R`, defined as the left adjoint
functor to the pushforward, when it exists. -/
noncomputable def pullback : PresheafOfModules.{v} S ⥤ PresheafOfModules.{v} R :=
  (pushforward.{v} φ).leftAdjoint

/-- Given a morphism of presheaves of rings `S ⟶ F.op ⋙ R`, this is the adjunction
between associated pullback and pushforward functors on the categories
of presheaves of modules. -/
noncomputable def pullbackPushforwardAdjunction : pullback.{v} φ ⊣ pushforward.{v} φ :=
  Adjunction.ofIsRightAdjoint (pushforward φ)

end

abbrev Elements {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  (M : PresheafOfModules.{v} R) := ((toPresheaf R).obj M ⋙ forget Ab).Elements

namespace Elements

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}} {M : PresheafOfModules.{v} R}

noncomputable abbrev freeYoneda (m : M.Elements) :
    PresheafOfModules.{v} R := (free R).obj (yoneda.obj m.1.unop)

noncomputable abbrev fromFreeYoneda (m : M.Elements) :
    m.freeYoneda ⟶ M :=
  (freeYonedaEquiv _ _).symm m.2

end Elements

-- to be moved to Presheaf.Generator
section

variable {C : Type u} [SmallCategory.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)

noncomputable abbrev freeYonedaCoproduct : PresheafOfModules.{u} R :=
    ∐ (Elements.freeYoneda (M := M))

noncomputable def fromFreeYonedaCoproduct : M.freeYonedaCoproduct ⟶ M :=
  Sigma.desc Elements.fromFreeYoneda

instance : Epi M.fromFreeYonedaCoproduct := sorry

noncomputable def toFreeYonedaCoproduct :
    (kernel M.fromFreeYonedaCoproduct).freeYonedaCoproduct ⟶ M.freeYonedaCoproduct :=
  (kernel M.fromFreeYonedaCoproduct).fromFreeYonedaCoproduct ≫ kernel.ι _

@[reassoc (attr := simp)]
lemma toFreeYonedaCoproduct_fromFreeYonedaCoproduct :
    M.toFreeYonedaCoproduct ≫ M.fromFreeYonedaCoproduct = 0 := by
  simp [toFreeYonedaCoproduct]

noncomputable abbrev freeYonedaCoproductsCokernelCofork :
    CokernelCofork M.toFreeYonedaCoproduct :=
  CokernelCofork.ofπ _ M.toFreeYonedaCoproduct_fromFreeYonedaCoproduct

def isColimitFreeYonedaCoproductsCokernelCofork :
    IsColimit M.freeYonedaCoproductsCokernelCofork := sorry

end

section

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

abbrev pullbackDefinitionSet : Set (PresheafOfModules.{u} S) :=
  (pushforward φ).leftAdjointDefinitionSet

namespace pullbackDefinitionSet

lemma free_yoneda_mem (X : C) :
    (free S).obj (yoneda.obj X) ∈ pullbackDefinitionSet φ :=
  ⟨op ((free R).obj (yoneda.obj (F.obj X))),
    ⟨NatIso.ofComponents
      (fun M ↦ Equiv.toIso
        ((freeYonedaEquiv M (F.obj X)).trans
          (freeYonedaEquiv ((pushforward φ).obj M) X).symm)) sorry⟩⟩

lemma eq_top : pullbackDefinitionSet φ = ⊤ := by
  ext M
  simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
  apply Functor.leftAdjointDefinitionSet.mem_of_isColimit
    M.isColimitFreeYonedaCoproductsCokernelCofork
  rintro (_|_)
  all_goals
    exact Functor.leftAdjointDefinitionSet.colimit_mem _ (fun _ ↦ free_yoneda_mem _ _)

end pullbackDefinitionSet

instance : (pushforward.{u} φ).IsRightAdjoint :=
  Functor.leftAdjointDefinitionSet.isRightAdjoint (pullbackDefinitionSet.eq_top φ)

end

end PresheafOfModules
