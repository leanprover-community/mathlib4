/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
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

abbrev PullbackObjIsDefined : PresheafOfModules.{v} S → Prop :=
  (pushforward φ).LeftAdjointObjIsDefined

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

noncomputable def pushforwardCompCoyonedaFreeYonedaCorepresentableBy (X : C) :
    (pushforward φ ⋙ coyoneda.obj (op ((free S).obj (yoneda.obj X)))).CorepresentableBy
      ((free R).obj (yoneda.obj (F.obj X))) where
  homEquiv {M} := (freeYonedaEquiv M (F.obj X)).trans
    (freeYonedaEquiv ((pushforward φ).obj M) X).symm
  homEquiv_comp := sorry

lemma pullbackObjIsDefined_free_yoneda (X : C) :
    PullbackObjIsDefined φ ((free S).obj (yoneda.obj X)) :=
  (pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).isCorepresentable

lemma pullbackObjIsDefined_eq_top :
    PullbackObjIsDefined.{u} φ = ⊤ := by
  ext M
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  apply Functor.leftAdjointObjIsDefined_of_isColimit
    M.isColimitFreeYonedaCoproductsCokernelCofork
  rintro (_ | _)
  all_goals
    apply Functor.leftAdjointObjIsDefined_colimit _
      (fun _ ↦ pullbackObjIsDefined_free_yoneda _ _)

instance : (pushforward.{u} φ).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (pullbackObjIsDefined_eq_top φ)

end

end PresheafOfModules
