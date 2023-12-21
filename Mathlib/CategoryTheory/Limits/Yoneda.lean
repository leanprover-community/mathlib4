/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.Util.AssertExists

#align_import category_theory.limits.yoneda from "leanprover-community/mathlib"@"e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b"

/-!
# Limit properties relating to the (co)yoneda embedding.

We calculate the colimit of `Y ↦ (X ⟶ Y)`, which is just `PUnit`.
(This is used in characterising cofinal functors.)

We also show the (co)yoneda embeddings preserve limits and jointly reflect them.
-/

open Opposite CategoryTheory Limits

universe w v u

namespace CategoryTheory

namespace Coyoneda

variable {C : Type v} [SmallCategory C]

/-- The colimit cocone over `coyoneda.obj X`, with cocone point `PUnit`.
-/
@[simps]
def colimitCocone (X : Cᵒᵖ) : Cocone (coyoneda.obj X) where
  pt := PUnit
  ι := { app := by aesop_cat }
#align category_theory.coyoneda.colimit_cocone CategoryTheory.Coyoneda.colimitCocone

/-- The proposed colimit cocone over `coyoneda.obj X` is a colimit cocone.
-/
@[simps]
def colimitCoconeIsColimit (X : Cᵒᵖ) : IsColimit (colimitCocone X)
    where
  desc s _ := s.ι.app (unop X) (𝟙 _)
  fac s Y := by
    funext f
    convert congr_fun (s.w f).symm (𝟙 (unop X))
    simp only [coyoneda_obj_obj, Functor.const_obj_obj, types_comp_apply,
      coyoneda_obj_map, Category.id_comp]
  uniq s m w := by
    apply funext; rintro ⟨⟩
    dsimp
    rw [← w]
    simp
#align category_theory.coyoneda.colimit_cocone_is_colimit CategoryTheory.Coyoneda.colimitCoconeIsColimit

instance (X : Cᵒᵖ) : HasColimit (coyoneda.obj X) :=
  HasColimit.mk
    { cocone := _
      isColimit := colimitCoconeIsColimit X }

/-- The colimit of `coyoneda.obj X` is isomorphic to `PUnit`.
-/
noncomputable def colimitCoyonedaIso (X : Cᵒᵖ) : colimit (coyoneda.obj X) ≅ PUnit := by
  apply colimit.isoColimitCocone
    { cocone := _
      isColimit := colimitCoconeIsColimit X }
#align category_theory.coyoneda.colimit_coyoneda_iso CategoryTheory.Coyoneda.colimitCoyonedaIso

end Coyoneda

variable {C : Type u} [Category.{v} C]

open Limits

/-- The yoneda embedding `yoneda.obj X : Cᵒᵖ ⥤ Type v` for `X : C` preserves limits. -/
instance yonedaPreservesLimits (X : C) : PreservesLimits (yoneda.obj X) where
  preservesLimitsOfShape {J} 𝒥 :=
    { preservesLimit := fun {K} =>
        { preserves := fun {c} t =>
            { lift := fun s x =>
                Quiver.Hom.unop (t.lift ⟨op X, fun j => (s.π.app j x).op, fun j₁ j₂ α => by
                  simp [← s.w α]⟩)
              fac := fun s j => funext fun x => Quiver.Hom.op_inj (t.fac _ _)
              uniq := fun s m w =>
                funext fun x => by
                  refine Quiver.Hom.op_inj (t.uniq ⟨op X, _, _⟩ _ fun j => ?_)
                  exact Quiver.Hom.unop_inj (congrFun (w j) x) } } }
#align category_theory.yoneda_preserves_limits CategoryTheory.yonedaPreservesLimits

/-- The coyoneda embedding `coyoneda.obj X : C ⥤ Type v` for `X : Cᵒᵖ` preserves limits. -/
instance coyonedaPreservesLimits (X : Cᵒᵖ) : PreservesLimits (coyoneda.obj X) where
  preservesLimitsOfShape {J} 𝒥 :=
    { preservesLimit := fun {K} =>
        { preserves := fun {c} t =>
            { lift := fun s x =>
                t.lift
                  ⟨unop X, fun j => s.π.app j x, fun j₁ j₂ α => by
                    dsimp
                    simp [← s.w α]⟩
              -- See library note [dsimp, simp]
              fac := fun s j => funext fun x => t.fac _ _
              uniq := fun s m w =>
                funext fun x => by
                  refine' t.uniq ⟨unop X, _⟩ _ fun j => _
                  exact congrFun (w j) x } } }
#align category_theory.coyoneda_preserves_limits CategoryTheory.coyonedaPreservesLimits

/-- The yoneda embeddings jointly reflect limits. -/
def yonedaJointlyReflectsLimits (J : Type w) [SmallCategory J] (K : J ⥤ Cᵒᵖ) (c : Cone K)
    (t : ∀ X : C, IsLimit ((yoneda.obj X).mapCone c)) : IsLimit c :=
  let s' : ∀ s : Cone K, Cone (K ⋙ yoneda.obj s.pt.unop) := fun s =>
    ⟨PUnit, fun j _ => (s.π.app j).unop, fun j₁ j₂ α =>
      funext fun _ => Quiver.Hom.op_inj (s.w α).symm⟩
  { lift := fun s => ((t s.pt.unop).lift (s' s) PUnit.unit).op
    fac := fun s j => Quiver.Hom.unop_inj (congr_fun ((t s.pt.unop).fac (s' s) j) PUnit.unit)
    uniq := fun s m w => by
      apply Quiver.Hom.unop_inj
      suffices (fun _ : PUnit => m.unop) = (t s.pt.unop).lift (s' s) by
        apply congr_fun this PUnit.unit
      apply (t _).uniq (s' s) _ fun j => _
      intro j
      funext
      exact Quiver.Hom.op_inj (w j) }
#align category_theory.yoneda_jointly_reflects_limits CategoryTheory.yonedaJointlyReflectsLimits

/-- The coyoneda embeddings jointly reflect limits. -/
def coyonedaJointlyReflectsLimits (J : Type w) [SmallCategory J] (K : J ⥤ C) (c : Cone K)
    (t : ∀ X : Cᵒᵖ, IsLimit ((coyoneda.obj X).mapCone c)) : IsLimit c :=
  let s' : ∀ s : Cone K, Cone (K ⋙ coyoneda.obj (op s.pt)) := fun s =>
    ⟨PUnit, fun j _ => s.π.app j, fun j₁ j₂ α => funext fun _ => (s.w α).symm⟩
  { lift := fun s => (t (op s.pt)).lift (s' s) PUnit.unit
    fac := fun s j => congr_fun ((t _).fac (s' s) j) PUnit.unit
    uniq := fun s m w => by
      suffices (fun _ : PUnit => m) = (t _).lift (s' s) by apply congr_fun this PUnit.unit
      apply (t _).uniq (s' s) _ fun j => _
      intro j
      funext
      exact w j }
#align category_theory.coyoneda_jointly_reflects_limits CategoryTheory.coyonedaJointlyReflectsLimits

variable {D : Type u} [SmallCategory D]

instance yonedaFunctorPreservesLimits : PreservesLimits (@yoneda D _) := by
  apply preservesLimitsOfEvaluation
  intro K
  change PreservesLimits (coyoneda.obj K)
  infer_instance
#align category_theory.yoneda_functor_preserves_limits CategoryTheory.yonedaFunctorPreservesLimits

instance coyonedaFunctorPreservesLimits : PreservesLimits (@coyoneda D _) := by
  apply preservesLimitsOfEvaluation
  intro K
  change PreservesLimits (yoneda.obj K)
  infer_instance
#align category_theory.coyoneda_functor_preserves_limits CategoryTheory.coyonedaFunctorPreservesLimits

instance yonedaFunctorReflectsLimits : ReflectsLimits (@yoneda D _) := inferInstance
#align category_theory.yoneda_functor_reflects_limits CategoryTheory.yonedaFunctorReflectsLimits

instance coyonedaFunctorReflectsLimits : ReflectsLimits (@coyoneda D _) := inferInstance
#align category_theory.coyoneda_functor_reflects_limits CategoryTheory.coyonedaFunctorReflectsLimits

end CategoryTheory

assert_not_exists Set.range

-- Porting note: after the port see if this import can be removed
-- assert_not_exists AddCommMonoid
