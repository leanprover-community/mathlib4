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
                   -- 🎉 no goals
#align category_theory.coyoneda.colimit_cocone CategoryTheory.Coyoneda.colimitCocone

/-- The proposed colimit cocone over `coyoneda.obj X` is a colimit cocone.
-/
@[simps]
def colimitCoconeIsColimit (X : Cᵒᵖ) : IsColimit (colimitCocone X)
    where
  desc s _ := s.ι.app (unop X) (𝟙 _)
  fac s Y := by
    funext f
    -- ⊢ (NatTrans.app (colimitCocone X).ι Y ≫ (fun s x => NatTrans.app s.ι X.unop (𝟙 …
    convert congr_fun (s.w f).symm (𝟙 (unop X))
    -- ⊢ NatTrans.app s.ι Y f = ((coyoneda.obj X).map f ≫ NatTrans.app s.ι Y) (𝟙 X.un …
    simp only [coyoneda_obj_obj, Functor.const_obj_obj, types_comp_apply,
      coyoneda_obj_map, Category.id_comp]
  uniq s m w := by
    apply funext; rintro ⟨⟩
    -- ⊢ ∀ (x : (colimitCocone X).pt), m x = (fun s x => NatTrans.app s.ι X.unop (𝟙 X …
                  -- ⊢ m PUnit.unit = (fun s x => NatTrans.app s.ι X.unop (𝟙 X.unop)) s PUnit.unit
    dsimp
    -- ⊢ m PUnit.unit = NatTrans.app s.ι X.unop (𝟙 X.unop)
    rw [← w]
    -- ⊢ m PUnit.unit = (NatTrans.app (colimitCocone X).ι X.unop ≫ m) (𝟙 X.unop)
    simp
    -- 🎉 no goals
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
instance yonedaPreservesLimits (X : C) : PreservesLimits (yoneda.obj X)
    where preservesLimitsOfShape {J} 𝒥 :=
    { preservesLimit := fun {K} =>
        { preserves := fun {c} t =>
            { lift := fun s x =>
                Quiver.Hom.unop (t.lift ⟨op X, fun j => (s.π.app j x).op, fun j₁ j₂ α => _⟩)
              fac := fun s j => funext fun x => Quiver.Hom.op_inj (t.fac _ _)
              uniq := fun s m w =>
                funext fun x => by
                  refine' Quiver.Hom.op_inj (t.uniq ⟨op X, _, _⟩ _ fun j => _)
                  -- ⊢ ∀ (X : C) {J : Type v} (𝒥 : Category.{v, v} J) {K : J ⥤ Cᵒᵖ} {c : Cone K}, I …
                  · intro X _ _ _ _ _ s _ _ _ α  -- Porting note: refine' gave a crazy goal
                    -- ⊢ ((Functor.const J✝).obj (op X)).map α ≫ (fun j => (NatTrans.app s.π j x✝).op …
                    dsimp
                    -- ⊢ 𝟙 (op X) ≫ (NatTrans.app s.π j₂✝ x✝).op = (NatTrans.app s.π j₁✝ x✝).op ≫ K✝. …
                    simp [← s.w α]
                    -- 🎉 no goals
                  -- See library note [dsimp, simp]
                  · exact Quiver.Hom.unop_inj (congrFun (w j) x) } } }
                    -- 🎉 no goals
#align category_theory.yoneda_preserves_limits CategoryTheory.yonedaPreservesLimits

/-- The coyoneda embedding `coyoneda.obj X : C ⥤ Type v` for `X : Cᵒᵖ` preserves limits. -/
instance coyonedaPreservesLimits (X : Cᵒᵖ) : PreservesLimits (coyoneda.obj X)
    where preservesLimitsOfShape {J} 𝒥 :=
    { preservesLimit := fun {K} =>
        { preserves := fun {c} t =>
            { lift := fun s x =>
                t.lift
                  ⟨unop X, fun j => s.π.app j x, fun j₁ j₂ α => by
                    dsimp
                    -- ⊢ 𝟙 X.unop ≫ NatTrans.app s.π j₂ x = NatTrans.app s.π j₁ x ≫ K.map α
                    simp [← s.w α]⟩
                    -- 🎉 no goals
              -- See library note [dsimp, simp]
              fac := fun s j => funext fun x => t.fac _ _
              uniq := fun s m w =>
                funext fun x => by
                  refine' t.uniq ⟨unop X, _⟩ _ fun j => _
                  -- ⊢ m x ≫ NatTrans.app c.π j = NatTrans.app { pt := X.unop, π := NatTrans.mk fun …
                  exact congrFun (w j) x } } }
                  -- 🎉 no goals
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
      -- ⊢ m.unop = ((fun s => (IsLimit.lift (t s.pt.unop) (s' s) PUnit.unit).op) s).unop
      suffices (fun _ : PUnit => m.unop) = (t s.pt.unop).lift (s' s) by
        apply congr_fun this PUnit.unit
      apply (t _).uniq (s' s) _ fun j => _
      -- ⊢ ∀ (j : J), (fun x => m.unop) ≫ NatTrans.app ((yoneda.obj s.pt.unop).mapCone  …
      intro j
      -- ⊢ (fun x => m.unop) ≫ NatTrans.app ((yoneda.obj s.pt.unop).mapCone c).π j = Na …
      funext
      -- ⊢ ((fun x => m.unop) ≫ NatTrans.app ((yoneda.obj s.pt.unop).mapCone c).π j) x✝ …
      exact Quiver.Hom.op_inj (w j) }
      -- 🎉 no goals
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
      -- ⊢ (fun x => m) = IsLimit.lift (t (op s.pt)) (s' s)
      apply (t _).uniq (s' s) _ fun j => _
      -- ⊢ ∀ (j : J), (fun x => m) ≫ NatTrans.app ((coyoneda.obj (op s.pt)).mapCone c). …
      intro j
      -- ⊢ (fun x => m) ≫ NatTrans.app ((coyoneda.obj (op s.pt)).mapCone c).π j = NatTr …
      funext
      -- ⊢ ((fun x => m) ≫ NatTrans.app ((coyoneda.obj (op s.pt)).mapCone c).π j) x✝ =  …
      exact w j }
      -- 🎉 no goals
#align category_theory.coyoneda_jointly_reflects_limits CategoryTheory.coyonedaJointlyReflectsLimits

variable {D : Type u} [SmallCategory D]

instance yonedaFunctorPreservesLimits : PreservesLimits (@yoneda D _) := by
  apply preservesLimitsOfEvaluation
  -- ⊢ (k : Dᵒᵖ) → PreservesLimitsOfSize.{u, u, u, u, u, u + 1} (yoneda ⋙ (evaluati …
  intro K
  -- ⊢ PreservesLimitsOfSize.{u, u, u, u, u, u + 1} (yoneda ⋙ (evaluation Dᵒᵖ (Type …
  change PreservesLimits (coyoneda.obj K)
  -- ⊢ PreservesLimits (coyoneda.obj K)
  infer_instance
  -- 🎉 no goals
#align category_theory.yoneda_functor_preserves_limits CategoryTheory.yonedaFunctorPreservesLimits

instance coyonedaFunctorPreservesLimits : PreservesLimits (@coyoneda D _) := by
  apply preservesLimitsOfEvaluation
  -- ⊢ (k : D) → PreservesLimitsOfSize.{u, u, u, u, u, u + 1} (coyoneda ⋙ (evaluati …
  intro K
  -- ⊢ PreservesLimitsOfSize.{u, u, u, u, u, u + 1} (coyoneda ⋙ (evaluation D (Type …
  change PreservesLimits (yoneda.obj K)
  -- ⊢ PreservesLimits (yoneda.obj K)
  infer_instance
  -- 🎉 no goals
#align category_theory.coyoneda_functor_preserves_limits CategoryTheory.coyonedaFunctorPreservesLimits

instance yonedaFunctorReflectsLimits : ReflectsLimits (@yoneda D _) :=
  Limits.fullyFaithfulReflectsLimits _
#align category_theory.yoneda_functor_reflects_limits CategoryTheory.yonedaFunctorReflectsLimits

instance coyonedaFunctorReflectsLimits : ReflectsLimits (@coyoneda D _) :=
  Limits.fullyFaithfulReflectsLimits _
#align category_theory.coyoneda_functor_reflects_limits CategoryTheory.coyonedaFunctorReflectsLimits

end CategoryTheory

assert_not_exists Set.range

-- Porting note: after the port see if this import can be removed
-- assert_not_exists AddCommMonoid
