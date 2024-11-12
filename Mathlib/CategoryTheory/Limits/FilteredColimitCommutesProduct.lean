/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.TypesFiltered
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Limits.FunctorCategory.Filtered

/-!
# The IPC property

Given a family of categories `I i` (`i : α`) and a family of functors `F i : I i ⥤ C`, we construct
the natural morphism `colim_k (∏ᶜ s ↦ (F s).obj (k s)) ⟶ ∏ᶜ s ↦ colim_k (F s).obj (k s)`.

Similarly to the study of finite limits commuting with filtered colimits, we then study sufficient
conditions for this morphism to be an isomorphism.

Our final goal is that for a small category `D` the presheaf category `Dᵒᵖ ⥤ Type v` satisfies the
IPC property, which is used in the calculation of products in the category of Ind-objects.
-/

universe w v v₁ v₂ u u₁ u₂

namespace CategoryTheory.Limits

section

variable {C : Type u} [Category.{v} C] {α : Type w} {I : α → Type u₁} [∀ i, Category.{v₁} (I i)]
  [HasLimitsOfShape (Discrete α) C]
  (F : ∀ i, I i ⥤ C)

/-- Given a family of functors `I i ⥤ C` for `i : α`, we obtain a functor `(∀ i, I i) ⥤ C` which
maps `k : ∀ i, I i` to `∏ᶜ fun (s : α) => (F s).obj (k s)`. -/
@[simps]
noncomputable def pointwiseProduct : (∀ i, I i) ⥤ C where
  obj k := ∏ᶜ fun (s : α) => (F s).obj (k s)
  map f := Pi.map (fun s => (F s).map (f s))

variable [∀ i, HasColimitsOfShape (I i) C] [HasColimitsOfShape (∀ i, I i) C]

/-- The inclusions `(F s).obj (k s) ⟶ colimit (F s)` induce a cocone on `pointwiseProduct F` with
cone point `∏ᶜ (fun s : α) => colimit (F s)`. -/
@[simps]
noncomputable def coconePointwiseProduct : Cocone (pointwiseProduct F) where
  pt := ∏ᶜ fun (s : α) => colimit (F s)
  ι := { app := fun k => Pi.map fun s => colimit.ι _ _ }

/-- The natural morphism `colim_k (∏ᶜ s ↦ (F s).obj (k s)) ⟶ ∏ᶜ s ↦ colim_k (F s).obj (k s)`.
We will say that a category has the `IPC` property if this morphism is an isomorphism as long
as the indexing categories are filtered. -/
noncomputable def colimitPointwiseProductToProductColimit :
    colimit (pointwiseProduct F) ⟶ ∏ᶜ fun (s : α) => colimit (F s) :=
  colimit.desc (pointwiseProduct F) (coconePointwiseProduct F)

@[reassoc (attr := simp)]
theorem ι_colimitPointwiseProductToProductColimit_π (k : ∀ i, I i) (s : α) :
    colimit.ι (pointwiseProduct F) k ≫ colimitPointwiseProductToProductColimit F ≫ Pi.π _ s =
      Pi.π _ s ≫ colimit.ι (F s) (k s) := by
  simp [colimitPointwiseProductToProductColimit]

end

section FME157

variable {α : Type w} {I : α → Type u₁} [∀ i, Category.{v₁} (I i)]

instance [∀ i, IsFilteredOrEmpty (I i)] : IsFilteredOrEmpty (∀ i, I i) where
  cocone_objs k l := ⟨fun s => IsFiltered.max (k s) (l s),
    fun s => IsFiltered.leftToMax (k s) (l s), fun s => IsFiltered.rightToMax (k s) (l s), trivial⟩
  cocone_maps k l f g := ⟨fun s => IsFiltered.coeq (f s) (g s),
    fun s => IsFiltered.coeqHom (f s) (g s),
    funext fun s => by simp [IsFiltered.coeq_condition (f s) (g s)]⟩

attribute [local instance] IsFiltered.nonempty

instance [∀ i, IsFiltered (I i)] : IsFiltered (∀ i, I i) where

end FME157

section

variable (C : Type u) [Category.{v} C]

class IsIPC [HasProducts.{w} C] [HasFilteredColimitsOfSize.{w} C] : Prop where
  isIso : ∀ (α : Type w) (I : α → Type w) [∀ i, SmallCategory (I i)] [∀ i, IsFiltered (I i)]
    (F : ∀ i, I i ⥤ C), IsIso (colimitPointwiseProductToProductColimit F)

end

section types

variable {α : Type u} {I : α → Type u} [∀ i, SmallCategory (I i)] [∀ i, IsFiltered (I i)]

theorem isIso_colimitPointwiseProductToProductColimit_types (F : ∀ i, I i ⥤ Type u) :
    IsIso (colimitPointwiseProductToProductColimit F) := by
  refine (isIso_iff_bijective _).2 ⟨fun y y' hy => ?_, fun x => ?_⟩
  · obtain ⟨ky, yk₀, hyk₀⟩ := Types.jointly_surjective' y
    obtain ⟨ky', yk₀', hyk₀'⟩ := Types.jointly_surjective' y'
    let k := IsFiltered.max ky ky'
    let yk : (pointwiseProduct F).obj k :=
      (pointwiseProduct F).map (IsFiltered.leftToMax ky ky') yk₀
    let yk' : (pointwiseProduct F).obj k :=
      (pointwiseProduct F).map (IsFiltered.rightToMax ky ky') yk₀'
    obtain rfl : y = colimit.ι (pointwiseProduct F) k yk := by
      simp only [yk, Types.Colimit.w_apply', hyk₀]
    obtain rfl : y' = colimit.ι (pointwiseProduct F) k yk' := by
      simp only [yk', Types.Colimit.w_apply', hyk₀']
    dsimp at yk
    dsimp at yk'
    have hch : ∀ (s : α), ∃ (i' : I s) (hi' : k s ⟶ i'),
        (F s).map hi' (Pi.π (fun s => (F s).obj (k s)) s yk) =
          (F s).map hi' (Pi.π (fun s => (F s).obj (k s)) s yk') := by
      intro s
      have hy₁ := congrFun (ι_colimitPointwiseProductToProductColimit_π F k s) yk
      have hy₂ := congrFun (ι_colimitPointwiseProductToProductColimit_π F k s) yk'
      dsimp at hy₁ hy₂
      rw [← hy, hy₁, Types.FilteredColimit.colimit_eq_iff] at hy₂
      obtain ⟨i₀, f₀, g₀, h₀⟩ := hy₂
      refine ⟨IsFiltered.coeq f₀ g₀, f₀ ≫ IsFiltered.coeqHom f₀ g₀, ?_⟩
      conv_rhs => rw [IsFiltered.coeq_condition]
      simp [h₀]
    choose k' f hk' using hch
    apply Types.colimit_sound' f f
    exact Types.limit_ext' _ _ _ (fun ⟨s⟩ => by simpa using hk' _)
  · have hch : ∀ (s : α), ∃ (i : I s) (xi : (F s).obj i), colimit.ι (F s) i xi =
        Pi.π (fun s => colimit (F s)) s x := fun s => Types.jointly_surjective' _
    choose k p hk using hch
    refine ⟨colimit.ι (pointwiseProduct F) k ((Types.productIso _).inv p), ?_⟩
    refine Types.limit_ext' _ _ _ (fun ⟨s⟩ => ?_)
    have := congrFun (ι_colimitPointwiseProductToProductColimit_π F k s)
      ((Types.productIso _).inv p)
    dsimp at this
    refine this.trans ?_
    simpa using hk _

instance : IsIPC.{u} (Type u) where
  isIso _ _ := isIso_colimitPointwiseProductToProductColimit_types

end types

section functorCategory

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
  {α : Type w} [HasLimitsOfShape (Discrete α) C]

noncomputable def piObjIso (f : α → D ⥤ C) (d : D) : (∏ᶜ f).obj d ≅ ∏ᶜ (fun s => (f s).obj d) :=
  limitObjIsoLimitCompEvaluation (Discrete.functor f) d ≪≫
    HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete _ _)

@[reassoc (attr := simp)]
theorem piObjIso_comp_π (f : α → D ⥤ C) (d : D) (s : α) :
    (piObjIso f d).hom ≫ Pi.π (fun s => (f s).obj d) s = (Pi.π f s).app d := by
  simp [piObjIso]

end functorCategory

section functorCategory

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
  {α : Type w} {I : α → Type u₂} [∀ i, Category (I i)]
  [HasLimitsOfShape (Discrete α) C]
  (F : ∀ i, I i ⥤ D ⥤ C)

@[simps!]
noncomputable def pointwiseProductCompEvaluation (d : D) :
    pointwiseProduct F ⋙ (evaluation D C).obj d ≅
      pointwiseProduct (fun s => F s ⋙ (evaluation _ _).obj d) :=
  NatIso.ofComponents (fun k => piObjIso _ _) (by
    intro k k' f
    simp
    ext
    simp
    rw [← NatTrans.comp_app]
    simp)

variable [∀ i, HasColimitsOfShape (I i) C] [HasColimitsOfShape (∀ i, I i) C]

theorem colimitPointwiseProductToProductColimit_app (d : D) :
    (colimitPointwiseProductToProductColimit F).app d =
      (colimitObjIsoColimitCompEvaluation _ _).hom ≫
        (HasColimit.isoOfNatIso (pointwiseProductCompEvaluation F d)).hom ≫
          (colimitPointwiseProductToProductColimit _) ≫
            (Pi.mapIso fun _ => (colimitObjIsoColimitCompEvaluation _ _).symm).hom ≫
            (piObjIso _ _).inv
            := by
  simp only [← Category.assoc]
  rw [Iso.eq_comp_inv]
  simp only [Category.assoc]
  rw [← Iso.inv_comp_eq]
  refine Pi.hom_ext _ _ (fun s => ?_)
  refine colimit.hom_ext (fun k => ?_)
  simp only [Functor.comp_obj, pointwiseProduct_obj, evaluation_obj_obj, Category.assoc,
    piObjIso_comp_π, colimitObjIsoColimitCompEvaluation_ι_inv_assoc, Functor.mapIso_hom, lim_map,
    limMap_π, Discrete.functor_obj_eq_as, Discrete.natIso_hom_app, Iso.symm_hom,
    HasColimit.isoOfNatIso_ι_hom_assoc, pointwiseProductCompEvaluation_hom_app,
    ι_colimitPointwiseProductToProductColimit_π_assoc, colimitObjIsoColimitCompEvaluation_ι_inv,
    piObjIso_comp_π_assoc]
  simp [← NatTrans.comp_app]

end functorCategory

section discrete

variable {C : Type u} [Category.{v} C]

instance [HasProducts.{w} C] [HasFilteredColimitsOfSize.{w, w} C] [IsIPC.{w} C] {D : Type u₁}
    [Category.{v₁} D] : IsIPC.{w} (D ⥤ C) := by
  refine ⟨fun β I _ _ F => ?_⟩
  suffices ∀ (X : D), IsIso ((colimitPointwiseProductToProductColimit F).app X) from
    NatIso.isIso_of_isIso_app _
  rintro x
  rw [colimitPointwiseProductToProductColimit_app]
  have := IsIPC.isIso _ _ (fun s => F s ⋙ (evaluation D C).obj x)
  exact inferInstance

end discrete

section final

theorem isIso_colimitPointwiseProductToProductColimit {C : Type u} [Category.{v} C]
    {α : Type v} {I : α → Type v} [∀ i, Category.{v} (I i)]
    [∀ i, IsFiltered (I i)] (F : ∀ i, I i ⥤ Cᵒᵖ ⥤ Type v) :
    IsIso (colimitPointwiseProductToProductColimit F) :=
  IsIPC.isIso _ _ F


end final

end CategoryTheory.Limits
