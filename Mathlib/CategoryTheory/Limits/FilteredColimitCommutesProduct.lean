/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Filtered
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# The IPC property

Given a family of categories `I i` (`i : α`) and a family of functors `F i : I i ⥤ C`, we consider
the diagram `pointwiseProduct F : Π i, I i ⥤ C` defined by `(Xᵢ)ᵢ ↦ ∏ᶜ Xᵢ`. Given a cocone
`cᵢ` on `Fᵢ` for each `i`, there is a natural cocone on `pointwiseProduct F` with point `∏ᶜ cᵢ`.

Similarly to the study of finite limits commuting with filtered colimits, we then study sufficient
conditions for this cocone to be colimiting if all the `cᵢ` are colimiting. We say that `C`
satisfies the `w`-IPC property if the morphism is an isomorphism as long as `α` is `w`-small and
`I i` is `w`-small and filtered for all `i`.

## Main definitions

- `CategoryTheory.Limits.IsIPCOfShape`: `C` satisfies `w`-IPC of shape `α` if `w`-sized filtered
  colimits commute products of shape `α`, i.e. if the joint cocone from above is colimiting if the
  components are.
- `CategoryTheory.Limits.IsIPC`: `C` satisfies the `w`-IPC property if it satisfies `w`-IPC for
  every `α : Type w`.

## Main results

- The category `Type u` satisfies the `u`-IPC property (available by `inferInstance`).
- If `C` satisfies the `w`-IPC property, then `D ⥤ C` satisfies the `w`-IPC property
  (available by `inferInstance`).

These results will be used to show that if a category `C` has products indexed by `α`, then so
does the category of Ind-objects of `C`.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], 3.1.10, 3.1.11, 3.1.12.
-/

@[expose] public section

universe w v v₁ v₂ u u₁ u₂

namespace CategoryTheory.Limits

open ConcreteCategory

section

variable {C : Type u} [Category.{v} C] {α : Type*} {I : α → Type*} [∀ i, Category* (I i)]
  [HasProductsOfShape α C] (F : ∀ i, I i ⥤ C)

/-- Given a family of functors `I i ⥤ C` for `i : α`, we obtain a functor `(∀ i, I i) ⥤ C` which
maps `k : ∀ i, I i` to `∏ᶜ fun (s : α) => (F s).obj (k s)`. -/
noncomputable abbrev pointwiseProduct : (∀ i, I i) ⥤ C :=
  Functor.pi F ⋙ Pi.functor α

attribute [local simp] Functor.pi in
/-- `pointwiseProduct` is invariant under re-indexing. -/
@[simps!]
noncomputable
def Pi.equivalenceOfEquivCompPointwiseProduct {β : Type*} (f : β ≃ α) [HasProductsOfShape β C] :
    (Pi.equivalenceOfEquiv I f).inverse ⋙ pointwiseProduct (fun i ↦ F (f i)) ≅
      pointwiseProduct F :=
  (NatIso.ofComponents
    (fun a ↦ (Pi.whiskerEquiv f (fun j ↦ (Iso.refl ((F (f j)).obj <| a (f j))))).symm)).symm

variable {F} in
/-- The inclusions `(F s).obj (k s) ⟶ colimit (F s)` induce a cocone on `pointwiseProduct F` with
cone point `∏ᶜ (fun s : α) => colimit (F s)`. -/
@[simps]
noncomputable def coconePointwiseProduct (c : ∀ i, Cocone (F i)) :
    Cocone (pointwiseProduct F) where
  pt := ∏ᶜ fun i ↦ (c i).pt
  ι := Functor.whiskerRight (NatTrans.pi fun i ↦ (c i).ι) _ ≫ (Pi.constCompPiIsoConst _).hom

/-- `coconePointwiseProduct` is invariant under isomorphisms of cocones. -/
noncomputable def coconePointwiseProductIso {c c' : ∀ i, Cocone (F i)} (e : ∀ i, c i ≅ c' i) :
    coconePointwiseProduct c ≅ coconePointwiseProduct c' :=
  Cocone.ext (Pi.mapIso fun i ↦ (Cocone.forget _).mapIso (e i)) fun i ↦ by
    dsimp
    ext
    simp [Functor.pi]

/-- The natural morphism `colim_k (∏ᶜ s ↦ (F s).obj (k s)) ⟶ ∏ᶜ s ↦ colim_k (F s).obj (k s)`.
A category has the `IPC` property of shape `α` if this morphism is an isomorphism as long
as the indexing categories are filtered. -/
noncomputable def colimitPointwiseProductToProductColimit [∀ i, HasColimit (F i)]
    [HasColimit (Functor.pi F ⋙ Pi.functor α)] :
    colimit (pointwiseProduct F) ⟶ ∏ᶜ fun (s : α) => colimit (F s) :=
  colimit.desc _ (coconePointwiseProduct _)

variable [∀ i, HasColimit (F i)] [HasColimit (pointwiseProduct F)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ι_colimitPointwiseProductToProductColimit_π (k : ∀ i, I i) (s : α) :
    colimit.ι (pointwiseProduct F) k ≫
      colimitPointwiseProductToProductColimit F ≫ Pi.π _ s =
      Pi.π _ s ≫ colimit.ι (F s) (k s) := by
  simp [colimitPointwiseProductToProductColimit, Functor.pi, Pi.functor]

end

section functorCategory

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  {α : Type*} {I : α → Type*} [∀ i, Category (I i)]
  [HasLimitsOfShape (Discrete α) C]
  (F : ∀ i, I i ⥤ D ⥤ C)

/-- Evaluating the pointwise product `k ↦ ∏ᶜ fun (s : α) => (F s).obj (k s)` at `d` is the same as
taking the pointwise product `k ↦ ∏ᶜ fun (s : α) => ((F s).obj (k s)).obj d`. -/
@[simps!]
noncomputable def pointwiseProductCompEvaluation (d : D) :
    pointwiseProduct F ⋙ (evaluation D C).obj d ≅
      pointwiseProduct (fun s => F s ⋙ (evaluation _ _).obj d) :=
  NatIso.ofComponents (fun k => piObjIso _ _)
    (fun f => Pi.hom_ext _ _ (by simp [Functor.pi, ← NatTrans.comp_app]))

/-- In a functor category, `coconePointwiseProduct` commutes with evaluation. -/
noncomputable def evaluationCoconePointwiseProductIso (X : D) (c : ∀ i, Cocone (F i)) :
    ((evaluation D C).obj X).mapCocone (coconePointwiseProduct c) ≅
      (Cocone.precompose <| (pointwiseProductCompEvaluation F X).hom).obj
        (coconePointwiseProduct fun i ↦ ((evaluation D C).obj X).mapCocone (c i)) :=
  Cocone.ext (piObjIso (fun i ↦ (c i).pt) X) fun j ↦ by
    dsimp
    ext
    simp [Functor.pi, NatTrans.pi, ← NatTrans.comp_app]

variable [∀ i, HasColimitsOfShape (I i) C] [HasColimitsOfShape (∀ i, I i) C]

set_option backward.isDefEq.respectTransparency false in
theorem colimitPointwiseProductToProductColimit_app (d : D) :
    (colimitPointwiseProductToProductColimit F).app d =
      (colimitObjIsoColimitCompEvaluation _ _).hom ≫
        (HasColimit.isoOfNatIso (pointwiseProductCompEvaluation F d)).hom ≫
          colimitPointwiseProductToProductColimit _ ≫
            (Pi.mapIso fun _ => (colimitObjIsoColimitCompEvaluation _ _).symm).hom ≫
              (piObjIso _ _).inv := by
  rw [← Iso.inv_comp_eq]
  simp only [← Category.assoc]
  rw [Iso.eq_comp_inv]
  refine Pi.hom_ext _ _ (fun s => colimit.hom_ext (fun k => ?_))
  simp [← NatTrans.comp_app, Functor.pi]

end functorCategory

section

variable {C : Type*} [Category* C]
variable {ι : Type*} [HasProductsOfShape ι C]

/-- A category `C` has the `w`-IPC property for shape `ι` if `w`-sized filtered colimits commute
with products of shape `ι`. -/
class IsIPCOfShape (ι : Type*) (C : Type*) [Category* C] [HasProductsOfShape ι C] : Prop where
  nonempty_isColimit ⦃J : ι → Type w⦄ [∀ i, SmallCategory (J i)]
    [∀ i, IsFiltered (J i)] ⦃F : ∀ i, J i ⥤ C⦄ ⦃c : ∀ i, Cocone (F i)⦄ :
    (∀ i, IsColimit (c i)) → Nonempty (IsColimit (coconePointwiseProduct c))

instance [IsIPCOfShape.{w} ι C] {J : ι → Type w} [∀ i, SmallCategory (J i)]
    [∀ i, IsFiltered (J i)] (F : ∀ i, J i ⥤ C)
    [∀ i, HasColimit (F i)] [HasColimit (pointwiseProduct F)] :
    IsIso (colimitPointwiseProductToProductColimit F) := by
  rw [colimitPointwiseProductToProductColimit, colimit.desc]
  refine ((colimit.isColimit (pointwiseProduct F)).nonempty_isColimit_iff_isIso_desc).mp ?_
  exact IsIPCOfShape.nonempty_isColimit fun i ↦ colimit.isColimit _

lemma IsIPCOfShape.of_forall_exists
    (H : ∀ ⦃J : ι → Type w⦄ [∀ i, SmallCategory (J i)]
      [∀ i, IsFiltered (J i)] (F : ∀ i, J i ⥤ C) [∀ i, HasColimit (F i)], ∃ (c : ∀ i, Cocone (F i))
      (_ : ∀ i, IsColimit (c i)), Nonempty (IsColimit (coconePointwiseProduct c))) :
    IsIPCOfShape.{w} ι C where
  nonempty_isColimit J _ _ F c hc := by
    have (i : ι) : HasColimit (F i) := ⟨_, hc i⟩
    obtain ⟨c', hc', _⟩ := H F
    let e : coconePointwiseProduct c ≅ coconePointwiseProduct c' :=
      coconePointwiseProductIso _ fun i ↦ (hc i).uniqueUpToIso (hc' i)
    rwa [(IsColimit.equivIsoColimit e).nonempty_congr]

lemma IsIPCOfShape.of_isIso
    (H : ∀ (J : ι → Type w) [∀ i, SmallCategory (J i)] [∀ i, IsFiltered (J i)]
      (F : ∀ i, J i ⥤ C) [∀ (i : ι), HasColimit (F i)],
      ∃ (_ : HasColimit (pointwiseProduct F)),
        IsIso (colimitPointwiseProductToProductColimit F)) :
    IsIPCOfShape.{w} ι C := by
  refine .of_forall_exists fun J _ _ F _ ↦ ?_
  refine ⟨fun i ↦ colimit.cocone _, fun i ↦ colimit.isColimit _, ?_⟩
  obtain ⟨_, h⟩ := H J F
  rwa [IsColimit.nonempty_isColimit_iff_isIso_desc (colimit.isColimit _)]

attribute [local simp] Functor.pi in
lemma IsIPCOfShape.of_equiv {ι' : Type*} [HasProductsOfShape ι' C] [IsIPCOfShape.{w} ι C]
    (e : ι ≃ ι') :
    IsIPCOfShape.{w} ι' C where
  nonempty_isColimit J _ _ F c hc := by
    obtain ⟨h⟩ := nonempty_isColimit fun i : ι ↦ hc (e i)
    constructor
    apply IsColimit.equivOfNatIsoOfIso _ _ _ _ <|
        h.whiskerEquivalence (Pi.equivalenceOfEquiv J e).symm
    · exact (Pi.equivalenceOfEquivCompPointwiseProduct F e)
    · -- Without the double `symm`, one runs into DTT hell
      exact (Cocone.ext (Pi.whiskerEquiv e fun _ ↦ Iso.refl _).symm).symm

variable (C) in
/-- A category `C` has the `w`-IPC property it satisfies the IPC-property for every `ι : Type w`. -/
class IsIPC [HasProducts.{w} C] [HasFilteredColimitsOfSize.{w} C] : Prop where
  isIPCOfShape (ι : Type w) : IsIPCOfShape.{w} ι C := by infer_instance

instance [HasProducts.{w} C] [HasFilteredColimitsOfSize.{w, w} C] [IsIPC.{w} C] (ι : Type*)
    [Small.{w} ι] [HasProductsOfShape ι C] :
    IsIPCOfShape.{w} ι C := by
  suffices IsIPCOfShape (Shrink.{w} ι) C from .of_equiv (equivShrink ι).symm
  apply IsIPC.isIPCOfShape

end

section types

variable {α : Type u} {I : α → Type u} [∀ i, SmallCategory (I i)] [∀ i, IsFiltered (I i)]

set_option backward.isDefEq.respectTransparency false in
theorem Types.isIso_colimitPointwiseProductToProductColimit (F : ∀ i, I i ⥤ Type u) :
    IsIso (colimitPointwiseProductToProductColimit F) := by
  -- We follow the proof in [Kashiwara2006], Prop. 3.1.11(ii)
  refine (isIso_iff_bijective _).2 ⟨fun y y' hy => ?_, fun x => ?_⟩
  · obtain ⟨ky, yk₀, hyk₀⟩ := Types.jointly_surjective' y
    obtain ⟨ky', yk₀', hyk₀'⟩ := Types.jointly_surjective' y'
    let k := IsFiltered.max ky ky'
    let yk : (pointwiseProduct F).obj k :=
      (pointwiseProduct F).map (IsFiltered.leftToMax ky ky') yk₀
    let yk' : (pointwiseProduct F).obj k :=
      (pointwiseProduct F).map (IsFiltered.rightToMax ky ky') yk₀'
    obtain rfl : y = colimit.ι (pointwiseProduct F) k yk := by
      simp only [k, yk, colimit.w_apply, hyk₀]
    obtain rfl : y' = colimit.ι (pointwiseProduct F) k yk' := by
      simp only [k, yk', colimit.w_apply, hyk₀']
    dsimp at yk yk'
    have hch : ∀ (s : α), ∃ (i' : I s) (hi' : k s ⟶ i'),
        (F s).map hi' (Pi.π (fun s => (F s).obj (k s)) s yk) =
          (F s).map hi' (Pi.π (fun s => (F s).obj (k s)) s yk') := by
      intro s
      have hy₁ := congr_hom (ι_colimitPointwiseProductToProductColimit_π F k s) yk
      have hy₂ := congr_hom (ι_colimitPointwiseProductToProductColimit_π F k s) yk'
      dsimp at hy₁ hy₂ hy
      rw [← hy, hy₁, Types.FilteredColimit.colimit_eq_iff] at hy₂
      obtain ⟨i₀, f₀, g₀, h₀⟩ := hy₂
      refine ⟨IsFiltered.coeq f₀ g₀, f₀ ≫ IsFiltered.coeqHom f₀ g₀, ?_⟩
      conv_rhs => rw [IsFiltered.coeq_condition]
      dsimp [Functor.pi] at h₀
      simp [h₀]
    choose k' f hk' using hch
    apply Types.colimit_sound' f f
    exact Types.limit_ext' _ _ _ (fun ⟨s⟩ => by simpa [Functor.pi, Pi.map_π_apply] using hk' s)
  · have hch : ∀ (s : α), ∃ (i : I s) (xi : (F s).obj i), colimit.ι (F s) i xi =
        Pi.π (fun s => colimit (F s)) s x := fun s => Types.jointly_surjective' _
    choose k p hk using hch
    refine ⟨colimit.ι (pointwiseProduct F) k ((Types.productIso _).inv p), ?_⟩
    refine Types.limit_ext' _ _ _ (fun ⟨s⟩ => ?_)
    have := congr_hom (ι_colimitPointwiseProductToProductColimit_π F k s)
      ((Types.productIso _).inv p)
    exact this.trans (by simpa [Functor.pi] using hk _)

instance : IsIPC.{u} (Type u) where
  isIPCOfShape _ :=
    .of_isIso fun _ _ _ _ _ ↦ ⟨inferInstance, Types.isIso_colimitPointwiseProductToProductColimit _⟩

end types

section functorCategory

variable {C : Type u} [Category.{v} C]

instance (ι : Type*) [HasProductsOfShape ι C] [IsIPCOfShape.{w} ι C]
    [HasFilteredColimitsOfSize.{w, w} C] {D : Type u₁}
    [Category.{v₁} D] : IsIPCOfShape.{w} ι (D ⥤ C) where
  nonempty_isColimit J _ _ F c hc := by
    refine ⟨evaluationJointlyReflectsColimits _ fun X ↦ ?_⟩
    exact IsColimit.equivOfNatIsoOfIso (pointwiseProductCompEvaluation F X).symm _ _
      (evaluationCoconePointwiseProductIso F X c).symm
      (IsIPCOfShape.nonempty_isColimit fun i ↦ isColimitOfPreserves _ (hc i)).some

instance [HasProducts.{w} C] [HasFilteredColimitsOfSize.{w, w} C] [IsIPC.{w} C] {D : Type u₁}
    [Category.{v₁} D] : IsIPC.{w} (D ⥤ C) where

end functorCategory

end CategoryTheory.Limits
