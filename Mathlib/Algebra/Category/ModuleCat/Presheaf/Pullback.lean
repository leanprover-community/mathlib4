/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint

/-!
# Pullback of presheaves of modules

Let `F : C ⥤ D` be a functor, `R : Dᵒᵖ ⥤ RingCat` and `S : Cᵒᵖ ⥤ RingCat` be presheaves
of rings, and `φ : S ⟶ F.op ⋙ R` be a morphism of presheaves of rings,
we introduce the pullback functor `pullback : PresheafOfModules S ⥤ PresheafOfModules R`
as the left adjoint of `pushforward : PresheafOfModules R ⥤ PresheafOfModules S`.
The existence of this left adjoint functor is obtained under suitable universe assumptions.

-/

universe v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

open CategoryTheory Limits Opposite

namespace PresheafOfModules

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)
  [(pushforward.{v} φ).IsRightAdjoint]

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

/-- Given a morphism of presheaves of rings `φ : S ⟶ F.op ⋙ R`, this is the property
that the (partial) left adjoint functor of `pushforward φ` is defined
on a certain object `M : PresheafOfModules S`. -/
abbrev PullbackObjIsDefined : PresheafOfModules.{v} S → Prop :=
  (pushforward φ).LeftAdjointObjIsDefined

end

section

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

/-- Given a morphism of presheaves of rings `φ : S ⟶ F.op ⋙ R`, where `F : C ⥤ D`,
`S : Cᵒᵖ ⥤ RingCat`, `R : Dᵒᵖ ⥤ RingCat` and `X : C`, the (partial) left adjoint
functor of `pushforward φ` is defined on the object `(free S).obj (yoneda.obj X)`:
this object shall be mapped to `(free R).obj (yoneda.obj (F.obj X))`. -/
noncomputable def pushforwardCompCoyonedaFreeYonedaCorepresentableBy (X : C) :
    (pushforward φ ⋙ coyoneda.obj (op ((free S).obj (yoneda.obj X)))).CorepresentableBy
      ((free R).obj (yoneda.obj (F.obj X))) where
  homEquiv {M} := (freeYonedaEquiv).trans
    (freeYonedaEquiv (M := (pushforward φ).obj M)).symm
  homEquiv_comp {M N} g f := freeYonedaEquiv.injective (by
    dsimp
    erw [Equiv.apply_symm_apply, freeYonedaEquiv_comp]
    conv_rhs => erw [freeYonedaEquiv_comp]
    erw [Equiv.apply_symm_apply]
    rfl)

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

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)
  {G : D ⥤ E} {T : Eᵒᵖ ⥤ RingCat.{u}} (ψ : R ⟶ G.op ⋙ T)

instance : (pushforward.{v} (F := 𝟭 C) (𝟙 S)).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (pushforwardId.{v} S).symm

variable (S) in
noncomputable def pullbackId : pullback.{v} (F := 𝟭 C) (𝟙 S) ≅ 𝟭 _ :=
  ((conjugateIsoEquiv (pullbackPushforwardAdjunction.{v} (F := 𝟭 C) (𝟙 S))
    Adjunction.id).symm (pushforwardId S)).symm

lemma pullbackId_inv_app (M : PresheafOfModules.{v} S) :
    (pullbackId S).inv.app M =
      (pullbackPushforwardAdjunction (F := 𝟭 C) (𝟙 S)).unit.app M ≫
        (pushforwardId S).hom.app ((pullback (F := 𝟭 C) (𝟙 S)).obj M) := rfl

variable [(pushforward.{v} φ).IsRightAdjoint]

section

variable [(pushforward.{v} ψ).IsRightAdjoint]

instance : (pushforward.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ)).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (pushforwardComp.{v} φ ψ).symm

noncomputable def pullbackComp :
    pullback.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ) ≅
      pullback.{v} φ ⋙ pullback.{v} ψ :=
  (conjugateIsoEquiv
    ((pullbackPushforwardAdjunction φ).comp (pullbackPushforwardAdjunction ψ))
    (pullbackPushforwardAdjunction (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ))).symm
      (pushforwardComp φ ψ).symm

@[reassoc]
lemma unit_app_comp_pushforward_map_pullbackComp_hom (M : PresheafOfModules.{v} S) :
    (pullbackPushforwardAdjunction (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ)).unit.app M ≫
        (pushforward _).map ((pullbackComp φ ψ).hom.app M) =
    (pullbackPushforwardAdjunction φ).unit.app M ≫
      (pushforward φ).map ((pullbackPushforwardAdjunction ψ).unit.app _) ≫
        (pushforwardComp φ ψ).inv.app _ := by
  simp [pullbackComp]

variable {T' : E'ᵒᵖ ⥤ RingCat.{u}} {G' : E ⥤ E'} (ψ' : T ⟶ G'.op ⋙ T')
  [(pushforward.{v} ψ').IsRightAdjoint]

lemma pullback_assoc :
    pullbackComp.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ) ψ' ≪≫
      isoWhiskerRight (pullbackComp.{v} φ ψ) _ =
    pullbackComp.{v} (G := G ⋙ G') φ (ψ ≫ whiskerLeft G.op ψ') ≪≫
      isoWhiskerLeft _ (pullbackComp.{v} ψ ψ') ≪≫ (Functor.associator _ _ _).symm := by
  ext M : 3
  apply ((pullbackPushforwardAdjunction _).homEquiv _ _).injective
  dsimp
  conv_lhs =>
    simp only [Functor.map_comp, unit_app_comp_pushforward_map_pullbackComp_hom_assoc,
      CategoryTheory.Functor.map_id, Category.comp_id, ← NatTrans.naturality,
      Functor.comp_obj, Functor.comp_map]
    simp only [← Functor.map_comp_assoc, Adjunction.unit_naturality]
    simp only [Functor.map_comp, Category.assoc,
       unit_app_comp_pushforward_map_pullbackComp_hom_assoc,
      ← (pushforwardComp.{v} φ ψ).inv.naturality_assoc, pushforward_inv_app_assoc]
    dsimp
  conv_rhs =>
    simp only [Functor.map_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  sorry
    --erw [unit_app_comp_pushforward_map_pullbackComp_hom_assoc.{v} (G := G ⋙ G')
    --  φ (ψ ≫ whiskerLeft G.op ψ'), ← NatTrans.naturality]
    --dsimp
    --rw [← Functor.map_comp_assoc, unit_app_comp_pushforward_map_pullbackComp_hom,
    --  Functor.map_comp, Functor.map_comp]
    --simp only [Category.assoc]

end

instance : (pushforward.{v} (F := 𝟭 C ⋙ F) (𝟙 S ≫ whiskerLeft (𝟭 C).op φ)).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (pushforwardComp (F := 𝟭 C) (𝟙 S) φ).symm

instance : (pushforward.{v} (F := F ⋙ 𝟭 D) (φ ≫ whiskerLeft F.op (𝟙 R))).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (pushforwardComp (G := 𝟭 D) φ (𝟙 R)).symm

lemma pullback_id_comp :
    pullbackComp.{v} (F := 𝟭 C) (𝟙 S) φ =
      (Functor.leftUnitor _).symm ≪≫ isoWhiskerRight (pullbackId S).symm _ := by
  ext M : 3
  apply ((pullbackPushforwardAdjunction _).homEquiv _ _).injective
  dsimp
  sorry
  --erw [unit_app_comp_pushforward_map_pullbackComp_hom]
  --simp [pushforward_id_comp, pullbackId_inv_app]
  --rfl

lemma pullback_comp_id :
    pullbackComp.{v} (G := 𝟭 _) φ (𝟙 R) =
      (Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft _ (pullbackId R).symm := by
  ext M : 3
  apply ((pullbackPushforwardAdjunction _).homEquiv _ _).injective
  dsimp [pullbackId_inv_app]
  sorry
  --erw [unit_app_comp_pushforward_map_pullbackComp_hom (G := 𝟭 _) φ (𝟙 R)]
  --simp
  --rfl

end

end PresheafOfModules
