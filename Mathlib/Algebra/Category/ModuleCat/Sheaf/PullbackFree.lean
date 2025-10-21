/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Final.Type

/-!
# Pullbacks of free sheaves of modules

Let `S` (resp.`R`) be a sheaf of rings on a category `C` (resp. `D`)
equipped with a Grothendieck topology `J` (resp. `K`).
Let `F : C ⥤ D` be a continuous functor.
Let `φ` be a morphism from `S` to the direct image of `R`.

We introduce `unitToPushforwardObjUnit φ` which is the morphism
in the category `SheafOfModules S` which corresponds to `φ`, and
show that the adjoint morphism
`pullbackObjUnitToUnit φ : (pullback.{u} φ).obj (unit S) ⟶ unit R`
is an isomorphism when `F` is a final functor.
More generally, the functor `pullback φ` sends the free sheaf
of modules `free I` to `free I`, see `pullbackObjFreeIso` and
`freeFunctorCompPullbackIso`.
-/

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous.{u} F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- The canonical map from the (global) sections of a sheaf of modules
to the (global) sections of its pushforward. -/
@[simps]
def pushforwardSections [Functor.IsContinuous.{v} F J K]
    {M : SheafOfModules.{v} R} (s : M.sections) :
    ((pushforward φ).obj M).sections where
  val _ := s.val _
  property _ := s.property _

variable (M) in
lemma bijective_pushforwardSections [Functor.IsContinuous.{v} F J K] [F.Final] :
    Function.Bijective (pushforwardSections φ (M := M)) :=
  Functor.bijective_sectionsPrecomp _ _

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- The canonical morphism `unit S ⟶ (pushforward.{u} φ).obj (unit R)`
of sheaves of modules corresponding to a continuous map between ringed sites. -/
def unitToPushforwardObjUnit : unit S ⟶ (pushforward.{u} φ).obj (unit R) where
  val.app X := ModuleCat.homMk ((forget₂ RingCat AddCommGrpCat).map (φ.val.app X)) (fun r ↦ by
    ext m
    exact ((φ.val.app X).hom.map_mul _ _).symm)
  val.naturality f := by
    ext
    exact ConcreteCategory.congr_hom (φ.val.naturality f) _

lemma unitToPushforwardObjUnit_val_app_apply {X : Cᵒᵖ} (a : S.val.obj X) :
    (unitToPushforwardObjUnit φ).val.app X a = φ.val.app X a := rfl

lemma pushforwardSections_unitHomEquiv
    {M : SheafOfModules.{u} R} (f : unit R ⟶ M) :
    pushforwardSections φ (M.unitHomEquiv f) =
      ((pushforward φ).obj M).unitHomEquiv
        (unitToPushforwardObjUnit φ ≫ (pushforward φ).map f) := by
  ext X
  have := unitToPushforwardObjUnit_val_app_apply φ (X := X) 1
  dsimp at this ⊢
  simp [this, map_one]
  rfl

variable [(pushforward.{u} φ).IsRightAdjoint]

/-- The canonical morphism `(pullback.{u} φ).obj (unit S) ⟶ unit R`
of sheaves of modules corresponding to a continuous map between ringed sites. -/
noncomputable def pullbackObjUnitToUnit :
    (pullback.{u} φ).obj (unit S) ⟶ unit R :=
  ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).symm (unitToPushforwardObjUnit φ)

@[simp]
lemma pullbackPushforwardAdjunction_homEquiv_symm_unitToPushforwardObjUnit :
    ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).symm (unitToPushforwardObjUnit φ) =
      pullbackObjUnitToUnit φ := rfl

@[simp]
lemma pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit :
    (pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ (pullbackObjUnitToUnit φ) =
      unitToPushforwardObjUnit φ :=
  Equiv.apply_symm_apply _ _

instance [F.Final] : IsIso (pullbackObjUnitToUnit φ) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).bijective.of_comp_iff',
    ← (unitHomEquiv _).bijective.of_comp_iff']
  convert (bijective_pushforwardSections φ M).comp (unitHomEquiv _).bijective
  ext f : 1
  dsimp
  rw [pushforwardSections_unitHomEquiv, EmbeddingLike.apply_eq_iff_eq,
    Adjunction.homEquiv_naturality_right,
    pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]

variable [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [F.Final]

/-- The pullback of a free sheaf of modules is a free sheaf of modules. -/
noncomputable def pullbackObjFreeIso (I : Type u) :
    (pullback φ).obj (free I) ≅ free I :=
  (asIso (sigmaComparison _ _)).symm ≪≫
    Sigma.mapIso (fun _ ↦ asIso (pullbackObjUnitToUnit φ))

@[reassoc (attr := simp)]
lemma pullback_map_ιFree_comp_pullbackObjFreeIso_hom {I : Type u} (i : I) :
    (pullback φ).map (ιFree i) ≫ (pullbackObjFreeIso φ I).hom =
      pullbackObjUnitToUnit φ ≫ ιFree i := by
  simp [pullbackObjFreeIso, ιFree]

@[reassoc (attr := simp)]
lemma pullbackObjFreeIso_hom_naturality {I J : Type u} (f : I → J) :
    (pullback φ).map (freeMap f) ≫ (pullbackObjFreeIso φ J).hom =
      (pullbackObjFreeIso φ I).hom ≫ freeMap f :=
  Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (pullback φ) _ _
    (isColimitFreeCofan (R := S) I)) _ _ (fun i ↦ by simp [← Functor.map_comp_assoc])

/-- The canonical isomorphism `freeFunctor ⋙ pullback φ ≅ freeFunctor` for a
continuous map between ringed sites, when the underlying functor between the sites
is final. -/
noncomputable def freeFunctorCompPullbackIso : freeFunctor ⋙ pullback φ ≅ freeFunctor :=
  NatIso.ofComponents (pullbackObjFreeIso φ)

end SheafOfModules
