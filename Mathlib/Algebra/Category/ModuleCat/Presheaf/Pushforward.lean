/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings

/-!
# Pushforward of presheaves of modules

If `F : C ⥤ D`, the precomposition `F.op ⋙ _` induces a functor from presheaves
over `D` to presheaves over `C`. When `R : Dᵒᵖ ⥤ RingCat`, we define the
induced functor `pushforward₀ : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} (F.op ⋙ R)`
on presheaves of modules.

In case we have a morphism of presheaves of rings `S ⟶ F.op ⋙ R`, we also construct
a functor `pushforward : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} S`, and
we show that they interact with the composition of morphisms similarly as pseudofunctors.

-/

@[expose] public section

universe v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

open CategoryTheory Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

namespace PresheafOfModules

variable (F : C ⥤ D)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `pushforward₀`. -/
@[simps]
def pushforward₀Obj (R : Dᵒᵖ ⥤ RingCat.{u}) (M : PresheafOfModules R) :
    PresheafOfModules (F.op ⋙ R) :=
  { obj X := ↧(M.obj (F.op.obj X))
    map {X Y} f := M.map (F.op.map f)
    map_id X := by
      refine ModuleCat.hom_ext
        -- Work around an instance diamond for `restrictScalarsId'`
        (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
      exact (M.congr_map_apply (F.op.map_id X) x).trans (by simp)
    map_comp := fun f g ↦ by
      refine ModuleCat.hom_ext
        -- Work around an instance diamond for `restrictScalarsId'`
        (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
      exact (M.congr_map_apply (F.op.map_comp f g) x).trans (by simp) }

@[deprecated (since := "2026-04-27")] alias pushforward₀_obj := pushforward₀Obj

set_option backward.isDefEq.respectTransparency false in
/-- The pushforward functor on presheaves of modules for a functor `F : C ⥤ D` and
`R : Dᵒᵖ ⥤ RingCat`. On the underlying presheaves of abelian groups, it is induced
by the precomposition with `F.op`. -/
def pushforward₀ (R : Dᵒᵖ ⥤ RingCat.{u}) :
    PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} (F.op ⋙ R) where
  obj M := pushforward₀Obj F R M
  map {M₁ M₂} φ := { app X := φ.app _ }

/-- If `F : C ⥤ D` if a functor and `R : Dᵒᵖ ⥤ CommRingCat` is a presheaf
of commutative rings, this is the pushforward functor from the category
of presheaves of modules on `R` to the category of presheaves of
modules on `F.op ⋙ R`. -/
abbrev pushforward₀OfCommRingCat (R : Dᵒᵖ ⥤ CommRingCat.{u}) :
    PresheafOfModules.{v} (R ⋙ forget₂ _ _) ⥤
      PresheafOfModules.{v} ((F.op ⋙ R) ⋙ forget₂ _ _) :=
  pushforward₀ F (R ⋙ forget₂ _ _)

/-- The pushforward of presheaves of modules commutes with the forgetful functor
to presheaves of abelian groups. -/
noncomputable def pushforward₀CompToPresheaf (R : Dᵒᵖ ⥤ RingCat.{u}) :
    pushforward₀.{v} F R ⋙ toPresheaf _ ≅ toPresheaf _ ⋙ (whiskeringLeft _ _ _).obj F.op :=
  Iso.refl _

variable {F}
variable {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

attribute [local simp] pushforward₀ in
/-- The pushforward functor `PresheafOfModules R ⥤ PresheafOfModules S` induced by
a morphism of presheaves of rings `S ⟶ F.op ⋙ R`. -/
@[simps! obj_obj]
noncomputable def pushforward : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} S :=
  pushforward₀ F R ⋙ restrictScalars φ

lemma forget₂_map_pushforward_obj_map {U V : Cᵒᵖ} (f : U ⟶ V) (M : PresheafOfModules R) :
    (forget₂ _ Ab).map (((PresheafOfModules.pushforward φ).obj M).map f) =
      M.presheaf.map (F.map f.unop).op :=
  rfl

lemma forget₂_map_pushforward_map_app {U : Cᵒᵖ} {M N : PresheafOfModules _} (g : M ⟶ N) :
    (forget₂ _ Ab).map (((pushforward φ).map g).app U) = (forget₂ _ Ab).map (g.app _) :=
  rfl

/-- The pushforward of presheaves of modules commutes with the forgetful functor
to presheaves of abelian groups. -/
noncomputable def pushforwardCompToPresheaf :
    pushforward.{v} φ ⋙ toPresheaf _ ≅ toPresheaf _ ⋙ (whiskeringLeft _ _ _).obj F.op :=
  Iso.refl _

lemma pushforward_obj_map_apply (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
      (((pushforward φ).obj M).map f).hom m = M.map (F.map f.unop).op m := rfl

#adaptation_note
/--
After https://github.com/leanprover/lean4/pull/14624:

We had to use the `instanceSearchTypes` backward compatibility flag to make an instance search
succeed. Concretely, the following instance cannot be synthesized, writing `P Z` for
`(ModuleCat.restrictScalars (RingCat.Hom.hom (φ.app Z))).obj (((pushforward₀ F R).obj M).obj Z)`:
```
DFunLike (↑(P X) →ₗ[↑(S.obj X)]
    ↑((ModuleCat.restrictScalars (RingCat.Hom.hom (S.map f))).obj (P Y))) _ _
```
It is needed to elaborate the `DFunLike.coe` in the statement below, whose `F` annotation spells
domain and codomain on the `restrictScalars` side.

The failure happens while applying `@LinearMap.instFunLike`: assigning one of its
instance-implicit-argument metavariables is rejected because the metavariable's type and the type
of the assigned value do not match at `.instances` transparency. The metavariable's expected type
is `Module ↑(S.obj X) ↑(P X)`, whereas the assigned value `(((pushforward φ).obj M).obj X).isModule`
has type `Module ↑(S.obj X) ↑(((pushforward φ).obj M).obj X)`. The comparison bottoms out at
`(ModuleCat.restrictScalars (RingCat.Hom.hom (φ.app X))).1 =?= ((pushforward φ).obj M).1`, the same
module written once through `pushforward` and once through `restrictScalars`. Lean falls back to
synthesize an instance of the correct type, which succeeds, but it returns
```
((ModuleCat.restrictScalars (RingCat.Hom.hom (φ.app X))).obj (((pushforward₀ F R).obj M).obj
X)).isModule
```
This again not defeq to the assigned value, stalling in the same way. That second comparison runs at
`.implicit`, but `pushforward` does not unfold there either.

Potential fix: Mark `pushforward`, `PresheafOfModules.restrictScalars` and
`PresheafOfModules.restrictScalarsObj` implicit-reducible; then both backward compatibility options
can go.
-/
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency.types false in
/-- `@[simp]`-normal form of `pushforward_obj_map_apply`. -/
@[simp]
lemma pushforward_obj_map_apply' (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
      DFunLike.coe
        (F := ↑((ModuleCat.restrictScalars _).obj _) →ₗ[_]
          ↑((ModuleCat.restrictScalars (S.map f).hom).obj ((ModuleCat.restrictScalars _).obj _)))
        (((pushforward φ).obj M).map f).hom m = M.map (F.map f.unop).op m := rfl

lemma pushforward_map_app_apply {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
    (((pushforward φ).map α).app X).hom m = α.app (Opposite.op (F.obj X.unop)) m := rfl

#adaptation_note
/--
After https://github.com/leanprover/lean4/pull/14624:

We had to use the `instanceSearchTypes` backward compatibility flag to make an instance search
succeed. Concretely, the following instance cannot be synthesized, writing `P Z` for
`(ModuleCat.restrictScalars (RingCat.Hom.hom (φ.app Z))).obj (((pushforward₀ F R).obj M).obj Z)`:
`DFunLike (↑(P X) →ₗ[↑(S.obj X)] ↑((ModuleCat.restrictScalars (RingCat.Hom.hom (φ.app X))).obj
  (((pushforward₀ F R).obj N).obj X))) _ _`
It is needed to elaborate the `DFunLike.coe` in the statement below.

This is the same failure as for `pushforward_obj_map_apply'` above, again while applying
`@LinearMap.instFunLike`: the metavariable's expected type is `Module ↑(S.obj X) ↑(P X)`, the
assigned value is `(((pushforward φ).obj M).obj X).isModule` of type
`Module ↑(S.obj X) ↑(((pushforward φ).obj M).obj X)`, and both the direct `.instances` check and the
comparison against the re-synthesized instance bottom out at
`(ModuleCat.restrictScalars (RingCat.Hom.hom (φ.app X))).1 =?= ((pushforward φ).obj M).1`.

Potential fix: Mark `pushforward`, `PresheafOfModules.restrictScalars` and
`PresheafOfModules.restrictScalarsObj` implicit-reducible; then both backward compatibility options
can go.
-/
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency.types false in
/-- `@[simp]`-normal form of `pushforward_map_app_apply`. -/
@[simp]
lemma pushforward_map_app_apply' {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
    DFunLike.coe
      (F := ↑((ModuleCat.restrictScalars _).obj _) →ₗ[_] ↑((ModuleCat.restrictScalars _).obj _))
      (((pushforward φ).map α).app X).hom m = α.app (Opposite.op (F.obj X.unop)) m := rfl

section

variable (R) in
/-- The pushforward functor by the identity morphism identifies to
the identify functor of the category of presheaves of modules. -/
noncomputable def pushforwardId :
    pushforward.{v} (S := R) (F := 𝟭 _) (𝟙 R) ≅ 𝟭 _ :=
  Iso.refl _

section

variable {T : Eᵒᵖ ⥤ RingCat.{u}} {G : D ⥤ E} (ψ : R ⟶ G.op ⋙ T)

/-- The composition of two pushforward functors on categories of presheaves of modules
identify to the pushforward for the composition. -/
noncomputable def pushforwardComp :
    pushforward.{v} ψ ⋙ pushforward.{v} φ ≅
      pushforward.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ) :=
  Iso.refl _

variable {T' : E'ᵒᵖ ⥤ RingCat.{u}} {G' : E ⥤ E'} (ψ' : T ⟶ G'.op ⋙ T')

lemma pushforward_assoc :
    (pushforward ψ').isoWhiskerLeft (pushforwardComp φ ψ) ≪≫
      pushforwardComp (F := F ⋙ G) (φ ≫ F.op.whiskerLeft ψ) ψ' =
    ((pushforward ψ').associator (pushforward ψ) (pushforward φ)).symm ≪≫
      isoWhiskerRight (pushforwardComp ψ ψ') (pushforward φ) ≪≫
        pushforwardComp (G := G ⋙ G') φ (ψ ≫ G.op.whiskerLeft ψ') := by ext; rfl

end

lemma pushforward_comp_id :
    pushforwardComp.{v} (F := 𝟭 C) (𝟙 S) φ =
      isoWhiskerLeft (pushforward.{v} φ) (pushforwardId S) ≪≫ rightUnitor _ := by ext; rfl

lemma pushforward_id_comp :
    pushforwardComp.{v} (G := 𝟭 _) φ (𝟙 R) =
      isoWhiskerRight (pushforwardId R) (pushforward.{v} φ) ≪≫ leftUnitor _ := by ext; rfl

end

end PresheafOfModules
