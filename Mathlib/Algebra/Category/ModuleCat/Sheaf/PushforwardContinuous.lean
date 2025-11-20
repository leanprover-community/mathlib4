/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Pushforward of sheaves of modules

Assume that categories `C` and `D` are equipped with Grothendieck topologies, and
that `F : C ⥤ D` is a continuous functor.
Then, if `φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R` is
a morphism of sheaves of rings, we construct the pushforward functor
`pushforward φ : SheafOfModules.{v} R ⥤ SheafOfModules.{v} S`.

-/

@[expose] public section

universe v' u' v v₁ v₂ v₃ u₁ u₂ u₃ u

open CategoryTheory

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous.{u} F J K] [Functor.IsContinuous.{v} F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- The pushforward of sheaves of modules that is induced by a continuous functor `F`
and a morphism of sheaves of rings `φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R`. -/
@[simps map_val, simps -isSimp obj_val]
noncomputable def pushforward : SheafOfModules.{v} R ⥤ SheafOfModules.{v} S where
  obj M :=
    { val := (PresheafOfModules.pushforward φ.val).obj M.val
      isSheaf := ((F.sheafPushforwardContinuous _ J K).obj ⟨_, M.isSheaf⟩).cond }
  map f :=
    { val := (PresheafOfModules.pushforward φ.val).map f.val }

/-- Given `M : SheafOfModules R` and `X : D`, this is the restriction of `M`
over the sheaf of rings `R.over X` on the category `Over X`. -/
noncomputable abbrev over (M : SheafOfModules.{v} R) (X : D) : SheafOfModules.{v} (R.over X) :=
  (pushforward.{v} (𝟙 _)).obj M

section Functorial

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {F : C ⥤ D} {G : D ⥤ E}
  {T : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}} {R : Sheaf L RingCat.{u}}
  [Functor.IsContinuous.{u} F J K] [Functor.IsContinuous.{v} F J K]
  [Functor.IsContinuous.{u} G K L] [Functor.IsContinuous.{v} G K L]
  (φ : T ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj S)
  (ψ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj R)

/-- Pushforward along the identity is (isomorphic to) the identity. -/
noncomputable def pushforwardId : pushforward.{v} (F := 𝟭 _) (𝟙 R) ≅ 𝟭 _ := Iso.refl _

/-- Pushforward along equal morphisms of sheaves of rings is isomorphic. -/
noncomputable
def pushforwardCongr {φ ψ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj R} (e : φ = ψ) :
    pushforward.{v} φ ≅ pushforward.{v} ψ :=
  NatIso.ofComponents (fun X ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ (ModuleCat.restrictScalarsCongr (by subst e; rfl)).app _)
      fun _ _ _ ↦ by subst e; rfl)) fun _ ↦ by subst e; rfl

@[simp] lemma pushforwardCongr_symm
    {φ ψ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj R} (e : φ = ψ) :
  (pushforwardCongr e).symm = pushforwardCongr e.symm := rfl

@[simp] lemma pushforwardCongr_hom_app_val_app
    {φ ψ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj R} (e : φ = ψ) (M U x) :
  ((pushforwardCongr e).hom.app M).val.app U x = x := rfl

/-- Composition of pushforwards is (isomorphic to) the pushforward along the composition. -/
noncomputable def pushforwardComp :
    letI := CategoryTheory.Functor.isContinuous_comp.{u} F G J K L
    letI := CategoryTheory.Functor.isContinuous_comp.{v} F G J K L
    pushforward.{v} ψ ⋙ pushforward.{v} φ ≅
      pushforward.{v} (F := F ⋙ G) (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) :=
  NatIso.ofComponents (fun X ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    (PresheafOfModules.pushforwardComp φ.val ψ.val).app X.val) fun f ↦ SheafOfModules.hom_ext
      ((PresheafOfModules.pushforwardComp φ.val ψ.val).hom.naturality f.val)

-- Not a simp because the type of the LHS is dsimp-able
lemma pushforwardComp_hom_app_val_app (M U x) :
  ((pushforwardComp φ ψ).hom.app M).val.app U x = x := rfl

-- Not a simp because the type of the LHS is dsimp-able
lemma pushforwardComp_inv_app_val_app (M U x) :
  ((pushforwardComp φ ψ).inv.app M).val.app U x = x := rfl

end Functorial

section NatTrans

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F G H : C ⥤ D} {T : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
  [Functor.IsContinuous.{u} F J K] [Functor.IsContinuous.{v} F J K]
  [Functor.IsContinuous.{u} G J K] [Functor.IsContinuous.{v} G J K]
  [Functor.IsContinuous.{u} H J K] [Functor.IsContinuous.{v} H J K]
  (φ : T ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj S)

/-- A natural transformation gives a natural transformation between the pushforward functors. -/
noncomputable
def pushforwardNatTrans (α : F ⟶ G) :
    pushforward.{v} φ ⟶
      pushforward.{v} (φ ≫ (Functor.sheafPushforwardContinuousNatTrans α _ _ _).app S) where
  app X :=
  { val.app U := (ModuleCat.restrictScalars (φ.val.app U).hom).map (X.val.map (α.app U.unop).op)
    val.naturality {U V} i := by
      ext x
      dsimp
      change (X.val.presheaf.map (G.map i.unop).op ≫ X.val.presheaf.map (α.app V.unop).op) _ =
        (X.val.presheaf.map (α.app U.unop).op ≫ X.val.presheaf.map (F.map i.unop).op) _
      simp only [← CategoryTheory.Functor.map_comp, ← op_comp, α.naturality] }
  naturality {X Y} f := by
    ext U x
    exact congr($(f.val.naturality (α.app U.unop).op) x).symm

@[simp] lemma pushforwardNatTrans_app_val_app (α : F ⟶ G) (M U x) :
    ((pushforwardNatTrans φ α).app M).val.app U x = M.val.map (α.app U.unop).op x := rfl

@[simp]
lemma pushforwardNatTrans_id :
    pushforwardNatTrans φ (𝟙 G) = (pushforwardCongr (by cat_disch)).hom := by cat_disch

@[simp]
lemma pushforwardNatTrans_comp (α : F ⟶ G) (β : G ⟶ H)
    (φ : T ⟶ (H.sheafPushforwardContinuous RingCat.{u} J K).obj S) :
    pushforwardNatTrans φ (α ≫ β) = pushforwardNatTrans φ β ≫ pushforwardNatTrans _ α ≫
      (pushforwardCongr (by cat_disch)).hom := by cat_disch

@[simp]
lemma pushforwardNatTrans_app_val_app_apply (α : F ⟶ G) (X U x) :
    ((pushforwardNatTrans φ α).app X).val.app U x = X.val.map (α.app U.unop).op x := rfl

/-- A natural isomorphism gives a natural isomorphism between the pushforward functors. -/
@[simps hom inv]
noncomputable def pushforwardNatIso (α : F ≅ G) :
    pushforward.{v} φ ≅
      pushforward.{v} (φ ≫ (Functor.sheafPushforwardContinuousNatTrans α.hom _ _ _).app S) where
  hom := pushforwardNatTrans _ α.hom
  inv := pushforwardNatTrans _ α.inv ≫
    (pushforwardCongr (by ext : 3; simp [← Functor.map_comp, ← op_comp])).hom
  hom_inv_id := by
    ext X U x
    suffices X.val.presheaf.map (α.hom.app U.unop).op ≫
      X.val.presheaf.map (α.inv.app U.unop).op = 𝟙 _ from congr($this x)
    simp only [← Functor.map_comp, ← op_comp,
      Iso.inv_hom_id_app, op_id, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    ext X U x
    suffices X.val.presheaf.map (α.inv.app U.unop).op ≫
      X.val.presheaf.map (α.hom.app U.unop).op = 𝟙 _ from congr($this x)
    simp only [← Functor.map_comp, ← op_comp,
      Iso.hom_inv_id_app, op_id, CategoryTheory.Functor.map_id]

end NatTrans

section Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D} {G : D ⥤ C}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous.{u} F J K] [Functor.IsContinuous.{v} F J K]
  [Functor.IsContinuous.{u} G K J] [Functor.IsContinuous.{v} G K J]
  (adj : F ⊣ G)
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj S)
  (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) R.val = ψ.val ≫ G.op.whiskerLeft φ.val)
  (H₂ : φ.val ≫ F.op.whiskerLeft ψ.val ≫
    Functor.whiskerRight (NatTrans.op adj.unit) S.val = 𝟙 S.val)

/-- If `F ⊣ G`, then the pushforward along `F` and `G` are also adjoint. -/
noncomputable
def pushforwardPushforwardAdj : pushforward.{v} φ ⊣ pushforward.{v} ψ where
  unit :=
    letI := CategoryTheory.Functor.isContinuous_comp.{v} G F K J K
    letI := CategoryTheory.Functor.isContinuous_comp.{u} G F K J K
    pushforwardId.inv ≫ pushforwardNatTrans (𝟙 _) adj.counit ≫
      (pushforwardCongr (by ext1; simpa)).hom ≫ (pushforwardComp _ _).inv
  counit :=
    letI := CategoryTheory.Functor.isContinuous_comp.{v} F G J K J
    letI := CategoryTheory.Functor.isContinuous_comp.{u} F G J K J
    (pushforwardComp _ _).hom ≫ pushforwardNatTrans _ adj.unit ≫
      (pushforwardCongr (by ext1; simpa)).hom ≫ pushforwardId.hom
  left_triangle_components X := by
    ext U x
    change (X.val.presheaf.map (adj.counit.app (F.obj U.unop)).op ≫
      X.val.presheaf.map (F.map (adj.unit.app U.unop)).op) _ = _
    rw [← Functor.map_comp, ← op_comp, adj.left_triangle_components]
    simp
  right_triangle_components X := by
    ext U x
    change (X.val.presheaf.map (G.map (adj.counit.app U.unop)).op ≫
      X.val.presheaf.map (adj.unit.app (G.obj U.unop)).op) _ = _
    rw [← Functor.map_comp, ← op_comp, adj.right_triangle_components]
    simp

-- Not a simp because the type of the LHS is dsimp-able
lemma pushforwardPushforwardAdj_unit_app_val_app (M U x) :
    ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M).val.app U x =
      M.val.map (adj.counit.app U.unop).op x := rfl

-- Not a simp because the type of the LHS is dsimp-able
lemma pushforwardPushforwardAdj_counit_app_val_app (M U x) :
    ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app M).val.app U x =
      M.val.map (adj.unit.app U.unop).op x := rfl

end Adjunction

end SheafOfModules
