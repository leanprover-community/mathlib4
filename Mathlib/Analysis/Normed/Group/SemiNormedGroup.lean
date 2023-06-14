/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Riccardo Brasca

! This file was ported from Lean 3 source module analysis.normed.group.SemiNormedGroup
! leanprover-community/mathlib commit 17ef379e997badd73e5eabb4d38f11919ab3c4b3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.Hom
import Mathbin.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom
import Mathbin.CategoryTheory.Elementwise

/-!
# The category of seminormed groups

We define `SemiNormedGroup`, the category of seminormed groups and normed group homs between them,
as well as `SemiNormedGroup₁`, the subcategory of norm non-increasing morphisms.
-/


noncomputable section

universe u

open CategoryTheory

/-- The category of seminormed abelian groups and bounded group homomorphisms. -/
def SemiNormedGroup : Type (u + 1) :=
  Bundled SeminormedAddCommGroup
#align SemiNormedGroup SemiNormedGroup

namespace SemiNormedGroup

instance bundledHom : BundledHom @NormedAddGroupHom :=
  ⟨@NormedAddGroupHom.toFun, @NormedAddGroupHom.id, @NormedAddGroupHom.comp,
    @NormedAddGroupHom.coe_inj⟩
#align SemiNormedGroup.bundled_hom SemiNormedGroup.bundledHom

deriving instance LargeCategory, ConcreteCategory for SemiNormedGroup

instance : CoeSort SemiNormedGroup (Type u) :=
  Bundled.hasCoeToSort

/-- Construct a bundled `SemiNormedGroup` from the underlying type and typeclass. -/
def of (M : Type u) [SeminormedAddCommGroup M] : SemiNormedGroup :=
  Bundled.of M
#align SemiNormedGroup.of SemiNormedGroup.of

instance (M : SemiNormedGroup) : SeminormedAddCommGroup M :=
  M.str

@[simp]
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGroup.of V : Type u) = V :=
  rfl
#align SemiNormedGroup.coe_of SemiNormedGroup.coe_of

@[simp]
theorem coe_id (V : SemiNormedGroup) : ⇑(𝟙 V) = id :=
  rfl
#align SemiNormedGroup.coe_id SemiNormedGroup.coe_id

@[simp]
theorem coe_comp {M N K : SemiNormedGroup} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : M → K) = g ∘ f :=
  rfl
#align SemiNormedGroup.coe_comp SemiNormedGroup.coe_comp

instance : Inhabited SemiNormedGroup :=
  ⟨of PUnit⟩

instance ofUnique (V : Type u) [SeminormedAddCommGroup V] [i : Unique V] :
    Unique (SemiNormedGroup.of V) :=
  i
#align SemiNormedGroup.of_unique SemiNormedGroup.ofUnique

instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGroup where

@[simp]
theorem zero_apply {V W : SemiNormedGroup} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl
#align SemiNormedGroup.zero_apply SemiNormedGroup.zero_apply

theorem isZero_of_subsingleton (V : SemiNormedGroup) [Subsingleton V] : Limits.IsZero V :=
  by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩
  · ext; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim
#align SemiNormedGroup.is_zero_of_subsingleton SemiNormedGroup.isZero_of_subsingleton

instance hasZeroObject : Limits.HasZeroObject SemiNormedGroup.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩
#align SemiNormedGroup.has_zero_object SemiNormedGroup.hasZeroObject

theorem iso_isometry_of_normNoninc {V W : SemiNormedGroup} (i : V ≅ W) (h1 : i.hom.NormNoninc)
    (h2 : i.inv.NormNoninc) : Isometry i.hom :=
  by
  apply AddMonoidHomClass.isometry_of_norm
  intro v
  apply le_antisymm (h1 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [iso.hom_inv_id_apply]
    _ ≤ ‖i.hom v‖ := h2 _
#align SemiNormedGroup.iso_isometry_of_norm_noninc SemiNormedGroup.iso_isometry_of_normNoninc

end SemiNormedGroup

/-- `SemiNormedGroup₁` is a type synonym for `SemiNormedGroup`,
which we shall equip with the category structure consisting only of the norm non-increasing maps.
-/
def SemiNormedGroup₁ : Type (u + 1) :=
  Bundled SeminormedAddCommGroup
#align SemiNormedGroup₁ SemiNormedGroup₁

namespace SemiNormedGroup₁

instance : CoeSort SemiNormedGroup₁ (Type u) :=
  Bundled.hasCoeToSort

instance : LargeCategory.{u} SemiNormedGroup₁
    where
  hom X Y := { f : NormedAddGroupHom X Y // f.NormNoninc }
  id X := ⟨NormedAddGroupHom.id X, NormedAddGroupHom.NormNoninc.id⟩
  comp X Y Z f g := ⟨(g : NormedAddGroupHom Y Z).comp (f : NormedAddGroupHom X Y), g.2.comp f.2⟩

@[ext]
theorem hom_ext {M N : SemiNormedGroup₁} (f g : M ⟶ N) (w : (f : M → N) = (g : M → N)) : f = g :=
  Subtype.eq (NormedAddGroupHom.ext (congr_fun w))
#align SemiNormedGroup₁.hom_ext SemiNormedGroup₁.hom_ext

instance : ConcreteCategory.{u} SemiNormedGroup₁
    where
  forget :=
    { obj := fun X => X
      map := fun X Y f => f }
  forget_faithful := { }

/-- Construct a bundled `SemiNormedGroup₁` from the underlying type and typeclass. -/
def of (M : Type u) [SeminormedAddCommGroup M] : SemiNormedGroup₁ :=
  Bundled.of M
#align SemiNormedGroup₁.of SemiNormedGroup₁.of

instance (M : SemiNormedGroup₁) : SeminormedAddCommGroup M :=
  M.str

/-- Promote a morphism in `SemiNormedGroup` to a morphism in `SemiNormedGroup₁`. -/
def mkHom {M N : SemiNormedGroup} (f : M ⟶ N) (i : f.NormNoninc) :
    SemiNormedGroup₁.of M ⟶ SemiNormedGroup₁.of N :=
  ⟨f, i⟩
#align SemiNormedGroup₁.mk_hom SemiNormedGroup₁.mkHom

@[simp]
theorem mkHom_apply {M N : SemiNormedGroup} (f : M ⟶ N) (i : f.NormNoninc) (x) :
    mkHom f i x = f x :=
  rfl
#align SemiNormedGroup₁.mk_hom_apply SemiNormedGroup₁.mkHom_apply

/-- Promote an isomorphism in `SemiNormedGroup` to an isomorphism in `SemiNormedGroup₁`. -/
@[simps]
def mkIso {M N : SemiNormedGroup} (f : M ≅ N) (i : f.hom.NormNoninc) (i' : f.inv.NormNoninc) :
    SemiNormedGroup₁.of M ≅ SemiNormedGroup₁.of N
    where
  hom := mkHom f.hom i
  inv := mkHom f.inv i'
  hom_inv_id' := by apply Subtype.eq; exact f.hom_inv_id
  inv_hom_id' := by apply Subtype.eq; exact f.inv_hom_id
#align SemiNormedGroup₁.mk_iso SemiNormedGroup₁.mkIso

instance : HasForget₂ SemiNormedGroup₁ SemiNormedGroup
    where forget₂ :=
    { obj := fun X => X
      map := fun X Y f => f.1 }

@[simp]
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGroup₁.of V : Type u) = V :=
  rfl
#align SemiNormedGroup₁.coe_of SemiNormedGroup₁.coe_of

@[simp]
theorem coe_id (V : SemiNormedGroup₁) : ⇑(𝟙 V) = id :=
  rfl
#align SemiNormedGroup₁.coe_id SemiNormedGroup₁.coe_id

@[simp]
theorem coe_comp {M N K : SemiNormedGroup₁} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : M → K) = g ∘ f :=
  rfl
#align SemiNormedGroup₁.coe_comp SemiNormedGroup₁.coe_comp

-- If `coe_fn_coe_base` fires before `coe_comp`, `coe_comp'` puts us back in normal form.
@[simp]
theorem coe_comp' {M N K : SemiNormedGroup₁} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : NormedAddGroupHom M K) = (↑g : NormedAddGroupHom N K).comp ↑f :=
  rfl
#align SemiNormedGroup₁.coe_comp' SemiNormedGroup₁.coe_comp'

instance : Inhabited SemiNormedGroup₁ :=
  ⟨of PUnit⟩

instance ofUnique (V : Type u) [SeminormedAddCommGroup V] [i : Unique V] :
    Unique (SemiNormedGroup₁.of V) :=
  i
#align SemiNormedGroup₁.of_unique SemiNormedGroup₁.ofUnique

instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGroup₁
    where
  Zero X Y := { zero := ⟨0, NormedAddGroupHom.NormNoninc.zero⟩ }
  comp_zero X Y f Z := by ext; rfl
  zero_comp X Y Z f := by ext; simp [coeFn_coe_base']

@[simp]
theorem zero_apply {V W : SemiNormedGroup₁} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl
#align SemiNormedGroup₁.zero_apply SemiNormedGroup₁.zero_apply

theorem isZero_of_subsingleton (V : SemiNormedGroup₁) [Subsingleton V] : Limits.IsZero V :=
  by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩
  · ext; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
    exact map_zero f.1
  · ext; apply Subsingleton.elim
#align SemiNormedGroup₁.is_zero_of_subsingleton SemiNormedGroup₁.isZero_of_subsingleton

instance hasZeroObject : Limits.HasZeroObject SemiNormedGroup₁.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩
#align SemiNormedGroup₁.has_zero_object SemiNormedGroup₁.hasZeroObject

theorem iso_isometry {V W : SemiNormedGroup₁} (i : V ≅ W) : Isometry i.hom :=
  by
  change Isometry (i.hom : V →+ W)
  refine' AddMonoidHomClass.isometry_of_norm i.hom _
  intro v
  apply le_antisymm (i.hom.2 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [iso.hom_inv_id_apply]
    _ ≤ ‖i.hom v‖ := i.inv.2 _
#align SemiNormedGroup₁.iso_isometry SemiNormedGroup₁.iso_isometry

end SemiNormedGroup₁

