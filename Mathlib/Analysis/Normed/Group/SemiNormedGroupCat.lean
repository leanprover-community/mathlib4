/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Riccardo Brasca

! This file was ported from Lean 3 source module analysis.normed.group.SemiNormedGroup
! leanprover-community/mathlib commit 17ef379e997badd73e5eabb4d38f11919ab3c4b3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.Normed.Group.Hom
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.Elementwise

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

set_option linter.uppercaseLean3 false --in [linter.uppercaseLean3]
#align SemiNormedGroup SemiNormedGroup

namespace SemiNormedGroup

instance bundledHom : BundledHom @NormedAddGroupHom where
  toFun := @NormedAddGroupHom.toFun
  id := @NormedAddGroupHom.id
  comp := @NormedAddGroupHom.comp

#align SemiNormedGroup.bundled_hom SemiNormedGroup.bundledHom

deriving instance LargeCategory for SemiNormedGroup

--Porting note: deriving fails for ConcreteCategory, adding instance manually.
--deriving instance LargeCategory, ConcreteCategory for SemiRingCat
instance : ConcreteCategory SemiNormedGroup := by
  dsimp [SemiNormedGroup]
  infer_instance

--Porting Note: hasCoeToSort doesn't exist anymore
--instance : CoeSort SemiNormedGroup (Type u) :=
--  Bundled.hasCoeToSort

instance : CoeSort SemiNormedGroup (Type _) where
  coe X := X.α

/-- Construct a bundled `SemiNormedGroup` from the underlying type and typeclass. -/
def of (M : Type u) [SeminormedAddCommGroup M] : SemiNormedGroup :=
  Bundled.of M
#align SemiNormedGroup.of SemiNormedGroup.of

instance (M : SemiNormedGroup) : SeminormedAddCommGroup M :=
  M.str

/-- Porting Note: Added -- needed to make coe_id work-/
instance {X Y : SemiNormedGroup} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X ⟶ Y) := NormedAddGroupHom.toFun f

@[simp]
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGroup.of V : Type u) = V :=
  rfl
#align SemiNormedGroup.coe_of SemiNormedGroup.coe_of

@[simp]
theorem coe_id (V : SemiNormedGroup) : (𝟙 V : V → V) = id :=
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

/--porting note: originally empty, which didn't work. Notation for composition changed?-/
instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGroup where
  Zero _ _ := NormedAddGroupHom.zero
  comp_zero _ _ := rfl
  zero_comp _ _ _ f:= NormedAddGroupHom.comp_zero f


@[simp]
theorem zero_apply {V W : SemiNormedGroup} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl
#align SemiNormedGroup.zero_apply SemiNormedGroup.zero_apply

--/--porting note :Added, Needed to make isZero_of_subsingleton work -/
-- instance {V W : SemiNormedGroup}: ZeroHomClass (V ⟶ W) V W where
--   coe := NormedAddGroupHom.toFun
--   coe_injective' := NormedAddGroupHom.coe_injective
--   map_zero f := by simp only [NormedAddGroupHom.toFun_eq_coe, map_zero]

/--porting note: Didn't work, manual rewrite-/
theorem isZero_of_subsingleton (V : SemiNormedGroup) [Subsingleton V] : Limits.IsZero V := by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩
  · ext x
    change V at x
    have  := Subsingleton.elim (x : V) (0 : V)
    rw [this]
    suffices f 0 = (0 : V⟶ X) 0 by convert this
    simp only [NormedAddGroupHom.toFun_eq_coe, map_zero, zero_apply]
  · ext
    apply @Subsingleton.elim V _
#align SemiNormedGroup.is_zero_of_subsingleton SemiNormedGroup.isZero_of_subsingleton

instance hasZeroObject : Limits.HasZeroObject SemiNormedGroup.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩
#align SemiNormedGroup.has_zero_object SemiNormedGroup.hasZeroObject

/--Porting Note: Added to make iso_isometry_of_normNoninc work-/
instance toAddMonoidHomClass {V W : SemiNormedGroup} : AddMonoidHomClass (V ⟶ W) V W where
  coe := (forget SemiNormedGroup).map
  coe_injective' := fun f g h => by cases f; cases g; congr
  map_add f := f.map_add'
  map_zero f := (AddMonoidHom.mk' f.toFun f.map_add').map_zero

theorem iso_isometry_of_normNoninc {V W : SemiNormedGroup} (i : V ≅ W) (h1 : i.hom.NormNoninc)
    (h2 : i.inv.NormNoninc) : Isometry i.hom := by
  apply AddMonoidHomClass.isometry_of_norm i.hom
  intro v
  apply le_antisymm (h1 v)
  have h3 : v = i.inv (i.hom v) := by
    change v = (forget _).map i.inv ((forget _).map i.hom v)
    simp only [FunctorToTypes.map_inv_map_hom_apply]
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [← h3]
    _ ≤ ‖i.hom v‖ := h2 _
#align SemiNormedGroup.iso_isometry_of_norm_noninc SemiNormedGroup.iso_isometry_of_normNoninc

end SemiNormedGroup

--Porting Note: Is this correct? It appears that the category structure is norm-non-increasing up to
-- a factor
/-- `SemiNormedGroup₁` is a type synonym for `SemiNormedGroup`,
which we shall equip with the category structure consisting only of the norm non-increasing maps.
-/
def SemiNormedGroup₁ : Type (u + 1) :=
  Bundled SeminormedAddCommGroup
#align SemiNormedGroup₁ SemiNormedGroup₁

namespace SemiNormedGroup₁

--Porting Note: hasCoeToSort doesn't exist anymore
--instance : CoeSort SemiNormedGroup₁ (Type u) :=
--  Bundled.hasCoeToSort

instance : CoeSort SemiNormedGroup₁ (Type _) where
  coe X := X.α


--Porting Note: Was explicitly shown before. Is there a problem doing it like this?
instance : LargeCategory.{u} SemiNormedGroup₁ where
  Hom X Y := { f : NormedAddGroupHom X Y // f.NormNoninc }
  id X := ⟨NormedAddGroupHom.id X, NormedAddGroupHom.NormNoninc.id⟩
  comp {X Y Z} f g := ⟨g.1.comp f.1, g.2.comp f.2⟩

/-- Porting Note: Added-/
instance {X Y : SemiNormedGroup₁} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X ⟶ Y) := f.1

@[ext]
theorem hom_ext {M N : SemiNormedGroup₁} (f g : M ⟶ N) (w : (↑f : M → N) = (↑g : M → N)) : f = g :=
  Subtype.ext (NormedAddGroupHom.ext (congr_fun w))
#align SemiNormedGroup₁.hom_ext SemiNormedGroup₁.hom_ext

/--Porting Note: Changed -/
instance : ConcreteCategory.{u} SemiNormedGroup₁ where
  forget := rfl


/-- Construct a bundled `SemiNormedGroup₁` from the underlying type and typeclass. -/
def of (M : Type u) [SeminormedAddCommGroup M] : SemiNormedGroup₁ :=
  Bundled.of M
#align SemiNormedGroup₁.of SemiNormedGroup₁.of

instance (M : SemiNormedGroup₁) : SeminormedAddCommGroup M :=
  M.str

--Porting Note: Some changes
/-- Promote a morphism in `SemiNormedGroup` to a morphism in `SemiNormedGroup₁`. -/
def mkHom {M N : SemiNormedGroup} (f : M ⟶ N) (i : f.NormNoninc) :
    SemiNormedGroup₁.of M ⟶ SemiNormedGroup₁.of N :=
  ⟨f, f.map_add' , ⟨1, by simpa using i⟩ ⟩
#align SemiNormedGroup₁.mk_hom SemiNormedGroup₁.mkHom

@[simp]
theorem mkHom_apply {M N : SemiNormedGroup} (f : M ⟶ N) (i : f.NormNoninc) (x) :
    mkHom f i x = f x :=
  rfl
#align SemiNormedGroup₁.mk_hom_apply SemiNormedGroup₁.mkHom_apply

/-- Promote an isomorphism in `SemiNormedGroup` to an isomorphism in `SemiNormedGroup₁`. -/
@[simps]
def mkIso {M N : SemiNormedGroup} (f : M ≅ N) (i : f.hom.NormNoninc) (i' : f.inv.NormNoninc) :
    SemiNormedGroup₁.of M ≅ SemiNormedGroup₁.of N where
  hom := mkHom f.hom i
  inv := mkHom f.inv i'
  hom_inv_id := by
    exact f.hom_inv_id
  inv_hom_id := by
    exact f.inv_hom_id
#align SemiNormedGroup₁.mk_iso SemiNormedGroup₁.mkIso

instance : HasForget₂ SemiNormedGroup₁ SemiNormedGroup where
  forget₂ :=
    { obj := fun X => X
      map := fun {X Y f} => f }


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

/--Porting Note: Had to add this to make Limits.HasZeroMorphisms work-/
lemma zero_NormNoninc {X Y : SemiNormedGroup} : NormedAddGroupHom.NormNoninc (0:X⟶ Y):= by
  change ∀ v : X, ‖(0 : (X⟶ Y)) v‖ ≤ ‖v‖
  intro v
  simp only [SemiNormedGroup.zero_apply, norm_zero, norm_nonneg]

/--Porting Note: Added some things to make it compile again - might have created issues?-/
instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGroup₁ where
  Zero X Y := {zero := mkHom 0 zero_NormNoninc}
  comp_zero {X Y} f Z := by
    ext x
    simp only [coe_comp', NormedAddGroupHom.toFun_eq_coe, NormedAddGroupHom.comp_apply]
    rfl
  zero_comp X Y Z f := by
    ext x
    simp only [coe_comp', NormedAddGroupHom.toFun_eq_coe, NormedAddGroupHom.comp_apply]
    apply map_zero

@[simp]
theorem zero_apply {V W : SemiNormedGroup₁} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl
#align SemiNormedGroup₁.zero_apply SemiNormedGroup₁.zero_apply

/--Porting Note: Didn't work, manual rewrite-/
theorem isZero_of_subsingleton (V : SemiNormedGroup₁) [Subsingleton V] : Limits.IsZero V := by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩
  · ext x
    have : x = 0 := Subsingleton.elim _ _
    simp only [this, map_zero]
    simp only [NormedAddGroupHom.toFun_eq_coe, map_zero, zero_apply]
  · ext
    apply Subsingleton.elim
#align SemiNormedGroup₁.is_zero_of_subsingleton SemiNormedGroup₁.isZero_of_subsingleton

instance hasZeroObject : Limits.HasZeroObject SemiNormedGroup₁.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩
#align SemiNormedGroup₁.has_zero_object SemiNormedGroup₁.hasZeroObject

/--Porting Note: I think this simply doesn't work with the current definition of SemiNormedGroup₁-/
theorem iso_isometry {V W : SemiNormedGroup₁} (i : V ≅ W) : Isometry i.hom := by
  intro v
  apply le_antisymm (i.hom.3 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [iso.hom_inv_id_apply]
    _ ≤ ‖i.hom v‖ := i.inv.2 _
#align SemiNormedGroup₁.iso_isometry SemiNormedGroup₁.iso_isometry

end SemiNormedGroup₁
