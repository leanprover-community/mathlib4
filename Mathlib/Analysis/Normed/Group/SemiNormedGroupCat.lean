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

We define `SemiNormedGroupCat`, the category of seminormed groups and normed group homs between
them, as well as `SemiNormedGroupCat₁`, the subcategory of norm non-increasing morphisms.
-/


noncomputable section

universe u

open CategoryTheory

/-- The category of seminormed abelian groups and bounded group homomorphisms. -/
def SemiNormedGroupCat : Type (u + 1) :=
  Bundled SeminormedAddCommGroup

set_option linter.uppercaseLean3 false --in [linter.uppercaseLean3]
#align SemiNormedGroup SemiNormedGroupCat

namespace SemiNormedGroupCat

instance bundledHom : BundledHom @NormedAddGroupHom where
  toFun := @NormedAddGroupHom.toFun
  id := @NormedAddGroupHom.id
  comp := @NormedAddGroupHom.comp

#align SemiNormedGroup.bundled_hom SemiNormedGroupCat.bundledHom

deriving instance LargeCategory for SemiNormedGroupCat

--Porting note: deriving fails for ConcreteCategory, adding instance manually.
--deriving instance LargeCategory, ConcreteCategory for SemiRingCat
instance : ConcreteCategory SemiNormedGroupCat := by
  dsimp [SemiNormedGroupCat]
  infer_instance

instance : CoeSort SemiNormedGroupCat (Type _) where
  coe X := X.α

/-- Construct a bundled `SemiNormedGroupCat` from the underlying type and typeclass. -/
def of (M : Type u) [SeminormedAddCommGroup M] : SemiNormedGroupCat :=
  Bundled.of M
#align SemiNormedGroupCat.of SemiNormedGroupCat.of

instance (M : SemiNormedGroupCat) : SeminormedAddCommGroup M :=
  M.str

-- Porting Note: Added -- needed to make coe_id work
instance instFunLike (X Y : SemiNormedGroupCat) : FunLike (X ⟶ Y) X (fun _ => Y) :=
show FunLike (NormedAddGroupHom X Y) X (fun _ => Y) from inferInstance

-- Porting note : Added
instance instZeroHomClass (X Y : SemiNormedGroupCat) : ZeroHomClass (X ⟶ Y) X Y :=
show ZeroHomClass (NormedAddGroupHom X Y) X Y from inferInstance


@[simp]
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGroupCat.of V : Type u) = V :=
  rfl
#align SemiNormedGroup.coe_of SemiNormedGroupCat.coe_of

-- Porting note : marked with high priority to short circuit simplifier's path
@[simp (high)]
theorem coe_id (V : SemiNormedGroupCat) : (𝟙 V : V → V) = id :=
  rfl
#align SemiNormedGroup.coe_id SemiNormedGroupCat.coe_id

-- Porting note : marked with high priority to short circuit simplifier's path
@[simp (high)]
theorem coe_comp {M N K : SemiNormedGroupCat} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : M → K) = g ∘ f :=
  rfl
#align SemiNormedGroup.coe_comp SemiNormedGroupCat.coe_comp

instance : Inhabited SemiNormedGroupCat :=
  ⟨of PUnit⟩

instance ofUnique (V : Type u) [SeminormedAddCommGroup V] [i : Unique V] :
    Unique (SemiNormedGroupCat.of V) :=
  i
#align SemiNormedGroup.of_unique SemiNormedGroupCat.ofUnique

/--porting note: originally empty, which didn't work. Notation for composition changed?-/
instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGroupCat where
  Zero _ _ := NormedAddGroupHom.zero
  comp_zero _ _ := rfl
  zero_comp _ _ _ f := NormedAddGroupHom.comp_zero f


@[simp]
theorem zero_apply {V W : SemiNormedGroupCat} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl
#align SemiNormedGroup.zero_apply SemiNormedGroupCat.zero_apply

theorem isZero_of_subsingleton (V : SemiNormedGroupCat) [Subsingleton V] : Limits.IsZero V := by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩
  · ext x
    --porting note: `Subsingleton.elim` didn't work without `change`
    change V at x
    have  := Subsingleton.elim (x : V) (0 : V)
    --porting note: Next three lines were simply `simp [this, map_zero]`
    rw [this]
    suffices f 0 = (0 : V⟶ X) 0 by convert this
    simp only [map_zero]
  · ext
    --porting note: was `Subsingleton.elim`
    apply @Subsingleton.elim V _
#align SemiNormedGroup.is_zero_of_subsingleton SemiNormedGroupCat.isZero_of_subsingleton

instance hasZeroObject : Limits.HasZeroObject SemiNormedGroupCat.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩
#align SemiNormedGroup.has_zero_object SemiNormedGroupCat.hasZeroObject

/--Porting Note: Added to make iso_isometry_of_normNoninc work-/
instance toAddMonoidHomClass {V W : SemiNormedGroupCat} : AddMonoidHomClass (V ⟶ W) V W where
  coe := (forget SemiNormedGroupCat).map
  coe_injective' := fun f g h => by cases f; cases g; congr
  map_add f := f.map_add'
  map_zero f := (AddMonoidHom.mk' f.toFun f.map_add').map_zero

theorem iso_isometry_of_normNoninc {V W : SemiNormedGroupCat} (i : V ≅ W) (h1 : i.hom.NormNoninc)
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
#align SemiNormedGroup.iso_isometry_of_norm_noninc SemiNormedGroupCat.iso_isometry_of_normNoninc

end SemiNormedGroupCat

/-- `SemiNormedGroupCat₁` is a type synonym for `SemiNormedGroupCat`,
which we shall equip with the category structure consisting only of the norm non-increasing maps.
-/
def SemiNormedGroupCat₁ : Type (u + 1) :=
  Bundled SeminormedAddCommGroup
#align SemiNormedGroup₁ SemiNormedGroupCat₁

namespace SemiNormedGroupCat₁

--Porting Note: hasCoeToSort doesn't exist anymore
--instance : CoeSort SemiNormedGroupCat₁ (Type u) :=
--  Bundled.hasCoeToSort

instance : CoeSort SemiNormedGroupCat₁ (Type _) where
  coe X := X.α

instance : LargeCategory.{u} SemiNormedGroupCat₁ where
  Hom X Y := { f : NormedAddGroupHom X Y // f.NormNoninc }
  id X := ⟨NormedAddGroupHom.id X, NormedAddGroupHom.NormNoninc.id⟩
  comp {X Y Z} f g := ⟨g.1.comp f.1, g.2.comp f.2⟩

/-- Porting Note: Added-/
instance instFunLike (X Y : SemiNormedGroupCat₁) : FunLike (X ⟶ Y) X (fun _ => Y) where
  coe f := f.1.toFun
  coe_injective' := by
    intros a b
    intro h
    apply Subtype.val_inj.mp
    apply NormedAddGroupHom.coe_injective
    exact h

instance instZeroHomClass (X Y : SemiNormedGroupCat₁) : ZeroHomClass (X ⟶ Y) X Y where
  map_zero := by
    intro f
    dsimp [instFunLike]
    simp only [map_zero]


@[ext]
theorem hom_ext {M N : SemiNormedGroupCat₁} (f g : M ⟶ N) (w : (f : M → N) = (g : M → N)) :
    f = g :=
  Subtype.eq (NormedAddGroupHom.ext (congr_fun w))
#align SemiNormedGroup₁.hom_ext SemiNormedGroupCat₁.hom_ext

instance : ConcreteCategory.{u} SemiNormedGroupCat₁ where
  forget :=
    { obj := fun X => X
      map := fun f => f }
  forget_faithful := { }

/-- Construct a bundled `SemiNormedGroupCat₁` from the underlying type and typeclass. -/
def of (M : Type u) [SeminormedAddCommGroup M] : SemiNormedGroupCat₁ :=
  Bundled.of M
#align SemiNormedGroup₁.of SemiNormedGroupCat₁.of

instance (M : SemiNormedGroupCat₁) : SeminormedAddCommGroup M :=
  M.str

/-- Promote a morphism in `SemiNormedGroupCat` to a morphism in `SemiNormedGroupCat₁`. -/
def mkHom {M N : SemiNormedGroupCat} (f : M ⟶ N) (i : f.NormNoninc) :
    SemiNormedGroupCat₁.of M ⟶ SemiNormedGroupCat₁.of N :=
  ⟨f, i⟩
#align SemiNormedGroup₁.mk_hom SemiNormedGroupCat₁.mkHom

@[simp, nolint simpNF] -- Porting note: claims LHS simplifies with `SemiNormedGroupCat₁.coe_of`
theorem mkHom_apply {M N : SemiNormedGroupCat} (f : M ⟶ N) (i : f.NormNoninc) (x) :
    mkHom f i x = f x :=
  rfl
#align SemiNormedGroup₁.mk_hom_apply SemiNormedGroupCat₁.mkHom_apply

/-- Promote an isomorphism in `SemiNormedGroupCat` to an isomorphism in `SemiNormedGroupCat₁`. -/
@[simps]
def mkIso {M N : SemiNormedGroupCat} (f : M ≅ N) (i : f.hom.NormNoninc) (i' : f.inv.NormNoninc) :
    SemiNormedGroupCat₁.of M ≅ SemiNormedGroupCat₁.of N where
  hom := mkHom f.hom i
  inv := mkHom f.inv i'
  hom_inv_id := by
    apply Subtype.eq
    exact f.hom_inv_id
  inv_hom_id := by
    apply Subtype.eq
    exact f.inv_hom_id
#align SemiNormedGroup₁.mk_iso SemiNormedGroupCat₁.mkIso

instance : HasForget₂ SemiNormedGroupCat₁ SemiNormedGroupCat
    where forget₂ :=
    { obj := fun X => X
      map := fun f => f.1 }

@[simp]
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGroupCat₁.of V : Type u) = V :=
  rfl
#align SemiNormedGroup₁.coe_of SemiNormedGroupCat₁.coe_of

@[simp]
theorem coe_id (V : SemiNormedGroupCat₁) : ⇑(𝟙 V) = id :=
  rfl
#align SemiNormedGroup₁.coe_id SemiNormedGroupCat₁.coe_id

-- Porting note : removed `simp` attribute for not being simp normal form
theorem coe_comp {M N K : SemiNormedGroupCat₁} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : M → K) = g ∘ f :=
  rfl
#align SemiNormedGroup₁.coe_comp SemiNormedGroupCat₁.coe_comp

/--Porting Note: Added to make `coe_comp'` work -- might cause double coercions-/
instance coeToNormedAddGroupHom {M N : SemiNormedGroupCat₁} :
    Coe (M ⟶ N) (NormedAddGroupHom M N) :=
  ⟨fun f => f.1⟩

-- Porting Note: This comment might no longer make sense
-- If `coe_fn_coe_base` fires before `coe_comp`, `coe_comp'` puts us back in normal form.
@[simp]
theorem coe_comp' {M N K : SemiNormedGroupCat₁} (f : M ⟶ N) (g : N ⟶ K) :
    ((f ≫ g) : NormedAddGroupHom M K) = (g : NormedAddGroupHom N K).comp f :=
  rfl
#align SemiNormedGroup₁.coe_comp' SemiNormedGroupCat₁.coe_comp'

instance : Inhabited SemiNormedGroupCat₁ :=
  ⟨of PUnit⟩

instance ofUnique (V : Type u) [SeminormedAddCommGroup V] [i : Unique V] :
    Unique (SemiNormedGroupCat₁.of V) :=
  i
#align SemiNormedGroup₁.of_unique SemiNormedGroupCat₁.ofUnique

instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGroupCat₁ where
  Zero X Y := { zero := ⟨0, NormedAddGroupHom.NormNoninc.zero⟩ }
  comp_zero {X Y} f Z := by
    ext
    rfl
  zero_comp X {Y Z} f := by
    ext x
    --porting note: used to be `simp [coe_fn_coe_base']` in mathlib3, added the below instead
    simp only [coe_comp', NormedAddGroupHom.comp_apply]
    change f ((0: X → Y) x) = (0: X → Z) x
    simp only [Pi.zero_apply, map_zero]

@[simp]
theorem zero_apply {V W : SemiNormedGroupCat₁} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl
#align SemiNormedGroup₁.zero_apply SemiNormedGroupCat₁.zero_apply

theorem isZero_of_subsingleton (V : SemiNormedGroupCat₁) [Subsingleton V] : Limits.IsZero V := by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩
  · ext x
    have : x = 0 := Subsingleton.elim _ _
    simp only [this, map_zero]
  · ext
    apply Subsingleton.elim
#align SemiNormedGroup₁.is_zero_of_subsingleton SemiNormedGroupCat₁.isZero_of_subsingleton

instance hasZeroObject : Limits.HasZeroObject SemiNormedGroupCat₁.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩
#align SemiNormedGroup₁.has_zero_object SemiNormedGroupCat₁.hasZeroObject

theorem iso_isometry {V W : SemiNormedGroupCat₁} (i : V ≅ W) : Isometry i.hom := by
  --porting note: was `change Isometry (⟨⟨i.hom, map_zero _⟩, fun _ _ => map_add _ _ _⟩ : V →+ W)`
  dsimp only [FunLike.coe]
  dsimp [NormedAddGroupHom.toFun]
  refine' AddMonoidHomClass.isometry_of_norm _ _
  intro v
  apply le_antisymm (i.hom.2 v)
  calc
    ‖v‖ = ‖ (i.hom ≫ i.inv) v‖ := by rw [Iso.hom_inv_id]; rfl
    _ = ‖i.inv (i.hom v)‖ := rfl
    _ ≤ ‖i.hom v‖ := i.inv.2 _
#align SemiNormedGroup₁.iso_isometry SemiNormedGroupCat₁.iso_isometry

end SemiNormedGroupCat₁
