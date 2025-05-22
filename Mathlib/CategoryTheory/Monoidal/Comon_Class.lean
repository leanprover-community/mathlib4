/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Mon_Class
import Mathlib.CategoryTheory.Monoidal.Braided.Opposite
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The category of comonoids in a monoidal category.

We define comonoids in a monoidal category `C`,
and show that they are equivalently monoid objects in the opposite category.

We construct the monoidal structure on `Comon_Cat C`, when `C` is braided.

An oplax monoidal functor takes comonoid objects to comonoid objects.
That is, a oplax monoidal functor `F : C ⥤ D` induces a functor `Comon_Cat C ⥤ Comon_Cat D`.

## TODO
* Comonoid objects in `C` are "just"
  oplax monoidal functors from the trivial monoidal category to `C`.
-/

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- A comonoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called a "coalgebra object".
-/
class Comon_Class (X : C) where
  /-- The counit morphism of a comonoid object. -/
  counit : X ⟶ 𝟙_ C
  /-- The comultiplication morphism of a comonoid object. -/
  comul : X ⟶ X ⊗ X
  counit_comul : comul ≫ (counit ▷ X) = (λ_ X).inv := by aesop_cat
  comul_counit : comul ≫ (X ◁ counit) = (ρ_ X).inv := by aesop_cat
  comul_assoc : comul ≫ (X ◁ comul) = comul ≫ (comul ▷ X) ≫ (α_ X X X).hom := by aesop_cat

namespace Comon_Class

@[inherit_doc] scoped notation "Δ" => Comon_Class.comul
@[inherit_doc] scoped notation "Δ["M"]" => Comon_Class.comul (X := M)
@[inherit_doc] scoped notation "ε" => Comon_Class.counit
@[inherit_doc] scoped notation "ε["M"]" => Comon_Class.counit (X := M)

attribute [reassoc, simp] counit_comul comul_counit
attribute [reassoc (attr := simp)] comul_assoc

-- @[reassoc, simp]
-- theorem counit_comul (X : C) [Comon_Class X] : Δ ≫ (ε ▷ X) = (λ_ X).inv := counit_comul'

-- @[reassoc, simp]
-- theorem comul_counit (X : C) [Comon_Class X] : Δ ≫ (X ◁ ε) = (ρ_ X).inv := comul_counit'

-- @[reassoc (attr := simp)]
-- theorem comul_assoc (X : C) [Comon_Class X] :
--     Δ ≫ (X ◁ Δ) = Δ ≫ (Δ ▷ X) ≫ (α_ X X X).hom := comul_assoc'

/-- The trivial comonoid object. We later show this is terminal in `Comon_Cat C`.
-/
@[simps]
instance trivial (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] :
    Comon_Class (𝟙_ C) where
  counit := 𝟙 _
  comul := (λ_ _).inv
  comul_assoc := by monoidal_coherence
  counit_comul := by monoidal_coherence
  comul_counit := by monoidal_coherence

instance : Inhabited (Comon_Class (𝟙_ C)) :=
  ⟨trivial C⟩

variable {M : C} [Comon_Class M]

@[simp]
theorem counit_comul_hom {Z : C} (f : M ⟶ Z) : Δ ≫ (ε ⊗ f) = f ≫ (λ_ Z).inv := by
  rw [tensorHom_def, counit_comul_assoc, leftUnitor_inv_naturality]

@[simp]
theorem comul_counit_hom {Z : C} (f : M ⟶ Z) : Δ ≫ (f ⊗ ε) = f ≫ (ρ_ Z).inv := by
  rw [tensorHom_def', comul_counit_assoc, rightUnitor_inv_naturality]

theorem comul_assoc_flip : Δ ≫ (Δ ▷ M) = Δ ≫ (M ◁ Δ) ≫ (α_ M M M).inv := by simp

end Comon_Class

open Comon_Class

/-- A morphism of comonoid objects. -/
@[ext]
structure Comon_ClassHom (M N : C) [Comon_Class M] [Comon_Class N] where
  hom : M ⟶ N
  hom_counit : hom ≫ ε = ε := by aesop_cat
  hom_comul : hom ≫ Δ = Δ ≫ (hom ⊗ hom) := by aesop_cat

attribute [reassoc (attr := simp)] Comon_ClassHom.hom_counit Comon_ClassHom.hom_comul

/-- The identity morphism on a comonoid object. -/
@[simps]
def Comon_ClassHom.id (M : C) [Comon_Class M] : Comon_ClassHom M M where
  hom := 𝟙 M

instance homInhabited (M : C) [Comon_Class M] : Inhabited (Comon_ClassHom M M) :=
  ⟨.id M⟩

/-- Composition of morphisms of comonoid objects. -/
@[simps]
def Comon_ClassHom.comp {M N O : C} [Comon_Class M] [Comon_Class N] [Comon_Class O]
    (f : Comon_ClassHom M N) (g : Comon_ClassHom N O) :
    Comon_ClassHom M O where
  hom := f.hom ≫ g.hom

@[ext]
structure Comon_ClassIso (M N : C) [Comon_Class M] [Comon_Class N] extends M ≅ N, Comon_ClassHom M N

initialize_simps_projections Comon_ClassIso (-hom, -inv, +toIso)

attribute [reassoc (attr := simp)] Comon_ClassIso.hom_counit Comon_ClassIso.hom_comul

@[simps]
def Comon_ClassIso.symm {M N : C} [Comon_Class M] [Comon_Class N] (f : Comon_ClassIso M N) :
    Comon_ClassIso N M where
  toIso := f.toIso.symm
  hom_counit := by simp [Iso.inv_comp_eq]
  hom_comul := by simp [Iso.inv_comp_eq]

structure Comon_Cat (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] where
  X : C
  [isComon_Class : Comon_Class X]

namespace Comon_Cat

open Comon_Class

attribute [instance] Comon_Cat.isComon_Class

instance : Inhabited (Comon_Cat C) :=
  ⟨⟨𝟙_ C⟩⟩

initialize_simps_projections Comon_Cat (-isComon_Class)

instance : Category.{v₁} (Comon_Cat C) where
  Hom M N := Comon_ClassHom M.X N.X
  id M := Comon_ClassHom.id M.X
  comp f g := Comon_ClassHom.comp f g

-- @[simp]
theorem mk_X (X : Comon_Cat C) : Comon_Cat.mk X.X = X :=
  rfl

def mkHom {X Y : C} [Comon_Class X] [Comon_Class Y] (f : Comon_ClassHom X Y) :
    mk X ⟶ mk Y :=
  f

def mkHom' {X Y : Comon_Cat C} (f : Comon_ClassHom X.X Y.X) :
    X ⟶ Y :=
  f

@[simp]
theorem mkHom_hom {X Y : C} [Comon_Class X] [Comon_Class Y] (f : Comon_ClassHom X Y) :
    (mkHom f).hom = f.hom :=
  rfl

-- Porting note: added, as Hom.ext does not apply to a morphism.
@[ext]
lemma ext' {X Y : Comon_Cat C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g :=
  Comon_ClassHom.ext w

@[simp]
theorem id_hom' {M : Comon_Cat C} : (𝟙 M : Comon_ClassHom M.X M.X).hom = 𝟙 M.X :=
  rfl

@[simp]
theorem comp_hom' {M N K : Comon_Cat C} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[simps]
def mkIso {X Y : C} [Comon_Class X] [Comon_Class Y] (f : Comon_ClassIso X Y) :
    mk X ≅ mk Y where
  hom := mkHom f.toComon_ClassHom
  inv := mkHom f.symm.toComon_ClassHom

@[simps!]
def mkIso' {X Y : Comon_Cat C} (f : Comon_ClassIso X.X Y.X) :
    X ≅ Y :=
  mkIso f

section

variable (C)

/-- The forgetful functor from comonoid objects to the ambient category. -/
@[simps!]
def forget : Comon_Cat C ⥤ C where
  obj A := A.X
  map f := f.hom

end

instance forget_faithful : (forget C).Faithful where

instance {A B : C} [Comon_Class A] [Comon_Class B] (f : Comon_ClassHom A B)
    [e : IsIso ((forget C).map (Comon_Cat.mkHom f))] :
    IsIso f.hom :=
  e

instance {A B : Comon_Cat C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] :
    IsIso f.hom :=
  e

instance uniqueHomToTrivial (A : Comon_Cat C) : Unique (A ⟶ mk (𝟙_ C)) where
  default :=
  { hom := ε
    hom_comul := by dsimp; simp only [unitors_inv_equal, comul_counit_hom] }
  uniq f := by
    ext
    dsimp only [trivial_comul]
    rw [← Category.comp_id f.hom, ← Comon_Class.trivial_counit, f.hom_counit]

open CategoryTheory.Limits

instance : HasTerminal (Comon_Cat C) :=
  hasTerminal_of_unique (mk (𝟙_ C))

end Comon_Cat

namespace Comon_Class

-- /-- Construct an isomorphism of comonoids by giving an isomorphism between the underlying objects
-- and checking compatibility with counit and comultiplication only in the forward direction.
-- -/
-- @[simps]
-- def mkIso {M N : C} [Comon_Class M] [Comon_Class N] (f : M ≅ N)
--     (f_counit : f.hom ≫ ε = ε := by aesop_cat)
--     (f_comul : f.hom ≫ Δ = Δ ≫ (f.hom ⊗ f.hom) := by aesop_cat) :
--     Comon_ClassIso M N where
--   hom := { hom := f.hom }
--   inv := {
--     hom := f.inv
--     hom_counit := by rw [← f_counit]; simp
--     hom_comul := by
--       rw [← cancel_epi f.hom]
--       slice_rhs 1 2 => rw [f_comul]
--       simp }

instance uniqueHomToTrivial (A : C) [Comon_Class A] : Unique (Comon_ClassHom A (𝟙_ C)) where
  default :=
    { hom := ε
      hom_counit := by dsimp; simp
      hom_comul := by dsimp; simp [comul_counit, unitors_inv_equal] }
  uniq f := by
    ext; simp
    rw [← Category.comp_id f.hom]
    erw [f.hom_counit]

open CategoryTheory.Limits

instance : HasTerminal (Comon_Cat C) :=
  hasTerminal_of_unique (.mk (𝟙_ C))

open Opposite Mon_Class

variable (C)

/--
Turn a comonoid object into a monoid object in the opposite category.
-/
-- @[simps]
instance Comon_ClassToMon_ClassOpOp_obj' (A : C) [Comon_Class A] : Mon_Class (op A : Cᵒᵖ) where
  one := counit.op
  mul := comul.op
  one_mul := by
    rw [← op_whiskerRight, ← op_comp, counit_comul]
    rfl
  mul_one := by
    rw [← op_whiskerLeft, ← op_comp, comul_counit]
    rfl
  mul_assoc := by
    rw [← op_inv_associator, ← op_whiskerRight, ← op_comp, ← op_whiskerLeft, ← op_comp,
      comul_assoc_flip, op_comp, op_comp_assoc]
    rfl

-- theorem Comon_ClassToMon_ClassOpOp_obj'_one (A : C) [Comon_Class A] : η = (ε : A ⟶ _).op := rfl

-- theorem Comon_ClassToMon_ClassOpOp_obj'_mul (A : C) [Comon_Class A] : μ = Δ.op

/--
The contravariant functor turning comonoid objects into monoid objects in the opposite category.
-/
@[simps] def Comon_ClassToMon_ClassOpOp : Comon_Cat C ⥤ (Mon_Cat (Cᵒᵖ))ᵒᵖ where
  obj A := op ⟨op A.X⟩
  map := fun f => op <|
    { hom := f.hom.op
      one_hom := by apply Quiver.Hom.unop_inj; simp [Comon_ClassToMon_ClassOpOp_obj']
      mul_hom := by apply Quiver.Hom.unop_inj; simp [Comon_ClassToMon_ClassOpOp_obj'] }

/--
Turn a monoid object in the opposite category into a comonoid object.
-/
instance Mon_ClassOpOpToComon_Classobj' (A : Cᵒᵖ) [Mon_Class A] : Comon_Class (unop A) where
  counit := Mon_Class.one.unop
  comul := Mon_Class.mul.unop
  counit_comul := by rw [← unop_whiskerRight, ← unop_comp, Mon_Class.one_mul]; rfl
  comul_counit := by rw [← unop_whiskerLeft, ← unop_comp, Mon_Class.mul_one]; rfl
  comul_assoc := by
    rw [← unop_whiskerRight, ← unop_whiskerLeft, ← unop_comp_assoc, ← unop_comp,
      Mon_Class.mul_assoc_flip]
    rfl

-- attribute [-simp] Comon_ClassToMon_ClassOpOp_obj'_one Comon_ClassToMon_ClassOpOp_obj'_mul in
/--
The contravariant functor turning monoid objects in the opposite category into comonoid objects.
-/
@[simps]
def Mon_ClassOpOpToComon_Class : (Mon_Cat (Cᵒᵖ))ᵒᵖ ⥤ Comon_Cat C where
  obj A := ⟨unop (unop A).X⟩
  map := fun f =>
    { hom := f.unop.hom.unop
      hom_counit := by apply Quiver.Hom.op_inj; simp [Mon_ClassOpOpToComon_Classobj']
      hom_comul := by apply Quiver.Hom.op_inj; simp [Mon_ClassOpOpToComon_Classobj'] }

/--
Comonoid objects are contravariantly equivalent to monoid objects in the opposite category.
-/
@[simps]
def Comon_ClassEquivMon_ClassOpOp : Comon_Cat C ≌ (Mon_Cat (Cᵒᵖ))ᵒᵖ :=
  { functor := Comon_ClassToMon_ClassOpOp C
    inverse := Mon_ClassOpOpToComon_Class C
    unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    counitIso := NatIso.ofComponents (fun _ => Iso.refl _) }

/--
Comonoid objects in a braided category form a monoidal category.

This definition is via transporting back and forth to monoids in the opposite category,
-/
@[simps!]
-- @[simps! tensorHom_hom whiskerLeft_hom whiskerRight_hom
--   associator_hom_hom associator_inv_hom leftUnitor_hom_hom leftUnitor_inv_hom
--   rightUnitor_hom_hom rightUnitor_inv_hom]
instance [BraidedCategory C] : MonoidalCategory (Comon_Cat C) :=
  Monoidal.transport (Comon_ClassEquivMon_ClassOpOp C).symm

variable [BraidedCategory C]

-- example (X Y Z : Comon_Cat C) : (α_ X Y Z).inv.hom = (α_ X.X Y.X Z.X).inv := by
--   dsimp only [instMonoidalCategoryComon_CatOfBraidedCategory_tensorObj_X]
--   rw [Monoidal.transportStruct_associator]
--   dsimp
--   simp

variable {C}

-- @[simp]
theorem tensorObj_X (A B : Comon_Cat C) : (A ⊗ B).X = A.X ⊗ B.X := rfl

@[instance]
def ofTensor (A B : C) [Comon_Class A] [Comon_Class B] :
    Comon_Class (A ⊗ B) :=
  inferInstanceAs <| Comon_Class (Comon_Cat.mk A ⊗ Comon_Cat.mk B).X

@[simp]
theorem ofTensor_counit (A B : C) [Comon_Class A] [Comon_Class B] :
    @Comon_Class.counit _ _ _ (A ⊗ B) (ofTensor A B) = (ε[A] ⊗ ε[B]) ≫ (λ_ _).hom :=
  rfl

/--
Preliminary statement of the comultiplication for a tensor product of comonoids.
This version is the definitional equality provided by transport, and not quite as good as
the version provided in `tensorObj_comul` below.
-/
@[simp]
theorem ofTensor_comul (A B : C) [Comon_Class A] [Comon_Class B] :
    @Comon_Class.comul _ _ _ (A ⊗ B) (ofTensor A B) =
        (Δ[A] ⊗ Δ[B]) ≫ (tensorμ (op A) (op B) (op A) (op B)).unop := by
  rfl

-- @[simps?]
-- instance (A B : C) [Comon_Class A] [Comon_Class B] : Comon_Class (A ⊗ B) where
--   counit := (ε[A] ⊗ ε[B]) ≫ (λ_ _).hom
--   /-
--   The comultiplication on the tensor product of two comonoids is
--   the tensor product of the comultiplications followed by the tensor strength
--   (to shuffle the factors back into order).
--   -/
--   comul := (Δ[A] ⊗ Δ[B]) ≫ tensor_μ C (A, A) (B, B)
--   counit_comul' := by
--     simpa [ofTensor_counit, ofTensor_comul, BraidedCategory.unop_tensor_μ] using
--       (ofTensor A B).counit_comul'
--   comul_counit' := by
--     simpa [ofTensor_counit, ofTensor_comul] using (ofTensor A B).comul_counit'
--   comul_assoc' := by
--     simpa [ofTensor_counit, ofTensor_comul] using (ofTensor A B).comul_assoc'

-- instance (A B : C) [Comon_Class A] [Comon_Class B] :
--  Comon_Class ((Comon_Cat.mk A) ⊗ (Comon_Cat.mk B)).X :=
--   inferInstanceAs (Comon_Class (A ⊗ B))

-- @[simp]
-- theorem tensorObj_counit (A B : C) [Comon_Class A] [Comon_Class B] :
--     ε[A ⊗ B] = (ε[A] ⊗ ε[B]) ≫ (λ_ _).hom :=
--   rfl

-- /--
-- Preliminary statement of the comultiplication for a tensor product of comonoids.
-- This version is the definitional equality provided by transport, and not quite as good as
-- the version provided in `tensorObj_comul` below.
-- -/
-- theorem tensorObj_comul' (A B : C) [Comon_Class A] [Comon_Class B] :
--     Δ[A ⊗ B] = (Δ[A] ⊗ Δ[B]) ≫ (tensor_μ Cᵒᵖ (op A, op B) (op A, op B)).unop := by
--   rfl

-- /--
-- The comultiplication on the tensor product of two comonoids is
-- the tensor product of the comultiplications followed by the tensor strength
-- (to shuffle the factors back into order).
-- -/
-- @[simp]
-- theorem tensorObj_comul (A B : C) [Comon_Class A] [Comon_Class B] :
--     (Δ : A ⊗ B ⟶ _) = (Δ[A] ⊗ Δ[B]) ≫ tensor_μ C (A, A) (B, B) := by
--   rw [tensorObj_comul']
--   congr
--   simp only [tensor_μ, unop_tensorObj, unop_op]
--   apply Quiver.Hom.unop_inj
--   dsimp [op_tensorObj, op_associator]
--   rw [Category.assoc, Category.assoc, Category.assoc]

end Comon_Class

namespace Comon_Cat

variable [BraidedCategory C]

-- open Comon_Class

-- attribute [local simp] Monoidal.transportStruct Monoidal.transport

variable (C)

/-- The forgetful functor from `Comon_ C` to `C` is monoidal when `C` is monoidal. -/
instance : (forget C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }

open Functor.LaxMonoidal Functor.OplaxMonoidal

@[simp] theorem forget_ε : «ε» (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_η : η (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_μ (X Y : Comon_Cat C) : μ (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl
@[simp] theorem forget_δ (X Y : Comon_Cat C) : δ (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl

end Comon_Cat

open Comon_Class

namespace CategoryTheory.Functor

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

open Functor.OplaxMonoidal

@[simps!]
def mapComonCatAux (F : C ⥤ D) [F.OplaxMonoidal] (A : C) [Comon_Class A] : Comon_Class (F.obj A) where
  counit := F.map ε ≫ η F
  comul := F.map Δ ≫ δ F _ _
  counit_comul := by
    simp_rw [comp_whiskerRight, Category.assoc, δ_natural_left_assoc, left_unitality,
      ← F.map_comp_assoc, counit_comul]
  comul_counit := by
    simp_rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, δ_natural_right_assoc,
      right_unitality, ← F.map_comp_assoc, comul_counit]
  comul_assoc := by
    simp_rw [comp_whiskerRight, Category.assoc, δ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, δ_natural_right_assoc,
      ← F.map_comp_assoc, comul_assoc, F.map_comp, Category.assoc, associativity]

/-- A oplax monoidal functor takes comonoid objects to comonoid objects.

That is, a oplax monoidal functor F : C ⥤ D induces a functor Comon_Cat C ⥤ Comon_Class D.
-/
@[simps]
def mapComonCat (F : C ⥤ D) [F.OplaxMonoidal] : Comon_Cat C ⥤ Comon_Cat D where
  obj A :=
    letI : Comon_Class (F.obj A.X) := mapComonCatAux F A.X
    Comon_Cat.mk (F.obj A.X)
  map {A B} f :=
    letI : Comon_Class (F.obj A.X) := mapComonCatAux F A.X
    letI : Comon_Class (F.obj B.X) := mapComonCatAux F B.X
    Comon_Cat.mkHom
    { hom := F.map f.hom
      hom_counit := by dsimp; rw [← F.map_comp_assoc, f.hom_counit]
      hom_comul := by
        dsimp
        rw [Category.assoc, δ_natural, ← F.map_comp_assoc, ← F.map_comp_assoc, f.hom_comul] }

-- TODO We haven't yet set up the category structure on `OplaxMonoidalFunctor C D`
-- and so can't state
-- `mapComonCatFunctor : OplaxMonoidalFunctor C D ⥤ Comon_Class C ⥤ Comon_Class D`.

end CategoryTheory.Functor
