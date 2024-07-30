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
  counit_comul' : comul ≫ (counit ▷ X) = (λ_ X).inv := by aesop_cat
  comul_counit' : comul ≫ (X ◁ counit) = (ρ_ X).inv := by aesop_cat
  comul_assoc' : comul ≫ (X ◁ comul) = comul ≫ (comul ▷ X) ≫ (α_ X X X).hom := by aesop_cat

namespace Comon_Class

@[inherit_doc] scoped notation "Δ" => Comon_Class.comul
@[inherit_doc] scoped notation "ε" => Comon_Class.counit

@[reassoc, simp]
theorem counit_comul (X : C) [Comon_Class X] : Δ ≫ (ε ▷ X) = (λ_ X).inv := counit_comul'

@[reassoc, simp]
theorem comul_counit (X : C) [Comon_Class X] : Δ ≫ (X ◁ ε) = (ρ_ X).inv := comul_counit'

@[reassoc (attr := simp)]
theorem comul_assoc (X : C) [Comon_Class X] : Δ ≫ (X ◁ Δ) = Δ ≫ (Δ ▷ X) ≫ (α_ X X X).hom := comul_assoc'

/-- The trivial comonoid object. We later show this is terminal in `Comon_Cat C`.
-/
@[simps]
instance trivial (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] : Comon_Class (𝟙_ C) where
  counit := 𝟙 _
  comul := (λ_ _).inv
  comul_assoc' := by coherence
  counit_comul' := by coherence
  comul_counit' := by coherence

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

/-- A morphism of comonoid objects. -/
@[ext]
structure Hom (M N : C) [Comon_Class M] [Comon_Class N] where
  hom : M ⟶ N
  hom_counit : hom ≫ ε = ε := by aesop_cat
  hom_comul : hom ≫ Δ = Δ ≫ (hom ⊗ hom) := by aesop_cat

attribute [reassoc (attr := simp)] Hom.hom_counit Hom.hom_comul

/-- The identity morphism on a comonoid object. -/
@[simps]
def Hom.id (M : C) [Comon_Class M] : Hom M M where
  hom := 𝟙 M

instance homInhabited (M : C) [Comon_Class M] : Inhabited (Hom M M) :=
  ⟨Hom.id M⟩

/-- Composition of morphisms of comonoid objects. -/
@[simps]
def Hom.comp {M N O : C} [Comon_Class M] [Comon_Class N] [Comon_Class O] (f : Hom M N) (g : Hom N O) :
    Hom M O where
  hom := f.hom ≫ g.hom

@[ext]
structure Iso (M N : C) [Comon_Class M] [Comon_Class N] where
  hom : Hom M N
  inv : Hom N M
  hom_inv_id : hom.hom ≫ inv.hom = 𝟙 M := by aesop_cat
  inv_hom_id : inv.hom ≫ hom.hom = 𝟙 N := by aesop_cat

attribute [simp] Iso.hom_inv_id Iso.inv_hom_id

end Comon_Class

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
  Hom M N := Comon_Class.Hom M.X N.X
  id M := Comon_Class.Hom.id M.X
  comp f g := Comon_Class.Hom.comp f g

-- @[simp]
theorem mk_X (X : Comon_Cat C) : Comon_Cat.mk X.X = X :=
  rfl

def mkHom {X Y : C} [Comon_Class X] [Comon_Class Y] (f : Comon_Class.Hom X Y) :
    mk X ⟶ mk Y :=
  f

@[simp]
theorem mkHom_hom {X Y : C} [Comon_Class X] [Comon_Class Y] (f : Hom X Y) : (mkHom f).hom = f.hom :=
  rfl

-- Porting note: added, as Hom.ext does not apply to a morphism.
@[ext]
lemma Hom.ext' {X Y : Comon_Cat C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g :=
  Hom.ext _ _ w

@[simp]
theorem id_hom' {M : Comon_Cat C} : (𝟙 M : Hom M.X M.X).hom = 𝟙 M.X :=
  rfl

@[simp]
theorem comp_hom' {M N K : Comon_Cat C} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[simps]
def mkIso {X Y : C} [Comon_Class X] [Comon_Class Y] (f : Comon_Class.Iso X Y) :
    mk X ≅ mk Y where
  hom := f.hom
  inv := f.inv

section

variable (C)

/-- The forgetful functor from comonoid objects to the ambient category. -/
@[simps]
def forget : Comon_Cat C ⥤ C where
  obj A := A.X
  map f := f.hom

end

instance forget_faithful : (forget C).Faithful where

instance {A B : C} [Comon_Class A] [Comon_Class B] (f : Hom A B)
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

/-- Construct an isomorphism of comonoids by giving an isomorphism between the underlying objects
and checking compatibility with counit and comultiplication only in the forward direction.
-/
@[simps]
def mkIso {M N : C} [Comon_Class M] [Comon_Class N] (f : M ≅ N) (f_counit : f.hom ≫ ε = ε)
    (f_comul : f.hom ≫ Δ = Δ ≫ (f.hom ⊗ f.hom)) :
    Iso M N where
  hom := { hom := f.hom }
  inv := {
    hom := f.inv
    hom_counit := by rw [← f_counit]; simp
    hom_comul := by
      rw [← cancel_epi f.hom]
      slice_rhs 1 2 => rw [f_comul]
      simp }

instance uniqueHomToTrivial (A : C) [Comon_Class A] : Unique (Hom A (𝟙_ C)) where
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
  one_mul' := by
    rw [← op_whiskerRight, ← op_comp, counit_comul]
    rfl
  mul_one' := by
    rw [← op_whiskerLeft, ← op_comp, comul_counit]
    rfl
  mul_assoc' := by
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
  counit_comul' := by rw [← unop_whiskerRight, ← unop_comp, Mon_Class.one_mul]; rfl
  comul_counit' := by rw [← unop_whiskerLeft, ← unop_comp, Mon_Class.mul_one]; rfl
  comul_assoc' := by
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
instance [BraidedCategory C] : MonoidalCategory (Comon_Cat C) :=
  Monoidal.transport (Comon_ClassEquivMon_ClassOpOp C).symm

variable [BraidedCategory C]

instance (A B : C) [Comon_Class A] [Comon_Class B] :
  Comon_Class (A ⊗ B) := Comon_Cat.isComon_Class (Comon_Cat.mk ((Comon_Cat.mk A) ⊗ (Comon_Cat.mk B)).X)

@[simp]
theorem tensorObj_X (A B : Comon_Cat C) : (A ⊗ B).X = A.X ⊗ B.X := rfl

@[simp]
theorem tensorObj_counit (A B : C) [Comon_Class A] [Comon_Class B] :
    (ε : A ⊗ B ⟶ _) = (ε ⊗ ε) ≫ (λ_ _).hom :=
  rfl

/--
Preliminary statement of the comultiplication for a tensor product of comonoids.
This version is the definitional equality provided by transport, and not quite as good as
the version provided in `tensorObj_comul` below.
-/
theorem tensorObj_comul' (A B : C) [Comon_Class A] [Comon_Class B] :
    (Δ : A ⊗ B ⟶ _) =
      (Δ ⊗ Δ) ≫ (tensor_μ Cᵒᵖ (op A, op B) (op A, op B)).unop := by
  rfl

/--
The comultiplication on the tensor product of two comonoids is
the tensor product of the comultiplications followed by the tensor strength
(to shuffle the factors back into order).
-/
@[simp]
theorem tensorObj_comul (A B : C) [Comon_Class A] [Comon_Class B] :
    (Δ : A ⊗ B ⟶ _) = (Δ ⊗ Δ) ≫ tensor_μ C (A, A) (B, B) := by
  rw [tensorObj_comul']
  congr
  simp only [tensor_μ, unop_tensorObj, unop_op]
  apply Quiver.Hom.unop_inj
  dsimp [op_tensorObj, op_associator]
  rw [Category.assoc, Category.assoc, Category.assoc]

end Comon_Class

namespace Comon_Cat

variable [BraidedCategory C]

-- open Comon_Class

variable (C)

/-- The forgetful functor from `Comon_Class C` to `C` is monoidal when `C` is braided monoidal. -/
def forgetMonoidal : MonoidalFunctor (Comon_Cat C) C :=
  { forget C with
    «ε» := 𝟙 _
    «μ» := fun X Y => 𝟙 _ }

@[simp low]
theorem forgetMonoidal_toFunctor : (forgetMonoidal C).toFunctor = forget C := rfl
@[simp] theorem forgetMonoidal_ε : (forgetMonoidal C).ε = 𝟙 (𝟙_ C) := rfl
variable {C} in
@[simp] theorem forgetMonoidal_μ
    (X Y : Comon_Cat C) : (forgetMonoidal C).μ X Y = 𝟙 (X.X ⊗ Y.X) := rfl

end Comon_Cat

open Comon_Class

namespace CategoryTheory.OplaxMonoidalFunctor

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

@[simps?]
instance (F : OplaxMonoidalFunctor C D) {A : C} [Comon_Class A] : Comon_Class (F.obj A) where
  counit := F.map ε ≫ F.η
  comul := F.map Δ ≫ F.δ _ _
  counit_comul' := by
    simp_rw [comp_whiskerRight, Category.assoc, F.δ_natural_left_assoc, F.left_unitality,
      ← F.map_comp_assoc, counit_comul]
  comul_counit' := by
        simp_rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, F.δ_natural_right_assoc,
          F.right_unitality, ← F.map_comp_assoc, comul_counit]
  comul_assoc' := by
    simp_rw [comp_whiskerRight, Category.assoc, F.δ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, F.δ_natural_right_assoc,
      ← F.map_comp_assoc, comul_assoc, F.map_comp, Category.assoc, F.associativity]

/-- A oplax monoidal functor takes comonoid objects to comonoid objects.

That is, a oplax monoidal functor F : C ⥤ D induces a functor Comon_Cat C ⥤ Comon_Class D.
-/
@[simps?]
def mapComon (F : OplaxMonoidalFunctor C D) : Comon_Cat C ⥤ Comon_Cat D where
  obj A := Comon_Cat.mk (F.obj A.X)
  map {A B} f := Comon_Cat.mkHom
    { hom := F.map f.hom
      hom_counit := by dsimp; rw [← F.map_comp_assoc, f.hom_counit]
      hom_comul := by
        dsimp
        rw [Category.assoc, F.δ_natural, ← F.map_comp_assoc, ← F.map_comp_assoc, f.hom_comul] }

-- TODO We haven't yet set up the category structure on `OplaxMonoidalFunctor C D`
-- and so can't state `mapComonFunctor : OplaxMonoidalFunctor C D ⥤ Comon_Class C ⥤ Comon_Class D`.

end CategoryTheory.OplaxMonoidalFunctor
