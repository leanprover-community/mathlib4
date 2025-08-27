/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Braided.Opposite
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The category of comonoids in a monoidal category.

We define comonoids in a monoidal category `C`,
and show that they are equivalently monoid objects in the opposite category.

We construct the monoidal structure on `Comon_ C`, when `C` is braided.

An oplax monoidal functor takes comonoid objects to comonoid objects.
That is, a oplax monoidal functor `F : C ⥤ D` induces a functor `Comon_ C ⥤ Comon_ D`.

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
  counit_comul (X) : comul ≫ counit ▷ X = (λ_ X).inv := by cat_disch
  comul_counit (X) : comul ≫ X ◁ counit = (ρ_ X).inv := by cat_disch
  comul_assoc (X) : comul ≫ X ◁ comul = comul ≫ (comul ▷ X) ≫ (α_ X X X).hom := by cat_disch

namespace Comon_Class

@[inherit_doc] scoped notation "Δ" => Comon_Class.comul
@[inherit_doc] scoped notation "Δ["M"]" => Comon_Class.comul (X := M)
@[inherit_doc] scoped notation "ε" => Comon_Class.counit
@[inherit_doc] scoped notation "ε["M"]" => Comon_Class.counit (X := M)

attribute [reassoc (attr := simp)] counit_comul comul_counit comul_assoc

@[simps]
instance (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] : Comon_Class (𝟙_ C) where
  counit := 𝟙 _
  comul := (λ_ _).inv
  counit_comul := by simp
  comul_counit := by monoidal_coherence
  comul_assoc := by monoidal_coherence

end Comon_Class

open scoped Comon_Class

variable {M N O : C} [Comon_Class M] [Comon_Class N] [Comon_Class O]

/-- The property that a morphism between comonoid objects is a comonoid morphism. -/
class IsComon_Hom (f : M ⟶ N) : Prop where
  hom_counit (f) : f ≫ ε = ε := by cat_disch
  hom_comul (f) : f ≫ Δ = Δ ≫ (f ⊗ₘ f) := by cat_disch

attribute [reassoc (attr := simp)] IsComon_Hom.hom_counit IsComon_Hom.hom_comul

instance : IsComon_Hom (𝟙 M) where

instance (f : M ⟶ N) (g : N ⟶ O) [IsComon_Hom f] [IsComon_Hom g] : IsComon_Hom (f ≫ g) where

instance (f : M ≅ N) [IsComon_Hom f.hom] : IsComon_Hom f.inv where
  hom_counit := by simp [Iso.inv_comp_eq]
  hom_comul := by simp [Iso.inv_comp_eq]

instance (f : M ⟶ N) [IsComon_Hom f] [IsIso f] : IsComon_Hom (inv f) where

variable (C) in
/-- A comonoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called a "coalgebra object".
-/
structure Comon_ where
  /-- The underlying object of a comonoid object. -/
  X : C
  [comon : Comon_Class X]

attribute [instance] Comon_.comon

namespace Comon_

variable (C) in
/-- The trivial comonoid object. We later show this is terminal in `Comon_ C`.
-/
@[simps!]
def trivial : Comon_ C := mk (𝟙_ C)

instance : Inhabited (Comon_ C) :=
  ⟨trivial C⟩

end Comon_

namespace Comon_Class

variable {M : C} [Comon_Class M]

@[reassoc (attr := simp)]
theorem counit_comul_hom {Z : C} (f : M ⟶ Z) : Δ[M] ≫ (ε[M] ⊗ₘ f) = f ≫ (λ_ Z).inv := by
  rw [leftUnitor_inv_naturality, tensorHom_def, counit_comul_assoc]

@[reassoc (attr := simp)]
theorem comul_counit_hom {Z : C} (f : M ⟶ Z) : Δ[M] ≫ (f ⊗ₘ ε[M]) = f ≫ (ρ_ Z).inv := by
  rw [rightUnitor_inv_naturality, tensorHom_def', comul_counit_assoc]

@[reassoc]
theorem comul_assoc_flip (X : C) [Comon_Class X] :
    Δ ≫ Δ ▷ X = Δ ≫ X ◁ Δ ≫ (α_ X X X).inv := by
  simp

end Comon_Class

namespace Comon_

open Mon_Class Comon_Class

/-- A morphism of comonoid objects. -/
@[ext]
structure Hom (M N : Comon_ C) where
  /-- The underlying morphism of a morphism of comonoid objects. -/
  hom : M.X ⟶ N.X
  [is_comon_hom : IsComon_Hom hom]

attribute [instance] Hom.is_comon_hom

/-- Construct a morphism `M ⟶ N` of `Comon_ C` from a map `f : M ⟶ N` and a `IsComon_Hom f`
instance. -/
abbrev Hom.mk' {M N : Comon_ C} (f : M.X ⟶ N.X)
    (f_counit : f ≫ ε[N.X] = ε[M.X] := by cat_disch)
    (f_comul : f ≫ Δ[N.X] = Δ[M.X] ≫ (f ⊗ₘ f) := by cat_disch) :
    Hom M N :=
  have : IsComon_Hom f := ⟨f_counit, f_comul⟩
  .mk f

/-- The identity morphism on a comonoid object. -/
@[simps]
def id (M : Comon_ C) : Hom M M where
  hom := 𝟙 M.X

instance homInhabited (M : Comon_ C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : Comon_ C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

instance : Category (Comon_ C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

instance {M N : Comon_ C} (f : M ⟶ N) : IsComon_Hom f.hom := inferInstanceAs (IsComon_Hom f.hom)

@[ext] lemma ext {X Y : Comon_ C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g := Hom.ext w

@[simp] theorem id_hom' (M : Comon_ C) : (𝟙 M : Hom M M).hom = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Comon_ C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

section

variable (C)

/-- The forgetful functor from comonoid objects to the ambient category. -/
@[simps]
def forget : Comon_ C ⥤ C where
  obj A := A.X
  map f := f.hom

end

instance forget_faithful : (@forget C _ _).Faithful where

instance {A B : Comon_ C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom := e

/-- The forgetful functor from comonoid objects to the ambient category reflects isomorphisms. -/
instance : (forget C).ReflectsIsomorphisms where
  reflects f e :=
    ⟨⟨{ hom := inv f.hom }, by cat_disch⟩⟩

/-- Construct an isomorphism of comonoids by giving an isomorphism between the underlying objects
and checking compatibility with counit and comultiplication only in the forward direction.
-/
@[simps]
def mkIso' {M N : Comon_ C} (f : M.X ≅ N.X) [IsComon_Hom f.hom] : M ≅ N where
  hom := Hom.mk f.hom
  inv := Hom.mk f.inv

/-- Construct an isomorphism of comonoids by giving an isomorphism between the underlying objects
and checking compatibility with counit and comultiplication only in the forward direction.
-/
@[simps]
def mkIso {M N : Comon_ C} (f : M.X ≅ N.X) (f_counit : f.hom ≫ ε[N.X] = ε[M.X] := by cat_disch)
    (f_comul : f.hom ≫ Δ[N.X] = Δ[M.X] ≫ (f.hom ⊗ₘ f.hom) := by cat_disch) : M ≅ N :=
  have : IsComon_Hom f.hom := ⟨f_counit, f_comul⟩
  ⟨⟨f.hom⟩, ⟨f.inv⟩, by cat_disch, by cat_disch⟩

@[simps]
instance uniqueHomToTrivial (A : Comon_ C) : Unique (A ⟶ trivial C) where
  default :=
    { hom := ε[A.X]
      is_comon_hom :=
        { hom_comul := by simp [unitors_inv_equal] } }
  uniq f := by
    ext
    rw [← Category.comp_id f.hom]
    dsimp only [trivial_X]
    rw [← trivial_comon_counit, IsComon_Hom.hom_counit]

open CategoryTheory.Limits

instance : HasTerminal (Comon_ C) :=
  hasTerminal_of_unique (trivial C)

open Opposite

/-- Auxiliary definition for `Comon_ToMon_OpOpObj`. -/
abbrev Comon_ToMon_OpOpObjMon (A : Comon_ C) : Mon_Class (op A.X) where
  one := ε[A.X].op
  mul := Δ[A.X].op
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

/--
Turn a comonoid object into a monoid object in the opposite category.
-/
@[simps] def Comon_ToMon_OpOpObj (A : Comon_ C) : Mon_ (Cᵒᵖ) where
  X := op A.X
  mon := Comon_ToMon_OpOpObjMon A

variable (C) in
/--
The contravariant functor turning comonoid objects into monoid objects in the opposite category.
-/
@[simps] def Comon_ToMon_OpOp : Comon_ C ⥤ (Mon_ (Cᵒᵖ))ᵒᵖ where
  obj A := op (Comon_ToMon_OpOpObj A)
  map := fun f => op <|
    { hom := f.hom.op
      is_mon_hom :=
        { one_hom := by apply Quiver.Hom.unop_inj; simp
          mul_hom := by apply Quiver.Hom.unop_inj; simp } }

/-- Auxiliary definition for `Mon_OpOpToComonObj`. -/
abbrev Mon_OpOpToComonObjComon (A : Mon_ (Cᵒᵖ)) : Comon_Class (unop A.X) where
  counit := η[A.X].unop
  comul := μ[A.X].unop
  counit_comul := by rw [← unop_whiskerRight, ← unop_comp, Mon_Class.one_mul]; rfl
  comul_counit := by rw [← unop_whiskerLeft, ← unop_comp, Mon_Class.mul_one]; rfl
  comul_assoc := by
    rw [← unop_whiskerRight, ← unop_whiskerLeft, ← unop_comp_assoc, ← unop_comp,
      Mon_Class.mul_assoc_flip]
    rfl

/--
Turn a monoid object in the opposite category into a comonoid object.
-/
@[simps] def Mon_OpOpToComonObj (A : (Mon_ (Cᵒᵖ))) : Comon_ C where
  X := unop A.X
  comon := Mon_OpOpToComonObjComon A

variable (C)

/--
The contravariant functor turning monoid objects in the opposite category into comonoid objects.
-/
@[simps]
def Mon_OpOpToComon_ : (Mon_ (Cᵒᵖ))ᵒᵖ ⥤ Comon_ C where
  obj A := Mon_OpOpToComonObj (unop A)
  map := fun f =>
    { hom := f.unop.hom.unop
      is_comon_hom :=
        { hom_counit := by apply Quiver.Hom.op_inj; simp
          hom_comul := by apply Quiver.Hom.op_inj; simp [op_tensorHom] } }

/--
Comonoid objects are contravariantly equivalent to monoid objects in the opposite category.
-/
@[simps]
def Comon_EquivMon_OpOp : Comon_ C ≌ (Mon_ (Cᵒᵖ))ᵒᵖ :=
  { functor := Comon_ToMon_OpOp C
    inverse := Mon_OpOpToComon_ C
    unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    counitIso := NatIso.ofComponents (fun _ => Iso.refl _) }

/--
Comonoid objects in a braided category form a monoidal category.

This definition is via transporting back and forth to monoids in the opposite category.
-/
@[simps!]
instance monoidal [BraidedCategory C] : MonoidalCategory (Comon_ C) :=
  Monoidal.transport (Comon_EquivMon_OpOp C).symm

variable {C} [BraidedCategory C]

theorem tensorObj_X (A B : Comon_ C) : (A ⊗ B).X = A.X ⊗ B.X := rfl

instance (A B : C) [Comon_Class A] [Comon_Class B] : Comon_Class (A ⊗ B) :=
  inferInstanceAs <| Comon_Class (Comon_.mk A ⊗ Comon_.mk B).X

@[simp]
theorem tensorObj_counit (A B : C) [Comon_Class A] [Comon_Class B] :
    ε[A ⊗ B] = (ε[A] ⊗ₘ ε[B]) ≫ (λ_ _).hom :=
  rfl

/--
Preliminary statement of the comultiplication for a tensor product of comonoids.
This version is the definitional equality provided by transport, and not quite as good as
the version provided in `tensorObj_comul` below.
-/
theorem tensorObj_comul' (A B : C) [Comon_Class A] [Comon_Class B] :
    Δ[A ⊗ B] =
      (Δ[A] ⊗ₘ Δ[B]) ≫ (tensorμ (op A) (op B) (op A) (op B)).unop := rfl

/--
The comultiplication on the tensor product of two comonoids is
the tensor product of the comultiplications followed by the tensor strength
(to shuffle the factors back into order).
-/
@[simp]
theorem tensorObj_comul (A B : C) [Comon_Class A] [Comon_Class B] :
    Δ[A ⊗ B] = (Δ[A] ⊗ₘ Δ[B]) ≫ tensorμ A A B B := by
  rw [tensorObj_comul']
  congr
  simp only [tensorμ, unop_tensorObj, unop_op]
  apply Quiver.Hom.unop_inj
  dsimp [op_tensorObj, op_associator]
  rw [Category.assoc, Category.assoc, Category.assoc]

/-- The forgetful functor from `Comon_ C` to `C` is monoidal when `C` is monoidal. -/
instance : (forget C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }

open Functor.LaxMonoidal Functor.OplaxMonoidal

@[simp] theorem forget_ε : «ε» (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_η : «η» (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_μ (X Y : Comon_ C) : «μ» (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl
@[simp] theorem forget_δ (X Y : Comon_ C) : δ (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl

end Comon_

namespace CategoryTheory.Functor

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

open OplaxMonoidal Comon_Class IsComon_Hom

/-- The image of a comonoid object under a oplax monoidal functor is a comonoid object. -/
abbrev obj.instComon_Class (A : C) [Comon_Class A] (F : C ⥤ D) [F.OplaxMonoidal] :
    Comon_Class (F.obj A) where
  counit := F.map ε[A] ≫ η F
  comul := F.map Δ[A] ≫ δ F _ _
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

attribute [local instance] obj.instComon_Class

@[reassoc, simp] lemma obj.ε_def (F : C ⥤ D) [F.OplaxMonoidal] (X : C) [Comon_Class X] :
    ε[F.obj X] = F.map ε ≫ η F :=
  rfl

@[reassoc, simp] lemma obj.Δ_def (F : C ⥤ D) [F.OplaxMonoidal] (X : C) [Comon_Class X] :
    Δ[F.obj X] = F.map Δ ≫ δ F _ _ :=
  rfl

instance map.instIsComon_Hom
    (F : C ⥤ D) [F.OplaxMonoidal]
    {X Y : C} [Comon_Class X] [Comon_Class Y] (f : X ⟶ Y) [IsComon_Hom f] :
    IsComon_Hom (F.map f) where
  hom_counit := by dsimp; rw [← F.map_comp_assoc, hom_counit]
  hom_comul := by
    dsimp
    rw [Category.assoc, δ_natural, ← F.map_comp_assoc, ← F.map_comp_assoc, hom_comul]

/-- A oplax monoidal functor takes comonoid objects to comonoid objects.

That is, a oplax monoidal functor `F : C ⥤ D` induces a functor `Comon_ C ⥤ Comon_ D`.
-/
@[simps]
def mapComon (F : C ⥤ D) [F.OplaxMonoidal] : Comon_ C ⥤ Comon_ D where
  obj A :=
    { X := F.obj A.X }
  map f :=
    { hom := F.map f.hom }
  map_id A := by ext; simp
  map_comp f g := by ext; simp

-- TODO We haven't yet set up the category structure on `OplaxMonoidalFunctor C D`
-- and so can't state `mapComonFunctor : OplaxMonoidalFunctor C D ⥤ Comon_ C ⥤ Comon_ D`.

end CategoryTheory.Functor
