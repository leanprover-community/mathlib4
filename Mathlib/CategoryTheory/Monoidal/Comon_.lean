/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon_
public import Mathlib.CategoryTheory.Monoidal.Braided.Opposite
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The category of comonoids in a monoidal category.

We define comonoids in a monoidal category `C`,
and show that they are equivalently monoid objects in the opposite category.

We construct the monoidal structure on `Comon C`, when `C` is braided.

An oplax monoidal functor takes comonoid objects to comonoid objects.
That is, an oplax monoidal functor `F : C ⥤ D` induces a functor `Comon C ⥤ Comon D`.

## TODO
* Comonoid objects in `C` are "just"
  oplax monoidal functors from the trivial monoidal category to `C`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- A comonoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called a "coalgebra object".
-/
class ComonObj (X : C) where
  /-- The counit morphism of a comonoid object. -/
  counit : X ⟶ 𝟙_ C
  /-- The comultiplication morphism of a comonoid object. -/
  comul : X ⟶ X ⊗ X
  counit_comul (X) : comul ≫ counit ▷ X = (λ_ X).inv := by cat_disch
  comul_counit (X) : comul ≫ X ◁ counit = (ρ_ X).inv := by cat_disch
  comul_assoc (X) : comul ≫ X ◁ comul = comul ≫ (comul ▷ X) ≫ (α_ X X X).hom := by cat_disch

namespace ComonObj

@[inherit_doc] scoped notation "Δ" => ComonObj.comul
@[inherit_doc] scoped notation "Δ[" M "]" => ComonObj.comul (X := M)
@[inherit_doc] scoped notation "ε" => ComonObj.counit
@[inherit_doc] scoped notation "ε[" M "]" => ComonObj.counit (X := M)

attribute [reassoc (attr := simp)] counit_comul comul_counit comul_assoc

/-- The canonical comonoid structure on the monoidal unit.
This is not a global instance to avoid conflicts with other comonoid structures. -/
@[instance_reducible, simps]
def instTensorUnit (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] : ComonObj (𝟙_ C) where
  counit := 𝟙 _
  comul := (λ_ _).inv
  counit_comul := by simp
  comul_counit := by monoidal_coherence
  comul_assoc := by monoidal_coherence

end ComonObj

open scoped ComonObj

variable {M N O : C} [ComonObj M] [ComonObj N] [ComonObj O]

/-- The property that a morphism between comonoid objects is a comonoid morphism. -/
class IsComonHom (f : M ⟶ N) : Prop where
  hom_counit (f) : f ≫ ε = ε := by cat_disch
  hom_comul (f) : f ≫ Δ = Δ ≫ (f ⊗ₘ f) := by cat_disch

attribute [reassoc (attr := simp)] IsComonHom.hom_counit IsComonHom.hom_comul

instance : IsComonHom (𝟙 M) where

instance (f : M ⟶ N) (g : N ⟶ O) [IsComonHom f] [IsComonHom g] : IsComonHom (f ≫ g) where

instance (f : M ≅ N) [IsComonHom f.hom] : IsComonHom f.inv where
  hom_counit := by simp [Iso.inv_comp_eq]
  hom_comul := by simp [Iso.inv_comp_eq]

instance (f : M ⟶ N) [IsComonHom f] [IsIso f] : IsComonHom (inv f) where

variable (C) in
/-- A comonoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called a "coalgebra object".
-/
structure Comon where
  /-- The underlying object of a comonoid object. -/
  X : C
  [comon : ComonObj X]

attribute [instance] Comon.comon

namespace Comon

attribute [local instance] ComonObj.instTensorUnit in
variable (C) in
/-- The trivial comonoid object. We later show this is terminal in `Comon C`.
-/
@[simps!]
def trivial : Comon C := mk (𝟙_ C)

instance : Inhabited (Comon C) :=
  ⟨trivial C⟩

end Comon

namespace ComonObj

variable {M : C} [ComonObj M]

@[reassoc (attr := simp)]
theorem counit_comul_hom {Z : C} (f : M ⟶ Z) : Δ[M] ≫ (ε[M] ⊗ₘ f) = f ≫ (λ_ Z).inv := by
  rw [leftUnitor_inv_naturality, tensorHom_def, counit_comul_assoc]

@[reassoc (attr := simp)]
theorem comul_counit_hom {Z : C} (f : M ⟶ Z) : Δ[M] ≫ (f ⊗ₘ ε[M]) = f ≫ (ρ_ Z).inv := by
  rw [rightUnitor_inv_naturality, tensorHom_def', comul_counit_assoc]

@[reassoc]
theorem comul_assoc_flip (X : C) [ComonObj X] :
    Δ ≫ Δ ▷ X = Δ ≫ X ◁ Δ ≫ (α_ X X X).inv := by
  simp

end ComonObj

namespace Comon

open MonObj ComonObj

/-- A morphism of comonoid objects. -/
@[ext]
structure Hom (M N : Comon C) where
  /-- The underlying morphism of a morphism of comonoid objects. -/
  hom : M.X ⟶ N.X
  [isComonHom_hom : IsComonHom hom]

attribute [instance] Hom.isComonHom_hom

/-- Construct a morphism `M ⟶ N` of `Comon C` from a map `f : M ⟶ N` and a `IsComonHom f`
instance. -/
abbrev Hom.mk' {M N : Comon C} (f : M.X ⟶ N.X)
    (f_counit : f ≫ ε[N.X] = ε[M.X] := by cat_disch)
    (f_comul : f ≫ Δ[N.X] = Δ[M.X] ≫ (f ⊗ₘ f) := by cat_disch) :
    Hom M N :=
  have : IsComonHom f := ⟨f_counit, f_comul⟩
  .mk f

/-- The identity morphism on a comonoid object. -/
@[simps]
def id (M : Comon C) : Hom M M where
  hom := 𝟙 M.X

instance homInhabited (M : Comon C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : Comon C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

instance : Category (Comon C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

instance {M N : Comon C} (f : M ⟶ N) : IsComonHom f.hom := inferInstanceAs (IsComonHom f.hom)

@[ext] lemma ext {X Y : Comon C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g := Hom.ext w

@[simp] theorem id_hom' (M : Comon C) : (𝟙 M : Hom M M).hom = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Comon C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

section

variable (C)

/-- The forgetful functor from comonoid objects to the ambient category. -/
@[simps]
def forget : Comon C ⥤ C where
  obj A := A.X
  map f := f.hom

end

instance forget_faithful : (@forget C _ _).Faithful where

instance {A B : Comon C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom := e

/-- The forgetful functor from comonoid objects to the ambient category reflects isomorphisms. -/
instance : (forget C).ReflectsIsomorphisms where
  reflects f e :=
    ⟨⟨{ hom := inv f.hom }, by cat_disch⟩⟩

/-- Construct an isomorphism of comonoids by giving an isomorphism between the underlying objects
and checking compatibility with counit and comultiplication only in the forward direction.
-/
@[simps]
def mkIso' {M N : Comon C} (f : M.X ≅ N.X) [IsComonHom f.hom] : M ≅ N where
  hom := Hom.mk f.hom
  inv := Hom.mk f.inv

/-- Construct an isomorphism of comonoids by giving an isomorphism between the underlying objects
and checking compatibility with counit and comultiplication only in the forward direction.
-/
@[simps]
def mkIso {M N : Comon C} (f : M.X ≅ N.X) (f_counit : f.hom ≫ ε[N.X] = ε[M.X] := by cat_disch)
    (f_comul : f.hom ≫ Δ[N.X] = Δ[M.X] ≫ (f.hom ⊗ₘ f.hom) := by cat_disch) : M ≅ N :=
  have : IsComonHom f.hom := ⟨f_counit, f_comul⟩
  ⟨⟨f.hom⟩, ⟨f.inv⟩, by cat_disch, by cat_disch⟩

set_option backward.isDefEq.respectTransparency false in
@[simps]
instance uniqueHomToTrivial (A : Comon C) : Unique (A ⟶ trivial C) where
  default.hom := ε[A.X]
  default.isComonHom_hom.hom_comul := by simp [unitors_inv_equal]
  uniq f := by
    ext
    rw [← Category.comp_id f.hom]
    dsimp only [trivial_X]
    rw [← trivial_comon_counit, IsComonHom.hom_counit]

open CategoryTheory.Limits

instance : HasTerminal (Comon C) :=
  hasTerminal_of_unique (trivial C)

open Opposite

/-- Auxiliary definition for `ComonToMonOpOpObj`. -/
abbrev ComonToMonOpOpObjMon (A : Comon C) : MonObj (op A.X) where
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
@[simps] def ComonToMonOpOpObj (A : Comon C) : Mon Cᵒᵖ where
  X := op A.X
  mon := ComonToMonOpOpObjMon A

variable (C) in
/--
The contravariant functor turning comonoid objects into monoid objects in the opposite category.
-/
@[simps] def ComonToMonOpOp : Comon C ⥤ (Mon Cᵒᵖ)ᵒᵖ where
  obj A := op (ComonToMonOpOpObj A)
  map := fun f => op <|
    { hom := f.hom.op
      isMonHom_hom.one_hom := by apply Quiver.Hom.unop_inj; simp
      isMonHom_hom.mul_hom := by apply Quiver.Hom.unop_inj; simp }

/-- Auxiliary definition for `MonOpOpToComonObj`. -/
abbrev MonOpOpToComonObjComon (A : Mon Cᵒᵖ) : ComonObj (unop A.X) where
  counit := η[A.X].unop
  comul := μ[A.X].unop
  counit_comul := by rw [← unop_whiskerRight, ← unop_comp, MonObj.one_mul]; rfl
  comul_counit := by rw [← unop_whiskerLeft, ← unop_comp, MonObj.mul_one]; rfl
  comul_assoc := by
    rw [← unop_whiskerRight, ← unop_whiskerLeft, ← unop_comp_assoc, ← unop_comp,
      MonObj.mul_assoc_flip]
    rfl

/--
Turn a monoid object in the opposite category into a comonoid object.
-/
@[simps] def MonOpOpToComonObj (A : Mon Cᵒᵖ) : Comon C where
  X := unop A.X
  comon := MonOpOpToComonObjComon A

variable (C)

/--
The contravariant functor turning monoid objects in the opposite category into comonoid objects.
-/
@[simps]
def MonOpOpToComon : (Mon Cᵒᵖ)ᵒᵖ ⥤ Comon C where
  obj A := MonOpOpToComonObj (unop A)
  map := fun f =>
    { hom := f.unop.hom.unop
      isComonHom_hom.hom_counit := by apply Quiver.Hom.op_inj; simp
      isComonHom_hom.hom_comul := by apply Quiver.Hom.op_inj; simp [op_tensorHom] }

set_option backward.isDefEq.respectTransparency false in
/--
Comonoid objects are contravariantly equivalent to monoid objects in the opposite category.
-/
@[simps]
def Comon_EquivMon_OpOp : Comon C ≌ (Mon Cᵒᵖ)ᵒᵖ where
  functor := ComonToMonOpOp C
  inverse := MonOpOpToComon C
  unitIso := NatIso.ofComponents fun _ => .refl _
  counitIso := NatIso.ofComponents fun _ => .refl _

#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12179
the simpNF linter complains about `monoidal_tensorObj_comon_counit` being `@[simp]`.
So we spell out all the other ones.
-/
/--
Comonoid objects in a braided category form a monoidal category.

This definition is via transporting back and forth to monoids in the opposite category.
-/
@[simps!
  tensorObj_X tensorObj_comon_comul
  whiskerLeft_hom whiskerRight_hom
  tensorHom_hom
  tensorUnit_X tensorUnit_comon_counit tensorUnit_comon_comul
  associator_hom_hom associator_inv_hom
  leftUnitor_hom_hom leftUnitor_inv_hom
  rightUnitor_hom_hom rightUnitor_inv_hom]
instance monoidal [BraidedCategory C] : MonoidalCategory (Comon C) :=
  Monoidal.transport (Comon_EquivMon_OpOp C).symm

variable {C} [BraidedCategory C]

theorem tensorObj_X (A B : Comon C) : (A ⊗ B).X = A.X ⊗ B.X := rfl

instance (A B : C) [ComonObj A] [ComonObj B] : ComonObj (A ⊗ B) :=
  inferInstanceAs <| ComonObj (Comon.mk A ⊗ Comon.mk B).X

@[simp]
theorem tensorObj_counit (A B : C) [ComonObj A] [ComonObj B] :
    ε[A ⊗ B] = (ε[A] ⊗ₘ ε[B]) ≫ (λ_ _).hom :=
  rfl

/--
Preliminary statement of the comultiplication for a tensor product of comonoids.
This version is the definitional equality provided by transport, and not quite as good as
the version provided in `tensorObj_comul` below.
-/
theorem tensorObj_comul' (A B : C) [ComonObj A] [ComonObj B] :
    Δ[A ⊗ B] =
      (Δ[A] ⊗ₘ Δ[B]) ≫ (tensorμ (op A) (op B) (op A) (op B)).unop := by
  rfl

/--
The comultiplication on the tensor product of two comonoids is
the tensor product of the comultiplications followed by the tensor strength
(to shuffle the factors back into order).
-/
@[simp]
theorem tensorObj_comul (A B : C) [ComonObj A] [ComonObj B] :
    Δ[A ⊗ B] = (Δ[A] ⊗ₘ Δ[B]) ≫ tensorμ A A B B := by
  simp [tensorObj_comul']

set_option backward.isDefEq.respectTransparency false in
/-- The forgetful functor from `Comon C` to `C` is monoidal when `C` is monoidal. -/
instance : (forget C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }

open Functor.LaxMonoidal Functor.OplaxMonoidal

@[simp] theorem forget_ε : «ε» (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_η : «η» (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_μ (X Y : Comon C) : «μ» (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl
@[simp] theorem forget_δ (X Y : Comon C) : δ (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl

end Comon

namespace Functor

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

open OplaxMonoidal ComonObj IsComonHom

/-- The image of a comonoid object under an oplax monoidal functor is a comonoid object. -/
abbrev obj.instComonObj (A : C) [ComonObj A] (F : C ⥤ D) [F.OplaxMonoidal] :
    ComonObj (F.obj A) where
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

attribute [local instance] obj.instComonObj

@[reassoc, simp] lemma obj.ε_def (F : C ⥤ D) [F.OplaxMonoidal] (X : C) [ComonObj X] :
    ε[F.obj X] = F.map ε ≫ η F :=
  rfl

@[reassoc, simp] lemma obj.Δ_def (F : C ⥤ D) [F.OplaxMonoidal] (X : C) [ComonObj X] :
    Δ[F.obj X] = F.map Δ ≫ δ F _ _ :=
  rfl

instance map.instIsComon_Hom
    (F : C ⥤ D) [F.OplaxMonoidal]
    {X Y : C} [ComonObj X] [ComonObj Y] (f : X ⟶ Y) [IsComonHom f] :
    IsComonHom (F.map f) where
  hom_counit := by dsimp; rw [← F.map_comp_assoc, hom_counit]
  hom_comul := by
    dsimp
    rw [Category.assoc, δ_natural, ← F.map_comp_assoc, ← F.map_comp_assoc, hom_comul]

/-- An oplax monoidal functor takes comonoid objects to comonoid objects.

That is, an oplax monoidal functor `F : C ⥤ D` induces a functor `Comon C ⥤ Comon D`.
-/
@[simps]
def mapComon (F : C ⥤ D) [F.OplaxMonoidal] : Comon C ⥤ Comon D where
  obj A :=
    { X := F.obj A.X }
  map f :=
    { hom := F.map f.hom }
  map_id A := by ext; simp
  map_comp f g := by ext; simp

-- TODO We haven't yet set up the category structure on `OplaxMonoidalFunctor C D`
-- and so can't state `mapComonFunctor : OplaxMonoidalFunctor C D ⥤ Comon C ⥤ Comon D`.

end Functor

variable [BraidedCategory.{v₁} C]

/-- Predicate for a comonoid object to be commutative. -/
class IsCommComonObj (X : C) [ComonObj X] where
  comul_comm (X) : Δ ≫ (β_ X X).hom = Δ := by cat_disch

open scoped ComonObj

attribute [reassoc (attr := simp)] IsCommComonObj.comul_comm

end CategoryTheory
