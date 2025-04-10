/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon_
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# The category of groups in a cartesian monoidal category

We define group objects in cartesian monoidal categories.

We show that the associativity diagram of a group object is always cartesian and deduce that
morphisms of group objects commute with taking inverses.

We show that a finite-product-preserving functor takes group objects to group objects.
-/

universe v₁ v₂ u₁ u₂ u

open CategoryTheory Category Limits MonoidalCategory ChosenFiniteProducts Mon_

variable (C : Type u₁) [Category.{v₁} C] [ChosenFiniteProducts.{v₁} C]

section

variable {C}

/-- A group object internal to a cartesian monoidal category. Also see the bundled `Grp_`. -/
class Grp_Class (X : C) extends Mon_Class X where
  /-- The inverse in a group object -/
  inv : X ⟶ X
  left_inv' : lift inv (𝟙 X) ≫ mul = toUnit _ ≫ one := by aesop_cat
  right_inv' : lift (𝟙 X) inv ≫ mul = toUnit _ ≫ one := by aesop_cat

namespace Mon_Class

@[inherit_doc] scoped notation "ι" => Grp_Class.inv
@[inherit_doc] scoped notation "ι["M"]" => Grp_Class.inv (X := M)

end Mon_Class

open scoped Mon_Class

namespace Grp_Class

@[reassoc (attr := simp)]
theorem left_inv (X : C) [Grp_Class X] : lift ι (𝟙 X) ≫ μ = toUnit _ ≫ η := left_inv'

@[reassoc (attr := simp)]
theorem right_inv (X : C) [Grp_Class X] : lift (𝟙 X) ι ≫ μ = toUnit _ ≫ η := right_inv'

end Grp_Class

end

/-- A group object in a cartesian monoidal category. -/
structure Grp_ extends Mon_ C where
  /-- The inversion operation -/
  inv : X ⟶ X
  left_inv : lift inv (𝟙 X) ≫ mul = toUnit _ ≫ one := by aesop_cat
  right_inv : lift (𝟙 X) inv ≫ mul = toUnit _ ≫ one := by aesop_cat

attribute [reassoc (attr := simp)] Grp_.left_inv
attribute [reassoc (attr := simp)] Grp_.right_inv

namespace Grp_

/-- The trivial group object. -/
@[simps!]
def trivial : Grp_ C :=
  { Mon_.trivial C with inv := 𝟙 _ }

instance : Inhabited (Grp_ C) where
  default := trivial C

variable {C}

/-- Make a group object from `Grp_Class`. -/
def mk' (X : C) [Grp_Class X] : Grp_ C where
  __ := Mon_.mk' X
  inv := Grp_Class.inv (X := X)

instance (X : Grp_ C) : Grp_Class X.X where
  inv := X.inv
  left_inv' := X.left_inv
  right_inv' := X.right_inv

instance : Category (Grp_ C) :=
  InducedCategory.category Grp_.toMon_

@[simp]
theorem id_hom (A : Grp_ C) : Mon_.Hom.hom (𝟙 A) = 𝟙 A.X :=
  rfl

@[simp]
theorem comp_hom {R S T : Grp_ C} (f : R ⟶ S) (g : S ⟶ T) :
    Mon_.Hom.hom (f ≫ g) = f.hom ≫ g.hom :=
  rfl

@[ext]
theorem hom_ext {A B : Grp_ C} (f g : A ⟶ B) (h : f.hom = g.hom) : f = g :=
  Mon_.Hom.ext h

@[simp]
lemma id' (A : Grp_ C) : (𝟙 A : A.toMon_ ⟶ A.toMon_) = 𝟙 (A.toMon_) := rfl

@[simp]
lemma comp' {A₁ A₂ A₃ : Grp_ C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    ((f ≫ g : A₁ ⟶ A₃) : A₁.toMon_ ⟶ A₃.toMon_) = @CategoryStruct.comp (Mon_ C) _ _ _ _ f g := rfl

@[reassoc (attr := simp)]
theorem lift_comp_inv_right {A : C} {B : Grp_ C} (f : A ⟶ B.X) :
    lift f (f ≫ B.inv) ≫ B.mul = toUnit _ ≫ B.one := by
  have := f ≫= B.right_inv
  rwa [comp_lift_assoc, comp_id, reassoc_of% toUnit_unique (f ≫ toUnit B.X) (toUnit A)] at this

@[reassoc]
theorem lift_inv_comp_right {A B : Grp_ C} (f : A ⟶ B) :
    lift f.hom (A.inv ≫ f.hom) ≫ B.mul = toUnit _ ≫ B.one := by
  have := A.right_inv =≫ f.hom
  rwa [assoc, f.mul_hom, assoc, f.one_hom, lift_map_assoc, id_comp] at this

@[reassoc (attr := simp)]
theorem lift_comp_inv_left {A : C} {B : Grp_ C} (f : A ⟶ B.X) :
    lift (f ≫ B.inv) f ≫ B.mul = toUnit _ ≫ B.one := by
  have := f ≫= B.left_inv
  rwa [comp_lift_assoc, comp_id, reassoc_of% toUnit_unique (f ≫ toUnit B.X) (toUnit A)] at this

@[reassoc]
theorem lift_inv_comp_left {A B : Grp_ C} (f : A ⟶ B) :
    lift (A.inv ≫ f.hom) f.hom ≫ B.mul = toUnit _ ≫ B.one := by
  have := A.left_inv =≫ f.hom
  rwa [assoc, f.mul_hom, assoc, f.one_hom, lift_map_assoc, id_comp] at this

theorem eq_lift_inv_left {A : C} {B : Grp_ C} (f g h : A ⟶ B.X) :
    f = lift (g ≫ B.inv) h ≫ B.mul ↔ lift g f ≫ B.mul = h := by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; simp [← lift_lift_assoc])

theorem lift_inv_left_eq {A : C} {B : Grp_ C} (f g h : A ⟶ B.X) :
    lift (f ≫ B.inv) g ≫ B.mul = h ↔ g = lift f h ≫ B.mul := by
  rw [eq_comm, eq_lift_inv_left, eq_comm]

theorem eq_lift_inv_right {A : C} {B : Grp_ C} (f g h : A ⟶ B.X) :
    f = lift g (h ≫ B.inv) ≫ B.mul ↔ lift f h ≫ B.mul = g := by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; simp [lift_lift_assoc])

theorem lift_inv_right_eq {A : C} {B : Grp_ C} (f g h : A ⟶ B.X) :
    lift f (g ≫ B.inv) ≫ B.mul = h ↔ f = lift h g ≫ B.mul := by
  rw [eq_comm, eq_lift_inv_right, eq_comm]

theorem lift_left_mul_ext {A : C} {B : Grp_ C} {f g : A ⟶ B.X} (i : A ⟶ B.X)
    (h : lift f i ≫ B.mul = lift g i ≫ B.mul) : f = g := by
  rwa [← eq_lift_inv_right, lift_lift_assoc, lift_comp_inv_right, lift_comp_one_right] at h

@[reassoc (attr := simp)]
theorem inv_comp_inv (A : Grp_ C) : A.inv ≫ A.inv = 𝟙 A.X := by
  apply lift_left_mul_ext A.inv
  rw [right_inv, ← comp_toUnit_assoc A.inv, ← left_inv, comp_lift_assoc, Category.comp_id]

instance (A : Grp_ C) : IsIso A.inv := ⟨A.inv, by simp, by simp⟩

/-- For `inv ≫ inv = 𝟙` see `inv_comp_inv`. -/
@[simp]
theorem inv_inv (A : Grp_ C) : CategoryTheory.inv A.inv = A.inv := by
  rw [eq_comm, ← CategoryTheory.inv_comp_eq_id, IsIso.inv_inv, inv_comp_inv]

@[reassoc]
theorem mul_inv (A : Grp_ C) :
    A.mul ≫ A.inv = (β_ A.X A.X).hom ≫ (A.inv ⊗ A.inv) ≫ A.mul := by
  apply lift_left_mul_ext A.mul
  nth_rw 2 [← Category.comp_id A.mul]
  rw [← comp_lift, Category.assoc, A.left_inv, ← Category.assoc (β_ A.X A.X).hom,
    ← lift_snd_fst, lift_map, lift_lift_assoc]
  nth_rw 2 [← Category.id_comp A.mul]
  rw [← lift_fst_snd, ← lift_lift_assoc (fst A.X A.X ≫ _), lift_comp_inv_left, lift_comp_one_left,
    lift_comp_inv_left, comp_toUnit_assoc]

@[reassoc (attr := simp)]
theorem tensorHom_inv_inv_mul (A : Grp_ C) :
    (A.inv ⊗ A.inv) ≫ A.mul = (β_ A.X A.X).hom ≫ A.mul ≫ A.inv := by
  rw [mul_inv A, SymmetricCategory.symmetry_assoc]

/-- The map `(· * f)`. -/
@[simps]
def mulRight (A : Grp_ C) (f : 𝟙_ C ⟶ A.X) : A.X ≅ A.X where
  hom := lift (𝟙 _) (toUnit _ ≫ f) ≫ A.mul
  inv := lift (𝟙 _) (toUnit _ ≫ f ≫ A.inv) ≫ A.mul
  hom_inv_id := by simp [comp_lift_assoc, lift_lift_assoc, ← comp_lift]
  inv_hom_id := by simp [comp_lift_assoc, lift_lift_assoc, ← comp_lift]

@[simp]
lemma mulRight_one (A : Grp_ C) : A.mulRight A.one = Iso.refl A.X := by
  ext; simp

/-- The associativity diagram of a group object is cartesian.

In fact, any monoid object whose associativity diagram is cartesian can be made into a group object
(we do not prove this in this file), so we should expect that many properties of group objects
follow from this result. -/
theorem isPullback (A : Grp_ C) :
    IsPullback (A.mul ▷ A.X) ((α_ A.X A.X A.X).hom ≫ (A.X ◁ A.mul)) A.mul A.mul where
  w := by simp
  isLimit' := Nonempty.intro <| PullbackCone.IsLimit.mk _
    (fun s => lift
      (lift
        (s.snd ≫ fst _ _)
        (lift (s.snd ≫ fst _ _ ≫ A.inv) (s.fst ≫ fst _ _) ≫ A.mul))
      (s.fst ≫ snd _ _))
    (by
      refine fun s => ChosenFiniteProducts.hom_ext _ _ ?_ (by simp)
      simp only [lift_whiskerRight, lift_fst]
      rw [← lift_lift_assoc, ← assoc, lift_comp_inv_right, lift_comp_one_left])
    (by
      refine fun s => ChosenFiniteProducts.hom_ext _ _ (by simp) ?_
      simp only [lift_lift_associator_hom_assoc, lift_whiskerLeft, lift_snd]
      have : lift (s.snd ≫ fst _ _ ≫ A.inv) (s.fst ≫ fst _ _) ≫ A.mul =
          lift (s.snd ≫ snd _ _) (s.fst ≫ snd _ _ ≫ A.inv) ≫ A.mul := by
        rw [← assoc s.fst, eq_lift_inv_right, lift_lift_assoc, ← assoc s.snd, lift_inv_left_eq,
          lift_comp_fst_snd, lift_comp_fst_snd, s.condition]
      rw [this, lift_lift_assoc, ← assoc, lift_comp_inv_left, lift_comp_one_right])
    (by
      intro s m hm₁ hm₂
      refine ChosenFiniteProducts.hom_ext _ _ (ChosenFiniteProducts.hom_ext _ _ ?_ ?_) ?_
      · simpa using hm₂ =≫ fst _ _
      · have h : m ≫ fst _ _ ≫ fst _ _ = s.snd ≫ fst _ _ := by simpa using hm₂ =≫ fst _ _
        have := hm₁ =≫ fst _ _
        simp only [assoc, whiskerRight_fst, lift_fst, lift_snd] at this ⊢
        rw [← assoc, ← lift_comp_fst_snd (m ≫ _), assoc, assoc, h] at this
        rwa [← assoc s.snd, eq_lift_inv_left]
      · simpa using hm₁ =≫ snd _ _)

/-- Morphisms of group objects preserve inverses. -/
@[reassoc (attr := simp)]
theorem inv_hom {A B : Grp_ C} (f : A ⟶ B) : A.inv ≫ f.hom = f.hom ≫ B.inv := by
  suffices lift (lift f.hom (A.inv ≫ f.hom)) f.hom =
      lift (lift f.hom (f.hom ≫ B.inv)) f.hom by simpa using (this =≫ fst _ _) =≫ snd _ _
  apply B.isPullback.hom_ext <;> apply ChosenFiniteProducts.hom_ext <;>
    simp [lift_inv_comp_right, lift_inv_comp_left]

open Mon_Class in
@[reassoc]
lemma _root_.IsMon_Hom.inv_hom {X Y : C} [Grp_Class X] [Grp_Class Y] (f : X ⟶ Y) [IsMon_Hom f] :
    ι ≫ f = f ≫ ι :=
  Grp_.inv_hom (A := .mk' X) (B := .mk' Y) (f := ⟨f, IsMon_Hom.one_hom, IsMon_Hom.mul_hom⟩)

lemma _root_.Grp_Class.toMon_Class_injective {X : C} :
    Function.Injective (@Grp_Class.toMon_Class C ‹_› ‹_› X) := by
  intro h₁ h₂ e
  let X₁ : Grp_ C := @Grp_.mk' _ _ _ X h₁
  let X₂ : Grp_ C := @Grp_.mk' _ _ _ X h₂
  suffices X₁.inv = X₂.inv by cases h₁; cases h₂; subst e this; rfl
  apply lift_left_mul_ext (𝟙 _)
  rw [left_inv, show X₁.mul = X₂.mul from congr(($e).mul),
    show X₁.one = X₂.one from congr(($e).one)]
  exact X₂.left_inv.symm

@[ext]
lemma _root_.Grp_Class.ext {X : C} (h₁ h₂ : Grp_Class X)
    (H : h₁.toMon_Class = h₂.toMon_Class) : h₁ = h₂ :=
  Grp_Class.toMon_Class_injective H

section

variable (C)

/-- The forgetful functor from group objects to monoid objects. -/
def forget₂Mon_ : Grp_ C ⥤ Mon_ C :=
  inducedFunctor Grp_.toMon_

/-- The forgetful functor from group objects to monoid objects is fully faithful. -/
def fullyFaithfulForget₂Mon_ : (forget₂Mon_ C).FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : (forget₂Mon_ C).Full := InducedCategory.full _
instance : (forget₂Mon_ C).Faithful := InducedCategory.faithful _

@[simp]
theorem forget₂Mon_obj_one (A : Grp_ C) : ((forget₂Mon_ C).obj A).one = A.one :=
  rfl

@[simp]
theorem forget₂Mon_obj_mul (A : Grp_ C) : ((forget₂Mon_ C).obj A).mul = A.mul :=
  rfl

@[simp]
theorem forget₂Mon_map_hom {A B : Grp_ C} (f : A ⟶ B) : ((forget₂Mon_ C).map f).hom = f.hom :=
  rfl

/-- The forgetful functor from group objects to the ambient category. -/
@[simps!]
def forget : Grp_ C ⥤ C :=
  forget₂Mon_ C ⋙ Mon_.forget C

instance : (forget C).Faithful where

@[simp]
theorem forget₂Mon_comp_forget : forget₂Mon_ C ⋙ Mon_.forget C = forget C := rfl

end

section

variable {M N : Grp_ C} (f : M.X ≅ N.X) (one_f : M.one ≫ f.hom = N.one := by aesop_cat)
  (mul_f : M.mul ≫ f.hom = (f.hom ⊗ f.hom) ≫ N.mul := by aesop_cat)

/-- Constructor for isomorphisms in the category `Grp_ C`. -/
def mkIso : M ≅ N :=
  (fullyFaithfulForget₂Mon_ C).preimageIso (Mon_.mkIso f one_f mul_f)

@[simp] lemma mkIso_hom_hom : (mkIso f one_f mul_f).hom.hom = f.hom := rfl
@[simp] lemma mkIso_inv_hom : (mkIso f one_f mul_f).inv.hom = f.inv := rfl

end

instance uniqueHomFromTrivial (A : Grp_ C) : Unique (trivial C ⟶ A) :=
  Mon_.uniqueHomFromTrivial A.toMon_

instance : HasInitial (Grp_ C) :=
  hasInitial_of_unique (trivial C)

end Grp_

namespace CategoryTheory.Functor

variable {C} {D : Type u₂} [Category.{v₂} D] [ChosenFiniteProducts.{v₂} D] (F : C ⥤ D)
variable [PreservesFiniteProducts F]

attribute [local instance] monoidalOfChosenFiniteProducts

/-- A finite-product-preserving functor takes group objects to group objects. -/
@[simps!]
noncomputable def mapGrp : Grp_ C ⥤ Grp_ D where
  obj A :=
    { F.mapMon.obj A.toMon_ with
      inv := F.map A.inv
      left_inv := by
        simp [← Functor.map_id, Functor.Monoidal.lift_μ_assoc,
          Functor.Monoidal.toUnit_ε_assoc, ← Functor.map_comp]
      right_inv := by
        simp [← Functor.map_id, Functor.Monoidal.lift_μ_assoc,
          Functor.Monoidal.toUnit_ε_assoc, ← Functor.map_comp] }
  map f := F.mapMon.map f

/-- `mapGrp` is functorial in the left-exact functor. -/
@[simps]
noncomputable def mapGrpFunctor : (C ⥤ₗ D) ⥤ Grp_ C ⥤ Grp_ D where
  obj F := F.1.mapGrp
  map {F G} α := { app := fun A => { hom := α.app A.X } }

end CategoryTheory.Functor
