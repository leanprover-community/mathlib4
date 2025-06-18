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

universe v₁ v₂ v₃ u₁ u₂ u₃ u

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory Mon_ Mon_Class

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory.{v₁} C]

section

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

namespace Grp_Class

@[reassoc (attr := simp)]
theorem left_inv (X : C) [Grp_Class X] : lift ι (𝟙 X) ≫ μ = toUnit _ ≫ η := left_inv'

@[reassoc (attr := simp)]
theorem right_inv (X : C) [Grp_Class X] : lift (𝟙 X) ι ≫ μ = toUnit _ ≫ η := right_inv'

@[simps inv]
instance : Grp_Class (𝟙_ C) where
  inv := 𝟙 (𝟙_ C)

end Grp_Class

end

variable (C) in
/-- A group object in a cartesian monoidal category. -/
structure Grp_ where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [grp : Grp_Class X]

attribute [instance] Grp_.grp

namespace Grp_

/-- A group object is a monoid object. -/
@[simps X]
def toMon_ (A : Grp_ C) : Mon_ C := ⟨A.X⟩

variable (C) in
/-- The trivial group object. -/
@[simps!]
def trivial : Grp_ C :=
  { Mon_.trivial C with grp := inferInstanceAs (Grp_Class (𝟙_ C)) }

instance : Inhabited (Grp_ C) where
  default := trivial C

@[deprecated (since := "2025-06-15")] alias mk' := mk

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

end Grp_

namespace Grp_Class

variable {A : C} {B : C}

@[reassoc (attr := simp)]
theorem lift_comp_inv_right [Grp_Class B] (f : A ⟶ B) :
    lift f (f ≫ ι) ≫ μ = toUnit _ ≫ η := by
  have := f ≫= right_inv B
  rwa [comp_lift_assoc, comp_id, reassoc_of% toUnit_unique (f ≫ toUnit B) (toUnit A)] at this

@[reassoc]
theorem lift_inv_comp_right [Grp_Class A] [Grp_Class B] (f : A ⟶ B) [IsMon_Hom f] :
    lift f (ι ≫ f) ≫ μ = toUnit _ ≫ η := by
  have := right_inv A =≫ f
  rwa [assoc, IsMon_Hom.mul_hom, assoc, IsMon_Hom.one_hom, lift_map_assoc, id_comp] at this

@[reassoc (attr := simp)]
theorem lift_comp_inv_left [Grp_Class B] (f : A ⟶ B) :
    lift (f ≫ ι) f ≫ μ = toUnit _ ≫ η := by
  have := f ≫= left_inv B
  rwa [comp_lift_assoc, comp_id, reassoc_of% toUnit_unique (f ≫ toUnit B) (toUnit A)] at this

@[reassoc]
theorem lift_inv_comp_left [Grp_Class A] [Grp_Class B] (f : A ⟶ B) [IsMon_Hom f] :
    lift (ι ≫ f) f ≫ μ = toUnit _ ≫ η := by
  have := left_inv A =≫ f
  rwa [assoc, IsMon_Hom.mul_hom, assoc, IsMon_Hom.one_hom, lift_map_assoc, id_comp] at this

theorem eq_lift_inv_left [Grp_Class B] (f g h : A ⟶ B) :
    f = lift (g ≫ ι) h ≫ μ ↔ lift g f ≫ μ = h := by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; simp [← lift_lift_assoc])

theorem lift_inv_left_eq [Grp_Class B] (f g h : A ⟶ B) :
    lift (f ≫ ι) g ≫ μ = h ↔ g = lift f h ≫ μ := by
  rw [eq_comm, eq_lift_inv_left, eq_comm]

theorem eq_lift_inv_right [Grp_Class B] (f g h : A ⟶ B) :
    f = lift g (h ≫ ι) ≫ μ ↔ lift f h ≫ μ = g := by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; simp [lift_lift_assoc])

theorem lift_inv_right_eq [Grp_Class B] (f g h : A ⟶ B) :
    lift f (g ≫ ι) ≫ μ = h ↔ f = lift h g ≫ μ := by
  rw [eq_comm, eq_lift_inv_right, eq_comm]

theorem lift_left_mul_ext [Grp_Class B] {f g : A ⟶ B} (i : A ⟶ B)
    (h : lift f i ≫ μ = lift g i ≫ μ) : f = g := by
  rwa [← eq_lift_inv_right, lift_lift_assoc, lift_comp_inv_right, lift_comp_one_right] at h

@[reassoc (attr := simp)]
theorem inv_comp_inv (A : C) [Grp_Class A] : ι ≫ ι = 𝟙 A := by
  apply lift_left_mul_ext ι[A]
  rw [right_inv, ← comp_toUnit_assoc ι, ← left_inv, comp_lift_assoc, Category.comp_id]

instance (A : C) [Grp_Class A] : IsIso ι[A] := ⟨ι, by simp, by simp⟩

/-- For `inv ≫ inv = 𝟙` see `inv_comp_inv`. -/
@[simp]
theorem inv_inv (A : C) [Grp_Class A] : CategoryTheory.inv ι = ι[A] := by
  rw [eq_comm, ← CategoryTheory.inv_comp_eq_id, IsIso.inv_inv, inv_comp_inv]

@[reassoc]
theorem mul_inv [BraidedCategory C] (A : C) [Grp_Class A] :
    μ ≫ ι = (β_ A A).hom ≫ (ι ⊗ₘ ι) ≫ μ := by
  apply lift_left_mul_ext μ
  nth_rw 2 [← Category.comp_id μ]
  rw [← comp_lift, Category.assoc, left_inv, ← Category.assoc (β_ A A).hom,
    ← lift_snd_fst, lift_map, lift_lift_assoc]
  nth_rw 2 [← Category.id_comp μ]
  rw [← lift_fst_snd, ← lift_lift_assoc (fst A A ≫ _), lift_comp_inv_left, lift_comp_one_left,
    lift_comp_inv_left, comp_toUnit_assoc]

@[reassoc]
theorem tensorHom_inv_inv_mul [BraidedCategory C] (A : C) [Grp_Class A] :
    (ι[A] ⊗ₘ ι[A]) ≫ μ = (β_ A A).hom ≫ μ ≫ ι := by
  rw [mul_inv A, SymmetricCategory.symmetry_assoc]

@[reassoc]
lemma mul_inv_rev [BraidedCategory C] (G : C) [Grp_Class G] :
    μ ≫ ι = (ι[G] ⊗ₘ ι) ≫ (β_ _ _).hom ≫ μ := by simp [tensorHom_inv_inv_mul]

/-- The map `(· * f)`. -/
@[simps]
def mulRight {A : C} [Grp_Class A] (f : 𝟙_ C ⟶ A) : A ≅ A where
  hom := lift (𝟙 _) (toUnit _ ≫ f) ≫ μ
  inv := lift (𝟙 _) (toUnit _ ≫ f ≫ ι) ≫ μ
  hom_inv_id := by simp [comp_lift_assoc, lift_lift_assoc, ← comp_lift]
  inv_hom_id := by simp [comp_lift_assoc, lift_lift_assoc, ← comp_lift]

@[simp]
lemma mulRight_one (A : C) [Grp_Class A] : mulRight η[A] = Iso.refl A := by
  ext; simp

/-- The associativity diagram of a group object is cartesian.

In fact, any monoid object whose associativity diagram is cartesian can be made into a group object
(we do not prove this in this file), so we should expect that many properties of group objects
follow from this result. -/
theorem isPullback (A : C) [Grp_Class A] :
    IsPullback (μ ▷ A) ((α_ A A A).hom ≫ (A ◁ μ)) μ μ where
  w := by simp
  isLimit' := Nonempty.intro <| PullbackCone.IsLimit.mk _
    (fun s => lift
      (lift
        (s.snd ≫ fst _ _)
        (lift (s.snd ≫ fst _ _ ≫ ι) (s.fst ≫ fst _ _) ≫ μ))
      (s.fst ≫ snd _ _))
    (by
      refine fun s => CartesianMonoidalCategory.hom_ext _ _ ?_ (by simp)
      simp only [lift_whiskerRight, lift_fst]
      rw [← lift_lift_assoc, ← assoc, lift_comp_inv_right, lift_comp_one_left])
    (by
      refine fun s => CartesianMonoidalCategory.hom_ext _ _ (by simp) ?_
      simp only [lift_lift_associator_hom_assoc, lift_whiskerLeft, lift_snd]
      have : lift (s.snd ≫ fst _ _ ≫ ι) (s.fst ≫ fst _ _) ≫ μ =
          lift (s.snd ≫ snd _ _) (s.fst ≫ snd _ _ ≫ ι) ≫ μ := by
        rw [← assoc s.fst, eq_lift_inv_right, lift_lift_assoc, ← assoc s.snd, lift_inv_left_eq,
          lift_comp_fst_snd, lift_comp_fst_snd, s.condition]
      rw [this, lift_lift_assoc, ← assoc, lift_comp_inv_left, lift_comp_one_right])
    (by
      intro s m hm₁ hm₂
      refine CartesianMonoidalCategory.hom_ext _ _ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_) ?_
      · simpa using hm₂ =≫ fst _ _
      · have h : m ≫ fst _ _ ≫ fst _ _ = s.snd ≫ fst _ _ := by simpa using hm₂ =≫ fst _ _
        have := hm₁ =≫ fst _ _
        simp only [assoc, whiskerRight_fst, lift_fst, lift_snd] at this ⊢
        rw [← assoc, ← lift_comp_fst_snd (m ≫ _), assoc, assoc, h] at this
        rwa [← assoc s.snd, eq_lift_inv_left]
      · simpa using hm₁ =≫ snd _ _)

/-- Morphisms of group objects preserve inverses. -/
@[reassoc (attr := simp)]
theorem inv_hom [Grp_Class A] [Grp_Class B] (f : A ⟶ B) [IsMon_Hom f] : ι ≫ f = f ≫ ι := by
  suffices lift (lift f (ι ≫ f)) f =
      lift (lift f (f ≫ ι)) f by simpa using (this =≫ fst _ _) =≫ snd _ _
  apply (isPullback B).hom_ext <;> apply CartesianMonoidalCategory.hom_ext <;>
    simp [lift_inv_comp_right, lift_inv_comp_left]

lemma toMon_Class_injective {X : C} :
    Function.Injective (@Grp_Class.toMon_Class C ‹_› ‹_› X) := by
  intro h₁ h₂ e
  let X₁ : Grp_ C := @Grp_.mk _ _ _ X h₁
  let X₂ : Grp_ C := @Grp_.mk _ _ _ X h₂
  suffices h₁.inv = h₂.inv by cases h₁; congr!
  apply lift_left_mul_ext (𝟙 _)
  rw [left_inv]
  convert @left_inv _ _ _ _ h₁ using 2
  exacts [congr(($e.symm).mul), congr(($e.symm).one)]

@[ext]
lemma _root_.Grp_Class.ext {X : C} (h₁ h₂ : Grp_Class X)
    (H : h₁.toMon_Class = h₂.toMon_Class) : h₁ = h₂ :=
  Grp_Class.toMon_Class_injective H

end Grp_Class

namespace Grp_

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

variable {C}

@[simp]
theorem forget₂Mon_obj_one (A : Grp_ C) : η[((forget₂Mon_ C).obj A).X] = η[A.X] :=
  rfl

@[simp]
theorem forget₂Mon_obj_mul (A : Grp_ C) : μ[((forget₂Mon_ C).obj A).X] = μ[A.X] :=
  rfl

@[simp]
theorem forget₂Mon_map_hom {A B : Grp_ C} (f : A ⟶ B) : ((forget₂Mon_ C).map f).hom = f.hom :=
  rfl

variable (C)

/-- The forgetful functor from group objects to the ambient category. -/
@[simps!]
def forget : Grp_ C ⥤ C :=
  forget₂Mon_ C ⋙ Mon_.forget C

instance : (forget C).Faithful where

@[simp]
theorem forget₂Mon_comp_forget : forget₂Mon_ C ⋙ Mon_.forget C = forget C := rfl

end

section

variable {M N : Grp_ C} (f : M.X ≅ N.X) (one_f : η[M.X] ≫ f.hom = η[N.X] := by aesop_cat)
  (mul_f : μ[M.X] ≫ f.hom = (f.hom ⊗ₘ f.hom) ≫ μ[N.X] := by aesop_cat)

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

namespace CategoryTheory
variable
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [CartesianMonoidalCategory E]

namespace Functor
variable {F F' : C ⥤ D} [F.Monoidal] [F'.Monoidal] {G : D ⥤ E} [G.Monoidal]

open Monoidal

variable (F) in
/-- A finite-product-preserving functor takes group objects to group objects. -/
@[simps!]
noncomputable def mapGrp : Grp_ C ⥤ Grp_ D where
  obj A :=
    { F.mapMon.obj A.toMon_ with
      grp :=
      { inv := F.map ι[A.X]
        left_inv' := by
          simp [← Functor.map_id, Functor.Monoidal.lift_μ_assoc,
            Functor.Monoidal.toUnit_ε_assoc, ← Functor.map_comp]
        right_inv' := by
          simp [← Functor.map_id, Functor.Monoidal.lift_μ_assoc,
            Functor.Monoidal.toUnit_ε_assoc, ← Functor.map_comp] } }
  map f := F.mapMon.map f

@[simp]
theorem mapGrp_id_one (A : Grp_ C) :
    η[((𝟭 C).mapGrp.obj A).X] = 𝟙 _ ≫ η[A.X] :=
  rfl

@[simp]
theorem mapGrp_id_mul (A : Grp_ C) :
    μ[((𝟭 C).mapGrp.obj A).X] = 𝟙 _ ≫ μ[A.X] :=
  rfl

@[simp]
theorem comp_mapGrp_one (A : Grp_ C) :
    η[((F ⋙ G).mapGrp.obj A).X] = LaxMonoidal.ε (F ⋙ G) ≫ (F ⋙ G).map η[A.X] :=
  rfl

@[simp]
theorem comp_mapGrp_mul (A : Grp_ C) :
    μ[((F ⋙ G).mapGrp.obj A).X] = LaxMonoidal.μ (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[A.X] :=
  rfl

/-- The identity functor is also the identity on group objects. -/
@[simps!]
noncomputable def mapGrpIdIso : mapGrp (𝟭 C) ≅ 𝟭 (Grp_ C) :=
  NatIso.ofComponents (fun X ↦ Grp_.mkIso (.refl _) (by simp [ε_of_cartesianMonoidalCategory])
    (by simp [μ_of_cartesianMonoidalCategory]))

/-- The composition functor is also the composition on group objects. -/
@[simps!]
noncomputable def mapGrpCompIso : (F ⋙ G).mapGrp ≅ F.mapGrp ⋙ G.mapGrp :=
  NatIso.ofComponents (fun X ↦ Grp_.mkIso (.refl _) (by simp [ε_of_cartesianMonoidalCategory])
    (by simp [μ_of_cartesianMonoidalCategory]))

/-- Natural transformations between functors lift to group objects. -/
@[simps!]
noncomputable def mapGrpNatTrans (f : F ⟶ F') : F.mapGrp ⟶ F'.mapGrp where
  app X := .mk' (f.app _)

/-- Natural isomorphisms between functors lift to group objects. -/
@[simps!]
noncomputable def mapGrpNatIso (e : F ≅ F') : F.mapGrp ≅ F'.mapGrp :=
  NatIso.ofComponents fun X ↦ Grp_.mkIso (e.app _)

attribute [local instance] Monoidal.ofChosenFiniteProducts in
/-- `mapGrp` is functorial in the left-exact functor. -/
@[simps]
noncomputable def mapGrpFunctor : (C ⥤ₗ D) ⥤ Grp_ C ⥤ Grp_ D where
  obj F := F.1.mapGrp
  map {F G} α := { app A := .mk' (α.app A.X) }

end Functor

open Functor

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Monoidal] [G.Monoidal]

/-- An adjunction of monoidal functors lifts to an adjunction of their lifts to group objects. -/
@[simps] noncomputable def mapGrp : F.mapGrp ⊣ G.mapGrp where
  unit := mapGrpIdIso.inv ≫ mapGrpNatTrans a.unit ≫ mapGrpCompIso.hom
  counit := mapGrpCompIso.inv ≫ mapGrpNatTrans a.counit ≫ mapGrpIdIso.hom

end Adjunction

namespace Equivalence
variable (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal]

/-- An equivalence of categories lifts to an equivalence of their group objects. -/
@[simps] noncomputable def mapGrp : Grp_ C ≌ Grp_ D where
  functor := e.functor.mapGrp
  inverse := e.inverse.mapGrp
  unitIso := mapGrpIdIso.symm ≪≫ mapGrpNatIso e.unitIso ≪≫ mapGrpCompIso
  counitIso := mapGrpCompIso.symm ≪≫ mapGrpNatIso e.counitIso ≪≫ mapGrpIdIso

end CategoryTheory.Equivalence
