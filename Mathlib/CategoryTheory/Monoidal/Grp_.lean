/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon_
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Algebra.Group.Invertible.Defs

/-!
# The category of groups in a Cartesian monoidal category

We define group objects in Cartesian monoidal categories.

We show that the associativity diagram of a group object is always Cartesian and deduce that
morphisms of group objects commute with taking inverses.

We show that a finite-product-preserving functor takes group objects to group objects.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃ u

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory Mon MonObj

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory.{v₁} C]

/-- A group object internal to a cartesian monoidal category. Also see the bundled `Grp`. -/
class GrpObj (X : C) extends MonObj X where
  /-- The inverse in a group object -/
  inv : X ⟶ X
  left_inv (X) : lift inv (𝟙 X) ≫ mul = toUnit _ ≫ one := by cat_disch
  right_inv (X) : lift (𝟙 X) inv ≫ mul = toUnit _ ≫ one := by cat_disch

@[deprecated (since := "2025-09-13")] alias Grp_Class := GrpObj

namespace MonObj

@[inherit_doc] scoped notation "ι" => GrpObj.inv
@[inherit_doc] scoped notation "ι[" G "]" => GrpObj.inv (X := G)

end MonObj

namespace GrpObj

attribute [reassoc (attr := simp)] left_inv right_inv

@[simps inv]
instance : GrpObj (𝟙_ C) where
  inv := 𝟙 (𝟙_ C)

end GrpObj

variable (C) in
/-- A group object in a Cartesian monoidal category. -/
structure Grp where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [grp : GrpObj X]

@[deprecated (since := "2025-10-13")] alias Grp_ := Grp

attribute [instance] Grp.grp

namespace Grp

/-- A group object is a monoid object. -/
@[simps -isSimp X]
abbrev toMon (A : Grp C) : Mon C := ⟨A.X⟩

@[deprecated (since := "2025-09-15")] alias toMon_ := toMon

variable (C) in
/-- The trivial group object. -/
@[simps!]
def trivial : Grp C :=
  { Mon.trivial C with grp := inferInstanceAs (GrpObj (𝟙_ C)) }

instance : Inhabited (Grp C) where
  default := trivial C

instance : Category (Grp C) :=
  inferInstanceAs (Category (InducedCategory _ Grp.toMon))

@[simp]
theorem id_hom_hom (A : Grp C) : Mon.Hom.hom (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.X :=
  rfl

@[simp]
theorem comp_hom_hom {R S T : Grp C} (f : R ⟶ S) (g : S ⟶ T) :
    Mon.Hom.hom (f ≫ g).hom = f.hom.hom ≫ g.hom.hom :=
  rfl

@[deprecated (since := "2025-12-18")] alias id_hom := id_hom_hom
@[deprecated (since := "2025-12-18")] alias comp_hom := comp_hom_hom

@[ext]
theorem hom_ext {A B : Grp C} (f g : A ⟶ B) (h : f.hom.hom = g.hom.hom) : f = g :=
  InducedCategory.hom_ext (Mon.Hom.ext h)

/-- Constructor for morphisms in `Grp C`. -/
@[simps]
def homMk' {A B : Grp C} (f : A.toMon ⟶ B.toMon) : A ⟶ B where
  hom := f

/-- Construct a morphism `A ⟶ B` of `Grp C` from a map `f : A.X ⟶ A.X` and a `IsMonHom f`
instance. -/
@[simps!]
def homMk {A B : Grp C} (f : A.X ⟶ B.X) [IsMonHom f] : A ⟶ B :=
  homMk' (.mk f)

/-- Constructor for morphisms in `Grp_ C`. -/
@[simps!]
def homMk'' {A B : Grp C} (f : A.X ⟶ B.X)
    (one_f : η ≫ f = η := by cat_disch)
    (mul_f : μ ≫ f = (f ⊗ₘ f) ≫ μ := by cat_disch) : A ⟶ B :=
  haveI : IsMonHom f := ⟨one_f, mul_f⟩
  homMk f

@[simp]
lemma id' (A : Grp C) :
    (InducedCategory.Hom.hom (𝟙 A) : A.toMon ⟶ A.toMon) = 𝟙 (A.toMon) := rfl

@[simp]
lemma comp' {A₁ A₂ A₃ : Grp C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    (InducedCategory.Hom.hom (f ≫ g : A₁ ⟶ A₃) : A₁.toMon ⟶ A₃.toMon) =
      f.hom ≫ g.hom := rfl

end Grp

namespace GrpObj
variable {G X : C} [GrpObj G]

variable {A : C} {B : C}

@[reassoc (attr := simp)]
theorem lift_comp_inv_right [GrpObj B] (f : A ⟶ B) :
    lift f (f ≫ ι) ≫ μ = toUnit _ ≫ η := by
  have := f ≫= right_inv B
  rwa [comp_lift_assoc, comp_id, reassoc_of% toUnit_unique (f ≫ toUnit B) (toUnit A)] at this

@[reassoc]
theorem lift_inv_comp_right [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] :
    lift f (ι ≫ f) ≫ μ = toUnit _ ≫ η := by
  have := right_inv A =≫ f
  rwa [assoc, IsMonHom.mul_hom, assoc, IsMonHom.one_hom, lift_map_assoc, id_comp] at this

@[reassoc (attr := simp)]
theorem lift_comp_inv_left [GrpObj B] (f : A ⟶ B) :
    lift (f ≫ ι) f ≫ μ = toUnit _ ≫ η := by
  have := f ≫= left_inv B
  rwa [comp_lift_assoc, comp_id, reassoc_of% toUnit_unique (f ≫ toUnit B) (toUnit A)] at this

@[reassoc]
theorem lift_inv_comp_left [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] :
    lift (ι ≫ f) f ≫ μ = toUnit _ ≫ η := by
  have := left_inv A =≫ f
  rwa [assoc, IsMonHom.mul_hom, assoc, IsMonHom.one_hom, lift_map_assoc, id_comp] at this

theorem eq_lift_inv_left [GrpObj B] (f g h : A ⟶ B) :
    f = lift (g ≫ ι) h ≫ μ ↔ lift g f ≫ μ = h := by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; simp [← lift_lift_assoc])

theorem lift_inv_left_eq [GrpObj B] (f g h : A ⟶ B) :
    lift (f ≫ ι) g ≫ μ = h ↔ g = lift f h ≫ μ := by
  rw [eq_comm, eq_lift_inv_left, eq_comm]

theorem eq_lift_inv_right [GrpObj B] (f g h : A ⟶ B) :
    f = lift g (h ≫ ι) ≫ μ ↔ lift f h ≫ μ = g := by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; simp [lift_lift_assoc])

theorem lift_inv_right_eq [GrpObj B] (f g h : A ⟶ B) :
    lift f (g ≫ ι) ≫ μ = h ↔ f = lift h g ≫ μ := by
  rw [eq_comm, eq_lift_inv_right, eq_comm]

theorem lift_left_mul_ext [GrpObj B] {f g : A ⟶ B} (i : A ⟶ B)
    (h : lift f i ≫ μ = lift g i ≫ μ) : f = g := by
  rwa [← eq_lift_inv_right, lift_lift_assoc, lift_comp_inv_right, lift_comp_one_right] at h

@[reassoc (attr := simp)]
theorem inv_comp_inv (A : C) [GrpObj A] : ι ≫ ι = 𝟙 A := by
  apply lift_left_mul_ext ι[A]
  rw [right_inv, ← comp_toUnit_assoc ι, ← left_inv, comp_lift_assoc, Category.comp_id]

set_option backward.whnf.reducibleClassField false in
/-- Transfer `GrpObj` along an isomorphism. -/
-- Note: The simps lemmas are not tagged simp because their `#discr_tree_simp_key` are too generic.
@[simps! -isSimp]
abbrev ofIso (e : G ≅ X) : GrpObj X where
  toMonObj := .ofIso e
  inv := e.inv ≫ ι[G] ≫ e.hom
  left_inv := by simp +instances [MonObj.ofIso]
  right_inv := by simp +instances [MonObj.ofIso]

instance (A : C) [GrpObj A] : IsIso ι[A] := ⟨ι, by simp, by simp⟩

/-- For `inv ≫ inv = 𝟙` see `inv_comp_inv`. -/
@[simp]
theorem inv_inv (A : C) [GrpObj A] : CategoryTheory.inv ι = ι[A] := by
  rw [eq_comm, ← CategoryTheory.inv_comp_eq_id, IsIso.inv_inv, inv_comp_inv]

@[reassoc]
theorem mul_inv [BraidedCategory C] (A : C) [GrpObj A] :
    μ ≫ ι = (β_ A A).hom ≫ (ι ⊗ₘ ι) ≫ μ := by
  apply lift_left_mul_ext μ
  nth_rw 2 [← Category.comp_id μ]
  rw [← comp_lift, Category.assoc, left_inv, ← Category.assoc (β_ A A).hom,
    ← lift_snd_fst, lift_map, lift_lift_assoc]
  nth_rw 2 [← Category.id_comp μ]
  rw [← lift_fst_snd, ← lift_lift_assoc (fst A A ≫ _), lift_comp_inv_left, lift_comp_one_left,
    lift_comp_inv_left, comp_toUnit_assoc]

@[reassoc]
theorem tensorHom_inv_inv_mul [BraidedCategory C] (A : C) [GrpObj A] :
    (ι[A] ⊗ₘ ι[A]) ≫ μ = (β_ A A).hom ≫ μ ≫ ι := by
  rw [mul_inv A, SymmetricCategory.symmetry_assoc]

@[reassoc]
lemma mul_inv_rev [BraidedCategory C] (G : C) [GrpObj G] :
    μ ≫ ι = (ι[G] ⊗ₘ ι) ≫ (β_ _ _).hom ≫ μ := by simp [tensorHom_inv_inv_mul]

/-- The map `(· * f)`. -/
@[simps]
def mulRight {A : C} [GrpObj A] (f : 𝟙_ C ⟶ A) : A ≅ A where
  hom := lift (𝟙 _) (toUnit _ ≫ f) ≫ μ
  inv := lift (𝟙 _) (toUnit _ ≫ f ≫ ι) ≫ μ
  hom_inv_id := by simp [comp_lift_assoc, lift_lift_assoc, ← comp_lift]
  inv_hom_id := by simp [comp_lift_assoc, lift_lift_assoc, ← comp_lift]

@[simp]
lemma mulRight_one (A : C) [GrpObj A] : mulRight η[A] = Iso.refl A := by
  ext; simp

/-- The associativity diagram of a group object is Cartesian.

In fact, any monoid object whose associativity diagram is Cartesian can be made into a group object
(we do not prove this in this file), so we should expect that many properties of group objects
follow from this result. -/
theorem isPullback (A : C) [GrpObj A] :
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
theorem inv_hom [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] : ι ≫ f = f ≫ ι := by
  suffices lift (lift f (ι ≫ f)) f =
      lift (lift f (f ≫ ι)) f by simpa using (this =≫ fst _ _) =≫ snd _ _
  apply (isPullback B).hom_ext <;> apply CartesianMonoidalCategory.hom_ext <;>
    simp [lift_inv_comp_right, lift_inv_comp_left]

lemma toMonObj_injective {X : C} :
    Function.Injective (@GrpObj.toMonObj C ‹_› ‹_› X) := by
  intro h₁ h₂ e
  suffices h₁.inv = h₂.inv by cases h₁; congr!
  apply lift_left_mul_ext (𝟙 _)
  rw [left_inv]
  convert @left_inv _ _ _ _ h₁ using 2
  exacts [congr(($e.symm).mul), congr(($e.symm).one)]

@[deprecated (since := "2025-09-09")] alias toMon_Class_injective := toMonObj_injective

@[ext]
lemma ext {X : C} (h₁ h₂ : GrpObj X) (H : h₁.toMonObj = h₂.toMonObj) : h₁ = h₂ :=
  GrpObj.toMonObj_injective H

set_option backward.isDefEq.respectTransparency false in
/-- A monoid object with invertible homs is a group object. -/
def ofInvertible (G : C) [CartesianMonoidalCategory C] [MonObj G]
    (h : ∀ X (f : X ⟶ G), Invertible f) : GrpObj G where
  inv := Yoneda.fullyFaithful.preimage ⟨fun X f ↦ (h X.unop f).invOf, fun X Y f ↦ by
    ext g
    simp_rw [types_comp_apply, yoneda_obj_map, invOf_eq_iff_left]
    rw [← comp_mul, invOf_mul_self, comp_one]⟩
  left_inv := by rw [Yoneda.fullyFaithful_preimage, ← Hom.mul_def, invOf_mul_self, Hom.one_def]
  right_inv := by rw [Yoneda.fullyFaithful_preimage, ← Hom.mul_def, mul_invOf_self, Hom.one_def]

namespace tensorObj
variable [BraidedCategory C] {G H : C} [GrpObj G] [GrpObj H]

@[simps inv]
instance : GrpObj (G ⊗ H) where
  inv := ι ⊗ₘ ι

end GrpObj.tensorObj

namespace Grp

section

variable (C)

/-- The forgetful functor from group objects to monoid objects. -/
@[simps! obj_X]
def forget₂Mon : Grp C ⥤ Mon C :=
  inducedFunctor Grp.toMon

@[deprecated (since := "2025-09-15")] alias forget₂Mon_ := forget₂Mon

/-- The forgetful functor from group objects to monoid objects is fully faithful. -/
def fullyFaithfulForget₂Mon : (forget₂Mon C).FullyFaithful :=
  fullyFaithfulInducedFunctor _

@[deprecated (since := "2025-09-15")] alias fullyFaithfulForget₂Mon_ := fullyFaithfulForget₂Mon

instance : (forget₂Mon C).Full := InducedCategory.full _
instance : (forget₂Mon C).Faithful := InducedCategory.faithful _

variable {C}

@[simp]
theorem forget₂Mon_obj_one (A : Grp C) : η[((forget₂Mon C).obj A).X] = η[A.X] :=
  rfl

@[simp]
theorem forget₂Mon_obj_mul (A : Grp C) : μ[((forget₂Mon C).obj A).X] = μ[A.X] :=
  rfl

@[simp]
theorem forget₂Mon_map_hom {A B : Grp C} (f : A ⟶ B) :
    ((forget₂Mon C).map f).hom = f.hom.hom :=
  rfl

variable (C)

/-- The forgetful functor from group objects to the ambient category. -/
@[simps!]
def forget : Grp C ⥤ C :=
  forget₂Mon C ⋙ Mon.forget C

instance : (forget C).Faithful where

@[simp]
theorem forget₂Mon_comp_forget : forget₂Mon C ⋙ Mon.forget C = forget C := rfl

instance {G H : Grp C} {f : G ⟶ H} [IsIso f] : IsIso f.hom.hom :=
  inferInstanceAs <| IsIso <| (forget C).map f

end

/-- Construct an isomorphism of group objects by giving a monoid isomorphism between the underlying
objects. -/
@[simps!]
def mkIso' {G H : C} (e : G ≅ H) [GrpObj G] [GrpObj H] [IsMonHom e.hom] : mk G ≅ mk H :=
  (fullyFaithfulForget₂Mon C).preimageIso (Mon.mkIso' e)

/-- Construct an isomorphism of group objects by giving an isomorphism between the underlying
objects and checking compatibility with unit and multiplication only in the forward direction. -/
@[simps!]
abbrev mkIso {G H : Grp C} (e : G.X ≅ H.X) (one_f : η[G.X] ≫ e.hom = η[H.X] := by cat_disch)
    (mul_f : μ[G.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[H.X] := by cat_disch) : G ≅ H :=
  have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

@[deprecated (since := "2025-12-18")] alias mkIso_hom_hom := mkIso_hom_hom_hom
@[deprecated (since := "2025-12-18")] alias mkIso_inv_hom := mkIso_inv_hom_hom

instance uniqueHomFromTrivial (A : Grp C) : Unique (trivial C ⟶ A) :=
  (show _ ≃ (Mon.trivial C ⟶ A.toMon) from InducedCategory.homEquiv).unique

instance uniqueHomToTrivial (A : Grp C) : Unique (A ⟶ trivial C) :=
  (show _ ≃ (A.toMon ⟶ Mon.trivial C) from InducedCategory.homEquiv).unique

instance : HasZeroObject (Grp C) where
  zero := ⟨Grp.trivial C,
    fun A ↦ nonempty_unique (Grp.trivial C ⟶ A),
    fun A ↦ nonempty_unique (A ⟶ Grp.trivial C)⟩

noncomputable instance : HasZeroMorphisms (Grp C) := HasZeroObject.zeroMorphismsOfZeroObject

/-! ### `Grp C` is cartesian-monoidal -/

variable [BraidedCategory C] {G H H₁ H₂ : Grp C}

@[simps! tensorObj_X tensorHom_hom]
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Grp C) where
  tensorObj G H := ⟨G.X ⊗ H.X⟩
  tensorHom f g := homMk' (tensorHom (C := Mon C) f.hom g.hom)
  whiskerRight f G := homMk' (whiskerRight (C := Mon C) f.hom G.toMon)
  whiskerLeft G _ _ f := homMk' (MonoidalCategoryStruct.whiskerLeft (C := Mon C) G.toMon f.hom)
  tensorUnit := ⟨𝟙_ C⟩
  associator X Y Z :=
    (Grp.fullyFaithfulForget₂Mon C).preimageIso (associator X.toMon Y.toMon Z.toMon)
  leftUnitor G := (Grp.fullyFaithfulForget₂Mon C).preimageIso (leftUnitor G.toMon)
  rightUnitor G := (Grp.fullyFaithfulForget₂Mon C).preimageIso (rightUnitor G.toMon)

@[simp] lemma tensorUnit_X : (𝟙_ (Grp C)).X = 𝟙_ C := rfl

@[simp] lemma tensorUnit_one : η[(𝟙_ (Grp C)).X] = η[𝟙_ C] := rfl
@[simp] lemma tensorUnit_mul : μ[(𝟙_ (Grp C)).X] = μ[𝟙_ C] := rfl

@[simp] lemma tensorObj_one (G H : Grp C) : η[(G ⊗ H).X] = η[G.X ⊗ H.X] := rfl
@[simp] lemma tensorObj_mul (G H : Grp C) : μ[(G ⊗ H).X] = μ[G.X ⊗ H.X] := rfl

@[simp] lemma whiskerLeft_hom_hom {G H : Grp C} (f : G ⟶ H) (I : Grp C) :
    (f ▷ I).hom.hom = f.hom.hom ▷ I.X := rfl

@[simp] lemma whiskerRight_hom_hom (G : Grp C) {H I : Grp C} (f : H ⟶ I) :
    (G ◁ f).hom.hom = G.X ◁ f.hom.hom := rfl


@[simp] lemma leftUnitor_hom_hom_hom (G : Grp C) : (λ_ G).hom.hom.hom = (λ_ G.X).hom := rfl
@[simp] lemma leftUnitor_inv_hom_hom (G : Grp C) : (λ_ G).inv.hom.hom = (λ_ G.X).inv := rfl
@[simp] lemma rightUnitor_hom_hom_hom (G : Grp C) : (ρ_ G).hom.hom.hom = (ρ_ G.X).hom := rfl
@[simp] lemma rightUnitor_inv_hom_hom (G : Grp C) : (ρ_ G).inv.hom.hom = (ρ_ G.X).inv := rfl
@[simp] lemma associator_hom_hom_hom (G H I : Grp C) :
    (α_ G H I).hom.hom.hom = (α_ G.X H.X I.X).hom := rfl
@[simp] lemma associator_inv_hom_hom (G H I : Grp C) :
    (α_ G H I).inv.hom.hom = (α_ G.X H.X I.X).inv := rfl

@[deprecated (since := "2025-12-18")] alias whiskerLeft_hom := whiskerLeft_hom_hom
@[deprecated (since := "2025-12-18")] alias whiskerRight_hom := whiskerRight_hom_hom
@[deprecated (since := "2025-12-18")] alias leftUnitor_hom_hom := leftUnitor_hom_hom_hom
@[deprecated (since := "2025-12-18")] alias leftUnitor_inv_hom := leftUnitor_inv_hom_hom
@[deprecated (since := "2025-12-18")] alias rightUnitor_hom_hom := rightUnitor_hom_hom_hom
@[deprecated (since := "2025-12-18")] alias rightUnitor_inv_hom := rightUnitor_inv_hom_hom
@[deprecated (since := "2025-12-18")] alias associator_hom_hom := associator_hom_hom_hom
@[deprecated (since := "2025-12-18")] alias associator_inv_hom := associator_inv_hom_hom

instance instMonoidalCategory : MonoidalCategory (Grp C) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]
  triangle _ _ := by ext; exact triangle _ _

instance instCartesianMonoidalCategory : CartesianMonoidalCategory (Grp C) where
  isTerminalTensorUnit :=
    .ofUniqueHom (fun G ↦ homMk' (toUnit G.toMon)) fun G f ↦ by ext; exact toUnit_unique ..
  fst G H := homMk' (fst G.toMon H.toMon)
  snd G H := homMk' (snd G.toMon H.toMon)
  tensorProductIsBinaryProduct G H :=
    BinaryFan.IsLimit.mk _ (fun {T} f g ↦ .mk (lift f.hom g.hom))
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def G H := by ext; apply fst_def
  snd_def G H := by ext; apply snd_def

@[simp] lemma lift_hom (f : G ⟶ H₁) (g : G ⟶ H₂) : (lift f g).hom = (lift f.hom g.hom) := rfl
@[simp] lemma fst_hom_hom (G H : Grp C) : (fst G H).hom.hom = fst G.X H.X := rfl
@[simp] lemma snd_hom_hom (G H : Grp C) : (snd G H).hom.hom = snd G.X H.X := rfl

@[deprecated (since := "2025-12-18")] alias fst_hom := fst_hom_hom
@[deprecated (since := "2025-12-18")] alias snd_hom := snd_hom_hom

set_option backward.isDefEq.respectTransparency false in
@[simps]
instance : (forget₂Mon C).Monoidal where
  ε := 𝟙 _
  «μ» G H := 𝟙 _
  «η» := 𝟙 _
  δ G H := 𝟙 _

attribute [local simp] MonObj.tensorObj.mul_def mul_eq_mul comp_mul in
instance instBraidedCategory : BraidedCategory (Grp C) :=
  .ofFaithful (forget₂Mon C) fun G H ↦ Grp.mkIso (β_ G.X H.X)

@[simp] lemma braiding_hom_hom_hom (G H : Grp C) : (β_ G H).hom.hom.hom = (β_ G.X H.X).hom := rfl
@[simp] lemma braiding_inv_hom_hom (G H : Grp C) : (β_ G H).inv.hom.hom = (β_ G.X H.X).inv := rfl

@[deprecated (since := "2025-12-18")] alias braiding_hom_hom := braiding_hom_hom_hom
@[deprecated (since := "2025-12-18")] alias braiding_inv_hom := braiding_inv_hom_hom

end Grp

variable
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [CartesianMonoidalCategory E]

namespace Functor
variable {F F' : C ⥤ D} {G : D ⥤ E}

section Monoidal
variable [F.Monoidal] [F'.Monoidal] [G.Monoidal]

open scoped Obj

/-- The image of a group object under a monoidal functor is a group object. -/
abbrev grpObjObj {G : C} [GrpObj G] : GrpObj (F.obj G) where
  inv := F.map ι
  left_inv := by
    simp [← Functor.map_id, Functor.Monoidal.lift_μ_assoc,
      Functor.Monoidal.toUnit_ε_assoc, ← Functor.map_comp]
  right_inv := by
    simp [← Functor.map_id, Functor.Monoidal.lift_μ_assoc,
      Functor.Monoidal.toUnit_ε_assoc, ← Functor.map_comp]

scoped[CategoryTheory.Obj] attribute [instance] CategoryTheory.Functor.grpObjObj

@[reassoc, simp] lemma obj.ι_def {G : C} [GrpObj G] : ι[F.obj G] = F.map ι := rfl

open Monoidal

variable (F) in
/-- A finite-product-preserving functor takes group objects to group objects. -/
@[simps!]
def mapGrp : Grp C ⥤ Grp D where
  obj A := .mk (F.obj A.X)
  map f := Grp.homMk' (F.mapMon.map f.hom)

protected instance Faithful.mapGrp [F.Faithful] : F.mapGrp.Faithful where
  map_injective hfg :=
    (Grp.forget₂Mon _).map_injective
      (F.mapMon.map_injective ((Grp.forget₂Mon _).congr_map hfg))

/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then
`GrpCat(F) : GrpCat C ⥤ GrpCat D` is fully faithful too. -/
@[simps]
protected def FullyFaithful.mapGrp (hF : F.FullyFaithful) : F.mapGrp.FullyFaithful where
  preimage f := Grp.homMk' (hF.mapMon.preimage f.hom)

protected instance Full.mapGrp [F.Full] [F.Faithful] : F.mapGrp.Full :=
  ((FullyFaithful.ofFullyFaithful F).mapGrp).full

@[simp]
theorem mapGrp_id_one (A : Grp C) :
    η[((𝟭 C).mapGrp.obj A).X] = 𝟙 _ ≫ η[A.X] :=
  rfl

@[simp]
theorem mapGrp_id_mul (A : Grp C) :
    μ[((𝟭 C).mapGrp.obj A).X] = 𝟙 _ ≫ μ[A.X] :=
  rfl

@[simp]
theorem comp_mapGrp_one (A : Grp C) :
    η[((F ⋙ G).mapGrp.obj A).X] = LaxMonoidal.ε (F ⋙ G) ≫ (F ⋙ G).map η[A.X] :=
  rfl

@[simp]
theorem comp_mapGrp_mul (A : Grp C) :
    μ[((F ⋙ G).mapGrp.obj A).X] = LaxMonoidal.μ (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[A.X] :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identity functor is also the identity on group objects. -/
@[simps!]
def mapGrpIdIso : mapGrp (𝟭 C) ≅ 𝟭 (Grp C) :=
  NatIso.ofComponents fun X ↦ Grp.mkIso (.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- The composition functor is also the composition on group objects. -/
@[simps!]
def mapGrpCompIso : (F ⋙ G).mapGrp ≅ F.mapGrp ⋙ G.mapGrp :=
  NatIso.ofComponents fun X ↦ Grp.mkIso (.refl _)

/-- Natural transformations between functors lift to group objects. -/
@[simps!]
def mapGrpNatTrans (f : F ⟶ F') : F.mapGrp ⟶ F'.mapGrp where
  app X := Grp.homMk' ((mapMonNatTrans f).app X.toMon)

/-- Natural isomorphisms between functors lift to group objects. -/
@[simps!]
def mapGrpNatIso (e : F ≅ F') : F.mapGrp ≅ F'.mapGrp :=
  NatIso.ofComponents fun X ↦ Grp.mkIso (e.app _)

attribute [local instance] Monoidal.ofChosenFiniteProducts in
/-- `mapGrp` is functorial in the left-exact functor. -/
@[simps]
noncomputable def mapGrpFunctor : (C ⥤ₗ D) ⥤ Grp C ⥤ Grp D where
  obj F := F.1.mapGrp
  map {F G} α := { app A := Grp.homMk'' (α.hom.app A.X) }

/-- Pullback a group object along a fully faithful monoidal functor. -/
@[simps]
abbrev FullyFaithful.grpObj (hF : F.FullyFaithful) (X : C) [GrpObj (F.obj X)] :
    GrpObj X where
  __ := hF.monObj X
  inv := hF.preimage ι[F.obj X]
  left_inv := hF.map_injective <| by
    simp [OplaxMonoidal.η_of_cartesianMonoidalCategory]
  right_inv := hF.map_injective <| by
    simp [OplaxMonoidal.η_of_cartesianMonoidalCategory]

@[deprecated (since := "2025-09-13")] alias FullyFaithful.grp_Class := FullyFaithful.grpObj

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] MonObj.ofIso_one MonObj.ofIso_mul in
/-- The essential image of a full and faithful functor between cartesian-monoidal categories is the
same on group objects as on objects. -/
@[simp] lemma essImage_mapGrp [F.Full] [F.Faithful] {G : Grp D} :
    F.mapGrp.essImage G ↔ F.essImage G.X where
  mp := by rintro ⟨H, ⟨e⟩⟩; exact ⟨H.X, ⟨(Grp.forget _).mapIso e⟩⟩
  mpr := by
    rintro ⟨H, ⟨e⟩⟩
    let : GrpObj (F.obj H) := .ofIso e.symm
    let : GrpObj H := (FullyFaithful.ofFullyFaithful F).grpObj H
    refine ⟨⟨H⟩, ⟨Grp.mkIso e ?_ ?_⟩⟩ <;> simp

end Monoidal

section Braided
variable [BraidedCategory C] [BraidedCategory D] (F : C ⥤ D) [F.Braided]

open Monoidal LaxMonoidal

noncomputable instance mapGrp.instMonoidal : F.mapGrp.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
  { εIso := (Grp.fullyFaithfulForget₂Mon _).preimageIso (εIso F.mapMon)
    μIso X Y := (Grp.fullyFaithfulForget₂Mon _).preimageIso (μIso F.mapMon X.toMon Y.toMon)
    μIso_hom_natural_left f Z :=
      (Grp.forget₂Mon _).map_injective (μ_natural_left F.mapMon f.hom Z.toMon)
    μIso_hom_natural_right Z f :=
      (Grp.forget₂Mon _).map_injective (μ_natural_right F.mapMon Z.toMon f.hom)
    associativity X Y Z :=
      (Grp.forget₂Mon _).map_injective (associativity F.mapMon X.toMon Y.toMon Z.toMon)
    left_unitality X :=
      (Grp.forget₂Mon _).map_injective (left_unitality F.mapMon X.toMon)
    right_unitality X :=
      (Grp.forget₂Mon _).map_injective (right_unitality F.mapMon X.toMon) }

noncomputable instance mapGrp.instBraided : F.mapGrp.Braided where
  braided X Y :=
    (Grp.forget₂Mon _).map_injective (Braided.braided X.toMon Y.toMon)

end Braided
end Functor

open Functor

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Monoidal] [G.Monoidal]

set_option backward.isDefEq.respectTransparency false in
/-- An adjunction of monoidal functors lifts to an adjunction of their lifts to group objects. -/
@[simps] def mapGrp : F.mapGrp ⊣ G.mapGrp where
  unit := mapGrpIdIso.inv ≫ mapGrpNatTrans a.unit ≫ mapGrpCompIso.hom
  counit := mapGrpCompIso.inv ≫ mapGrpNatTrans a.counit ≫ mapGrpIdIso.hom

end Adjunction

namespace Equivalence
variable (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal]

set_option backward.isDefEq.respectTransparency false in
/-- An equivalence of categories lifts to an equivalence of their group objects. -/
@[simps] def mapGrp : Grp C ≌ Grp D where
  functor := e.functor.mapGrp
  inverse := e.inverse.mapGrp
  unitIso := mapGrpIdIso.symm ≪≫ mapGrpNatIso e.unitIso ≪≫ mapGrpCompIso
  counitIso := mapGrpCompIso.symm ≪≫ mapGrpNatIso e.counitIso ≪≫ mapGrpIdIso

end CategoryTheory.Equivalence
