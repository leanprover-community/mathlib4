import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

universe u v

open CategoryTheory Limits

noncomputable section

variable (C : Type u) [Category.{v, u} C] [HasFiniteProducts C] --[HasTerminal C]

structure GroupObject where
  X : C
--  binary_product : HasBinaryProduct X X
--  ternary_product₁ : HasBinaryProduct X (prod X X)
--  ternary_product₂ : HasBinaryProduct (prod X X) X
  one : ⊤_ C ⟶ X
  mul : prod X X ⟶ X
  inv : X ⟶ X
  one_mul : prod.map one (𝟙 X) ≫ mul = (prod.leftUnitor X).hom := by aesop_cat
  mul_one : prod.map (𝟙 X) one ≫ mul = (prod.rightUnitor X).hom := by aesop_cat
  mul_assoc : prod.map mul (𝟙 X) ≫ mul =
    (Limits.prod.associator X X X).hom ≫ prod.map (𝟙 X) mul ≫ mul := by aesop_cat
  mul_left_inv : prod.lift inv (𝟙 X) ≫ mul = 𝟙 X := by aesop_cat
  mul_right_inv : prod.lift (𝟙 X) inv ≫ mul = 𝟙 X := by aesop_cat

attribute [reassoc] GroupObject.one_mul GroupObject.mul_one

attribute [simp] GroupObject.one_mul GroupObject.mul_one GroupObject.mul_left_inv
  GroupObject.mul_right_inv

attribute [reassoc (attr := simp)] GroupObject.mul_assoc

namespace GroupObject

/-- The trivial group object. We later show this is initial in `GroupObject C`.
-/
@[simps]
def trivial : GroupObject C where
  X := ⊤_ C
  one := 𝟙 _
  mul := (prod.leftUnitor (⊤_ C)).hom
  inv := 𝟙 _

instance : Inhabited (GroupObject C) :=
  ⟨trivial C⟩

variable {C}
variable {G : GroupObject C}

@[simp]
theorem one_mul_hom {Z : C} (f : Z ⟶ G.X) : prod.map G.one f ≫ G.mul =
    (prod.leftUnitor Z).hom ≫ f := by
  rw [← prod.leftUnitor_hom_naturality]
  have : prod.map G.one f = prod.map (𝟙 _) f ≫ prod.map G.one (𝟙 _) := by
    simp only [prod.map_map, Category.id_comp, Category.comp_id]
  rw [this, Category.assoc, G.one_mul]

@[simp]
theorem mul_one_hom {Z : C} (f : Z ⟶ G.X) : prod.map f G.one ≫ G.mul =
    (prod.rightUnitor Z).hom ≫ f := by
  rw [← prod.rightUnitor_hom_naturality]
  have : prod.map f G.one = prod.map f (𝟙 _) ≫ prod.map (𝟙 _) G.one := by
    simp only [prod.map_map, Category.comp_id, Category.id_comp]
  rw [this, Category.assoc, G.mul_one]

theorem assoc_flip : prod.map (𝟙 _) G.mul ≫ G.mul =
    (Limits.prod.associator G.X G.X G.X).inv ≫ prod.map G.mul (𝟙 _) ≫ G.mul := by
  rw [Iso.eq_inv_comp]
  simp only [prod.associator_inv, mul_assoc, prod.associator_hom, prod.lift_map_assoc,
  Category.comp_id]

/-
theorem inv_unique (G : GroupObject C) {f : G.X ⟶ G.X}
  (fleft : prod.lift f (𝟙 _) ≫ G.mul = 𝟙 _)
  (fright : prod.lift (𝟙 _) f ≫ G.mul = 𝟙 _) : f = G.inv := sorry
-/

/-- A morphism of group objects. -/
@[ext]
structure Hom (G H : GroupObject C) where
  hom : G.X ⟶ H.X
  one_hom : G.one ≫ hom = H.one := by aesop_cat
  mul_hom : G.mul ≫ hom = prod.map hom hom ≫ H.mul := by aesop_cat

attribute [reassoc (attr := simp)] Hom.one_hom Hom.mul_hom

/-- The identity morphism on a monoid object. -/
@[simps]
def id (G : GroupObject C) : Hom G G where
  hom := 𝟙 G.X

instance homInhabited (G : GroupObject C) : Inhabited (Hom G G) :=
  ⟨id G⟩

/-- Composition of morphisms of group objects. -/
@[simps]
def comp {G H K : GroupObject C} (f : Hom G H) (g : Hom H K) : Hom G K where
  hom := f.hom ≫ g.hom

instance : Category (GroupObject C) where
  Hom G H := Hom G H
  id := id
  comp f g := comp f g

-- Porting note: added, as `Hom.ext` does not apply to a morphism.
@[ext]
lemma ext {G H : GroupObject C} {f g : G ⟶ H} (w : f.hom = g.hom) : f = g :=
  Hom.ext _ _ w

@[simp]
theorem id_hom' (G : GroupObject C) : (𝟙 G : Hom G G).hom = 𝟙 G.X :=
  rfl

@[simp]
theorem comp_hom' {G H K : GroupObject C} (f : G ⟶ H) (g : H ⟶ K) :
    (f ≫ g : Hom G K).hom = f.hom ≫ g.hom :=
  rfl

section

variable (C)

/-- The forgetful functor from group objects to the ambient category. -/
@[simps]
def forget : GroupObject C ⥤ C where
  obj A := A.X
  map f := f.hom

end

instance forget_faithful : (forget C).Faithful where

instance {A B : GroupObject C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom :=
  e

/-- The forgetful functor from group objects to the ambient category reflects isomorphisms. -/
instance : (forget C).ReflectsIsomorphisms where
  reflects f e :=
    ⟨⟨{ hom := CategoryTheory.inv f.hom
        mul_hom := by simp only [IsIso.comp_inv_eq, Category.assoc, Hom.mul_hom, prod.map_map_assoc,
          IsIso.inv_hom_id, prod.map_id_id, Category.id_comp]},
        by aesop_cat⟩⟩

/-- Construct an isomorphism of groups by giving an isomorphism between the underlying objects
and checking compatibility with unit and multiplication only in the forward direction.
-/
@[simps]
def isoOfIso {G H : GroupObject C} (f : G.X ≅ H.X) (one_f : G.one ≫ f.hom = H.one)
    (mul_f : G.mul ≫ f.hom = prod.map f.hom f.hom ≫ H.mul) : G ≅ H where
  hom :=
    { hom := f.hom
      one_hom := one_f
      mul_hom := mul_f }
  inv :=
    { hom := f.inv
      one_hom := by rw [← one_f]; simp
      mul_hom := by
        rw [← cancel_mono f.hom]
        slice_rhs 2 3 => rw [mul_f]
        simp }

instance uniqueHomFromTrivial (A : GroupObject C) : Unique (trivial C ⟶ A) where
  default :=
    { hom := A.one
      one_hom := by dsimp; simp
      mul_hom := by dsimp; simp [A.one_mul]; rw [Subsingleton.elim prod.snd]}
  uniq f := by
    ext; simp
    rw [← Category.id_comp f.hom]
    erw [f.one_hom]


theorem inv_hom {G H : GroupObject C} (f : G ⟶ H) :
    G.inv ≫ f.hom = f.hom ≫ H.inv := sorry


end GroupObject
