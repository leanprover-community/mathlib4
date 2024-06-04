import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Fubini

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
  mul_left_inv : prod.lift inv (𝟙 X) ≫ mul = (Limits.uniqueToTerminal X).default ≫ one :=
    by aesop_cat
--  mul_right_inv : prod.lift (𝟙 X) inv ≫ mul = (Limits.uniqueToTerminal X).default ≫ one :=
--    by aesop_cat
-- mul_right_inv should be a lemma

attribute [reassoc] GroupObject.one_mul GroupObject.mul_one

attribute [simp] GroupObject.one_mul GroupObject.mul_one GroupObject.mul_left_inv
--  GroupObject.mul_right_inv

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

instance : IsTerminal (trivial C).X := sorry

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
  inv_hom : G.inv ≫ hom = hom ≫ H.inv := by aesop_cat

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
  inv_hom := by rw [← Category.assoc, f.inv_hom, Category.assoc, g.inv_hom, Category.assoc]

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
        inv_hom := by
          rw [IsIso.eq_inv_comp, ← Category.assoc, ← f.inv_hom,
            Category.assoc, IsIso.hom_inv_id, Category.comp_id]
        },
        by aesop_cat⟩⟩

/-- Construct an isomorphism of groups by giving an isomorphism between the underlying objects
and checking compatibility with unit and multiplication only in the forward direction.
-/
@[simps]
def isoOfIso {G H : GroupObject C} (f : G.X ≅ H.X) (one_f : G.one ≫ f.hom = H.one)
    (mul_f : G.mul ≫ f.hom = prod.map f.hom f.hom ≫ H.mul)
    (inv_f : G.inv ≫ f.hom = f.hom ≫ H.inv) : G ≅ H where
  hom :=
    { hom := f.hom
      one_hom := one_f
      mul_hom := mul_f
      inv_hom := inv_f
    }
  inv :=
    { hom := f.inv
      one_hom := by rw [← one_f]; simp
      mul_hom := by
        rw [← cancel_mono f.hom]
        slice_rhs 2 3 => rw [mul_f]
        simp
      inv_hom := by
        rw [Iso.eq_inv_comp, ← Category.assoc, ← inv_f, Category.assoc, Iso.hom_inv_id,
          Category.comp_id]
    }

instance uniqueHomFromTrivial (A : GroupObject C) : Unique (trivial C ⟶ A) where
  default :=
    { hom := A.one
      mul_hom := by dsimp; simp [A.one_mul]; rw [Subsingleton.elim prod.snd]
      inv_hom := by
        dsimp; rw [Category.id_comp]
        sorry
    }
  uniq f := by
    ext; simp
    rw [← Category.id_comp f.hom]
    erw [f.one_hom]
-- Might have to put this one later, it needs G.one = G.one ≫ G.inv.

instance uniqueHomToTrivial (A : GroupObject C) : Unique (A ⟶ trivial C) where
  default :=
    { hom := (default : A.X ⟶ ⊤_ C) }
  uniq f := by
    ext; simp only [trivial_X]
    convert Subsingleton.elim f.hom default
    simp only [trivial_X]
    exact inferInstance


/- Limits of group objects.-/

variable {J : Type*} [Category J] [HasLimitsOfShape J C]
  [HasLimitsOfShape (Discrete WalkingPair × J) C] [HasLimitsOfShape (J × Discrete WalkingPair) C]

example (F : J ⥤ GroupObject C) : Cone F where
  pt :=
  {
    X := limit (F ⋙ forget C)
    one := sorry
    mul := by
      set e := limitFlipCompLimIsoLimitCompLim (pair (F ⋙ forget C) (F ⋙ forget C))
      set f := HasLimit.isoOfNatIso (pairComp (F ⋙ forget C) (F ⋙ forget C)
        (lim : (J ⥤ C) ⥤ C))
      refine (f.symm.trans e.symm).hom ≫ limMap ?_
      have g : ∀ (j : J),
          (pair (F ⋙ forget C) (F ⋙ forget C)).flip.obj j ≅ pair (F.obj j).X (F.obj j).X :=
        fun _ ↦ mapPairIso (Iso.refl _) (Iso.refl _)
      exact
      {
        app := fun j ↦ (HasLimit.isoOfNatIso (g j)).hom ≫ (F.obj j).mul
        naturality := by
          intro j j' f
          simp only [Functor.comp_obj, lim_obj, forget_obj, Functor.comp_map, lim_map, forget_map,
            Category.assoc, Hom.mul_hom]
          sorry 
      }
    inv := sorry
  }
  π := sorry


/- The Yoneda embedding.-/

def HomAsGroup (X : C) (G : GroupObject C) : Group (X ⟶ G.X) where
  mul f g := prod.lift f g ≫ G.mul
  mul_assoc f g h := by
    change prod.lift (_ ≫ G.mul) _ ≫ G.mul = prod.lift _ (_ ≫ G.mul) ≫ G.mul
    have h₁ : prod.lift (prod.lift f g ≫ G.mul) h = prod.lift (prod.lift f g) h ≫
        prod.map G.mul (𝟙 G.X) := by simp only [prod.lift_map, Category.comp_id]
    have h₂ : prod.lift f (prod.lift g h ≫ G.mul) = prod.lift f (prod.lift g h) ≫
        prod.map (𝟙 G.X) G.mul := by simp only [prod.lift_map, Category.comp_id]
    rw [h₁, h₂, Category.assoc, Category.assoc, G.mul_assoc]
    rw [← Category.assoc]; congr 1
    simp only [prod.associator_hom, prod.comp_lift, limit.lift_π_assoc, BinaryFan.mk_pt,
      pair_obj_left, BinaryFan.π_app_left, BinaryFan.mk_fst, limit.lift_π, BinaryFan.π_app_right,
      BinaryFan.mk_snd]
  one := (Limits.uniqueToTerminal X).default ≫ G.one
  one_mul f := by
    change _ ≫ G.mul = _
    have : ∀ (h : X ⟶ ⊤_ C), prod.lift (h ≫ G.one) f = prod.lift h f ≫
      prod.map G.one (𝟙 _) := by simp only [prod.lift_map, Category.comp_id, implies_true]
    erw [this]
    rw [Category.assoc, G.one_mul]
    simp only [prod.leftUnitor_hom, limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right,
      BinaryFan.mk_snd]
  mul_one f := by
    change _ ≫ G.mul = _
    have : ∀ (h : X ⟶ ⊤_ C), prod.lift f (h ≫ G.one) = prod.lift f h ≫
      prod.map (𝟙 _) G.one := by simp only [prod.lift_map, Category.comp_id, implies_true]
    erw [this]
    rw [Category.assoc, G.mul_one]
    simp only [prod.rightUnitor_hom, limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_left,
      BinaryFan.mk_fst]
  inv f := f ≫ G.inv
  mul_left_inv f := by
    change prod.lift (_ ≫ G.inv) _ ≫ G.mul = _
    have : prod.lift (f ≫ G.inv) f = f ≫ prod.lift G.inv (𝟙 _) := by
      simp only [prod.comp_lift, Category.comp_id]
    rw [this, Category.assoc, G.mul_left_inv, ← Category.assoc,
      Subsingleton.elim (f ≫ default) default]
    rfl

end GroupObject
