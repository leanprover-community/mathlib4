/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Equivalence

#align_import category_theory.adjunction.basic from "leanprover-community/mathlib"@"d101e93197bb5f6ea89bd7ba386b7f7dff1f3903"

/-!
# Adjunctions between functors

`F ⊣ G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.

We provide various useful constructors:
* `mkOfHomEquiv`
* `mkOfUnitCounit`
* `leftAdjointOfEquiv` / `rightAdjointOfEquiv`
  construct a left/right adjoint of a given functor given the action on objects and
  the relevant equivalence of morphism spaces.
* `adjunctionOfEquivLeft` / `adjunctionOfEquivRight` witness that these constructions
  give adjunctions.

There are also typeclasses `IsLeftAdjoint` / `IsRightAdjoint`, carrying data witnessing
that a given functor is a left or right adjoint.
Given `[IsLeftAdjoint F]`, a right adjoint of `F` can be constructed as `rightAdjoint F`.

`Adjunction.comp` composes adjunctions.

`toEquivalence` upgrades an adjunction to an equivalence,
given witnesses that the unit and counit are pointwise isomorphisms.
Conversely `Equivalence.toAdjunction` recovers the underlying adjunction from an equivalence.
-/


namespace CategoryTheory

open Category

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

-- Porting Note: `elab_without_expected_type` cannot be a local attribute
-- attribute [local elab_without_expected_type] whiskerLeft whiskerRight

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- `F ⊣ G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.

To construct an `adjunction` between two functors, it's often easier to instead use the
constructors `mkOfHomEquiv` or `mkOfUnitCounit`. To construct a left adjoint,
there are also constructors `leftAdjointOfEquiv` and `adjunctionOfEquivLeft` (as
well as their duals) which can be simpler in practice.

Uniqueness of adjoints is shown in `CategoryTheory.Adjunction.Opposites`.

See <https://stacks.math.columbia.edu/tag/0037>.
-/
structure Adjunction (F : C ⥤ D) (G : D ⥤ C) where
  /-- The equivalence between `Hom (F X) Y` and `Hom X (G Y)` coming from an adjunction -/
  homEquiv : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  /-- The unit of an adjunction -/
  unit : 𝟭 C ⟶ F.comp G
  /-- The counit of an adjunction -/
  counit : G.comp F ⟶ 𝟭 D
  -- Porting note: It's strange that this `Prop` is being flagged by the `docBlame` linter
  /-- Naturality of the unit of an adjunction -/
  homEquiv_unit : ∀ {X Y f}, (homEquiv X Y) f = (unit : _ ⟶ _).app X ≫ G.map f := by aesop_cat
  -- Porting note: It's strange that this `Prop` is being flagged by the `docBlame` linter
  /-- Naturality of the counit of an adjunction -/
  homEquiv_counit : ∀ {X Y g}, (homEquiv X Y).symm g = F.map g ≫ counit.app Y := by aesop_cat
#align category_theory.adjunction CategoryTheory.Adjunction
#align category_theory.adjunction.hom_equiv CategoryTheory.Adjunction.homEquiv
#align category_theory.adjunction.hom_equiv_unit CategoryTheory.Adjunction.homEquiv_unit
#align category_theory.adjunction.hom_equiv_unit' CategoryTheory.Adjunction.homEquiv_unit
#align category_theory.adjunction.hom_equiv_counit CategoryTheory.Adjunction.homEquiv_counit
#align category_theory.adjunction.hom_equiv_counit' CategoryTheory.Adjunction.homEquiv_counit

-- mathport name: «expr ⊣ »
/-- The notation `F ⊣ G` stands for `Adjunction F G` representing that `F` is left adjoint to `G` -/
infixl:15 " ⊣ " => Adjunction

/-- A class giving a chosen right adjoint to the functor `left`. -/
class IsLeftAdjoint (left : C ⥤ D) where
  /-- The right adjoint to `left` -/
  right : D ⥤ C
  /-- The adjunction between `left` and `right` -/
  adj : left ⊣ right
#align category_theory.is_left_adjoint CategoryTheory.IsLeftAdjoint

/-- A class giving a chosen left adjoint to the functor `right`. -/
class IsRightAdjoint (right : D ⥤ C) where
  /-- The left adjoint to `right` -/
  left : C ⥤ D
  /-- The adjunction between `left` and `right` -/
  adj : left ⊣ right
#align category_theory.is_right_adjoint CategoryTheory.IsRightAdjoint

/-- Extract the left adjoint from the instance giving the chosen adjoint. -/
def leftAdjoint (R : D ⥤ C) [IsRightAdjoint R] : C ⥤ D :=
  IsRightAdjoint.left R
#align category_theory.left_adjoint CategoryTheory.leftAdjoint

/-- Extract the right adjoint from the instance giving the chosen adjoint. -/
def rightAdjoint (L : C ⥤ D) [IsLeftAdjoint L] : D ⥤ C :=
  IsLeftAdjoint.right L
#align category_theory.right_adjoint CategoryTheory.rightAdjoint

/-- The adjunction associated to a functor known to be a left adjoint. -/
def Adjunction.ofLeftAdjoint (left : C ⥤ D) [IsLeftAdjoint left] :
    Adjunction left (rightAdjoint left) :=
  IsLeftAdjoint.adj
#align category_theory.adjunction.of_left_adjoint CategoryTheory.Adjunction.ofLeftAdjoint

/-- The adjunction associated to a functor known to be a right adjoint. -/
def Adjunction.ofRightAdjoint (right : C ⥤ D) [IsRightAdjoint right] :
    Adjunction (leftAdjoint right) right :=
  IsRightAdjoint.adj
#align category_theory.adjunction.of_right_adjoint CategoryTheory.Adjunction.ofRightAdjoint

namespace Adjunction

-- Porting note: Workaround not needed in Lean 4
-- restate_axiom homEquiv_unit'

-- restate_axiom homEquiv_counit'

attribute [simp] homEquiv_unit homEquiv_counit

section

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X' X : C} {Y Y' : D}

theorem homEquiv_id (X : C) : adj.homEquiv X _ (𝟙 _) = adj.unit.app X := by simp
#align category_theory.adjunction.hom_equiv_id CategoryTheory.Adjunction.homEquiv_id

theorem homEquiv_symm_id (X : D) : (adj.homEquiv _ X).symm (𝟙 _) = adj.counit.app X := by simp
#align category_theory.adjunction.hom_equiv_symm_id CategoryTheory.Adjunction.homEquiv_symm_id

/-
Porting note: `nolint simpNF` as the linter was complaining that this was provable using `simp`
but it is in fact not. Also the `docBlame` linter expects a docstring even though this is `Prop`
valued
-/
@[simp, nolint simpNF]
theorem homEquiv_naturality_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) :
    (adj.homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (adj.homEquiv X Y).symm g := by
  rw [homEquiv_counit, F.map_comp, assoc, adj.homEquiv_counit.symm]
#align category_theory.adjunction.hom_equiv_naturality_left_symm CategoryTheory.Adjunction.homEquiv_naturality_left_symm

-- Porting note: Same as above
@[simp, nolint simpNF]
theorem homEquiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (adj.homEquiv X Y) g := by
  rw [← Equiv.eq_symm_apply]
  simp only [Equiv.symm_apply_apply,eq_self_iff_true,homEquiv_naturality_left_symm]
#align category_theory.adjunction.hom_equiv_naturality_left CategoryTheory.Adjunction.homEquiv_naturality_left

-- Porting note: Same as above
@[simp, nolint simpNF]
theorem homEquiv_naturality_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y') (f ≫ g) = (adj.homEquiv X Y) f ≫ G.map g := by
  rw [homEquiv_unit, G.map_comp, ← assoc, ← homEquiv_unit]
#align category_theory.adjunction.hom_equiv_naturality_right CategoryTheory.Adjunction.homEquiv_naturality_right

-- Porting note: Same as above
@[simp, nolint simpNF]
theorem homEquiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y').symm (f ≫ G.map g) = (adj.homEquiv X Y).symm f ≫ g := by
  rw [Equiv.symm_apply_eq]
  simp only [homEquiv_naturality_right,eq_self_iff_true,Equiv.apply_symm_apply]
#align category_theory.adjunction.hom_equiv_naturality_right_symm CategoryTheory.Adjunction.homEquiv_naturality_right_symm

@[simp]
theorem left_triangle : whiskerRight adj.unit F ≫ whiskerLeft F adj.counit = 𝟙 _ := by
  ext; dsimp
  erw [← adj.homEquiv_counit, Equiv.symm_apply_eq, adj.homEquiv_unit]
  simp
#align category_theory.adjunction.left_triangle CategoryTheory.Adjunction.left_triangle

@[simp]
theorem right_triangle : whiskerLeft G adj.unit ≫ whiskerRight adj.counit G = 𝟙 _ := by
  ext; dsimp
  erw [← adj.homEquiv_unit, ← Equiv.eq_symm_apply, adj.homEquiv_counit]
  simp
#align category_theory.adjunction.right_triangle CategoryTheory.Adjunction.right_triangle

variable (X Y)

@[reassoc (attr := simp)]
theorem left_triangle_components :
    F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X) = 𝟙 (F.obj X) :=
  congr_arg (fun t : NatTrans _ (𝟭 C ⋙ F) => t.app X) adj.left_triangle
#align category_theory.adjunction.left_triangle_components CategoryTheory.Adjunction.left_triangle_components

@[reassoc (attr := simp)]
theorem right_triangle_components :
    adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y) = 𝟙 (G.obj Y) :=
  congr_arg (fun t : NatTrans _ (G ⋙ 𝟭 C) => t.app Y) adj.right_triangle
#align category_theory.adjunction.right_triangle_components CategoryTheory.Adjunction.right_triangle_components

variable {X Y}

@[reassoc (attr := simp)]
theorem counit_naturality {X Y : D} (f : X ⟶ Y) :
    F.map (G.map f) ≫ adj.counit.app Y = adj.counit.app X ≫ f :=
  adj.counit.naturality f
#align category_theory.adjunction.counit_naturality CategoryTheory.Adjunction.counit_naturality

@[reassoc (attr := simp)]
theorem unit_naturality {X Y : C} (f : X ⟶ Y) :
    adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app Y :=
  (adj.unit.naturality f).symm
#align category_theory.adjunction.unit_naturality CategoryTheory.Adjunction.unit_naturality

theorem homEquiv_apply_eq {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    adj.homEquiv A B f = g ↔ f = (adj.homEquiv A B).symm g :=
  ⟨fun h => by
    cases h
    simp, fun h => by
    cases h
    simp⟩
#align category_theory.adjunction.hom_equiv_apply_eq CategoryTheory.Adjunction.homEquiv_apply_eq

theorem eq_homEquiv_apply {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    g = adj.homEquiv A B f ↔ (adj.homEquiv A B).symm g = f :=
  ⟨fun h => by
    cases h
    simp, fun h => by
    cases h
    simp⟩
#align category_theory.adjunction.eq_hom_equiv_apply CategoryTheory.Adjunction.eq_homEquiv_apply

end

end Adjunction

namespace Adjunction

/-- This is an auxiliary data structure useful for constructing adjunctions.
See `Adjunction.mkOfHomEquiv`.
This structure won't typically be used anywhere else.
-/
-- Porting comment: `has_nonempty_instance` linter doesn't exist (yet?)
-- @[nolint has_nonempty_instance]
structure CoreHomEquiv (F : C ⥤ D) (G : D ⥤ C) where
  /-- The equivalence between `Hom (F X) Y` and `Hom X (G Y)` -/
  homEquiv : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  /-- The property that describes how `homEquiv.symm` transforms compositions `X' ⟶ X ⟶ G Y` -/
  homEquiv_naturality_left_symm :
    ∀ {X' X Y} (f : X' ⟶ X) (g : X ⟶ G.obj Y),
      (homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (homEquiv X Y).symm g := by
    aesop_cat
  /-- The property that describes how `homEquiv` transforms compositions `F X ⟶ Y ⟶ Y'` -/
  homEquiv_naturality_right :
    ∀ {X Y Y'} (f : F.obj X ⟶ Y) (g : Y ⟶ Y'),
      (homEquiv X Y') (f ≫ g) = (homEquiv X Y) f ≫ G.map g := by
    aesop_cat
#align category_theory.adjunction.core_hom_equiv CategoryTheory.Adjunction.CoreHomEquiv
#align category_theory.adjunction.core_hom_equiv.hom_equiv CategoryTheory.Adjunction.CoreHomEquiv.homEquiv
#align category_theory.adjunction.core_hom_equiv.hom_equiv' CategoryTheory.Adjunction.CoreHomEquiv.homEquiv
#align category_theory.adjunction.core_hom_equiv.hom_equiv_naturality_right CategoryTheory.Adjunction.CoreHomEquiv.homEquiv_naturality_right
#align category_theory.adjunction.core_hom_equiv.hom_equiv_naturality_right' CategoryTheory.Adjunction.CoreHomEquiv.homEquiv_naturality_right
#align category_theory.adjunction.core_hom_equiv.hom_equiv_naturality_left_symm CategoryTheory.Adjunction.CoreHomEquiv.homEquiv_naturality_left_symm
#align category_theory.adjunction.core_hom_equiv.hom_equiv_naturality_left_symm' CategoryTheory.Adjunction.CoreHomEquiv.homEquiv_naturality_left_symm

namespace CoreHomEquiv

-- Porting note: Workaround not needed in Lean 4.
-- restate_axiom homEquiv_naturality_left_symm'

-- restate_axiom homEquiv_naturality_right'

attribute [simp] homEquiv_naturality_left_symm homEquiv_naturality_right

variable {F : C ⥤ D} {G : D ⥤ C} (adj : CoreHomEquiv F G) {X' X : C} {Y Y' : D}

@[simp]
theorem homEquiv_naturality_left_aux (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.homEquiv X' (F.obj X)) (F.map f) ≫ G.map g = f ≫ (adj.homEquiv X Y) g := by
  rw [← homEquiv_naturality_right, ← Equiv.eq_symm_apply]; simp

-- @[simp] -- Porting note: LHS simplifies, added aux lemma above
theorem homEquiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (adj.homEquiv X Y) g := by
  rw [← Equiv.eq_symm_apply]; simp
#align category_theory.adjunction.core_hom_equiv.hom_equiv_naturality_left CategoryTheory.Adjunction.CoreHomEquiv.homEquiv_naturality_left

@[simp]
theorem homEquiv_naturality_right_symm_aux (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
    F.map f ≫ (adj.homEquiv (G.obj Y) Y').symm (G.map g) = (adj.homEquiv X Y).symm f ≫ g := by
  rw [← homEquiv_naturality_left_symm, Equiv.symm_apply_eq]; simp

-- @[simp] -- Porting note: LHS simplifies, added aux lemma above
theorem homEquiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y').symm (f ≫ G.map g) = (adj.homEquiv X Y).symm f ≫ g := by
  rw [Equiv.symm_apply_eq]; simp
#align category_theory.adjunction.core_hom_equiv.hom_equiv_naturality_right_symm CategoryTheory.Adjunction.CoreHomEquiv.homEquiv_naturality_right_symm

end CoreHomEquiv

/-- This is an auxiliary data structure useful for constructing adjunctions.
See `Adjunction.mkOfUnitCounit`.
This structure won't typically be used anywhere else.
-/
-- Porting comment: `has_nonempty_instance` linter doesn't exist (yet?)
-- @[nolint has_nonempty_instance]
structure CoreUnitCounit (F : C ⥤ D) (G : D ⥤ C) where
  /-- The unit of an adjunction between `F` and `G` -/
  unit : 𝟭 C ⟶ F.comp G
  /-- The counit of an adjunction between `F` and `G`s -/
  counit : G.comp F ⟶ 𝟭 D
  /-- Equality of the composition of the unit, associator, and counit with the identity
  `F ⟶ (F G) F ⟶ F (G F) ⟶ F = NatTrans.id F` -/
  left_triangle :
    whiskerRight unit F ≫ (Functor.associator F G F).hom ≫ whiskerLeft F counit =
      NatTrans.id (𝟭 C ⋙ F) := by
    aesop_cat
  /-- Equality of the composition of the unit, associator, and counit with the identity
  `G ⟶ G (F G) ⟶ (F G) F ⟶ G = NatTrans.id G` -/
  right_triangle :
    whiskerLeft G unit ≫ (Functor.associator G F G).inv ≫ whiskerRight counit G =
      NatTrans.id (G ⋙ 𝟭 C) := by
    aesop_cat
#align category_theory.adjunction.core_unit_counit CategoryTheory.Adjunction.CoreUnitCounit
#align category_theory.adjunction.core_unit_counit.left_triangle' CategoryTheory.Adjunction.CoreUnitCounit.left_triangle
#align category_theory.adjunction.core_unit_counit.left_triangle CategoryTheory.Adjunction.CoreUnitCounit.left_triangle
#align category_theory.adjunction.core_unit_counit.right_triangle' CategoryTheory.Adjunction.CoreUnitCounit.right_triangle
#align category_theory.adjunction.core_unit_counit.right_triangle CategoryTheory.Adjunction.CoreUnitCounit.right_triangle

namespace CoreUnitCounit

attribute [simp] left_triangle right_triangle

end CoreUnitCounit

variable {F : C ⥤ D} {G : D ⥤ C}

/-- Construct an adjunction between `F` and `G` out of a natural bijection between each
`F.obj X ⟶ Y` and `X ⟶ G.obj Y`. -/
@[simps]
def mkOfHomEquiv (adj : CoreHomEquiv F G) : F ⊣ G :=
  -- See note [dsimp, simp].
  { adj with
    unit :=
      { app := fun X => (adj.homEquiv X (F.obj X)) (𝟙 (F.obj X))
        naturality := by
          intros
          erw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
          dsimp; simp }
    counit :=
      { app := fun Y => (adj.homEquiv _ _).invFun (𝟙 (G.obj Y))
        naturality := by
          intros
          erw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
          dsimp; simp }
    homEquiv_unit := @fun X Y f => by erw [← adj.homEquiv_naturality_right]; simp
    homEquiv_counit := @fun X Y f => by erw [← adj.homEquiv_naturality_left_symm]; simp
  }
#align category_theory.adjunction.mk_of_hom_equiv CategoryTheory.Adjunction.mkOfHomEquiv

/-- Construct an adjunction between functors `F` and `G` given a unit and counit for the adjunction
satisfying the triangle identities. -/

@[simps!]
def mkOfUnitCounit (adj : CoreUnitCounit F G) : F ⊣ G :=
  { adj with
    homEquiv := fun X Y =>
      { toFun := fun f => adj.unit.app X ≫ G.map f
        invFun := fun g => F.map g ≫ adj.counit.app Y
        left_inv := fun f => by
          change F.map (_ ≫ _) ≫ _ = _
          rw [F.map_comp, assoc, ← Functor.comp_map, adj.counit.naturality, ← assoc]
          convert id_comp f
          have t := congrArg (fun (s : NatTrans (𝟭 C ⋙ F) (F ⋙ 𝟭 D)) => s.app X) adj.left_triangle
          dsimp at t
          simp only [id_comp] at t
          exact t
        right_inv := fun g => by
          change _ ≫ G.map (_ ≫ _) = _
          rw [G.map_comp, ← assoc, ← Functor.comp_map, ← adj.unit.naturality, assoc]
          convert comp_id g
          have t := congrArg (fun t : NatTrans (G ⋙ 𝟭 C) (𝟭 D ⋙ G) => t.app Y) adj.right_triangle
          dsimp at t
          simp only [id_comp] at t
          exact t } }
#align category_theory.adjunction.mk_of_unit_counit CategoryTheory.Adjunction.mkOfUnitCounit

/- Porting note: simpNF linter claims these are solved by simp but that
is not true -/
attribute [nolint simpNF] CategoryTheory.Adjunction.mkOfUnitCounit_homEquiv_symm_apply
attribute [nolint simpNF] CategoryTheory.Adjunction.mkOfUnitCounit_homEquiv_apply

/-- The adjunction between the identity functor on a category and itself. -/
def id : 𝟭 C ⊣ 𝟭 C where
  homEquiv X Y := Equiv.refl _
  unit := 𝟙 _
  counit := 𝟙 _
#align category_theory.adjunction.id CategoryTheory.Adjunction.id

-- Satisfy the inhabited linter.
instance : Inhabited (Adjunction (𝟭 C) (𝟭 C)) :=
  ⟨id⟩

/-- If F and G are naturally isomorphic functors, establish an equivalence of hom-sets. -/
@[simps]
def equivHomsetLeftOfNatIso {F F' : C ⥤ D} (iso : F ≅ F') {X : C} {Y : D} :
    (F.obj X ⟶ Y) ≃ (F'.obj X ⟶ Y)
    where
  toFun f := iso.inv.app _ ≫ f
  invFun g := iso.hom.app _ ≫ g
  left_inv f := by simp
  right_inv g := by simp
#align category_theory.adjunction.equiv_homset_left_of_nat_iso CategoryTheory.Adjunction.equivHomsetLeftOfNatIso

/-- If G and H are naturally isomorphic functors, establish an equivalence of hom-sets. -/
@[simps]
def equivHomsetRightOfNatIso {G G' : D ⥤ C} (iso : G ≅ G') {X : C} {Y : D} :
    (X ⟶ G.obj Y) ≃ (X ⟶ G'.obj Y)
    where
  toFun f := f ≫ iso.hom.app _
  invFun g := g ≫ iso.inv.app _
  left_inv f := by simp
  right_inv g := by simp
#align category_theory.adjunction.equiv_homset_right_of_nat_iso CategoryTheory.Adjunction.equivHomsetRightOfNatIso

/-- Transport an adjunction along a natural isomorphism on the left. -/
def ofNatIsoLeft {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) : G ⊣ H :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => (equivHomsetLeftOfNatIso iso.symm).trans (adj.homEquiv X Y) }
#align category_theory.adjunction.of_nat_iso_left CategoryTheory.Adjunction.ofNatIsoLeft

/-- Transport an adjunction along a natural isomorphism on the right. -/
def ofNatIsoRight {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) : F ⊣ H :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => (adj.homEquiv X Y).trans (equivHomsetRightOfNatIso iso) }
#align category_theory.adjunction.of_nat_iso_right CategoryTheory.Adjunction.ofNatIsoRight

/-- Transport being a right adjoint along a natural isomorphism. -/
def rightAdjointOfNatIso {F G : C ⥤ D} (h : F ≅ G) [r : IsRightAdjoint F] : IsRightAdjoint G
    where
  left := r.left
  adj := ofNatIsoRight r.adj h
#align category_theory.adjunction.right_adjoint_of_nat_iso CategoryTheory.Adjunction.rightAdjointOfNatIso

/-- Transport being a left adjoint along a natural isomorphism. -/
def leftAdjointOfNatIso {F G : C ⥤ D} (h : F ≅ G) [r : IsLeftAdjoint F] : IsLeftAdjoint G
    where
  right := r.right
  adj := ofNatIsoLeft r.adj h
#align category_theory.adjunction.left_adjoint_of_nat_iso CategoryTheory.Adjunction.leftAdjointOfNatIso

section

variable {E : Type u₃} [ℰ : Category.{v₃} E] {H : D ⥤ E} {I : E ⥤ D}

/-- Composition of adjunctions.

See <https://stacks.math.columbia.edu/tag/0DV0>.
-/
def comp (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) : F ⋙ H ⊣ I ⋙ G
    where
  homEquiv X Z := Equiv.trans (adj₂.homEquiv _ _) (adj₁.homEquiv _ _)
  unit := adj₁.unit ≫ (whiskerLeft F <| whiskerRight adj₂.unit G) ≫ (Functor.associator _ _ _).inv
  counit :=
    (Functor.associator _ _ _).hom ≫ (whiskerLeft I <| whiskerRight adj₁.counit H) ≫ adj₂.counit
#align category_theory.adjunction.comp CategoryTheory.Adjunction.comp

/-- If `F` and `G` are left adjoints then `F ⋙ G` is a left adjoint too. -/
instance leftAdjointOfComp {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [Fl : IsLeftAdjoint F] [Gl : IsLeftAdjoint G] : IsLeftAdjoint (F ⋙ G)
    where
  right := Gl.right ⋙ Fl.right
  adj := Fl.adj.comp Gl.adj
#align category_theory.adjunction.left_adjoint_of_comp CategoryTheory.Adjunction.leftAdjointOfComp

/-- If `F` and `G` are right adjoints then `F ⋙ G` is a right adjoint too. -/
instance rightAdjointOfComp {E : Type u₃} [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E}
    [Fr : IsRightAdjoint F] [Gr : IsRightAdjoint G] : IsRightAdjoint (F ⋙ G)
    where
  left := Gr.left ⋙ Fr.left
  adj := Gr.adj.comp Fr.adj
#align category_theory.adjunction.right_adjoint_of_comp CategoryTheory.Adjunction.rightAdjointOfComp

end

section ConstructLeft

-- Construction of a left adjoint. In order to construct a left
-- adjoint to a functor G : D → C, it suffices to give the object part
-- of a functor F : C → D together with isomorphisms Hom(FX, Y) ≃
-- Hom(X, GY) natural in Y. The action of F on morphisms can be
-- constructed from this data.
variable {F_obj : C → D}
variable (e : ∀ X Y, (F_obj X ⟶ Y) ≃ (X ⟶ G.obj Y))
variable (he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g)

private theorem he' {X Y Y'} (f g) : (e X Y').symm (f ≫ G.map g) = (e X Y).symm f ≫ g := by
  rw [Equiv.symm_apply_eq, he]; simp
-- #align category_theory.adjunction.he' category_theory.adjunction.he'

/-- Construct a left adjoint functor to `G`, given the functor's value on objects `F_obj` and
a bijection `e` between `F_obj X ⟶ Y` and `X ⟶ G.obj Y` satisfying a naturality law
`he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g`.
Dual to `rightAdjointOfEquiv`. -/
@[simps!]
def leftAdjointOfEquiv : C ⥤ D where
  obj := F_obj
  map {X} {X'} f := (e X (F_obj X')).symm (f ≫ e X' (F_obj X') (𝟙 _))
  map_comp := fun f f' => by
    rw [Equiv.symm_apply_eq, he, Equiv.apply_symm_apply]
    conv =>
      rhs
      rw [assoc, ← he, id_comp, Equiv.apply_symm_apply]
    simp
#align category_theory.adjunction.left_adjoint_of_equiv CategoryTheory.Adjunction.leftAdjointOfEquiv

/-- Show that the functor given by `leftAdjointOfEquiv` is indeed left adjoint to `G`. Dual
to `adjunctionOfRightEquiv`. -/
@[simps!]
def adjunctionOfEquivLeft : leftAdjointOfEquiv e he ⊣ G :=
  mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := fun {X'} {X} {Y} f g => by
        have := @he' C _ D _ G F_obj e he
        erw [← this, ← Equiv.apply_eq_iff_eq (e X' Y)]
        simp only [leftAdjointOfEquiv_obj, Equiv.apply_symm_apply, assoc]
        congr
        rw [← he]
        simp
    }
#align category_theory.adjunction.adjunction_of_equiv_left CategoryTheory.Adjunction.adjunctionOfEquivLeft

end ConstructLeft

section ConstructRight

-- Construction of a right adjoint, analogous to the above.
variable {G_obj : D → C}
variable (e : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G_obj Y))
variable (he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g)

private theorem he'' {X' X Y} (f g) : F.map f ≫ (e X Y).symm g = (e X' Y).symm (f ≫ g) := by
  rw [Equiv.eq_symm_apply, he]; simp
-- #align category_theory.adjunction.he' category_theory.adjunction.he'

/-- Construct a right adjoint functor to `F`, given the functor's value on objects `G_obj` and
a bijection `e` between `F.obj X ⟶ Y` and `X ⟶ G_obj Y` satisfying a naturality law
`he : ∀ X Y Y' g h, e X' Y (F.map f ≫ g) = f ≫ e X Y g`.
Dual to `leftAdjointOfEquiv`. -/
@[simps!]
def rightAdjointOfEquiv : D ⥤ C where
  obj := G_obj
  map {Y} {Y'} g := (e (G_obj Y) Y') ((e (G_obj Y) Y).symm (𝟙 _) ≫ g)
  map_comp := fun {Y} {Y'} {Y''} g g' => by
    rw [← Equiv.eq_symm_apply, ← he'' e he, Equiv.symm_apply_apply]
    conv =>
      rhs
      rw [← assoc, he'' e he, comp_id, Equiv.symm_apply_apply]
    simp
#align category_theory.adjunction.right_adjoint_of_equiv CategoryTheory.Adjunction.rightAdjointOfEquiv

/-- Show that the functor given by `rightAdjointOfEquiv` is indeed right adjoint to `F`. Dual
to `adjunctionOfEquivRight`. -/
@[simps!]
def adjunctionOfEquivRight : F ⊣ (rightAdjointOfEquiv e he) :=
  mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := by
        intro X X' Y f g; rw [Equiv.symm_apply_eq]; dsimp; rw [he]; simp
      homEquiv_naturality_right := by
        intro X Y Y' g h
        erw [← he, Equiv.apply_eq_iff_eq, ← assoc, he'' e he, comp_id, Equiv.symm_apply_apply] }
#align category_theory.adjunction.adjunction_of_equiv_right CategoryTheory.Adjunction.adjunctionOfEquivRight

end ConstructRight

/--
If the unit and counit of a given adjunction are (pointwise) isomorphisms, then we can upgrade the
adjunction to an equivalence.
-/
@[simps!]
noncomputable def toEquivalence (adj : F ⊣ G) [∀ X, IsIso (adj.unit.app X)]
    [∀ Y, IsIso (adj.counit.app Y)] : C ≌ D
    where
  functor := F
  inverse := G
  unitIso := NatIso.ofComponents fun X => asIso (adj.unit.app X)
  counitIso := NatIso.ofComponents fun Y => asIso (adj.counit.app Y)
#align category_theory.adjunction.to_equivalence CategoryTheory.Adjunction.toEquivalence

/--
If the unit and counit for the adjunction corresponding to a right adjoint functor are (pointwise)
isomorphisms, then the functor is an equivalence of categories.
-/
@[simps!]
noncomputable def isRightAdjointToIsEquivalence [IsRightAdjoint G]
    [∀ X, IsIso ((Adjunction.ofRightAdjoint G).unit.app X)]
    [∀ Y, IsIso ((Adjunction.ofRightAdjoint G).counit.app Y)] : IsEquivalence G :=
  IsEquivalence.ofEquivalenceInverse (Adjunction.ofRightAdjoint G).toEquivalence
#align category_theory.adjunction.is_right_adjoint_to_is_equivalence CategoryTheory.Adjunction.isRightAdjointToIsEquivalence

end Adjunction

open Adjunction

namespace Equivalence

/-- The adjunction given by an equivalence of categories. (To obtain the opposite adjunction,
simply use `e.symm.toAdjunction`. -/
@[pp_dot, simps! unit counit]
def toAdjunction (e : C ≌ D) : e.functor ⊣ e.inverse :=
  mkOfUnitCounit
    ⟨e.unit, e.counit, by
      ext
      dsimp
      simp only [id_comp]
      exact e.functor_unit_comp _, by
      ext
      dsimp
      simp only [id_comp]
      exact e.unit_inverse_comp _⟩
#align category_theory.equivalence.to_adjunction CategoryTheory.Equivalence.toAdjunction

#align category_theory.equivalence.as_equivalence_to_adjunction_unit CategoryTheory.Equivalence.toAdjunction_unitₓ
#align category_theory.equivalence.as_equivalence_to_adjunction_counit CategoryTheory.Equivalence.toAdjunction_counitₓ

end Equivalence

namespace Functor

/-- An equivalence `E` is left adjoint to its inverse. -/
def adjunction (E : C ⥤ D) [IsEquivalence E] : E ⊣ E.inv :=
  E.asEquivalence.toAdjunction
#align category_theory.functor.adjunction CategoryTheory.Functor.adjunction

@[simp]
theorem adjunction_unit (E : C ⥤ D) [IsEquivalence E] :
    E.adjunction.unit = E.asEquivalence.unit :=
  rfl

@[simp]
theorem adjunction_counit (E : C ⥤ D) [IsEquivalence E] :
    E.adjunction.counit = E.asEquivalence.counit :=
  rfl

/-- If `F` is an equivalence, it's a left adjoint. -/
instance (priority := 10) leftAdjointOfEquivalence {F : C ⥤ D} [IsEquivalence F] : IsLeftAdjoint F
    where
  right := _
  adj := Functor.adjunction F
#align category_theory.functor.left_adjoint_of_equivalence CategoryTheory.Functor.leftAdjointOfEquivalence

@[simp]
theorem rightAdjoint_of_isEquivalence {F : C ⥤ D} [IsEquivalence F] : rightAdjoint F = inv F :=
  rfl
#align category_theory.functor.right_adjoint_of_is_equivalence CategoryTheory.Functor.rightAdjoint_of_isEquivalence

/-- If `F` is an equivalence, it's a right adjoint. -/
instance (priority := 10) rightAdjointOfEquivalence {F : C ⥤ D} [IsEquivalence F] : IsRightAdjoint F
    where
  left := _
  adj := Functor.adjunction F.inv
#align category_theory.functor.right_adjoint_of_equivalence CategoryTheory.Functor.rightAdjointOfEquivalence

@[simp]
theorem leftAdjoint_of_isEquivalence {F : C ⥤ D} [IsEquivalence F] : leftAdjoint F = inv F :=
  rfl
#align category_theory.functor.left_adjoint_of_is_equivalence CategoryTheory.Functor.leftAdjoint_of_isEquivalence

end Functor

end CategoryTheory
