/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Yoneda

/-!
# Adjunctions between functors

`F ⊣ G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.

We provide various useful constructors:
* `mkOfHomEquiv`
* `mk'`: construct an adjunction from the data of a hom set equivalence, unit and counit natural
  transformations together with proofs of the equalities `homEquiv_unit` and `homEquiv_counit`
  relating them to each other.
* `leftAdjointOfEquiv` / `rightAdjointOfEquiv`
  construct a left/right adjoint of a given functor given the action on objects and
  the relevant equivalence of morphism spaces.
* `adjunctionOfEquivLeft` / `adjunctionOfEquivRight` witness that these constructions
  give adjunctions.

There are also typeclasses `IsLeftAdjoint` / `IsRightAdjoint`, which asserts the
existence of a adjoint functor. Given `[F.IsLeftAdjoint]`, a chosen right
adjoint can be obtained as `F.rightAdjoint`.

`Adjunction.comp` composes adjunctions.

`toEquivalence` upgrades an adjunction to an equivalence,
given witnesses that the unit and counit are pointwise isomorphisms.
Conversely `Equivalence.toAdjunction` recovers the underlying adjunction from an equivalence.

## Overview of the directory `CategoryTheory.Adjunction`

* Adjoint lifting theorems are in the directory `Lifting`.
* The file `AdjointFunctorTheorems` proves the adjoint functor theorems.
* The file `Comma` shows that for a functor `G : D ⥤ C` the data of an initial object in each
  `StructuredArrow` category on `G` is equivalent to a left adjoint to `G`, as well as the dual.
* The file `Evaluation` shows that products and coproducts are adjoint to evaluation of functors.
* The file `FullyFaithful` characterizes when adjoints are full or faithful in terms of the unit
  and counit.
* The file `Limits` proves that left adjoints preserve colimits and right adjoints preserve limits.
* The file `Mates` establishes the bijection between the 2-cells
  ```
          L₁                  R₁
        C --→ D             C ←-- D
      G ↓  ↗  ↓ H         G ↓  ↘  ↓ H
        E --→ F             E ←-- F
          L₂                  R₂
  ```
  where `L₁ ⊣ R₁` and `L₂ ⊣ R₂`. Specializing to a pair of adjoints `L₁ L₂ : C ⥤ D`,
  `R₁ R₂ : D ⥤ C`, it provides equivalences `(L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂)` and `(L₂ ≅ L₁) ≃ (R₁ ≅ R₂)`.
* The file `Opposites` contains constructions to relate adjunctions of functors to adjunctions of
  their opposites.
* The file `Reflective` defines reflective functors, i.e. fully faithful right adjoints. Note that
  many facts about reflective functors are proved in the earlier file `FullyFaithful`.
* The file `Restrict` defines the restriction of an adjunction along fully faithful functors.
* The file `Triple` proves that in an adjoint triple, the left adjoint is fully faithful if and
  only if the right adjoint is.
* The file `Unique` proves uniqueness of adjoints.
* The file `Whiskering` proves that functors `F : D ⥤ E` and `G : E ⥤ D` with an adjunction
  `F ⊣ G`, induce adjunctions between the functor categories `C ⥤ D` and `C ⥤ E`,
  and the functor categories `E ⥤ C` and `D ⥤ C`.

## Other files related to adjunctions

* The file `CategoryTheory.Monad.Adjunction` develops the basic relationship between adjunctions
  and (co)monads. There it is also shown that given an adjunction `L ⊣ R` and an isomorphism
  `L ⋙ R ≅ 𝟭 C`, the unit is an isomorphism, and similarly for the counit.
-/


namespace CategoryTheory

open Category Functor

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- `F ⊣ G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.

We use the unit-counit definition of an adjunction. There is a constructor `Adjunction.mk'`
which constructs an adjunction from the data of a hom set equivalence, a unit, and a counit,
together with proofs of the equalities `homEquiv_unit` and `homEquiv_counit` relating them to each
other.

There is also a constructor `Adjunction.mkOfHomEquiv` which constructs an adjunction from a natural
hom set equivalence.

To construct adjoints to a given functor, there are constructors `leftAdjointOfEquiv` and
`adjunctionOfEquivLeft` (as well as their duals). -/
@[stacks 0037]
structure Adjunction (F : C ⥤ D) (G : D ⥤ C) where
  /-- The unit of an adjunction -/
  unit : 𝟭 C ⟶ F.comp G
  /-- The counit of an adjunction -/
  counit : G.comp F ⟶ 𝟭 D
  /-- Equality of the composition of the unit and counit with the identity `F ⟶ FGF ⟶ F = 𝟙` -/
  left_triangle_components (X : C) :
      F.map (unit.app X) ≫ counit.app (F.obj X) = 𝟙 (F.obj X) := by cat_disch
  /-- Equality of the composition of the unit and counit with the identity `G ⟶ GFG ⟶ G = 𝟙` -/
  right_triangle_components (Y : D) :
      unit.app (G.obj Y) ≫ G.map (counit.app Y) = 𝟙 (G.obj Y) := by cat_disch

/-- The notation `F ⊣ G` stands for `Adjunction F G` representing that `F` is left adjoint to `G` -/
infixl:15 " ⊣ " => Adjunction

namespace Functor

/-- A class asserting the existence of a right adjoint. -/
class IsLeftAdjoint (left : C ⥤ D) : Prop where
  exists_rightAdjoint : ∃ (right : D ⥤ C), Nonempty (left ⊣ right)

/-- A class asserting the existence of a left adjoint. -/
class IsRightAdjoint (right : D ⥤ C) : Prop where
  exists_leftAdjoint : ∃ (left : C ⥤ D), Nonempty (left ⊣ right)

/-- A chosen left adjoint to a functor that is a right adjoint. -/
noncomputable def leftAdjoint (R : D ⥤ C) [IsRightAdjoint R] : C ⥤ D :=
  (IsRightAdjoint.exists_leftAdjoint (right := R)).choose

/-- A chosen right adjoint to a functor that is a left adjoint. -/
noncomputable def rightAdjoint (L : C ⥤ D) [IsLeftAdjoint L] : D ⥤ C :=
  (IsLeftAdjoint.exists_rightAdjoint (left := L)).choose

end Functor

/-- The adjunction associated to a functor known to be a left adjoint. -/
noncomputable def Adjunction.ofIsLeftAdjoint (left : C ⥤ D) [left.IsLeftAdjoint] :
    left ⊣ left.rightAdjoint :=
  IsLeftAdjoint.exists_rightAdjoint.choose_spec.some

/-- The adjunction associated to a functor known to be a right adjoint. -/
noncomputable def Adjunction.ofIsRightAdjoint (right : C ⥤ D) [right.IsRightAdjoint] :
    right.leftAdjoint ⊣ right :=
  IsRightAdjoint.exists_leftAdjoint.choose_spec.some

namespace Adjunction

attribute [reassoc (attr := simp)] left_triangle_components right_triangle_components

/-- The hom set equivalence associated to an adjunction. -/
@[simps -isSimp]
def homEquiv {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y) where
  toFun := fun f => adj.unit.app X ≫ G.map f
  invFun := fun g => F.map g ≫ adj.counit.app Y
  left_inv := fun f => by
    dsimp
    rw [F.map_comp, assoc, ← Functor.comp_map, adj.counit.naturality, ← assoc]
    simp
  right_inv := fun g => by
    simp only [Functor.comp_obj, Functor.map_comp]
    rw [← assoc, ← Functor.comp_map, ← adj.unit.naturality]
    simp

alias homEquiv_unit := homEquiv_apply
alias homEquiv_counit := homEquiv_symm_apply

end Adjunction

-- These lemmas are not global simp lemmas because certain adjunctions
-- are constructed using `Adjunction.mkOfHomEquiv`, and we certainly
-- do not want `dsimp` to apply `homEquiv_unit` or `homEquiv_counit`
-- in that case. However, when proving general API results about adjunctions,
-- it may be advisable to add a local simp attribute to these lemmas.
attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit

namespace Adjunction

@[ext]
lemma ext {F : C ⥤ D} {G : D ⥤ C} {adj adj' : F ⊣ G}
    (h : adj.unit = adj'.unit) : adj = adj' := by
  suffices h' : adj.counit = adj'.counit by cases adj; cases adj'; aesop
  ext X
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Adjunction.right_triangle_components, h, Adjunction.right_triangle_components]

section

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

lemma isLeftAdjoint (adj : F ⊣ G) : F.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩

lemma isRightAdjoint (adj : F ⊣ G) : G.IsRightAdjoint := ⟨_, ⟨adj⟩⟩

instance (R : D ⥤ C) [R.IsRightAdjoint] : R.leftAdjoint.IsLeftAdjoint :=
  (ofIsRightAdjoint R).isLeftAdjoint

instance (L : C ⥤ D) [L.IsLeftAdjoint] : L.rightAdjoint.IsRightAdjoint :=
  (ofIsLeftAdjoint L).isRightAdjoint

variable {X' X : C} {Y Y' : D}

theorem homEquiv_id (X : C) : adj.homEquiv X _ (𝟙 _) = adj.unit.app X := by simp

theorem homEquiv_symm_id (X : D) : (adj.homEquiv _ X).symm (𝟙 _) = adj.counit.app X := by simp

theorem homEquiv_naturality_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) :
    (adj.homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (adj.homEquiv X Y).symm g := by
  simp

theorem homEquiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (adj.homEquiv X Y) g := by
  rw [← Equiv.eq_symm_apply]
  simp only [Equiv.symm_apply_apply, homEquiv_naturality_left_symm]

theorem homEquiv_naturality_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y') (f ≫ g) = (adj.homEquiv X Y) f ≫ G.map g := by
  simp

theorem homEquiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y').symm (f ≫ G.map g) = (adj.homEquiv X Y).symm f ≫ g := by
  rw [Equiv.symm_apply_eq]
  simp only [homEquiv_naturality_right, Equiv.apply_symm_apply]

@[reassoc]
theorem homEquiv_naturality_left_square (f : X' ⟶ X) (g : F.obj X ⟶ Y')
    (h : F.obj X' ⟶ Y) (k : Y ⟶ Y') (w : F.map f ≫ g = h ≫ k) :
    f ≫ (adj.homEquiv X Y') g = (adj.homEquiv X' Y) h ≫ G.map k := by
  rw [← homEquiv_naturality_left, ← homEquiv_naturality_right, w]

@[reassoc]
theorem homEquiv_naturality_right_square (f : X' ⟶ X) (g : X ⟶ G.obj Y')
    (h : X' ⟶ G.obj Y) (k : Y ⟶ Y') (w : f ≫ g = h ≫ G.map k) :
    F.map f ≫ (adj.homEquiv X Y').symm g = (adj.homEquiv X' Y).symm h ≫ k := by
  rw [← homEquiv_naturality_left_symm, ← homEquiv_naturality_right_symm, w]

theorem homEquiv_naturality_left_square_iff (f : X' ⟶ X) (g : F.obj X ⟶ Y')
    (h : F.obj X' ⟶ Y) (k : Y ⟶ Y') :
    (f ≫ (adj.homEquiv X Y') g = (adj.homEquiv X' Y) h ≫ G.map k) ↔
      (F.map f ≫ g = h ≫ k) :=
  ⟨fun w ↦ by simpa only [Equiv.symm_apply_apply]
      using homEquiv_naturality_right_square adj _ _ _ _ w,
    homEquiv_naturality_left_square adj f g h k⟩

theorem homEquiv_naturality_right_square_iff (f : X' ⟶ X) (g : X ⟶ G.obj Y')
    (h : X' ⟶ G.obj Y) (k : Y ⟶ Y') :
    (F.map f ≫ (adj.homEquiv X Y').symm g = (adj.homEquiv X' Y).symm h ≫ k) ↔
      (f ≫ g = h ≫ G.map k) :=
  ⟨fun w ↦ by simpa only [Equiv.apply_symm_apply]
      using homEquiv_naturality_left_square adj _ _ _ _ w,
    homEquiv_naturality_right_square adj f g h k⟩

@[simp]
theorem left_triangle : whiskerRight adj.unit F ≫ whiskerLeft F adj.counit = 𝟙 _ := by
  ext; simp

@[simp]
theorem right_triangle : whiskerLeft G adj.unit ≫ whiskerRight adj.counit G = 𝟙 _ := by
  ext; simp

@[reassoc (attr := simp)]
theorem counit_naturality {X Y : D} (f : X ⟶ Y) :
    F.map (G.map f) ≫ adj.counit.app Y = adj.counit.app X ≫ f :=
  adj.counit.naturality f

@[reassoc (attr := simp)]
theorem unit_naturality {X Y : C} (f : X ⟶ Y) :
    adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app Y :=
  (adj.unit.naturality f).symm

lemma unit_comp_map_eq_iff {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    adj.unit.app A ≫ G.map f = g ↔ f = F.map g ≫ adj.counit.app B :=
  ⟨fun h => by simp [← h], fun h => by simp [h]⟩

lemma eq_unit_comp_map_iff {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    g = adj.unit.app A ≫ G.map f ↔ F.map g ≫ adj.counit.app B = f :=
  ⟨fun h => by simp [h], fun h => by simp [← h]⟩

theorem homEquiv_apply_eq {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    adj.homEquiv A B f = g ↔ f = (adj.homEquiv A B).symm g :=
  unit_comp_map_eq_iff adj f g

theorem eq_homEquiv_apply {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    g = adj.homEquiv A B f ↔ (adj.homEquiv A B).symm g = f :=
  eq_unit_comp_map_iff adj f g

/-- If `adj : F ⊣ G`, and `X : C`, then `F.obj X` corepresents `Y ↦ (X ⟶ G.obj Y)`. -/
@[simps]
def corepresentableBy (X : C) :
    (G ⋙ coyoneda.obj (Opposite.op X)).CorepresentableBy (F.obj X) where
  homEquiv := adj.homEquiv _ _
  homEquiv_comp := by simp

/-- If `adj : F ⊣ G`, and `Y : D`, then `G.obj Y` represents `X ↦ (F.obj X ⟶ Y)`. -/
@[simps]
def representableBy (Y : D) :
    (F.op ⋙ yoneda.obj Y).RepresentableBy (G.obj Y) where
  homEquiv := (adj.homEquiv _ _).symm
  homEquiv_comp := by simp

end

end Adjunction

namespace Adjunction

/--
This is an auxiliary data structure useful for constructing adjunctions.
See `Adjunction.mk'`. This structure won't typically be used anywhere else.
-/
structure CoreHomEquivUnitCounit (F : C ⥤ D) (G : D ⥤ C) where
  /-- The equivalence between `Hom (F X) Y` and `Hom X (G Y)` coming from an adjunction -/
  homEquiv : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  /-- The unit of an adjunction -/
  unit : 𝟭 C ⟶ F ⋙ G
  /-- The counit of an adjunction -/
  counit : G ⋙ F ⟶ 𝟭 D
  /-- The relationship between the unit and hom set equivalence of an adjunction -/
  homEquiv_unit : ∀ {X Y f}, (homEquiv X Y) f = unit.app X ≫ G.map f := by cat_disch
  /-- The relationship between the counit and hom set equivalence of an adjunction -/
  homEquiv_counit : ∀ {X Y g}, (homEquiv X Y).symm g = F.map g ≫ counit.app Y := by cat_disch

/-- This is an auxiliary data structure useful for constructing adjunctions.
See `Adjunction.mkOfHomEquiv`.
This structure won't typically be used anywhere else.
-/
structure CoreHomEquiv (F : C ⥤ D) (G : D ⥤ C) where
  /-- The equivalence between `Hom (F X) Y` and `Hom X (G Y)` -/
  homEquiv : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  /-- The property that describes how `homEquiv.symm` transforms compositions `X' ⟶ X ⟶ G Y` -/
  homEquiv_naturality_left_symm :
    ∀ {X' X Y} (f : X' ⟶ X) (g : X ⟶ G.obj Y),
      (homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (homEquiv X Y).symm g := by
    cat_disch
  /-- The property that describes how `homEquiv` transforms compositions `F X ⟶ Y ⟶ Y'` -/
  homEquiv_naturality_right :
    ∀ {X Y Y'} (f : F.obj X ⟶ Y) (g : Y ⟶ Y'),
      (homEquiv X Y') (f ≫ g) = (homEquiv X Y) f ≫ G.map g := by
    cat_disch

namespace CoreHomEquiv

attribute [simp] homEquiv_naturality_left_symm homEquiv_naturality_right

variable {F : C ⥤ D} {G : D ⥤ C} (adj : CoreHomEquiv F G) {X' X : C} {Y Y' : D}

theorem homEquiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (adj.homEquiv X Y) g := by
  rw [← Equiv.eq_symm_apply]; simp

theorem homEquiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y').symm (f ≫ G.map g) = (adj.homEquiv X Y).symm f ≫ g := by
  rw [Equiv.symm_apply_eq]; simp

end CoreHomEquiv

/-- This is an auxiliary data structure useful for constructing adjunctions.
See `Adjunction.mkOfUnitCounit`.
This structure won't typically be used anywhere else.
-/
structure CoreUnitCounit (F : C ⥤ D) (G : D ⥤ C) where
  /-- The unit of an adjunction between `F` and `G` -/
  unit : 𝟭 C ⟶ F.comp G
  /-- The counit of an adjunction between `F` and `G`s -/
  counit : G.comp F ⟶ 𝟭 D
  /-- Equality of the composition of the unit, associator, and counit with the identity
  `F ⟶ (F G) F ⟶ F (G F) ⟶ F = NatTrans.id F` -/
  left_triangle :
    whiskerRight unit F ≫ (associator F G F).hom ≫ whiskerLeft F counit =
      NatTrans.id (𝟭 C ⋙ F) := by
    cat_disch
  /-- Equality of the composition of the unit, associator, and counit with the identity
  `G ⟶ G (F G) ⟶ (F G) F ⟶ G = NatTrans.id G` -/
  right_triangle :
    whiskerLeft G unit ≫ (associator G F G).inv ≫ whiskerRight counit G =
      NatTrans.id (G ⋙ 𝟭 C) := by
    cat_disch

namespace CoreUnitCounit

attribute [simp] left_triangle right_triangle

end CoreUnitCounit

variable {F : C ⥤ D} {G : D ⥤ C}

attribute [local simp] CoreHomEquivUnitCounit.homEquiv_unit CoreHomEquivUnitCounit.homEquiv_counit

/--
Construct an adjunction from the data of a `CoreHomEquivUnitCounit`, i.e. a hom set
equivalence, unit and counit natural transformations together with proofs of the equalities
`homEquiv_unit` and `homEquiv_counit` relating them to each other.
-/
@[simps]
def mk' (adj : CoreHomEquivUnitCounit F G) : F ⊣ G where
  unit := adj.unit
  counit := adj.counit
  left_triangle_components X := by
    rw [← adj.homEquiv_counit, (adj.homEquiv _ _).symm_apply_eq, adj.homEquiv_unit]
    simp
  right_triangle_components Y := by
    rw [← adj.homEquiv_unit, ← (adj.homEquiv _ _).eq_symm_apply, adj.homEquiv_counit]
    simp

lemma mk'_homEquiv (adj : CoreHomEquivUnitCounit F G) : (mk' adj).homEquiv = adj.homEquiv := by
  ext
  rw [homEquiv_unit, adj.homEquiv_unit, mk'_unit]

/-- Construct an adjunction between `F` and `G` out of a natural bijection between each
`F.obj X ⟶ Y` and `X ⟶ G.obj Y`. -/
@[simps!]
def mkOfHomEquiv (adj : CoreHomEquiv F G) : F ⊣ G :=
  mk' {
    unit :=
      { app := fun X => (adj.homEquiv X (F.obj X)) (𝟙 (F.obj X))
        naturality := by
          intros
          simp [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right] }
    counit :=
      { app := fun Y => (adj.homEquiv _ _).invFun (𝟙 (G.obj Y))
        naturality := by
          intros
          simp [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm] }
    homEquiv := adj.homEquiv
    homEquiv_unit := fun {X Y f} => by simp [← adj.homEquiv_naturality_right]
    homEquiv_counit := fun {X Y f} => by simp [← adj.homEquiv_naturality_left_symm] }

@[simp]
lemma mkOfHomEquiv_homEquiv (adj : CoreHomEquiv F G) :
    (mkOfHomEquiv adj).homEquiv = adj.homEquiv := by
  ext X Y g
  simp [mkOfHomEquiv, ← adj.homEquiv_naturality_right (𝟙 _) g]

/-- Construct an adjunction between functors `F` and `G` given a unit and counit for the adjunction
satisfying the triangle identities. -/
@[simps!]
def mkOfUnitCounit (adj : CoreUnitCounit F G) : F ⊣ G where
  unit := adj.unit
  counit := adj.counit
  left_triangle_components X := by
    have := adj.left_triangle
    rw [NatTrans.ext_iff, funext_iff] at this
    simpa [-CoreUnitCounit.left_triangle] using this X
  right_triangle_components Y := by
    have := adj.right_triangle
    rw [NatTrans.ext_iff, funext_iff] at this
    simpa [-CoreUnitCounit.right_triangle] using this Y

/-- The adjunction between the identity functor on a category and itself. -/
def id : 𝟭 C ⊣ 𝟭 C where
  unit := 𝟙 _
  counit := 𝟙 _

-- Satisfy the inhabited linter.
instance : Inhabited (Adjunction (𝟭 C) (𝟭 C)) :=
  ⟨id⟩

/-- If F and G are naturally isomorphic functors, establish an equivalence of hom-sets. -/
@[simps]
def equivHomsetLeftOfNatIso {F F' : C ⥤ D} (iso : F ≅ F') {X : C} {Y : D} :
    (F.obj X ⟶ Y) ≃ (F'.obj X ⟶ Y) where
  toFun f := iso.inv.app _ ≫ f
  invFun g := iso.hom.app _ ≫ g
  left_inv f := by simp
  right_inv g := by simp

/-- If G and H are naturally isomorphic functors, establish an equivalence of hom-sets. -/
@[simps]
def equivHomsetRightOfNatIso {G G' : D ⥤ C} (iso : G ≅ G') {X : C} {Y : D} :
    (X ⟶ G.obj Y) ≃ (X ⟶ G'.obj Y) where
  toFun f := f ≫ iso.hom.app _
  invFun g := g ≫ iso.inv.app _
  left_inv f := by simp
  right_inv g := by simp

/-- Transport an adjunction along a natural isomorphism on the left. -/
def ofNatIsoLeft {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) : G ⊣ H :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => (equivHomsetLeftOfNatIso iso.symm).trans (adj.homEquiv X Y) }

/-- Transport an adjunction along a natural isomorphism on the right. -/
def ofNatIsoRight {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) : F ⊣ H :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => (adj.homEquiv X Y).trans (equivHomsetRightOfNatIso iso) }

/-- The isomorphism which an adjunction `F ⊣ G` induces on `G ⋙ yoneda`. This states that
`Adjunction.homEquiv` is natural in both arguments. -/
@[simps!]
def compYonedaIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    G ⋙ yoneda ≅ yoneda ⋙ (whiskeringLeft _ _ _).obj F.op :=
  NatIso.ofComponents fun X => NatIso.ofComponents fun Y => (adj.homEquiv Y.unop X).toIso.symm

/-- The isomorphism which an adjunction `F ⊣ G` induces on `F.op ⋙ coyoneda`. This states that
`Adjunction.homEquiv` is natural in both arguments. -/
@[simps!]
def compCoyonedaIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    F.op ⋙ coyoneda ≅ coyoneda ⋙ (whiskeringLeft _ _ _).obj G :=
  NatIso.ofComponents fun X => NatIso.ofComponents fun Y => (adj.homEquiv X.unop Y).toIso

/-- The isomorpism which an adjunction `F ⊣ G` induces on `F.op ⋙ uliftCoyoneda`.
This states that `Adjunction.homEquiv` is natural in both arguments. -/
@[simps!]
def compUliftCoyonedaIso (adj : F ⊣ G) :
    F.op ⋙ uliftCoyoneda.{max w v₁} ≅
      uliftCoyoneda.{max w v₂} ⋙ (whiskeringLeft _ _ _).obj G :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun Y ↦ (Equiv.ulift.trans
      ((adj.homEquiv X.unop Y).trans Equiv.ulift.symm)).toIso))

section

variable {E : Type u₃} [ℰ : Category.{v₃} E] {H : D ⥤ E} {I : E ⥤ D}
  (adj₁ : F ⊣ G) (adj₂ : H ⊣ I)

/-- Composition of adjunctions. -/
@[simps! -isSimp unit counit, stacks 0DV0]
def comp : F ⋙ H ⊣ I ⋙ G :=
  mk' {
    homEquiv := fun _ _ ↦ Equiv.trans (adj₂.homEquiv _ _) (adj₁.homEquiv _ _)
    unit := adj₁.unit ≫ whiskerRight (F.rightUnitor.inv ≫ whiskerLeft F adj₂.unit ≫
      (associator _ _ _ ).inv) G ≫ (associator _ _ _).hom
    counit := (associator _ _ _ ).inv ≫ whiskerRight ((associator _ _ _ ).hom ≫
      whiskerLeft _ adj₁.counit ≫ I.rightUnitor.hom) _ ≫ adj₂.counit }

@[simp, reassoc]
lemma comp_unit_app (X : C) :
    (adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X)) := by
  simp [Adjunction.comp]

@[simp, reassoc]
lemma comp_counit_app (X : E) :
    (adj₁.comp adj₂).counit.app X = H.map (adj₁.counit.app (I.obj X)) ≫ adj₂.counit.app X := by
  simp [Adjunction.comp]

lemma comp_homEquiv : (adj₁.comp adj₂).homEquiv =
    fun _ _ ↦ Equiv.trans (adj₂.homEquiv _ _) (adj₁.homEquiv _ _) :=
  mk'_homEquiv _

end

section ConstructLeft

-- Construction of a left adjoint. In order to construct a left
-- adjoint to a functor G : D → C, it suffices to give the object part
-- of a functor F : C → D together with isomorphisms Hom(FX, Y) ≃
-- Hom(X, GY) natural in Y. The action of F on morphisms can be
-- constructed from this data.
variable {F_obj : C → D}
variable (e : ∀ X Y, (F_obj X ⟶ Y) ≃ (X ⟶ G.obj Y))

/-- Construct a left adjoint functor to `G`, given the functor's value on objects `F_obj` and
a bijection `e` between `F_obj X ⟶ Y` and `X ⟶ G.obj Y` satisfying a naturality law
`he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g`.
Dual to `rightAdjointOfEquiv`. -/
@[simps!]
def leftAdjointOfEquiv (he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g) : C ⥤ D where
  obj := F_obj
  map {X} {X'} f := (e X (F_obj X')).symm (f ≫ e X' (F_obj X') (𝟙 _))
  map_comp := fun f f' => by
    rw [Equiv.symm_apply_eq, he, Equiv.apply_symm_apply]
    conv =>
      rhs
      rw [assoc, ← he, id_comp, Equiv.apply_symm_apply]
    simp

variable (he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g)

/-- Show that the functor given by `leftAdjointOfEquiv` is indeed left adjoint to `G`. Dual
to `adjunctionOfRightEquiv`. -/
@[simps!]
def adjunctionOfEquivLeft : leftAdjointOfEquiv e he ⊣ G :=
  mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := fun {X'} {X} {Y} f g => by
        have {X : C} {Y Y' : D} (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
            (e X Y').symm (f ≫ G.map g) = (e X Y).symm f ≫ g := by
          rw [Equiv.symm_apply_eq, he]; simp
        simp [← this, ← he] }

end ConstructLeft

section ConstructRight

-- Construction of a right adjoint, analogous to the above.
variable {G_obj : D → C}
variable (e : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G_obj Y))

private theorem he'' (he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g)
    {X' X Y} (f g) : F.map f ≫ (e X Y).symm g = (e X' Y).symm (f ≫ g) := by
  rw [Equiv.eq_symm_apply, he]; simp

/-- Construct a right adjoint functor to `F`, given the functor's value on objects `G_obj` and
a bijection `e` between `F.obj X ⟶ Y` and `X ⟶ G_obj Y` satisfying a naturality law
`he : ∀ X Y Y' g h, e X' Y (F.map f ≫ g) = f ≫ e X Y g`.
Dual to `leftAdjointOfEquiv`. -/
@[simps!]
def rightAdjointOfEquiv (he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g) : D ⥤ C where
  obj := G_obj
  map {Y} {Y'} g := (e (G_obj Y) Y') ((e (G_obj Y) Y).symm (𝟙 _) ≫ g)
  map_comp := fun {Y} {Y'} {Y''} g g' => by
    rw [← Equiv.eq_symm_apply, ← he'' e he, Equiv.symm_apply_apply]
    conv =>
      rhs
      rw [← assoc, he'' e he, comp_id, Equiv.symm_apply_apply]
    simp

/-- Show that the functor given by `rightAdjointOfEquiv` is indeed right adjoint to `F`. Dual
to `adjunctionOfEquivRight`. -/
@[simps!]
def adjunctionOfEquivRight (he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g) :
    F ⊣ (rightAdjointOfEquiv e he) :=
  mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := by
        intro X X' Y f g; rw [Equiv.symm_apply_eq]; simp [he]
      homEquiv_naturality_right := by
        intro X Y Y' g h
        simp [← he, reassoc_of% (he'' e)] }

end ConstructRight

/--
If the unit and counit of a given adjunction are (pointwise) isomorphisms, then we can upgrade the
adjunction to an equivalence.
-/
@[simps!]
noncomputable def toEquivalence (adj : F ⊣ G) [∀ X, IsIso (adj.unit.app X)]
    [∀ Y, IsIso (adj.counit.app Y)] : C ≌ D where
  functor := F
  inverse := G
  unitIso := NatIso.ofComponents fun X => asIso (adj.unit.app X)
  counitIso := NatIso.ofComponents fun Y => asIso (adj.counit.app Y)

end Adjunction

open Adjunction

/--
If the unit and counit for the adjunction corresponding to a right adjoint functor are (pointwise)
isomorphisms, then the functor is an equivalence of categories.
-/
lemma Functor.isEquivalence_of_isRightAdjoint (G : C ⥤ D) [IsRightAdjoint G]
    [∀ X, IsIso ((Adjunction.ofIsRightAdjoint G).unit.app X)]
    [∀ Y, IsIso ((Adjunction.ofIsRightAdjoint G).counit.app Y)] : G.IsEquivalence :=
  (Adjunction.ofIsRightAdjoint G).toEquivalence.isEquivalence_inverse

namespace Equivalence

variable (e : C ≌ D)

/-- The adjunction given by an equivalence of categories. (To obtain the opposite adjunction,
simply use `e.symm.toAdjunction`. -/
@[simps]
def toAdjunction : e.functor ⊣ e.inverse where
  unit := e.unit
  counit := e.counit

lemma isLeftAdjoint_functor : e.functor.IsLeftAdjoint where
  exists_rightAdjoint := ⟨_, ⟨e.toAdjunction⟩⟩

lemma isRightAdjoint_inverse : e.inverse.IsRightAdjoint where
  exists_leftAdjoint := ⟨_, ⟨e.toAdjunction⟩⟩

lemma isLeftAdjoint_inverse : e.inverse.IsLeftAdjoint :=
  e.symm.isLeftAdjoint_functor

lemma isRightAdjoint_functor : e.functor.IsRightAdjoint :=
  e.symm.isRightAdjoint_inverse

lemma refl_toAdjunction : (refl (C := C)).toAdjunction = Adjunction.id := rfl

lemma trans_toAdjunction {E : Type*} [Category E] (e' : D ≌ E) :
    (e.trans e').toAdjunction = e.toAdjunction.comp e'.toAdjunction := rfl

end Equivalence

namespace Functor

/-- If `F` and `G` are left adjoints then `F ⋙ G` is a left adjoint too. -/
instance isLeftAdjoint_comp {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [F.IsLeftAdjoint] [G.IsLeftAdjoint] : (F ⋙ G).IsLeftAdjoint where
  exists_rightAdjoint :=
    ⟨_, ⟨(Adjunction.ofIsLeftAdjoint F).comp (Adjunction.ofIsLeftAdjoint G)⟩⟩

/-- If `F` and `G` are right adjoints then `F ⋙ G` is a right adjoint too. -/
instance isRightAdjoint_comp {E : Type u₃} [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E}
    [IsRightAdjoint F] [IsRightAdjoint G] : IsRightAdjoint (F ⋙ G) where
  exists_leftAdjoint :=
    ⟨_, ⟨(Adjunction.ofIsRightAdjoint G).comp (Adjunction.ofIsRightAdjoint F)⟩⟩

/-- Transport being a right adjoint along a natural isomorphism. -/
lemma isRightAdjoint_of_iso {F G : C ⥤ D} (h : F ≅ G) [F.IsRightAdjoint] :
    IsRightAdjoint G where
  exists_leftAdjoint := ⟨_, ⟨(Adjunction.ofIsRightAdjoint F).ofNatIsoRight h⟩⟩

/-- Transport being a left adjoint along a natural isomorphism. -/
lemma isLeftAdjoint_of_iso {F G : C ⥤ D} (h : F ≅ G) [IsLeftAdjoint F] :
    IsLeftAdjoint G where
  exists_rightAdjoint := ⟨_, ⟨(Adjunction.ofIsLeftAdjoint F).ofNatIsoLeft h⟩⟩


/-- An equivalence `E` is left adjoint to its inverse. -/
noncomputable def adjunction (E : C ⥤ D) [IsEquivalence E] : E ⊣ E.inv :=
  E.asEquivalence.toAdjunction

/-- If `F` is an equivalence, it's a left adjoint. -/
instance (priority := 10) isLeftAdjoint_of_isEquivalence {F : C ⥤ D} [F.IsEquivalence] :
    IsLeftAdjoint F :=
  F.asEquivalence.isLeftAdjoint_functor

/-- If `F` is an equivalence, it's a right adjoint. -/
instance (priority := 10) isRightAdjoint_of_isEquivalence {F : C ⥤ D} [F.IsEquivalence] :
    IsRightAdjoint F :=
  F.asEquivalence.isRightAdjoint_functor

end Functor

end CategoryTheory
