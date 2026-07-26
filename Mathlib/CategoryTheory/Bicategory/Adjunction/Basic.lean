/-
Copyright (c) 2023 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Fernando Chu
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Adjunctions in bicategories

For 1-morphisms `f : a ⟶ b` and `g : b ⟶ a` in a bicategory, an adjunction between `f` and `g`
consists of a pair of 2-morphisms `η : 𝟙 a ⟶ f ≫ g` and `ε : g ≫ f ⟶ 𝟙 b` satisfying the triangle
identities. The 2-morphism `η` is called the unit and `ε` is called the counit.

## Main definitions

* `Bicategory.Adjunction`: adjunctions between two 1-morphisms.
* `Bicategory.Equivalence`: adjoint equivalences between two objects.
* `Bicategory.Equivalence.mkOfAdjointifyCounit`: construct an adjoint equivalence from
  2-isomorphisms
  `η : 𝟙 a ≅ f ≫ g` and `ε : g ≫ f ≅ 𝟙 b`, by upgrading `ε` to a counit.
* `Pseudofunctor.mapAdjunction`: a pseudofunctor `F` carries an adjunction `f ⊣ g`
  between 1-morphisms to an adjunction `F.map f ⊣ F.map g`. An analogous definition is given
  for `StrictPseudofunctor`.

## TODO

* `Bicategory.Equivalence.mkOfAdjointifyUnit`: construct an adjoint equivalence from
  2-isomorphisms
  `η : 𝟙 a ≅ f ≫ g` and `ε : g ≫ f ≅ 𝟙 b`, by upgrading `η` to a unit.
-/

@[expose] public section

namespace CategoryTheory

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {a b c : B} {f : a ⟶ b} {g : b ⟶ a}

namespace Bicategory

/-- The 2-morphism defined by the following pasting diagram:
```
a －－－－－－ ▸ a
  ＼    η      ◥   ＼
  f ＼   g  ／       ＼ f
       ◢  ／     ε      ◢
        b －－－－－－ ▸ b
```
-/
abbrev leftZigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :=
  η ▷ f ⊗≫ f ◁ ε

/-- The 2-morphism defined by the following pasting diagram:
```
        a －－－－－－ ▸ a
       ◥  ＼     η      ◥
  g ／      ＼ f     ／ g
  ／    ε      ◢   ／
b －－－－－－ ▸ b
```
-/
abbrev rightZigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :=
  g ◁ η ⊗≫ ε ▷ g

theorem rightZigzag_idempotent_of_left_triangle
    (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) (h : leftZigzag η ε = (λ_ _).hom ≫ (ρ_ _).inv) :
    rightZigzag η ε ⊗≫ rightZigzag η ε = rightZigzag η ε := by
  dsimp only [rightZigzag]
  calc
    _ = g ◁ η ⊗≫ ((ε ▷ g ▷ 𝟙 a) ≫ (𝟙 b ≫ g) ◁ η) ⊗≫ ε ▷ g := by
      bicategory
    _ = 𝟙 _ ⊗≫ g ◁ (η ▷ 𝟙 a ≫ (f ≫ g) ◁ η) ⊗≫ (ε ▷ (g ≫ f) ≫ 𝟙 b ◁ ε) ▷ g ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = g ◁ η ⊗≫ g ◁ leftZigzag η ε ▷ g ⊗≫ ε ▷ g := by
      rw [← whisker_exchange, ← whisker_exchange, leftZigzag]; bicategory
    _ = g ◁ η ⊗≫ ε ▷ g := by
      rw [h]; bicategory

/-- Adjunction between two 1-morphisms. -/
@[ext]
structure Adjunction (f : a ⟶ b) (g : b ⟶ a) where
  /-- The unit of an adjunction. -/
  unit : 𝟙 a ⟶ f ≫ g
  /-- The counit of an adjunction. -/
  counit : g ≫ f ⟶ 𝟙 b
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  left_triangle : leftZigzag unit counit = (λ_ _).hom ≫ (ρ_ _).inv := by cat_disch
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  right_triangle : rightZigzag unit counit = (ρ_ _).hom ≫ (λ_ _).inv := by cat_disch

@[inherit_doc] scoped infixr:15 " ⊣ " => Bicategory.Adjunction

namespace Adjunction

attribute [simp] left_triangle right_triangle

/-- Adjunction between identities. -/
def id (a : B) : 𝟙 a ⊣ 𝟙 a where
  unit := (ρ_ _).inv
  counit := (ρ_ _).hom
  left_triangle := by bicategory_coherence
  right_triangle := by bicategory_coherence

instance : Inhabited (Adjunction (𝟙 a) (𝟙 a)) :=
  ⟨id a⟩

section Composition

variable {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}

/-- Auxiliary definition for `Adjunction.comp`. -/
@[simp]
def compUnit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : 𝟙 a ⟶ (f₁ ≫ f₂) ≫ g₂ ≫ g₁ :=
  adj₁.unit ⊗≫ f₁ ◁ adj₂.unit ▷ g₁ ⊗≫ 𝟙 _

/-- Auxiliary definition for `Adjunction.comp`. -/
@[simp]
def compCounit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : (g₂ ≫ g₁) ≫ f₁ ≫ f₂ ⟶ 𝟙 c :=
  𝟙 _ ⊗≫ g₂ ◁ adj₁.counit ▷ f₂ ⊗≫ adj₂.counit

theorem comp_left_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    leftZigzag (compUnit adj₁ adj₂) (compCounit adj₁ adj₂) = (λ_ _).hom ≫ (ρ_ _).inv := by
  calc
    _ = 𝟙 _ ⊗≫
          adj₁.unit ▷ (f₁ ≫ f₂) ⊗≫
            f₁ ◁ (adj₂.unit ▷ (g₁ ≫ f₁) ≫ (f₂ ≫ g₂) ◁ adj₁.counit) ▷ f₂ ⊗≫
              (f₁ ≫ f₂) ◁ adj₂.counit ⊗≫ 𝟙 _ := by
      dsimp only [compUnit, compCounit]; bicategory
    _ = 𝟙 _ ⊗≫
          (leftZigzag adj₁.unit adj₁.counit) ▷ f₂ ⊗≫
            f₁ ◁ (leftZigzag adj₂.unit adj₂.counit) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = _ := by
      simp_rw [left_triangle]; bicategory

theorem comp_right_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    rightZigzag (compUnit adj₁ adj₂) (compCounit adj₁ adj₂) = (ρ_ _).hom ≫ (λ_ _).inv := by
  calc
    _ = 𝟙 _ ⊗≫
          (g₂ ≫ g₁) ◁ adj₁.unit ⊗≫
            g₂ ◁ ((g₁ ≫ f₁) ◁ adj₂.unit ≫ adj₁.counit ▷ (f₂ ≫ g₂)) ▷ g₁ ⊗≫
              adj₂.counit ▷ (g₂ ≫ g₁) ⊗≫ 𝟙 _ := by
      dsimp only [compUnit, compCounit]; bicategory
    _ = 𝟙 _ ⊗≫
          g₂ ◁ (rightZigzag adj₁.unit adj₁.counit) ⊗≫
            (rightZigzag adj₂.unit adj₂.counit) ▷ g₁ ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]; bicategory
    _ = _ := by
      simp_rw [right_triangle]; bicategory

/-- Composition of adjunctions. -/
@[simps]
def comp (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : f₁ ≫ f₂ ⊣ g₂ ≫ g₁ where
  unit := compUnit adj₁ adj₂
  counit := compCounit adj₁ adj₂
  left_triangle := by apply comp_left_triangle_aux
  right_triangle := by apply comp_right_triangle_aux

end Composition

end Adjunction

noncomputable section

variable (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)

/-- The isomorphism version of `leftZigzag`. -/
abbrev leftZigzagIso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :=
  whiskerRightIso η f ≪⊗≫ whiskerLeftIso f ε

/-- The isomorphism version of `rightZigzag`. -/
abbrev rightZigzagIso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :=
  whiskerLeftIso g η ≪⊗≫ whiskerRightIso ε g

@[simp]
theorem leftZigzagIso_hom : (leftZigzagIso η ε).hom = leftZigzag η.hom ε.hom :=
  rfl

@[simp]
theorem rightZigzagIso_hom : (rightZigzagIso η ε).hom = rightZigzag η.hom ε.hom :=
  rfl

@[simp]
theorem leftZigzagIso_inv : (leftZigzagIso η ε).inv = rightZigzag ε.inv η.inv := by
  simp [bicategoricalComp, bicategoricalIsoComp]

@[simp]
theorem rightZigzagIso_inv : (rightZigzagIso η ε).inv = leftZigzag ε.inv η.inv := by
  simp [bicategoricalComp, bicategoricalIsoComp]

@[simp]
theorem leftZigzagIso_symm : (leftZigzagIso η ε).symm = rightZigzagIso ε.symm η.symm :=
  Iso.ext (leftZigzagIso_inv η ε)

@[simp]
theorem rightZigzagIso_symm : (rightZigzagIso η ε).symm = leftZigzagIso ε.symm η.symm :=
  Iso.ext (rightZigzagIso_inv η ε)

instance : IsIso (leftZigzag η.hom ε.hom) := inferInstanceAs <| IsIso (leftZigzagIso η ε).hom

instance : IsIso (rightZigzag η.hom ε.hom) := inferInstanceAs <| IsIso (rightZigzagIso η ε).hom

theorem right_triangle_of_left_triangle (h : leftZigzag η.hom ε.hom = (λ_ f).hom ≫ (ρ_ f).inv) :
    rightZigzag η.hom ε.hom = (ρ_ g).hom ≫ (λ_ g).inv := by
  rw [← cancel_epi (rightZigzag η.hom ε.hom ≫ (λ_ g).hom ≫ (ρ_ g).inv)]
  calc
    _ = rightZigzag η.hom ε.hom ⊗≫ rightZigzag η.hom ε.hom := by bicategory
    _ = rightZigzag η.hom ε.hom := rightZigzag_idempotent_of_left_triangle _ _ h
    _ = _ := by simp

/-- An auxiliary definition for `mkOfAdjointifyCounit`. -/
def adjointifyCounit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : g ≫ f ≅ 𝟙 b :=
  whiskerLeftIso g ((ρ_ f).symm ≪≫ rightZigzagIso ε.symm η.symm ≪≫ λ_ f) ≪≫ ε

set_option backward.defeqAttrib.useBackward true in
theorem adjointifyCounit_left_triangle (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    leftZigzagIso η (adjointifyCounit η ε) = λ_ f ≪≫ (ρ_ f).symm := by
  apply Iso.ext
  dsimp [adjointifyCounit, bicategoricalIsoComp]
  calc
    _ = 𝟙 _ ⊗≫ (η.hom ▷ (f ≫ 𝟙 b) ≫ (f ≫ g) ◁ f ◁ ε.inv) ⊗≫
          f ◁ g ◁ η.inv ▷ f ⊗≫ f ◁ ε.hom := by
      bicategory
    _ = 𝟙 _ ⊗≫ f ◁ ε.inv ⊗≫ (η.hom ▷ (f ≫ g) ≫ (f ≫ g) ◁ η.inv) ▷ f ⊗≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom (f ◁ ε.inv)]; bicategory
    _ = 𝟙 _ ⊗≫ f ◁ ε.inv ⊗≫ (η.inv ≫ η.hom) ▷ f ⊗≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom η.inv]; bicategory
    _ = 𝟙 _ ⊗≫ f ◁ (ε.inv ≫ ε.hom) := by
      rw [Iso.inv_hom_id]; bicategory
    _ = _ := by
      rw [Iso.inv_hom_id]; bicategory

/-- Adjoint equivalences between two objects. -/
structure Equivalence (a b : B) where
  /-- A 1-morphism in one direction. -/
  hom : a ⟶ b
  /-- A 1-morphism in the other direction. -/
  inv : b ⟶ a
  /-- The composition `hom ≫ inv` is isomorphic to the identity. -/
  unit : 𝟙 a ≅ hom ≫ inv
  /-- The composition `inv ≫ hom` is isomorphic to the identity. -/
  counit : inv ≫ hom ≅ 𝟙 b
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  left_triangle : leftZigzagIso unit counit = λ_ hom ≪≫ (ρ_ hom).symm := by cat_disch

@[inherit_doc] scoped infixr:10 " ≌ " => Bicategory.Equivalence

namespace Equivalence

/-- The identity 1-morphism is an equivalence. -/
def id (a : B) : a ≌ a := ⟨_, _, (ρ_ _).symm, ρ_ _, by ext; simp [bicategoricalIsoComp]⟩

instance : Inhabited (Equivalence a a) := ⟨id a⟩

theorem left_triangle_hom (e : a ≌ b) :
    leftZigzag e.unit.hom e.counit.hom = (λ_ e.hom).hom ≫ (ρ_ e.hom).inv :=
  congrArg Iso.hom e.left_triangle

theorem right_triangle (e : a ≌ b) :
    rightZigzagIso e.unit e.counit = ρ_ e.inv ≪≫ (λ_ e.inv).symm :=
  Iso.ext (right_triangle_of_left_triangle e.unit e.counit e.left_triangle_hom)

theorem right_triangle_hom (e : a ≌ b) :
    rightZigzag e.unit.hom e.counit.hom = (ρ_ e.inv).hom ≫ (λ_ e.inv).inv :=
  congrArg Iso.hom e.right_triangle

/-- Construct an adjoint equivalence from 2-isomorphisms by upgrading `ε` to a counit. -/
def mkOfAdjointifyCounit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : a ≌ b where
  hom := f
  inv := g
  unit := η
  counit := adjointifyCounit η ε
  left_triangle := adjointifyCounit_left_triangle η ε

end Equivalence

end

noncomputable
section

/-- A structure giving a chosen right adjoint of a 1-morphism `left`. -/
structure RightAdjoint (left : a ⟶ b) where
  /-- The right adjoint to `left`. -/
  right : b ⟶ a
  /-- The adjunction between `left` and `right`. -/
  adj : left ⊣ right

/-- The existence of a right adjoint of `f`. -/
class IsLeftAdjoint (left : a ⟶ b) : Prop where mk' ::
  nonempty : Nonempty (RightAdjoint left)

theorem IsLeftAdjoint.mk (adj : f ⊣ g) : IsLeftAdjoint f :=
  ⟨⟨g, adj⟩⟩

/-- Use the axiom of choice to extract a right adjoint from an `IsLeftAdjoint` instance. -/
def getRightAdjoint (f : a ⟶ b) [IsLeftAdjoint f] : RightAdjoint f :=
  Classical.choice IsLeftAdjoint.nonempty

/-- The right adjoint of a 1-morphism. -/
def rightAdjoint (f : a ⟶ b) [IsLeftAdjoint f] : b ⟶ a :=
  (getRightAdjoint f).right

/-- Evidence that `rightAdjoint f` is a right adjoint of `f`. -/
def Adjunction.ofIsLeftAdjoint (f : a ⟶ b) [IsLeftAdjoint f] : f ⊣ rightAdjoint f :=
  (getRightAdjoint f).adj

/-- A structure giving a chosen left adjoint of a 1-morphism `right`. -/
structure LeftAdjoint (right : b ⟶ a) where
  /-- The left adjoint to `right`. -/
  left : a ⟶ b
  /-- The adjunction between `left` and `right`. -/
  adj : left ⊣ right

/-- The existence of a left adjoint of `right`. -/
class IsRightAdjoint (right : b ⟶ a) : Prop where mk' ::
  nonempty : Nonempty (LeftAdjoint right)

theorem IsRightAdjoint.mk (adj : f ⊣ g) : IsRightAdjoint g :=
  ⟨⟨f, adj⟩⟩

/-- Use the axiom of choice to extract a left adjoint from an `IsRightAdjoint` instance. -/
def getLeftAdjoint (f : b ⟶ a) [IsRightAdjoint f] : LeftAdjoint f :=
  Classical.choice IsRightAdjoint.nonempty

/-- The left adjoint of a 1-morphism. -/
def leftAdjoint (f : b ⟶ a) [IsRightAdjoint f] : a ⟶ b :=
  (getLeftAdjoint f).left

/-- Evidence that `leftAdjoint f` is a left adjoint of `f`. -/
def Adjunction.ofIsRightAdjoint (f : b ⟶ a) [IsRightAdjoint f] : leftAdjoint f ⊣ f :=
  (getLeftAdjoint f).adj

end

end Bicategory

namespace Pseudofunctor

variable (F : Pseudofunctor B C) (adj : f ⊣ g)

lemma leftZigzag_map :
    leftZigzag ((F.mapId a).inv ≫ F.map₂ adj.unit ≫ (F.mapComp f g).hom)
      ((F.mapComp g f).inv ≫ F.map₂ adj.counit ≫ (F.mapId b).hom) =
    (F.mapId a).inv ▷ F.map f ⊗≫ (F.mapComp (𝟙 a) f).inv ≫
      F.map₂ (leftZigzag adj.unit adj.counit) ≫
        (F.mapComp f (𝟙 b)).hom ⊗≫ F.map f ◁ (F.mapId b).hom := by
  simp [leftZigzag, bicategoricalComp]

lemma rightZigzag_map :
    rightZigzag ((F.mapId a).inv ≫ F.map₂ adj.unit ≫ (F.mapComp f g).hom)
      ((F.mapComp g f).inv ≫ F.map₂ adj.counit ≫ (F.mapId b).hom) =
    F.map g ◁ (F.mapId a).inv ⊗≫ (F.mapComp g (𝟙 a)).inv ≫
      F.map₂ (rightZigzag adj.unit adj.counit) ≫
        (F.mapComp (𝟙 b) g).hom ⊗≫ (F.mapId b).hom ▷ F.map g := by
  simp [rightZigzag, bicategoricalComp, F.map₂_iso_inv]

/-- A pseudofunctor carries an adjunction `f ⊣ g` to an adjunction `F.map f ⊣ F.map g`. -/
@[simps]
def mapAdjunction : F.map f ⊣ F.map g where
  unit := (F.mapId a).inv ≫ F.map₂ adj.unit ≫ (F.mapComp f g).hom
  counit := (F.mapComp g f).inv ≫ F.map₂ adj.counit ≫ (F.mapId b).hom
  left_triangle := by simp [leftZigzag_map, bicategoricalComp, F.map₂_iso_inv]
  right_triangle := by simp [rightZigzag_map, bicategoricalComp, F.map₂_iso_inv]

end Pseudofunctor

namespace StrictPseudofunctor

variable (F : StrictPseudofunctor B C) (adj : f ⊣ g)

/-- A strict pseudofunctor carries an adjunction `f ⊣ g` to an adjunction
`F.map f ⊣ F.map g`. -/
@[simps!]
def mapAdjunction : F.map f ⊣ F.map g := F.toPseudofunctor.mapAdjunction adj

lemma mapAdjunction_unit' :
    (F.mapAdjunction adj).unit =
      eqToHom (F.map_id a).symm ≫ F.map₂ adj.unit ≫ eqToHom (F.map_comp f g) := by
  simp [F.mapId_eq_eqToIso, F.mapComp_eq_eqToIso]

lemma mapAdjunction_counit' :
    (F.mapAdjunction adj).counit =
      eqToHom (F.map_comp g f).symm ≫ F.map₂ adj.counit ≫ eqToHom (F.map_id b) := by
  simp [F.mapId_eq_eqToIso, F.mapComp_eq_eqToIso]

end StrictPseudofunctor

end CategoryTheory
