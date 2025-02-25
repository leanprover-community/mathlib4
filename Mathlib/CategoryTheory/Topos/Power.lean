/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen
-/
import Mathlib.CategoryTheory.Topos.Classifier
import Mathlib.CategoryTheory.ChosenFiniteProducts

/-!
# Power Objects

We Define power objects for a category `C` with a subobject classifier and chosen finite products.

## Main definitions

Let `C` be a category with a terminal object, a subobject classifier, and chosen finite products.

* For an object `B : C`, `CategoryTheory.PowerObject B` contains the data
  of a power object for `B`.

* `CategoryTheory.HasPowerObjects C` says that every object in `C` has a power object.

* If `C` has all power objects, then there is a functor `powFunctor C : Cᵒᵖ ⥤ C` which
  sends an object `B : C` to its power object `𝒫 B`, and sends a morphism `f : A ⟶ B` to the
  corresponding "inverse image" morphism `f⁻¹ : 𝒫 B ⟶ 𝒫 A`.

## Main results

* `powFunctor C` is self adjoint, in the sense that its adjoint is the corresponding
  functor `powFunctorOp C : C ⥤ Cᵒᵖ`. This adjunction is defined as `powSelfAdj C`.

## Notation

* `𝒫 B` is notation for `𝒫 B`, which is a choice of a power object for `B`.

* if `f : B ⊗ A ⟶ Ω C` is a morphism in a category with power objects, then
  `f^` denotes the corresponding morphism `A ⟶ 𝒫 B`, and `^f` denotes the corresponding
  morphism `B ⟶ 𝒫 A`.

* If `g : A ⟶ 𝒫 B` is a morphism in a category with power objects, then
  `g^` denotes the corresponding morphism `B ⊗ A ⟶ Ω C`.

* To "curry" maps in the other coordinate, put the caret `^` before the function argument
  instead of after.

* If `f : A ⟶ B` is a morphism in a category with power objects, then `f⁻¹` denotes
  the corresponding map `inverseImage f : 𝒫 B ⟶ 𝒫 A`.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MLM92]

## TODO

* Show that a cartesian closed category with a subobject classifier has power objects.

-/

universe u v

open CategoryTheory Category Limits HasClassifier MonoidalCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasTerminal C] [HasClassifier C]
variable [ChosenFiniteProducts C]

/-- An object `PB` and a map `in_B : B ⊗ PB ⟶ Ω C` form a power object for `B : C`
if, for any map `f : B ⊗ A ⟶ Ω C`, there is a unique map `f^ : A ⟶ PB` such that
the following diagram commutes:
```
        B ⊗ A ---f---> Ω C
          |             ^
          |            /
          |           /
       B ◁ f^       /
          |         /
          |       in_B
          |       /
          |      /
          |     /
          |    /
          v   /
        B ⊗ PB
```
-/
structure PowerObject (B : C) where
  /-- The power object associated to `B` -/
  pow : C
  /-- The membership predicate for `B` -/
  in_ : B ⊗ pow ⟶ Ω C
  /-- The transpose of a map `B ⊗ A ⟶ Ω C` -/
  transpose {A} (f : B ⊗ A ⟶ Ω C) : A ⟶ pow
  /-- the characterizing property of the transpose -/
  comm {A} (f : B ⊗ A ⟶ Ω C) : B ◁ (transpose f) ≫ in_ = f
  /-- `transpose f` is the only map which satisfies the commutativity condition -/
  uniq {A} {f : B ⊗ A ⟶ Ω C} {hat' : A ⟶ pow} (hat'_comm : B ◁ hat' ≫ in_ = f) :
      transpose f = hat'


variable (C)

/-- A category has power objects if each of its objects has a power object. -/
class HasPowerObjects : Prop where
  /-- Each `B : C` has a power object. -/
  has_power_object (B : C) : Nonempty (PowerObject B)

namespace HasPowerObjects

variable {C}
variable [HasPowerObjects C]

noncomputable section

/-- Notation for a choice of power object of an object. -/
abbrev pow (B : C) : C := (HasPowerObjects.has_power_object B).some.pow

@[inherit_doc]
prefix:100 "𝒫" => pow

/-- Notation for the predicate "b ∈ S" as a map `B ⊗ 𝒫 B ⟶ Ω`. -/
abbrev in_ (B : C) : B ⊗ 𝒫 B ⟶ Ω C := (HasPowerObjects.has_power_object B).some.in_

/-- The map Hom(B⊗A,Ω) → Hom(A,P(B)).
This is currying the left argument.
-/
def transpose {A B : C} (f : B ⊗ A ⟶ Ω C) : A ⟶ 𝒫 B :=
  (HasPowerObjects.has_power_object B).some.transpose f

/-- Notation for the `transpose` operator, which curries the left argument -/
scoped postfix:82 "^" => transpose

/-- The characterizing property of `transpose` -/
@[reassoc (attr := simp)]
lemma comm (B) {A : C} (f : B ⊗ A ⟶ Ω C) : B ◁ f^ ≫ in_ B = f :=
  (HasPowerObjects.has_power_object B).some.comm f

/-- `transpose` is the only map which satisfies the commutativity condition. -/
lemma unique (B) {A : C} {f : B ⊗ A ⟶ Ω C} {hat' : A ⟶ 𝒫 B} (hat'_comm : B ◁ hat' ≫ in_ B = f ) :
    f^ = hat' :=
  (HasPowerObjects.has_power_object B).some.uniq hat'_comm

/-- Un-currying on the left. The inverse of `HasPowerObjects.transpose. -/
def transposeInv {B A : C} (f : A ⟶ 𝒫 B) : B ⊗ A ⟶ Ω C :=
  B ◁ f ≫ in_ B

/-- Notation for the `transposeInv` operator, which un-curries on the left -/
scoped postfix:82 "^" => transposeInv

/-- Equivalence between Hom(B⊗A,Ω) and Hom(A,P(B)). -/
def transposeEquiv (A B : C) : (B ⊗ A ⟶ Ω C) ≃ (A ⟶ 𝒫 B) where
  toFun := transpose
  invFun := transposeInv
  left_inv := fun _ => comm _ _
  right_inv := fun _ => unique _ rfl

variable {A B : C}

/-- `transposeInv` is a left inverse of `transpose`. -/
@[simp]
lemma transpose_left_inv (f : B ⊗ A ⟶ Ω C) : (f^)^ = f :=
  (transposeEquiv _ _).left_inv _

/-- `transposeInv` is a right inverse of `transpose`. -/
@[simp]
lemma transpose_right_inv (f : A ⟶ 𝒫 B) : (f^)^ = f :=
  (transposeEquiv _ _).right_inv _

/-- The map Hom(B⊗A,Ω) → Hom(B,P(A)).
This is currying the right argument.
-/
def transposeSymm (f : B ⊗ A ⟶ Ω C) : B ⟶ 𝒫 A :=
  transpose ((β_ A B).hom ≫ f)

/-- Notation for the `transposeSymm` operator, which curries the right argument -/
scoped prefix:82 "^" => transposeSymm

/-- Un-currying on the right. -/
def transposeSymmInv (f : B ⟶ 𝒫 A) : B ⊗ A ⟶ Ω C :=
  (β_ A B).inv ≫ (transposeInv f)

/-- Notation for the `transposeSymmInv` operator, which un-curries on the right -/
scoped prefix:82 "^" => transposeSymmInv

variable (A B)

/-- Equivalence between Hom(B⨯A,Ω) and Hom(B,P(A)). -/
def transposeEquivSymm : (B ⊗ A ⟶ Ω C) ≃ (B ⟶ 𝒫 A) where
  toFun := transposeSymm
  invFun := transposeSymmInv
  left_inv := by
    intro
    simp [comm, transposeSymm, transposeSymmInv]
  right_inv := by
    intro
    apply unique
    simp [transposeSymmInv]
    rfl

variable {A B : C}

/-- `transposeSymmInv` is the left inverse of `transposeSymm`. -/
@[simp]
lemma transpose_symm_left_inv (f : B ⊗ A ⟶ Ω C) :
    ^(^f) = f :=
  (transposeEquivSymm _ _).left_inv _

/-- `transposeSymmInv` is the right inverse of `transposeSymm`. -/
@[simp]
lemma transpose_symm_right_inv {B A : C} (f : B ⟶ 𝒫 A) :
    (^(^f)) = f :=
  (transposeEquivSymm _ _).right_inv _

/-- Equivalence between Hom(A,P(B)) and Hom(B, P(A)).
This is just the composition of `transposeEquiv` and `transposeEquivSymm`.
-/
def transposeTransposeEquiv (A B : C) : (B ⟶ 𝒫 A) ≃ (A ⟶ 𝒫 B) :=
  Equiv.trans (transposeEquivSymm A B).symm (transposeEquiv A B)

/-- The power object functor's action on arrows.
Sends `h : A ⟶ B` to the P-transpose of the map `A ⊗ 𝒫 B ⟶ B ⊗ 𝒫 B ⟶ Ω`.
-/
def inverseImage {B A : C} (h : A ⟶ B) : 𝒫 B ⟶ 𝒫 A :=
  (h ▷ 𝒫 B ≫ in_ B)^

@[inherit_doc]
postfix:100 "⁻¹" => inverseImage

/-- The following diagram commutes:
```
    A ⊗ 𝒫 B ----------A ◁ h⁻¹-------> A ⊗ 𝒫 A
      |                                     |
      |                                     |
    h ▷ 𝒫 B                             in_ A
      |                                     |
      v                                     v
    B ⊗ 𝒫 B ----------in_ B------------> Ω C
```
-/
lemma inverseImage_comm {A B : C} (h : A ⟶ B) :
    A ◁ h⁻¹ ≫ in_ A = h ▷ 𝒫 B ≫ in_ B := by
  simp only [inverseImage, comm]

/-- `inverseImage` sends the identity on an object `B` to the identity on `𝒫 B`. -/
@[simp]
lemma inverseImage_id {B : C} : (𝟙 B)⁻¹ = 𝟙 (𝒫 B) := unique _ rfl

variable (C)

/-- The power object functor.
Sends objects `B` to their power objects `𝒫 B`.
Sends arrows `h : A ⟶ B` to the P-transpose of the map `A ⊗ 𝒫 B ⟶ B ⊗ 𝒫 B ⟶ Ω`,
which is the "inverse image" morphism `𝒫 B ⟶ 𝒫 A`.
-/
def powFunctor : Cᵒᵖ ⥤ C where
  obj := fun ⟨B⟩ ↦ 𝒫 B
  map := fun ⟨h⟩ ↦ h⁻¹
  map_id := fun _ => unique _ rfl
  map_comp := by
    intro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f⟩ ⟨g⟩
    apply unique
    dsimp [inverseImage]
    rw [comp_whiskerRight_assoc, ←inverseImage_comm, ←whisker_exchange_assoc]
    simp [inverseImage]

/-- The power object functor, treated as a functor `C ⥤ Cᵒᵖ`. -/
def powFunctorOp : C ⥤ Cᵒᵖ where
  obj := fun B ↦ ⟨𝒫 B⟩
  map := fun h ↦ ⟨inverseImage h⟩
  map_id := by
    intro
    apply congrArg Opposite.op
    apply (powFunctor C).map_id
  map_comp := by
    intros
    apply congrArg Opposite.op
    apply (powFunctor C).map_comp

/-- The adjunction between the power object functor and itself. -/
def powSelfAdj : powFunctorOp C ⊣ powFunctor C := by
  apply Adjunction.mkOfHomEquiv
  fapply Adjunction.CoreHomEquiv.mk
  · exact fun X ⟨Y⟩ => {
      toFun := fun ⟨f⟩ => (transposeTransposeEquiv X Y).toFun f
      invFun := fun g => ⟨(transposeTransposeEquiv X Y).invFun g⟩
      left_inv := fun ⟨f⟩ => by simp
      right_inv := fun g => by simp
    }
  · intro X' X ⟨Y⟩ f g
    simp
    congr
    show ^(f ≫ g)^ = ^g^ ≫ f⁻¹
    dsimp only [transposeSymm, transposeInv, inverseImage]
    apply unique
    rw [MonoidalCategory.whiskerLeft_comp, assoc, comm, ← assoc, whisker_exchange]
    simp
  · intro X ⟨Y⟩ ⟨Y'⟩ ⟨f⟩ ⟨g⟩
    dsimp only [transposeTransposeEquiv, transposeEquiv, transposeEquivSymm]
    simp
    show transpose ((β_ X Y').inv ≫ X ◁ (g ≫ f) ≫ in_ X) =
      transpose ((β_ X Y).inv ≫ X ◁ f ≫ in_ X) ≫ g⁻¹
    dsimp only [transposeInv, inverseImage]
    apply unique
    rw [MonoidalCategory.whiskerLeft_comp, assoc, comm, ← assoc _ _ (in_ Y), whisker_exchange]
    simp

end
end CategoryTheory.HasPowerObjects
