/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Preadditive.FreydCategory.Homotopy
public import Mathlib.CategoryTheory.Quotient.Preadditive

/-!
# The right Freyd category

Let `V` be a preadditive category. The right Freyd category of `V` is the quotient of
`Arrow V` by the right homotopy relation.


## References
* [Posur, S., *A constructive approach to Freyd categories*][posur2021Freyd]

-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits Arrow

variable (V : Type*) [Category* V] [Preadditive V]

namespace CategoryTheory.Preadditive

/-- If `V` is a preadditive category, then `RightFreyd V` is the category of arrows in `V`,
with morphisms identified when they are right homotopic. -/
def RightFreyd :=
  CategoryTheory.Quotient (rightHomotopic V)

instance : Category (RightFreyd V) :=
  inferInstanceAs <| Category (CategoryTheory.Quotient (rightHomotopic V))

/-- The category `RightFreyd V` is preadditive. -/
instance : Preadditive (RightFreyd V) :=
  Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨h'⟩
    exact ⟨RightHomotopy.add h h'⟩)

namespace RightFreyd

/-- The quotient functor from `Arrow V` to `RightFreyd V`. -/
def quotient : Arrow V ⥤ RightFreyd V :=
  CategoryTheory.Quotient.functor _

instance : (quotient V).Full := Quotient.full_functor _

instance : (quotient V).EssSurj := Quotient.essSurj_functor _

instance : (quotient V).Additive where

variable {V}

/-- If two morphisms in `Arrow V` are right homotopic, then they become equal in the right
Freyd category. -/
theorem eq_of_rightHomotopy {u v : Arrow V} (f g : u ⟶ v) (h : RightHomotopy f g) :
    (quotient V).map f = (quotient V).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩

/-- If two morphisms of `Arrow V` become equal in the right Freyd category,
then they are right homotopic. -/
def homotopyOfEq {u v : Arrow V} (f g : u ⟶ v)
    (w : (quotient V).map f = (quotient V).map g) : RightHomotopy f g :=
  ((Quotient.functor_map_eq_iff _ _ _).mp w).some

variable {u v : Arrow V} (f g : u ⟶ v)

/-- Two morphisms in `Arrow V` have the same image in `RightFreyd V` if and only if there
exists a right homotopy between them. -/
lemma quotient_map_eq_iff :
    (quotient V).map f = (quotient V).map g ↔ Nonempty (RightHomotopy f g) :=
  ⟨fun h ↦ ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ ↦ by simpa using eq_of_rightHomotopy _ _ h⟩

/-- A morphism `f` in `Arrow V` is sent to `0` in `RightFreyd V` if and only if there
exists a right homotopy between `f` and `0`. -/
lemma quotient_map_eq_zero_iff : (quotient V).map f = 0 ↔ Nonempty (RightHomotopy f 0) :=
  ⟨fun h ↦ ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ ↦ by simpa using eq_of_rightHomotopy _ _ h⟩

/-- If `f` is a morphism of `Arrow V` such that `f.right` is an isomorphism, then the image of `f`
in the right Freyd category is an epimorphism. -/
lemma epi_of_isIso_right [IsIso f.right] : Epi ((quotient V).map f) where
  left_cancellation g₁ g₂ eq := by
    obtain ⟨g₁, rfl⟩ := (quotient V).map_surjective g₁
    obtain ⟨g₂, rfl⟩ := (quotient V).map_surjective g₂
    set h : RightHomotopy (f ≫ g₁) (f ≫ g₂) := homotopyOfEq _ _ eq
    exact eq_of_rightHomotopy _ _ ⟨inv f.right ≫ h.hom, by simp [dsimp% h.comm]⟩

section Functor

variable [HasZeroObject V]

variable (V)

open ZeroObject in
set_option backward.defeqAttrib.useBackward true in
/-- If `V` has a zero object, this is the functor from `V` to `Arrow V`
that sends an object `X` to the arrow `0 ⟶ X`. -/
def rightFunctor : V ⥤ Arrow V where
  obj X := Arrow.mk (0 : 0 ⟶ X)
  map f := Arrow.homMk 0 f

instance : (rightFunctor V).Additive where
  map_add {_ _ _ _} := by
    ext
    · exact HasZeroObject.from_zero_ext _ _
    · rfl

/-- The fully faithful additive functor from  `V` to `RightFreyd V` sending an object `X` of `V`
to the class of the arrow `0 ⟶ X`. -/
def functor : V ⥤ RightFreyd V := rightFunctor V ⋙ quotient V

instance : (functor V).Additive := by dsimp [functor]; infer_instance

instance : (functor V).Full where
  map_surjective a := by
    obtain ⟨u, rfl⟩ := (quotient V).map_surjective a
    use u.right
    apply congrArg (quotient V).map
    ext
    · exact HasZeroObject.from_zero_ext _ _
    · rfl

instance : (functor V).Faithful where
  map_injective {_ _} _ _ eq := by
    refine eq_of_sub_eq_zero (((quotient_map_eq_iff _ _).mp eq).some.comm.trans ?_)
    convert comp_zero
    · exact HasZeroObject.from_zero_ext _ _
    · rfl

end Functor

end RightFreyd

end CategoryTheory.Preadditive
