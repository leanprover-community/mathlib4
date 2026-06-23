/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Balanced
public import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Strong epimorphisms

In this file, we define strong epimorphisms. A strong epimorphism is an epimorphism `f`
which has the (unique) left lifting property with respect to monomorphisms. Similarly,
a strong monomorphism is a monomorphism which has the (unique) right lifting property
with respect to epimorphisms.

## Main results

Besides the definition, we show that
* the composition of two strong epimorphisms is a strong epimorphism,
* if `f ≫ g` is a strong epimorphism, then so is `g`,
* if `f` is both a strong epimorphism and a monomorphism, then it is an isomorphism

We also define classes `StrongMonoCategory` and `StrongEpiCategory` for categories in which
every monomorphism or epimorphism is strong, and deduce that these categories are balanced.

## TODO

Show that the dual of a strong epimorphism is a strong monomorphism, and vice versa.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/

public section


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {P Q : C}

to_dual_name_hint Epi Mono, LLP RLP

/-- A strong epimorphism `f` is an epimorphism which has the left lifting property
with respect to monomorphisms. -/
class StrongEpi (f : P ⟶ Q) : Prop where
  /-- The epimorphism condition on `f` -/
  epi : Epi f
  /-- The left lifting property with respect to all monomorphisms -/
  llp : ∀ ⦃X Y : C⦄ (z : X ⟶ Y) [Mono z], HasLiftingProperty f z

/-- A strong monomorphism `f` is a monomorphism which has the right lifting property
with respect to epimorphisms. -/
@[to_dual]
class StrongMono (f : P ⟶ Q) : Prop where
  /-- The monomorphism condition on `f` -/
  mono : Mono f
  /-- The right lifting property with respect to all epimorphisms -/
  rlp : ∀ ⦃X Y : C⦄ (z : X ⟶ Y) [Epi z], HasLiftingProperty z f

attribute [to_dual existing] StrongEpi.llp StrongEpi.mk

@[to_dual (reorder := hf (X Y))]
theorem StrongEpi.mk' {f : P ⟶ Q} [Epi f]
    (hf : ∀ (X Y : C) (z : X ⟶ Y) (_ : Mono z) (u : P ⟶ X)
      (v : Q ⟶ Y) (sq : CommSq u f z v), sq.HasLift) : StrongEpi f where
  epi := inferInstance
  llp {X Y} z hz := ⟨fun {u v} sq => hf X Y z hz u v sq⟩

attribute [instance 100] StrongEpi.epi StrongEpi.llp StrongMono.mono StrongMono.rlp

section

variable {R : C} (f : P ⟶ Q) (g : Q ⟶ R)

/-- The composition of two strong epimorphisms is a strong epimorphism. -/
@[to_dual /-- The composition of two strong monomorphisms is a strong monomorphism. -/]
instance strongEpi_comp [StrongEpi f] [StrongEpi g] : StrongEpi (f ≫ g) :=
  { epi := epi_comp _ _
    llp := by
      intros
      infer_instance }

/-- If `f ≫ g` is a strong epimorphism, then so is `g`. -/
@[to_dual (reorder := f g) (rename := f ↔ g, P ↔ R)
/-- If `f ≫ g` is a strong monomorphism, then so is `f`. -/]
theorem strongEpi_of_strongEpi [StrongEpi (f ≫ g)] : StrongEpi g :=
  { epi := epi_of_epi f g
    llp := fun {X Y} z _ => by
      constructor
      intro u v sq
      have h₀ : (f ≫ u) ≫ z = (f ≫ g) ≫ v := by simp only [Category.assoc, sq.w]
      exact
        CommSq.HasLift.mk'
          ⟨(CommSq.mk h₀).lift, by
            simp only [← cancel_mono z, Category.assoc, CommSq.fac_right, sq.w], by simp⟩ }

/-- An isomorphism is in particular a strong epimorphism. -/
@[to_dual /-- An isomorphism is in particular a strong monomorphism. -/]
instance (priority := 100) strongEpi_of_isIso [IsIso f] : StrongEpi f where
  epi := by infer_instance
  llp {_ _} _ := HasLiftingProperty.of_left_iso _ _

set_option backward.isDefEq.respectTransparency false in
@[to_dual]
theorem StrongEpi.of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) [h : StrongEpi f] : StrongEpi g where
  epi := by
    rw [Arrow.iso_w' e]
    infer_instance
  llp := fun {X Y} z => by
    intro
    apply HasLiftingProperty.of_arrow_iso_left e z

@[to_dual]
theorem StrongEpi.iff_of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) : StrongEpi f ↔ StrongEpi g := by
  constructor <;> intro
  exacts [StrongEpi.of_arrow_iso e, StrongEpi.of_arrow_iso e.symm]

end

/-- A strong epimorphism that is a monomorphism is an isomorphism. -/
@[to_dual /-- A strong monomorphism that is an epimorphism is an isomorphism. -/]
theorem isIso_of_mono_of_strongEpi (f : P ⟶ Q) [StrongEpi f] [Mono f] : IsIso f :=
  ⟨⟨(CommSq.mk (show 𝟙 P ≫ f = f ≫ 𝟙 Q by simp)).lift, by simp⟩⟩

section

variable (C)

/-- A strong epi category is a category in which every epimorphism is strong. -/
class StrongEpiCategory : Prop where
  /-- A strong epi category is a category in which every epimorphism is strong. -/
  strongEpi_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], StrongEpi f

/-- A strong mono category is a category in which every monomorphism is strong. -/
@[to_dual]
class StrongMonoCategory : Prop where
  /-- A strong mono category is a category in which every monomorphism is strong. -/
  strongMono_of_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], StrongMono f

attribute [to_dual existing] StrongEpiCategory.strongEpi_of_epi StrongEpiCategory.mk

end

@[to_dual]
theorem strongEpi_of_epi [StrongEpiCategory C] (f : P ⟶ Q) [Epi f] : StrongEpi f :=
  StrongEpiCategory.strongEpi_of_epi _

section

attribute [local instance] strongEpi_of_epi

@[to_dual]
instance (priority := 100) balanced_of_strongEpiCategory [StrongEpiCategory C] : Balanced C where
  isIso_of_mono_of_epi _ _ _ := isIso_of_mono_of_strongEpi _

end

end CategoryTheory
