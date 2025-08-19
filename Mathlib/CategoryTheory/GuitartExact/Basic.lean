/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Functor.TwoSquare

/-!
# Guitart exact squares

Given four functors `T`, `L`, `R` and `B`, a 2-square `TwoSquare T L R B` consists of
a natural transformation `w : T ⋙ R ⟶ L ⋙ B`:
```
     T
  C₁ ⥤ C₂
L |     | R
  v     v
  C₃ ⥤ C₄
     B
```

In this file, we define a typeclass `w.GuitartExact` which expresses
that this square is exact in the sense of Guitart. This means that
for any `X₃ : C₃`, the induced functor
`CostructuredArrow L X₃ ⥤ CostructuredArrow R (B.obj X₃)` is final.
It is also equivalent to the fact that for any `X₂ : C₂`, the
induced functor `StructuredArrow X₂ T ⥤ StructuredArrow (R.obj X₂) B`
is initial.

Various categorical notions (fully faithful functors, adjunctions, etc.) can
be characterized in terms of Guitart exact squares. Their particular role
in pointwise Kan extensions shall also be used in the construction of
derived functors.

## TODO

* Define the notion of derivability structure from
[the paper by Kahn and Maltsiniotis][KahnMaltsiniotis2008] using Guitart exact squares
and construct (pointwise) derived functors using this notion

## References
* https://ncatlab.org/nlab/show/exact+square
* [René Guitart, *Relations et carrés exacts*][Guitart1980]
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Category

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

namespace TwoSquare

variable {T L R B} (w : TwoSquare T L R B)

/-- Given `w : TwoSquare T L R B` and `X₃ : C₃`, this is the obvious functor
`CostructuredArrow L X₃ ⥤ CostructuredArrow R (B.obj X₃)`. -/
@[simps! obj map]
def costructuredArrowRightwards (X₃ : C₃) :
    CostructuredArrow L X₃ ⥤ CostructuredArrow R (B.obj X₃) :=
  CostructuredArrow.post L B X₃ ⋙ Comma.mapLeft _ w ⋙
    CostructuredArrow.pre T R (B.obj X₃)

/-- Given `w : TwoSquare T L R B` and `X₂ : C₂`, this is the obvious functor
`StructuredArrow X₂ T ⥤ StructuredArrow (R.obj X₂) B`. -/
@[simps! obj map]
def structuredArrowDownwards (X₂ : C₂) :
    StructuredArrow X₂ T ⥤ StructuredArrow (R.obj X₂) B :=
  StructuredArrow.post X₂ T R ⋙ Comma.mapRight _ w ⋙
    StructuredArrow.pre (R.obj X₂) L B

section

variable {X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃)

/- In [the paper by Kahn and Maltsiniotis, §4.3][KahnMaltsiniotis2008], given
`w : TwoSquare T L R B` and `g : R.obj X₂ ⟶ B.obj X₃`, a category `J` is introduced
and it is observed that it is equivalent to the two categories
`w.StructuredArrowRightwards g` and `w.CostructuredArrowDownwards g`. We shall show below
that there is an equivalence
`w.equivalenceJ g : w.StructuredArrowRightwards g ≌ w.CostructuredArrowDownwards g`. -/

/-- Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is the
category `StructuredArrow (CostructuredArrow.mk g) (w.costructuredArrowRightwards X₃)`,
see the constructor `StructuredArrowRightwards.mk` for the data that is involved. -/
abbrev StructuredArrowRightwards :=
  StructuredArrow (CostructuredArrow.mk g) (w.costructuredArrowRightwards X₃)

/-- Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is the
category `CostructuredArrow (w.structuredArrowDownwards X₂) (StructuredArrow.mk g)`,
see the constructor `CostructuredArrowDownwards.mk` for the data that is involved. -/
abbrev CostructuredArrowDownwards :=
  CostructuredArrow (w.structuredArrowDownwards X₂) (StructuredArrow.mk g)

section

variable (X₁ : C₁) (a : X₂ ⟶ T.obj X₁) (b : L.obj X₁ ⟶ X₃)

/-- Constructor for objects in `w.StructuredArrowRightwards g`. -/
abbrev StructuredArrowRightwards.mk (comm : R.map a ≫ w.app X₁ ≫ B.map b = g) :
    w.StructuredArrowRightwards g :=
  StructuredArrow.mk (Y := CostructuredArrow.mk b) (CostructuredArrow.homMk a comm)

/-- Constructor for objects in `w.CostructuredArrowDownwards g`. -/
abbrev CostructuredArrowDownwards.mk (comm : R.map a ≫ w.app X₁ ≫ B.map b = g) :
    w.CostructuredArrowDownwards g :=
  CostructuredArrow.mk (Y := StructuredArrow.mk a)
    (StructuredArrow.homMk b (by simpa using comm))

variable {w g}

lemma StructuredArrowRightwards.mk_surjective
    (f : w.StructuredArrowRightwards g) :
    ∃ (X₁ : C₁) (a : X₂ ⟶ T.obj X₁) (b : L.obj X₁ ⟶ X₃)
      (comm : R.map a ≫ w.app X₁ ≫ B.map b = g), f = mk w g X₁ a b comm := by
  obtain ⟨g, φ, rfl⟩ := StructuredArrow.mk_surjective f
  obtain ⟨X₁, b, rfl⟩ := g.mk_surjective
  obtain ⟨a, ha, rfl⟩ := CostructuredArrow.homMk_surjective φ
  exact ⟨X₁, a, b, by simpa using ha, rfl⟩

lemma CostructuredArrowDownwards.mk_surjective
    (f : w.CostructuredArrowDownwards g) :
    ∃ (X₁ : C₁) (a : X₂ ⟶ T.obj X₁) (b : L.obj X₁ ⟶ X₃)
      (comm : R.map a ≫ w.app X₁ ≫ B.map b = g), f = mk w g X₁ a b comm := by
  obtain ⟨g, φ, rfl⟩ := CostructuredArrow.mk_surjective f
  obtain ⟨X₁, a, rfl⟩ := g.mk_surjective
  obtain ⟨b, hb, rfl⟩ := StructuredArrow.homMk_surjective φ
  exact ⟨X₁, a, b, by simpa using hb, rfl⟩

end

namespace EquivalenceJ

/-- Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is
the obvious functor `w.StructuredArrowRightwards g ⥤ w.CostructuredArrowDownwards g`. -/
@[simps]
def functor : w.StructuredArrowRightwards g ⥤ w.CostructuredArrowDownwards g where
  obj f := CostructuredArrow.mk (Y := StructuredArrow.mk f.hom.left)
      (StructuredArrow.homMk f.right.hom (by simpa using CostructuredArrow.w f.hom))
  map {f₁ f₂} φ :=
    CostructuredArrow.homMk (StructuredArrow.homMk φ.right.left
      (by dsimp; rw [← StructuredArrow.w φ]; rfl))
      (by ext; exact CostructuredArrow.w φ.right)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is
the obvious functor `w.CostructuredArrowDownwards g ⥤ w.StructuredArrowRightwards g`. -/
@[simps]
def inverse : w.CostructuredArrowDownwards g ⥤ w.StructuredArrowRightwards g where
  obj f := StructuredArrow.mk (Y := CostructuredArrow.mk f.hom.right)
      (CostructuredArrow.homMk f.left.hom (by simpa using StructuredArrow.w f.hom))
  map {f₁ f₂} φ :=
    StructuredArrow.homMk (CostructuredArrow.homMk φ.left.right
      (by dsimp; rw [← CostructuredArrow.w φ]; rfl))
      (by ext; exact StructuredArrow.w φ.left)
  map_id _ := rfl
  map_comp _ _ := rfl

end EquivalenceJ

/-- Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is
the obvious equivalence of categories
`w.StructuredArrowRightwards g ≌ w.CostructuredArrowDownwards g`. -/
@[simps functor inverse unitIso counitIso]
def equivalenceJ : w.StructuredArrowRightwards g ≌ w.CostructuredArrowDownwards g where
  functor := EquivalenceJ.functor w g
  inverse := EquivalenceJ.inverse w g
  unitIso := Iso.refl _
  counitIso := Iso.refl _

lemma isConnected_rightwards_iff_downwards :
    IsConnected (w.StructuredArrowRightwards g) ↔ IsConnected (w.CostructuredArrowDownwards g) :=
  isConnected_iff_of_equivalence (w.equivalenceJ g)

end

section

/-- The functor `w.CostructuredArrowDownwards g ⥤ w.CostructuredArrowDownwards g'` induced
by a morphism `γ` such that `R.map γ ≫ g = g'`. -/
@[simps]
def costructuredArrowDownwardsPrecomp
    {X₂ X₂' : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃) (g' : R.obj X₂' ⟶ B.obj X₃)
    (γ : X₂' ⟶ X₂) (hγ : R.map γ ≫ g = g') :
    w.CostructuredArrowDownwards g ⥤ w.CostructuredArrowDownwards g' where
  obj A := CostructuredArrowDownwards.mk _ _ A.left.right (γ ≫ A.left.hom) A.hom.right
    (by simpa [← hγ] using R.map γ ≫= StructuredArrow.w A.hom)
  map {A A'} φ := CostructuredArrow.homMk (StructuredArrow.homMk φ.left.right (by
      dsimp
      rw [assoc, StructuredArrow.w])) (by
    ext
    dsimp
    rw [← CostructuredArrow.w φ, structuredArrowDownwards_map]
    rfl)
  map_id _ := rfl
  map_comp _ _ := rfl

end

/-- Condition on `w : TwoSquare T L R B` expressing that it is a Guitart exact square.
It is equivalent to saying that for any `X₃ : C₃`, the induced functor
`CostructuredArrow L X₃ ⥤ CostructuredArrow R (B.obj X₃)` is final (see `guitartExact_iff_final`)
or equivalently that for any `X₂ : C₂`, the induced functor
`StructuredArrow X₂ T ⥤ StructuredArrow (R.obj X₂) B` is initial (see `guitartExact_iff_initial`).
See also  `guitartExact_iff_isConnected_rightwards`, `guitartExact_iff_isConnected_downwards`
for characterizations in terms of the connectedness of auxiliary categories. -/
class GuitartExact : Prop where
  isConnected_rightwards {X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃) :
    IsConnected (w.StructuredArrowRightwards g)

lemma guitartExact_iff_isConnected_rightwards :
    w.GuitartExact ↔ ∀ {X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃),
      IsConnected (w.StructuredArrowRightwards g) :=
  ⟨fun h ↦ h.isConnected_rightwards, fun h ↦ ⟨h⟩⟩

lemma guitartExact_iff_isConnected_downwards :
    w.GuitartExact ↔ ∀ {X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃),
      IsConnected (w.CostructuredArrowDownwards g) := by
  simp only [guitartExact_iff_isConnected_rightwards,
    isConnected_rightwards_iff_downwards]

instance [hw : w.GuitartExact] {X₃ : C₃} (g : CostructuredArrow R (B.obj X₃)) :
    IsConnected (StructuredArrow g (w.costructuredArrowRightwards X₃)) := by
  rw [guitartExact_iff_isConnected_rightwards] at hw
  apply hw

instance [hw : w.GuitartExact] {X₂ : C₂} (g : StructuredArrow (R.obj X₂) B) :
    IsConnected (CostructuredArrow (w.structuredArrowDownwards X₂) g) := by
  rw [guitartExact_iff_isConnected_downwards] at hw
  apply hw

lemma guitartExact_iff_final :
    w.GuitartExact ↔ ∀ (X₃ : C₃), (w.costructuredArrowRightwards X₃).Final :=
  ⟨fun _ _ ↦ ⟨fun _ ↦ inferInstance⟩, fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩

instance [hw : w.GuitartExact] (X₃ : C₃) :
    (w.costructuredArrowRightwards X₃).Final := by
  rw [guitartExact_iff_final] at hw
  apply hw

lemma guitartExact_iff_initial :
    w.GuitartExact ↔ ∀ (X₂ : C₂), (w.structuredArrowDownwards X₂).Initial :=
  ⟨fun _ _ ↦ ⟨fun _ ↦ inferInstance⟩, by
    rw [guitartExact_iff_isConnected_downwards]
    intros
    infer_instance⟩

instance [hw : w.GuitartExact] (X₂ : C₂) :
    (w.structuredArrowDownwards X₂).Initial := by
  rw [guitartExact_iff_initial] at hw
  apply hw

/-- When the left and right functors of a 2-square are equivalences, and the natural
transformation of the 2-square is an isomorphism, then the 2-square is Guitart exact. -/
instance (priority := 100) guitartExact_of_isEquivalence_of_isIso
    [L.IsEquivalence] [R.IsEquivalence] [IsIso w] : GuitartExact w := by
  rw [guitartExact_iff_initial]
  intro X₂
  have := StructuredArrow.isEquivalence_post X₂ T R
  have : (Comma.mapRight _ w : StructuredArrow (R.obj X₂) _ ⥤ _).IsEquivalence :=
    (Comma.mapRightIso _ (asIso w)).isEquivalence_functor
  have := StructuredArrow.isEquivalence_pre (R.obj X₂) L B
  dsimp only [structuredArrowDownwards]
  infer_instance

instance guitartExact_id (F : C₁ ⥤ C₂) :
    GuitartExact (TwoSquare.mk (𝟭 C₁) F F (𝟭 C₂) (𝟙 F)) := by
  rw [guitartExact_iff_isConnected_rightwards]
  intro X₂ X₃ (g : F.obj X₂ ⟶ X₃)
  let Z := StructuredArrowRightwards (TwoSquare.mk (𝟭 C₁) F F (𝟭 C₂) (𝟙 F)) g
  let X₀ : Z := StructuredArrow.mk (Y := CostructuredArrow.mk g) (CostructuredArrow.homMk (𝟙 _))
  have φ : ∀ (X : Z), X₀ ⟶ X := fun X ↦
    StructuredArrow.homMk (CostructuredArrow.homMk X.hom.left
      (by simpa using CostructuredArrow.w X.hom))
  have : Nonempty Z := ⟨X₀⟩
  apply zigzag_isConnected
  intro X Y
  exact Zigzag.of_inv_hom (φ X) (φ Y)

end TwoSquare

end CategoryTheory
