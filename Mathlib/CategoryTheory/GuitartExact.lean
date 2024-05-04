/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Final

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

universe v₁ v₂ v₃ v₄ v₁' v₂' v₃' v₄' u₁ u₂ u₃ u₄ u₁' u₂' u₃' u₄'

namespace CategoryTheory

open Limits

namespace IsConnected

variable {C D : Type*} [Category C] [Category D]

instance [IsConnected C] [IsConnected D] : IsConnected (C × D) := by
  apply zigzag_isConnected
  intro ⟨X₁, Y₁⟩ ⟨X₂, Y₂⟩
  exact (zigzag_obj_of_zigzag (Functor.prod' (𝟭 C) ((Functor.const C).obj Y₁))
      (isPreconnected_zigzag X₁ X₂)).trans
    (zigzag_obj_of_zigzag (Functor.prod' ((Functor.const D).obj X₂) (𝟭 D))
      (isPreconnected_zigzag Y₁ Y₂))

end IsConnected

open Category

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

section

variable {T}

theorem StructuredArrow.mk_surjective {X₂ : C₂} (f : StructuredArrow X₂ T) :
    ∃ (X₁ : C₁) (g : X₂ ⟶ T.obj X₁), f = mk g := ⟨_, _, eq_mk f⟩

theorem StructuredArrow.homMk_surjective {X₂ : C₂} {f g : StructuredArrow X₂ T} (φ : f ⟶ g) :
    ∃ (ψ : f.right ⟶ g.right) (hψ : f.hom ≫ T.map ψ = g.hom),
      φ = StructuredArrow.homMk ψ hψ := ⟨φ.right, StructuredArrow.w φ, rfl⟩

theorem CostructuredArrow.mk_surjective {X₂ : C₂} (f : CostructuredArrow T X₂) :
    ∃ (X₁ : C₁) (g :T.obj X₁ ⟶ X₂), f = mk g := ⟨_, _, eq_mk f⟩

theorem CostructuredArrow.homMk_surjective {X₂ : C₂} {f g : CostructuredArrow T X₂} (φ : f ⟶ g) :
    ∃ (ψ : f.left ⟶ g.left) (hψ : T.map ψ ≫ g.hom = f.hom),
      φ = CostructuredArrow.homMk ψ hψ := ⟨φ.left, CostructuredArrow.w φ, rfl⟩

end

/-- A `2`-square consists of a natural transformation `T ⋙ R ⟶ L ⋙ B`
involving fours functors `T`, `L`, `R`, `B` that are on the
top/left/right/bottom sides of a square of categories. -/
def TwoSquare := T ⋙ R ⟶ L ⋙ B

namespace TwoSquare

abbrev mk (α : T ⋙ R ⟶ L ⋙ B) : TwoSquare T L R B := α

variable {T L R B}

@[ext]
lemma ext (w w' : TwoSquare T L R B) (h : ∀ (X : C₁), w.app X = w'.app X) :
    w = w' :=
  NatTrans.ext _ _ (funext h)

variable (w : TwoSquare T L R B)

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
  (comm : R.map a ≫ w.app X₁ ≫ B.map b = g)

/-- Constructor for objects in `w.StructuredArrowRightwards g`. -/
abbrev StructuredArrowRightwards.mk : w.StructuredArrowRightwards g :=
  StructuredArrow.mk (Y := CostructuredArrow.mk b) (CostructuredArrow.homMk a comm)

/-- Constructor for objects in `w.CostructuredArrowDownwards g`. -/
abbrev CostructuredArrowDownwards.mk : w.CostructuredArrowDownwards g :=
  CostructuredArrow.mk (Y := StructuredArrow.mk a)
    (StructuredArrow.homMk b (by simpa using comm))

variable {w g}

lemma StructuredArrowRightwards.mk_surjective
    (f : w.StructuredArrowRightwards g) :
    ∃ (X₁ : C₁) (a : X₂ ⟶ T.obj X₁) (b : L.obj X₁ ⟶ X₃) (comm : R.map a ≫ w.app X₁ ≫ B.map b = g),
      f = mk w g X₁ a b comm := by
  obtain ⟨g, φ, rfl⟩ := StructuredArrow.mk_surjective f
  obtain ⟨X₁, b, rfl⟩ := g.mk_surjective
  obtain ⟨a, ha, rfl⟩ := CostructuredArrow.homMk_surjective φ
  exact ⟨X₁, a, b, by simpa using ha, rfl⟩

lemma CostructuredArrowDownwards.mk_surjective
    (f : w.CostructuredArrowDownwards g) :
    ∃ (X₁ : C₁) (a : X₂ ⟶ T.obj X₁) (b : L.obj X₁ ⟶ X₃) (comm : R.map a ≫ w.app X₁ ≫ B.map b = g),
      f = mk w g X₁ a b comm := by
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
  ⟨fun h => h.isConnected_rightwards, fun h => ⟨h⟩⟩

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
  ⟨fun _ _ => ⟨fun _ => inferInstance⟩, fun _ => ⟨fun _ => inferInstance⟩⟩

instance [hw : w.GuitartExact] (X₃ : C₃) :
    (w.costructuredArrowRightwards X₃).Final := by
  rw [guitartExact_iff_final] at hw
  apply hw

lemma guitartExact_iff_initial :
    w.GuitartExact ↔ ∀ (X₂ : C₂), (w.structuredArrowDownwards X₂).Initial :=
  ⟨fun _ _ => ⟨fun _ => inferInstance⟩, by
    rw [guitartExact_iff_isConnected_downwards]
    intros
    infer_instance⟩

instance [hw : w.GuitartExact] (X₂ : C₂) :
    (w.structuredArrowDownwards X₂).Initial := by
  rw [guitartExact_iff_initial] at hw
  apply hw

instance [L.IsEquivalence] [R.IsEquivalence] [IsIso w] : GuitartExact w := by
  rw [guitartExact_iff_initial]
  intro X₂
  have := StructuredArrow.isEquivalencePost X₂ T R
  have : (Comma.mapRight _ w : StructuredArrow (R.obj X₂) _ ⥤ StructuredArrow (R.obj X₂) _).IsEquivalence :=
    Functor.IsEquivalence.ofEquivalence (Comma.mapRightIso _ (asIso w))
  have := StructuredArrow.isEquivalencePre (R.obj X₂) L B
  dsimp only [structuredArrowDownwards]
  infer_instance

@[simps!]
def whiskerVertical {L' : C₁ ⥤ C₃} {R' : C₂ ⥤ C₄} (α : L ⟶ L') (β : R' ⟶ R) :
    TwoSquare T L' R' B :=
  whiskerLeft _ β ≫ w ≫ whiskerRight α _

namespace GuitartExact

lemma whiskerVertical [w.GuitartExact] {L' : C₁ ⥤ C₃} {R' : C₂ ⥤ C₄}
    (α : L ≅ L') (β : R ≅ R') : (w.whiskerVertical α.hom β.inv).GuitartExact := by
  rw [guitartExact_iff_initial]
  intro X₂
  let e : structuredArrowDownwards (w.whiskerVertical α.hom β.inv) X₂ ≅
      w.structuredArrowDownwards X₂ ⋙ (StructuredArrow.mapIso (β.app X₂) ).functor :=
    NatIso.ofComponents (fun f => StructuredArrow.isoMk (α.symm.app f.right) (by
      dsimp
      simp only [NatTrans.naturality_assoc, assoc, NatIso.cancel_natIso_inv_left, ← B.map_comp,
        Iso.hom_inv_id_app, B.map_id, comp_id])) (by aesop_cat)
  rw [Functor.initial_natIso_iff e]
  infer_instance

@[simp]
lemma whiskerVertical_iff {L' : C₁ ⥤ C₃} {R' : C₂ ⥤ C₄}
    (α : L ≅ L') (β : R ≅ R') :
    (w.whiskerVertical α.hom β.inv).GuitartExact ↔ w.GuitartExact := by
  constructor
  · intro h
    have : w = TwoSquare.whiskerVertical
        (TwoSquare.whiskerVertical w α.hom β.inv) α.inv β.hom := by
      ext X₁
      simp only [Functor.comp_obj, whiskerVertical_app, assoc, Iso.hom_inv_id_app_assoc,
        ← B.map_comp, Iso.hom_inv_id_app, B.map_id, comp_id]
    rw [this]
    exact whiskerVertical (w.whiskerVertical α.hom β.inv) α.symm β.symm
  · intro h
    exact whiskerVertical w α β

instance [w.GuitartExact] {L' : C₁ ⥤ C₃} {R' : C₂ ⥤ C₄} (α : L ⟶ L') (β : R' ⟶ R)
    [IsIso α] [IsIso β] : (w.whiskerVertical α β).GuitartExact :=
  whiskerVertical w (asIso α) (asIso β).symm

end GuitartExact

section prod

variable {C₁' : Type u₁'} {C₂' : Type u₂'} {C₃' : Type u₃'} {C₄' : Type u₄'}
  [Category.{v₁'} C₁'] [Category.{v₂'} C₂'] [Category.{v₃'} C₃'] [Category.{v₄'} C₄']
  {T' : C₁' ⥤ C₂'} {L' : C₁' ⥤ C₃'} {R' : C₂' ⥤ C₄'} {B' : C₃' ⥤ C₄'}
  (w' : TwoSquare T' L' R' B')

def prod : TwoSquare (T.prod T') (L.prod L') (R.prod R') (B.prod B') := NatTrans.prod w w'

section

variable {Y₂ : C₂ × C₂'} {Y₃ : C₃ × C₃'} (g : (R.prod R').obj Y₂ ⟶ (B.prod B').obj Y₃)

namespace JRightwardsProdEquivalence

@[simp]
def functorObj (X : StructuredArrowRightwards (w.prod w') g) : (StructuredArrowRightwards w g.1) × (StructuredArrowRightwards w' g.2) :=
  ⟨StructuredArrowRightwards.mk w g.1 _ X.hom.left.1 X.right.hom.1
      (by simpa using congr_arg _root_.Prod.fst X.hom.w),
    StructuredArrowRightwards.mk w' g.2 _ X.hom.left.2 X.right.hom.2
      (by simpa using congr_arg _root_.Prod.snd X.hom.w)⟩

@[simps]
def functor : StructuredArrowRightwards (w.prod w') g ⥤ (StructuredArrowRightwards w g.1) × (StructuredArrowRightwards w' g.2) where
  obj X := functorObj w w' g X
  map {X Y} f :=
    ⟨StructuredArrow.homMk (CostructuredArrow.homMk f.right.left.1
        (by simpa using congr_arg _root_.Prod.fst f.right.w)) (by
          ext
          have eq := StructuredArrow.w f
          dsimp at eq ⊢
          rw [← eq]
          rfl),
      StructuredArrow.homMk (CostructuredArrow.homMk f.right.left.2
        (by simpa using congr_arg _root_.Prod.snd f.right.w)) (by
          ext
          have eq := StructuredArrow.w f
          dsimp at eq ⊢
          rw [← eq]
          rfl)⟩
  map_id _ := rfl
  map_comp f g := rfl

@[simp]
def inverseObj (X : (StructuredArrowRightwards w g.1) × (StructuredArrowRightwards w' g.2)) : StructuredArrowRightwards (w.prod w') g :=
  StructuredArrowRightwards.mk _ _ ⟨X.1.right.left, X.2.right.left⟩
    ⟨X.1.hom.left, X.2.hom.left⟩ ⟨X.1.right.hom, X.2.right.hom⟩ (by
      dsimp
      ext
      · simpa using X.1.hom.w
      · simpa using X.2.hom.w)

@[simps]
def inverse : (StructuredArrowRightwards w g.1) × (StructuredArrowRightwards w' g.2) ⥤ StructuredArrowRightwards (w.prod w') g where
  obj X := inverseObj w w' g X
  map {X Y} f := StructuredArrow.homMk
    (CostructuredArrow.homMk ⟨f.1.right.left, f.2.right.left⟩ (by
      dsimp
      ext
      · exact CostructuredArrow.w f.1.right
      · exact CostructuredArrow.w f.2.right)) (by
      dsimp
      ext
      dsimp
      ext
      · have eq := StructuredArrow.w f.1
        dsimp at eq ⊢
        rw [← eq]
        rfl
      · have eq := StructuredArrow.w f.2
        dsimp at eq ⊢
        rw [← eq]
        rfl)
  map_id _ := rfl
  map_comp _ _ := rfl

end JRightwardsProdEquivalence

set_option maxHeartbeats 400000 in
@[simps]
def StructuredArrowRightwardsProdEquivalence :
    StructuredArrowRightwards (w.prod w') g ≌ (StructuredArrowRightwards w g.1) × (StructuredArrowRightwards w' g.2) where
  functor := JRightwardsProdEquivalence.functor w w' g
  inverse := JRightwardsProdEquivalence.inverse w w' g
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp X := by
    dsimp
    erw [comp_id, comp_id]
    rfl

end

namespace GuitartExact

instance prod [w.GuitartExact] [w'.GuitartExact] :
    (w.prod w').GuitartExact := by
  rw [guitartExact_iff_isConnected_rightwards]
  rintro Y₂ Y₃ g
  exact isConnected_of_equivalent (StructuredArrowRightwardsProdEquivalence w w' g).symm

instance id (F : C₁ ⥤ C₂) : TwoSquare.GuitartExact (show TwoSquare (𝟭 C₁) F F (𝟭 C₂) from 𝟙 F) := by
  rw [guitartExact_iff_isConnected_rightwards]
  intro X₂ X₃ (g : F.obj X₂ ⟶ X₃)
  let Z := StructuredArrowRightwards (show TwoSquare (𝟭 C₁) F F (𝟭 C₂) from 𝟙 F) g
  let X₀ : Z := StructuredArrow.mk (Y := CostructuredArrow.mk g) (CostructuredArrow.homMk (𝟙 _))
  have φ : ∀ (X : Z), X₀ ⟶ X := fun X =>
    StructuredArrow.homMk (CostructuredArrow.homMk X.hom.left
      (by simpa using CostructuredArrow.w X.hom))
  have : Nonempty Z := ⟨X₀⟩
  change IsConnected Z
  apply zigzag_isConnected
  intro X Y
  exact (zigzag_symmetric (Relation.ReflTransGen.single (Or.inl ⟨φ X⟩))).trans
    (Relation.ReflTransGen.single (Or.inl ⟨φ Y⟩))

end GuitartExact

end prod

end TwoSquare

end CategoryTheory
