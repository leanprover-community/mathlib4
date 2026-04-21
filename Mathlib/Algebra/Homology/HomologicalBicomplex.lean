/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Bicomplexes

Given a category `C` with zero morphisms and two complex shapes
`c₁ : ComplexShape I₁` and `c₂ : ComplexShape I₂`, we define
the type of bicomplexes `HomologicalComplex₂ C c₁ c₂` as an
abbreviation for `HomologicalComplex (HomologicalComplex C c₂) c₁`.
In particular, if `K : HomologicalComplex₂ C c₁ c₂`, then
for each `i₁ : I₁`, `K.X i₁` is a column of `K`.

In this file, we obtain the equivalence of categories
`HomologicalComplex₂.flipEquivalence : HomologicalComplex₂ C c₁ c₂ ≌ HomologicalComplex₂ C c₂ c₁`
which is obtained by exchanging the horizontal and vertical directions.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


open CategoryTheory Limits

variable (C : Type*) [Category* C] [HasZeroMorphisms C]
  {I₁ I₂ : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)

/-- Given a category `C` and two complex shapes `c₁` and `c₂` on types `I₁` and `I₂`,
the associated type of bicomplexes `HomologicalComplex₂ C c₁ c₂` is
`K : HomologicalComplex (HomologicalComplex C c₂) c₁`. Then, the object in
position `⟨i₁, i₂⟩` can be obtained as `(K.X i₁).X i₂`. -/
abbrev HomologicalComplex₂ :=
  HomologicalComplex (HomologicalComplex C c₂) c₁

namespace HomologicalComplex₂

open HomologicalComplex

variable {C c₁ c₂}

/-- The graded object indexed by `I₁ × I₂` induced by a bicomplex. -/
def toGradedObject (K : HomologicalComplex₂ C c₁ c₂) :
    GradedObject (I₁ × I₂) C :=
  fun ⟨i₁, i₂⟩ => (K.X i₁).X i₂

/-- The morphism of graded objects induced by a morphism of bicomplexes. -/
def toGradedObjectMap {K L : HomologicalComplex₂ C c₁ c₂} (φ : K ⟶ L) :
    K.toGradedObject ⟶ L.toGradedObject :=
  fun ⟨i₁, i₂⟩ => (φ.f i₁).f i₂

@[simp]
lemma toGradedObjectMap_apply {K L : HomologicalComplex₂ C c₁ c₂} (φ : K ⟶ L) (i₁ : I₁) (i₂ : I₂) :
    toGradedObjectMap φ ⟨i₁, i₂⟩ = (φ.f i₁).f i₂ := rfl

variable (C c₁ c₂) in
/-- The functor which sends a bicomplex to its associated graded object. -/
@[simps]
def toGradedObjectFunctor : HomologicalComplex₂ C c₁ c₂ ⥤ GradedObject (I₁ × I₂) C where
  obj K := K.toGradedObject
  map φ := toGradedObjectMap φ

instance : (toGradedObjectFunctor C c₁ c₂).Faithful where
  map_injective {_ _ φ₁ φ₂} h := by
    ext i₁ i₂
    exact congr_fun h ⟨i₁, i₂⟩

section OfGradedObject

variable (c₁ c₂)
variable (X : GradedObject (I₁ × I₂) C)
    (d₁ : ∀ (i₁ i₁' : I₁) (i₂ : I₂), X ⟨i₁, i₂⟩ ⟶ X ⟨i₁', i₂⟩)
    (d₂ : ∀ (i₁ : I₁) (i₂ i₂' : I₂), X ⟨i₁, i₂⟩ ⟶ X ⟨i₁, i₂'⟩)
    (shape₁ : ∀ (i₁ i₁' : I₁) (_ : ¬c₁.Rel i₁ i₁') (i₂ : I₂), d₁ i₁ i₁' i₂ = 0)
    (shape₂ : ∀ (i₁ : I₁) (i₂ i₂' : I₂) (_ : ¬c₂.Rel i₂ i₂'), d₂ i₁ i₂ i₂' = 0)
    (d₁_comp_d₁ : ∀ (i₁ i₁' i₁'' : I₁) (i₂ : I₂), d₁ i₁ i₁' i₂ ≫ d₁ i₁' i₁'' i₂ = 0)
    (d₂_comp_d₂ : ∀ (i₁ : I₁) (i₂ i₂' i₂'' : I₂), d₂ i₁ i₂ i₂' ≫ d₂ i₁ i₂' i₂'' = 0)
    (comm : ∀ (i₁ i₁' : I₁) (i₂ i₂' : I₂), d₁ i₁ i₁' i₂ ≫ d₂ i₁' i₂ i₂' =
      d₂ i₁ i₂ i₂' ≫ d₁ i₁ i₁' i₂')

/-- Constructor for bicomplexes taking as inputs a graded object, horizontal differentials
and vertical differentials satisfying suitable relations. -/
@[simps]
def ofGradedObject :
    HomologicalComplex₂ C c₁ c₂ where
  X i₁ :=
    { X := fun i₂ => X ⟨i₁, i₂⟩
      d := fun i₂ i₂' => d₂ i₁ i₂ i₂'
      shape := shape₂ i₁
      d_comp_d' := by intros; apply d₂_comp_d₂ }
  d i₁ i₁' :=
    { f := fun i₂ => d₁ i₁ i₁' i₂
      comm' := by intros; apply comm }
  shape i₁ i₁' h := by
    ext i₂
    exact shape₁ i₁ i₁' h i₂
  d_comp_d' i₁ i₁' i₁'' _ _ := by ext i₂; apply d₁_comp_d₁

@[simp]
lemma ofGradedObject_toGradedObject :
    (ofGradedObject c₁ c₂ X d₁ d₂ shape₁ shape₂ d₁_comp_d₁ d₂_comp_d₂ comm).toGradedObject = X :=
  rfl

end OfGradedObject

/-- Constructor for a morphism `K ⟶ L` in the category `HomologicalComplex₂ C c₁ c₂` which
takes as inputs a morphism `f : K.toGradedObject ⟶ L.toGradedObject` and
the compatibilities with both horizontal and vertical differentials. -/
@[simps!]
def homMk {K L : HomologicalComplex₂ C c₁ c₂}
    (f : K.toGradedObject ⟶ L.toGradedObject)
    (comm₁ : ∀ i₁ i₁' i₂, c₁.Rel i₁ i₁' →
      f ⟨i₁, i₂⟩ ≫ (L.d i₁ i₁').f i₂ = (K.d i₁ i₁').f i₂ ≫ f ⟨i₁', i₂⟩)
    (comm₂ : ∀ i₁ i₂ i₂', c₂.Rel i₂ i₂' →
      f ⟨i₁, i₂⟩ ≫ (L.X i₁).d i₂ i₂' = (K.X i₁).d i₂ i₂' ≫ f ⟨i₁, i₂'⟩) : K ⟶ L where
  f i₁ :=
    { f := fun i₂ => f ⟨i₁, i₂⟩
      comm' := comm₂ i₁ }
  comm' i₁ i₁' h₁ := by
    ext i₂
    exact comm₁ i₁ i₁' i₂ h₁

lemma shape_f (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (h : ¬ c₁.Rel i₁ i₁') (i₂ : I₂) :
    (K.d i₁ i₁').f i₂ = 0 := by
  rw [K.shape _ _ h, zero_f]

@[reassoc (attr := simp)]
lemma d_f_comp_d_f (K : HomologicalComplex₂ C c₁ c₂)
    (i₁ i₁' i₁'' : I₁) (i₂ : I₂) :
    (K.d i₁ i₁').f i₂ ≫ (K.d i₁' i₁'').f i₂ = 0 := by
  rw [← comp_f, d_comp_d, zero_f]

@[reassoc]
lemma d_comm (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (i₂ i₂' : I₂) :
    (K.d i₁ i₁').f i₂ ≫ (K.X i₁').d i₂ i₂' = (K.X i₁).d i₂ i₂' ≫ (K.d i₁ i₁').f i₂' := by
  simp

@[reassoc (attr := simp)]
lemma comm_f {K L : HomologicalComplex₂ C c₁ c₂} (f : K ⟶ L) (i₁ i₁' : I₁) (i₂ : I₂) :
    (f.f i₁).f i₂ ≫ (L.d i₁ i₁').f i₂ = (K.d i₁ i₁').f i₂ ≫ (f.f i₁').f i₂ :=
  congr_hom (f.comm i₁ i₁') i₂

/-- Flip a complex of complexes over the diagonal,
exchanging the horizontal and vertical directions.
-/
@[simps]
def flip (K : HomologicalComplex₂ C c₁ c₂) : HomologicalComplex₂ C c₂ c₁ where
  X i :=
    { X := fun j => (K.X j).X i
      d := fun j j' => (K.d j j').f i
      shape := fun _ _ w => K.shape_f _ _ w i }
  d i i' := { f := fun j => (K.X j).d i i' }
  shape i i' w := by
    ext j
    exact (K.X j).shape i i' w

@[simp]
lemma flip_flip (K : HomologicalComplex₂ C c₁ c₂) : K.flip.flip = K := rfl

variable (C c₁ c₂)

/-- Flipping a complex of complexes over the diagonal, as a functor. -/
@[simps]
def flipFunctor :
    HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex₂ C c₂ c₁ where
  obj K := K.flip
  map {K L} f :=
    { f := fun i =>
        { f := fun j => (f.f j).f i
          comm' := by intros; simp }
      comm' := by intros; ext; simp }

/-- Auxiliary definition for `HomologicalComplex₂.flipEquivalence`. -/
@[simps!]
def flipEquivalenceUnitIso :
    𝟭 (HomologicalComplex₂ C c₁ c₂) ≅ flipFunctor C c₁ c₂ ⋙ flipFunctor C c₂ c₁ :=
  NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun i₁ =>
    HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by simp)) (by cat_disch)) (by cat_disch)

/-- Auxiliary definition for `HomologicalComplex₂.flipEquivalence`. -/
@[simps!]
def flipEquivalenceCounitIso :
    flipFunctor C c₂ c₁ ⋙ flipFunctor C c₁ c₂ ≅ 𝟭 (HomologicalComplex₂ C c₂ c₁) :=
  NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun i₂ =>
    HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by simp)) (by cat_disch)) (by cat_disch)

/-- Flipping a complex of complexes over the diagonal, as an equivalence of categories. -/
@[simps]
def flipEquivalence :
    HomologicalComplex₂ C c₁ c₂ ≌ HomologicalComplex₂ C c₂ c₁ where
  functor := flipFunctor C c₁ c₂
  inverse := flipFunctor C c₂ c₁
  unitIso := flipEquivalenceUnitIso C c₁ c₂
  counitIso := flipEquivalenceCounitIso C c₁ c₂

variable (K : HomologicalComplex₂ C c₁ c₂)

/-- The obvious isomorphism `(K.X x₁).X x₂ ≅ (K.X y₁).X y₂` when `x₁ = y₁` and `x₂ = y₂`. -/
def XXIsoOfEq {x₁ y₁ : I₁} (h₁ : x₁ = y₁) {x₂ y₂ : I₂} (h₂ : x₂ = y₂) :
    (K.X x₁).X x₂ ≅ (K.X y₁).X y₂ :=
  eqToIso (by subst h₁ h₂; rfl)

@[simp]
lemma XXIsoOfEq_rfl (i₁ : I₁) (i₂ : I₂) :
    K.XXIsoOfEq _ _ _ (rfl : i₁ = i₁) (rfl : i₂ = i₂) = Iso.refl _ := rfl


end HomologicalComplex₂
