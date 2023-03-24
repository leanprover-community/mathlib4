/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin, Andrew Yang

! This file was ported from Lean 3 source module category_theory.shift
! leanprover-community/mathlib commit 14b69e9f3c16630440a2cbd46f1ddad0d561dee7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Monoidal.End
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.Tactic.LibrarySearch

/-!
# Shift

A `Shift` on a category `C` indexed by a monoid `A` is nothing more than a monoidal functor
from `A` to `C ⥤ C`. A typical example to keep in mind might be the category of
complexes `⋯ → C_{n-1} → C_n → C_{n+1} → ⋯`. It has a shift indexed by `ℤ`, where we assign to
each `n : ℤ` the functor `C ⥤ C` that re-indexes the terms, so the degree `i` term of `Shift n C`
would be the degree `i+n`-th term of `C`.

## Main definitions
* `HasShift`: A typeclass asserting the existence of a shift functor.
* `shiftEquiv`: When the indexing monoid is a group, then the functor indexed by `n` and `-n` forms
  an self-equivalence of `C`.
* `shiftComm`: When the indexing monoid is commutative, then shifts commute as well.

## Implementation Notes

`[HasShift C A]` is implemented using `MonoidalFunctor (Discrete A) (C ⥤ C)`.
However, the API of monodial functors is used only internally: one should use the API of
shifts functors which includes `shiftFunctor C a : C ⥤ C` for `a : A`,
`shiftFunctorZero C A : shiftFunctor C (0 : A) ≅ 𝟭 C` and
`shiftFunctorAdd C i j : shiftFunctor C (i + j) ≅ shiftFunctor C i ⋙ shiftFunctor C j`
(and its variant `shiftFunctorAdd'`). These isomorphisms satisfy some coherence properties
which are stated in lemmas like `shiftFunctorAdd'_assoc`, `shiftFunctorAdd'_zero_add` and
`shiftFunctorAdd'_add_zero`.

-/


namespace CategoryTheory

noncomputable section

universe v u

variable (C : Type u) (A : Type _) [Category.{v} C]

attribute [local instance] endofunctorMonoidalCategory

section EqToHom

variable {A C}

variable [AddMonoid A] (F : MonoidalFunctor (Discrete A) (C ⥤ C))

-- porting note: the simp tag was removed because the linter complained it would never apply
@[reassoc]
theorem eqToHom_μ_app {i j i' j' : A} (h₁ : i = i') (h₂ : j = j') (X : C) :
    eqToHom (by rw [h₁, h₂] : (F.obj ⟨i⟩ ⊗ F.obj ⟨j⟩).obj X = (F.obj ⟨i'⟩ ⊗ F.obj ⟨j'⟩).obj X) ≫
        (F.μ ⟨i'⟩ ⟨j'⟩).app X =
      (F.μ ⟨i⟩ ⟨j⟩).app X ≫ eqToHom (by rw [h₁, h₂]) := by
  cases h₁
  cases h₂
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
#align category_theory.eq_to_hom_μ_app CategoryTheory.eqToHom_μ_app

-- porting note: the simp tag was removed because the linter complained it would never apply
@[reassoc]
theorem μ_inv_app_eqToHom {i j i' j' : A} (h₁ : i = i') (h₂ : j = j') (X : C) :
    inv ((F.μ ⟨i⟩ ⟨j⟩).app X) ≫ eqToHom (by rw [h₁, h₂]) =
      eqToHom (by rw [h₁, h₂]) ≫ inv ((F.μ ⟨i'⟩ ⟨j'⟩).app X) := by
  cases h₁
  cases h₂
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
#align category_theory.μ_inv_app_eq_to_hom CategoryTheory.μ_inv_app_eqToHom

end EqToHom

variable {A C}

/-- A monoidal functor from a group `A` into `C ⥤ C` induces
a self-equivalence of `C` for each `n : A`. -/
@[simps! functor inverse unitIso_hom unitIso_inv counitIso_hom counitIso_inv]
def addNegEquiv [AddGroup A] (F : MonoidalFunctor (Discrete A) (C ⥤ C)) (n : A) : C ≌ C :=
  equivOfTensorIsoUnit F ⟨n⟩ ⟨(-n : A)⟩ (Discrete.eqToIso (add_neg_self n))
    (Discrete.eqToIso (neg_add_self n)) (Subsingleton.elim _ _)
#align category_theory.add_neg_equiv CategoryTheory.addNegEquiv

section Defs

variable (A C) [AddMonoid A]

/-- A category has a shift indexed by an additive monoid `A`
if there is a monoidal functor from `A` to `C ⥤ C`. -/
class HasShift (C : Type u) (A : Type _) [Category.{v} C] [AddMonoid A] where
  /-- a shift is a monoidal functor from `A` to `C ⥤ C` -/
  shift : MonoidalFunctor (Discrete A) (C ⥤ C)
#align category_theory.has_shift CategoryTheory.HasShift

-- porting note: removed @[nolint has_nonempty_instance]
/-- A helper structure to construct the shift functor `(Discrete A) ⥤ (C ⥤ C)`. -/
structure ShiftMkCore where
  /-- the family of shift functors -/
  F : A → C ⥤ C
  /-- the shift by 0 identifies to the identity functor -/
  ε : 𝟭 C ≅ F 0
  /-- the composition of shift functors identifies to the shift by the sum -/
  μ : ∀ n m : A, F n ⋙ F m ≅ F (n + m)
  /-- compatibility with the associativity -/
  associativity :
    ∀ (m₁ m₂ m₃ : A) (X : C),
      (F m₃).map ((μ m₁ m₂).hom.app X) ≫
          (μ (m₁ + m₂) m₃).hom.app X ≫
            eqToHom (by congr 2; rw [add_assoc]) =
        (μ m₂ m₃).hom.app ((F m₁).obj X) ≫ (μ m₁ (m₂ + m₃)).hom.app X := by aesop_cat
  /-- compatibility with the left addition with 0 -/
  left_unitality :
    ∀ (n : A) (X : C),
      (F n).map (ε.hom.app X) ≫ (μ 0 n).hom.app X =
        eqToHom (by dsimp; rw [zero_add]) := by aesop_cat
  /-- compatibility with the right addition with 0 -/
  right_unitality :
    ∀ (n : A) (X : C),
      ε.hom.app ((F n).obj X) ≫ (μ n 0).hom.app X =
        eqToHom (by dsimp; rw [add_zero]) := by aesop_cat
#align category_theory.shift_mk_core CategoryTheory.ShiftMkCore

section

attribute [local simp] eqToHom_map

--attribute [local reducible] endofunctorMonoidalCategory Discrete.addMonoidal

/-- Constructs a `HasShift C A` instance from `ShiftMkCore`. -/
@[simps]
def hasShiftMk (h : ShiftMkCore C A) : HasShift C A :=
  ⟨{ Discrete.functor h.F with
      ε := h.ε.hom
      μ := fun m n => (h.μ m.as n.as).hom
      μ_natural := by
        rintro ⟨X⟩ ⟨Y⟩ ⟨X'⟩ ⟨Y'⟩ ⟨⟨⟨rfl⟩⟩⟩ ⟨⟨⟨rfl⟩⟩⟩
        ext
        dsimp
        simp
      associativity := by
        introv
        ext x
        dsimp [endofunctorMonoidalCategory]
        simpa using h.associativity _ _ _ _
      left_unitality := by
        rintro ⟨X⟩
        ext
        dsimp [endofunctorMonoidalCategory]
        rw [Category.id_comp, ← Category.assoc, h.left_unitality]
        simp
      right_unitality := by
        rintro ⟨X⟩
        ext
        dsimp [endofunctorMonoidalCategory]
        rw [Functor.map_id, Category.comp_id, ← Category.assoc, h.right_unitality]
        simp }⟩
#align category_theory.has_shift_mk CategoryTheory.hasShiftMk

end

variable [HasShift C A]

/-- The monoidal functor from `A` to `C ⥤ C` given a `HasShift` instance. -/
def shiftMonoidalFunctor : MonoidalFunctor (Discrete A) (C ⥤ C) :=
  HasShift.shift
#align category_theory.shift_monoidal_functor CategoryTheory.shiftMonoidalFunctor

variable {A}

/-- The shift autoequivalence, moving objects and morphisms 'up'. -/
def shiftFunctor (i : A) : C ⥤ C :=
  (shiftMonoidalFunctor C A).obj ⟨i⟩
#align category_theory.shift_functor CategoryTheory.shiftFunctor

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
def shiftFunctorAdd (i j : A) : shiftFunctor C (i + j) ≅ shiftFunctor C i ⋙ shiftFunctor C j :=
  ((shiftMonoidalFunctor C A).μIso ⟨i⟩ ⟨j⟩).symm
#align category_theory.shift_functor_add CategoryTheory.shiftFunctorAdd

/-- When `k = i + j`, shifting by `k` is the same as shifting by `i` and then shifting by `j`. -/
def shiftFunctorAdd' (i j k : A) (h : i + j = k) :
  shiftFunctor C k ≅ shiftFunctor C i ⋙ shiftFunctor C j :=
  eqToIso (by rw [h]) ≪≫ shiftFunctorAdd C i j

lemma shiftFunctorAdd'_eq_shiftFunctorAdd (i j : A) :
  shiftFunctorAdd' C i j (i+j) rfl = shiftFunctorAdd C i j := by
  ext1
  apply Category.id_comp

variable (A)

/-- Shifting by zero is the identity functor. -/
def shiftFunctorZero : shiftFunctor C (0 : A) ≅ 𝟭 C :=
  (shiftMonoidalFunctor C A).εIso.symm
#align category_theory.shift_functor_zero CategoryTheory.shiftFunctorZero

variable {C A}

lemma shiftFunctor_of_hasShiftMk (h : ShiftMkCore C A) (a : A) :
    letI := hasShiftMk C A h;
    shiftFunctor C a = h.F a := by
  rfl

lemma shiftFunctorZero_of_hasShiftMk (h : ShiftMkCore C A) :
    letI := hasShiftMk C A h;
    shiftFunctorZero C A = h.ε.symm  := by
  letI := hasShiftMk C A h
  change (shiftFunctorZero C A).symm.symm = h.ε.symm
  congr 1
  ext
  rfl

lemma shiftFunctorAdd_of_hasShiftMk (h : ShiftMkCore C A) (a b : A) :
    letI := hasShiftMk C A h;
    shiftFunctorAdd C a b = (h.μ a b).symm  := by
  letI := hasShiftMk C A h
  change (shiftFunctorAdd C a b).symm.symm = (h.μ a b).symm
  congr 1
  ext
  rfl

set_option quotPrecheck false in
/-- shifting an object `X` by `n` is obtained by the notation `X⟦n⟧` -/
notation -- Any better notational suggestions?
X "⟦" n "⟧" => (shiftFunctor _ n).obj X

set_option quotPrecheck false in
/-- shifting a morphism `f` by `n` is obtained by the notation `f⟦n⟧'` -/
notation f "⟦" n "⟧'" => (shiftFunctor _ n).map f

variable (C)

lemma shiftFunctorAdd'_zero_add (a : A) :
  shiftFunctorAdd' C 0 a a (zero_add a) = (Functor.leftUnitor _).symm ≪≫
    isoWhiskerRight (shiftFunctorZero C A).symm (shiftFunctor C a) := by
  ext X
  dsimp [shiftFunctorAdd', shiftFunctorZero, shiftFunctor]
  simp only [eqToHom_app, obj_ε_app, Discrete.addMonoidal_leftUnitor, eqToIso.inv,
    eqToHom_map, Category.id_comp]
  rfl

lemma shiftFunctorAdd'_add_zero (a : A) :
  shiftFunctorAdd' C a 0 a (add_zero a) = (Functor.rightUnitor _).symm ≪≫
    isoWhiskerLeft (shiftFunctor C a) (shiftFunctorZero C A).symm := by
  ext
  dsimp [shiftFunctorAdd', shiftFunctorZero, shiftFunctor]
  simp only [eqToHom_app, ε_app_obj, Discrete.addMonoidal_rightUnitor, eqToIso.inv,
    eqToHom_map, Category.id_comp]
  rfl

lemma shiftFunctorAdd'_assoc (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h₁₂₃ : a₁ + a₂ + a₃ = a₁₂₃) :
    shiftFunctorAdd' C a₁₂ a₃ a₁₂₃ (by rw [← h₁₂, h₁₂₃]) ≪≫
      isoWhiskerRight (shiftFunctorAdd' C a₁ a₂ a₁₂ h₁₂) _ ≪≫ Functor.associator _ _ _  =
    shiftFunctorAdd' C a₁ a₂₃ a₁₂₃ (by rw [← h₂₃, ← add_assoc, h₁₂₃]) ≪≫
      isoWhiskerLeft _ (shiftFunctorAdd' C a₂ a₃ a₂₃ h₂₃) := by
  subst h₁₂ h₂₃ h₁₂₃
  ext X
  dsimp
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, Category.comp_id]
  dsimp [shiftFunctorAdd']
  simp only [eqToHom_app]
  dsimp [shiftFunctorAdd, shiftFunctor]
  simp only [obj_μ_inv_app, Discrete.addMonoidal_associator, eqToIso.hom, eqToHom_map,
    eqToHom_app]
  erw [Iso.inv_hom_id_app_assoc, Category.assoc]
  rfl

variable {C}

lemma shiftFunctorAdd'_zero_add_hom (a : A) (X : C) :
  (shiftFunctorAdd' C 0 a a (zero_add a)).hom.app X =
    ((shiftFunctorZero C A).inv.app X)⟦a⟧' := by
  simpa using NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorAdd'_zero_add C a)) X

lemma shiftFunctorAdd'_zero_add_inv (a : A) (X : C) :
  (shiftFunctorAdd' C 0 a a (zero_add a)).inv.app X =
    ((shiftFunctorZero C A).hom.app X)⟦a⟧' := by
  simpa using NatTrans.congr_app (congr_arg Iso.inv (shiftFunctorAdd'_zero_add C a)) X

lemma shiftFunctorAdd'_add_zero_hom (a : A) (X : C):
  (shiftFunctorAdd' C a 0 a (add_zero a)).hom.app X =
    (shiftFunctorZero C A).inv.app (X⟦a⟧) := by
  simpa using NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorAdd'_add_zero C a)) X

lemma shiftFunctorAdd'_add_zero_inv (a : A) (X : C):
  (shiftFunctorAdd' C a 0 a (add_zero a)).inv.app X =
    (shiftFunctorZero C A).hom.app (X⟦a⟧) := by
  simpa using NatTrans.congr_app (congr_arg Iso.inv (shiftFunctorAdd'_add_zero C a)) X

lemma shiftFunctorAdd'_assoc_hom (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h₁₂₃ : a₁ + a₂ + a₃ = a₁₂₃) (X : C) :
    (shiftFunctorAdd' C a₁₂ a₃ a₁₂₃ (by rw [← h₁₂, h₁₂₃])).hom.app X ≫
      ((shiftFunctorAdd' C a₁ a₂ a₁₂ h₁₂).hom.app X)⟦a₃⟧' =
    (shiftFunctorAdd' C a₁ a₂₃ a₁₂₃ (by rw [← h₂₃, ← add_assoc, h₁₂₃])).hom.app X ≫
      (shiftFunctorAdd' C a₂ a₃ a₂₃ h₂₃).hom.app (X⟦a₁⟧) := by
  simpa using NatTrans.congr_app (congr_arg Iso.hom
    (shiftFunctorAdd'_assoc C _ _ _ _ _ _ h₁₂ h₂₃ h₁₂₃)) X

lemma shiftFunctorAdd'_assoc_inv (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h₁₂₃ : a₁ + a₂ + a₃ = a₁₂₃) (X : C) :
    ((shiftFunctorAdd' C a₁ a₂ a₁₂ h₁₂).inv.app X)⟦a₃⟧' ≫
      (shiftFunctorAdd' C a₁₂ a₃ a₁₂₃ (by rw [← h₁₂, h₁₂₃])).inv.app X =
    (shiftFunctorAdd' C a₂ a₃ a₂₃ h₂₃).inv.app (X⟦a₁⟧) ≫
      (shiftFunctorAdd' C a₁ a₂₃ a₁₂₃ (by rw [← h₂₃, ← add_assoc, h₁₂₃])).inv.app X := by
  simpa using NatTrans.congr_app (congr_arg Iso.inv
    (shiftFunctorAdd'_assoc C _ _ _ _ _ _ h₁₂ h₂₃ h₁₂₃)) X

end Defs

section AddMonoid

variable [AddMonoid A] [HasShift C A] (X Y : C) (f : X ⟶ Y)

@[simp]
theorem HasShift.shift_obj_obj (n : A) (X : C) : (HasShift.shift.obj ⟨n⟩).obj X = X⟦n⟧ :=
  rfl
#align category_theory.has_shift.shift_obj_obj CategoryTheory.HasShift.shift_obj_obj

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
abbrev shiftAdd (i j : A) : X⟦i + j⟧ ≅ X⟦i⟧⟦j⟧ :=
  (shiftFunctorAdd C i j).app _
#align category_theory.shift_add CategoryTheory.shiftAdd

@[reassoc]
theorem shiftAdd_hom_comp_eqToHom₁ (i i' j : A) (h : i = i') :
    (shiftAdd X i j).hom ≫ eqToHom (by rw [h]) = eqToHom (by rw [h]) ≫ (shiftAdd X i' j).hom := by
  cases h
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
#align category_theory.shift_add_hom_comp_eq_to_hom₁ CategoryTheory.shiftAdd_hom_comp_eqToHom₁

@[reassoc]
theorem shiftAdd_hom_comp_eqToHom₂ (i j j' : A) (h : j = j') :
    (shiftAdd X i j).hom ≫ eqToHom (by rw [h]) = eqToHom (by rw [h]) ≫ (shiftAdd X i j').hom := by
  cases h
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
#align category_theory.shift_add_hom_comp_eq_to_hom₂ CategoryTheory.shiftAdd_hom_comp_eqToHom₂

@[reassoc]
theorem shiftAdd_hom_comp_eqToHom₁₂ (i j i' j' : A) (h₁ : i = i') (h₂ : j = j') :
    (shiftAdd X i j).hom ≫ eqToHom (by rw [h₁, h₂]) =
      eqToHom (by rw [h₁, h₂]) ≫ (shiftAdd X i' j').hom := by
  cases h₁
  cases h₂
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
#align category_theory.shift_add_hom_comp_eq_to_hom₁₂ CategoryTheory.shiftAdd_hom_comp_eqToHom₁₂

@[reassoc]
theorem eqToHom_comp_shiftAdd_inv₁ (i i' j : A) (h : i = i') :
    eqToHom (by rw [h]) ≫ (shiftAdd X i' j).inv = (shiftAdd X i j).inv ≫ eqToHom (by rw [h]) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, shiftAdd_hom_comp_eqToHom₁ _ _ _ _ h]
#align category_theory.eq_to_hom_comp_shift_add_inv₁ CategoryTheory.eqToHom_comp_shiftAdd_inv₁

@[reassoc]
theorem eqToHom_comp_shiftAdd_inv₂ (i j j' : A) (h : j = j') :
    eqToHom (by rw [h]) ≫ (shiftAdd X i j').inv = (shiftAdd X i j).inv ≫ eqToHom (by rw [h]) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, shiftAdd_hom_comp_eqToHom₂ _ _ _ _ h]
#align category_theory.eq_to_hom_comp_shift_add_inv₂ CategoryTheory.eqToHom_comp_shiftAdd_inv₂

@[reassoc]
theorem eqToHom_comp_shiftAdd_inv₁₂ (i j i' j' : A) (h₁ : i = i') (h₂ : j = j') :
    eqToHom (by rw [h₁, h₂]) ≫ (shiftAdd X i' j').inv =
      (shiftAdd X i j).inv ≫ eqToHom (by rw [h₁, h₂]) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, shiftAdd_hom_comp_eqToHom₁₂ _ _ _ _ _ h₁ h₂]
#align category_theory.eq_to_hom_comp_shift_add_inv₁₂ CategoryTheory.eqToHom_comp_shiftAdd_inv₁₂

theorem shift_shift' (i j : A) :
    f⟦i⟧'⟦j⟧' = (shiftAdd X i j).inv ≫ f⟦i + j⟧' ≫ (shiftAdd Y i j).hom := by
  symm
  apply NatIso.naturality_1
#align category_theory.shift_shift' CategoryTheory.shift_shift'

variable (A)

/-- Shifting by zero is the identity functor. -/
abbrev shiftZero : X⟦(0 : A)⟧ ≅ X :=
  (shiftFunctorZero C A).app _
#align category_theory.shift_zero CategoryTheory.shiftZero

theorem shift_zero' : f⟦(0 : A)⟧' = (shiftZero A X).hom ≫ f ≫ (shiftZero A Y).inv := by
  symm
  apply NatIso.naturality_2
#align category_theory.shift_zero' CategoryTheory.shift_zero'

variable (C) {A}

/-- When `i + j = 0`, shifting by `i` and by `j` gives the identity functor -/
def shiftFunctorCompIsoId (i j : A) (h : i + j = 0) :
    shiftFunctor C i ⋙ shiftFunctor C j ≅ 𝟭 C :=
  (shiftFunctorAdd' C i j 0 h).symm ≪≫ shiftFunctorZero C A

end AddMonoid

section AddGroup

variable (C)
variable [AddGroup A] [HasShift C A]

/-- Shifting by `n` and shifting by `-n` forms an equivalence. -/
@[simps]
def shiftEquiv (n : A) : C ≌ C where
  functor := shiftFunctor C n
  inverse := shiftFunctor C (-n)
  unitIso := (shiftFunctorCompIsoId C n (-n) (add_neg_self n)).symm
  counitIso := shiftFunctorCompIsoId C (-n) n (neg_add_self n)
  functor_unitIso_comp X := by
    convert (addNegEquiv (shiftMonoidalFunctor C A) n).functor_unitIso_comp X
    all_goals
      ext X
      dsimp [shiftFunctorCompIsoId, addNegEquiv, unitOfTensorIsoUnit,
        shiftFunctorAdd']
      simp only [Category.assoc, eqToHom_map]
      rfl
#align category_theory.shift_equiv CategoryTheory.shiftEquiv

variable (X Y : C) (f : X ⟶ Y)

/-- Shifting by `i` is an equivalence. -/
instance (i : A) : IsEquivalence (shiftFunctor C i) := by
  change IsEquivalence (shiftEquiv C i).functor
  infer_instance

@[simp]
theorem shiftFunctor_inv (i : A) : (shiftFunctor C i).inv = shiftFunctor C (-i) :=
  rfl
#align category_theory.shift_functor_inv CategoryTheory.shiftFunctor_inv

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
abbrev shiftFunctorCompShiftFunctorNeg (i : A) : shiftFunctor C i ⋙ shiftFunctor C (-i) ≅ 𝟭 C :=
  shiftFunctorCompIsoId C i (-i) (add_neg_self i)
#align category_theory.shift_functor_comp_shift_functor_neg CategoryTheory.shiftFunctorCompShiftFunctorNeg

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
abbrev shiftFunctorNegCompShiftFunctor (i : A) : shiftFunctor C (-i) ⋙ shiftFunctor C i ≅ 𝟭 C :=
  shiftFunctorCompIsoId C (-i) i (neg_add_self i)
#align category_theory.shift_functor_neg_comp_shift_functor CategoryTheory.shiftFunctorNegCompShiftFunctor

section

/-- Shifting by `n` is a faithful functor. -/
instance shiftFunctor_faithful (i : A) : Faithful (shiftFunctor C i) :=
  Faithful.of_comp_iso (shiftFunctorCompShiftFunctorNeg C i)
#align category_theory.shift_functor_faithful CategoryTheory.shiftFunctor_faithful

/-- Shifting by `n` is a full functor. -/
instance shiftFunctorFull (i : A) : Full (shiftFunctor C i) :=
  haveI : Full (shiftFunctor C i ⋙ shiftFunctor C (-i)) :=
    Full.ofIso (shiftFunctorCompShiftFunctorNeg C i).symm
  Full.ofCompFaithful _ (shiftFunctor C (-i))
#align category_theory.shift_functor_full CategoryTheory.shiftFunctorFull

/-- Shifting by `n` is an essentially surjective functor. -/
instance shiftFunctor_essSurj (i : A) : EssSurj (shiftFunctor C i)
    where mem_essImage Y := ⟨Y⟦-i⟧, ⟨(shiftFunctorNegCompShiftFunctor C i).app Y⟩⟩
#align category_theory.shift_functor_ess_surj CategoryTheory.shiftFunctor_essSurj

end

variable {C}

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
abbrev shiftShiftNeg (i : A) : X⟦i⟧⟦-i⟧ ≅ X :=
  (shiftFunctorCompShiftFunctorNeg C i).app _
#align category_theory.shift_shift_neg CategoryTheory.shiftShiftNeg

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
abbrev shiftNegShift (i : A) : X⟦-i⟧⟦i⟧ ≅ X :=
  (shiftFunctorNegCompShiftFunctor C i).app _
#align category_theory.shift_neg_shift CategoryTheory.shiftNegShift

variable {X Y}

theorem shift_shift_neg' (i : A) :
    f⟦i⟧'⟦-i⟧' = (shiftFunctorCompShiftFunctorNeg C i).hom.app X ≫
      f ≫ (shiftFunctorCompShiftFunctorNeg C i).inv.app Y :=
  (NatIso.naturality_2 (shiftFunctorCompShiftFunctorNeg C i) f).symm
#align category_theory.shift_shift_neg' CategoryTheory.shift_shift_neg'

theorem shift_neg_shift' (i : A) :
    f⟦-i⟧'⟦i⟧' = (shiftFunctorNegCompShiftFunctor C i).hom.app X ≫ f ≫
      (shiftFunctorNegCompShiftFunctor C i).inv.app Y :=
  (NatIso.naturality_2 (shiftFunctorNegCompShiftFunctor C i) f).symm
#align category_theory.shift_neg_shift' CategoryTheory.shift_neg_shift'

theorem shift_equiv_triangle (n : A) (X : C) :
    (shiftShiftNeg X n).inv⟦n⟧' ≫ (shiftNegShift (X⟦n⟧) n).hom = 𝟙 (X⟦n⟧) :=
  (shiftEquiv C n).functor_unitIso_comp X
#align category_theory.shift_equiv_triangle CategoryTheory.shift_equiv_triangle

section

theorem shift_shiftFunctorCompIsoId_hom (n m : A) (h : n + m = 0) (X : C) :
  ((shiftFunctorCompIsoId C n m h).hom.app X)⟦n⟧' =
    ((shiftFunctorCompIsoId C m n
      (by rw [← neg_eq_of_add_eq_zero_left h, add_right_neg])).hom.app (X⟦n⟧)) := by
  dsimp [shiftFunctorCompIsoId]
  simpa only [Functor.map_comp, ← shiftFunctorAdd'_zero_add_inv n X,
    ← shiftFunctorAdd'_add_zero_inv n X]
    using shiftFunctorAdd'_assoc_inv n m n 0 0 n h
      (by rw [← neg_eq_of_add_eq_zero_left h, add_right_neg]) (by rw [h, zero_add]) X

theorem shift_shiftFunctorCompIsoId_inv (n m : A) (h : n + m = 0) (X : C) :
  ((shiftFunctorCompIsoId C n m h).inv.app X)⟦n⟧' =
    ((shiftFunctorCompIsoId C m n
      (by rw [← neg_eq_of_add_eq_zero_left h, add_right_neg])).inv.app (X⟦n⟧)) := by
  rw [← cancel_mono (((shiftFunctorCompIsoId C n m h).hom.app X)⟦n⟧'),
    ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id,
    shift_shiftFunctorCompIsoId_hom, Iso.inv_hom_id_app]
  rfl

theorem shiftShiftNeg_hom_shift (n : A) (X : C) :
    (shiftShiftNeg X n).hom⟦n⟧' = (shiftNegShift (X⟦n⟧) n).hom :=
  shift_shiftFunctorCompIsoId_hom n (-n) (add_neg_self n) X
#align category_theory.shift_shift_neg_hom_shift CategoryTheory.shiftShiftNeg_hom_shift

theorem shiftShiftNeg_inv_shift (n : A) (X : C) :
    (shiftShiftNeg X n).inv⟦n⟧' = (shiftNegShift (X⟦n⟧) n).inv := by
  apply Iso.inv_ext'
  rw [← shiftShiftNeg_hom_shift, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id]
#align category_theory.shift_shift_neg_inv_shift CategoryTheory.shiftShiftNeg_inv_shift

theorem shiftFunctorCompShiftFunctorNeg_inv_app_shift (n : A) (X : C) :
    ((shiftFunctorCompShiftFunctorNeg C n).inv.app X)⟦n⟧' =
      (shiftFunctorNegCompShiftFunctor C n).inv.app (X⟦n⟧) :=
  shiftShiftNeg_inv_shift n X

theorem shiftFunctorCompShiftFunctorNeg_hom_app_shift (n : A) (X : C) :
    ((shiftFunctorCompShiftFunctorNeg C n).hom.app X)⟦n⟧' =
      (shiftFunctorNegCompShiftFunctor C n).hom.app (X⟦n⟧) :=
  shiftShiftNeg_hom_shift n X

@[simp]
theorem shiftShiftNeg_shift_eq (n : A) (X : C) :
    (shiftFunctor C n).mapIso (shiftShiftNeg X n) = shiftNegShift (X⟦n⟧) n :=
  CategoryTheory.Iso.ext <| shiftShiftNeg_hom_shift _ _
#align category_theory.shift_shift_neg_shift_eq CategoryTheory.shiftShiftNeg_shift_eq

end

open CategoryTheory.Limits

variable [HasZeroMorphisms C]

theorem shift_zero_eq_zero (X Y : C) (n : A) : (0 : X ⟶ Y)⟦n⟧' = (0 : X⟦n⟧ ⟶ Y⟦n⟧) :=
  CategoryTheory.Functor.map_zero _ _ _
#align category_theory.shift_zero_eq_zero CategoryTheory.shift_zero_eq_zero

end AddGroup

section AddCommMonoid

variable [AddCommMonoid A] [HasShift C A]

variable (C)

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
def shiftFunctorComm (i j : A) :
    shiftFunctor C i ⋙ shiftFunctor C j ≅
      shiftFunctor C j ⋙ shiftFunctor C i :=
  (shiftFunctorAdd C i j).symm ≪≫ shiftFunctorAdd' C j i (i + j) (add_comm j i)

lemma shiftFunctorComm_eq (i j k : A) (h : i + j = k):
    shiftFunctorComm C i j = (shiftFunctorAdd' C i j k h).symm ≪≫
      shiftFunctorAdd' C j i k (by rw [add_comm j i, h]) := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]
  rfl

lemma shiftFunctorComm_symm (i j : A) :
  (shiftFunctorComm C i j).symm = shiftFunctorComm C j i := by
  ext1
  dsimp
  rw [shiftFunctorComm_eq C i j (i+j) rfl, shiftFunctorComm_eq C j i (i+j) (add_comm j i)]
  rfl

variable {C}

variable (X Y : C) (f : X ⟶ Y)

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
abbrev shiftComm (i j : A) : X⟦i⟧⟦j⟧ ≅ X⟦j⟧⟦i⟧ :=
  (shiftFunctorComm C i j).app X
#align category_theory.shift_comm CategoryTheory.shiftComm

@[simp]
theorem shiftComm_symm (i j : A) : (shiftComm X i j).symm = shiftComm X j i := by
  ext
  exact NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorComm_symm C i j)) X
#align category_theory.shift_comm_symm CategoryTheory.shiftComm_symm

variable {X Y}

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
theorem shift_comm' (i j : A) :
    f⟦i⟧'⟦j⟧' = (shiftComm _ _ _).hom ≫ f⟦j⟧'⟦i⟧' ≫ (shiftComm _ _ _).hom := by
  erw [← shiftComm_symm Y i j, ← ((shiftFunctorComm C i j).hom.naturality_assoc f)]
  dsimp
  simp only [Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
#align category_theory.shift_comm' CategoryTheory.shift_comm'

@[reassoc]
theorem shiftComm_hom_comp (i j : A) :
    (shiftComm X i j).hom ≫ f⟦j⟧'⟦i⟧' = f⟦i⟧'⟦j⟧' ≫ (shiftComm Y i j).hom := by
  rw [shift_comm', ← shiftComm_symm, Iso.symm_hom, Iso.inv_hom_id_assoc]
#align category_theory.shift_comm_hom_comp CategoryTheory.shiftComm_hom_comp

end AddCommMonoid

variable {D : Type _} [Category D] [AddMonoid A] [HasShift D A]

variable (F : C ⥤ D) [Full F] [Faithful F]

section

--attribute [local reducible] Discrete.addMonoidal

variable (s : A → C ⥤ C) (i : ∀ i, s i ⋙ F ≅ F ⋙ shiftFunctor D i)

-- porting note: the fields `ε` and `μ` in the definition of `hasShiftOfFullyFaithful` have
-- been defined separately as `hasShiftOfFullyFaithful_μ` and `hasShiftOfFullyFaithful_ε`
-- with suitable simplifications lemmas, in order to ease the port and future use

/-- auxiliary definition for `hasShiftOfFullyFaithful` -/
def hasShiftOfFullyFaithful_ε : 𝟭 C ≅ s 0 :=
  natIsoOfCompFullyFaithful F
    (calc
      𝟭 C ⋙ F ≅ F := Functor.leftUnitor _
      _ ≅ F ⋙ 𝟭 D := (Functor.rightUnitor _).symm
      _ ≅ F ⋙ shiftFunctor D (0 : A) := (isoWhiskerLeft F (shiftFunctorZero D A).symm)
      _ ≅ s 0 ⋙ F := (i 0).symm)

@[simp]
lemma map_hasShiftOfFullyFaithful_ε_hom_app (X : C) :
    F.map ((hasShiftOfFullyFaithful_ε F s i).hom.app X) =
      (shiftFunctorZero D A).inv.app (F.obj X) ≫ (i 0).inv.app X := by
  simp [hasShiftOfFullyFaithful_ε]

@[simp]
lemma map_hasShiftOfFullyFaithful_ε_inv_app (X : C) :
    F.map ((hasShiftOfFullyFaithful_ε F s i).inv.app X) =
      (i 0).hom.app X ≫ (shiftFunctorZero D A).hom.app (F.obj X) := by
  simp [hasShiftOfFullyFaithful_ε]

/-- auxiliary definition for `hasShiftOfFullyFaithful` -/
def hasShiftOfFullyFaithful_μ (a b : A) : s a ⋙ s b ≅ s (a + b) :=
  natIsoOfCompFullyFaithful F
    (calc
      (s a ⋙ s b) ⋙ F ≅ s a ⋙ s b ⋙ F := Functor.associator _ _ _
      _ ≅ s a ⋙ F ⋙ shiftFunctor D b := (isoWhiskerLeft _ (i b))
      _ ≅ (s a ⋙ F) ⋙ shiftFunctor D b := (Functor.associator _ _ _).symm
      _ ≅ (F ⋙ shiftFunctor D a) ⋙ shiftFunctor D b := (isoWhiskerRight (i a) _)
      _ ≅ F ⋙ shiftFunctor D a ⋙ shiftFunctor D b := (Functor.associator _ _ _)
      _ ≅ F ⋙ shiftFunctor D (a + b) := (isoWhiskerLeft _ (shiftFunctorAdd D a b).symm)
      _ ≅ s (a + b) ⋙ F := (i (a + b)).symm)

@[simp]
lemma map_hasShiftOfFullyFaithful_μ_hom_app (a b : A) (X : C) :
    F.map ((hasShiftOfFullyFaithful_μ F s i a b).hom.app X) =
      (i b).hom.app ((s a).obj X) ≫ ((i a).hom.app X)⟦b⟧' ≫
        (shiftFunctorAdd D a b).inv.app (F.obj X) ≫ (i (a + b)).inv.app X  := by
  dsimp [hasShiftOfFullyFaithful_μ]
  simp

@[simp]
lemma map_hasShiftOfFullyFaithful_μ_inv_app (a b : A) (X : C) :
    F.map ((hasShiftOfFullyFaithful_μ F s i a b).inv.app X) =
      (i (a + b)).hom.app X ≫ (shiftFunctorAdd D a b).hom.app (F.obj X) ≫
        ((i a).inv.app X)⟦b⟧' ≫ (i b).inv.app ((s a).obj X) := by
  dsimp [hasShiftOfFullyFaithful_μ]
  simp

/-- Given a family of endomorphisms of `C` which are interwined by a fully faithful `F : C ⥤ D`
with shift functors on `D`, we can promote that family to shift functors on `C`. -/
def hasShiftOfFullyFaithful :
    HasShift C A :=
  hasShiftMk C A
    { F := s
      ε := hasShiftOfFullyFaithful_ε F s i
      μ := hasShiftOfFullyFaithful_μ F s i
      associativity := fun m₁ m₂ m₃ X => F.map_injective (by
        have h := shiftFunctorAdd'_assoc_inv m₁ m₂ m₃ _ _ _ rfl rfl rfl (F.obj X)
        simp only [shiftFunctorAdd'_eq_shiftFunctorAdd] at h
        simp only [F.map_comp, map_hasShiftOfFullyFaithful_μ_hom_app, Category.assoc,
          Iso.inv_hom_id_app_assoc]
        erw [(i m₃).hom.naturality_assoc]
        dsimp
        simp only [map_hasShiftOfFullyFaithful_μ_hom_app, ← Functor.map_comp_assoc,
          Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
        simp only [Functor.map_comp, Category.assoc]
        erw [Functor.map_id, Category.id_comp, ← NatTrans.naturality_assoc,
          dcongr_arg (fun a => (i a).inv.app X) (add_assoc m₁ m₂ m₃)]
        slice_lhs 4 5 => rw [h]
        dsimp [shiftFunctorAdd']
        simp only [Category.assoc, eqToHom_map, eqToHom_app, eqToHom_trans, eqToHom_refl,
          Category.comp_id, eqToHom_trans_assoc, Category.id_comp])
      left_unitality := fun n X => F.map_injective (by
        erw [Functor.map_comp, map_hasShiftOfFullyFaithful_μ_hom_app, (i n).hom.naturality_assoc]
        dsimp
        simp only [map_hasShiftOfFullyFaithful_ε_hom_app, Functor.map_comp]
        rw [← shiftFunctorAdd'_zero_add_hom n (F.obj X)]
        simp only [Category.assoc, ← (shiftFunctor D n).map_comp_assoc, Iso.inv_hom_id_app]
        dsimp [shiftFunctorAdd']
        simp only [Functor.map_id, Category.id_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
        rw [dcongr_arg (fun a => (i a).inv.app X) (zero_add n)]
        simp only [eqToHom_app, Functor.comp_obj, eqToHom_trans_assoc,
          eqToHom_refl, Category.id_comp, Iso.hom_inv_id_app_assoc, eqToHom_map])
      right_unitality := fun n X => F.map_injective (by
        have := dcongr_arg (fun a => (i a).inv.app X) (add_zero n)
        simp only [Functor.id_obj, Functor.map_comp, map_hasShiftOfFullyFaithful_ε_hom_app,
          Functor.comp_obj, map_hasShiftOfFullyFaithful_μ_hom_app, Category.assoc,
          Iso.inv_hom_id_app_assoc, this, ← NatTrans.naturality_assoc,
          ← shiftFunctorAdd'_add_zero_hom n]
        dsimp [shiftFunctorAdd']
        simp only [Category.assoc, Iso.hom_inv_id_app_assoc, eqToHom_app, eqToHom_trans_assoc,
          eqToHom_refl, Category.id_comp, eqToHom_map]) }
#align category_theory.has_shift_of_fully_faithful CategoryTheory.hasShiftOfFullyFaithful

end

/-- When we construct shifts on a subcategory from shifts on the ambient category,
the inclusion functor intertwines the shifts. -/
def hasShiftOfFullyFaithfulComm (s : A → C ⥤ C) (i : ∀ i, s i ⋙ F ≅ F ⋙ shiftFunctor D i)
  (m : A) :
    haveI := hasShiftOfFullyFaithful F s i
    shiftFunctor C m ⋙ F ≅ F ⋙ shiftFunctor D m :=
  i m
#align category_theory.has_shift_of_fully_faithful_comm CategoryTheory.hasShiftOfFullyFaithfulComm

end

end CategoryTheory
