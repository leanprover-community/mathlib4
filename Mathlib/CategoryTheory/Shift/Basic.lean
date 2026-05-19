/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin, Andrew Yang, Joël Riou
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Monoidal.End
public import Mathlib.CategoryTheory.Monoidal.Discrete

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
  a self-equivalence of `C`.
* `shiftComm`: When the indexing monoid is commutative, then shifts commute as well.

## Implementation Notes

`[HasShift C A]` is implemented using monoidal functors from `Discrete A` to `C ⥤ C`.
However, the API of monoidal functors is used only internally: one should use the API of
shift functors which includes `shiftFunctor C a : C ⥤ C` for `a : A`,
`shiftFunctorZero C A : shiftFunctor C (0 : A) ≅ 𝟭 C` and
`shiftFunctorAdd C i j : shiftFunctor C (i + j) ≅ shiftFunctor C i ⋙ shiftFunctor C j`
(and its variant `shiftFunctorAdd'`). These isomorphisms satisfy some coherence properties
which are stated in lemmas like `shiftFunctorAdd'_assoc`, `shiftFunctorAdd'_zero_add` and
`shiftFunctorAdd'_add_zero`.

-/

@[expose] public section


namespace CategoryTheory

open Functor

noncomputable section

universe v u

variable (C : Type u) (A : Type*) [Category.{v} C]

attribute [local instance] endofunctorMonoidalCategory

variable {A C}

section Defs

variable (A C) [AddMonoid A]

/-- A category has a shift indexed by an additive monoid `A`
if there is a monoidal functor from `A` to `C ⥤ C`. -/
class HasShift (C : Type u) (A : Type*) [Category.{v} C] [AddMonoid A] where
  /-- a shift is a monoidal functor from `A` to `C ⥤ C` -/
  shift : Discrete A ⥤ C ⥤ C
  /-- `shift` is monoidal -/
  shiftMonoidal : shift.Monoidal := by infer_instance

/-- A helper structure to construct the shift functor `(Discrete A) ⥤ (C ⥤ C)`. -/
structure ShiftMkCore where
  /-- the family of shift functors -/
  F : A → C ⥤ C
  /-- the shift by 0 identifies to the identity functor -/
  zero : F 0 ≅ 𝟭 C
  /-- the composition of shift functors identifies to the shift by the sum -/
  add : ∀ n m : A, F (n + m) ≅ F n ⋙ F m
  /-- compatibility with the associativity -/
  assoc_hom_app : ∀ (m₁ m₂ m₃ : A) (X : C),
    (add (m₁ + m₂) m₃).hom.app X ≫ (F m₃).map ((add m₁ m₂).hom.app X) =
      eqToHom (by rw [add_assoc]) ≫ (add m₁ (m₂ + m₃)).hom.app X ≫
        (add m₂ m₃).hom.app ((F m₁).obj X) := by cat_disch
  /-- compatibility with the left addition with 0 -/
  zero_add_hom_app : ∀ (n : A) (X : C), (add 0 n).hom.app X =
    eqToHom (by dsimp; rw [zero_add]) ≫ (F n).map (zero.inv.app X) := by cat_disch
  /-- compatibility with the right addition with 0 -/
  add_zero_hom_app : ∀ (n : A) (X : C), (add n 0).hom.app X =
    eqToHom (by dsimp; rw [add_zero]) ≫ zero.inv.app ((F n).obj X) := by cat_disch

namespace ShiftMkCore

variable {C A}

attribute [reassoc] assoc_hom_app

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma assoc_inv_app (h : ShiftMkCore C A) (m₁ m₂ m₃ : A) (X : C) :
    (h.F m₃).map ((h.add m₁ m₂).inv.app X) ≫ (h.add (m₁ + m₂) m₃).inv.app X =
    (h.add m₂ m₃).inv.app ((h.F m₁).obj X) ≫ (h.add m₁ (m₂ + m₃)).inv.app X ≫
      eqToHom (by rw [add_assoc]) := by
  rw [← cancel_mono ((h.add (m₁ + m₂) m₃).hom.app X ≫ (h.F m₃).map ((h.add m₁ m₂).hom.app X)),
    Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app, Functor.map_id, h.assoc_hom_app, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma zero_add_inv_app (h : ShiftMkCore C A) (n : A) (X : C) :
    (h.add 0 n).inv.app X = (h.F n).map (h.zero.hom.app X) ≫
      eqToHom (by dsimp; rw [zero_add]) := by
  rw [← cancel_epi ((h.add 0 n).hom.app X), Iso.hom_inv_id_app, h.zero_add_hom_app,
    Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp, eqToHom_trans, eqToHom_refl]

set_option backward.isDefEq.respectTransparency false in
lemma add_zero_inv_app (h : ShiftMkCore C A) (n : A) (X : C) :
    (h.add n 0).inv.app X = h.zero.hom.app ((h.F n).obj X) ≫
      eqToHom (by dsimp; rw [add_zero]) := by
  rw [← cancel_epi ((h.add n 0).hom.app X), Iso.hom_inv_id_app, h.add_zero_hom_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, eqToHom_trans, eqToHom_refl]

end ShiftMkCore

section

attribute [local simp] eqToHom_map

set_option backward.isDefEq.respectTransparency false in
instance (h : ShiftMkCore C A) : (Discrete.functor h.F).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := h.zero.symm
      μIso := fun m n ↦ (h.add m.as n.as).symm
      μIso_hom_natural_left := by
        rintro ⟨X⟩ ⟨Y⟩ ⟨⟨⟨rfl⟩⟩⟩ ⟨X'⟩
        ext
        simp
      μIso_hom_natural_right := by
        rintro ⟨X⟩ ⟨Y⟩ ⟨X'⟩ ⟨⟨⟨rfl⟩⟩⟩
        ext
        simp
      associativity := by
        rintro ⟨m₁⟩ ⟨m₂⟩ ⟨m₃⟩
        ext X
        simp [h.assoc_inv_app_assoc]
      left_unitality := by
        rintro ⟨n⟩
        ext X
        simp [h.zero_add_inv_app, ← Functor.map_comp]
      right_unitality := by
        rintro ⟨n⟩
        ext X
        simp [h.add_zero_inv_app] }

/-- Constructs a `HasShift C A` instance from `ShiftMkCore`. -/
@[implicit_reducible]
def hasShiftMk (h : ShiftMkCore C A) : HasShift C A where
  shift := Discrete.functor h.F

end

section
variable [HasShift C A]

/-- The monoidal functor from `A` to `C ⥤ C` given a `HasShift` instance. -/
def shiftMonoidalFunctor : Discrete A ⥤ C ⥤ C :=
  HasShift.shift

instance : (shiftMonoidalFunctor C A).Monoidal := HasShift.shiftMonoidal

variable {A}

open Functor.Monoidal

/-- The shift autoequivalence, moving objects and morphisms 'up'. -/
def shiftFunctor (i : A) : C ⥤ C :=
  (shiftMonoidalFunctor C A).obj ⟨i⟩

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
def shiftFunctorAdd (i j : A) : shiftFunctor C (i + j) ≅ shiftFunctor C i ⋙ shiftFunctor C j :=
  (μIso (shiftMonoidalFunctor C A) ⟨i⟩ ⟨j⟩).symm

/-- When `k = i + j`, shifting by `k` is the same as shifting by `i` and then shifting by `j`. -/
def shiftFunctorAdd' (i j k : A) (h : i + j = k) :
    shiftFunctor C k ≅ shiftFunctor C i ⋙ shiftFunctor C j :=
  eqToIso (by rw [h]) ≪≫ shiftFunctorAdd C i j

lemma shiftFunctorAdd'_eq_shiftFunctorAdd (i j : A) :
    shiftFunctorAdd' C i j (i + j) rfl = shiftFunctorAdd C i j := by
  ext1
  apply Category.id_comp

variable (A) in
/-- Shifting by zero is the identity functor. -/
def shiftFunctorZero : shiftFunctor C (0 : A) ≅ 𝟭 C :=
  (εIso (shiftMonoidalFunctor C A)).symm

/-- Shifting by `a` such that `a = 0` identifies to the identity functor. -/
def shiftFunctorZero' (a : A) (ha : a = 0) : shiftFunctor C a ≅ 𝟭 C :=
  eqToIso (by rw [ha]) ≪≫ shiftFunctorZero C A

end

variable {C A}

lemma ShiftMkCore.shiftFunctor_eq (h : ShiftMkCore C A) (a : A) :
    letI := hasShiftMk C A h
    shiftFunctor C a = h.F a := rfl

lemma ShiftMkCore.shiftFunctorZero_eq (h : ShiftMkCore C A) :
    letI := hasShiftMk C A h
    shiftFunctorZero C A = h.zero := rfl

lemma ShiftMkCore.shiftFunctorAdd_eq (h : ShiftMkCore C A) (a b : A) :
    letI := hasShiftMk C A h
    shiftFunctorAdd C a b = h.add a b := rfl

set_option quotPrecheck false in
/-- shifting an object `X` by `n` is obtained by the notation `X⟦n⟧` -/
notation -- Any better notational suggestions?
X "⟦" n "⟧" => (shiftFunctor _ n).obj X

set_option quotPrecheck false in
/-- shifting a morphism `f` by `n` is obtained by the notation `f⟦n⟧'` -/
notation f "⟦" n "⟧'" => (shiftFunctor _ n).map f

variable (C)
variable [HasShift C A]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma shiftFunctorAdd'_zero_add (a : A) :
    shiftFunctorAdd' C 0 a a (zero_add a) = (leftUnitor _).symm ≪≫
    isoWhiskerRight (shiftFunctorZero C A).symm (shiftFunctor C a) := by
  ext X
  dsimp [shiftFunctorAdd', shiftFunctorZero, shiftFunctor]
  simp only [eqToHom_app, obj_ε_app, Discrete.addMonoidal_leftUnitor, eqToIso.inv,
    eqToHom_map, Category.id_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
lemma shiftFunctorAdd'_add_zero (a : A) :
    shiftFunctorAdd' C a 0 a (add_zero a) = (rightUnitor _).symm ≪≫
    isoWhiskerLeft (shiftFunctor C a) (shiftFunctorZero C A).symm := by
  ext
  dsimp [shiftFunctorAdd', shiftFunctorZero, shiftFunctor]
  simp only [eqToHom_app, ε_app_obj, Discrete.addMonoidal_rightUnitor, eqToIso.inv,
    eqToHom_map, Category.id_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma shiftFunctorAdd'_assoc (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h₁₂₃ : a₁ + a₂ + a₃ = a₁₂₃) :
    shiftFunctorAdd' C a₁₂ a₃ a₁₂₃ (by rw [← h₁₂, h₁₂₃]) ≪≫
      isoWhiskerRight (shiftFunctorAdd' C a₁ a₂ a₁₂ h₁₂) _ ≪≫ associator _ _ _ =
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
  erw [δ_μ_app_assoc, Category.assoc]
  rfl

lemma shiftFunctorAdd_assoc (a₁ a₂ a₃ : A) :
    shiftFunctorAdd C (a₁ + a₂) a₃ ≪≫
      isoWhiskerRight (shiftFunctorAdd C a₁ a₂) _ ≪≫ associator _ _ _ =
    shiftFunctorAdd' C a₁ (a₂ + a₃) _ (add_assoc a₁ a₂ a₃).symm ≪≫
      isoWhiskerLeft _ (shiftFunctorAdd C a₂ a₃) := by
  ext X
  simpa [shiftFunctorAdd'_eq_shiftFunctorAdd]
    using NatTrans.congr_app (congr_arg Iso.hom
      (shiftFunctorAdd'_assoc C a₁ a₂ a₃ _ _ _ rfl rfl rfl)) X

variable {C}

set_option backward.defeqAttrib.useBackward true in
lemma shiftFunctorAdd'_zero_add_hom_app (a : A) (X : C) :
    (shiftFunctorAdd' C 0 a a (zero_add a)).hom.app X =
    ((shiftFunctorZero C A).inv.app X)⟦a⟧' := by
  simpa using NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorAdd'_zero_add C a)) X

set_option backward.isDefEq.respectTransparency false in
lemma shiftFunctorAdd_zero_add_hom_app (a : A) (X : C) :
    (shiftFunctorAdd C 0 a).hom.app X =
    eqToHom (by dsimp; rw [zero_add]) ≫ ((shiftFunctorZero C A).inv.app X)⟦a⟧' := by
  simp [← shiftFunctorAdd'_zero_add_hom_app, shiftFunctorAdd']

set_option backward.defeqAttrib.useBackward true in
lemma shiftFunctorAdd'_zero_add_inv_app (a : A) (X : C) :
    (shiftFunctorAdd' C 0 a a (zero_add a)).inv.app X =
    ((shiftFunctorZero C A).hom.app X)⟦a⟧' := by
  simpa using NatTrans.congr_app (congr_arg Iso.inv (shiftFunctorAdd'_zero_add C a)) X

set_option backward.isDefEq.respectTransparency false in
lemma shiftFunctorAdd_zero_add_inv_app (a : A) (X : C) : (shiftFunctorAdd C 0 a).inv.app X =
    ((shiftFunctorZero C A).hom.app X)⟦a⟧' ≫ eqToHom (by dsimp; rw [zero_add]) := by
  simp [← shiftFunctorAdd'_zero_add_inv_app, shiftFunctorAdd']

set_option backward.defeqAttrib.useBackward true in
lemma shiftFunctorAdd'_add_zero_hom_app (a : A) (X : C) :
    (shiftFunctorAdd' C a 0 a (add_zero a)).hom.app X =
    (shiftFunctorZero C A).inv.app (X⟦a⟧) := by
  simpa using NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorAdd'_add_zero C a)) X

set_option backward.defeqAttrib.useBackward true in
lemma shiftFunctorAdd_add_zero_hom_app (a : A) (X : C) : (shiftFunctorAdd C a 0).hom.app X =
    eqToHom (by dsimp; rw [add_zero]) ≫ (shiftFunctorZero C A).inv.app (X⟦a⟧) := by
  simp [← shiftFunctorAdd'_add_zero_hom_app, shiftFunctorAdd']

set_option backward.defeqAttrib.useBackward true in
lemma shiftFunctorAdd'_add_zero_inv_app (a : A) (X : C) :
    (shiftFunctorAdd' C a 0 a (add_zero a)).inv.app X =
    (shiftFunctorZero C A).hom.app (X⟦a⟧) := by
  simpa using NatTrans.congr_app (congr_arg Iso.inv (shiftFunctorAdd'_add_zero C a)) X

set_option backward.defeqAttrib.useBackward true in
lemma shiftFunctorAdd_add_zero_inv_app (a : A) (X : C) : (shiftFunctorAdd C a 0).inv.app X =
    (shiftFunctorZero C A).hom.app (X⟦a⟧) ≫ eqToHom (by dsimp; rw [add_zero]) := by
  simp [← shiftFunctorAdd'_add_zero_inv_app, shiftFunctorAdd']

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma shiftFunctorAdd'_assoc_hom_app (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h₁₂₃ : a₁ + a₂ + a₃ = a₁₂₃) (X : C) :
    (shiftFunctorAdd' C a₁₂ a₃ a₁₂₃ (by rw [← h₁₂, h₁₂₃])).hom.app X ≫
      ((shiftFunctorAdd' C a₁ a₂ a₁₂ h₁₂).hom.app X)⟦a₃⟧' =
    (shiftFunctorAdd' C a₁ a₂₃ a₁₂₃ (by rw [← h₂₃, ← add_assoc, h₁₂₃])).hom.app X ≫
      (shiftFunctorAdd' C a₂ a₃ a₂₃ h₂₃).hom.app (X⟦a₁⟧) := by
  simpa using NatTrans.congr_app (congr_arg Iso.hom
    (shiftFunctorAdd'_assoc C _ _ _ _ _ _ h₁₂ h₂₃ h₁₂₃)) X

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma shiftFunctorAdd'_assoc_inv_app (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h₁₂₃ : a₁ + a₂ + a₃ = a₁₂₃) (X : C) :
    ((shiftFunctorAdd' C a₁ a₂ a₁₂ h₁₂).inv.app X)⟦a₃⟧' ≫
      (shiftFunctorAdd' C a₁₂ a₃ a₁₂₃ (by rw [← h₁₂, h₁₂₃])).inv.app X =
    (shiftFunctorAdd' C a₂ a₃ a₂₃ h₂₃).inv.app (X⟦a₁⟧) ≫
      (shiftFunctorAdd' C a₁ a₂₃ a₁₂₃ (by rw [← h₂₃, ← add_assoc, h₁₂₃])).inv.app X := by
  simpa using NatTrans.congr_app (congr_arg Iso.inv
    (shiftFunctorAdd'_assoc C _ _ _ _ _ _ h₁₂ h₂₃ h₁₂₃)) X

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma shiftFunctorAdd_assoc_hom_app (a₁ a₂ a₃ : A) (X : C) :
    (shiftFunctorAdd C (a₁ + a₂) a₃).hom.app X ≫
      ((shiftFunctorAdd C a₁ a₂).hom.app X)⟦a₃⟧' =
    (shiftFunctorAdd' C a₁ (a₂ + a₃) (a₁ + a₂ + a₃) (add_assoc _ _ _).symm).hom.app X ≫
      (shiftFunctorAdd C a₂ a₃).hom.app (X⟦a₁⟧) := by
  simpa using NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorAdd_assoc C a₁ a₂ a₃)) X

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma shiftFunctorAdd_assoc_inv_app (a₁ a₂ a₃ : A) (X : C) :
    ((shiftFunctorAdd C a₁ a₂).inv.app X)⟦a₃⟧' ≫
      (shiftFunctorAdd C (a₁ + a₂) a₃).inv.app X =
    (shiftFunctorAdd C a₂ a₃).inv.app (X⟦a₁⟧) ≫
      (shiftFunctorAdd' C a₁ (a₂ + a₃) (a₁ + a₂ + a₃) (add_assoc _ _ _).symm).inv.app X := by
  simpa using NatTrans.congr_app (congr_arg Iso.inv (shiftFunctorAdd_assoc C a₁ a₂ a₃)) X

end Defs

section AddMonoid

variable [AddMonoid A] [HasShift C A] (X Y : C) (f : X ⟶ Y)

--@[simp]
--theorem HasShift.shift_obj_obj (n : A) (X : C) : (HasShift.shift.obj ⟨n⟩).obj X = X⟦n⟧ :=
--  rfl

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
abbrev shiftAdd (i j : A) : X⟦i + j⟧ ≅ X⟦i⟧⟦j⟧ :=
  (shiftFunctorAdd C i j).app _

set_option backward.isDefEq.respectTransparency false in
theorem shift_shift' (i j : A) :
    f⟦i⟧'⟦j⟧' = (shiftAdd X i j).inv ≫ f⟦i + j⟧' ≫ (shiftAdd Y i j).hom := by
  simp

variable (A)

/-- Shifting by zero is the identity functor. -/
abbrev shiftZero : X⟦(0 : A)⟧ ≅ X :=
  (shiftFunctorZero C A).app _

theorem shiftZero' : f⟦(0 : A)⟧' = (shiftZero A X).hom ≫ f ≫ (shiftZero A Y).inv := by
  symm
  rw [Iso.app_inv, Iso.app_hom]
  apply NatIso.naturality_2

variable (C) {A}

/-- When `i + j = 0`, shifting by `i` and by `j` gives the identity functor -/
def shiftFunctorCompIsoId (i j : A) (h : i + j = 0) :
    shiftFunctor C i ⋙ shiftFunctor C j ≅ 𝟭 C :=
  (shiftFunctorAdd' C i j 0 h).symm ≪≫ shiftFunctorZero C A

end AddMonoid

section AddGroup

variable (C)
variable [AddGroup A] [HasShift C A]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Shifting by `i` and shifting by `j` forms an equivalence when `i + j = 0`. -/
@[simps]
def shiftEquiv' (i j : A) (h : i + j = 0) : C ≌ C where
  functor := shiftFunctor C i
  inverse := shiftFunctor C j
  unitIso := (shiftFunctorCompIsoId C i j h).symm
  counitIso := shiftFunctorCompIsoId C j i
    (by rw [← add_left_inj j, add_assoc, h, zero_add, add_zero])
  functor_unitIso_comp X := by
    convert (equivOfTensorIsoUnit (shiftMonoidalFunctor C A) ⟨i⟩ ⟨j⟩ (Discrete.eqToIso h)
      (Discrete.eqToIso (by dsimp; rw [← add_left_inj j, add_assoc, h, zero_add, add_zero]))
      (Subsingleton.elim _ _)).functor_unitIso_comp X
    all_goals
      ext X
      dsimp [shiftFunctorCompIsoId, unitOfTensorIsoUnit,
        shiftFunctorAdd']
      simp only [Category.assoc, eqToHom_map]
      rfl

/-- Shifting by `n` and shifting by `-n` forms an equivalence. -/
abbrev shiftEquiv (n : A) : C ≌ C := shiftEquiv' C n (-n) (add_neg_cancel n)

variable (X Y : C) (f : X ⟶ Y)

/-- Shifting by `i` is an equivalence. -/
instance (i : A) : (shiftFunctor C i).IsEquivalence := by
  change (shiftEquiv C i).functor.IsEquivalence
  infer_instance

variable {C}

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
abbrev shiftShiftNeg (i : A) : X⟦i⟧⟦-i⟧ ≅ X :=
  (shiftEquiv C i).unitIso.symm.app X

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
abbrev shiftNegShift (i : A) : X⟦-i⟧⟦i⟧ ≅ X :=
  (shiftEquiv C i).counitIso.app X

variable {X Y}

@[reassoc (attr := simp)]
lemma shiftFunctorCompIsoId_naturality_1 (i j : A) (hij : i + j = 0) :
    (shiftFunctorCompIsoId C i j hij).inv.app X ≫ f⟦i⟧'⟦j⟧' ≫
    (shiftFunctorCompIsoId C i j hij).hom.app Y = f :=
  NatIso.naturality_1 (shiftFunctorCompIsoId C i j hij) f

theorem shift_shift_neg' (i : A) :
    f⟦i⟧'⟦-i⟧' = (shiftFunctorCompIsoId C i (-i) (add_neg_cancel i)).hom.app X ≫
      f ≫ (shiftFunctorCompIsoId C i (-i) (add_neg_cancel i)).inv.app Y :=
  (NatIso.naturality_2 (shiftFunctorCompIsoId C i (-i) (add_neg_cancel i)) f).symm

theorem shift_neg_shift' (i : A) :
    f⟦-i⟧'⟦i⟧' = (shiftFunctorCompIsoId C (-i) i (neg_add_cancel i)).hom.app X ≫ f ≫
      (shiftFunctorCompIsoId C (-i) i (neg_add_cancel i)).inv.app Y :=
  (NatIso.naturality_2 (shiftFunctorCompIsoId C (-i) i (neg_add_cancel i)) f).symm

theorem shift_equiv_triangle (n : A) (X : C) :
    (shiftShiftNeg X n).inv⟦n⟧' ≫ (shiftNegShift (X⟦n⟧) n).hom = 𝟙 (X⟦n⟧) :=
  (shiftEquiv C n).functor_unitIso_comp X

section

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem shift_shiftFunctorCompIsoId_hom_app (n m : A) (h : n + m = 0) (X : C) :
    ((shiftFunctorCompIsoId C n m h).hom.app X)⟦n⟧' =
    (shiftFunctorCompIsoId C m n
      (by rw [← neg_eq_of_add_eq_zero_left h, add_neg_cancel])).hom.app (X⟦n⟧) := by
  dsimp [shiftFunctorCompIsoId]
  simpa only [Functor.map_comp, ← shiftFunctorAdd'_zero_add_inv_app n X,
    ← shiftFunctorAdd'_add_zero_inv_app n X]
    using shiftFunctorAdd'_assoc_inv_app n m n 0 0 n h
      (by rw [← neg_eq_of_add_eq_zero_left h, add_neg_cancel]) (by rw [h, zero_add]) X

set_option backward.isDefEq.respectTransparency false in
theorem shift_shiftFunctorCompIsoId_inv_app (n m : A) (h : n + m = 0) (X : C) :
    ((shiftFunctorCompIsoId C n m h).inv.app X)⟦n⟧' =
    ((shiftFunctorCompIsoId C m n
      (by rw [← neg_eq_of_add_eq_zero_left h, add_neg_cancel])).inv.app (X⟦n⟧)) := by
  rw [← cancel_mono (((shiftFunctorCompIsoId C n m h).hom.app X)⟦n⟧'),
    ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id,
    shift_shiftFunctorCompIsoId_hom_app, Iso.inv_hom_id_app]
  rfl

theorem shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app (n : A) (X : C) :
    ((shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.app X)⟦n⟧' =
    (shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).hom.app (X⟦n⟧) := by
  apply shift_shiftFunctorCompIsoId_hom_app

theorem shift_shiftFunctorCompIsoId_add_neg_cancel_inv_app (n : A) (X : C) :
    ((shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).inv.app X)⟦n⟧' =
    (shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).inv.app (X⟦n⟧) := by
  apply shift_shiftFunctorCompIsoId_inv_app

theorem shift_shiftFunctorCompIsoId_neg_add_cancel_hom_app (n : A) (X : C) :
    ((shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).hom.app X)⟦-n⟧' =
    (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.app (X⟦-n⟧) := by
  apply shift_shiftFunctorCompIsoId_hom_app

theorem shift_shiftFunctorCompIsoId_neg_add_cancel_inv_app (n : A) (X : C) :
    ((shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).inv.app X)⟦-n⟧' =
    (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).inv.app (X⟦-n⟧) := by
  apply shift_shiftFunctorCompIsoId_inv_app

end

section

variable (A)

set_option backward.defeqAttrib.useBackward true in
lemma shiftFunctorCompIsoId_zero_zero_hom_app (X : C) :
    (shiftFunctorCompIsoId C 0 0 (add_zero 0)).hom.app X =
      ((shiftFunctorZero C A).hom.app X)⟦0⟧' ≫ (shiftFunctorZero C A).hom.app X := by
  simp [shiftFunctorCompIsoId, shiftFunctorAdd'_zero_add_inv_app]

set_option backward.defeqAttrib.useBackward true in
lemma shiftFunctorCompIsoId_zero_zero_inv_app (X : C) :
    (shiftFunctorCompIsoId C 0 0 (add_zero 0)).inv.app X =
      (shiftFunctorZero C A).inv.app X ≫ ((shiftFunctorZero C A).inv.app X)⟦0⟧' := by
  simp [shiftFunctorCompIsoId, shiftFunctorAdd'_zero_add_hom_app]

end

section

variable (m n p m' n' p' : A) (hm : m' + m = 0) (hn : n' + n = 0) (hp : p' + p = 0)
  (h : m + n = p)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma shiftFunctorCompIsoId_add'_inv_app :
    (shiftFunctorCompIsoId C p' p hp).inv.app X =
      (shiftFunctorCompIsoId C n' n hn).inv.app X ≫
      (shiftFunctorCompIsoId C m' m hm).inv.app (X⟦n'⟧)⟦n⟧' ≫
      (shiftFunctorAdd' C m n p h).inv.app (X⟦n'⟧⟦m'⟧) ≫
      ((shiftFunctorAdd' C n' m' p'
        (by rw [← add_left_inj p, hp, ← h, add_assoc,
          ← add_assoc m', hm, zero_add, hn])).inv.app X)⟦p⟧' := by
  dsimp [shiftFunctorCompIsoId]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  rw [← NatTrans.naturality]
  dsimp
  rw [← cancel_mono ((shiftFunctorAdd' C p' p 0 hp).inv.app X), Iso.hom_inv_id_app,
    Category.assoc, Category.assoc, Category.assoc, Category.assoc,
    ← shiftFunctorAdd'_assoc_inv_app p' m n n' p 0
      (by rw [← add_left_inj n, hn, add_assoc, h, hp]) h (by rw [add_assoc, h, hp]),
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    Category.assoc, Category.assoc,
    shiftFunctorAdd'_assoc_inv_app n' m' m p' 0 n' _ hm
      (by rw [add_assoc, hm, add_zero]), Iso.hom_inv_id_app_assoc,
    ← shiftFunctorAdd'_add_zero_hom_app, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma shiftFunctorCompIsoId_add'_hom_app :
    (shiftFunctorCompIsoId C p' p hp).hom.app X =
      ((shiftFunctorAdd' C n' m' p'
          (by rw [← add_left_inj p, hp, ← h, add_assoc,
            ← add_assoc m', hm, zero_add, hn])).hom.app X)⟦p⟧' ≫
      (shiftFunctorAdd' C m n p h).hom.app (X⟦n'⟧⟦m'⟧) ≫
      (shiftFunctorCompIsoId C m' m hm).hom.app (X⟦n'⟧)⟦n⟧' ≫
      (shiftFunctorCompIsoId C n' n hn).hom.app X := by
  rw [← cancel_mono ((shiftFunctorCompIsoId C p' p hp).inv.app X), Iso.hom_inv_id_app,
    shiftFunctorCompIsoId_add'_inv_app m n p m' n' p' hm hn hp h,
    Category.assoc, Category.assoc, Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  dsimp
  rw [Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]

end

open CategoryTheory.Limits

variable [HasZeroMorphisms C]

theorem shift_zero_eq_zero (X Y : C) (n : A) : (0 : X ⟶ Y)⟦n⟧' = (0 : X⟦n⟧ ⟶ Y⟦n⟧) :=
  CategoryTheory.Functor.map_zero _ _ _

end AddGroup

section AddCommMonoid

variable [AddCommMonoid A] [HasShift C A]
variable (C)

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
def shiftFunctorComm (i j : A) :
    shiftFunctor C i ⋙ shiftFunctor C j ≅
      shiftFunctor C j ⋙ shiftFunctor C i :=
  (shiftFunctorAdd C i j).symm ≪≫ shiftFunctorAdd' C j i (i + j) (add_comm j i)

lemma shiftFunctorComm_eq (i j k : A) (h : i + j = k) :
    shiftFunctorComm C i j = (shiftFunctorAdd' C i j k h).symm ≪≫
      shiftFunctorAdd' C j i k (by rw [add_comm j i, h]) := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]
  rfl

@[simp]
lemma shiftFunctorComm_eq_refl (i : A) :
    shiftFunctorComm C i i = Iso.refl _ := by
  rw [shiftFunctorComm_eq C i i (i + i) rfl, Iso.symm_self_id]

lemma shiftFunctorComm_symm (i j : A) :
    (shiftFunctorComm C i j).symm = shiftFunctorComm C j i := by
  ext1
  dsimp
  rw [shiftFunctorComm_eq C i j (i + j) rfl, shiftFunctorComm_eq C j i (i + j) (add_comm j i)]
  rfl

variable {C}
variable (X Y : C) (f : X ⟶ Y)

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
abbrev shiftComm (i j : A) : X⟦i⟧⟦j⟧ ≅ X⟦j⟧⟦i⟧ :=
  (shiftFunctorComm C i j).app X

@[simp]
theorem shiftComm_symm (i j : A) : (shiftComm X i j).symm = shiftComm X j i := by
  ext
  exact NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorComm_symm C i j)) X

variable {X Y}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
theorem shiftComm' (i j : A) :
    f⟦i⟧'⟦j⟧' = (shiftComm _ _ _).hom ≫ f⟦j⟧'⟦i⟧' ≫ (shiftComm _ _ _).hom := by
  erw [← shiftComm_symm Y i j, ← ((shiftFunctorComm C i j).hom.naturality_assoc f)]
  dsimp
  simp only [Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]

@[reassoc]
theorem shiftComm_hom_comp (i j : A) :
    (shiftComm X i j).hom ≫ f⟦j⟧'⟦i⟧' = f⟦i⟧'⟦j⟧' ≫ (shiftComm Y i j).hom := by
  rw [shiftComm', ← shiftComm_symm, Iso.symm_hom, Iso.inv_hom_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma shiftFunctorZero_hom_app_shift (n : A) :
    (shiftFunctorZero C A).hom.app (X⟦n⟧) =
    (shiftFunctorComm C n 0).hom.app X ≫ ((shiftFunctorZero C A).hom.app X)⟦n⟧' := by
  rw [← shiftFunctorAdd'_zero_add_inv_app n X, shiftFunctorComm_eq C n 0 n (add_zero n)]
  dsimp
  rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id, shiftFunctorAdd'_add_zero_inv_app]

set_option backward.isDefEq.respectTransparency false in
lemma shiftFunctorZero_inv_app_shift (n : A) :
    (shiftFunctorZero C A).inv.app (X⟦n⟧) =
      ((shiftFunctorZero C A).inv.app X)⟦n⟧' ≫ (shiftFunctorComm C n 0).inv.app X := by
  rw [← cancel_mono ((shiftFunctorZero C A).hom.app (X⟦n⟧)), Category.assoc, Iso.inv_hom_id_app,
    shiftFunctorZero_hom_app_shift, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  dsimp
  rw [Functor.map_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma shiftFunctorComm_zero_hom_app (a : A) :
    (shiftFunctorComm C a 0).hom.app X =
      (shiftFunctorZero C A).hom.app (X⟦a⟧) ≫ ((shiftFunctorZero C A).inv.app X)⟦a⟧' := by
  simp only [shiftFunctorZero_hom_app_shift, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, Functor.map_id, Functor.comp_obj, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app (m₁ m₂ m₃ : A) (X : C) :
    (shiftFunctorComm C m₁ (m₂ + m₃)).hom.app X ≫
    ((shiftFunctorAdd C m₂ m₃).hom.app X)⟦m₁⟧' =
      (shiftFunctorAdd C m₂ m₃).hom.app (X⟦m₁⟧) ≫
        ((shiftFunctorComm C m₁ m₂).hom.app X)⟦m₃⟧' ≫
        (shiftFunctorComm C m₁ m₃).hom.app (X⟦m₂⟧) := by
  rw [← cancel_mono ((shiftFunctorComm C m₁ m₃).inv.app (X⟦m₂⟧)),
    ← cancel_mono (((shiftFunctorComm C m₁ m₂).inv.app X)⟦m₃⟧')]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  dsimp
  simp only [Category.id_comp, ← Functor.map_comp, Iso.hom_inv_id_app]
  dsimp
  simp only [Functor.map_id, Category.comp_id,
    shiftFunctorComm_eq C _ _ _ rfl, ← shiftFunctorAdd'_eq_shiftFunctorAdd]
  dsimp
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp,
    shiftFunctorAdd'_assoc_hom_app_assoc m₂ m₃ m₁ (m₂ + m₃) (m₁ + m₃) (m₁ + (m₂ + m₃)) rfl
      (add_comm m₃ m₁) (add_comm _ m₁) X,
    ← shiftFunctorAdd'_assoc_hom_app_assoc m₂ m₁ m₃ (m₁ + m₂) (m₁ + m₃)
      (m₁ + (m₂ + m₃)) (add_comm _ _) rfl (by rw [add_comm m₂ m₁, add_assoc]) X,
    shiftFunctorAdd'_assoc_hom_app m₁ m₂ m₃
      (m₁ + m₂) (m₂ + m₃) (m₁ + (m₂ + m₃)) rfl rfl (add_assoc _ _ _) X]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma shiftFunctorComm_hom_app_of_add_eq_zero (m n : A) (hmn : m + n = 0) (X : C) :
    (shiftFunctorComm C m n).hom.app X =
      (shiftFunctorCompIsoId C m n hmn).hom.app X ≫
        (shiftFunctorCompIsoId C n m (by rw [add_comm, hmn])).inv.app X := by
  simp [shiftFunctorCompIsoId, shiftFunctorComm_eq C m n 0 hmn]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma shiftFunctorComm_inv_app_of_add_eq_zero (m n : A) (hmn : m + n = 0) (X : C) :
    (shiftFunctorComm C m n).inv.app X =
      (shiftFunctorCompIsoId C n m (by rw [add_comm, hmn])).hom.app X ≫
        (shiftFunctorCompIsoId C m n hmn).inv.app X := by
  simp [shiftFunctorCompIsoId, shiftFunctorComm_eq C m n 0 hmn]

end AddCommMonoid

namespace Functor.FullyFaithful

variable {D : Type*} [Category* D] [AddMonoid A] [HasShift D A]
variable {F : C ⥤ D} (hF : F.FullyFaithful)
variable (s : A → C ⥤ C) (i : ∀ i, s i ⋙ F ≅ F ⋙ shiftFunctor D i)

namespace hasShift

/-- auxiliary definition for `FullyFaithful.hasShift` -/
def zero : s 0 ≅ 𝟭 C :=
  (hF.whiskeringRight C).preimageIso ((i 0) ≪≫ isoWhiskerLeft F (shiftFunctorZero D A) ≪≫
    rightUnitor _ ≪≫ (leftUnitor _).symm)

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma map_zero_hom_app (X : C) :
    F.map ((zero hF s i).hom.app X) =
      (i 0).hom.app X ≫ (shiftFunctorZero D A).hom.app (F.obj X) := by
  simp [zero]

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma map_zero_inv_app (X : C) :
    F.map ((zero hF s i).inv.app X) =
      (shiftFunctorZero D A).inv.app (F.obj X) ≫ (i 0).inv.app X := by
  simp [zero]

/-- auxiliary definition for `FullyFaithful.hasShift` -/
def add (a b : A) : s (a + b) ≅ s a ⋙ s b :=
  (hF.whiskeringRight C).preimageIso (i (a + b) ≪≫ isoWhiskerLeft _ (shiftFunctorAdd D a b) ≪≫
      (associator _ _ _).symm ≪≫ (isoWhiskerRight (i a).symm _) ≪≫
      associator _ _ _ ≪≫ (isoWhiskerLeft _ (i b).symm) ≪≫
      (associator _ _ _).symm)

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma map_add_hom_app (a b : A) (X : C) :
    F.map ((add hF s i a b).hom.app X) =
      (i (a + b)).hom.app X ≫ (shiftFunctorAdd D a b).hom.app (F.obj X) ≫
        ((i a).inv.app X)⟦b⟧' ≫ (i b).inv.app ((s a).obj X) := by
  dsimp [add]
  simp

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma map_add_inv_app (a b : A) (X : C) :
    F.map ((add hF s i a b).inv.app X) =
      (i b).hom.app ((s a).obj X) ≫ ((i a).hom.app X)⟦b⟧' ≫
        (shiftFunctorAdd D a b).inv.app (F.obj X) ≫ (i (a + b)).inv.app X := by
  dsimp [add]
  simp

end hasShift

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open hasShift in
/-- Given a family of endomorphisms of `C` which are intertwined by a fully faithful `F : C ⥤ D`
with shift functors on `D`, we can promote that family to shift functors on `C`. -/
@[implicit_reducible]
def hasShift :
    HasShift C A :=
  hasShiftMk C A
    { F := s
      zero := zero hF s i
      add := add hF s i
      assoc_hom_app := fun m₁ m₂ m₃ X => hF.map_injective (by
        have h := shiftFunctorAdd'_assoc_hom_app m₁ m₂ m₃ _ _ (m₁ + m₂ + m₃) rfl rfl rfl (F.obj X)
        simp only [shiftFunctorAdd'_eq_shiftFunctorAdd] at h
        rw [← cancel_mono ((i m₃).hom.app ((s m₂).obj ((s m₁).obj X)))]
        simp only [Functor.comp_obj, Functor.map_comp, map_add_hom_app,
          Category.assoc, Iso.inv_hom_id_app_assoc, NatTrans.naturality_assoc, Functor.comp_map,
          Iso.inv_hom_id_app, Category.comp_id]
        erw [(i m₃).hom.naturality]
        rw [Functor.comp_map, map_add_hom_app,
          Functor.map_comp, Functor.map_comp, Iso.inv_hom_id_app_assoc,
          ← Functor.map_comp_assoc _ ((i (m₁ + m₂)).inv.app X), Iso.inv_hom_id_app,
          Functor.map_id, Category.id_comp, reassoc_of% h,
          dcongr_arg (fun a => (i a).hom.app X) (add_assoc m₁ m₂ m₃)]
        simp [shiftFunctorAdd', eqToHom_map])
      zero_add_hom_app := fun n X => hF.map_injective (by
        have this := dcongr_arg (fun a => (i a).hom.app X) (zero_add n)
        rw [← cancel_mono ((i n).hom.app ((s 0).obj X))]
        simp only [comp_obj, map_add_hom_app, this, shiftFunctorAdd_zero_add_hom_app, id_obj,
          Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Iso.inv_hom_id_app,
          Category.comp_id, map_comp, eqToHom_map]
        congr 1
        erw [(i n).hom.naturality]
        simp)
      add_zero_hom_app := fun n X => hF.map_injective (by
        have := dcongr_arg (fun a => (i a).hom.app X) (add_zero n)
        simp [this, ← NatTrans.naturality_assoc, eqToHom_map,
          shiftFunctorAdd_add_zero_hom_app]) }

end Functor.FullyFaithful

end

end CategoryTheory
