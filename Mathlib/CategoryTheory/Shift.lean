/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin, Andrew Yang

! This file was ported from Lean 3 source module category_theory.shift
! leanprover-community/mathlib commit 14b69e9f3c16630440a2cbd46f1ddad0d561dee7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathbin.CategoryTheory.Monoidal.End
import Mathbin.CategoryTheory.Monoidal.Discrete

/-!
# Shift

A `shift` on a category `C` indexed by a monoid `A` is nothing more than a monoidal functor
from `A` to `C ⥤ C`. A typical example to keep in mind might be the category of
complexes `⋯ → C_{n-1} → C_n → C_{n+1} → ⋯`. It has a shift indexed by `ℤ`, where we assign to
each `n : ℤ` the functor `C ⥤ C` that re-indexes the terms, so the degree `i` term of `shift n C`
would be the degree `i+n`-th term of `C`.

## Main definitions
* `has_shift`: A typeclass asserting the existence of a shift functor.
* `shift_equiv`: When the indexing monoid is a group, then the functor indexed by `n` and `-n` forms
  an self-equivalence of `C`.
* `shift_comm`: When the indexing monoid is commutative, then shifts commute as well.

## Implementation Notes

Many of the definitions in this file are marked as an `abbreviation` so that the simp lemmas in
`category_theory/monoidal/End` can apply.

-/


namespace CategoryTheory

noncomputable section

universe v u

variable (C : Type u) (A : Type _) [Category.{v} C]

attribute [local instance] endofunctor_monoidal_category

section EqToHom

variable {A C}

variable [AddMonoid A] (F : MonoidalFunctor (Discrete A) (C ⥤ C))

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, reassoc.1]
theorem eqToHom_μ_app {i j i' j' : A} (h₁ : i = i') (h₂ : j = j') (X : C) :
    eqToHom (by rw [h₁, h₂] : (F.obj ⟨i⟩ ⊗ F.obj ⟨j⟩).obj X = (F.obj ⟨i'⟩ ⊗ F.obj ⟨j'⟩).obj X) ≫
        (F.μ ⟨i'⟩ ⟨j'⟩).app X =
      (F.μ ⟨i⟩ ⟨j⟩).app X ≫ eqToHom (by rw [h₁, h₂]) :=
  by
  cases h₁
  cases h₂
  rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id]
#align category_theory.eq_to_hom_μ_app CategoryTheory.eqToHom_μ_app

@[simp, reassoc.1]
theorem μ_inv_app_eqToHom {i j i' j' : A} (h₁ : i = i') (h₂ : j = j') (X : C) :
    inv ((F.μ ⟨i⟩ ⟨j⟩).app X) ≫ eqToHom (by rw [h₁, h₂]) =
      eqToHom (by rw [h₁, h₂]) ≫ inv ((F.μ ⟨i'⟩ ⟨j'⟩).app X) :=
  by
  cases h₁
  cases h₂
  rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id]
#align category_theory.μ_inv_app_eq_to_hom CategoryTheory.μ_inv_app_eqToHom

end EqToHom

variable {A C}

/-- A monoidal functor from a group `A` into `C ⥤ C` induces
a self-equivalence of `C` for each `n : A`. -/
@[simps Functor inverse unit_iso_hom unit_iso_inv counit_iso_hom counit_iso_inv]
def addNegEquiv [AddGroup A] (F : MonoidalFunctor (Discrete A) (C ⥤ C)) (n : A) : C ≌ C :=
  equivOfTensorIsoUnit F ⟨n⟩ ⟨(-n : A)⟩ (Discrete.eqToIso (add_neg_self n))
    (Discrete.eqToIso (neg_add_self n)) (Subsingleton.elim _ _)
#align category_theory.add_neg_equiv CategoryTheory.addNegEquiv

section Defs

variable (A C) [AddMonoid A]

/-- A category has a shift indexed by an additive monoid `A`
if there is a monoidal functor from `A` to `C ⥤ C`. -/
class HasShift (C : Type u) (A : Type _) [Category.{v} C] [AddMonoid A] where
  shift : MonoidalFunctor (Discrete A) (C ⥤ C)
#align category_theory.has_shift CategoryTheory.HasShift

/-- A helper structure to construct the shift functor `(discrete A) ⥤ (C ⥤ C)`. -/
@[nolint has_nonempty_instance]
structure ShiftMkCore where
  f : A → C ⥤ C
  ε : 𝟭 C ≅ F 0
  μ : ∀ n m : A, F n ⋙ F m ≅ F (n + m)
  associativity :
    ∀ (m₁ m₂ m₃ : A) (X : C),
      (F m₃).map ((μ m₁ m₂).Hom.app X) ≫
          (μ (m₁ + m₂) m₃).Hom.app X ≫
            eqToHom
              (by
                congr 2
                exact add_assoc _ _ _) =
        (μ m₂ m₃).Hom.app ((F m₁).obj X) ≫ (μ m₁ (m₂ + m₃)).Hom.app X := by
    obviously
  left_unitality :
    ∀ (n : A) (X : C),
      (F n).map (ε.Hom.app X) ≫ (μ 0 n).Hom.app X =
        eqToHom
          (by
            dsimp
            rw [zero_add]) := by
    obviously
  right_unitality :
    ∀ (n : A) (X : C),
      ε.Hom.app ((F n).obj X) ≫ (μ n 0).Hom.app X =
        eqToHom
          (by
            dsimp
            rw [add_zero]) := by
    obviously
#align category_theory.shift_mk_core CategoryTheory.ShiftMkCore

section

attribute [local simp] eq_to_hom_map

attribute [local reducible] endofunctor_monoidal_category Discrete.addMonoidal

/-- Constructs a `has_shift C A` instance from `shift_mk_core`. -/
@[simps]
def hasShiftMk (h : ShiftMkCore C A) : HasShift C A :=
  ⟨{ Discrete.functor h.f with
      ε := h.ε.Hom
      μ := fun m n => (h.μ m.as n.as).Hom
      μ_natural' := by
        rintro ⟨X⟩ ⟨Y⟩ ⟨X'⟩ ⟨Y'⟩ ⟨⟨⟨rfl⟩⟩⟩ ⟨⟨⟨rfl⟩⟩⟩
        ext
        dsimp
        simp
        dsimp
        simp
      associativity' := by
        introv
        ext
        dsimp
        simpa using h.associativity _ _ _ _
      left_unitality' := by
        rintro ⟨X⟩
        ext
        dsimp
        rw [category.id_comp, ← category.assoc, h.left_unitality]
        simp
      right_unitality' := by
        rintro ⟨X⟩
        ext
        dsimp
        rw [Functor.map_id, category.comp_id, ← category.assoc, h.right_unitality]
        simp }⟩
#align category_theory.has_shift_mk CategoryTheory.hasShiftMk

end

variable [HasShift C A]

/-- The monoidal functor from `A` to `C ⥤ C` given a `has_shift` instance. -/
def shiftMonoidalFunctor : MonoidalFunctor (Discrete A) (C ⥤ C) :=
  HasShift.shift
#align category_theory.shift_monoidal_functor CategoryTheory.shiftMonoidalFunctor

variable {A}

/-- The shift autoequivalence, moving objects and morphisms 'up'. -/
abbrev shiftFunctor (i : A) : C ⥤ C :=
  (shiftMonoidalFunctor C A).obj ⟨i⟩
#align category_theory.shift_functor CategoryTheory.shiftFunctor

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
abbrev shiftFunctorAdd (i j : A) : shiftFunctor C (i + j) ≅ shiftFunctor C i ⋙ shiftFunctor C j :=
  ((shiftMonoidalFunctor C A).μIso ⟨i⟩ ⟨j⟩).symm
#align category_theory.shift_functor_add CategoryTheory.shiftFunctorAdd

variable (A)

/-- Shifting by zero is the identity functor. -/
abbrev shiftFunctorZero : shiftFunctor C (0 : A) ≅ 𝟭 C :=
  (shiftMonoidalFunctor C A).εIso.symm
#align category_theory.shift_functor_zero CategoryTheory.shiftFunctorZero

-- mathport name: «expr ⟦ ⟧»
notation -- Any better notational suggestions?
X "⟦" n "⟧" => (shiftFunctor _ n).obj X

-- mathport name: «expr ⟦ ⟧'»
notation f "⟦" n "⟧'" => (shiftFunctor _ n).map f

end Defs

section AddMonoid

variable {C A} [AddMonoid A] [HasShift C A] (X Y : C) (f : X ⟶ Y)

@[simp]
theorem HasShift.shift_obj_obj (n : A) (X : C) : (HasShift.shift.obj ⟨n⟩).obj X = X⟦n⟧ :=
  rfl
#align category_theory.has_shift.shift_obj_obj CategoryTheory.HasShift.shift_obj_obj

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
abbrev shiftAdd (i j : A) : X⟦i + j⟧ ≅ X⟦i⟧⟦j⟧ :=
  (shiftFunctorAdd C i j).app _
#align category_theory.shift_add CategoryTheory.shiftAdd

@[reassoc.1]
theorem shiftAdd_hom_comp_eq_to_hom₁ (i i' j : A) (h : i = i') :
    (shiftAdd X i j).Hom ≫ eqToHom (by rw [h]) = eqToHom (by rw [h]) ≫ (shiftAdd X i' j).Hom :=
  by
  cases h
  rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id]
#align category_theory.shift_add_hom_comp_eq_to_hom₁ CategoryTheory.shiftAdd_hom_comp_eq_to_hom₁

@[reassoc.1]
theorem shiftAdd_hom_comp_eq_to_hom₂ (i j j' : A) (h : j = j') :
    (shiftAdd X i j).Hom ≫ eqToHom (by rw [h]) = eqToHom (by rw [h]) ≫ (shiftAdd X i j').Hom :=
  by
  cases h
  rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id]
#align category_theory.shift_add_hom_comp_eq_to_hom₂ CategoryTheory.shiftAdd_hom_comp_eq_to_hom₂

@[reassoc.1]
theorem shiftAdd_hom_comp_eq_to_hom₁₂ (i j i' j' : A) (h₁ : i = i') (h₂ : j = j') :
    (shiftAdd X i j).Hom ≫ eqToHom (by rw [h₁, h₂]) =
      eqToHom (by rw [h₁, h₂]) ≫ (shiftAdd X i' j').Hom :=
  by
  cases h₁
  cases h₂
  rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id]
#align category_theory.shift_add_hom_comp_eq_to_hom₁₂ CategoryTheory.shiftAdd_hom_comp_eq_to_hom₁₂

@[reassoc.1]
theorem eqToHom_comp_shiftAdd_inv₁ (i i' j : A) (h : i = i') :
    eqToHom (by rw [h]) ≫ (shiftAdd X i' j).inv = (shiftAdd X i j).inv ≫ eqToHom (by rw [h]) := by
  rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₁]
#align category_theory.eq_to_hom_comp_shift_add_inv₁ CategoryTheory.eqToHom_comp_shiftAdd_inv₁

@[reassoc.1]
theorem eqToHom_comp_shiftAdd_inv₂ (i j j' : A) (h : j = j') :
    eqToHom (by rw [h]) ≫ (shiftAdd X i j').inv = (shiftAdd X i j).inv ≫ eqToHom (by rw [h]) := by
  rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₂]
#align category_theory.eq_to_hom_comp_shift_add_inv₂ CategoryTheory.eqToHom_comp_shiftAdd_inv₂

@[reassoc.1]
theorem eqToHom_comp_shiftAdd_inv₁₂ (i j i' j' : A) (h₁ : i = i') (h₂ : j = j') :
    eqToHom (by rw [h₁, h₂]) ≫ (shiftAdd X i' j').inv =
      (shiftAdd X i j).inv ≫ eqToHom (by rw [h₁, h₂]) :=
  by rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₁₂]
#align category_theory.eq_to_hom_comp_shift_add_inv₁₂ CategoryTheory.eqToHom_comp_shiftAdd_inv₁₂

theorem shift_shift' (i j : A) :
    f⟦i⟧'⟦j⟧' = (shiftAdd X i j).inv ≫ f⟦i + j⟧' ≫ (shiftAdd Y i j).Hom :=
  by
  symm
  apply nat_iso.naturality_1
#align category_theory.shift_shift' CategoryTheory.shift_shift'

variable (A)

/-- Shifting by zero is the identity functor. -/
abbrev shiftZero : X⟦0⟧ ≅ X :=
  (shiftFunctorZero C A).app _
#align category_theory.shift_zero CategoryTheory.shiftZero

theorem shift_zero' : f⟦(0 : A)⟧' = (shiftZero A X).Hom ≫ f ≫ (shiftZero A Y).inv :=
  by
  symm
  apply nat_iso.naturality_2
#align category_theory.shift_zero' CategoryTheory.shift_zero'

end AddMonoid

section AddGroup

variable (C) {A} [AddGroup A] [HasShift C A]

variable (X Y : C) (f : X ⟶ Y)

/-- Shifting by `i` is an equivalence. -/
instance (i : A) : IsEquivalence (shiftFunctor C i) :=
  by
  change is_equivalence (add_neg_equiv (shift_monoidal_functor C A) i).Functor
  infer_instance

@[simp]
theorem shiftFunctor_inv (i : A) : (shiftFunctor C i).inv = shiftFunctor C (-i) :=
  rfl
#align category_theory.shift_functor_inv CategoryTheory.shiftFunctor_inv

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
abbrev shiftFunctorCompShiftFunctorNeg (i : A) : shiftFunctor C i ⋙ shiftFunctor C (-i) ≅ 𝟭 C :=
  unitOfTensorIsoUnit (shiftMonoidalFunctor C A) ⟨i⟩ ⟨(-i : A)⟩ (Discrete.eqToIso (add_neg_self i))
#align category_theory.shift_functor_comp_shift_functor_neg CategoryTheory.shiftFunctorCompShiftFunctorNeg

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
abbrev shiftFunctorNegCompShiftFunctor (i : A) : shiftFunctor C (-i) ⋙ shiftFunctor C i ≅ 𝟭 C :=
  unitOfTensorIsoUnit (shiftMonoidalFunctor C A) ⟨(-i : A)⟩ ⟨i⟩ (Discrete.eqToIso (neg_add_self i))
#align category_theory.shift_functor_neg_comp_shift_functor CategoryTheory.shiftFunctorNegCompShiftFunctor

section

variable (C)

/-- Shifting by `n` is a faithful functor. -/
instance shiftFunctor_faithful (i : A) : Faithful (shiftFunctor C i) :=
  Faithful.of_comp_iso (shiftFunctorCompShiftFunctorNeg C i)
#align category_theory.shift_functor_faithful CategoryTheory.shiftFunctor_faithful

/-- Shifting by `n` is a full functor. -/
instance shiftFunctorFull (i : A) : Full (shiftFunctor C i) :=
  haveI : full (shift_functor C i ⋙ shift_functor C (-i)) :=
    full.of_iso (shift_functor_comp_shift_functor_neg C i).symm
  full.of_comp_faithful _ (shift_functor C (-i))
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
    f⟦i⟧'⟦-i⟧' = (shiftShiftNeg X i).Hom ≫ f ≫ (shiftShiftNeg Y i).inv :=
  by
  symm
  apply nat_iso.naturality_2
#align category_theory.shift_shift_neg' CategoryTheory.shift_shift_neg'

theorem shift_neg_shift' (i : A) :
    f⟦-i⟧'⟦i⟧' = (shiftNegShift X i).Hom ≫ f ≫ (shiftNegShift Y i).inv :=
  by
  symm
  apply nat_iso.naturality_2
#align category_theory.shift_neg_shift' CategoryTheory.shift_neg_shift'

theorem shift_equiv_triangle (n : A) (X : C) :
    (shiftShiftNeg X n).inv⟦n⟧' ≫ (shiftNegShift (X⟦n⟧) n).Hom = 𝟙 (X⟦n⟧) :=
  (addNegEquiv (shiftMonoidalFunctor C A) n).functor_unitIso_comp X
#align category_theory.shift_equiv_triangle CategoryTheory.shift_equiv_triangle

section

attribute [local reducible] Discrete.addMonoidal

theorem shiftShiftNeg_hom_shift (n : A) (X : C) :
    (shiftShiftNeg X n).Hom⟦n⟧' = (shiftNegShift (X⟦n⟧) n).Hom :=
  by
  -- This is just `simp, simp [eq_to_hom_map]`.
  simp only [iso.app_hom, unit_of_tensor_iso_unit_hom_app, eq_to_iso.hom, functor.map_comp,
    obj_μ_app, eq_to_iso.inv, obj_ε_inv_app, μ_naturalityₗ_assoc, category.assoc,
    μ_inv_hom_app_assoc, ε_inv_app_obj, μ_naturalityᵣ_assoc]
  simp only [eq_to_hom_map, eq_to_hom_app, eq_to_hom_trans]
#align category_theory.shift_shift_neg_hom_shift CategoryTheory.shiftShiftNeg_hom_shift

end

theorem shiftShiftNeg_inv_shift (n : A) (X : C) :
    (shiftShiftNeg X n).inv⟦n⟧' = (shiftNegShift (X⟦n⟧) n).inv :=
  by
  ext
  rw [← shift_shift_neg_hom_shift, ← functor.map_comp, iso.hom_inv_id, Functor.map_id]
#align category_theory.shift_shift_neg_inv_shift CategoryTheory.shiftShiftNeg_inv_shift

@[simp]
theorem shiftShiftNeg_shift_eq (n : A) (X : C) :
    (shiftFunctor C n).mapIso (shiftShiftNeg X n) = shiftNegShift (X⟦n⟧) n :=
  CategoryTheory.Iso.ext <| shiftShiftNeg_hom_shift _ _
#align category_theory.shift_shift_neg_shift_eq CategoryTheory.shiftShiftNeg_shift_eq

variable (C)

/-- Shifting by `n` and shifting by `-n` forms an equivalence. -/
@[simps]
def shiftEquiv (n : A) : C ≌ C :=
  {
    addNegEquiv (shiftMonoidalFunctor C A)
      n with
    Functor := shiftFunctor C n
    inverse := shiftFunctor C (-n) }
#align category_theory.shift_equiv CategoryTheory.shiftEquiv

variable {C}

open CategoryTheory.Limits

variable [HasZeroMorphisms C]

theorem shift_zero_eq_zero (X Y : C) (n : A) : (0 : X ⟶ Y)⟦n⟧' = (0 : X⟦n⟧ ⟶ Y⟦n⟧) :=
  CategoryTheory.Functor.map_zero _ _ _
#align category_theory.shift_zero_eq_zero CategoryTheory.shift_zero_eq_zero

end AddGroup

section AddCommMonoid

variable {C A} [AddCommMonoid A] [HasShift C A]

variable (X Y : C) (f : X ⟶ Y)

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
def shiftComm (i j : A) : X⟦i⟧⟦j⟧ ≅ X⟦j⟧⟦i⟧ :=
  (shiftAdd X i j).symm ≪≫
    ((shiftMonoidalFunctor C A).toFunctor.mapIso
            (Discrete.eqToIso <| add_comm i j : (⟨i + j⟩ : Discrete A) ≅ ⟨j + i⟩)).app
        X ≪≫
      shiftAdd X j i
#align category_theory.shift_comm CategoryTheory.shiftComm

@[simp]
theorem shiftComm_symm (i j : A) : (shiftComm X i j).symm = shiftComm X j i := by ext;
  dsimp [shift_comm]; simpa [eq_to_hom_map]
#align category_theory.shift_comm_symm CategoryTheory.shiftComm_symm

variable {X Y}

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
theorem shift_comm' (i j : A) :
    f⟦i⟧'⟦j⟧' = (shiftComm _ _ _).Hom ≫ f⟦j⟧'⟦i⟧' ≫ (shiftComm _ _ _).Hom :=
  by
  -- This is just `simp, simp [eq_to_hom_map]`.
  simp only [shift_comm, iso.trans_hom, iso.symm_hom, iso.app_inv, iso.symm_inv,
    monoidal_functor.μ_iso_hom, iso.app_hom, functor.map_iso_hom, eq_to_iso.hom, μ_naturality_assoc,
    nat_trans.naturality_assoc, nat_trans.naturality, functor.comp_map, category.assoc,
    μ_inv_hom_app_assoc]
  simp only [eq_to_hom_map, eq_to_hom_app, eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp,
    μ_hom_inv_app_assoc]
#align category_theory.shift_comm' CategoryTheory.shift_comm'

@[reassoc.1]
theorem shiftComm_hom_comp (i j : A) :
    (shiftComm X i j).Hom ≫ f⟦j⟧'⟦i⟧' = f⟦i⟧'⟦j⟧' ≫ (shiftComm Y i j).Hom := by
  rw [shift_comm', ← shift_comm_symm, iso.symm_hom, iso.inv_hom_id_assoc]
#align category_theory.shift_comm_hom_comp CategoryTheory.shiftComm_hom_comp

end AddCommMonoid

variable {D : Type _} [Category D] [AddMonoid A] [HasShift D A]

variable (F : C ⥤ D) [Full F] [Faithful F]

section

attribute [local reducible] Discrete.addMonoidal

/-- Given a family of endomorphisms of `C` which are interwined by a fully faithful `F : C ⥤ D`
with shift functors on `D`, we can promote that family to shift functors on `C`. -/
def hasShiftOfFullyFaithful (s : A → C ⥤ C) (i : ∀ i, s i ⋙ F ≅ F ⋙ shiftFunctor D i) :
    HasShift C A :=
  hasShiftMk C A
    { f := s
      ε :=
        natIsoOfCompFullyFaithful F
          (calc
            𝟭 C ⋙ F ≅ F := Functor.leftUnitor _
            _ ≅ F ⋙ 𝟭 D := (Functor.rightUnitor _).symm
            _ ≅ F ⋙ shiftFunctor D (0 : A) := (isoWhiskerLeft F (shiftFunctorZero D A).symm)
            _ ≅ s 0 ⋙ F := (i 0).symm
            )
      μ := fun a b =>
        natIsoOfCompFullyFaithful F
          (calc
            (s a ⋙ s b) ⋙ F ≅ s a ⋙ s b ⋙ F := Functor.associator _ _ _
            _ ≅ s a ⋙ F ⋙ shiftFunctor D b := (isoWhiskerLeft _ (i b))
            _ ≅ (s a ⋙ F) ⋙ shiftFunctor D b := (Functor.associator _ _ _).symm
            _ ≅ (F ⋙ shiftFunctor D a) ⋙ shiftFunctor D b := (isoWhiskerRight (i a) _)
            _ ≅ F ⋙ shiftFunctor D a ⋙ shiftFunctor D b := (Functor.associator _ _ _)
            _ ≅ F ⋙ shiftFunctor D (a + b) := (isoWhiskerLeft _ (shiftFunctorAdd D a b).symm)
            _ ≅ s (a + b) ⋙ F := (i (a + b)).symm
            )
      associativity := by
        intros ; apply F.map_injective; dsimp
        simp only [category.comp_id, category.id_comp, category.assoc,
          CategoryTheory.Functor.map_comp, functor.image_preimage, eq_to_hom_map,
          iso.inv_hom_id_app_assoc]
        erw [(i m₃).Hom.naturality_assoc]
        congr 1
        dsimp
        simp only [eq_to_iso.inv, eq_to_hom_app, eq_to_hom_map, obj_μ_app, μ_naturality_assoc,
          category.assoc, CategoryTheory.Functor.map_comp, functor.image_preimage]
        congr 3
        dsimp
        simp only [← (shift_functor D m₃).map_comp_assoc, iso.inv_hom_id_app]
        erw [(shift_functor D m₃).map_id, category.id_comp]
        erw [((shift_monoidal_functor D A).μIso ⟨m₁ + m₂⟩ ⟨m₃⟩).inv_hom_id_app_assoc]
        congr 1
        have := dcongr_arg (fun a => (i a).inv.app X) (add_assoc m₁ m₂ m₃)
        dsimp at this
        simp [this]
      left_unitality := by
        intros ; apply F.map_injective; dsimp
        simp only [category.comp_id, category.id_comp, category.assoc,
          CategoryTheory.Functor.map_comp, eq_to_hom_app, eq_to_hom_map, functor.image_preimage]
        erw [(i n).Hom.naturality_assoc]
        dsimp
        simp only [eq_to_iso.inv, eq_to_hom_app, category.assoc, CategoryTheory.Functor.map_comp,
          eq_to_hom_map, obj_ε_app, functor.image_preimage]
        simp only [← (shift_functor D n).map_comp_assoc, iso.inv_hom_id_app]
        dsimp
        simp only [category.id_comp, μ_inv_hom_app_assoc, CategoryTheory.Functor.map_id]
        have := dcongr_arg (fun a => (i a).inv.app X) (zero_add n)
        dsimp at this
        simp [this]
      right_unitality := by
        intros ; apply F.map_injective; dsimp
        simp only [category.comp_id, category.id_comp, category.assoc, iso.inv_hom_id_app_assoc,
          eq_to_iso.inv, eq_to_hom_app, eq_to_hom_map, CategoryTheory.Functor.map_comp,
          functor.image_preimage, obj_zero_map_μ_app, ε_hom_inv_app_assoc]
        have := dcongr_arg (fun a => (i a).inv.app X) (add_zero n)
        dsimp at this
        simp [this] }
#align category_theory.has_shift_of_fully_faithful CategoryTheory.hasShiftOfFullyFaithful

end

-- incorrectly reports that `[full F]` and `[faithful F]` are unused.
/-- When we construct shifts on a subcategory from shifts on the ambient category,
the inclusion functor intertwines the shifts. -/
@[nolint unused_arguments]
def hasShiftOfFullyFaithfulComm (s : A → C ⥤ C) (i : ∀ i, s i ⋙ F ≅ F ⋙ shiftFunctor D i) (m : A) :
    haveI := has_shift_of_fully_faithful F s i
    shift_functor C m ⋙ F ≅ F ⋙ shift_functor D m :=
  i m
#align category_theory.has_shift_of_fully_faithful_comm CategoryTheory.hasShiftOfFullyFaithfulComm

end CategoryTheory

