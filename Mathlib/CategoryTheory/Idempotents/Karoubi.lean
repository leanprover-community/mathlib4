/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module category_theory.idempotents.karoubi
! leanprover-community/mathlib commit 200eda15d8ff5669854ff6bcc10aaf37cb70498f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Idempotents.Basic
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor
import Mathbin.CategoryTheory.Equivalence

/-!
# The Karoubi envelope of a category

In this file, we define the Karoubi envelope `karoubi C` of a category `C`.

## Main constructions and definitions

- `karoubi C` is the Karoubi envelope of a category `C`: it is an idempotent
complete category. It is also preadditive when `C` is preadditive.
- `to_karoubi C : C ⥤ karoubi C` is a fully faithful functor, which is an equivalence
(`to_karoubi_is_equivalence`) when `C` is idempotent complete.

-/


noncomputable section

open CategoryTheory.Category

open CategoryTheory.Preadditive

open CategoryTheory.Limits

open BigOperators

namespace CategoryTheory

variable (C : Type _) [Category C]

namespace Idempotents

/-- In a preadditive category `C`, when an object `X` decomposes as `X ≅ P ⨿ Q`, one may
consider `P` as a direct factor of `X` and up to unique isomorphism, it is determined by the
obvious idempotent `X ⟶ P ⟶ X` which is the projection onto `P` with kernel `Q`. More generally,
one may define a formal direct factor of an object `X : C` : it consists of an idempotent
`p : X ⟶ X` which is thought as the "formal image" of `p`. The type `karoubi C` shall be the
type of the objects of the karoubi enveloppe of `C`. It makes sense for any category `C`. -/
@[nolint has_nonempty_instance]
structure Karoubi where
  pt : C
  p : X ⟶ X
  idem : p ≫ p = p
#align category_theory.idempotents.karoubi CategoryTheory.Idempotents.Karoubi

namespace Karoubi

variable {C}

attribute [simp, reassoc.1] idem

@[ext]
theorem ext {P Q : Karoubi C} (h_X : P.pt = Q.pt) (h_p : P.p ≫ eqToHom h_X = eqToHom h_X ≫ Q.p) :
    P = Q := by
  cases P
  cases Q
  dsimp at h_X h_p
  subst h_X
  simpa only [true_and_iff, eq_self_iff_true, id_comp, eq_to_hom_refl, heq_iff_eq, comp_id] using
    h_p
#align category_theory.idempotents.karoubi.ext CategoryTheory.Idempotents.Karoubi.ext

/-- A morphism `P ⟶ Q` in the category `karoubi C` is a morphism in the underlying category
`C` which satisfies a relation, which in the preadditive case, expresses that it induces a
map between the corresponding "formal direct factors" and that it vanishes on the complement
formal direct factor. -/
@[ext]
structure Hom (P Q : Karoubi C) where
  f : P.pt ⟶ Q.pt
  comm : f = P.p ≫ f ≫ Q.p
#align category_theory.idempotents.karoubi.hom CategoryTheory.Idempotents.Karoubi.Hom

instance [Preadditive C] (P Q : Karoubi C) : Inhabited (Hom P Q) :=
  ⟨⟨0, by rw [zero_comp, comp_zero]⟩⟩

@[simp]
theorem hom_ext {P Q : Karoubi C} {f g : Hom P Q} : f = g ↔ f.f = g.f :=
  by
  constructor
  · intro h
    rw [h]
  · ext
#align category_theory.idempotents.karoubi.hom_ext CategoryTheory.Idempotents.Karoubi.hom_ext

@[simp, reassoc.1]
theorem p_comp {P Q : Karoubi C} (f : Hom P Q) : P.p ≫ f.f = f.f := by rw [f.comm, ← assoc, P.idem]
#align category_theory.idempotents.karoubi.p_comp CategoryTheory.Idempotents.Karoubi.p_comp

@[simp, reassoc.1]
theorem comp_p {P Q : Karoubi C} (f : Hom P Q) : f.f ≫ Q.p = f.f := by
  rw [f.comm, assoc, assoc, Q.idem]
#align category_theory.idempotents.karoubi.comp_p CategoryTheory.Idempotents.Karoubi.comp_p

theorem p_comm {P Q : Karoubi C} (f : Hom P Q) : P.p ≫ f.f = f.f ≫ Q.p := by rw [p_comp, comp_p]
#align category_theory.idempotents.karoubi.p_comm CategoryTheory.Idempotents.Karoubi.p_comm

theorem comp_proof {P Q R : Karoubi C} (g : Hom Q R) (f : Hom P Q) :
    f.f ≫ g.f = P.p ≫ (f.f ≫ g.f) ≫ R.p := by rw [assoc, comp_p, ← assoc, p_comp]
#align category_theory.idempotents.karoubi.comp_proof CategoryTheory.Idempotents.Karoubi.comp_proof

/-- The category structure on the karoubi envelope of a category. -/
instance : Category (Karoubi C) where
  Hom := Karoubi.Hom
  id P := ⟨P.p, by repeat' rw [P.idem]⟩
  comp P Q R f g := ⟨f.f ≫ g.f, Karoubi.comp_proof g f⟩

@[simp]
theorem comp_f {P Q R : Karoubi C} (f : P ⟶ Q) (g : Q ⟶ R) : (f ≫ g).f = f.f ≫ g.f := by rfl
#align category_theory.idempotents.karoubi.comp_f CategoryTheory.Idempotents.Karoubi.comp_f

@[simp]
theorem id_eq {P : Karoubi C} : 𝟙 P = ⟨P.p, by repeat' rw [P.idem]⟩ := by rfl
#align category_theory.idempotents.karoubi.id_eq CategoryTheory.Idempotents.Karoubi.id_eq

/-- It is possible to coerce an object of `C` into an object of `karoubi C`.
See also the functor `to_karoubi`. -/
instance coe : CoeTC C (Karoubi C) :=
  ⟨fun X => ⟨X, 𝟙 X, by rw [comp_id]⟩⟩
#align category_theory.idempotents.karoubi.coe CategoryTheory.Idempotents.Karoubi.coe

@[simp]
theorem coe_x (X : C) : (X : Karoubi C).pt = X := by rfl
#align category_theory.idempotents.karoubi.coe_X CategoryTheory.Idempotents.Karoubi.coe_x

@[simp]
theorem coe_p (X : C) : (X : Karoubi C).p = 𝟙 X := by rfl
#align category_theory.idempotents.karoubi.coe_p CategoryTheory.Idempotents.Karoubi.coe_p

@[simp]
theorem eqToHom_f {P Q : Karoubi C} (h : P = Q) :
    Karoubi.Hom.f (eqToHom h) = P.p ≫ eqToHom (congr_arg Karoubi.x h) :=
  by
  subst h
  simp only [eq_to_hom_refl, karoubi.id_eq, comp_id]
#align category_theory.idempotents.karoubi.eq_to_hom_f CategoryTheory.Idempotents.Karoubi.eqToHom_f

end Karoubi

/-- The obvious fully faithful functor `to_karoubi` sends an object `X : C` to the obvious
formal direct factor of `X` given by `𝟙 X`. -/
@[simps]
def toKaroubi : C ⥤ Karoubi C
    where
  obj X := ⟨X, 𝟙 X, by rw [comp_id]⟩
  map X Y f := ⟨f, by simp only [comp_id, id_comp]⟩
#align category_theory.idempotents.to_karoubi CategoryTheory.Idempotents.toKaroubi

instance : Full (toKaroubi C) where preimage X Y f := f.f

instance : Faithful (toKaroubi C) where

variable {C}

@[simps]
instance [Preadditive C] {P Q : Karoubi C} : AddCommGroup (P ⟶ Q)
    where
  add f g :=
    ⟨f.f + g.f, by
      rw [add_comp, comp_add]
      congr
      exacts[f.comm, g.comm]⟩
  zero := ⟨0, by simp only [comp_zero, zero_comp]⟩
  zero_add f := by
    ext
    simp only [zero_add]
  add_zero f := by
    ext
    simp only [add_zero]
  add_assoc f g h' := by simp only [add_assoc]
  add_comm f g := by
    ext
    apply_rules [add_comm]
  neg f := ⟨-f.f, by simpa only [neg_comp, comp_neg, neg_inj] using f.comm⟩
  add_left_neg f := by
    ext
    apply_rules [add_left_neg]

namespace Karoubi

theorem hom_eq_zero_iff [Preadditive C] {P Q : Karoubi C} {f : Hom P Q} : f = 0 ↔ f.f = 0 :=
  hom_ext
#align category_theory.idempotents.karoubi.hom_eq_zero_iff CategoryTheory.Idempotents.Karoubi.hom_eq_zero_iff

/-- The map sending `f : P ⟶ Q` to `f.f : P.X ⟶ Q.X` is additive. -/
@[simps]
def inclusionHom [Preadditive C] (P Q : Karoubi C) : AddMonoidHom (P ⟶ Q) (P.pt ⟶ Q.pt)
    where
  toFun f := f.f
  map_zero' := rfl
  map_add' f g := rfl
#align category_theory.idempotents.karoubi.inclusion_hom CategoryTheory.Idempotents.Karoubi.inclusionHom

@[simp]
theorem sum_hom [Preadditive C] {P Q : Karoubi C} {α : Type _} (s : Finset α) (f : α → (P ⟶ Q)) :
    (∑ x in s, f x).f = ∑ x in s, (f x).f :=
  AddMonoidHom.map_sum (inclusionHom P Q) f s
#align category_theory.idempotents.karoubi.sum_hom CategoryTheory.Idempotents.Karoubi.sum_hom

end Karoubi

/-- The category `karoubi C` is preadditive if `C` is. -/
instance [Preadditive C] : Preadditive (Karoubi C) where homGroup P Q := by infer_instance

instance [Preadditive C] : Functor.Additive (toKaroubi C) where

open Karoubi

variable (C)

instance : IsIdempotentComplete (Karoubi C) :=
  by
  refine' ⟨_⟩
  intro P p hp
  have hp' := hom_ext.mp hp
  simp only [comp_f] at hp'
  use ⟨P.X, p.f, hp'⟩
  use ⟨p.f, by rw [comp_p p, hp']⟩
  use ⟨p.f, by rw [hp', p_comp p]⟩
  constructor <;> simpa only [hom_ext] using hp'

instance [IsIdempotentComplete C] : EssSurj (toKaroubi C) :=
  ⟨fun P => by
    have h : is_idempotent_complete C := inferInstance
    rcases is_idempotent_complete.idempotents_split P.X P.p P.idem with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
    use Y
    exact
      Nonempty.intro
        { Hom := ⟨i, by erw [id_comp, ← h₂, ← assoc, h₁, id_comp]⟩
          inv := ⟨e, by erw [comp_id, ← h₂, assoc, h₁, comp_id]⟩ }⟩

/-- If `C` is idempotent complete, the functor `to_karoubi : C ⥤ karoubi C` is an equivalence. -/
def toKaroubiIsEquivalence [IsIdempotentComplete C] : IsEquivalence (toKaroubi C) :=
  Equivalence.ofFullyFaithfullyEssSurj (toKaroubi C)
#align category_theory.idempotents.to_karoubi_is_equivalence CategoryTheory.Idempotents.toKaroubiIsEquivalence

/-- The equivalence `C ≅ karoubi C` when `C` is idempotent complete. -/
def toKaroubiEquivalence [IsIdempotentComplete C] : C ≌ Karoubi C :=
  haveI := to_karoubi_is_equivalence C
  functor.as_equivalence (to_karoubi C)
#align category_theory.idempotents.to_karoubi_equivalence CategoryTheory.Idempotents.toKaroubiEquivalence

instance toKaroubiEquivalence_functor_additive [Preadditive C] [IsIdempotentComplete C] :
    (toKaroubiEquivalence C).Functor.Additive :=
  (inferInstance : (toKaroubi C).Additive)
#align category_theory.idempotents.to_karoubi_equivalence_functor_additive CategoryTheory.Idempotents.toKaroubiEquivalence_functor_additive

namespace Karoubi

variable {C}

/-- The split mono which appears in the factorisation `decomp_id P`. -/
@[simps]
def decompIdI (P : Karoubi C) : P ⟶ P.pt :=
  ⟨P.p, by erw [coe_p, comp_id, P.idem]⟩
#align category_theory.idempotents.karoubi.decomp_id_i CategoryTheory.Idempotents.Karoubi.decompIdI

/-- The split epi which appears in the factorisation `decomp_id P`. -/
@[simps]
def decompIdP (P : Karoubi C) : (P.pt : Karoubi C) ⟶ P :=
  ⟨P.p, by erw [coe_p, id_comp, P.idem]⟩
#align category_theory.idempotents.karoubi.decomp_id_p CategoryTheory.Idempotents.Karoubi.decompIdP

/-- The formal direct factor of `P.X` given by the idempotent `P.p` in the category `C`
is actually a direct factor in the category `karoubi C`. -/
theorem decomp_id (P : Karoubi C) : 𝟙 P = decompIdI P ≫ decompIdP P :=
  by
  ext
  simp only [comp_f, id_eq, P.idem, decomp_id_i, decomp_id_p]
#align category_theory.idempotents.karoubi.decomp_id CategoryTheory.Idempotents.Karoubi.decomp_id

theorem decomp_p (P : Karoubi C) : (toKaroubi C).map P.p = decompIdP P ≫ decompIdI P :=
  by
  ext
  simp only [comp_f, decomp_id_p_f, decomp_id_i_f, P.idem, to_karoubi_map_f]
#align category_theory.idempotents.karoubi.decomp_p CategoryTheory.Idempotents.Karoubi.decomp_p

theorem decompIdI_toKaroubi (X : C) : decompIdI ((toKaroubi C).obj X) = 𝟙 _ :=
  by
  ext
  rfl
#align category_theory.idempotents.karoubi.decomp_id_i_to_karoubi CategoryTheory.Idempotents.Karoubi.decompIdI_toKaroubi

theorem decompIdP_toKaroubi (X : C) : decompIdP ((toKaroubi C).obj X) = 𝟙 _ :=
  by
  ext
  rfl
#align category_theory.idempotents.karoubi.decomp_id_p_to_karoubi CategoryTheory.Idempotents.Karoubi.decompIdP_toKaroubi

theorem decompIdI_naturality {P Q : Karoubi C} (f : P ⟶ Q) :
    f ≫ decompIdI _ = decompIdI _ ≫ ⟨f.f, by erw [comp_id, id_comp]⟩ :=
  by
  ext
  simp only [comp_f, decomp_id_i_f, karoubi.comp_p, karoubi.p_comp]
#align category_theory.idempotents.karoubi.decomp_id_i_naturality CategoryTheory.Idempotents.Karoubi.decompIdI_naturality

theorem decompIdP_naturality {P Q : Karoubi C} (f : P ⟶ Q) :
    decompIdP P ≫ f =
      (⟨f.f, by erw [comp_id, id_comp]⟩ : (P.pt : Karoubi C) ⟶ Q.pt) ≫ decompIdP Q :=
  by
  ext
  simp only [comp_f, decomp_id_p_f, karoubi.comp_p, karoubi.p_comp]
#align category_theory.idempotents.karoubi.decomp_id_p_naturality CategoryTheory.Idempotents.Karoubi.decompIdP_naturality

@[simp]
theorem zsmul_hom [Preadditive C] {P Q : Karoubi C} (n : ℤ) (f : P ⟶ Q) : (n • f).f = n • f.f :=
  map_zsmul (inclusionHom P Q) n f
#align category_theory.idempotents.karoubi.zsmul_hom CategoryTheory.Idempotents.Karoubi.zsmul_hom

end Karoubi

end Idempotents

end CategoryTheory

