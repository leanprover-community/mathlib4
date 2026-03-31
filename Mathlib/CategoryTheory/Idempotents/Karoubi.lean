/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Equivalence

/-!
# The Karoubi envelope of a category

In this file, we define the Karoubi envelope `Karoubi C` of a category `C`.

## Main constructions and definitions

- `Karoubi C` is the Karoubi envelope of a category `C`: it is an idempotent
  complete category. It is also preadditive when `C` is preadditive.
- `toKaroubi C : C ⥤ Karoubi C` is a fully faithful functor, which is an equivalence
  (`toKaroubiIsEquivalence`) when `C` is idempotent complete.

-/

@[expose] public section

noncomputable section

open CategoryTheory.Category CategoryTheory.Preadditive CategoryTheory.Limits

namespace CategoryTheory

variable (C : Type*) [Category* C]

namespace Idempotents

/-- In a preadditive category `C`, when an object `X` decomposes as `X ≅ P ⨿ Q`, one may
consider `P` as a direct factor of `X` and up to unique isomorphism, it is determined by the
obvious idempotent `X ⟶ P ⟶ X` which is the projection onto `P` with kernel `Q`. More generally,
one may define a formal direct factor of an object `X : C` : it consists of an idempotent
`p : X ⟶ X` which is thought as the "formal image" of `p`. The type `Karoubi C` shall be the
type of the objects of the karoubi envelope of `C`. It makes sense for any category `C`. -/
structure Karoubi where
  /-- an object of the underlying category -/
  X : C
  /-- an endomorphism of the object -/
  p : X ⟶ X
  /-- the condition that the given endomorphism is an idempotent -/
  idem : p ≫ p = p := by cat_disch

namespace Karoubi

variable {C}

attribute [reassoc (attr := simp)] idem

@[ext (iff := false)]
theorem ext {P Q : Karoubi C} (h_X : P.X = Q.X) (h_p : P.p ≫ eqToHom h_X = eqToHom h_X ≫ Q.p) :
    P = Q := by
  cases P
  cases Q
  dsimp at h_X h_p
  subst h_X
  simpa only [mk.injEq, heq_eq_eq, true_and, eqToHom_refl, comp_id, id_comp] using h_p

/-- A morphism `P ⟶ Q` in the category `Karoubi C` is a morphism in the underlying category
`C` which satisfies a relation, which in the preadditive case, expresses that it induces a
map between the corresponding "formal direct factors" and that it vanishes on the complement
formal direct factor. -/
@[ext]
structure Hom (P Q : Karoubi C) where
  /-- a morphism between the underlying objects -/
  f : P.X ⟶ Q.X
  /-- compatibility of the given morphism with the given idempotents -/
  comm : P.p ≫ f ≫ Q.p = f := by cat_disch

instance [Preadditive C] (P Q : Karoubi C) : Inhabited (Hom P Q) :=
  ⟨⟨0, by rw [zero_comp, comp_zero]⟩⟩

@[reassoc (attr := simp)]
theorem p_comp {P Q : Karoubi C} (f : Hom P Q) : P.p ≫ f.f = f.f := by
  rw [← f.comm, ← assoc, P.idem]

@[reassoc (attr := simp)]
theorem comp_p {P Q : Karoubi C} (f : Hom P Q) : f.f ≫ Q.p = f.f := by
  rw [← f.comm, assoc, assoc, Q.idem]

@[reassoc]
theorem p_comm {P Q : Karoubi C} (f : Hom P Q) : P.p ≫ f.f = f.f ≫ Q.p := by rw [p_comp, comp_p]

theorem comp_proof {P Q R : Karoubi C} (g : Hom Q R) (f : Hom P Q) :
    P.p ≫ (f.f ≫ g.f) ≫ R.p = f.f ≫ g.f := by simp

/-- The category structure on the karoubi envelope of a category. -/
instance : Category (Karoubi C) where
  Hom := Karoubi.Hom
  id P := ⟨P.p, by repeat' rw [P.idem]⟩
  comp f g := ⟨f.f ≫ g.f, Karoubi.comp_proof g f⟩

@[simp]
theorem hom_ext_iff {P Q : Karoubi C} {f g : P ⟶ Q} : f = g ↔ f.f = g.f := by
  constructor
  · intro h
    rw [h]
  · apply Hom.ext

@[ext]
theorem hom_ext {P Q : Karoubi C} (f g : P ⟶ Q) (h : f.f = g.f) : f = g := by
  simpa [hom_ext_iff] using h

@[simp]
theorem comp_f {P Q R : Karoubi C} (f : P ⟶ Q) (g : Q ⟶ R) : (f ≫ g).f = f.f ≫ g.f := rfl

@[simp]
theorem id_f {P : Karoubi C} : Hom.f (𝟙 P) = P.p := rfl

/-- It is possible to coerce an object of `C` into an object of `Karoubi C`.
See also the functor `toKaroubi`. -/
instance coe : CoeTC C (Karoubi C) :=
  ⟨fun X => ⟨X, 𝟙 X, by rw [comp_id]⟩⟩

theorem coe_X (X : C) : (X : Karoubi C).X = X := by simp

@[simp]
theorem coe_p (X : C) : (X : Karoubi C).p = 𝟙 X := rfl

@[simp]
theorem eqToHom_f {P Q : Karoubi C} (h : P = Q) :
    Karoubi.Hom.f (eqToHom h) = P.p ≫ eqToHom (congr_arg Karoubi.X h) := by
  subst h
  simp only [eqToHom_refl, Karoubi.id_f, comp_id]

end Karoubi

/-- The obvious fully faithful functor `toKaroubi` sends an object `X : C` to the obvious
formal direct factor of `X` given by `𝟙 X`. -/
@[simps]
def toKaroubi : C ⥤ Karoubi C where
  obj X := ⟨X, 𝟙 X, by rw [comp_id]⟩
  map f := ⟨f, by simp only [comp_id, id_comp]⟩

instance : (toKaroubi C).Full where map_surjective f := ⟨f.f, rfl⟩

instance : (toKaroubi C).Faithful where
  map_injective := fun h => congr_arg Karoubi.Hom.f h

variable {C}

@[simps add]
instance instAdd [Preadditive C] {P Q : Karoubi C} : Add (P ⟶ Q) where
  add f g := ⟨f.f + g.f, by rw [add_comp, comp_add, f.comm, g.comm]⟩

@[simps neg]
instance instNeg [Preadditive C] {P Q : Karoubi C} : Neg (P ⟶ Q) where
  neg f := ⟨-f.f, by simpa only [neg_comp, comp_neg, neg_inj] using f.comm⟩

@[simps zero]
instance instZero [Preadditive C] {P Q : Karoubi C} : Zero (P ⟶ Q) where
  zero := ⟨0, by simp only [comp_zero, zero_comp]⟩

instance instAddCommGroupHom [Preadditive C] {P Q : Karoubi C} : AddCommGroup (P ⟶ Q) where
  zero_add f := by
    ext
    apply zero_add
  add_zero f := by
    ext
    apply add_zero
  add_assoc f g h' := by
    ext
    apply add_assoc
  add_comm f g := by
    ext
    apply add_comm
  neg_add_cancel f := by
    ext
    apply neg_add_cancel
  zsmul := zsmulRec
  nsmul := nsmulRec

namespace Karoubi

theorem hom_eq_zero_iff [Preadditive C] {P Q : Karoubi C} {f : P ⟶ Q} : f = 0 ↔ f.f = 0 :=
  hom_ext_iff

/-- The map sending `f : P ⟶ Q` to `f.f : P.X ⟶ Q.X` is additive. -/
@[simps]
def inclusionHom [Preadditive C] (P Q : Karoubi C) : AddMonoidHom (P ⟶ Q) (P.X ⟶ Q.X) where
  toFun f := f.f
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem sum_hom [Preadditive C] {P Q : Karoubi C} {α : Type*} (s : Finset α) (f : α → (P ⟶ Q)) :
    (∑ x ∈ s, f x).f = ∑ x ∈ s, (f x).f :=
  map_sum (inclusionHom P Q) f s

end Karoubi

/-- The category `Karoubi C` is preadditive if `C` is. -/
instance [Preadditive C] : Preadditive (Karoubi C) where
  homGroup P Q := by infer_instance

instance [Preadditive C] : Functor.Additive (toKaroubi C) where

open Karoubi

variable (C)

instance : IsIdempotentComplete (Karoubi C) := by
  refine ⟨?_⟩
  intro P p hp
  simp only [hom_ext_iff, comp_f] at hp
  use ⟨P.X, p.f, hp⟩
  use ⟨p.f, by rw [comp_p p, hp]⟩
  use ⟨p.f, by rw [hp, p_comp p]⟩
  simp [hp]

instance [IsIdempotentComplete C] : (toKaroubi C).EssSurj :=
  ⟨fun P => by
    rcases IsIdempotentComplete.idempotents_split P.X P.p P.idem with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
    use Y
    exact
      Nonempty.intro
        { hom := ⟨i, by simp [← Category.assoc, h₁, ← h₂]⟩
          inv := ⟨e, by simp [Category.assoc, h₁, ← h₂]⟩ }⟩

/-- If `C` is idempotent complete, the functor `toKaroubi : C ⥤ Karoubi C` is an equivalence. -/
instance toKaroubi_isEquivalence [IsIdempotentComplete C] : (toKaroubi C).IsEquivalence where

/-- The equivalence `C ≅ Karoubi C` when `C` is idempotent complete. -/
def toKaroubiEquivalence [IsIdempotentComplete C] : C ≌ Karoubi C :=
  (toKaroubi C).asEquivalence

instance toKaroubiEquivalence_functor_additive [Preadditive C] [IsIdempotentComplete C] :
    (toKaroubiEquivalence C).functor.Additive :=
  inferInstanceAs <| (toKaroubi C).Additive

namespace Karoubi

variable {C}

/-- The split mono which appears in the factorisation `decompId P`. -/
@[simps]
def decompId_i (P : Karoubi C) : P ⟶ P.X :=
  ⟨P.p, by rw [coe_p, comp_id, P.idem]⟩

/-- The split epi which appears in the factorisation `decompId P`. -/
@[simps]
def decompId_p (P : Karoubi C) : (P.X : Karoubi C) ⟶ P :=
  ⟨P.p, by rw [coe_p, id_comp, P.idem]⟩

/-- The formal direct factor of `P.X` given by the idempotent `P.p` in the category `C`
is actually a direct factor in the category `Karoubi C`. -/
@[reassoc]
theorem decompId (P : Karoubi C) : 𝟙 P = decompId_i P ≫ decompId_p P := by
  ext
  simp only [comp_f, id_f, P.idem, decompId_i, decompId_p]

theorem decomp_p (P : Karoubi C) : (toKaroubi C).map P.p = decompId_p P ≫ decompId_i P := by
  ext
  simp only [comp_f, decompId_p_f, decompId_i_f, P.idem, toKaroubi_map_f]

theorem decompId_i_toKaroubi (X : C) : decompId_i ((toKaroubi C).obj X) = 𝟙 _ :=
  rfl

theorem decompId_p_toKaroubi (X : C) : decompId_p ((toKaroubi C).obj X) = 𝟙 _ :=
  rfl

theorem decompId_i_naturality {P Q : Karoubi C} (f : P ⟶ Q) :
    f ≫ decompId_i Q = decompId_i P ≫ (by exact Hom.mk f.f (by simp)) := by
  simp

theorem decompId_p_naturality {P Q : Karoubi C} (f : P ⟶ Q) :
    decompId_p P ≫ f = (by exact Hom.mk f.f (by simp)) ≫ decompId_p Q := by
  simp

@[simp]
theorem zsmul_hom [Preadditive C] {P Q : Karoubi C} (n : ℤ) (f : P ⟶ Q) : (n • f).f = n • f.f :=
  map_zsmul (inclusionHom P Q) n f

/-- If `X : Karoubi C`, then `X` is a retract of `((toKaroubi C).obj X.X)`. -/
@[simps]
def retract (X : Karoubi C) : Retract X ((toKaroubi C).obj X.X) where
  i := ⟨X.p, by simp⟩
  r := ⟨X.p, by simp⟩

end Karoubi

set_option backward.isDefEq.respectTransparency false in
instance : (toKaroubi C).PreservesEpimorphisms where
  preserves f _ := ⟨fun g h eq ↦ by
    ext
    rw [← cancel_epi f]
    simpa using eq⟩

set_option backward.isDefEq.respectTransparency false in
instance : (toKaroubi C).PreservesMonomorphisms where
  preserves f _ := ⟨fun g h eq ↦ by
    ext
    rw [← cancel_mono f]
    simpa using eq⟩

end Idempotents

end CategoryTheory
