/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCategoryInduction
public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCover

/-!
# The degree of an object in a Galois category

-/

-- to be moved to `CategoryTheory/Galois`

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

open PreGaloisCategory

namespace GaloisCategory

variable [GaloisCategory C]

instance {Y X : C} [PreGaloisCategory.IsConnected Y]
    [PreGaloisCategory.IsConnected X] (f : Y ⟶ X) : Epi f :=
  epi_of_nonempty_of_isConnected (getFiberFunctor C) f

/-- The degree of an object `X` in a Galois category. This is the cardinality
of `F.obj X` for any fiber functor `F`, see the lemma `deg_eq_card_fiber` below. -/
@[no_expose]
noncomputable def deg (X : C) : ℕ :=
  Nat.card ((getFiberFunctor C).obj X)

lemma card_fiber_eq_zero
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] {X : C}
    (hX : IsInitial X) :
    Nat.card (F.obj X) = 0 := by
  have := (initial_iff_fiber_empty F X).1 ⟨hX⟩
  exact Nat.card_of_isEmpty

lemma card_fiber_eq_card_hom
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] {Y X : C}
    [PreGaloisCategory.IsConnected X] [IsGalois Y] (f : Y ⟶ X) :
    Nat.card (F.obj X) = Nat.card (Y ⟶ X) := by
  let y : F.obj Y := Classical.arbitrary _
  refine (Nat.card_eq_of_bijective (fun g ↦ F.map g y)
    ⟨fun g₁ g₂ h ↦ hom_ext_of_isConnected F y h, fun x ↦ ?_⟩).symm
  obtain ⟨z, rfl⟩ := surjective_of_epi ((forget _).map (F.map f)) x
  obtain ⟨γ, rfl⟩ := (isPretransitive_of_isGalois F Y).exists_smul_eq y z
  exact ⟨γ.hom ≫ f, by cat_disch⟩


lemma deg_eq_card_fiber [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (X : C) :
    deg X = Nat.card (F.obj X) := by
  induction X using obj_rec with
  | of_isInitial X hX =>
    simp [deg, card_fiber_eq_zero _ hX]
  | of_isConnected X hX =>
    obtain ⟨Y, f, _⟩ := exists_hom_from_galois_of_connected X
    simp [deg, card_fiber_eq_card_hom _ f]
  | of_isColimit X Y b hb hX hY =>
    simp only [deg] at hX hY
    simp [deg, card_fiber_eq_add_of_isColimit _ hb, hX, hY]

/-- The degree of a morphism `f : Y ⟶ X` in a Galois category, where `X`
is connected. -/
noncomputable def degMap {Y X : C}
    [PreGaloisCategory.IsConnected X] (f : Y ⟶ X) : ℕ :=
  deg (Over.mk f)

-- TODO: show the multiplicativity of degrees

end GaloisCategory

end CategoryTheory
