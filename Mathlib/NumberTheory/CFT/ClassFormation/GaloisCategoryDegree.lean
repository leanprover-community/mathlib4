/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCategoryAut
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

lemma deg_eq_card_fiber (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (X : C) :
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

lemma deg_neq_zero_of_not_isInitial {X : C} (hX : IsInitial X → False) :
    deg X ≠ 0 := by
  let F := getFiberFunctor C
  rw [deg_eq_card_fiber F]
  exact non_zero_card_fiber_of_not_initial F X hX

lemma deg_neq_zero_of_isConnected (X : C) [PreGaloisCategory.IsConnected X] :
    deg X ≠ 0 :=
  deg_neq_zero_of_not_isInitial IsConnected.notInitial

lemma congr_deg_of_iso {X Y : C} (e : X ≅ Y) : deg X = deg Y := by
  let F := getFiberFunctor C
  simp only [deg_eq_card_fiber F]
  exact Nat.card_eq_of_bijective _ ((F ⋙ forget _).mapIso e).toEquiv.bijective

/-- The degree of a morphism `f : Y ⟶ X` in a Galois category, where `X`
is connected. -/
noncomputable def degMap {Y X : C}
    [PreGaloisCategory.IsConnected X] (f : Y ⟶ X) : ℕ :=
  deg (Over.mk f)

@[simp]
lemma degMap_overMk {Y X : C}
    [PreGaloisCategory.IsConnected X] (f : Y ⟶ X) :
    deg (Over.mk f) = degMap f := rfl

lemma degMap_eq_card_fiber {Y X : C}
    [PreGaloisCategory.IsConnected X] (f : Y ⟶ X)
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (x : F.obj X) :
    degMap f = (F.map f ⁻¹' {x}).ncard := by
  rw [← degMap_overMk, deg_eq_card_fiber (fiberFunctorOver F X x)]
  dsimp

lemma deg_eq_of_isEquivalence {D : Type*} [Category* D] [GaloisCategory D]
    (G : C ⥤ D) [G.IsEquivalence] (X : C) :
    deg (G.obj X) = deg X := by
  let F := getFiberFunctor D
  simp [deg_eq_card_fiber F, deg_eq_card_fiber (G ⋙ F)]

attribute [local instance] FintypeCat.fintype in
lemma degMap_mul_deg {Y X : C} [PreGaloisCategory.IsConnected X] (f : Y ⟶ X) :
    degMap f * deg X = deg Y := by
  rw [mul_comm]
  let F := getFiberFunctor C
  have := Nat.card_sigma (β := fun (x : F.obj X) ↦ F.map f ⁻¹' {x})
  simp only [← degMap_eq_card_fiber, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, ← deg_eq_card_fiber, Nat.card_coe_set_eq] at this
  rw [← this, deg_eq_card_fiber F]
  exact Nat.card_eq_of_bijective _ (Equiv.sigmaFiberEquiv (F.map f)).bijective

lemma degMap_comp {Z Y X : C} [PreGaloisCategory.IsConnected Y]
    [PreGaloisCategory.IsConnected X] (f : Z ⟶ Y) (g : Y ⟶ X) :
    degMap (f ≫ g) = degMap f * degMap g := by
  have : GaloisCategory (Over (Over.mk g).left) := by dsimp; infer_instance
  rw [← dsimp% deg_eq_of_isEquivalence (Over.iteratedSliceEquiv (Over.mk g)).inverse (Over.mk f)]
  exact (degMap_mul_deg (Over.homMk f : Over.mk (f ≫ g) ⟶ Over.mk g)).symm

lemma degMap_comp' {Z Y X : C} [PreGaloisCategory.IsConnected Y]
    [PreGaloisCategory.IsConnected X] (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X)
    (hfg : f ≫ g = fg := by cat_disch) :
    degMap fg = degMap f * degMap g := by
  rw [← hfg, degMap_comp]

lemma degMap_left_dvd {Z Y X : C} [PreGaloisCategory.IsConnected Y]
    [PreGaloisCategory.IsConnected X] (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X)
    (hfg : f ≫ g = fg := by cat_disch) :
    degMap f ∣ degMap fg := by
  rw [degMap_comp' f g fg]
  apply Nat.dvd_mul_right

lemma degMap_right_dvd {Z Y X : C} [PreGaloisCategory.IsConnected Y]
    [PreGaloisCategory.IsConnected X] (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X)
    (hfg : f ≫ g = fg := by cat_disch) :
    degMap g ∣ degMap fg := by
  rw [degMap_comp' f g fg]
  apply Nat.dvd_mul_left

@[simp]
lemma natCard_aut_eq_deg {X : C} [IsGalois X] :
    Nat.card (Aut X) = deg X := by
  let F := getFiberFunctor C
  rw [deg_eq_card_fiber F]
  exact Nat.card_congr (evaluationEquivOfIsGalois F X (Classical.arbitrary _))

@[simp high]
lemma natCard_aut_overMk {Y X : C} [PreGaloisCategory.IsConnected X]
    (f : Y ⟶ X) [IsGaloisCover f] :
    Nat.card (Aut (Over.mk f)) = degMap f := by
  simp

lemma degMap_eq_card_range_overMap
    {Z Y X : C} [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
    (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X) [IsGaloisCover fg]
    (fac : f ≫ g = fg := by cat_disch) :
    degMap f = Nat.card (Aut.overMap f g fg).range := by
  have := isGaloisCover_of_comp f g fg
  rw [← natCard_aut_overMk]
  exact Nat.card_congr (Aut.overMapEquiv f g fg).toEquiv

variable {Y X : C} [PreGaloisCategory.IsConnected Y]
    [PreGaloisCategory.IsConnected X] (f : Y ⟶ X)

lemma test {X Y : Type*} [Finite X] [Finite Y] (f : X → Y)
    (h : Nat.card X = Nat.card Y)
    (hf : Function.Surjective f) :
    Function.Injective f :=
  ((Nat.bijective_iff_surjective_and_card f).2 ⟨hf, h⟩).injective

lemma isIso_iff_degMap_eq_one {Y X : C}
    [PreGaloisCategory.IsConnected X] (f : Y ⟶ X) :
    IsIso f ↔ degMap f = 1 := by
  have hX := deg_neq_zero_of_isConnected X
  refine ⟨fun _ ↦ mul_left_injective₀ hX ?_, fun hf ↦ ?_⟩
  · simp [degMap_mul_deg f, congr_deg_of_iso (asIso f)]
  · let F := getFiberFunctor C
    have hY : deg Y = deg X := by simp [← degMap_mul_deg f, hf]
    have : Nonempty (F.obj Y) := by
      by_contra!
      exact hX (by rw [← hY, deg_eq_card_fiber F, Nat.card_of_isEmpty])
    simp only [deg_eq_card_fiber F] at hY
    have := epi_of_nonempty_of_isConnected F f
    have : Mono f :=
      F.mono_of_mono_map (ConcreteCategory.mono_of_injective _
        (((Nat.bijective_iff_surjective_and_card _).2
          ⟨surjective_of_epi ((forget _).map (F.map f)), hY⟩).injective))
    apply isIso_of_mono_of_epi

instance {X : C} [PreGaloisCategory.IsConnected X] (f : X ⟶ X) : IsIso f := by
  rw [isIso_iff_degMap_eq_one]
  exact mul_left_injective₀ (deg_neq_zero_of_isConnected X)
    (by simpa using degMap_mul_deg f)

end GaloisCategory

end CategoryTheory
