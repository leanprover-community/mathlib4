/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Dialectica.Monoidal

/-!
# The Dialectica category is monoidal closed

We show that the category `Dial` has a closed monoidal category structure.
-/

noncomputable section

namespace CategoryTheory

open Limits

theorem CartesianClosed.ev_natural {C} [Category C] {A X Y : C}
    [HasFiniteProducts C] [Exponentiable A] (g : X ⟶ Y) :
    prod.map (𝟙 A) ((exp A).map g) ≫ (exp.ev A).app Y = (exp.ev A).app X ≫ g := by
  rw [← uncurry_eq, ← Category.id_comp ((exp A).map g), uncurry_natural_right]
  simp [uncurry_eq]

namespace Subobject
variable {C} [Category C] [HasPullbacks C] {A : C}

variable (C) in
/-- If `Subobject.HasHImp C` then `Subobject (A : C)` has a Heyting implication. -/
protected class HasHImp where
  /-- The Heyting implication of `Subobject A`. -/
  himp {A : C} (X Y : Subobject A) : Subobject A
  le_himp_iff {A : C} {a b c : Subobject A} : a ≤ himp b c ↔ a ⊓ b ≤ c
  /-- The Heyting implication is stable under pullbacks. -/
  himp_pullback_le {A B : C} (f : A ⟶ B) {a b : Subobject B} :
    himp ((pullback f).obj a) ((pullback f).obj b) ≤ (pullback f).obj (himp a b)

variable [Subobject.HasHImp C]

instance : HImp (Subobject A) := ⟨Subobject.HasHImp.himp⟩

variable [HasCoproducts C] [HasImages C]

instance : GeneralizedHeytingAlgebra (Subobject A) where
  le_himp_iff _ _ _ := Subobject.HasHImp.le_himp_iff

theorem himp_pullback {X Y : C} (g : X ⟶ Y) (f₁ f₂) :
    (pullback g).obj (f₁ ⇨ f₂) = (pullback g).obj f₁ ⇨ (pullback g).obj f₂ := by
  apply le_antisymm
  · rw [le_himp_iff, ← inf_pullback]
    exact (pullback g).monotone himp_inf_le
  · exact HasHImp.himp_pullback_le _

end Subobject

universe v u
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [HasPullbacks C]
variable [CartesianClosed C] [Subobject.HasHImp C] [HasCoproducts C] [HasImages C]

namespace Dial

local notation "π₁" => prod.fst
local notation "π₂" => prod.snd
local notation "π(" a ", " b ")" => prod.lift a b

open MonoidalCategory CartesianClosed

/-- The internal hom object in `Dial C`. -/
@[simps] def ihomObj (X Y : Dial C) : Dial C where
  src := (X.src ⟹ Y.src) ⨯ ((X.src ⨯ Y.tgt) ⟹ X.tgt)
  tgt := X.src ⨯ Y.tgt
  rel :=
    haveI F1 := π(π₂ ≫ π₁, π(π₂, π₁ ≫ π₂) ≫ (exp.ev _).app _)
    haveI F2 := π(π(π₂ ≫ π₁, π₁ ≫ π₁) ≫ (exp.ev _).app _, π₂ ≫ π₂)
    (Subobject.pullback F1).obj X.rel ⇨ (Subobject.pullback F2).obj Y.rel

/-- The functorial action of `ihom X Y` in the second argument. -/
@[simps] def ihomMap {X Y₁ Y₂ : Dial C} (f : Y₁ ⟶ Y₂) : ihomObj X Y₁ ⟶ ihomObj X Y₂ where
  f := π(π₁ ≫ (exp _).map f.f,
    CartesianClosed.curry
      (π(π(π₁ ≫ π₁, π(π(π₁ ≫ π₁, π₂ ≫ π₁) ≫ (exp.ev _).app _, π₁ ≫ π₂) ≫ f.F),
        π₂ ≫ π₂) ≫ (exp.ev _).app _))
  F := π(π₂ ≫ π₁, π(π(π₂ ≫ π₁, π₁ ≫ π₁) ≫ (exp.ev _).app _, π₂ ≫ π₂) ≫ f.F)
  le := by
    dsimp; rw [Subobject.himp_pullback, Subobject.himp_pullback]
    iterate 4 rw [← Subobject.pullback_comp]
    refine himp_le_himp (le_of_eq ?_) ?_
    · congr 3; ext <;> simp
      slice_lhs 1 2 => simp
      set G := _ ≫ (exp.ev (X.src ⨯ Y₁.tgt)).app _
      have := congr((prod.braiding ..).hom ≫ $(uncurry_curry G))
      simp [uncurry_eq] at this; rw [this]
      (slice_lhs 1 2 => rfl); (slice_rhs 1 2 => rfl); congr 1; simp; congr 2
      (slice_lhs 1 2 => rfl); (slice_rhs 1 2 => rfl); congr 1; simp
    · let F : (ihomObj X Y₁).src ⨯ X.src ⨯ Y₂.tgt ⟶ Y₁.src ⨯ Y₂.tgt :=
        π(π(π₂ ≫ π₁, π₁ ≫ π₁) ≫ (exp.ev X.src).app Y₁.src, π₂ ≫ π₂)
      have := (Subobject.pullback F).monotone (Dial.Hom.le f)
      rw [← Subobject.pullback_comp, ← Subobject.pullback_comp] at this
      convert this using 4 <;> ext <;> simp [F]
      · (slice_lhs 1 2 => rfl); (slice_rhs 1 2 => rfl); congr 1; simp
      · slice_lhs 1 2 =>
          equals π(π₂ ≫ π₁, π₁ ≫ π₁) ≫ prod.map (𝟙 _) ((exp X.src).map f.f) => simp
        rw [Category.assoc, ev_natural]

/-- `(ihom X -)` is a functor on `Dial C`. -/
@[simps] def ihom (X : Dial C) : Dial C ⥤ Dial C where
  obj := ihomObj X
  map := ihomMap
  map_id Y := by
    ext <;> simp <;> ext <;> simp
    rw [curry_eq_iff, uncurry_eq]
    congr 1; ext <;> simp
  map_comp {Y₁ Y₂ Y₃} f g := by
    ext <;> simp <;> ext <;> simp
    · rw [curry_eq_iff, uncurry_eq]; symm
      set G1 := _ ≫ (exp.ev (X.src ⨯ Y₁.tgt)).app _
      set G2 := _ ≫ (exp.ev (X.src ⨯ Y₂.tgt)).app _
      have H1 := uncurry_curry G1
      have H2 := uncurry_curry G2
      simp [uncurry_eq] at H1 H2
      slice_lhs 1 1 =>
        equals
            π(π₁, π₂ ≫ π(π₁ ≫ (exp X.src).map f.f, CartesianClosed.curry G1)) ≫
            prod.map (𝟙 (X.src ⨯ Y₃.tgt)) (CartesianClosed.curry G2) =>
          ext <;> simp; (slice_lhs 1 2 => rfl); congr 1; simp
      rw [Category.assoc, H2]
      slice_lhs 1 2 =>
        equals
          π(π(π₁ ≫ π₁,
              π(prod.map π₁ π₁ ≫ (exp.ev X.src).app Y₁.src ≫ f.f,
                π₁ ≫ π₂) ≫ g.F), π₂) ≫
            prod.map (𝟙 _) (CartesianClosed.curry G1) =>
          rw [← ev_natural]
          simp; congr 2; (slice_lhs 1 2 => rfl); congr 1; simp
      rw [Category.assoc, H1]
      (slice_lhs 1 2 => rfl); congr 1; simp; congr 2
      (slice_lhs 1 2 => rfl); (slice_rhs 1 2 => rfl); congr 1; simp
    · (slice_lhs 1 2 => rfl); (slice_rhs 1 2 => rfl); congr 1; simp; congr 1
      · (slice_rhs 1 2 => rfl); congr 1; simp
      · (slice_rhs 1 2 => rfl); congr 1; rw [← ev_natural]; simp; congr 1
        (slice_rhs 1 2 => rfl); congr 1; simp

/-- `curry` maps `X ⊗ Y ⟶ Z` to `X ⟶ Y ⟹ Z`, in `Dial C`. -/
@[simps] def curry {X Y Z : Dial C} (f : tensorObj X Y ⟶ Z) : Y ⟶ ihomObj X Z where
  f := π(
    CartesianClosed.curry f.f,
    CartesianClosed.curry (π(prod.map π₁ (𝟙 _), π₁ ≫ π₂) ≫ f.F ≫ π₁))
  F := π(π(π₂ ≫ π₁, π₁), π₂ ≫ π₂) ≫ f.F ≫ π₂
  le := by
    dsimp
    rw [Subobject.himp_pullback, ← Subobject.pullback_comp, ← Subobject.pullback_comp,
      le_himp_iff, inf_comm]
    have := (Subobject.pullback π(π(π₂ ≫ π₁, π₁), π₂ ≫ π₂)).monotone (Dial.Hom.le f)
    simp [Subobject.inf_pullback, ← Subobject.pullback_comp,
      ← Subobject.pullback_comp] at this
    set G := π(prod.map π₁ (𝟙 _), π₁ ≫ π₂) ≫ f.F ≫ π₁
    convert this <;> ext <;> simp <;> clear this
    · have := congr((prod.braiding ..).hom ≫ $(uncurry_curry G))
      rw [uncurry_eq] at this
      convert this using 1 <;>
        simp only [← Category.assoc, G] <;> [congr 1; congr 2] <;> simp
    · conv_rhs =>
        rw [← uncurry_curry f.f, uncurry_eq, ← Category.assoc]
      rw [← Category.assoc]; congr 1; simp

theorem curry_natural_right {X Y Z Z' : Dial C} (f : tensorObj X Y ⟶ Z) (g : Z ⟶ Z') :
    curry (f ≫ g) = curry f ≫ ihomMap g := by
  ext <;> simp
  · ext <;> simp
    · rw [CartesianClosed.curry_natural_right]
    · rw [curry_eq_iff, uncurry_eq]
      set G1 := π(prod.map π₁ (𝟙 _), π₁ ≫ π₂) ≫ f.F ≫ π₁
      set G2 : _ ⟶ X.tgt := _ ≫ (exp.ev (X.src ⨯ Z.tgt)).app X.tgt
      slice_rhs 1 1 =>
        equals prod.map (𝟙 (X.src ⨯ Z'.tgt))
          (π(CartesianClosed.curry f.f, CartesianClosed.curry G1)) ≫
            prod.map (𝟙 _) (CartesianClosed.curry G2) =>
          simp
      rw [Category.assoc, ← uncurry_eq, uncurry_curry]
      slice_rhs 1 2 =>
        equals
          π(π(π₁ ≫ π₁,
            prod.map (𝟙 (X.src ⨯ Z'.tgt)) π(CartesianClosed.curry f.f, CartesianClosed.curry G1) ≫
              π(prod.map π₁ π₁ ≫ (exp.ev X.src).app Z.src, π₁ ≫ π₂) ≫ g.F), π₂) ≫
            prod.map (𝟙 _) (CartesianClosed.curry G1) => simp
      rw [Category.assoc, ← uncurry_eq, uncurry_curry]
      (slice_lhs 1 2 => rfl); (slice_rhs 1 3 => rfl); congr 2
      simp; congr 1
      · ext <;> simp
      · (slice_rhs 1 2 => rfl); congr 1
        simp; congr 1
        slice_rhs 1 1 =>
          equals prod.map π₁ (𝟙 Y.src) ≫ prod.map (𝟙 _) (CartesianClosed.curry f.f) => simp
        rw [Category.assoc, ← uncurry_eq, uncurry_curry]
  · set G1 := π(prod.map π₁ (𝟙 _), π₁ ≫ π₂) ≫ f.F ≫ π₁
    (slice_lhs 1 2 => rfl); (slice_rhs 1 2 => rfl); congr 2; simp; congr 1
    (slice_rhs 1 2 => rfl); congr 2; simp; congr 1
    slice_rhs 1 2 =>
      equals π(π₂ ≫ π₁, π₁) ≫ prod.map (𝟙 _) (CartesianClosed.curry f.f) => simp
    rw [Category.assoc, ← uncurry_eq, uncurry_curry]

/-- `uncurry` maps `X ⟶ Y ⟹ Z` to `X ⊗ Y ⟶ Z`, in `Dial C`. -/
@[simps] def uncurry {X Y Z : Dial C} (f : Y ⟶ ihomObj X Z) : tensorObj X Y ⟶ Z where
  f := CartesianClosed.uncurry (f.f ≫ π₁)
  F := π(
    π(prod.map π₁ (𝟙 _), π₁ ≫ π₂) ≫ CartesianClosed.uncurry (f.f ≫ π₂),
    π(π₁ ≫ π₂, π(π₁ ≫ π₁, π₂)) ≫ f.F)
  le := by
    have := (Subobject.pullback π(π₁ ≫ π₂, π(π₁ ≫ π₁, π₂))).monotone (Hom.le f)
    rw [ihomObj_rel, Subobject.himp_pullback] at this
    rw [tensorObj_rel, Subobject.inf_pullback]
    simp [Subobject.inf_pullback, Subobject.himp_pullback, ← Subobject.pullback_comp] at this ⊢
    rw [inf_comm] at this
    simp [uncurry_eq]
    convert this using 1 <;> [congr 5; (congr 3; ext <;> simp)]
      <;> (simp only [← Category.assoc]; congr 1; ext <;> simp)

theorem uncurry_natural_left {X Y' Y Z : Dial C} (f : Y' ⟶ Y) (g : Y ⟶ ihomObj X Z) :
    uncurry (f ≫ g) = X ◁ f ≫ uncurry g := by
  ext <;> simp
  · rw [CartesianClosed.uncurry_natural_left]
  · congr 1
    · slice_rhs 1 2 =>
        equals π(prod.map π₁ (𝟙 Z.tgt), π₁ ≫ π₂) ≫ prod.map (𝟙 _) f.f => simp
      rw [Category.assoc, CartesianClosed.uncurry_natural_left]
    · (slice_lhs 1 2 => rfl); congr 1; simp; congr 1
      (slice_rhs 1 2 => rfl); congr 1; simp

theorem uncurry_curry {X Y Z : Dial C} (f : tensorObj X Y ⟶ Z) : uncurry (curry f) = f := by
  ext <;> simp
  ext <;> simp <;> (slice_lhs 1 2 => equals 𝟙 _ => ext <;> simp) <;> simp

theorem curry_uncurry {X Y Z : Dial C} (f : Y ⟶ ihomObj X Z) : curry (uncurry f) = f := by
  ext <;> simp
  · ext <;> simp
    rw [curry_eq_iff]
    (slice_lhs 1 2 => equals 𝟙 _ => ext <;> simp); simp
  · (slice_lhs 1 2 => equals 𝟙 _ => ext <;> simp); simp

instance : MonoidalClosed (Dial C) where
  closed X := {
    rightAdj := ihom X
    adj := Adjunction.mkOfHomEquiv {
      homEquiv := fun _ _ => ⟨curry, uncurry, uncurry_curry, curry_uncurry⟩
      homEquiv_naturality_left_symm := uncurry_natural_left
      homEquiv_naturality_right := curry_natural_right
    }
  }
