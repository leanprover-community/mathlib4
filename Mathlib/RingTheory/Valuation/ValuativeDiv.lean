/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.Bases

/-!

# Valuative Relations

In this file we introduce a class called `ValuativeRel R` for a ring `R`.
This bundles a relation `rel : R → R → Prop` on `R` which mimics a
preorder on `R` arising from a valuation.
We introduce the notation `x ∣ᵥ y` for this relation.

Recall that the equivalence class of a valuation is *completely* characterized by
such a preorder. Thus, we can think of `ValuativeRel R` as a way of
saying that `R` is endowed with an equivalence class of a valuation.
-/

noncomputable section

/-- The class `[ValuativeRel R]` class introduces an operator `x ∣ᵥ y : Prop` for `x y : R`
which is the natural relation arising from an equivalence class of a valuation on `R`.
More precisely, if v is a valuation on R then the associated relation is `x ∣ᵥ y ↔ v x ≤ v y`.
Use this class to talk about the case where `R` is equipped with an equivalence class
of valuations. -/
class ValuativeRel (R : Type*) [CommRing R] where
  /-- The relation operator arising from `ValuativeRel`. -/
  rel : R → R → Prop
  rel_total (x y) : rel x y ∨ rel y x
  rel_trans {z y x} : rel x y → rel y z → rel x z
  rel_add {x y z} : rel x z → rel y z → rel (x + y) z
  rel_mul_right {x y} (z) : rel x y → rel (x * z) (y * z)
  rel_mul_cancel {x y z} : ¬ rel z 0 → rel (x * z) (y * z) → rel x y
  not_rel_one_zero : ¬ rel 1 0

@[inherit_doc] infix:50  " ≤ᵥ " => ValuativeRel.rel

namespace Valuation

variable {R Γ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ]
  (v : Valuation R Γ)

/-- We say that a valuation `v` is `Compatible` if the relation `x ∣ᵥ y`
is equivalent to `v x ≤ x y`. -/
class Compatible [ValuativeRel R] where
  dvd_iff_le (x y : R) : x ≤ᵥ y ↔ v x ≤ v y

end Valuation

/-- A preorder on a ring is said to be "valuative" if it agrees with the
valuative relation. -/
class ValuativePreorder (R : Type*) [CommRing R] [ValuativeRel R] [Preorder R] where
  dvd_iff_le (x y : R) : x ≤ᵥ y ↔ x ≤ y

namespace ValuativeRel

variable {R : Type*} [CommRing R] [ValuativeRel R]

lemma rel_refl (x : R) : x ≤ᵥ x := by
  cases rel_total x x <;> assumption

lemma rel_rfl {x : R} : x ≤ᵥ x :=
  rel_refl x

protected alias rel.refl := rel_refl

protected alias rel.rfl := rel_rfl

lemma rel_mul_left {x y : R} (z) : x ≤ᵥ y → (z * x) ≤ᵥ (z * y) := by
  rw [mul_comm z x, mul_comm z y]
  apply rel_mul_right

instance : Trans (rel (R := R)) (rel (R := R)) (rel (R := R)) where
  trans h1 h2 := rel_trans h1 h2

lemma rel_mul {x x' y y' : R} : x ≤ᵥ y → x' ≤ᵥ y' → x * x' ≤ᵥ y * y' := by
  intro h1 h2
  calc x * x' ≤ᵥ x * y' := rel_mul_left _ h2
    _ ≤ᵥ y * y' := rel_mul_right _ h1

variable (R) in
def unitSubmonoid : Submonoid R where
  carrier := { x | ¬ x ≤ᵥ 0}
  mul_mem' := by
    intro x y hx hy
    by_contra c
    apply hy
    simp only [Set.mem_setOf_eq, not_not] at c
    rw [show (0 : R) = x * 0 by simp, mul_comm x y, mul_comm x 0] at c
    exact rel_mul_cancel hx c
  one_mem' := not_rel_one_zero

@[simp]
lemma right_cancel_unitSubmonoid (x y : R) (u : unitSubmonoid R) :
    x * u ≤ᵥ y * u ↔ x ≤ᵥ y := by
  refine ⟨fun h => rel_mul_cancel u.prop h, fun h => ?_⟩
  exact rel_mul_right _ h

@[simp]
lemma left_cancel_unitSubmonoid (x y : R) (u : unitSubmonoid R) :
    u * x ≤ᵥ u * y ↔ x ≤ᵥ y := by
  rw [← right_cancel_unitSubmonoid x y u]
  simp only [mul_comm _ x, mul_comm _ y]

variable (R) in
/-- The setoid used to construct `ValueMonoid R`. -/
def valueSetoid : Setoid (R × unitSubmonoid R) where
  r := fun (x,s) (y,t) => x * t ≤ᵥ y * s ∧ y * s ≤ᵥ x * t
  iseqv := {
    refl ru := ⟨rel_refl _, rel_refl _⟩
    symm h := ⟨h.2, h.1⟩
    trans := by
      rintro ⟨r, u⟩ ⟨s, v⟩ ⟨t, w⟩ ⟨h1, h2⟩ ⟨h3, h4⟩
      constructor
      · have := rel_mul h1 (rel_refl ↑w)
        rw [mul_right_comm s] at this
        have := rel_trans this (rel_mul h3 (rel_refl _))
        rw [mul_right_comm r, mul_right_comm t] at this
        simpa using this
      · have := rel_mul h4 (rel_refl ↑u)
        rw [mul_right_comm s] at this
        have := rel_trans this (rel_mul h2 (rel_refl _))
        rw [mul_right_comm t, mul_right_comm r] at this
        simpa using this
  }

variable (R) in
/-- The "canonical" value monoid of a ring with a valuative relation. -/
def ValueGroup := Quotient (valueSetoid R)

protected
def ValueGroup.mk (x : R) (y : unitSubmonoid R) : ValueGroup R :=
  Quotient.mk _ (x, y)

protected
def ValueGroup.lift {α : Sort*} (f : R → unitSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : unitSubmonoid R), x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → f x s = f y t)
    (t : ValueGroup R) : α :=
  Quotient.lift (fun (x, y) => f x y) (fun (x, t) (y, s) ⟨h₁, h₂⟩ => hf x y s t h₁ h₂) t

@[simp] protected
theorem ValueGroup.lift_mk {α : Sort*} (f : R → unitSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : unitSubmonoid R), x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → f x s = f y t)
    (x : R) (y : unitSubmonoid R) : ValueGroup.lift f hf (.mk x y) = f x y := rfl

protected
def ValueGroup.lift₂ {α : Sort*} (f : R → unitSubmonoid R → R → unitSubmonoid R → α)
    (hf : ∀ (x y z w : R) (t s u v : unitSubmonoid R),
      x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → z * u ≤ᵥ w * v → w * v ≤ᵥ z * u →
      f x s z v = f y t w u)
    (t₁ : ValueGroup R) (t₂ : ValueGroup R) : α :=
  Quotient.lift₂ (fun (x, t) (y, s) => f x t y s)
    (fun (x, t) (z, v) (y, s) (w, u) ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ => hf x y z w s t u v h₁ h₂ h₃ h₄) t₁ t₂

@[simp] protected
def ValueGroup.lift₂_mk {α : Sort*} (f : R → unitSubmonoid R → R → unitSubmonoid R → α)
    (hf : ∀ (x y z w : R) (t s u v : unitSubmonoid R),
      x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → z * u ≤ᵥ w * v → w * v ≤ᵥ z * u →
      f x s z v = f y t w u)
    (x y : R) (z w : unitSubmonoid R) :
    ValueGroup.lift₂ f hf (.mk x z) (.mk y w) = f x z y w := rfl

instance : Zero (ValueGroup R) where
  zero := .mk 0 1

instance : One (ValueGroup R) where
  one := .mk 1 1

instance : Mul (ValueGroup R) where
  mul := ValueGroup.lift₂ (fun a b c d => .mk (a * c) (b * d)) sorry

instance : LE (ValueGroup R) where
  le := ValueGroup.lift₂ (fun a s b t => a * t ≤ᵥ b * s) sorry

instance : LinearOrder (ValueGroup R) where
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry
  le_total := sorry
  toDecidableLE := Classical.decRel LE.le

instance : Bot (ValueGroup R) where
  bot := 0

@[simp]
theorem ValueGroup.bot_eq_zero : (⊥ : ValueGroup R) = 0 := rfl

open Classical in
/-- The value monoid is a linearly ordered commutative monoid with zero. -/
instance : LinearOrderedCommGroupWithZero (ValueGroup R) where
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  npow := fun n => Quotient.lift (fun x => Quotient.mk _ <| x^n) sorry
  npow_zero := sorry
  npow_succ := sorry
  mul_comm := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_le_mul_left := sorry
  mul_le_mul_right := sorry
  bot_le := sorry
  zero_le_one := sorry
  inv := Quotient.lift
    (fun (x,s) => Quotient.mk _ <| if h : x ∈ unitSubmonoid R then (s, ⟨x, h⟩) else (0, 1))
    sorry
  exists_pair_ne := sorry
  inv_zero := sorry
  mul_inv_cancel := sorry

variable (R) in
/-- The "canonical" valuation associated to a valuative relation. -/
def valuation : Valuation R (ValueGroup R) where
  toFun r := Quotient.mk _ (r, 1)
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := sorry
  map_add_le_max' := by sorry

instance : (valuation R).Compatible where
  dvd_iff_le _ _ := sorry

/-- Construct a valuative relation on a ring using a valuation. -/
def ofValuation
    {S Γ : Type*} [CommRing S]
    [LinearOrderedCommMonoidWithZero Γ]
    [Nontrivial Γ] [NoZeroDivisors Γ]
    (v : Valuation S Γ) : ValuativeRel S where
  rel x y := v x ≤ v y
  rel_total := sorry
  rel_trans := sorry
  rel_add := sorry
  rel_mul_right := sorry
  rel_mul_cancel := sorry
  not_rel_one_zero := sorry

lemma isEquiv {Γ₁ Γ₂ : Type*}
    [LinearOrderedCommMonoidWithZero Γ₁]
    [LinearOrderedCommMonoidWithZero Γ₂]
    (v₁ : Valuation R Γ₁)
    (v₂ : Valuation R Γ₂)
    [v₁.Compatible] [v₂.Compatible] :
    v₁.IsEquiv v₂ := by
  intro x y
  simp_rw [← Valuation.Compatible.dvd_iff_le]

variable (R) in
/-- An alias for endowing a ring with a preorder defined as the valuative relation. -/
def WithPreorder := R

/-- The ring instance on `WithPreorder R` arising from the ring structure on `R`. -/
instance : CommRing (WithPreorder R) := inferInstanceAs (CommRing R)

/-- The preorder on `WithPreorder R` arising from the valuative relation on `R`. -/
instance : Preorder (WithPreorder R) where
  le (x y : R) := x ≤ᵥ y
  le_refl _ := rel_refl _
  le_trans _ _ _ := rel_trans

/-- The valutaive relation on `WithPreorder R` arising from the valuative relation on `R`.
This is defined as the preorder itself. -/
instance : ValuativeRel (WithPreorder R) where
  rel := (· ≤ ·)
  rel_total := rel_total (R := R)
  rel_trans := rel_trans (R := R)
  rel_add := rel_add (R := R)
  rel_mul_right := rel_mul_right (R := R)
  rel_mul_cancel := rel_mul_cancel (R := R)
  not_rel_one_zero := not_rel_one_zero (R := R)


instance : ValuativePreorder (WithPreorder R) where
  dvd_iff_le _ _ := Iff.rfl

open NNReal in variable (R) in
/-- An auxiliary structure used to define `IsRankOne`. -/
structure RankOneStruct where
  /-- The embedding of the value monoid into the nonnegative reals. -/
  emb : ValueGroup R →*₀ ℝ≥0
  strictMono : StrictMono emb
  nontrivial : ∃ γ : ValueGroup R, emb γ ≠ 0 ∧ emb γ ≠ 1

variable (R) in
/-- We say that a ring with a valuative relation is of rank one if
there exists a strictly monotone embedding of the "canonical" value monoid into
the nonnegative reals, and the image of this embedding contains some element different
from `0` and `1`. -/
class IsRankOne where
  nonempty : Nonempty (RankOneStruct R)

variable (R) in
/-- A ring with a valuative relation is discrete if its value monoid
has a maximal element `< 1`. -/
class IsDiscrete where
  has_maximal_element :
    ∃ γ : ValueGroup R, γ < 1 ∧ (∀ δ : ValueGroup R, δ < 1 → δ ≤ γ)

lemma valuation_surjective (γ : ValueGroup R) :
    ∃ (a : R) (b : unitSubmonoid R), valuation _ a / valuation _ (b : R) = γ := by
  obtain ⟨a,b⟩ := γ
  use a, b
  sorry

end ValuativeRel

open Topology ValuativeRel in
/-- We say that a topology on `R` is valuative if the neighborhoods of `0` in `R`
are determined by the relation `· ∣ᵥ ·`. -/
class ValuativeTopology (R : Type*) [CommRing R] [ValuativeRel R] [TopologicalSpace R] where
  mem_nhds_iff : ∀ s : Set R, s ∈ 𝓝 (0 : R) ↔ ∃ γ : (ValueGroup R)ˣ, { x | valuation _ x < γ } ⊆ s

namespace ValuativeRel

variable
  {R Γ : Type*} [CommRing R] [ValuativeRel R] [TopologicalSpace R]
  [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation R Γ) [v.Compatible]

end ValuativeRel

/-- If `B` is an `A` algebra and both `A` and `B` have valuative relations,
we say that `B|A` is a valuative extension if the valuative relation on `A` is
induced by the one on `B`. -/
class ValuativeExtension
    (A B : Type*)
    [CommRing A] [CommRing B]
    [ValuativeRel A] [ValuativeRel B]
    [Algebra A B] where
  dvd_iff_dvd (a b : A) : a ≤ᵥ b ↔ algebraMap A B a ≤ᵥ algebraMap A B b
