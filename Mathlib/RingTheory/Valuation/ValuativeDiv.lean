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
  refl (x : R) : rel x x
  trans {x y z : R} : rel x y → rel y z → rel x z
  rel_mul_mul_of_rel_of_rel (x y x' y' : R) : rel x y → rel x' y' → rel (x * x') (y * y')
  rel_total (x y) : rel x y ∨ rel y x
  rel_zero (x) : rel 0 x
  rel_add_of_rel_of_rel (x y z) : rel x z → rel y z → rel (x + y) z
  not_rel_zero_cancel (x y z : R) : ¬ rel x 0 → rel (x * y) (x * z) → rel y z
  not_rel_one_zero : ¬ rel 1 0

@[inherit_doc] infix:50  " ∣ᵥ " => ValuativeRel.rel

namespace Valuation

variable {R Γ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ]
  (v : Valuation R Γ)

/-- We say that a valuation `v` is `Compatible` if the relation `x ∣ᵥ y`
is equivalent to `v x ≤ x y`. -/
class Compatible [ValuativeRel R] where
  dvd_iff_le (x y : R) : x ∣ᵥ y ↔ v x ≤ v y

end Valuation

/-- A preorder on a ring is said to be "valuative" if it agrees with the
valuative relation. -/
class ValuativePreorder (R : Type*) [CommRing R] [ValuativeRel R] [Preorder R] where
  dvd_iff_le (x y : R) : x ∣ᵥ y ↔ x ≤ y

namespace ValuativeRel

variable {R : Type*} [CommRing R] [ValuativeRel R]

variable (R) in
def unitSubmonoid : Submonoid R where
  carrier := { x | ¬ x ∣ᵥ 0}
  mul_mem' := by
    intro x y hx hy
    by_contra c
    apply hy
    simp only [Set.mem_setOf_eq, not_not] at c
    rw [show (0 : R) = x * 0 by simp] at c
    exact not_rel_zero_cancel _ _ _ hx c
  one_mem' := not_rel_one_zero

@[simp]
lemma left_cancel_unitSubmonoid (x y : R) (u : unitSubmonoid R) :
    u * x ∣ᵥ u * y ↔ x ∣ᵥ y := by
  refine ⟨fun h => not_rel_zero_cancel _ _ _ u.prop h, fun h => ?_⟩
  exact rel_mul_mul_of_rel_of_rel _ _ _ _ (refl _) h

@[simp]
lemma right_cancel_unitSubmonoid (x y : R) (u : unitSubmonoid R) :
    x * u ∣ᵥ y * u ↔ x ∣ᵥ y := by
  rw [← left_cancel_unitSubmonoid x y u]
  simp only [mul_comm x, mul_comm y]

variable (R) in
/-- The setoid used to construct `ValueMonoid R`. -/
def valueSetoid : Setoid (R × unitSubmonoid R) where
  r := fun (x,s) (y,t) => x * t ∣ᵥ y * s ∧ y * s ∣ᵥ x * t
  iseqv := {
    refl ru := ⟨refl _, refl _⟩
    symm h := ⟨h.2, h.1⟩
    trans := by
      rintro ⟨r, u⟩ ⟨s, v⟩ ⟨t, w⟩ ⟨h1, h2⟩ ⟨h3, h4⟩
      constructor
      · have := rel_mul_mul_of_rel_of_rel _ _ _ _ h1 (refl ↑w)
        rw [show s * u * w = s * w * u by ring] at this
        have := trans this (rel_mul_mul_of_rel_of_rel _ _ _ _ h3 (refl _))
        rw [show r * v * w = r * w * v by ring] at this
        rw [show t * v * u = t * u * v by ring] at this
        simpa using this
      · have := rel_mul_mul_of_rel_of_rel _ _ _ _ h4 (refl ↑u)
        rw [show s * w * u = s * u * w by ring] at this
        have := trans this (rel_mul_mul_of_rel_of_rel _ _ _ _ h2 (refl _))
        rw [show t * v * u = t * u * v by ring] at this
        rw [show r * v * w = r * w * v by ring] at this
        simpa using this
  }

variable (R) in
/-- The "canonical" value monoid of a ring with a valuative relation. -/
def ValueGroup := Quotient (valueSetoid R)

open Classical in
/-- The value monoid is a linearly ordered commutative monoid with zero. -/
instance : LinearOrderedCommGroupWithZero (ValueGroup R) where
  mul := Quotient.lift₂ (fun x y => Quotient.mk _ <| x * y) sorry
  mul_assoc := sorry
  one := Quotient.mk _ (1,1)
  one_mul := sorry
  mul_one := sorry
  npow := fun n => Quotient.lift (fun x => Quotient.mk _ <| x^n) sorry
  npow_zero := sorry
  npow_succ := sorry
  mul_comm := sorry
  zero := Quotient.mk _ (0, 1)
  zero_mul := sorry
  mul_zero := sorry
  le := Quotient.lift₂ (fun (a,s) (b,t) => a * t ∣ᵥ b * s) sorry
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry
  le_total := sorry
  toDecidableLE := inferInstance
  mul_le_mul_left := sorry
  mul_le_mul_right := sorry
  bot := Quotient.mk _ (0, 1)
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
  refl a := le_refl _
  trans h1 h2 := h1.trans h2
  rel_mul_mul_of_rel_of_rel x x' y y' h1 h2 := by
    simp_rw [v.map_mul]
    apply mul_le_mul
    · assumption
    · assumption
    · exact zero_le'
    · exact zero_le'
  rel_total x y := by apply le_total
  rel_zero x := by simp only [map_zero, zero_le']
  rel_add_of_rel_of_rel x y z h1 h2 := by
    refine le_trans (v.map_add x y) ?_
    simpa only [sup_le_iff] using ⟨h1, h2⟩
  not_rel_zero_cancel := sorry
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
  le (x y : R) := x ∣ᵥ y
  le_refl _ := refl _
  le_trans _ _ _ := trans

/-- The valutaive relation on `WithPreorder R` arising from the valuative relation on `R`.
This is defined as the preorder itself. -/
instance : ValuativeRel (WithPreorder R) where
  rel := (· ≤ ·)
  refl := refl (R := R)
  trans := trans (R := R)
  rel_mul_mul_of_rel_of_rel := rel_mul_mul_of_rel_of_rel (R := R)
  rel_total := rel_total (R := R)
  rel_zero := rel_zero (R := R)
  rel_add_of_rel_of_rel := rel_add_of_rel_of_rel (R := R)
  not_rel_zero_cancel := not_rel_zero_cancel (R := R)
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
  dvd_iff_dvd (a b : A) : a ∣ᵥ b ↔ algebraMap A B a ∣ᵥ algebraMap A B b
