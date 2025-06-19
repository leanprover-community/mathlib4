/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.NNReal.Basic

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
Use this class to talk about the case where `R` is equipped with an equivalence class
of a valuation. -/
class ValuativeRel (R : Type*) [CommRing R] where
  /-- The relation operator arising from `ValuativeRel`. -/
  rel : R → R → Prop
  refl (x : R) : rel x x
  trans {x y z : R} : rel x y → rel y z → rel x z
  rel_mul_mul_of_rel_of_rel (x y x' y' : R) : rel x y → rel x' y' → rel (x * x') (y * y')
  rel_total (x y) : rel x y ∨ rel y x
  rel_zero (x) : rel 0 x
  rel_add_of_rel_of_rel (x y z) : rel x z → rel y z → rel (x + y) z

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
/-- The setoid used to construct `ValueMonoid R`. -/
def valueSetoid : Setoid R where
  r x y := x ∣ᵥ y ∧ y ∣ᵥ x
  iseqv := by
    constructor
    · intro x
      let h := refl x
      exact ⟨h, h⟩
    · rintro _ _ ⟨h1,h2⟩
      exact ⟨h2,h1⟩
    · rintro _ _ _ ⟨h1,h2⟩ ⟨h3,h4⟩
      exact ⟨trans h1 h3, ValuativeRel.trans h4 h2⟩

variable (R) in
/-- The "canonical" value monoid of a ring with a valuative relation. -/
def ValueMonoid := Quotient (valueSetoid R)

open Classical in
/-- The value monoid is a linearly ordered commutative monoid with zero. -/
instance : LinearOrderedCommMonoidWithZero (ValueMonoid R) where
  mul := Quotient.lift₂ (fun x y => .mk _ <| x * y) <| by
    intro a₁ b₁ a₂ b₂ ⟨ha1,ha2⟩ ⟨hb1,hb2⟩
    apply Quotient.sound
    constructor <;> apply rel_mul_mul_of_rel_of_rel <;> assumption
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    apply Quotient.sound
    simp only [mul_assoc, Setoid.refl]
  one := .mk _ 1
  one_mul := by
    rintro ⟨a⟩
    apply Quotient.sound
    simp
  mul_one := by
    rintro ⟨a⟩
    apply Quotient.sound
    simp
  npow n := Quotient.lift (fun x => .mk _ <| x^n) <| by
    intro a b h
    apply Quotient.sound
    induction n with
    | zero => simp
    | succ n hh =>
      simp_rw [pow_succ]
      cases h ; cases hh
      constructor <;> apply rel_mul_mul_of_rel_of_rel <;> assumption
  npow_zero := by
    rintro ⟨x⟩
    apply Quotient.sound
    simp only [pow_zero, Setoid.refl]
  npow_succ := by
    rintro n ⟨x⟩
    apply Quotient.sound
    simp only [pow_succ, Setoid.refl]
  mul_comm := by
    rintro ⟨a⟩ ⟨b⟩
    apply Quotient.sound
    simp only [mul_comm, Setoid.refl]
  zero := Quotient.mk _ 0
  zero_mul := by
    rintro ⟨a⟩
    apply Quotient.sound
    simp only [zero_mul, Setoid.refl]
  mul_zero := by
    rintro ⟨a⟩
    apply Quotient.sound
    simp only [mul_zero, Setoid.refl]
  le := Quotient.lift₂ (fun a b => a ∣ᵥ b) <| by
    rintro a₁ b₁ a₂ b₂ ⟨ha1,ha2⟩ ⟨hb1,hb2⟩
    ext ; constructor
    · dsimp ; intro h
      refine trans ha2 ?_
      exact trans h hb1
    · dsimp ; intro h
      refine trans ha1 ?_
      refine trans h hb2
  le_refl := by
    rintro ⟨a⟩
    show a ∣ᵥ a
    apply refl
  le_trans := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ (h1 : a ∣ᵥ b) (h2 : b ∣ᵥ c)
    show a ∣ᵥ c
    exact trans h1 h2
  le_antisymm := by
    rintro ⟨a⟩ ⟨b⟩ (h1 : a ∣ᵥ b) (h2 : b ∣ᵥ a)
    apply Quotient.sound
    exact ⟨h1,h2⟩
  le_total := by
    rintro ⟨a⟩ ⟨b⟩
    show (a ∣ᵥ b) ∨ (b ∣ᵥ a)
    apply rel_total
  toDecidableLE := inferInstance
  mul_le_mul_left := by
    rintro ⟨a⟩ ⟨b⟩ (h : a ∣ᵥ b) ⟨c⟩
    show c * a ∣ᵥ c * b
    apply rel_mul_mul_of_rel_of_rel
    · apply refl
    · assumption
  mul_le_mul_right := by
    rintro ⟨a⟩ ⟨b⟩ (h : a ∣ᵥ b) ⟨c⟩
    show a * c ∣ᵥ b * c
    apply rel_mul_mul_of_rel_of_rel
    · assumption
    · apply refl
  bot := Quotient.mk _ 0
  bot_le := by
    rintro ⟨a⟩
    apply rel_zero
  zero_le_one := by apply rel_zero

variable (R) in
/-- The "canonical" valuation associated to a valuative relation. -/
def valuation : Valuation R (ValueMonoid R) where
  toFun := Quotient.mk _
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add_le_max' := by
    intro x y
    let x' : ValueMonoid R := .mk _ x
    let y' : ValueMonoid R := .mk _ y
    set t := max x' y'
    obtain ⟨s,hs⟩ : ∃ s : R, .mk _ s = t := Quotient.exists_rep t
    rw [← hs]
    apply rel_add_of_rel_of_rel
    · suffices x' ≤ t by rw [← hs] at this ; exact this
      simp only [le_sup_left, t]
    · suffices y' ≤ t by rw [← hs] at this ; exact this
      simp only [le_sup_right, t]

instance : (valuation R).Compatible where
  dvd_iff_le _ _ := Iff.rfl

/-- Construct a valuative relation on a ring using a valuation. -/
def ofValuation
    {S Γ : Type*} [CommRing S] [LinearOrderedCommMonoidWithZero Γ]
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

instance : ValuativePreorder (WithPreorder R) where
  dvd_iff_le _ _ := Iff.rfl

open NNReal in variable (R) in
/-- An auxiliary structure used to define `IsRankOne`. -/
structure RankOneStruct where
  /-- The embedding of the value monoid into the nonnegative reals. -/
  emb : ValueMonoid R →*₀ ℝ≥0
  strictMono : StrictMono emb
  nontrivial : ∃ γ : ValueMonoid R, emb γ ≠ 0 ∧ emb γ ≠ 1

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
    ∃ γ : ValueMonoid R, γ < 1 ∧ (∀ δ : ValueMonoid R, δ < 1 → δ ≤ γ)

end ValuativeRel

open Topology ValuativeRel in
/-- We say that a topology on `R` is valuative if the neighborhoods of `0` in `R`
are determined by the relation `· ∣ᵥ ·`. -/
class ValuativeTopology (R : Type*) [CommRing R] [ValuativeRel R] [TopologicalSpace R] where
  mem_nhds_iff : ∀ s : Set R, s ∈ 𝓝 (0 : R) ↔ ∃ γ : ValueMonoid R, { x | valuation _ x < γ } ⊆ s

/-- If `B` is an `A` algebra and both `A` and `B` have valuative relations,
we say that `B|A` is a valuative extension if the valuative relation on `A` is
induced by the one on `B`. -/
class ValuativeExtension
    (A B : Type*)
    [CommRing A] [CommRing B]
    [ValuativeRel A] [ValuativeRel B]
    [Algebra A B] where
  dvd_iff_dvd (a b : A) : a ∣ᵥ b ↔ algebraMap A B a ∣ᵥ algebraMap A B b
