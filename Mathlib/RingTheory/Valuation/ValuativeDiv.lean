/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.NNReal.Basic

noncomputable section

/-!

# Valuative Division Operators

In this file we introduce a class called `ValuativeDiv R` for a ring `R`.
This bundles a relation `div : R → R → Prop` on `R` which mimics a
preorder on `R` arising from a valuation.
We introduce the notation `x ∣ᵥ y` for this relation.

Recall that the equivalence class of a valuation is *completely* characterized by
such a preorder. Thus, we can think of `ValuativeDiv R` as a way of
saying that `R` is endowed with an equivalence class of a valuation.
-/

/-- The class `[ValuativeDiv R]` class introduces an operator `x ∣ᵥ y : Prop` for `x y : R`
which is the natural relation arising from an equivalence class of a valuation on `R`.
Use this class to talk about the case where `R` is equipped with an equivalence class
of a valuation. -/
class ValuativeDiv (R : Type*) [CommRing R] where
  /-- The divisibility operator arising from `ValuativeDiv`. -/
  dvd : R → R → Prop
  isPreorder : IsPreorder _ dvd
  mul_dvd_mul (x y x' y' : R) : dvd x y → dvd x' y' → dvd (x * x') (y * y')
  dvd_total (x y) : dvd x y ∨ dvd y x
  zero_dvd (x) : dvd 0 x
  add_dvd (x y z) : dvd x z → dvd y z → dvd (x + y) z

@[inherit_doc] infix:50  " ∣ᵥ " => ValuativeDiv.dvd

namespace Valuation

variable {R Γ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ]
  (v : Valuation R Γ)

/-- We say that a valuation `v` is `Compatible` if the relation `x ∣ᵥ y`
is equivalent to `v x ≤ x y`. -/
class Compatible [ValuativeDiv R] where
  dvd_iff_le (x y : R) : x ∣ᵥ y ↔ v x ≤ v y

end Valuation

open Topology in
/-- We say that a topology on `R` is valuative if the neighborhoods of `0` in `R`
are determined by the relation `· ∣ᵥ ·`. -/
class ValuativeTopology (R : Type*) [CommRing R] [ValuativeDiv R] [TopologicalSpace R] where
  mem_nhds_iff : ∀ s : Set R, s ∈ 𝓝 (0 : R) ↔ ∃ r : R, { s | (s ∣ᵥ r) ∧ ¬ (r ∣ᵥ s) } ⊆ s

class ValuativePreorder (R : Type*) [CommRing R] [ValuativeDiv R] [Preorder R] where
  dvd_iff_le (x y : R) : x ∣ᵥ y ↔ x ≤ y

namespace ValuativeDiv

variable {R : Type*} [CommRing R] [ValuativeDiv R]

variable (R) in
def valueSetoid : Setoid R where
  r x y := x ∣ᵥ y ∧ y ∣ᵥ x
  iseqv := by
    constructor
    · intro x
      let h := isPreorder.refl x
      exact ⟨h, h⟩
    · rintro _ _ ⟨h1,h2⟩
      exact ⟨h2,h1⟩
    · rintro _ _ _ ⟨h1,h2⟩ ⟨h3,h4⟩
      exact ⟨isPreorder.trans _ _ _ h1 h3, isPreorder.trans _ _ _ h4 h2⟩

variable (R) in
def ValueMonoid := Quotient (valueSetoid R)

open Classical in
instance : LinearOrderedCommMonoidWithZero (ValueMonoid R) where
  mul := Quotient.lift₂ (fun x y => .mk _ <| x * y) <| by
    intro a₁ b₁ a₂ b₂ ⟨ha1,ha2⟩ ⟨hb1,hb2⟩
    apply Quotient.sound
    constructor <;> apply mul_dvd_mul <;> assumption
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
      constructor <;> apply mul_dvd_mul <;> assumption
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
      refine isPreorder.trans _ _ _ ha2 ?_
      exact isPreorder.trans _ _ _ h hb1
    · dsimp ; intro h
      refine isPreorder.trans _ _ _ ha1 ?_
      refine isPreorder.trans _ _ _ h hb2
  le_refl := by
    rintro ⟨a⟩
    show a ∣ᵥ a
    apply isPreorder.refl
  le_trans := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ (h1 : a ∣ᵥ b) (h2 : b ∣ᵥ c)
    show a ∣ᵥ c
    exact isPreorder.trans _ _ _ h1 h2
  le_antisymm := by
    rintro ⟨a⟩ ⟨b⟩ (h1 : a ∣ᵥ b) (h2 : b ∣ᵥ a)
    apply Quotient.sound
    exact ⟨h1,h2⟩
  le_total := by
    rintro ⟨a⟩ ⟨b⟩
    show (a ∣ᵥ b) ∨ (b ∣ᵥ a)
    apply dvd_total
  toDecidableLE := inferInstance
  mul_le_mul_left := by
    rintro ⟨a⟩ ⟨b⟩ (h : a ∣ᵥ b) ⟨c⟩
    show c * a ∣ᵥ c * b
    apply mul_dvd_mul
    · apply isPreorder.refl
    · assumption
  mul_le_mul_right := by
    rintro ⟨a⟩ ⟨b⟩ (h : a ∣ᵥ b) ⟨c⟩
    show a * c ∣ᵥ b * c
    apply mul_dvd_mul
    · assumption
    · apply isPreorder.refl
  bot := Quotient.mk _ 0
  bot_le := by
    rintro ⟨a⟩
    apply zero_dvd
  zero_le_one := by apply zero_dvd

variable (R) in
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
    apply add_dvd
    · suffices x' ≤ t by rw [← hs] at this ; exact this
      simp only [le_sup_left, t]
    · suffices y' ≤ t by rw [← hs] at this ; exact this
      simp only [le_sup_right, t]

instance : (valuation R).Compatible where
  dvd_iff_le _ _ := Iff.rfl

def ofValuation
    {S Γ : Type*} [CommRing S] [LinearOrderedCommMonoidWithZero Γ]
    (v : Valuation S Γ) : ValuativeDiv S where
  dvd x y := v x ≤ v y
  isPreorder := {
    refl a := le_refl _
    trans a b c h1 h2 := h1.trans h2
  }
  mul_dvd_mul x x' y y' h1 h2 := by
    simp_rw [v.map_mul]
    apply mul_le_mul
    · assumption
    · assumption
    · exact zero_le'
    · exact zero_le'
  dvd_total x y := by apply le_total
  zero_dvd x := by simp only [map_zero, zero_le']
  add_dvd x y z h1 h2 := by
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

open NNReal in variable (R) in
structure DiscreteRankOneStruct where
  emb : ValueMonoid R →*₀ ℝ≥0
  strictMono : StrictMono emb
  nontrivial : ∃ γ : ValueMonoid R, emb γ ≠ 0 ∧ emb γ ≠ 1

variable (R) in
class IsDiscreteRankOne where
  nonempty : Nonempty (DiscreteRankOneStruct R)

end ValuativeDiv
