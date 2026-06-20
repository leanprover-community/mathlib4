/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.SharplyLT.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Lemmas about sharply smaller regular cardinals

-/

@[expose] public section

universe u

open CategoryTheory Limits

lemma Cardinal.mk_iio_le_lift (κ : Cardinal.{u}) :
    Cardinal.mk (Set.Iio κ) ≤ Cardinal.lift.{u + 1} κ := by
  conv_rhs => rw [← card_ord κ, ← mk_Iio_ordinal]
  rw [Cardinal.le_def]
  exact ⟨⟨fun ⟨a, ha⟩ ↦ ⟨a.ord, by simpa⟩, fun _ _ h ↦ by aesop⟩⟩

namespace CategoryTheory.CardinalFilteredPoset.SetCardinalLT

variable (κ : Cardinal.{u}) (X : Type u)

def fromSigma (x : Σ (κ' : Set.Iio κ), κ'.val.ord.ToType → X) : SetCardinalLT κ X :=
  ⟨Set.range x.2,
    HasCardinalLT.of_surjective
      (by simpa only [hasCardinalLT_iff_cardinal_mk_lt,
        Cardinal.mk_toType, Cardinal.card_ord] using! x.1.prop) _
      Set.rangeFactorization_surjective⟩

lemma fromSigma_surjective : Function.Surjective (fromSigma κ X) := by
  rintro ⟨A, hA⟩
  rw [hasCardinalLT_iff_cardinal_mk_lt] at hA
  let e : (Cardinal.mk A).ord.ToType ≃ A :=
    Nonempty.some (by simp [← Cardinal.lift_mk_eq'])
  refine ⟨⟨⟨_, hA⟩, Subtype.val ∘ e⟩, ?_⟩
  rw [Subtype.mk_eq_mk]
  simp [fromSigma]

end CategoryTheory.CardinalFilteredPoset.SetCardinalLT

namespace Cardinal.SharplyLT

open CardinalFilteredPoset

lemma of_pow_lt {κ₁ κ₂ : Cardinal.{u}} [Fact κ₁.IsRegular] [Fact κ₂.IsRegular]
    (h₀ : κ₁ < κ₂) (h : ∀ (α β : Cardinal.{u}), α < κ₁ → β < κ₂ → β ^ α < κ₂) :
    SharplyLT κ₁ κ₂ :=
  .of_exists_cofinal h₀ (fun X hX ↦ by
    refine ⟨.univ, ?_, by simp⟩
    rw [hasCardinalLT_iff_of_equiv (Equiv.Set.univ _)]
    refine HasCardinalLT.of_surjective ?_ _ (SetCardinalLT.fromSigma_surjective _ _)
    refine hasCardinalLT_sigma _ _ ?_ (fun ⟨α, hα⟩ ↦ ?_)
    · refine lt_of_le_of_lt (le_trans ?_ (Cardinal.mk_iio_le_lift κ₁)) (by simpa)
      rw [lift_id'.{u, u + 1}]
    · simpa [hasCardinalLT_iff_cardinal_mk_lt] using
        h _ _ hα (by rwa [hasCardinalLT_iff_cardinal_mk_lt] at hX))

lemma of_le {κ₁ κ₂ : Cardinal.{u}} [Fact κ₁.IsRegular] [Fact κ₂.IsRegular]
    (h₀ : κ₁ ≤ κ₂) :
    letI hκ₂ : κ₂.IsRegular := Fact.out
    letI : Fact (Cardinal.IsRegular (Order.succ (2 ^ κ₂))) :=
      ⟨isRegular_succ (hκ₂.aleph0_le.trans (cantor _).le)⟩
    SharplyLT κ₁ (Order.succ (2 ^ κ₂)) := by
  letI hκ₂ : κ₂.IsRegular := Fact.out
  letI : Fact (Cardinal.IsRegular (Order.succ (2 ^ κ₂))) :=
    ⟨isRegular_succ (hκ₂.aleph0_le.trans (cantor _).le)⟩
  refine of_pow_lt ?_ (fun α β hα hβ ↦ ?_)
  · simp only [Order.lt_succ_iff]
    exact h₀.trans (cantor _).le
  · simp only [Order.lt_succ_iff] at hβ ⊢
    refine (power_le_power_right hβ).trans ?_
    rw [← power_mul]
    refine power_le_power_left (by simp) ?_
    conv_rhs => rw [← mul_eq_self (c := κ₂) (IsRegular.aleph0_le Fact.out)]
    exact mul_le_mul_right (hα.le.trans h₀) _

end Cardinal.SharplyLT
