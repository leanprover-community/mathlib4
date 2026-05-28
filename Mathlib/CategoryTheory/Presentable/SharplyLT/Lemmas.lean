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

def Cardinal.setIioOrderEmbeddingToTypeOrd (κ : Cardinal.{u}) :
    Set.Iio κ ↪o κ.ord.ToType := by
  sorry

@[no_expose]
noncomputable def Cardinal.toTypeOrdMkEquiv (X : Type u) :
    (Cardinal.mk X).ord.ToType ≃ X :=
  Nonempty.some (by simp [← Cardinal.lift_mk_eq'])

namespace CategoryTheory.CardinalFilteredPoset.SetCardinalLT

variable (κ : Cardinal.{u}) (X : Type u)

def fromSigma (x : Σ (κ' : Set.Iio κ), κ'.val.ord.ToType → X) : SetCardinalLT κ X :=
  ⟨Set.range x.2,
    HasCardinalLT.of_surjective
      (by simpa only [hasCardinalLT_iff_cardinal_mk_lt,
        Cardinal.mk_toType, Cardinal.card_ord] using x.1.prop) _
      Set.rangeFactorization_surjective⟩

lemma fromSigma_surjective : Function.Surjective (fromSigma κ X) := by
  rintro ⟨A, hA⟩
  rw [hasCardinalLT_iff_cardinal_mk_lt] at hA
  refine ⟨⟨⟨_, hA⟩, Subtype.val ∘ Cardinal.toTypeOrdMkEquiv A⟩, ?_⟩
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
    · refine HasCardinalLT.of_injective ?_ _
        ((Cardinal.setIioOrderEmbeddingToTypeOrd κ₁).injective)
      simpa [hasCardinalLT_iff_cardinal_mk_lt]
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
