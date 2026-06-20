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

lemma of_le {κ₁ κ₂ : Cardinal.{u}} [Fact κ₁.IsRegular] --[Fact κ₂.IsRegular]
    (h₀ : κ₁ ≤ κ₂) (hκ₂ : Cardinal.aleph0 ≤ κ₂) :
    letI : Fact (Cardinal.IsRegular (Order.succ (2 ^ κ₂))) :=
      ⟨isRegular_succ (hκ₂.trans (cantor _).le)⟩
    SharplyLT κ₁ (Order.succ (2 ^ κ₂)) := by
  letI : Fact (Cardinal.IsRegular (Order.succ (2 ^ κ₂))) :=
    ⟨isRegular_succ (hκ₂.trans (cantor _).le)⟩
  refine of_pow_lt ?_ (fun α β hα hβ ↦ ?_)
  · simp only [Order.lt_succ_iff]
    exact h₀.trans (cantor _).le
  · simp only [Order.lt_succ_iff] at hβ ⊢
    refine (power_le_power_right hβ).trans ?_
    rw [← power_mul]
    refine power_le_power_left (by simp) ?_
    conv_rhs => rw [← mul_eq_self hκ₂]
    exact mul_le_mul_right (hα.le.trans h₀) _

-- to be moved
lemma _root_.Cardinal.exists_le_of_small {ι : Type*} [Small.{u} ι]
    (κ : ι → Cardinal.{u}) :
    ∃ (κ' : Cardinal.{u}), ∀ (i : ι), κ i ≤ κ' := by
  let T (i : Shrink.{u} ι) : Type u := (κ ((equivShrink _).symm i)).ord.ToType
  refine ⟨Cardinal.mk (Sigma T), fun i ↦ ?_⟩
  obtain ⟨i, rfl⟩ := (equivShrink.{u} _).symm.surjective i
  simpa [T] using Cardinal.mk_le_of_injective
    (sigma_mk_injective (β := fun i ↦ (κ ((equivShrink _).symm i)).ord.ToType))

lemma exists_of_small {ι : Type*} [Small.{u} ι] (κ : ι → Cardinal.{u})
    [∀ i, Fact (κ i).IsRegular] :
    ∃ (κ' : Cardinal.{u}) (_ : Fact κ'.IsRegular),
      ∀ i, SharplyLT (κ i) κ' := by
  obtain ⟨κ₀, hκ₀, h⟩ :
      ∃ (κ₀ : Cardinal.{u}), Cardinal.aleph0 ≤ κ₀ ∧ ∀ (i : ι), κ i ≤ κ₀ := by
    obtain ⟨κ', h⟩ := Cardinal.exists_le_of_small κ
    exact ⟨max κ' .aleph0, by simp, fun i ↦ (h i).trans (by simp)⟩
  exact ⟨Order.succ (2 ^ κ₀), ⟨isRegular_succ (hκ₀.trans (cantor _).le)⟩,
    fun i ↦ of_le (h i) hκ₀⟩

lemma exists_of_pair (κ₁ κ₂ : Cardinal.{u})
    [Fact κ₁.IsRegular] [Fact κ₂.IsRegular] :
    ∃ (κ' : Cardinal.{u}) (_ : Fact κ'.IsRegular),
      SharplyLT κ₁ κ' ∧ SharplyLT κ₂ κ' := by
  let f (i : Fin 2) : Cardinal.{u} := match i with
    | 0 => κ₁
    | 1 => κ₂
  have (i : _) : Fact (f i).IsRegular := match i with
    | 0 => by assumption
    | 1 => by assumption
  obtain ⟨κ', _, h₂⟩ := exists_of_small f
  exact ⟨κ', inferInstance, h₂ 0, h₂ 1⟩

lemma exists_of_triple (κ₁ κ₂ κ₃ : Cardinal.{u})
    [Fact κ₁.IsRegular] [Fact κ₂.IsRegular] [Fact κ₃.IsRegular] :
    ∃ (κ' : Cardinal.{u}) (_ : Fact κ'.IsRegular),
      SharplyLT κ₁ κ' ∧ SharplyLT κ₂ κ' ∧ SharplyLT κ₃ κ':= by
  let f (i : Fin 3) : Cardinal.{u} := match i with
    | 0 => κ₁
    | 1 => κ₂
    | 2 => κ₃
  have (i : _) : Fact (f i).IsRegular := match i with
    | 0 => by assumption
    | 1 => by assumption
    | 2 => by assumption
  obtain ⟨κ', _, h₂⟩ := exists_of_small f
  exact ⟨κ', inferInstance, h₂ 0, h₂ 1, h₂ 2⟩

end Cardinal.SharplyLT
