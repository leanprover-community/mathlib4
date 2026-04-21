/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Limits.Final

/-! # Properties of the truncated simplex category

We prove that for `n > 0`, the inclusion functor from the `n`-truncated simplex category to the
untruncated simplex category, and the inclusion functor from the `n`-truncated to the `m`-truncated
simplex category, for `n ≤ m` are initial.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open Simplicial CategoryTheory

namespace SimplexCategory.Truncated

instance {d : ℕ} {n m : Truncated d} : DecidableEq (n ⟶ m) := fun a b =>
  decidable_of_iff (a.hom.toOrderHom = b.hom.toOrderHom) (by cat_disch)

/-- For `0 < n`, the inclusion functor from the `n`-truncated simplex category to the untruncated
simplex category is initial. -/
instance initial_inclusion {n : ℕ} [NeZero n] : (inclusion n).Initial := by
  have := Nat.pos_of_neZero n
  constructor
  intro Δ
  have : Nonempty (CostructuredArrow (inclusion n) Δ) := ⟨⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ 0 ⟩⟩
  apply zigzag_isConnected
  rintro ⟨⟨Δ₁, hΔ₁⟩, ⟨⟨⟩⟩, f⟩ ⟨⟨Δ₂, hΔ₂⟩, ⟨⟨⟩⟩, f'⟩
  apply Zigzag.trans (j₂ := ⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ (f 0)⟩)
    (.of_inv <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0)
  by_cases hff' : f 0 ≤ f' 0
  · trans ⟨⦋1⦌ₙ, ⟨⟨⟩⟩, mkOfLe (n := Δ.len) (f 0) (f' 0) hff'⟩
    · apply Zigzag.of_hom <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0
    · trans ⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ (f' 0)⟩
      · apply Zigzag.of_inv <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 1
      · apply Zigzag.of_hom <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0
  · trans ⟨⦋1⦌ₙ, ⟨⟨⟩⟩, mkOfLe (n := Δ.len) (f' 0) (f 0) (le_of_not_ge hff')⟩
    · apply Zigzag.of_hom <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 1
    · trans ⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ (f' 0)⟩
      · apply Zigzag.of_inv <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0
      · apply Zigzag.of_hom <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0

/-- For `0 < n ≤ m`, the inclusion functor from the `n`-truncated simplex category to the
`m`-truncated simplex category is initial. -/
theorem initial_incl {n m : ℕ} [NeZero n] (hm : n ≤ m) : (incl n m).Initial := by
  have : (incl n m hm ⋙ inclusion m).Initial :=
    Functor.initial_of_natIso (inclCompInclusion (by lia)).symm
  apply Functor.initial_of_comp_full_faithful _ (inclusion m)

/-- Abbreviation for face maps in the `n`-truncated simplex category. -/
abbrev δ (m : Nat) {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide) :
  (⟨⦋n⦌, hn⟩ : SimplexCategory.Truncated m) ⟶ ⟨⦋n + 1⦌, hn'⟩ := Hom.tr (SimplexCategory.δ i)

/-- Abbreviation for degeneracy maps in the `n`-truncated simplex category. -/
abbrev σ (m : Nat) {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide) :
    (⟨⦋n + 1⦌, hn⟩ : SimplexCategory.Truncated m) ⟶ ⟨⦋n⦌, hn'⟩ := Hom.tr (SimplexCategory.σ i)

section Two

/-- Abbreviation for face maps in the 2-truncated simplex category. -/
abbrev δ₂ {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide) := δ 2 i hn hn'

/-- Abbreviation for face maps in the 2-truncated simplex category. -/
abbrev σ₂ {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide) := σ 2 i hn hn'

@[reassoc (attr := simp)]
lemma δ₂_zero_comp_σ₂_zero {n} (hn := by decide) (hn' := by decide) :
    δ₂ (n := n) 0 hn hn' ≫ σ₂ 0 hn' hn = 𝟙 _ :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_self)

@[reassoc]
lemma δ₂_zero_comp_σ₂_one : δ₂ (0 : Fin 3) ≫ σ₂ 1 = σ₂ 0 ≫ δ₂ 0 :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_of_le (i := 0) (j := 0) (Fin.zero_le _))

@[reassoc (attr := simp)]
lemma δ₂_one_comp_σ₂_zero {n} (hn := by decide) (hn' := by decide) :
    δ₂ (n := n) 1 hn hn' ≫ σ₂ 0 hn' hn = 𝟙 _ :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_succ)

@[reassoc (attr := simp)]
lemma δ₂_one_comp_σ₂_one {n} (hn := by decide) (hn' := by decide) :
    δ₂ (n := n + 1) 1 hn hn' ≫ σ₂ 1 hn' hn = 𝟙 _ :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_self (n := n + 1) (i := 1))

@[reassoc (attr := simp)]
lemma δ₂_two_comp_σ₂_one : δ₂ (2 : Fin 3) ≫ σ₂ 1 = 𝟙 _ :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_succ' (by decide))

@[reassoc]
lemma δ₂_two_comp_σ₂_zero : δ₂ (2 : Fin 3) ≫ σ₂ 0 = σ₂ 0 ≫ δ₂ 1 :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_of_gt' (by decide))

lemma δ₂_one_eq_const : δ₂ (1 : Fin 2) = Hom.tr (const _ _ 0) := by decide

lemma δ₂_zero_eq_const : δ₂ (0 : Fin 2) = Hom.tr (const _ _ 1) := by decide

@[reassoc]
lemma δ₂_zero_comp_δ₂_two : δ₂ (0 : Fin 2) ≫ δ₂ 2 = δ₂ 1 ≫ δ₂ 0 := by decide

end Two

end SimplexCategory.Truncated
