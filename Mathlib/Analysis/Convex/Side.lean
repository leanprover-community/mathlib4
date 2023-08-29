/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.Normed.Group.AddTorsor

#align_import analysis.convex.side from "leanprover-community/mathlib"@"a63928c34ec358b5edcda2bf7513c50052a5230f"

/-!
# Sides of affine subspaces

This file defines notions of two points being on the same or opposite sides of an affine subspace.

## Main definitions

* `s.WSameSide x y`: The points `x` and `y` are weakly on the same side of the affine
  subspace `s`.
* `s.SSameSide x y`: The points `x` and `y` are strictly on the same side of the affine
  subspace `s`.
* `s.WOppSide x y`: The points `x` and `y` are weakly on opposite sides of the affine
  subspace `s`.
* `s.SOppSide x y`: The points `x` and `y` are strictly on opposite sides of the affine
  subspace `s`.

-/


variable {R V V' P P' : Type*}

open AffineEquiv AffineMap

namespace AffineSubspace

section StrictOrderedCommRing

variable [StrictOrderedCommRing R] [AddCommGroup V] [Module R V] [AddTorsor V P]

variable [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

/-- The points `x` and `y` are weakly on the same side of `s`. -/
def WSameSide (s : AffineSubspace R P) (x y : P) : Prop :=
  ∃ (p₁ : _) (_ : p₁ ∈ s) (p₂ : _) (_ : p₂ ∈ s), SameRay R (x -ᵥ p₁) (y -ᵥ p₂)
#align affine_subspace.w_same_side AffineSubspace.WSameSide

/-- The points `x` and `y` are strictly on the same side of `s`. -/
def SSameSide (s : AffineSubspace R P) (x y : P) : Prop :=
  s.WSameSide x y ∧ x ∉ s ∧ y ∉ s
#align affine_subspace.s_same_side AffineSubspace.SSameSide

/-- The points `x` and `y` are weakly on opposite sides of `s`. -/
def WOppSide (s : AffineSubspace R P) (x y : P) : Prop :=
  ∃ (p₁ : _) (_ : p₁ ∈ s) (p₂ : _) (_ : p₂ ∈ s), SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)
#align affine_subspace.w_opp_side AffineSubspace.WOppSide

/-- The points `x` and `y` are strictly on opposite sides of `s`. -/
def SOppSide (s : AffineSubspace R P) (x y : P) : Prop :=
  s.WOppSide x y ∧ x ∉ s ∧ y ∉ s
#align affine_subspace.s_opp_side AffineSubspace.SOppSide

theorem WSameSide.map {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) (f : P →ᵃ[R] P') :
    (s.map f).WSameSide (f x) (f y) := by
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h⟩
  -- ⊢ WSameSide (AffineSubspace.map f s) (↑f x) (↑f y)
  refine' ⟨f p₁, mem_map_of_mem f hp₁, f p₂, mem_map_of_mem f hp₂, _⟩
  -- ⊢ SameRay R (↑f x -ᵥ ↑f p₁) (↑f y -ᵥ ↑f p₂)
  simp_rw [← linearMap_vsub]
  -- ⊢ SameRay R (↑f.linear (x -ᵥ p₁)) (↑f.linear (y -ᵥ p₂))
  exact h.map f.linear
  -- 🎉 no goals
#align affine_subspace.w_same_side.map AffineSubspace.WSameSide.map

theorem _root_.Function.Injective.wSameSide_map_iff {s : AffineSubspace R P} {x y : P}
    {f : P →ᵃ[R] P'} (hf : Function.Injective f) :
    (s.map f).WSameSide (f x) (f y) ↔ s.WSameSide x y := by
  refine' ⟨fun h => _, fun h => h.map _⟩
  -- ⊢ WSameSide s x y
  rcases h with ⟨fp₁, hfp₁, fp₂, hfp₂, h⟩
  -- ⊢ WSameSide s x y
  rw [mem_map] at hfp₁ hfp₂
  -- ⊢ WSameSide s x y
  rcases hfp₁ with ⟨p₁, hp₁, rfl⟩
  -- ⊢ WSameSide s x y
  rcases hfp₂ with ⟨p₂, hp₂, rfl⟩
  -- ⊢ WSameSide s x y
  refine' ⟨p₁, hp₁, p₂, hp₂, _⟩
  -- ⊢ SameRay R (x -ᵥ p₁) (y -ᵥ p₂)
  simp_rw [← linearMap_vsub, (f.linear_injective_iff.2 hf).sameRay_map_iff] at h
  -- ⊢ SameRay R (x -ᵥ p₁) (y -ᵥ p₂)
  exact h
  -- 🎉 no goals
#align function.injective.w_same_side_map_iff Function.Injective.wSameSide_map_iff

theorem _root_.Function.Injective.sSameSide_map_iff {s : AffineSubspace R P} {x y : P}
    {f : P →ᵃ[R] P'} (hf : Function.Injective f) :
    (s.map f).SSameSide (f x) (f y) ↔ s.SSameSide x y := by
  simp_rw [SSameSide, hf.wSameSide_map_iff, mem_map_iff_mem_of_injective hf]
  -- 🎉 no goals
#align function.injective.s_same_side_map_iff Function.Injective.sSameSide_map_iff

@[simp]
theorem _root_.AffineEquiv.wSameSide_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).WSameSide (f x) (f y) ↔ s.WSameSide x y :=
  (show Function.Injective f.toAffineMap from f.injective).wSameSide_map_iff
#align affine_equiv.w_same_side_map_iff AffineEquiv.wSameSide_map_iff

@[simp]
theorem _root_.AffineEquiv.sSameSide_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).SSameSide (f x) (f y) ↔ s.SSameSide x y :=
  (show Function.Injective f.toAffineMap from f.injective).sSameSide_map_iff
#align affine_equiv.s_same_side_map_iff AffineEquiv.sSameSide_map_iff

theorem WOppSide.map {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y) (f : P →ᵃ[R] P') :
    (s.map f).WOppSide (f x) (f y) := by
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h⟩
  -- ⊢ WOppSide (AffineSubspace.map f s) (↑f x) (↑f y)
  refine' ⟨f p₁, mem_map_of_mem f hp₁, f p₂, mem_map_of_mem f hp₂, _⟩
  -- ⊢ SameRay R (↑f x -ᵥ ↑f p₁) (↑f p₂ -ᵥ ↑f y)
  simp_rw [← linearMap_vsub]
  -- ⊢ SameRay R (↑f.linear (x -ᵥ p₁)) (↑f.linear (p₂ -ᵥ y))
  exact h.map f.linear
  -- 🎉 no goals
#align affine_subspace.w_opp_side.map AffineSubspace.WOppSide.map

theorem _root_.Function.Injective.wOppSide_map_iff {s : AffineSubspace R P} {x y : P}
    {f : P →ᵃ[R] P'} (hf : Function.Injective f) :
    (s.map f).WOppSide (f x) (f y) ↔ s.WOppSide x y := by
  refine' ⟨fun h => _, fun h => h.map _⟩
  -- ⊢ WOppSide s x y
  rcases h with ⟨fp₁, hfp₁, fp₂, hfp₂, h⟩
  -- ⊢ WOppSide s x y
  rw [mem_map] at hfp₁ hfp₂
  -- ⊢ WOppSide s x y
  rcases hfp₁ with ⟨p₁, hp₁, rfl⟩
  -- ⊢ WOppSide s x y
  rcases hfp₂ with ⟨p₂, hp₂, rfl⟩
  -- ⊢ WOppSide s x y
  refine' ⟨p₁, hp₁, p₂, hp₂, _⟩
  -- ⊢ SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)
  simp_rw [← linearMap_vsub, (f.linear_injective_iff.2 hf).sameRay_map_iff] at h
  -- ⊢ SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)
  exact h
  -- 🎉 no goals
#align function.injective.w_opp_side_map_iff Function.Injective.wOppSide_map_iff

theorem _root_.Function.Injective.sOppSide_map_iff {s : AffineSubspace R P} {x y : P}
    {f : P →ᵃ[R] P'} (hf : Function.Injective f) :
    (s.map f).SOppSide (f x) (f y) ↔ s.SOppSide x y := by
  simp_rw [SOppSide, hf.wOppSide_map_iff, mem_map_iff_mem_of_injective hf]
  -- 🎉 no goals
#align function.injective.s_opp_side_map_iff Function.Injective.sOppSide_map_iff

@[simp]
theorem _root_.AffineEquiv.wOppSide_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).WOppSide (f x) (f y) ↔ s.WOppSide x y :=
  (show Function.Injective f.toAffineMap from f.injective).wOppSide_map_iff
#align affine_equiv.w_opp_side_map_iff AffineEquiv.wOppSide_map_iff

@[simp]
theorem _root_.AffineEquiv.sOppSide_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).SOppSide (f x) (f y) ↔ s.SOppSide x y :=
  (show Function.Injective f.toAffineMap from f.injective).sOppSide_map_iff
#align affine_equiv.s_opp_side_map_iff AffineEquiv.sOppSide_map_iff

theorem WSameSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.choose, h.choose_spec.choose⟩
#align affine_subspace.w_same_side.nonempty AffineSubspace.WSameSide.nonempty

theorem SSameSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.1.choose, h.1.choose_spec.choose⟩
#align affine_subspace.s_same_side.nonempty AffineSubspace.SSameSide.nonempty

theorem WOppSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.choose, h.choose_spec.choose⟩
#align affine_subspace.w_opp_side.nonempty AffineSubspace.WOppSide.nonempty

theorem SOppSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.1.choose, h.1.choose_spec.choose⟩
#align affine_subspace.s_opp_side.nonempty AffineSubspace.SOppSide.nonempty

theorem SSameSide.wSameSide {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    s.WSameSide x y :=
  h.1
#align affine_subspace.s_same_side.w_same_side AffineSubspace.SSameSide.wSameSide

theorem SSameSide.left_not_mem {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) : x ∉ s :=
  h.2.1
#align affine_subspace.s_same_side.left_not_mem AffineSubspace.SSameSide.left_not_mem

theorem SSameSide.right_not_mem {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) : y ∉ s :=
  h.2.2
#align affine_subspace.s_same_side.right_not_mem AffineSubspace.SSameSide.right_not_mem

theorem SOppSide.wOppSide {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    s.WOppSide x y :=
  h.1
#align affine_subspace.s_opp_side.w_opp_side AffineSubspace.SOppSide.wOppSide

theorem SOppSide.left_not_mem {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) : x ∉ s :=
  h.2.1
#align affine_subspace.s_opp_side.left_not_mem AffineSubspace.SOppSide.left_not_mem

theorem SOppSide.right_not_mem {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) : y ∉ s :=
  h.2.2
#align affine_subspace.s_opp_side.right_not_mem AffineSubspace.SOppSide.right_not_mem

theorem wSameSide_comm {s : AffineSubspace R P} {x y : P} : s.WSameSide x y ↔ s.WSameSide y x :=
  ⟨fun ⟨p₁, hp₁, p₂, hp₂, h⟩ => ⟨p₂, hp₂, p₁, hp₁, h.symm⟩,
    fun ⟨p₁, hp₁, p₂, hp₂, h⟩ => ⟨p₂, hp₂, p₁, hp₁, h.symm⟩⟩
#align affine_subspace.w_same_side_comm AffineSubspace.wSameSide_comm

alias ⟨WSameSide.symm, _⟩ := wSameSide_comm
#align affine_subspace.w_same_side.symm AffineSubspace.WSameSide.symm

theorem sSameSide_comm {s : AffineSubspace R P} {x y : P} : s.SSameSide x y ↔ s.SSameSide y x := by
  rw [SSameSide, SSameSide, wSameSide_comm, and_comm (b := x ∉ s)]
  -- 🎉 no goals
#align affine_subspace.s_same_side_comm AffineSubspace.sSameSide_comm

alias ⟨SSameSide.symm, _⟩ := sSameSide_comm
#align affine_subspace.s_same_side.symm AffineSubspace.SSameSide.symm

theorem wOppSide_comm {s : AffineSubspace R P} {x y : P} : s.WOppSide x y ↔ s.WOppSide y x := by
  constructor
  -- ⊢ WOppSide s x y → WOppSide s y x
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    -- ⊢ WOppSide s y x
    refine' ⟨p₂, hp₂, p₁, hp₁, _⟩
    -- ⊢ SameRay R (y -ᵥ p₂) (p₁ -ᵥ x)
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
    -- 🎉 no goals
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    -- ⊢ WOppSide s x y
    refine' ⟨p₂, hp₂, p₁, hp₁, _⟩
    -- ⊢ SameRay R (x -ᵥ p₂) (p₁ -ᵥ y)
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
    -- 🎉 no goals
#align affine_subspace.w_opp_side_comm AffineSubspace.wOppSide_comm

alias ⟨WOppSide.symm, _⟩ := wOppSide_comm
#align affine_subspace.w_opp_side.symm AffineSubspace.WOppSide.symm

theorem sOppSide_comm {s : AffineSubspace R P} {x y : P} : s.SOppSide x y ↔ s.SOppSide y x := by
  rw [SOppSide, SOppSide, wOppSide_comm, and_comm (b := x ∉ s)]
  -- 🎉 no goals
#align affine_subspace.s_opp_side_comm AffineSubspace.sOppSide_comm

alias ⟨SOppSide.symm, _⟩ := sOppSide_comm
#align affine_subspace.s_opp_side.symm AffineSubspace.SOppSide.symm

theorem not_wSameSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).WSameSide x y :=
  fun ⟨_, h, _⟩ => h.elim
#align affine_subspace.not_w_same_side_bot AffineSubspace.not_wSameSide_bot

theorem not_sSameSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).SSameSide x y :=
  fun h => not_wSameSide_bot x y h.wSameSide
#align affine_subspace.not_s_same_side_bot AffineSubspace.not_sSameSide_bot

theorem not_wOppSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).WOppSide x y :=
  fun ⟨_, h, _⟩ => h.elim
#align affine_subspace.not_w_opp_side_bot AffineSubspace.not_wOppSide_bot

theorem not_sOppSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).SOppSide x y :=
  fun h => not_wOppSide_bot x y h.wOppSide
#align affine_subspace.not_s_opp_side_bot AffineSubspace.not_sOppSide_bot

@[simp]
theorem wSameSide_self_iff {s : AffineSubspace R P} {x : P} :
    s.WSameSide x x ↔ (s : Set P).Nonempty :=
  ⟨fun h => h.nonempty, fun ⟨p, hp⟩ => ⟨p, hp, p, hp, SameRay.rfl⟩⟩
#align affine_subspace.w_same_side_self_iff AffineSubspace.wSameSide_self_iff

theorem sSameSide_self_iff {s : AffineSubspace R P} {x : P} :
    s.SSameSide x x ↔ (s : Set P).Nonempty ∧ x ∉ s :=
  ⟨fun ⟨h, hx, _⟩ => ⟨wSameSide_self_iff.1 h, hx⟩, fun ⟨h, hx⟩ => ⟨wSameSide_self_iff.2 h, hx, hx⟩⟩
#align affine_subspace.s_same_side_self_iff AffineSubspace.sSameSide_self_iff

theorem wSameSide_of_left_mem {s : AffineSubspace R P} {x : P} (y : P) (hx : x ∈ s) :
    s.WSameSide x y := by
  refine' ⟨x, hx, x, hx, _⟩
  -- ⊢ SameRay R (x -ᵥ x) (y -ᵥ x)
  rw [vsub_self]
  -- ⊢ SameRay R 0 (y -ᵥ x)
  apply SameRay.zero_left
  -- 🎉 no goals
#align affine_subspace.w_same_side_of_left_mem AffineSubspace.wSameSide_of_left_mem

theorem wSameSide_of_right_mem {s : AffineSubspace R P} (x : P) {y : P} (hy : y ∈ s) :
    s.WSameSide x y :=
  (wSameSide_of_left_mem x hy).symm
#align affine_subspace.w_same_side_of_right_mem AffineSubspace.wSameSide_of_right_mem

theorem wOppSide_of_left_mem {s : AffineSubspace R P} {x : P} (y : P) (hx : x ∈ s) :
    s.WOppSide x y := by
  refine' ⟨x, hx, x, hx, _⟩
  -- ⊢ SameRay R (x -ᵥ x) (x -ᵥ y)
  rw [vsub_self]
  -- ⊢ SameRay R 0 (x -ᵥ y)
  apply SameRay.zero_left
  -- 🎉 no goals
#align affine_subspace.w_opp_side_of_left_mem AffineSubspace.wOppSide_of_left_mem

theorem wOppSide_of_right_mem {s : AffineSubspace R P} (x : P) {y : P} (hy : y ∈ s) :
    s.WOppSide x y :=
  (wOppSide_of_left_mem x hy).symm
#align affine_subspace.w_opp_side_of_right_mem AffineSubspace.wOppSide_of_right_mem

theorem wSameSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.WSameSide (v +ᵥ x) y ↔ s.WSameSide x y := by
  constructor
  -- ⊢ WSameSide s (v +ᵥ x) y → WSameSide s x y
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    -- ⊢ WSameSide s x y
    refine'
      ⟨-v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) hp₁, p₂, hp₂, _⟩
    rwa [vsub_vadd_eq_vsub_sub, sub_neg_eq_add, add_comm, ← vadd_vsub_assoc]
    -- 🎉 no goals
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    -- ⊢ WSameSide s (v +ᵥ x) y
    refine' ⟨v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction hv hp₁, p₂, hp₂, _⟩
    -- ⊢ SameRay R (v +ᵥ x -ᵥ (v +ᵥ p₁)) (y -ᵥ p₂)
    rwa [vadd_vsub_vadd_cancel_left]
    -- 🎉 no goals
#align affine_subspace.w_same_side_vadd_left_iff AffineSubspace.wSameSide_vadd_left_iff

theorem wSameSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.WSameSide x (v +ᵥ y) ↔ s.WSameSide x y := by
  rw [wSameSide_comm, wSameSide_vadd_left_iff hv, wSameSide_comm]
  -- 🎉 no goals
#align affine_subspace.w_same_side_vadd_right_iff AffineSubspace.wSameSide_vadd_right_iff

theorem sSameSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.SSameSide (v +ᵥ x) y ↔ s.SSameSide x y := by
  rw [SSameSide, SSameSide, wSameSide_vadd_left_iff hv, vadd_mem_iff_mem_of_mem_direction hv]
  -- 🎉 no goals
#align affine_subspace.s_same_side_vadd_left_iff AffineSubspace.sSameSide_vadd_left_iff

theorem sSameSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.SSameSide x (v +ᵥ y) ↔ s.SSameSide x y := by
  rw [sSameSide_comm, sSameSide_vadd_left_iff hv, sSameSide_comm]
  -- 🎉 no goals
#align affine_subspace.s_same_side_vadd_right_iff AffineSubspace.sSameSide_vadd_right_iff

theorem wOppSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.WOppSide (v +ᵥ x) y ↔ s.WOppSide x y := by
  constructor
  -- ⊢ WOppSide s (v +ᵥ x) y → WOppSide s x y
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    -- ⊢ WOppSide s x y
    refine'
      ⟨-v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) hp₁, p₂, hp₂, _⟩
    rwa [vsub_vadd_eq_vsub_sub, sub_neg_eq_add, add_comm, ← vadd_vsub_assoc]
    -- 🎉 no goals
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    -- ⊢ WOppSide s (v +ᵥ x) y
    refine' ⟨v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction hv hp₁, p₂, hp₂, _⟩
    -- ⊢ SameRay R (v +ᵥ x -ᵥ (v +ᵥ p₁)) (p₂ -ᵥ y)
    rwa [vadd_vsub_vadd_cancel_left]
    -- 🎉 no goals
#align affine_subspace.w_opp_side_vadd_left_iff AffineSubspace.wOppSide_vadd_left_iff

theorem wOppSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.WOppSide x (v +ᵥ y) ↔ s.WOppSide x y := by
  rw [wOppSide_comm, wOppSide_vadd_left_iff hv, wOppSide_comm]
  -- 🎉 no goals
#align affine_subspace.w_opp_side_vadd_right_iff AffineSubspace.wOppSide_vadd_right_iff

theorem sOppSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.SOppSide (v +ᵥ x) y ↔ s.SOppSide x y := by
  rw [SOppSide, SOppSide, wOppSide_vadd_left_iff hv, vadd_mem_iff_mem_of_mem_direction hv]
  -- 🎉 no goals
#align affine_subspace.s_opp_side_vadd_left_iff AffineSubspace.sOppSide_vadd_left_iff

theorem sOppSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.SOppSide x (v +ᵥ y) ↔ s.SOppSide x y := by
  rw [sOppSide_comm, sOppSide_vadd_left_iff hv, sOppSide_comm]
  -- 🎉 no goals
#align affine_subspace.s_opp_side_vadd_right_iff AffineSubspace.sOppSide_vadd_right_iff

theorem wSameSide_smul_vsub_vadd_left {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : 0 ≤ t) : s.WSameSide (t • (x -ᵥ p₁) +ᵥ p₂) x := by
  refine' ⟨p₂, hp₂, p₁, hp₁, _⟩
  -- ⊢ SameRay R (t • (x -ᵥ p₁) +ᵥ p₂ -ᵥ p₂) (x -ᵥ p₁)
  rw [vadd_vsub]
  -- ⊢ SameRay R (t • (x -ᵥ p₁)) (x -ᵥ p₁)
  exact SameRay.sameRay_nonneg_smul_left _ ht
  -- 🎉 no goals
#align affine_subspace.w_same_side_smul_vsub_vadd_left AffineSubspace.wSameSide_smul_vsub_vadd_left

theorem wSameSide_smul_vsub_vadd_right {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : 0 ≤ t) : s.WSameSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (wSameSide_smul_vsub_vadd_left x hp₁ hp₂ ht).symm
#align affine_subspace.w_same_side_smul_vsub_vadd_right AffineSubspace.wSameSide_smul_vsub_vadd_right

theorem wSameSide_lineMap_left {s : AffineSubspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
    (ht : 0 ≤ t) : s.WSameSide (lineMap x y t) y :=
  wSameSide_smul_vsub_vadd_left y h h ht
#align affine_subspace.w_same_side_line_map_left AffineSubspace.wSameSide_lineMap_left

theorem wSameSide_lineMap_right {s : AffineSubspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
    (ht : 0 ≤ t) : s.WSameSide y (lineMap x y t) :=
  (wSameSide_lineMap_left y h ht).symm
#align affine_subspace.w_same_side_line_map_right AffineSubspace.wSameSide_lineMap_right

theorem wOppSide_smul_vsub_vadd_left {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : t ≤ 0) : s.WOppSide (t • (x -ᵥ p₁) +ᵥ p₂) x := by
  refine' ⟨p₂, hp₂, p₁, hp₁, _⟩
  -- ⊢ SameRay R (t • (x -ᵥ p₁) +ᵥ p₂ -ᵥ p₂) (p₁ -ᵥ x)
  rw [vadd_vsub, ← neg_neg t, neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]
  -- ⊢ SameRay R (-t • (p₁ -ᵥ x)) (p₁ -ᵥ x)
  exact SameRay.sameRay_nonneg_smul_left _ (neg_nonneg.2 ht)
  -- 🎉 no goals
#align affine_subspace.w_opp_side_smul_vsub_vadd_left AffineSubspace.wOppSide_smul_vsub_vadd_left

theorem wOppSide_smul_vsub_vadd_right {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : t ≤ 0) : s.WOppSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (wOppSide_smul_vsub_vadd_left x hp₁ hp₂ ht).symm
#align affine_subspace.w_opp_side_smul_vsub_vadd_right AffineSubspace.wOppSide_smul_vsub_vadd_right

theorem wOppSide_lineMap_left {s : AffineSubspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
    (ht : t ≤ 0) : s.WOppSide (lineMap x y t) y :=
  wOppSide_smul_vsub_vadd_left y h h ht
#align affine_subspace.w_opp_side_line_map_left AffineSubspace.wOppSide_lineMap_left

theorem wOppSide_lineMap_right {s : AffineSubspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
    (ht : t ≤ 0) : s.WOppSide y (lineMap x y t) :=
  (wOppSide_lineMap_left y h ht).symm
#align affine_subspace.w_opp_side_line_map_right AffineSubspace.wOppSide_lineMap_right

theorem _root_.Wbtw.wSameSide₂₃ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hx : x ∈ s) : s.WSameSide y z := by
  rcases h with ⟨t, ⟨ht0, -⟩, rfl⟩
  -- ⊢ WSameSide s (↑(lineMap x z) t) z
  exact wSameSide_lineMap_left z hx ht0
  -- 🎉 no goals
#align wbtw.w_same_side₂₃ Wbtw.wSameSide₂₃

theorem _root_.Wbtw.wSameSide₃₂ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hx : x ∈ s) : s.WSameSide z y :=
  (h.wSameSide₂₃ hx).symm
#align wbtw.w_same_side₃₂ Wbtw.wSameSide₃₂

theorem _root_.Wbtw.wSameSide₁₂ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hz : z ∈ s) : s.WSameSide x y :=
  h.symm.wSameSide₃₂ hz
#align wbtw.w_same_side₁₂ Wbtw.wSameSide₁₂

theorem _root_.Wbtw.wSameSide₂₁ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hz : z ∈ s) : s.WSameSide y x :=
  h.symm.wSameSide₂₃ hz
#align wbtw.w_same_side₂₁ Wbtw.wSameSide₂₁

theorem _root_.Wbtw.wOppSide₁₃ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hy : y ∈ s) : s.WOppSide x z := by
  rcases h with ⟨t, ⟨ht0, ht1⟩, rfl⟩
  -- ⊢ WOppSide s x z
  refine' ⟨_, hy, _, hy, _⟩
  -- ⊢ SameRay R (x -ᵥ ↑(lineMap x z) t) (↑(lineMap x z) t -ᵥ z)
  rcases ht1.lt_or_eq with (ht1' | rfl); swap
  -- ⊢ SameRay R (x -ᵥ ↑(lineMap x z) t) (↑(lineMap x z) t -ᵥ z)
                                         -- ⊢ SameRay R (x -ᵥ ↑(lineMap x z) 1) (↑(lineMap x z) 1 -ᵥ z)
  · rw [lineMap_apply_one]; simp
    -- ⊢ SameRay R (x -ᵥ z) (z -ᵥ z)
                            -- 🎉 no goals
  rcases ht0.lt_or_eq with (ht0' | rfl); swap
  -- ⊢ SameRay R (x -ᵥ ↑(lineMap x z) t) (↑(lineMap x z) t -ᵥ z)
                                         -- ⊢ SameRay R (x -ᵥ ↑(lineMap x z) 0) (↑(lineMap x z) 0 -ᵥ z)
  · rw [lineMap_apply_zero]; simp
    -- ⊢ SameRay R (x -ᵥ x) (x -ᵥ z)
                             -- 🎉 no goals
  refine' Or.inr (Or.inr ⟨1 - t, t, sub_pos.2 ht1', ht0', _⟩)
  -- ⊢ (1 - t) • (x -ᵥ ↑(lineMap x z) t) = t • (↑(lineMap x z) t -ᵥ z)
  -- TODO: after lean4#2336 "simp made no progress feature"
  -- had to add `_` to several lemmas here. Not sure why!
  simp_rw [lineMap_apply _, vadd_vsub_assoc _, vsub_vadd_eq_vsub_sub _,
    ← neg_vsub_eq_vsub_rev z x, vsub_self _, zero_sub, ← neg_one_smul R (z -ᵥ x),
    ← add_smul, smul_neg, ← neg_smul, smul_smul]
  ring_nf
  -- 🎉 no goals
#align wbtw.w_opp_side₁₃ Wbtw.wOppSide₁₃

theorem _root_.Wbtw.wOppSide₃₁ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hy : y ∈ s) : s.WOppSide z x :=
  h.symm.wOppSide₁₃ hy
#align wbtw.w_opp_side₃₁ Wbtw.wOppSide₃₁

end StrictOrderedCommRing

section LinearOrderedField

variable [LinearOrderedField R] [AddCommGroup V] [Module R V] [AddTorsor V P]

variable [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

@[simp]
theorem wOppSide_self_iff {s : AffineSubspace R P} {x : P} : s.WOppSide x x ↔ x ∈ s := by
  constructor
  -- ⊢ WOppSide s x x → x ∈ s
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    -- ⊢ x ∈ s
    obtain ⟨a, -, -, -, -, h₁, -⟩ := h.exists_eq_smul_add
    -- ⊢ x ∈ s
    rw [add_comm, vsub_add_vsub_cancel, ← eq_vadd_iff_vsub_eq] at h₁
    -- ⊢ x ∈ s
    rw [h₁]
    -- ⊢ a • (p₂ -ᵥ p₁) +ᵥ p₁ ∈ s
    exact s.smul_vsub_vadd_mem a hp₂ hp₁ hp₁
    -- 🎉 no goals
  · exact fun h => ⟨x, h, x, h, SameRay.rfl⟩
    -- 🎉 no goals
#align affine_subspace.w_opp_side_self_iff AffineSubspace.wOppSide_self_iff

theorem not_sOppSide_self (s : AffineSubspace R P) (x : P) : ¬s.SOppSide x x := by
  rw [SOppSide]
  -- ⊢ ¬(WOppSide s x x ∧ ¬x ∈ s ∧ ¬x ∈ s)
  simp
  -- 🎉 no goals
#align affine_subspace.not_s_opp_side_self AffineSubspace.not_sOppSide_self

theorem wSameSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
    s.WSameSide x y ↔ x ∈ s ∨ ∃ p₂ ∈ s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) := by
  constructor
  -- ⊢ WSameSide s x y → x ∈ s ∨ ∃ p₂, p₂ ∈ s ∧ SameRay R (x -ᵥ p₁) (y -ᵥ p₂)
  · rintro ⟨p₁', hp₁', p₂', hp₂', h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hr⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h0
      -- ⊢ x ∈ s ∨ ∃ p₂, p₂ ∈ s ∧ SameRay R (x -ᵥ p₁) (y -ᵥ p₂)
      rw [h0]
      -- ⊢ p₁' ∈ s ∨ ∃ p₂, p₂ ∈ s ∧ SameRay R (p₁' -ᵥ p₁) (y -ᵥ p₂)
      exact Or.inl hp₁'
      -- 🎉 no goals
    · refine' Or.inr ⟨p₂', hp₂', _⟩
      -- ⊢ SameRay R (x -ᵥ p₁) (y -ᵥ p₂')
      rw [h0]
      -- ⊢ SameRay R (x -ᵥ p₁) 0
      exact SameRay.zero_right _
      -- 🎉 no goals
    · refine' Or.inr ⟨(r₁ / r₂) • (p₁ -ᵥ p₁') +ᵥ p₂', s.smul_vsub_vadd_mem _ h hp₁' hp₂',
        Or.inr (Or.inr ⟨r₁, r₂, hr₁, hr₂, _⟩)⟩
      rw [vsub_vadd_eq_vsub_sub, smul_sub, ← hr, smul_smul, mul_div_cancel' _ hr₂.ne.symm,
        ← smul_sub, vsub_sub_vsub_cancel_right]
  · rintro (h' | ⟨h₁, h₂, h₃⟩)
    -- ⊢ WSameSide s x y
    · exact wSameSide_of_left_mem y h'
      -- 🎉 no goals
    · exact ⟨p₁, h, h₁, h₂, h₃⟩
      -- 🎉 no goals
#align affine_subspace.w_same_side_iff_exists_left AffineSubspace.wSameSide_iff_exists_left

theorem wSameSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
    s.WSameSide x y ↔ y ∈ s ∨ ∃ p₁ ∈ s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) := by
  rw [wSameSide_comm, wSameSide_iff_exists_left h]
  -- ⊢ (y ∈ s ∨ ∃ p₂_1, p₂_1 ∈ s ∧ SameRay R (y -ᵥ p₂) (x -ᵥ p₂_1)) ↔ y ∈ s ∨ ∃ p₁, …
  simp_rw [SameRay.sameRay_comm]
  -- 🎉 no goals
#align affine_subspace.w_same_side_iff_exists_right AffineSubspace.wSameSide_iff_exists_right

theorem sSameSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
    s.SSameSide x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₂ ∈ s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) := by
  rw [SSameSide, and_comm, wSameSide_iff_exists_left h, and_assoc, and_congr_right_iff]
  -- ⊢ ¬x ∈ s → (¬y ∈ s ∧ (x ∈ s ∨ ∃ p₂, p₂ ∈ s ∧ SameRay R (x -ᵥ p₁) (y -ᵥ p₂)) ↔  …
  intro hx
  -- ⊢ ¬y ∈ s ∧ (x ∈ s ∨ ∃ p₂, p₂ ∈ s ∧ SameRay R (x -ᵥ p₁) (y -ᵥ p₂)) ↔ ¬y ∈ s ∧ ∃ …
  rw [or_iff_right hx]
  -- 🎉 no goals
#align affine_subspace.s_same_side_iff_exists_left AffineSubspace.sSameSide_iff_exists_left

theorem sSameSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
    s.SSameSide x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₁ ∈ s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) := by
  rw [sSameSide_comm, sSameSide_iff_exists_left h, ← and_assoc, and_comm (a := y ∉ s), and_assoc]
  -- ⊢ (¬x ∈ s ∧ ¬y ∈ s ∧ ∃ p₂_1, p₂_1 ∈ s ∧ SameRay R (y -ᵥ p₂) (x -ᵥ p₂_1)) ↔ ¬x  …
  simp_rw [SameRay.sameRay_comm]
  -- 🎉 no goals
#align affine_subspace.s_same_side_iff_exists_right AffineSubspace.sSameSide_iff_exists_right

theorem wOppSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
    s.WOppSide x y ↔ x ∈ s ∨ ∃ p₂ ∈ s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) := by
  constructor
  -- ⊢ WOppSide s x y → x ∈ s ∨ ∃ p₂, p₂ ∈ s ∧ SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)
  · rintro ⟨p₁', hp₁', p₂', hp₂', h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hr⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h0
      -- ⊢ x ∈ s ∨ ∃ p₂, p₂ ∈ s ∧ SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)
      rw [h0]
      -- ⊢ p₁' ∈ s ∨ ∃ p₂, p₂ ∈ s ∧ SameRay R (p₁' -ᵥ p₁) (p₂ -ᵥ y)
      exact Or.inl hp₁'
      -- 🎉 no goals
    · refine' Or.inr ⟨p₂', hp₂', _⟩
      -- ⊢ SameRay R (x -ᵥ p₁) (p₂' -ᵥ y)
      rw [h0]
      -- ⊢ SameRay R (x -ᵥ p₁) 0
      exact SameRay.zero_right _
      -- 🎉 no goals
    · refine' Or.inr ⟨(-r₁ / r₂) • (p₁ -ᵥ p₁') +ᵥ p₂', s.smul_vsub_vadd_mem _ h hp₁' hp₂',
        Or.inr (Or.inr ⟨r₁, r₂, hr₁, hr₂, _⟩)⟩
      rw [vadd_vsub_assoc, smul_add, ← hr, smul_smul, neg_div, mul_neg,
        mul_div_cancel' _ hr₂.ne.symm, neg_smul, neg_add_eq_sub, ← smul_sub,
        vsub_sub_vsub_cancel_right]
  · rintro (h' | ⟨h₁, h₂, h₃⟩)
    -- ⊢ WOppSide s x y
    · exact wOppSide_of_left_mem y h'
      -- 🎉 no goals
    · exact ⟨p₁, h, h₁, h₂, h₃⟩
      -- 🎉 no goals
#align affine_subspace.w_opp_side_iff_exists_left AffineSubspace.wOppSide_iff_exists_left

theorem wOppSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
    s.WOppSide x y ↔ y ∈ s ∨ ∃ p₁ ∈ s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) := by
  rw [wOppSide_comm, wOppSide_iff_exists_left h]
  -- ⊢ (y ∈ s ∨ ∃ p₂_1, p₂_1 ∈ s ∧ SameRay R (y -ᵥ p₂) (p₂_1 -ᵥ x)) ↔ y ∈ s ∨ ∃ p₁, …
  constructor
  -- ⊢ (y ∈ s ∨ ∃ p₂_1, p₂_1 ∈ s ∧ SameRay R (y -ᵥ p₂) (p₂_1 -ᵥ x)) → y ∈ s ∨ ∃ p₁, …
  · rintro (hy | ⟨p, hp, hr⟩)
    -- ⊢ y ∈ s ∨ ∃ p₁, p₁ ∈ s ∧ SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)
    · exact Or.inl hy
      -- 🎉 no goals
    refine' Or.inr ⟨p, hp, _⟩
    -- ⊢ SameRay R (x -ᵥ p) (p₂ -ᵥ y)
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
    -- 🎉 no goals
  · rintro (hy | ⟨p, hp, hr⟩)
    -- ⊢ y ∈ s ∨ ∃ p₂_1, p₂_1 ∈ s ∧ SameRay R (y -ᵥ p₂) (p₂_1 -ᵥ x)
    · exact Or.inl hy
      -- 🎉 no goals
    refine' Or.inr ⟨p, hp, _⟩
    -- ⊢ SameRay R (y -ᵥ p₂) (p -ᵥ x)
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
    -- 🎉 no goals
#align affine_subspace.w_opp_side_iff_exists_right AffineSubspace.wOppSide_iff_exists_right

theorem sOppSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
    s.SOppSide x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₂ ∈ s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) := by
  rw [SOppSide, and_comm, wOppSide_iff_exists_left h, and_assoc, and_congr_right_iff]
  -- ⊢ ¬x ∈ s → (¬y ∈ s ∧ (x ∈ s ∨ ∃ p₂, p₂ ∈ s ∧ SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)) ↔  …
  intro hx
  -- ⊢ ¬y ∈ s ∧ (x ∈ s ∨ ∃ p₂, p₂ ∈ s ∧ SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)) ↔ ¬y ∈ s ∧ ∃ …
  rw [or_iff_right hx]
  -- 🎉 no goals
#align affine_subspace.s_opp_side_iff_exists_left AffineSubspace.sOppSide_iff_exists_left

theorem sOppSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
    s.SOppSide x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₁ ∈ s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) := by
  rw [SOppSide, and_comm, wOppSide_iff_exists_right h, and_assoc, and_congr_right_iff,
    and_congr_right_iff]
  rintro _ hy
  -- ⊢ (y ∈ s ∨ ∃ p₁, p₁ ∈ s ∧ SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)) ↔ ∃ p₁, p₁ ∈ s ∧ Same …
  rw [or_iff_right hy]
  -- 🎉 no goals
#align affine_subspace.s_opp_side_iff_exists_right AffineSubspace.sOppSide_iff_exists_right

theorem WSameSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.WSameSide y z) (hy : y ∉ s) : s.WSameSide x z := by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  -- ⊢ WSameSide s x z
  rw [wSameSide_iff_exists_left hp₂, or_iff_right hy] at hyz
  -- ⊢ WSameSide s x z
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  -- ⊢ WSameSide s x z
  refine' ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz _⟩
  -- ⊢ y -ᵥ p₂ = 0 → x -ᵥ p₁ = 0 ∨ z -ᵥ p₃ = 0
  refine' fun h => False.elim _
  -- ⊢ False
  rw [vsub_eq_zero_iff_eq] at h
  -- ⊢ False
  exact hy (h.symm ▸ hp₂)
  -- 🎉 no goals
#align affine_subspace.w_same_side.trans AffineSubspace.WSameSide.trans

theorem WSameSide.trans_sSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.SSameSide y z) : s.WSameSide x z :=
  hxy.trans hyz.1 hyz.2.1
#align affine_subspace.w_same_side.trans_s_same_side AffineSubspace.WSameSide.trans_sSameSide

theorem WSameSide.trans_wOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.WOppSide y z) (hy : y ∉ s) : s.WOppSide x z := by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  -- ⊢ WOppSide s x z
  rw [wOppSide_iff_exists_left hp₂, or_iff_right hy] at hyz
  -- ⊢ WOppSide s x z
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  -- ⊢ WOppSide s x z
  refine' ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz _⟩
  -- ⊢ y -ᵥ p₂ = 0 → x -ᵥ p₁ = 0 ∨ p₃ -ᵥ z = 0
  refine' fun h => False.elim _
  -- ⊢ False
  rw [vsub_eq_zero_iff_eq] at h
  -- ⊢ False
  exact hy (h.symm ▸ hp₂)
  -- 🎉 no goals
#align affine_subspace.w_same_side.trans_w_opp_side AffineSubspace.WSameSide.trans_wOppSide

theorem WSameSide.trans_sOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.SOppSide y z) : s.WOppSide x z :=
  hxy.trans_wOppSide hyz.1 hyz.2.1
#align affine_subspace.w_same_side.trans_s_opp_side AffineSubspace.WSameSide.trans_sOppSide

theorem SSameSide.trans_wSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.WSameSide y z) : s.WSameSide x z :=
  (hyz.symm.trans_sSameSide hxy.symm).symm
#align affine_subspace.s_same_side.trans_w_same_side AffineSubspace.SSameSide.trans_wSameSide

theorem SSameSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.SSameSide y z) : s.SSameSide x z :=
  ⟨hxy.wSameSide.trans_sSameSide hyz, hxy.2.1, hyz.2.2⟩
#align affine_subspace.s_same_side.trans AffineSubspace.SSameSide.trans

theorem SSameSide.trans_wOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.WOppSide y z) : s.WOppSide x z :=
  hxy.wSameSide.trans_wOppSide hyz hxy.2.2
#align affine_subspace.s_same_side.trans_w_opp_side AffineSubspace.SSameSide.trans_wOppSide

theorem SSameSide.trans_sOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.SOppSide y z) : s.SOppSide x z :=
  ⟨hxy.trans_wOppSide hyz.1, hxy.2.1, hyz.2.2⟩
#align affine_subspace.s_same_side.trans_s_opp_side AffineSubspace.SSameSide.trans_sOppSide

theorem WOppSide.trans_wSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.WSameSide y z) (hy : y ∉ s) : s.WOppSide x z :=
  (hyz.symm.trans_wOppSide hxy.symm hy).symm
#align affine_subspace.w_opp_side.trans_w_same_side AffineSubspace.WOppSide.trans_wSameSide

theorem WOppSide.trans_sSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.SSameSide y z) : s.WOppSide x z :=
  hxy.trans_wSameSide hyz.1 hyz.2.1
#align affine_subspace.w_opp_side.trans_s_same_side AffineSubspace.WOppSide.trans_sSameSide

theorem WOppSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.WOppSide y z) (hy : y ∉ s) : s.WSameSide x z := by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  -- ⊢ WSameSide s x z
  rw [wOppSide_iff_exists_left hp₂, or_iff_right hy] at hyz
  -- ⊢ WSameSide s x z
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  -- ⊢ WSameSide s x z
  rw [← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] at hyz
  -- ⊢ WSameSide s x z
  refine' ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz _⟩
  -- ⊢ p₂ -ᵥ y = 0 → x -ᵥ p₁ = 0 ∨ z -ᵥ p₃ = 0
  refine' fun h => False.elim _
  -- ⊢ False
  rw [vsub_eq_zero_iff_eq] at h
  -- ⊢ False
  exact hy (h ▸ hp₂)
  -- 🎉 no goals
#align affine_subspace.w_opp_side.trans AffineSubspace.WOppSide.trans

theorem WOppSide.trans_sOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.SOppSide y z) : s.WSameSide x z :=
  hxy.trans hyz.1 hyz.2.1
#align affine_subspace.w_opp_side.trans_s_opp_side AffineSubspace.WOppSide.trans_sOppSide

theorem SOppSide.trans_wSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.WSameSide y z) : s.WOppSide x z :=
  (hyz.symm.trans_sOppSide hxy.symm).symm
#align affine_subspace.s_opp_side.trans_w_same_side AffineSubspace.SOppSide.trans_wSameSide

theorem SOppSide.trans_sSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.SSameSide y z) : s.SOppSide x z :=
  (hyz.symm.trans_sOppSide hxy.symm).symm
#align affine_subspace.s_opp_side.trans_s_same_side AffineSubspace.SOppSide.trans_sSameSide

theorem SOppSide.trans_wOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.WOppSide y z) : s.WSameSide x z :=
  (hyz.symm.trans_sOppSide hxy.symm).symm
#align affine_subspace.s_opp_side.trans_w_opp_side AffineSubspace.SOppSide.trans_wOppSide

theorem SOppSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.SOppSide y z) : s.SSameSide x z :=
  ⟨hxy.trans_wOppSide hyz.1, hxy.2.1, hyz.2.2⟩
#align affine_subspace.s_opp_side.trans AffineSubspace.SOppSide.trans

theorem wSameSide_and_wOppSide_iff {s : AffineSubspace R P} {x y : P} :
    s.WSameSide x y ∧ s.WOppSide x y ↔ x ∈ s ∨ y ∈ s := by
  constructor
  -- ⊢ WSameSide s x y ∧ WOppSide s x y → x ∈ s ∨ y ∈ s
  · rintro ⟨hs, ho⟩
    -- ⊢ x ∈ s ∨ y ∈ s
    rw [wOppSide_comm] at ho
    -- ⊢ x ∈ s ∨ y ∈ s
    by_contra h
    -- ⊢ False
    rw [not_or] at h
    -- ⊢ False
    exact h.1 (wOppSide_self_iff.1 (hs.trans_wOppSide ho h.2))
    -- 🎉 no goals
  · rintro (h | h)
    -- ⊢ WSameSide s x y ∧ WOppSide s x y
    · exact ⟨wSameSide_of_left_mem y h, wOppSide_of_left_mem y h⟩
      -- 🎉 no goals
    · exact ⟨wSameSide_of_right_mem x h, wOppSide_of_right_mem x h⟩
      -- 🎉 no goals
#align affine_subspace.w_same_side_and_w_opp_side_iff AffineSubspace.wSameSide_and_wOppSide_iff

theorem WSameSide.not_sOppSide {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) :
    ¬s.SOppSide x y := by
  intro ho
  -- ⊢ False
  have hxy := wSameSide_and_wOppSide_iff.1 ⟨h, ho.1⟩
  -- ⊢ False
  rcases hxy with (hx | hy)
  -- ⊢ False
  · exact ho.2.1 hx
    -- 🎉 no goals
  · exact ho.2.2 hy
    -- 🎉 no goals
#align affine_subspace.w_same_side.not_s_opp_side AffineSubspace.WSameSide.not_sOppSide

theorem SSameSide.not_wOppSide {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    ¬s.WOppSide x y := by
  intro ho
  -- ⊢ False
  have hxy := wSameSide_and_wOppSide_iff.1 ⟨h.1, ho⟩
  -- ⊢ False
  rcases hxy with (hx | hy)
  -- ⊢ False
  · exact h.2.1 hx
    -- 🎉 no goals
  · exact h.2.2 hy
    -- 🎉 no goals
#align affine_subspace.s_same_side.not_w_opp_side AffineSubspace.SSameSide.not_wOppSide

theorem SSameSide.not_sOppSide {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    ¬s.SOppSide x y :=
  fun ho => h.not_wOppSide ho.1
#align affine_subspace.s_same_side.not_s_opp_side AffineSubspace.SSameSide.not_sOppSide

theorem WOppSide.not_sSameSide {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y) :
    ¬s.SSameSide x y :=
  fun hs => hs.not_wOppSide h
#align affine_subspace.w_opp_side.not_s_same_side AffineSubspace.WOppSide.not_sSameSide

theorem SOppSide.not_wSameSide {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    ¬s.WSameSide x y :=
  fun hs => hs.not_sOppSide h
#align affine_subspace.s_opp_side.not_w_same_side AffineSubspace.SOppSide.not_wSameSide

theorem SOppSide.not_sSameSide {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    ¬s.SSameSide x y :=
  fun hs => h.not_wSameSide hs.1
#align affine_subspace.s_opp_side.not_s_same_side AffineSubspace.SOppSide.not_sSameSide

theorem wOppSide_iff_exists_wbtw {s : AffineSubspace R P} {x y : P} :
    s.WOppSide x y ↔ ∃ p ∈ s, Wbtw R x p y := by
  refine' ⟨fun h => _, fun ⟨p, hp, h⟩ => h.wOppSide₁₃ hp⟩
  -- ⊢ ∃ p, p ∈ s ∧ Wbtw R x p y
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
  · rw [vsub_eq_zero_iff_eq] at h
    -- ⊢ ∃ p, p ∈ s ∧ Wbtw R x p y
    rw [h]
    -- ⊢ ∃ p, p ∈ s ∧ Wbtw R p₁ p y
    exact ⟨p₁, hp₁, wbtw_self_left _ _ _⟩
    -- 🎉 no goals
  · rw [vsub_eq_zero_iff_eq] at h
    -- ⊢ ∃ p, p ∈ s ∧ Wbtw R x p y
    rw [← h]
    -- ⊢ ∃ p, p ∈ s ∧ Wbtw R x p p₂
    exact ⟨p₂, hp₂, wbtw_self_right _ _ _⟩
    -- 🎉 no goals
  · refine' ⟨lineMap x y (r₂ / (r₁ + r₂)), _, _⟩
    -- ⊢ ↑(lineMap x y) (r₂ / (r₁ + r₂)) ∈ s
    · have : (r₂ / (r₁ + r₂)) • (y -ᵥ p₂ + (p₂ -ᵥ p₁) - (x -ᵥ p₁)) + (x -ᵥ p₁) =
          (r₂ / (r₁ + r₂)) • (p₂ -ᵥ p₁) := by
        rw [add_comm (y -ᵥ p₂), smul_sub, smul_add, add_sub_assoc, add_assoc, add_right_eq_self,
          div_eq_inv_mul, ← neg_vsub_eq_vsub_rev, smul_neg, ← smul_smul, ← h, smul_smul, ← neg_smul,
          ← sub_smul, ← div_eq_inv_mul, ← div_eq_inv_mul, ← neg_div, ← sub_div, sub_eq_add_neg,
          ← neg_add, neg_div, div_self (Left.add_pos hr₁ hr₂).ne.symm, neg_one_smul, neg_add_self]
      rw [lineMap_apply, ← vsub_vadd x p₁, ← vsub_vadd y p₂, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc,
        ← vadd_assoc, vadd_eq_add, this]
      exact s.smul_vsub_vadd_mem (r₂ / (r₁ + r₂)) hp₂ hp₁ hp₁
      -- 🎉 no goals
    · exact Set.mem_image_of_mem _
        ⟨div_nonneg hr₂.le (Left.add_pos hr₁ hr₂).le,
          div_le_one_of_le (le_add_of_nonneg_left hr₁.le) (Left.add_pos hr₁ hr₂).le⟩
#align affine_subspace.w_opp_side_iff_exists_wbtw AffineSubspace.wOppSide_iff_exists_wbtw

theorem SOppSide.exists_sbtw {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    ∃ p ∈ s, Sbtw R x p y := by
  obtain ⟨p, hp, hw⟩ := wOppSide_iff_exists_wbtw.1 h.wOppSide
  -- ⊢ ∃ p, p ∈ s ∧ Sbtw R x p y
  refine' ⟨p, hp, hw, _, _⟩
  -- ⊢ p ≠ x
  · rintro rfl
    -- ⊢ False
    exact h.2.1 hp
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ False
    exact h.2.2 hp
    -- 🎉 no goals
#align affine_subspace.s_opp_side.exists_sbtw AffineSubspace.SOppSide.exists_sbtw

theorem _root_.Sbtw.sOppSide_of_not_mem_of_mem {s : AffineSubspace R P} {x y z : P}
    (h : Sbtw R x y z) (hx : x ∉ s) (hy : y ∈ s) : s.SOppSide x z := by
  refine' ⟨h.wbtw.wOppSide₁₃ hy, hx, fun hz => hx _⟩
  -- ⊢ x ∈ s
  rcases h with ⟨⟨t, ⟨ht0, ht1⟩, rfl⟩, hyx, hyz⟩
  -- ⊢ x ∈ s
  rw [lineMap_apply] at hy
  -- ⊢ x ∈ s
  have ht : t ≠ 1 := by
    rintro rfl
    simp [lineMap_apply] at hyz
  have hy' := vsub_mem_direction hy hz
  -- ⊢ x ∈ s
  rw [vadd_vsub_assoc, ← neg_vsub_eq_vsub_rev z, ← neg_one_smul R (z -ᵥ x), ← add_smul,
    ← sub_eq_add_neg, s.direction.smul_mem_iff (sub_ne_zero_of_ne ht)] at hy'
  rwa [vadd_mem_iff_mem_of_mem_direction (Submodule.smul_mem _ _ hy')] at hy
  -- 🎉 no goals
#align sbtw.s_opp_side_of_not_mem_of_mem Sbtw.sOppSide_of_not_mem_of_mem

theorem sSameSide_smul_vsub_vadd_left {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : 0 < t) : s.SSameSide (t • (x -ᵥ p₁) +ᵥ p₂) x := by
  refine' ⟨wSameSide_smul_vsub_vadd_left x hp₁ hp₂ ht.le, fun h => hx _, hx⟩
  -- ⊢ x ∈ s
  rwa [vadd_mem_iff_mem_direction _ hp₂, s.direction.smul_mem_iff ht.ne.symm,
    vsub_right_mem_direction_iff_mem hp₁] at h
#align affine_subspace.s_same_side_smul_vsub_vadd_left AffineSubspace.sSameSide_smul_vsub_vadd_left

theorem sSameSide_smul_vsub_vadd_right {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : 0 < t) : s.SSameSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (sSameSide_smul_vsub_vadd_left hx hp₁ hp₂ ht).symm
#align affine_subspace.s_same_side_smul_vsub_vadd_right AffineSubspace.sSameSide_smul_vsub_vadd_right

theorem sSameSide_lineMap_left {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) {t : R}
    (ht : 0 < t) : s.SSameSide (lineMap x y t) y :=
  sSameSide_smul_vsub_vadd_left hy hx hx ht
#align affine_subspace.s_same_side_line_map_left AffineSubspace.sSameSide_lineMap_left

theorem sSameSide_lineMap_right {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) {t : R}
    (ht : 0 < t) : s.SSameSide y (lineMap x y t) :=
  (sSameSide_lineMap_left hx hy ht).symm
#align affine_subspace.s_same_side_line_map_right AffineSubspace.sSameSide_lineMap_right

theorem sOppSide_smul_vsub_vadd_left {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : t < 0) : s.SOppSide (t • (x -ᵥ p₁) +ᵥ p₂) x := by
  refine' ⟨wOppSide_smul_vsub_vadd_left x hp₁ hp₂ ht.le, fun h => hx _, hx⟩
  -- ⊢ x ∈ s
  rwa [vadd_mem_iff_mem_direction _ hp₂, s.direction.smul_mem_iff ht.ne,
    vsub_right_mem_direction_iff_mem hp₁] at h
#align affine_subspace.s_opp_side_smul_vsub_vadd_left AffineSubspace.sOppSide_smul_vsub_vadd_left

theorem sOppSide_smul_vsub_vadd_right {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : t < 0) : s.SOppSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (sOppSide_smul_vsub_vadd_left hx hp₁ hp₂ ht).symm
#align affine_subspace.s_opp_side_smul_vsub_vadd_right AffineSubspace.sOppSide_smul_vsub_vadd_right

theorem sOppSide_lineMap_left {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) {t : R}
    (ht : t < 0) : s.SOppSide (lineMap x y t) y :=
  sOppSide_smul_vsub_vadd_left hy hx hx ht
#align affine_subspace.s_opp_side_line_map_left AffineSubspace.sOppSide_lineMap_left

theorem sOppSide_lineMap_right {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) {t : R}
    (ht : t < 0) : s.SOppSide y (lineMap x y t) :=
  (sOppSide_lineMap_left hx hy ht).symm
#align affine_subspace.s_opp_side_line_map_right AffineSubspace.sOppSide_lineMap_right

theorem setOf_wSameSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
    { y | s.WSameSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Ici 0) s := by
  ext y
  -- ⊢ y ∈ {y | WSameSide s x y} ↔ y ∈ Set.image2 (fun t q => t • (x -ᵥ p) +ᵥ q) (S …
  simp_rw [Set.mem_setOf, Set.mem_image2, Set.mem_Ici]
  -- ⊢ WSameSide s x y ↔ ∃ a b, 0 ≤ a ∧ b ∈ ↑s ∧ a • (x -ᵥ p) +ᵥ b = y
  constructor
  -- ⊢ WSameSide s x y → ∃ a b, 0 ≤ a ∧ b ∈ ↑s ∧ a • (x -ᵥ p) +ᵥ b = y
  · rw [wSameSide_iff_exists_left hp, or_iff_right hx]
    -- ⊢ (∃ p₂, p₂ ∈ s ∧ SameRay R (x -ᵥ p) (y -ᵥ p₂)) → ∃ a b, 0 ≤ a ∧ b ∈ ↑s ∧ a •  …
    rintro ⟨p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      -- ⊢ ∃ a b, 0 ≤ a ∧ b ∈ ↑s ∧ a • (x -ᵥ p) +ᵥ b = y
      exact False.elim (hx (h.symm ▸ hp))
      -- 🎉 no goals
    · rw [vsub_eq_zero_iff_eq] at h
      -- ⊢ ∃ a b, 0 ≤ a ∧ b ∈ ↑s ∧ a • (x -ᵥ p) +ᵥ b = y
      refine' ⟨0, p₂, le_refl _, hp₂, _⟩
      -- ⊢ 0 • (x -ᵥ p) +ᵥ p₂ = y
      simp [h]
      -- 🎉 no goals
    · refine' ⟨r₁ / r₂, p₂, (div_pos hr₁ hr₂).le, hp₂, _⟩
      -- ⊢ (r₁ / r₂) • (x -ᵥ p) +ᵥ p₂ = y
      rw [div_eq_inv_mul, ← smul_smul, h, smul_smul, inv_mul_cancel hr₂.ne.symm, one_smul,
        vsub_vadd]
  · rintro ⟨t, p', ht, hp', rfl⟩
    -- ⊢ WSameSide s x (t • (x -ᵥ p) +ᵥ p')
    exact wSameSide_smul_vsub_vadd_right x hp hp' ht
    -- 🎉 no goals
#align affine_subspace.set_of_w_same_side_eq_image2 AffineSubspace.setOf_wSameSide_eq_image2

theorem setOf_sSameSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
    { y | s.SSameSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Ioi 0) s := by
  ext y
  -- ⊢ y ∈ {y | SSameSide s x y} ↔ y ∈ Set.image2 (fun t q => t • (x -ᵥ p) +ᵥ q) (S …
  simp_rw [Set.mem_setOf, Set.mem_image2, Set.mem_Ioi]
  -- ⊢ SSameSide s x y ↔ ∃ a b, 0 < a ∧ b ∈ ↑s ∧ a • (x -ᵥ p) +ᵥ b = y
  constructor
  -- ⊢ SSameSide s x y → ∃ a b, 0 < a ∧ b ∈ ↑s ∧ a • (x -ᵥ p) +ᵥ b = y
  · rw [sSameSide_iff_exists_left hp]
    -- ⊢ (¬x ∈ s ∧ ¬y ∈ s ∧ ∃ p₂, p₂ ∈ s ∧ SameRay R (x -ᵥ p) (y -ᵥ p₂)) → ∃ a b, 0 < …
    rintro ⟨-, hy, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      -- ⊢ ∃ a b, 0 < a ∧ b ∈ ↑s ∧ a • (x -ᵥ p) +ᵥ b = y
      exact False.elim (hx (h.symm ▸ hp))
      -- 🎉 no goals
    · rw [vsub_eq_zero_iff_eq] at h
      -- ⊢ ∃ a b, 0 < a ∧ b ∈ ↑s ∧ a • (x -ᵥ p) +ᵥ b = y
      exact False.elim (hy (h.symm ▸ hp₂))
      -- 🎉 no goals
    · refine' ⟨r₁ / r₂, p₂, div_pos hr₁ hr₂, hp₂, _⟩
      -- ⊢ (r₁ / r₂) • (x -ᵥ p) +ᵥ p₂ = y
      rw [div_eq_inv_mul, ← smul_smul, h, smul_smul, inv_mul_cancel hr₂.ne.symm, one_smul,
        vsub_vadd]
  · rintro ⟨t, p', ht, hp', rfl⟩
    -- ⊢ SSameSide s x (t • (x -ᵥ p) +ᵥ p')
    exact sSameSide_smul_vsub_vadd_right hx hp hp' ht
    -- 🎉 no goals
#align affine_subspace.set_of_s_same_side_eq_image2 AffineSubspace.setOf_sSameSide_eq_image2

theorem setOf_wOppSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
    { y | s.WOppSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Iic 0) s := by
  ext y
  -- ⊢ y ∈ {y | WOppSide s x y} ↔ y ∈ Set.image2 (fun t q => t • (x -ᵥ p) +ᵥ q) (Se …
  simp_rw [Set.mem_setOf, Set.mem_image2, Set.mem_Iic]
  -- ⊢ WOppSide s x y ↔ ∃ a b, a ≤ 0 ∧ b ∈ ↑s ∧ a • (x -ᵥ p) +ᵥ b = y
  constructor
  -- ⊢ WOppSide s x y → ∃ a b, a ≤ 0 ∧ b ∈ ↑s ∧ a • (x -ᵥ p) +ᵥ b = y
  · rw [wOppSide_iff_exists_left hp, or_iff_right hx]
    -- ⊢ (∃ p₂, p₂ ∈ s ∧ SameRay R (x -ᵥ p) (p₂ -ᵥ y)) → ∃ a b, a ≤ 0 ∧ b ∈ ↑s ∧ a •  …
    rintro ⟨p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      -- ⊢ ∃ a b, a ≤ 0 ∧ b ∈ ↑s ∧ a • (x -ᵥ p) +ᵥ b = y
      exact False.elim (hx (h.symm ▸ hp))
      -- 🎉 no goals
    · rw [vsub_eq_zero_iff_eq] at h
      -- ⊢ ∃ a b, a ≤ 0 ∧ b ∈ ↑s ∧ a • (x -ᵥ p) +ᵥ b = y
      refine' ⟨0, p₂, le_refl _, hp₂, _⟩
      -- ⊢ 0 • (x -ᵥ p) +ᵥ p₂ = y
      simp [h]
      -- 🎉 no goals
    · refine' ⟨-r₁ / r₂, p₂, (div_neg_of_neg_of_pos (Left.neg_neg_iff.2 hr₁) hr₂).le, hp₂, _⟩
      -- ⊢ (-r₁ / r₂) • (x -ᵥ p) +ᵥ p₂ = y
      rw [div_eq_inv_mul, ← smul_smul, neg_smul, h, smul_neg, smul_smul, inv_mul_cancel hr₂.ne.symm,
        one_smul, neg_vsub_eq_vsub_rev, vsub_vadd]
  · rintro ⟨t, p', ht, hp', rfl⟩
    -- ⊢ WOppSide s x (t • (x -ᵥ p) +ᵥ p')
    exact wOppSide_smul_vsub_vadd_right x hp hp' ht
    -- 🎉 no goals
#align affine_subspace.set_of_w_opp_side_eq_image2 AffineSubspace.setOf_wOppSide_eq_image2

theorem setOf_sOppSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
    { y | s.SOppSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Iio 0) s := by
  ext y
  -- ⊢ y ∈ {y | SOppSide s x y} ↔ y ∈ Set.image2 (fun t q => t • (x -ᵥ p) +ᵥ q) (Se …
  simp_rw [Set.mem_setOf, Set.mem_image2, Set.mem_Iio]
  -- ⊢ SOppSide s x y ↔ ∃ a b, a < 0 ∧ b ∈ ↑s ∧ a • (x -ᵥ p) +ᵥ b = y
  constructor
  -- ⊢ SOppSide s x y → ∃ a b, a < 0 ∧ b ∈ ↑s ∧ a • (x -ᵥ p) +ᵥ b = y
  · rw [sOppSide_iff_exists_left hp]
    -- ⊢ (¬x ∈ s ∧ ¬y ∈ s ∧ ∃ p₂, p₂ ∈ s ∧ SameRay R (x -ᵥ p) (p₂ -ᵥ y)) → ∃ a b, a < …
    rintro ⟨-, hy, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      -- ⊢ ∃ a b, a < 0 ∧ b ∈ ↑s ∧ a • (x -ᵥ p) +ᵥ b = y
      exact False.elim (hx (h.symm ▸ hp))
      -- 🎉 no goals
    · rw [vsub_eq_zero_iff_eq] at h
      -- ⊢ ∃ a b, a < 0 ∧ b ∈ ↑s ∧ a • (x -ᵥ p) +ᵥ b = y
      exact False.elim (hy (h ▸ hp₂))
      -- 🎉 no goals
    · refine' ⟨-r₁ / r₂, p₂, div_neg_of_neg_of_pos (Left.neg_neg_iff.2 hr₁) hr₂, hp₂, _⟩
      -- ⊢ (-r₁ / r₂) • (x -ᵥ p) +ᵥ p₂ = y
      rw [div_eq_inv_mul, ← smul_smul, neg_smul, h, smul_neg, smul_smul, inv_mul_cancel hr₂.ne.symm,
        one_smul, neg_vsub_eq_vsub_rev, vsub_vadd]
  · rintro ⟨t, p', ht, hp', rfl⟩
    -- ⊢ SOppSide s x (t • (x -ᵥ p) +ᵥ p')
    exact sOppSide_smul_vsub_vadd_right hx hp hp' ht
    -- 🎉 no goals
#align affine_subspace.set_of_s_opp_side_eq_image2 AffineSubspace.setOf_sOppSide_eq_image2

theorem wOppSide_pointReflection {s : AffineSubspace R P} {x : P} (y : P) (hx : x ∈ s) :
    s.WOppSide y (pointReflection R x y) :=
  (wbtw_pointReflection R _ _).wOppSide₁₃ hx
#align affine_subspace.w_opp_side_point_reflection AffineSubspace.wOppSide_pointReflection

theorem sOppSide_pointReflection {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) :
    s.SOppSide y (pointReflection R x y) := by
  refine' (sbtw_pointReflection_of_ne R fun h => hy _).sOppSide_of_not_mem_of_mem hy hx
  -- ⊢ y ∈ s
  rwa [← h]
  -- 🎉 no goals
#align affine_subspace.s_opp_side_point_reflection AffineSubspace.sOppSide_pointReflection

end LinearOrderedField

section Normed

variable [SeminormedAddCommGroup V] [NormedSpace ℝ V] [PseudoMetricSpace P]

variable [NormedAddTorsor V P]

theorem isConnected_setOf_wSameSide {s : AffineSubspace ℝ P} (x : P) (h : (s : Set P).Nonempty) :
    IsConnected { y | s.WSameSide x y } := by
  obtain ⟨p, hp⟩ := h
  -- ⊢ IsConnected {y | WSameSide s x y}
  haveI : Nonempty s := ⟨⟨p, hp⟩⟩
  -- ⊢ IsConnected {y | WSameSide s x y}
  by_cases hx : x ∈ s
  -- ⊢ IsConnected {y | WSameSide s x y}
  · simp only [wSameSide_of_left_mem, hx]
    -- ⊢ IsConnected {y | True}
    have := AddTorsor.connectedSpace V P
    -- ⊢ IsConnected {y | True}
    exact isConnected_univ
    -- 🎉 no goals
  · rw [setOf_wSameSide_eq_image2 hx hp, ← Set.image_prod]
    -- ⊢ IsConnected ((fun x_1 => x_1.fst • (x -ᵥ p) +ᵥ x_1.snd) '' Set.Ici 0 ×ˢ ↑s)
    refine' (isConnected_Ici.prod (isConnected_iff_connectedSpace.2 _)).image _
      ((continuous_fst.smul continuous_const).vadd continuous_snd).continuousOn
    convert AddTorsor.connectedSpace s.direction s
    -- 🎉 no goals
#align affine_subspace.is_connected_set_of_w_same_side AffineSubspace.isConnected_setOf_wSameSide

theorem isPreconnected_setOf_wSameSide (s : AffineSubspace ℝ P) (x : P) :
    IsPreconnected { y | s.WSameSide x y } := by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  -- ⊢ IsPreconnected {y | WSameSide s x y}
  · rw [coe_eq_bot_iff] at h
    -- ⊢ IsPreconnected {y | WSameSide s x y}
    simp only [h, not_wSameSide_bot]
    -- ⊢ IsPreconnected {y | False}
    exact isPreconnected_empty
    -- 🎉 no goals
  · exact (isConnected_setOf_wSameSide x h).isPreconnected
    -- 🎉 no goals
#align affine_subspace.is_preconnected_set_of_w_same_side AffineSubspace.isPreconnected_setOf_wSameSide

theorem isConnected_setOf_sSameSide {s : AffineSubspace ℝ P} {x : P} (hx : x ∉ s)
    (h : (s : Set P).Nonempty) : IsConnected { y | s.SSameSide x y } := by
  obtain ⟨p, hp⟩ := h
  -- ⊢ IsConnected {y | SSameSide s x y}
  haveI : Nonempty s := ⟨⟨p, hp⟩⟩
  -- ⊢ IsConnected {y | SSameSide s x y}
  rw [setOf_sSameSide_eq_image2 hx hp, ← Set.image_prod]
  -- ⊢ IsConnected ((fun x_1 => x_1.fst • (x -ᵥ p) +ᵥ x_1.snd) '' Set.Ioi 0 ×ˢ ↑s)
  refine' (isConnected_Ioi.prod (isConnected_iff_connectedSpace.2 _)).image _
    ((continuous_fst.smul continuous_const).vadd continuous_snd).continuousOn
  convert AddTorsor.connectedSpace s.direction s
  -- 🎉 no goals
#align affine_subspace.is_connected_set_of_s_same_side AffineSubspace.isConnected_setOf_sSameSide

theorem isPreconnected_setOf_sSameSide (s : AffineSubspace ℝ P) (x : P) :
    IsPreconnected { y | s.SSameSide x y } := by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  -- ⊢ IsPreconnected {y | SSameSide s x y}
  · rw [coe_eq_bot_iff] at h
    -- ⊢ IsPreconnected {y | SSameSide s x y}
    simp only [h, not_sSameSide_bot]
    -- ⊢ IsPreconnected {y | False}
    exact isPreconnected_empty
    -- 🎉 no goals
  · by_cases hx : x ∈ s
    -- ⊢ IsPreconnected {y | SSameSide s x y}
    · simp only [hx, SSameSide, not_true, false_and_iff, and_false_iff]
      -- ⊢ IsPreconnected {y | False}
      exact isPreconnected_empty
      -- 🎉 no goals
    · exact (isConnected_setOf_sSameSide hx h).isPreconnected
      -- 🎉 no goals
#align affine_subspace.is_preconnected_set_of_s_same_side AffineSubspace.isPreconnected_setOf_sSameSide

theorem isConnected_setOf_wOppSide {s : AffineSubspace ℝ P} (x : P) (h : (s : Set P).Nonempty) :
    IsConnected { y | s.WOppSide x y } := by
  obtain ⟨p, hp⟩ := h
  -- ⊢ IsConnected {y | WOppSide s x y}
  haveI : Nonempty s := ⟨⟨p, hp⟩⟩
  -- ⊢ IsConnected {y | WOppSide s x y}
  by_cases hx : x ∈ s
  -- ⊢ IsConnected {y | WOppSide s x y}
  · simp only [wOppSide_of_left_mem, hx]
    -- ⊢ IsConnected {y | True}
    have := AddTorsor.connectedSpace V P
    -- ⊢ IsConnected {y | True}
    exact isConnected_univ
    -- 🎉 no goals
  · rw [setOf_wOppSide_eq_image2 hx hp, ← Set.image_prod]
    -- ⊢ IsConnected ((fun x_1 => x_1.fst • (x -ᵥ p) +ᵥ x_1.snd) '' Set.Iic 0 ×ˢ ↑s)
    refine' (isConnected_Iic.prod (isConnected_iff_connectedSpace.2 _)).image _
      ((continuous_fst.smul continuous_const).vadd continuous_snd).continuousOn
    convert AddTorsor.connectedSpace s.direction s
    -- 🎉 no goals
#align affine_subspace.is_connected_set_of_w_opp_side AffineSubspace.isConnected_setOf_wOppSide

theorem isPreconnected_setOf_wOppSide (s : AffineSubspace ℝ P) (x : P) :
    IsPreconnected { y | s.WOppSide x y } := by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  -- ⊢ IsPreconnected {y | WOppSide s x y}
  · rw [coe_eq_bot_iff] at h
    -- ⊢ IsPreconnected {y | WOppSide s x y}
    simp only [h, not_wOppSide_bot]
    -- ⊢ IsPreconnected {y | False}
    exact isPreconnected_empty
    -- 🎉 no goals
  · exact (isConnected_setOf_wOppSide x h).isPreconnected
    -- 🎉 no goals
#align affine_subspace.is_preconnected_set_of_w_opp_side AffineSubspace.isPreconnected_setOf_wOppSide

theorem isConnected_setOf_sOppSide {s : AffineSubspace ℝ P} {x : P} (hx : x ∉ s)
    (h : (s : Set P).Nonempty) : IsConnected { y | s.SOppSide x y } := by
  obtain ⟨p, hp⟩ := h
  -- ⊢ IsConnected {y | SOppSide s x y}
  haveI : Nonempty s := ⟨⟨p, hp⟩⟩
  -- ⊢ IsConnected {y | SOppSide s x y}
  rw [setOf_sOppSide_eq_image2 hx hp, ← Set.image_prod]
  -- ⊢ IsConnected ((fun x_1 => x_1.fst • (x -ᵥ p) +ᵥ x_1.snd) '' Set.Iio 0 ×ˢ ↑s)
  refine' (isConnected_Iio.prod (isConnected_iff_connectedSpace.2 _)).image _
    ((continuous_fst.smul continuous_const).vadd continuous_snd).continuousOn
  convert AddTorsor.connectedSpace s.direction s
  -- 🎉 no goals
#align affine_subspace.is_connected_set_of_s_opp_side AffineSubspace.isConnected_setOf_sOppSide

theorem isPreconnected_setOf_sOppSide (s : AffineSubspace ℝ P) (x : P) :
    IsPreconnected { y | s.SOppSide x y } := by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  -- ⊢ IsPreconnected {y | SOppSide s x y}
  · rw [coe_eq_bot_iff] at h
    -- ⊢ IsPreconnected {y | SOppSide s x y}
    simp only [h, not_sOppSide_bot]
    -- ⊢ IsPreconnected {y | False}
    exact isPreconnected_empty
    -- 🎉 no goals
  · by_cases hx : x ∈ s
    -- ⊢ IsPreconnected {y | SOppSide s x y}
    · simp only [hx, SOppSide, not_true, false_and_iff, and_false_iff]
      -- ⊢ IsPreconnected {y | False}
      exact isPreconnected_empty
      -- 🎉 no goals
    · exact (isConnected_setOf_sOppSide hx h).isPreconnected
      -- 🎉 no goals
#align affine_subspace.is_preconnected_set_of_s_opp_side AffineSubspace.isPreconnected_setOf_sOppSide

end Normed

end AffineSubspace
