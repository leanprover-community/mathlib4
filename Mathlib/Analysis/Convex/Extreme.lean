/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Analysis.Convex.Hull

#align_import analysis.convex.extreme from "leanprover-community/mathlib"@"c5773405394e073885e2a144c9ca14637e8eb963"

/-!
# Extreme sets

This file defines extreme sets and extreme points for sets in a module.

An extreme set of `A` is a subset of `A` that is as far as it can get in any outward direction: If
point `x` is in it and point `y ∈ A`, then the line passing through `x` and `y` leaves `A` at `x`.
This is an analytic notion of "being on the side of". It is weaker than being exposed (see
`IsExposed.isExtreme`).

## Main declarations

* `IsExtreme 𝕜 A B`: States that `B` is an extreme set of `A` (in the literature, `A` is often
  implicit).
* `Set.extremePoints 𝕜 A`: Set of extreme points of `A` (corresponding to extreme singletons).
* `Convex.mem_extremePoints_iff_convex_diff`: A useful equivalent condition to being an extreme
  point: `x` is an extreme point iff `A \ {x}` is convex.

## Implementation notes

The exact definition of extremeness has been carefully chosen so as to make as many lemmas
unconditional (in particular, the Krein-Milman theorem doesn't need the set to be convex!).
In practice, `A` is often assumed to be a convex set.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

## TODO

Prove lemmas relating extreme sets and points to the intrinsic frontier.

More not-yet-PRed stuff is available on the mathlib3 branch `sperner_again`.
-/


open Function Set

open Affine Classical

variable {𝕜 E F ι : Type*} {π : ι → Type*}

section SMul

variable (𝕜) [OrderedSemiring 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

/-- A set `B` is an extreme subset of `A` if `B ⊆ A` and all points of `B` only belong to open
segments whose ends are in `B`. -/
def IsExtreme (A B : Set E) : Prop :=
  B ⊆ A ∧ ∀ ⦃x₁⦄, x₁ ∈ A → ∀ ⦃x₂⦄, x₂ ∈ A → ∀ ⦃x⦄, x ∈ B → x ∈ openSegment 𝕜 x₁ x₂ → x₁ ∈ B ∧ x₂ ∈ B
#align is_extreme IsExtreme

/-- A point `x` is an extreme point of a set `A` if `x` belongs to no open segment with ends in
`A`, except for the obvious `openSegment x x`. -/
def Set.extremePoints (A : Set E) : Set E :=
  { x ∈ A | ∀ ⦃x₁⦄, x₁ ∈ A → ∀ ⦃x₂⦄, x₂ ∈ A → x ∈ openSegment 𝕜 x₁ x₂ → x₁ = x ∧ x₂ = x }
#align set.extreme_points Set.extremePoints

@[refl]
protected theorem IsExtreme.refl (A : Set E) : IsExtreme 𝕜 A A :=
  ⟨Subset.rfl, fun _ hx₁A _ hx₂A _ _ _ ↦ ⟨hx₁A, hx₂A⟩⟩
#align is_extreme.refl IsExtreme.refl

variable {𝕜} {A B C : Set E} {x : E}

protected theorem IsExtreme.rfl : IsExtreme 𝕜 A A :=
  IsExtreme.refl 𝕜 A
#align is_extreme.rfl IsExtreme.rfl

@[trans]
protected theorem IsExtreme.trans (hAB : IsExtreme 𝕜 A B) (hBC : IsExtreme 𝕜 B C) :
    IsExtreme 𝕜 A C := by
  refine' ⟨Subset.trans hBC.1 hAB.1, fun x₁ hx₁A x₂ hx₂A x hxC hx ↦ _⟩
  -- ⊢ x₁ ∈ C ∧ x₂ ∈ C
  obtain ⟨hx₁B, hx₂B⟩ := hAB.2 hx₁A hx₂A (hBC.1 hxC) hx
  -- ⊢ x₁ ∈ C ∧ x₂ ∈ C
  exact hBC.2 hx₁B hx₂B hxC hx
  -- 🎉 no goals
#align is_extreme.trans IsExtreme.trans

protected theorem IsExtreme.antisymm : AntiSymmetric (IsExtreme 𝕜 : Set E → Set E → Prop) :=
  fun _ _ hAB hBA ↦ Subset.antisymm hBA.1 hAB.1
#align is_extreme.antisymm IsExtreme.antisymm

instance : IsPartialOrder (Set E) (IsExtreme 𝕜) where
  refl := IsExtreme.refl 𝕜
  trans _ _ _ := IsExtreme.trans
  antisymm := IsExtreme.antisymm

theorem IsExtreme.inter (hAB : IsExtreme 𝕜 A B) (hAC : IsExtreme 𝕜 A C) :
    IsExtreme 𝕜 A (B ∩ C) := by
  use Subset.trans (inter_subset_left _ _) hAB.1
  -- ⊢ ∀ ⦃x₁ : E⦄, x₁ ∈ A → ∀ ⦃x₂ : E⦄, x₂ ∈ A → ∀ ⦃x : E⦄, x ∈ B ∩ C → x ∈ openSeg …
  rintro x₁ hx₁A x₂ hx₂A x ⟨hxB, hxC⟩ hx
  -- ⊢ x₁ ∈ B ∩ C ∧ x₂ ∈ B ∩ C
  obtain ⟨hx₁B, hx₂B⟩ := hAB.2 hx₁A hx₂A hxB hx
  -- ⊢ x₁ ∈ B ∩ C ∧ x₂ ∈ B ∩ C
  obtain ⟨hx₁C, hx₂C⟩ := hAC.2 hx₁A hx₂A hxC hx
  -- ⊢ x₁ ∈ B ∩ C ∧ x₂ ∈ B ∩ C
  exact ⟨⟨hx₁B, hx₁C⟩, hx₂B, hx₂C⟩
  -- 🎉 no goals
#align is_extreme.inter IsExtreme.inter

protected theorem IsExtreme.mono (hAC : IsExtreme 𝕜 A C) (hBA : B ⊆ A) (hCB : C ⊆ B) :
    IsExtreme 𝕜 B C :=
  ⟨hCB, fun _ hx₁B _ hx₂B _ hxC hx ↦ hAC.2 (hBA hx₁B) (hBA hx₂B) hxC hx⟩
#align is_extreme.mono IsExtreme.mono

theorem isExtreme_iInter {ι : Sort*} [Nonempty ι] {F : ι → Set E}
    (hAF : ∀ i : ι, IsExtreme 𝕜 A (F i)) : IsExtreme 𝕜 A (⋂ i : ι, F i) := by
  obtain i := Classical.arbitrary ι
  -- ⊢ IsExtreme 𝕜 A (⋂ (i : ι), F i)
  refine' ⟨iInter_subset_of_subset i (hAF i).1, fun x₁ hx₁A x₂ hx₂A x hxF hx ↦ _⟩
  -- ⊢ x₁ ∈ ⋂ (i : ι), F i ∧ x₂ ∈ ⋂ (i : ι), F i
  simp_rw [mem_iInter] at hxF ⊢
  -- ⊢ (∀ (i : ι), x₁ ∈ F i) ∧ ∀ (i : ι), x₂ ∈ F i
  have h := fun i ↦ (hAF i).2 hx₁A hx₂A (hxF i) hx
  -- ⊢ (∀ (i : ι), x₁ ∈ F i) ∧ ∀ (i : ι), x₂ ∈ F i
  exact ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩
  -- 🎉 no goals
#align is_extreme_Inter isExtreme_iInter

theorem isExtreme_biInter {F : Set (Set E)} (hF : F.Nonempty) (hA : ∀ B ∈ F, IsExtreme 𝕜 A B) :
    IsExtreme 𝕜 A (⋂ B ∈ F, B) := by
  haveI := hF.to_subtype
  -- ⊢ IsExtreme 𝕜 A (⋂ (B : Set E) (_ : B ∈ F), B)
  simpa only [iInter_subtype] using isExtreme_iInter fun i : F ↦ hA _ i.2
  -- 🎉 no goals
#align is_extreme_bInter isExtreme_biInter

theorem isExtreme_sInter {F : Set (Set E)} (hF : F.Nonempty) (hAF : ∀ B ∈ F, IsExtreme 𝕜 A B) :
    IsExtreme 𝕜 A (⋂₀ F) := by
  obtain ⟨B, hB⟩ := hF
  -- ⊢ IsExtreme 𝕜 A (⋂₀ F)
  refine' ⟨(sInter_subset_of_mem hB).trans (hAF B hB).1, fun x₁ hx₁A x₂ hx₂A x hxF hx ↦ _⟩
  -- ⊢ x₁ ∈ ⋂₀ F ∧ x₂ ∈ ⋂₀ F
  simp_rw [mem_sInter] at hxF ⊢
  -- ⊢ (∀ (t : Set E), t ∈ F → x₁ ∈ t) ∧ ∀ (t : Set E), t ∈ F → x₂ ∈ t
  have h := fun B hB ↦ (hAF B hB).2 hx₁A hx₂A (hxF B hB) hx
  -- ⊢ (∀ (t : Set E), t ∈ F → x₁ ∈ t) ∧ ∀ (t : Set E), t ∈ F → x₂ ∈ t
  exact ⟨fun B hB ↦ (h B hB).1, fun B hB ↦ (h B hB).2⟩
  -- 🎉 no goals
#align is_extreme_sInter isExtreme_sInter

theorem mem_extremePoints : x ∈ A.extremePoints 𝕜 ↔
    x ∈ A ∧ ∀ (x₁) (_ : x₁ ∈ A) (x₂) (_ : x₂ ∈ A), x ∈ openSegment 𝕜 x₁ x₂ → x₁ = x ∧ x₂ = x :=
  Iff.rfl
#align mem_extreme_points mem_extremePoints

/-- x is an extreme point to A iff {x} is an extreme set of A. -/
theorem mem_extremePoints_iff_extreme_singleton : x ∈ A.extremePoints 𝕜 ↔ IsExtreme 𝕜 A {x} := by
  refine' ⟨_, fun hx ↦ ⟨singleton_subset_iff.1 hx.1, fun x₁ hx₁ x₂ hx₂ ↦ hx.2 hx₁ hx₂ rfl⟩⟩
  -- ⊢ x ∈ extremePoints 𝕜 A → IsExtreme 𝕜 A {x}
  rintro ⟨hxA, hAx⟩
  -- ⊢ IsExtreme 𝕜 A {x}
  use singleton_subset_iff.2 hxA
  -- ⊢ ∀ ⦃x₁ : E⦄, x₁ ∈ A → ∀ ⦃x₂ : E⦄, x₂ ∈ A → ∀ ⦃x_1 : E⦄, x_1 ∈ {x} → x_1 ∈ ope …
  rintro x₁ hx₁A x₂ hx₂A y (rfl : y = x)
  -- ⊢ y ∈ openSegment 𝕜 x₁ x₂ → x₁ ∈ {y} ∧ x₂ ∈ {y}
  exact hAx hx₁A hx₂A
  -- 🎉 no goals
#align mem_extreme_points_iff_extreme_singleton mem_extremePoints_iff_extreme_singleton

theorem extremePoints_subset : A.extremePoints 𝕜 ⊆ A :=
  fun _ hx ↦ hx.1
#align extreme_points_subset extremePoints_subset

@[simp]
theorem extremePoints_empty : (∅ : Set E).extremePoints 𝕜 = ∅ :=
  subset_empty_iff.1 extremePoints_subset
#align extreme_points_empty extremePoints_empty

@[simp]
theorem extremePoints_singleton : ({x} : Set E).extremePoints 𝕜 = {x} :=
  extremePoints_subset.antisymm <|
    singleton_subset_iff.2 ⟨mem_singleton x, fun _ hx₁ _ hx₂ _ ↦ ⟨hx₁, hx₂⟩⟩
#align extreme_points_singleton extremePoints_singleton

theorem inter_extremePoints_subset_extremePoints_of_subset (hBA : B ⊆ A) :
    B ∩ A.extremePoints 𝕜 ⊆ B.extremePoints 𝕜 :=
  fun _ ⟨hxB, hxA⟩ ↦ ⟨hxB, fun _ hx₁ _ hx₂ hx ↦ hxA.2 (hBA hx₁) (hBA hx₂) hx⟩
#align inter_extreme_points_subset_extreme_points_of_subset inter_extremePoints_subset_extremePoints_of_subset

theorem IsExtreme.extremePoints_subset_extremePoints (hAB : IsExtreme 𝕜 A B) :
    B.extremePoints 𝕜 ⊆ A.extremePoints 𝕜 :=
  fun _ hx ↦ mem_extremePoints_iff_extreme_singleton.2
    (hAB.trans (mem_extremePoints_iff_extreme_singleton.1 hx))
#align is_extreme.extreme_points_subset_extreme_points IsExtreme.extremePoints_subset_extremePoints

theorem IsExtreme.extremePoints_eq (hAB : IsExtreme 𝕜 A B) :
    B.extremePoints 𝕜 = B ∩ A.extremePoints 𝕜 :=
  Subset.antisymm (fun _ hx ↦ ⟨hx.1, hAB.extremePoints_subset_extremePoints hx⟩)
    (inter_extremePoints_subset_extremePoints_of_subset hAB.1)
#align is_extreme.extreme_points_eq IsExtreme.extremePoints_eq

end SMul

section OrderedSemiring

variable [OrderedSemiring 𝕜] [AddCommGroup E] [AddCommGroup F] [∀ i, AddCommGroup (π i)]
  [Module 𝕜 E] [Module 𝕜 F] [∀ i, Module 𝕜 (π i)] {A B : Set E} {x : E}

theorem IsExtreme.convex_diff (hA : Convex 𝕜 A) (hAB : IsExtreme 𝕜 A B) : Convex 𝕜 (A \ B) :=
  convex_iff_openSegment_subset.2 fun _ ⟨hx₁A, hx₁B⟩ _ ⟨hx₂A, _⟩ _ hx ↦
    ⟨hA.openSegment_subset hx₁A hx₂A hx, fun hxB ↦ hx₁B (hAB.2 hx₁A hx₂A hxB hx).1⟩
#align is_extreme.convex_diff IsExtreme.convex_diff

@[simp]
theorem extremePoints_prod (s : Set E) (t : Set F) :
    (s ×ˢ t).extremePoints 𝕜 = s.extremePoints 𝕜 ×ˢ t.extremePoints 𝕜 := by
  ext
  -- ⊢ x✝ ∈ extremePoints 𝕜 (s ×ˢ t) ↔ x✝ ∈ extremePoints 𝕜 s ×ˢ extremePoints 𝕜 t
  refine' (and_congr_right fun hx ↦ ⟨fun h ↦ _, fun h ↦ _⟩).trans and_and_and_comm
  -- ⊢ (∀ ⦃x₁ : E⦄, x₁ ∈ s → ∀ ⦃x₂ : E⦄, x₂ ∈ s → x✝.fst ∈ openSegment 𝕜 x₁ x₂ → x₁ …
  constructor
  · rintro x₁ hx₁ x₂ hx₂ hx_fst
    -- ⊢ x₁ = x✝.fst ∧ x₂ = x✝.fst
    refine' (h (mk_mem_prod hx₁ hx.2) (mk_mem_prod hx₂ hx.2) _).imp (congr_arg Prod.fst)
        (congr_arg Prod.fst)
    rw [← Prod.image_mk_openSegment_left]
    -- ⊢ x✝ ∈ (fun x => (x, x✝.snd)) '' openSegment 𝕜 x₁ x₂
    exact ⟨_, hx_fst, Prod.mk.eta⟩
    -- 🎉 no goals
  · rintro x₁ hx₁ x₂ hx₂ hx_snd
    -- ⊢ x₁ = x✝.snd ∧ x₂ = x✝.snd
    refine' (h (mk_mem_prod hx.1 hx₁) (mk_mem_prod hx.1 hx₂) _).imp (congr_arg Prod.snd)
        (congr_arg Prod.snd)
    rw [← Prod.image_mk_openSegment_right]
    -- ⊢ x✝ ∈ (fun y => (x✝.fst, y)) '' openSegment 𝕜 x₁ x₂
    exact ⟨_, hx_snd, Prod.mk.eta⟩
    -- 🎉 no goals
  · rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hx'⟩
    -- ⊢ x₁ = x✝ ∧ x₂ = x✝
    simp_rw [Prod.ext_iff]
    -- ⊢ (x₁.fst = x✝.fst ∧ x₁.snd = x✝.snd) ∧ x₂.fst = x✝.fst ∧ x₂.snd = x✝.snd
    exact and_and_and_comm.1
        ⟨h.1 hx₁.1 hx₂.1 ⟨a, b, ha, hb, hab, congr_arg Prod.fst hx'⟩,
          h.2 hx₁.2 hx₂.2 ⟨a, b, ha, hb, hab, congr_arg Prod.snd hx'⟩⟩
#align extreme_points_prod extremePoints_prod

@[simp]
theorem extremePoints_pi (s : ∀ i, Set (π i)) :
    (univ.pi s).extremePoints 𝕜 = univ.pi fun i ↦ (s i).extremePoints 𝕜 := by
  ext x
  -- ⊢ x ∈ extremePoints 𝕜 (pi univ s) ↔ x ∈ pi univ fun i => extremePoints 𝕜 (s i)
  simp only [mem_extremePoints, mem_pi, mem_univ, true_imp_iff, @forall_and ι]
  -- ⊢ ((∀ (i : ι), x i ∈ s i) ∧ ∀ (x₁ : (i : ι) → π i), (∀ (i : ι), x₁ i ∈ s i) →  …
  refine' and_congr_right fun hx ↦ ⟨fun h i ↦ _, fun h ↦ _⟩
  -- ⊢ ∀ (x₁ : π i), x₁ ∈ s i → ∀ (x₂ : π i), x₂ ∈ s i → x i ∈ openSegment 𝕜 x₁ x₂  …
  · rintro x₁ hx₁ x₂ hx₂ hi
    -- ⊢ x₁ = x i ∧ x₂ = x i
    refine' (h (update x i x₁) _ (update x i x₂) _ _).imp (fun h₁ ↦ by rw [← h₁, update_same])
        fun h₂ ↦ by rw [← h₂, update_same]
    iterate 2
      rintro j
      obtain rfl | hji := eq_or_ne j i
      · rwa [update_same]
      · rw [update_noteq hji]
        exact hx _
    rw [← Pi.image_update_openSegment]
    -- ⊢ x ∈ update x i '' openSegment 𝕜 x₁ x₂
    exact ⟨_, hi, update_eq_self _ _⟩
    -- 🎉 no goals
  · rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hx'⟩
    -- ⊢ x₁ = x ∧ x₂ = x
    simp_rw [funext_iff, ← forall_and]
    -- ⊢ ∀ (x_1 : ι), x₁ x_1 = x x_1 ∧ x₂ x_1 = x x_1
    exact fun i ↦ h _ _ (hx₁ _) _ (hx₂ _) ⟨a, b, ha, hb, hab, congr_fun hx' _⟩
    -- 🎉 no goals
#align extreme_points_pi extremePoints_pi

end OrderedSemiring

section LinearOrderedRing

variable [LinearOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable [DenselyOrdered 𝕜] [NoZeroSMulDivisors 𝕜 E] {A B : Set E} {x : E}

/-- A useful restatement using `segment`: `x` is an extreme point iff the only (closed) segments
that contain it are those with `x` as one of their endpoints. -/
theorem mem_extremePoints_iff_forall_segment : x ∈ A.extremePoints 𝕜 ↔
    x ∈ A ∧ ∀ (x₁) (_ : x₁ ∈ A) (x₂) (_ : x₂ ∈ A), x ∈ segment 𝕜 x₁ x₂ → x₁ = x ∨ x₂ = x := by
  refine' and_congr_right fun hxA ↦ forall₄_congr fun x₁ h₁ x₂ h₂ ↦ _
  -- ⊢ x ∈ openSegment 𝕜 x₁ x₂ → x₁ = x ∧ x₂ = x ↔ x ∈ segment 𝕜 x₁ x₂ → x₁ = x ∨ x …
  constructor
  -- ⊢ (x ∈ openSegment 𝕜 x₁ x₂ → x₁ = x ∧ x₂ = x) → x ∈ segment 𝕜 x₁ x₂ → x₁ = x ∨ …
  · rw [← insert_endpoints_openSegment]
    -- ⊢ (x ∈ openSegment 𝕜 x₁ x₂ → x₁ = x ∧ x₂ = x) → x ∈ insert x₁ (insert x₂ (open …
    rintro H (rfl | rfl | hx)
    exacts [Or.inl rfl, Or.inr rfl, Or.inl <| (H hx).1]
    -- 🎉 no goals
  · intro H hx
    -- ⊢ x₁ = x ∧ x₂ = x
    rcases H (openSegment_subset_segment _ _ _ hx) with (rfl | rfl)
    -- ⊢ x₁ = x₁ ∧ x₂ = x₁
    exacts [⟨rfl, (left_mem_openSegment_iff.1 hx).symm⟩, ⟨right_mem_openSegment_iff.1 hx, rfl⟩]
    -- 🎉 no goals
#align mem_extreme_points_iff_forall_segment mem_extremePoints_iff_forall_segment

theorem Convex.mem_extremePoints_iff_convex_diff (hA : Convex 𝕜 A) :
    x ∈ A.extremePoints 𝕜 ↔ x ∈ A ∧ Convex 𝕜 (A \ {x}) := by
  use fun hx ↦ ⟨hx.1, (mem_extremePoints_iff_extreme_singleton.1 hx).convex_diff hA⟩
  -- ⊢ x ∈ A ∧ Convex 𝕜 (A \ {x}) → x ∈ extremePoints 𝕜 A
  rintro ⟨hxA, hAx⟩
  -- ⊢ x ∈ extremePoints 𝕜 A
  refine' mem_extremePoints_iff_forall_segment.2 ⟨hxA, fun x₁ hx₁ x₂ hx₂ hx ↦ _⟩
  -- ⊢ x₁ = x ∨ x₂ = x
  rw [convex_iff_segment_subset] at hAx
  -- ⊢ x₁ = x ∨ x₂ = x
  by_contra' h
  -- ⊢ False
  exact (hAx ⟨hx₁, fun hx₁ ↦ h.1 (mem_singleton_iff.2 hx₁)⟩
      ⟨hx₂, fun hx₂ ↦ h.2 (mem_singleton_iff.2 hx₂)⟩ hx).2 rfl
#align convex.mem_extreme_points_iff_convex_diff Convex.mem_extremePoints_iff_convex_diff

theorem Convex.mem_extremePoints_iff_mem_diff_convexHull_diff (hA : Convex 𝕜 A) :
    x ∈ A.extremePoints 𝕜 ↔ x ∈ A \ convexHull 𝕜 (A \ {x}) := by
  rw [hA.mem_extremePoints_iff_convex_diff, hA.convex_remove_iff_not_mem_convexHull_remove,
    mem_diff]
#align convex.mem_extreme_points_iff_mem_diff_convex_hull_diff Convex.mem_extremePoints_iff_mem_diff_convexHull_diff

theorem extremePoints_convexHull_subset : (convexHull 𝕜 A).extremePoints 𝕜 ⊆ A := by
  rintro x hx
  -- ⊢ x ∈ A
  rw [(convex_convexHull 𝕜 _).mem_extremePoints_iff_convex_diff] at hx
  -- ⊢ x ∈ A
  by_contra h
  -- ⊢ False
  exact (convexHull_min (subset_diff.2 ⟨subset_convexHull 𝕜 _, disjoint_singleton_right.2 h⟩) hx.2
    hx.1).2 rfl
#align extreme_points_convex_hull_subset extremePoints_convexHull_subset

end LinearOrderedRing
