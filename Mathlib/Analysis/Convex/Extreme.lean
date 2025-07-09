/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Analysis.Convex.Hull

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
-/


open Function Set Affine

variable {𝕜 E F ι : Type*} {M : ι → Type*}

section SMul

variable (𝕜) [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

/-- A set `B` is an extreme subset of `A` if `B ⊆ A` and all points of `B` only belong to open
segments whose ends are in `B`. -/
def IsExtreme (A B : Set E) : Prop :=
  B ⊆ A ∧ ∀ ⦃x₁⦄, x₁ ∈ A → ∀ ⦃x₂⦄, x₂ ∈ A → ∀ ⦃x⦄, x ∈ B → x ∈ openSegment 𝕜 x₁ x₂ → x₁ ∈ B ∧ x₂ ∈ B

/-- A point `x` is an extreme point of a set `A` if `x` belongs to no open segment with ends in
`A`, except for the obvious `openSegment x x`.

In order to prove that `x` is an extreme point of `A`,
it is convenient to use `mem_extremePoints_iff_left` to avoid repeating arguments twice. -/
def Set.extremePoints (A : Set E) : Set E :=
  { x ∈ A | ∀ ⦃x₁⦄, x₁ ∈ A → ∀ ⦃x₂⦄, x₂ ∈ A → x ∈ openSegment 𝕜 x₁ x₂ → x₁ = x ∧ x₂ = x }

@[refl]
protected theorem IsExtreme.refl (A : Set E) : IsExtreme 𝕜 A A :=
  ⟨Subset.rfl, fun _ hx₁A _ hx₂A _ _ _ ↦ ⟨hx₁A, hx₂A⟩⟩

variable {𝕜} {A B C : Set E} {x : E}

protected theorem IsExtreme.rfl : IsExtreme 𝕜 A A :=
  IsExtreme.refl 𝕜 A

@[trans]
protected theorem IsExtreme.trans (hAB : IsExtreme 𝕜 A B) (hBC : IsExtreme 𝕜 B C) :
    IsExtreme 𝕜 A C := by
  refine ⟨Subset.trans hBC.1 hAB.1, fun x₁ hx₁A x₂ hx₂A x hxC hx ↦ ?_⟩
  obtain ⟨hx₁B, hx₂B⟩ := hAB.2 hx₁A hx₂A (hBC.1 hxC) hx
  exact hBC.2 hx₁B hx₂B hxC hx

protected theorem IsExtreme.antisymm : AntiSymmetric (IsExtreme 𝕜 : Set E → Set E → Prop) :=
  fun _ _ hAB hBA ↦ Subset.antisymm hBA.1 hAB.1

instance : IsPartialOrder (Set E) (IsExtreme 𝕜) where
  refl := IsExtreme.refl 𝕜
  trans _ _ _ := IsExtreme.trans
  antisymm := IsExtreme.antisymm

theorem IsExtreme.inter (hAB : IsExtreme 𝕜 A B) (hAC : IsExtreme 𝕜 A C) :
    IsExtreme 𝕜 A (B ∩ C) := by
  use Subset.trans inter_subset_left hAB.1
  rintro x₁ hx₁A x₂ hx₂A x ⟨hxB, hxC⟩ hx
  obtain ⟨hx₁B, hx₂B⟩ := hAB.2 hx₁A hx₂A hxB hx
  obtain ⟨hx₁C, hx₂C⟩ := hAC.2 hx₁A hx₂A hxC hx
  exact ⟨⟨hx₁B, hx₁C⟩, hx₂B, hx₂C⟩

protected theorem IsExtreme.mono (hAC : IsExtreme 𝕜 A C) (hBA : B ⊆ A) (hCB : C ⊆ B) :
    IsExtreme 𝕜 B C :=
  ⟨hCB, fun _ hx₁B _ hx₂B _ hxC hx ↦ hAC.2 (hBA hx₁B) (hBA hx₂B) hxC hx⟩

theorem isExtreme_iInter {ι : Sort*} [Nonempty ι] {F : ι → Set E}
    (hAF : ∀ i : ι, IsExtreme 𝕜 A (F i)) : IsExtreme 𝕜 A (⋂ i : ι, F i) := by
  obtain i := Classical.arbitrary ι
  refine ⟨iInter_subset_of_subset i (hAF i).1, fun x₁ hx₁A x₂ hx₂A x hxF hx ↦ ?_⟩
  simp_rw [mem_iInter] at hxF ⊢
  have h := fun i ↦ (hAF i).2 hx₁A hx₂A (hxF i) hx
  exact ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩

theorem isExtreme_biInter {F : Set (Set E)} (hF : F.Nonempty) (hA : ∀ B ∈ F, IsExtreme 𝕜 A B) :
    IsExtreme 𝕜 A (⋂ B ∈ F, B) := by
  haveI := hF.to_subtype
  simpa only [iInter_subtype] using isExtreme_iInter fun i : F ↦ hA _ i.2

theorem isExtreme_sInter {F : Set (Set E)} (hF : F.Nonempty) (hAF : ∀ B ∈ F, IsExtreme 𝕜 A B) :
    IsExtreme 𝕜 A (⋂₀ F) := by simpa [sInter_eq_biInter] using isExtreme_biInter hF hAF

theorem mem_extremePoints : x ∈ A.extremePoints 𝕜 ↔
    x ∈ A ∧ ∀ᵉ (x₁ ∈ A) (x₂ ∈ A), x ∈ openSegment 𝕜 x₁ x₂ → x₁ = x ∧ x₂ = x :=
  Iff.rfl

/-- In order to prove that a point `x` is an extreme point of a set `A`,
it suffices to show that `x ∈ A`
and for any `x₁`, `x₂` such that `x` belongs to the open segment `(x₁, x₂)`, we have `x₁ = x`.

The definition of `extremePoints` also requires `x₂ = x`, but this condition is redundant. -/
theorem mem_extremePoints_iff_left : x ∈ A.extremePoints 𝕜 ↔
    x ∈ A ∧ ∀ x₁ ∈ A, ∀ x₂ ∈ A, x ∈ openSegment 𝕜 x₁ x₂ → x₁ = x := by
  refine ⟨fun h ↦ ⟨h.1, fun x₁ hx₁ x₂ hx₂ hx ↦ (h.2 hx₁ hx₂ hx).1⟩, ?_⟩
  rintro ⟨hxA, Hx⟩
  use hxA
  refine fun x₁ hx₁ x₂ hx₂ hx ↦ ⟨Hx x₁ hx₁ x₂ hx₂ hx, Hx x₂ hx₂ x₁ hx₁ ?_⟩
  rwa [openSegment_symm]

/-- x is an extreme point to A iff {x} is an extreme set of A. -/
@[simp] lemma isExtreme_singleton : IsExtreme 𝕜 A {x} ↔ x ∈ A.extremePoints 𝕜 := by
  refine ⟨fun hx ↦ ⟨singleton_subset_iff.1 hx.1, fun x₁ hx₁ x₂ hx₂ ↦ hx.2 hx₁ hx₂ rfl⟩, ?_⟩
  rintro ⟨hxA, hAx⟩
  use singleton_subset_iff.2 hxA
  rintro x₁ hx₁A x₂ hx₂A y (rfl : y = x)
  exact hAx hx₁A hx₂A

alias ⟨IsExtreme.mem_extremePoints, _⟩ := isExtreme_singleton

theorem extremePoints_subset : A.extremePoints 𝕜 ⊆ A :=
  fun _ hx ↦ hx.1

@[simp]
theorem extremePoints_empty : (∅ : Set E).extremePoints 𝕜 = ∅ :=
  subset_empty_iff.1 extremePoints_subset

@[simp]
theorem extremePoints_singleton : ({x} : Set E).extremePoints 𝕜 = {x} :=
  extremePoints_subset.antisymm <|
    singleton_subset_iff.2 ⟨mem_singleton x, fun _ hx₁ _ hx₂ _ ↦ ⟨hx₁, hx₂⟩⟩

theorem inter_extremePoints_subset_extremePoints_of_subset (hBA : B ⊆ A) :
    B ∩ A.extremePoints 𝕜 ⊆ B.extremePoints 𝕜 :=
  fun _ ⟨hxB, hxA⟩ ↦ ⟨hxB, fun _ hx₁ _ hx₂ hx ↦ hxA.2 (hBA hx₁) (hBA hx₂) hx⟩

theorem IsExtreme.extremePoints_subset_extremePoints (hAB : IsExtreme 𝕜 A B) :
    B.extremePoints 𝕜 ⊆ A.extremePoints 𝕜 :=
  fun _ ↦ by simpa only [← isExtreme_singleton] using hAB.trans

theorem IsExtreme.extremePoints_eq (hAB : IsExtreme 𝕜 A B) :
    B.extremePoints 𝕜 = B ∩ A.extremePoints 𝕜 :=
  Subset.antisymm (fun _ hx ↦ ⟨hx.1, hAB.extremePoints_subset_extremePoints hx⟩)
    (inter_extremePoints_subset_extremePoints_of_subset hAB.1)

end SMul

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [AddCommGroup F] [∀ i, AddCommGroup (M i)]
  [Module 𝕜 E] [Module 𝕜 F] [∀ i, Module 𝕜 (M i)] {A B : Set E}

theorem IsExtreme.convex_diff [IsOrderedRing 𝕜] (hA : Convex 𝕜 A) (hAB : IsExtreme 𝕜 A B) :
    Convex 𝕜 (A \ B) :=
  convex_iff_openSegment_subset.2 fun _ ⟨hx₁A, hx₁B⟩ _ ⟨hx₂A, _⟩ _ hx ↦
    ⟨hA.openSegment_subset hx₁A hx₂A hx, fun hxB ↦ hx₁B (hAB.2 hx₁A hx₂A hxB hx).1⟩

@[simp]
theorem extremePoints_prod (s : Set E) (t : Set F) :
    (s ×ˢ t).extremePoints 𝕜 = s.extremePoints 𝕜 ×ˢ t.extremePoints 𝕜 := by
  ext
  refine (and_congr_right fun hx ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩).trans and_and_and_comm
  constructor
  · rintro x₁ hx₁ x₂ hx₂ hx_fst
    refine (h (mk_mem_prod hx₁ hx.2) (mk_mem_prod hx₂ hx.2) ?_).imp (congr_arg Prod.fst)
        (congr_arg Prod.fst)
    rw [← Prod.image_mk_openSegment_left]
    exact ⟨_, hx_fst, rfl⟩
  · rintro x₁ hx₁ x₂ hx₂ hx_snd
    refine (h (mk_mem_prod hx.1 hx₁) (mk_mem_prod hx.1 hx₂) ?_).imp (congr_arg Prod.snd)
        (congr_arg Prod.snd)
    rw [← Prod.image_mk_openSegment_right]
    exact ⟨_, hx_snd, rfl⟩
  · rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hx'⟩
    simp_rw [Prod.ext_iff]
    exact and_and_and_comm.1
        ⟨h.1 hx₁.1 hx₂.1 ⟨a, b, ha, hb, hab, congr_arg Prod.fst hx'⟩,
          h.2 hx₁.2 hx₂.2 ⟨a, b, ha, hb, hab, congr_arg Prod.snd hx'⟩⟩

@[simp]
theorem extremePoints_pi (s : ∀ i, Set (M i)) :
    (univ.pi s).extremePoints 𝕜 = univ.pi fun i ↦ (s i).extremePoints 𝕜 := by
  classical
  ext x
  simp only [mem_extremePoints, mem_pi, mem_univ, true_imp_iff, @forall_and ι]
  refine and_congr_right fun hx ↦ ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · rintro x₁ hx₁ x₂ hx₂ hi
    refine (h (update x i x₁) ?_ (update x i x₂) ?_ ?_).imp (fun h₁ ↦ by rw [← h₁, update_self])
        fun h₂ ↦ by rw [← h₂, update_self]
    iterate 2
      rintro j
      obtain rfl | hji := eq_or_ne j i
      · rwa [update_self]
      · rw [update_of_ne hji]
        exact hx _
    rw [← Pi.image_update_openSegment]
    exact ⟨_, hi, update_eq_self _ _⟩
  · rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hx'⟩
    simp_rw [funext_iff, ← forall_and]
    exact fun i ↦ h _ _ (hx₁ _) _ (hx₂ _) ⟨a, b, ha, hb, hab, congr_fun hx' _⟩

end OrderedSemiring

section OrderedRing
variable {L : Type*} [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [EquivLike L E F] [LinearEquivClass L 𝕜 E F]

lemma image_extremePoints (f : L) (s : Set E) :
    f '' extremePoints 𝕜 s = extremePoints 𝕜 (f '' s) := by
  ext b
  obtain ⟨a, rfl⟩ := EquivLike.surjective f b
  have : ∀ x y, f '' openSegment 𝕜 x y = openSegment 𝕜 (f x) (f y) :=
    image_openSegment _ (LinearMapClass.linearMap f).toAffineMap
  simp only [mem_extremePoints, (EquivLike.surjective f).forall,
    (EquivLike.injective f).mem_set_image, (EquivLike.injective f).eq_iff, ← this]

end OrderedRing

section LinearOrderedRing

variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [DenselyOrdered 𝕜] [NoZeroSMulDivisors 𝕜 E] {A : Set E} {x : E}

/-- A useful restatement using `segment`: `x` is an extreme point iff the only (closed) segments
that contain it are those with `x` as one of their endpoints. -/
theorem mem_extremePoints_iff_forall_segment : x ∈ A.extremePoints 𝕜 ↔
    x ∈ A ∧ ∀ᵉ (x₁ ∈ A) (x₂ ∈ A), x ∈ segment 𝕜 x₁ x₂ → x₁ = x ∨ x₂ = x := by
  refine and_congr_right fun hxA ↦ forall₄_congr fun x₁ h₁ x₂ h₂ ↦ ?_
  constructor
  · rw [← insert_endpoints_openSegment]
    rintro H (rfl | rfl | hx)
    exacts [Or.inl rfl, Or.inr rfl, Or.inl <| (H hx).1]
  · intro H hx
    rcases H (openSegment_subset_segment _ _ _ hx) with (rfl | rfl)
    exacts [⟨rfl, (left_mem_openSegment_iff.1 hx).symm⟩, ⟨right_mem_openSegment_iff.1 hx, rfl⟩]

theorem Convex.mem_extremePoints_iff_convex_diff (hA : Convex 𝕜 A) :
    x ∈ A.extremePoints 𝕜 ↔ x ∈ A ∧ Convex 𝕜 (A \ {x}) := by
  use fun hx ↦ ⟨hx.1, (isExtreme_singleton.2 hx).convex_diff hA⟩
  rintro ⟨hxA, hAx⟩
  refine mem_extremePoints_iff_forall_segment.2 ⟨hxA, fun x₁ hx₁ x₂ hx₂ hx ↦ ?_⟩
  rw [convex_iff_segment_subset] at hAx
  by_contra! h
  exact (hAx ⟨hx₁, fun hx₁ ↦ h.1 (mem_singleton_iff.2 hx₁)⟩
      ⟨hx₂, fun hx₂ ↦ h.2 (mem_singleton_iff.2 hx₂)⟩ hx).2 rfl

theorem Convex.mem_extremePoints_iff_mem_diff_convexHull_diff (hA : Convex 𝕜 A) :
    x ∈ A.extremePoints 𝕜 ↔ x ∈ A \ convexHull 𝕜 (A \ {x}) := by
  rw [hA.mem_extremePoints_iff_convex_diff, hA.convex_remove_iff_notMem_convexHull_remove,
    mem_diff]

theorem extremePoints_convexHull_subset : (convexHull 𝕜 A).extremePoints 𝕜 ⊆ A := by
  rintro x hx
  rw [(convex_convexHull 𝕜 _).mem_extremePoints_iff_convex_diff] at hx
  by_contra h
  exact (convexHull_min (subset_diff.2 ⟨subset_convexHull 𝕜 _, disjoint_singleton_right.2 h⟩) hx.2
    hx.1).2 rfl

end LinearOrderedRing
