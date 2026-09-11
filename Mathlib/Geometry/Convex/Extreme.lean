/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Geometry.Convex.Hull

/-!
# Extreme sets

This file defines extreme sets and extreme points of a set in a convex space.

An extreme set of `A` is a subset of `A` that is as far as it can get in any outward direction: If
point `x` is in it and point `y ∈ A`, then the line passing through `x` and `y` leaves `A` at `x`.
This is an analytic notion of "being on the side of". It is weaker than being exposed.

Since a convex space only comes with convex combinations, we phrase extremeness in terms of
`Convexity.convexCombPair` rather than of (open) segments: `B` is extreme in `A` when a binary
convex combination of points of `A` with *positive* weights can only land in `B` if both points
already lie in `B`.

## Main declarations

* `Convexity.IsExtremeSet R A B`: States that `B` is an extreme set of `A` (in the literature, `A`
  is often implicit).
* `Convexity.extremePoints R A`: Set of extreme points of `A` (corresponding to extreme singletons).
* `Convexity.IsConvexSet.mem_extremePoints_iff_isConvexSet_sdiff`: A useful equivalent condition to
  being an extreme point: `x` is an extreme point iff `A \ {x}` is convex. This needs the ambient
  convex space to be cancellative, see `Convexity.IsCancelConvexSpace`.

## Implementation notes

The exact definition of extremeness has been carefully chosen so as to make as many lemmas
unconditional (in particular, the Krein-Milman lemma doesn't need the set to be convex!).
In practice, `A` is often assumed to be a convex set.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

## TODO

Replace `IsExtreme` and `Set.extremePoints` with `Convexity.IsExtremeSet` and
`Convexity.extremePoints`.
-/

open Function Set

public section

namespace Convexity
variable {ι R K X Y : Type*}

section Semiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X] [ConvexSpace R Y]

variable (R) in
/-- A set `B` is an extreme subset of `A` if `B ⊆ A` and a binary convex combination with positive
weights of points of `A` lies in `B` only if both points already lie in `B`.

Our definition only requires that the first of the two points lies in `B`, but by symmetry of binary
convex combinations the second point must lie in `B` too.
See `Convexity.IsExtremeSet.right_mem_of_convexCombPair_mem`. -/
@[mk_iff]
structure IsExtremeSet (A B : Set X) : Prop where
  subset : B ⊆ A
  left_mem_of_convexCombPair_mem : ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → ∀ ⦃a b : R⦄ (ha : 0 < a)
    (hb : 0 < b) (hab : a + b = 1), convexCombPair a b ha.le hb.le hab x y ∈ B → x ∈ B

variable (R) in
/-- A point `x` is an extreme point of a set `A` if the only way to write `x` as a binary convex
combination with positive weights of points of `A` is the trivial one. -/
@[expose]
def extremePoints (A : Set X) : Set X :=
  {x ∈ A | ∀ ⦃y⦄, y ∈ A → ∀ ⦃z⦄, z ∈ A → ∀ ⦃a b : R⦄ (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1),
    convexCombPair a b ha.le hb.le hab y z = x → y = x}

@[refl]
protected lemma IsExtremeSet.refl (A : Set X) : IsExtremeSet R A A :=
  ⟨Subset.rfl, fun _ hx _ _ _ _ _ _ _ _ ↦ hx⟩

variable {A B C : Set X} {x : X}

protected lemma IsExtremeSet.rfl : IsExtremeSet R A A := .refl A

lemma IsExtremeSet.right_mem_of_convexCombPair_mem (h : IsExtremeSet R A B) {y : X}
    (hx : x ∈ A) (hy : y ∈ A) {a b : R} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hmem : convexCombPair a b ha.le hb.le hab x y ∈ B) : y ∈ B :=
  h.left_mem_of_convexCombPair_mem hy hx hb ha ((add_comm _ _).trans hab) <| by
    rwa [convexCombPair_symm]

@[trans]
protected lemma IsExtremeSet.trans (hAB : IsExtremeSet R A B) (hBC : IsExtremeSet R B C) :
    IsExtremeSet R A C where
  subset := hBC.subset.trans hAB.subset
  left_mem_of_convexCombPair_mem _ hx _ hy _ _ ha hb hab hmem :=
    hBC.left_mem_of_convexCombPair_mem
      (hAB.left_mem_of_convexCombPair_mem hx hy ha hb hab (hBC.subset hmem))
      (hAB.right_mem_of_convexCombPair_mem hx hy ha hb hab (hBC.subset hmem)) ha hb hab hmem

protected lemma IsExtremeSet.antisymm :
    Std.Antisymm (IsExtremeSet R : Set X → Set X → Prop) :=
  ⟨fun _ _ hAB hBA ↦ hBA.subset.antisymm hAB.subset⟩

instance : IsPartialOrder (Set X) (IsExtremeSet R) where
  refl := .refl
  trans _ _ _ := .trans
  __ := IsExtremeSet.antisymm

protected lemma IsExtremeSet.inter (hAB : IsExtremeSet R A B) (hAC : IsExtremeSet R A C) :
    IsExtremeSet R A (B ∩ C) where
  subset := inter_subset_left.trans hAB.subset
  left_mem_of_convexCombPair_mem _ hx _ hy _ _ ha hb hab hmem :=
    ⟨hAB.left_mem_of_convexCombPair_mem hx hy ha hb hab hmem.1,
      hAC.left_mem_of_convexCombPair_mem hx hy ha hb hab hmem.2⟩

protected lemma IsExtremeSet.mono (hAC : IsExtremeSet R A C) (hBA : B ⊆ A) (hCB : C ⊆ B) :
    IsExtremeSet R B C :=
  ⟨hCB, fun _ hx _ hy _ _ ha hb hab hmem ↦
    hAC.left_mem_of_convexCombPair_mem (hBA hx) (hBA hy) ha hb hab hmem⟩

lemma isExtremeSet_iInter {ι : Sort*} [Nonempty ι] {F : ι → Set X}
    (hAF : ∀ i, IsExtremeSet R A (F i)) : IsExtremeSet R A (⋂ i, F i) := by
  inhabit ι
  refine ⟨iInter_subset_of_subset default (hAF default).subset,
    fun x hx y hy a b ha hb hab hmem ↦ ?_⟩
  rw [mem_iInter] at hmem ⊢
  exact fun i ↦ (hAF i).left_mem_of_convexCombPair_mem hx hy ha hb hab (hmem i)

lemma isExtremeSet_biInter {F : Set (Set X)} (hF : F.Nonempty)
    (hA : ∀ B ∈ F, IsExtremeSet R A B) : IsExtremeSet R A (⋂ B ∈ F, B) := by
  have := hF.to_subtype
  simpa only [iInter_subtype] using isExtremeSet_iInter fun i : F ↦ hA _ i.2

lemma isExtremeSet_sInter {F : Set (Set X)} (hF : F.Nonempty)
    (hAF : ∀ B ∈ F, IsExtremeSet R A B) : IsExtremeSet R A (⋂₀ F) := by
  simpa [sInter_eq_biInter] using isExtremeSet_biInter hF hAF

/-- A point `x` is an extreme point of a set `A` iff `x ∈ A` and for any `y`, `z` such that `x` is a
convex combination of `y` and `z` with positive weights, we have `y = x` and `z = x`.

The conclusion `z = x` is redundant, hence the definition of `Convexity.extremePoints` only asks for
`y = x`. See `Convexity.mem_extremePoints_iff_left`. -/
lemma mem_extremePoints : x ∈ extremePoints R A ↔ x ∈ A ∧
    ∀ y ∈ A, ∀ z ∈ A, ∀ (a b : R) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1),
      convexCombPair a b ha.le hb.le hab y z = x → y = x ∧ z = x := by
  refine ⟨fun h ↦ ⟨h.1, fun y hy z hz a b ha hb hab hmem ↦
      ⟨h.2 hy hz ha hb hab hmem, ?_⟩⟩,
    fun h ↦ ⟨h.1, fun y hy z hz a b ha hb hab hmem ↦ (h.2 y hy z hz a b ha hb hab hmem).1⟩⟩
  refine h.2 hz hy hb ha ((add_comm _ _).trans hab) ?_
  rwa [convexCombPair_symm]

/-- A point `x` is an extreme point of a set `A` iff `x ∈ A` and for any `y`, `z` such that `x` is a
convex combination of `y` and `z` with positive weights, we have `y = x`. -/
lemma mem_extremePoints_iff_left : x ∈ extremePoints R A ↔ x ∈ A ∧
    ∀ y ∈ A, ∀ z ∈ A, ∀ (a b : R) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1),
      convexCombPair a b ha.le hb.le hab y z = x → y = x :=
  .rfl

/-- `x` is an extreme point of `A` iff `{x}` is an extreme set of `A`. -/
@[simp] lemma isExtremeSet_singleton : IsExtremeSet R A {x} ↔ x ∈ extremePoints R A := by
  simp [isExtremeSet_iff, extremePoints]

alias ⟨IsExtremeSet.mem_extremePoints, _⟩ := isExtremeSet_singleton

lemma extremePoints_subset_self : extremePoints R A ⊆ A := fun _ hx ↦ hx.1

variable (R) in
@[simp] lemma extremePoints_empty : extremePoints R (∅ : Set X) = ∅ :=
  subset_empty_iff.1 extremePoints_subset_self

variable (R x) in
@[simp] lemma extremePoints_singleton : extremePoints R ({x} : Set X) = {x} :=
  extremePoints_subset_self.antisymm <|
    singleton_subset_iff.2 ⟨mem_singleton x, fun _ hy _ _ _ _ _ _ _ _ ↦ hy⟩

lemma inter_extremePoints_subset_extremePoints_of_subset (hBA : B ⊆ A) :
    B ∩ extremePoints R A ⊆ extremePoints R B :=
  fun _ ⟨hxB, hxA⟩ ↦ ⟨hxB, fun _ hy _ hz _ _ ha hb hab hmem ↦
    hxA.2 (hBA hy) (hBA hz) ha hb hab hmem⟩

lemma IsExtremeSet.extremePoints_subset_extremePoints (hAB : IsExtremeSet R A B) :
    extremePoints R B ⊆ extremePoints R A :=
  fun _ ↦ by simpa only [← isExtremeSet_singleton] using hAB.trans

lemma IsExtremeSet.extremePoints_eq_inter (hAB : IsExtremeSet R A B) :
    extremePoints R B = B ∩ extremePoints R A :=
  subset_antisymm (fun _ hx ↦ ⟨hx.1, hAB.extremePoints_subset_extremePoints hx⟩)
    (inter_extremePoints_subset_extremePoints_of_subset hAB.subset)

@[nontriviality]
lemma extremePoints_eq_self_of_subsingleton [Subsingleton X] (A : Set X) : extremePoints R A = A :=
  extremePoints_subset_self.antisymm fun _ h ↦ ⟨h, fun _ _ _ _ _ _ _ _ _ _ ↦ Subsingleton.elim ..⟩

@[simp]
lemma extremePoints_prod (s : Set X) (t : Set Y) :
    extremePoints R (s ×ˢ t) = extremePoints R s ×ˢ extremePoints R t := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨⟨hxs, hyt⟩, h⟩
    refine ⟨⟨hxs, fun x₁ hx₁ x₂ hx₂ a b ha hb hab hmem ↦ ?_⟩,
      hyt, fun y₁ hy₁ y₂ hy₂ a b ha hb hab hmem ↦ ?_⟩
    · exact congrArg Prod.fst <| h (mk_mem_prod hx₁ hyt) (mk_mem_prod hx₂ hyt) ha hb hab <|
        Prod.ext_iff.2 ⟨by simpa using hmem, by simp⟩
    · exact congrArg Prod.snd <| h (mk_mem_prod hxs hy₁) (mk_mem_prod hxs hy₂) ha hb hab <|
        Prod.ext_iff.2 ⟨by simp, by simpa using hmem⟩
  · rintro ⟨⟨hxs, hx⟩, hyt, hy⟩
    refine ⟨⟨hxs, hyt⟩, ?_⟩
    rintro ⟨x₁, y₁⟩ hxy₁ ⟨x₂, y₂⟩ hxy₂ a b ha hb hab hmem
    exact Prod.ext_iff.2 ⟨hx hxy₁.1 hxy₂.1 ha hb hab (by simpa using congrArg Prod.fst hmem),
      hy hxy₁.2 hxy₂.2 ha hb hab (by simpa using congrArg Prod.snd hmem)⟩

@[simp]
lemma extremePoints_pi {X : ι → Type*} [∀ i, ConvexSpace R (X i)] (s : ∀ i, Set (X i)) :
    extremePoints R (univ.pi s) = univ.pi fun i ↦ extremePoints R (s i) := by
  classical
  ext x
  simp only [mem_extremePoints_iff_left, mem_univ_pi, @forall_and ι]
  refine and_congr_right fun hx ↦ ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · rintro x₁ hx₁ x₂ hx₂ a b ha hb hab hmem
    rw [← update_self i x₁ x, h (update x i x₁) ?_ (update x i x₂) ?_ a b ha hb hab ?_]
    · rintro j
      obtain rfl | hji := eq_or_ne j i <;> simp [*]
    · rintro j
      obtain rfl | hji := eq_or_ne j i <;> simp [*]
    · funext j
      obtain rfl | hji := eq_or_ne j i <;> simp [*]
  · rintro x₁ hx₁ x₂ hx₂ a b ha hb hab hmem
    funext i
    exact h i _ (hx₁ i) _ (hx₂ i) a b ha hb hab (by simpa using congrFun hmem i)

/-- The image of the extreme points of `A` under an injective affine map `f` is the set of extreme
points of the image of `A`. -/
lemma image_extremePoints {f : X → Y} (hf : IsAffineMap R f) (hfi : Injective f) (A : Set X) :
    f '' extremePoints R A = extremePoints R (f '' A) := by
  refine subset_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨mem_image_of_mem _ hx.1, ?_⟩
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ a b ha hb hab hmem
    exact congrArg f <| hx.2 hy hz ha hb hab <| hfi <| by rwa [hf.map_convexCombPair]
  · rintro _ ⟨⟨x, hx, rfl⟩, hfx⟩
    refine mem_image_of_mem _ ⟨hx, fun y hy z hz a b ha hb hab hmem ↦ hfi ?_⟩
    exact hfx (mem_image_of_mem _ hy) (mem_image_of_mem _ hz) ha hb hab <| by
      rw [← hf.map_convexCombPair, hmem]

end Semiring

section Field
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [ConvexSpace K X] {A B : Set X} {x : X}

protected lemma IsExtremeSet.isConvexSet_sdiff (hA : IsConvexSet K A)
    (hAB : IsExtremeSet K A B) : IsConvexSet K (A \ B) := by
  refine .of_convexCombPair_mem fun a b ha hb hab x hx y hy ↦
    ⟨hA.convexCombPair_mem hx.1 hy.1 ha hb hab, fun hmem ↦ ?_⟩
  obtain rfl | ha' := ha.eq_or_lt
  · obtain rfl : b = 1 := by simpa using hab
    exact hy.2 (by simpa using hmem)
  obtain rfl | hb' := hb.eq_or_lt
  · obtain rfl : a = 1 := by simpa using hab
    exact hx.2 (by simpa using hmem)
  exact hx.2 <| hAB.left_mem_of_convexCombPair_mem hx.1 hy.1 ha' hb' hab hmem

lemma extremePoints_convexHull_subset : extremePoints K (convexHull K A) ⊆ A := by
  rintro x hx
  by_contra h
  exact (convexHull_min (subset_sdiff.2 ⟨subset_convexHull_self, disjoint_singleton_right.2 h⟩)
    ((isExtremeSet_singleton.2 hx).isConvexSet_sdiff .convexHull) hx.1).2 rfl

variable [IsCancelConvexSpace K X]

/-- A useful restatement allowing the weights to merely be nonnegative: `x` is an extreme point of
`A` iff the only ways to write `x` as a binary convex combination of points of `A` are the ones
having `x` as one of the two points. -/
lemma mem_extremePoints_iff_forall_nonneg : x ∈ extremePoints K A ↔ x ∈ A ∧
    ∀ y ∈ A, ∀ z ∈ A, ∀ (a b : K) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
      convexCombPair a b ha hb hab y z = x → y = x ∨ z = x := by
  rw [mem_extremePoints_iff_left]
  refine and_congr_right fun hxA ↦ ⟨fun h y hy z hz a b ha hb hab hmem ↦ ?_,
    fun h y hy z hz a b ha hb hab hmem ↦ ?_⟩
  · obtain rfl | ha' := ha.eq_or_lt
    · obtain rfl : b = 1 := by simpa using hab
      exact .inr (by simpa using hmem)
    obtain rfl | hb' := hb.eq_or_lt
    · obtain rfl : a = 1 := by simpa using hab
      exact .inl (by simpa using hmem)
    exact .inl (h y hy z hz a b ha' hb' hab hmem)
  · obtain hy' | rfl := h y hy z hz a b ha.le hb.le hab hmem
    · exact hy'
    exact (convexCombPair_eq_right ha hb.le hab).1 hmem

lemma IsConvexSet.mem_extremePoints_iff_isConvexSet_sdiff (hA : IsConvexSet K A) :
    x ∈ extremePoints K A ↔ x ∈ A ∧ IsConvexSet K (A \ {x}) := by
  refine ⟨fun hx ↦ ⟨hx.1, (isExtremeSet_singleton.2 hx).isConvexSet_sdiff hA⟩, ?_⟩
  rintro ⟨hxA, hAx⟩
  refine mem_extremePoints_iff_forall_nonneg.2 ⟨hxA, fun y hy z hz a b ha hb hab hmem ↦ ?_⟩
  by_contra! h
  exact (hmem ▸ hAx.convexCombPair_mem ⟨hy, h.1⟩ ⟨hz, h.2⟩ ha hb hab).2 rfl

lemma IsConvexSet.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff (hA : IsConvexSet K A) :
    x ∈ extremePoints K A ↔ x ∈ A \ convexHull K (A \ {x}) := by
  rw [hA.mem_extremePoints_iff_isConvexSet_sdiff, hA.sdiff_singleton_iff_notMem_convexHull,
    mem_sdiff]

end Field
end Convexity
