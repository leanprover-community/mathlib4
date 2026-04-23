/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Segment
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Algebra.Module.LinearMap.Prod
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Module.Synonym
import Mathlib.Algebra.Order.Monoid.OrderDual
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.Lattice
import Mathlib.Init
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Star-convex sets

This file defines star-convex sets (aka star domains, star-shaped set, radially convex set).

A set is star-convex at `x` if every segment from `x` to a point in the set is contained in the set.

This is the prototypical example of a contractible set in homotopy theory (by scaling every point
towards `x`), but has wider uses.

Note that this has nothing to do with star rings, `Star` and co.

## Main declarations

* `StarConvex 𝕜 x s`: `s` is star-convex at `x` with scalars `𝕜`.

## Implementation notes

Instead of saying that a set is star-convex, we say a set is star-convex *at a point*. This has the
advantage of allowing us to talk about convexity as being "everywhere star-convexity" and of making
the union of star-convex sets be star-convex.

Incidentally, this choice means we don't need to assume a set is nonempty for it to be star-convex.
Concretely, the empty set is star-convex at every point.

## TODO

Balanced sets are star-convex.

The closure of a star-convex set is star-convex.

Star-convex sets are contractible.

A nonempty open star-convex set in `ℝ^n` is diffeomorphic to the entire space.
-/

@[expose] public section


open Set

open Convex Pointwise

variable {𝕜 E F : Type*}

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section SMul

variable (𝕜) [SMul 𝕜 E] [SMul 𝕜 F] (x : E) (s : Set E)

/-- Star-convexity of sets. `s` is star-convex at `x` if every segment from `x` to a point in `s` is
contained in `s`. -/
def StarConvex (𝕜 : Type*) {E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E] (x : E) (s : Set E) : Prop :=
  ∀ ⦃y : E⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s

variable {𝕜 x s} {t : Set E}

theorem starConvex_iff_segment_subset : StarConvex 𝕜 x s ↔ ∀ ⦃y⦄, y ∈ s → [x -[𝕜] y] ⊆ s := by
  constructor
  · rintro h y hy z ⟨a, b, ha, hb, hab, rfl⟩
    exact h hy ha hb hab
  · rintro h y hy a b ha hb hab
    exact h hy ⟨a, b, ha, hb, hab, rfl⟩

theorem StarConvex.segment_subset (h : StarConvex 𝕜 x s) {y : E} (hy : y ∈ s) : [x -[𝕜] y] ⊆ s :=
  starConvex_iff_segment_subset.1 h hy

theorem StarConvex.openSegment_subset (h : StarConvex 𝕜 x s) {y : E} (hy : y ∈ s) :
    openSegment 𝕜 x y ⊆ s :=
  (openSegment_subset_segment 𝕜 x y).trans (h.segment_subset hy)

/-- Alternative definition of star-convexity, in terms of pointwise set operations. -/
theorem starConvex_iff_pointwise_add_subset :
    StarConvex 𝕜 x s ↔ ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • {x} + b • s ⊆ s := by
  refine
    ⟨?_, fun h y hy a b ha hb hab =>
      h ha hb hab (add_mem_add (smul_mem_smul_set <| mem_singleton _) ⟨_, hy, rfl⟩)⟩
  rintro hA a b ha hb hab w ⟨au, ⟨u, rfl : u = x, rfl⟩, bv, ⟨v, hv, rfl⟩, rfl⟩
  exact hA hv ha hb hab

theorem starConvex_empty (x : E) : StarConvex 𝕜 x ∅ := fun _ hy => hy.elim

theorem starConvex_univ (x : E) : StarConvex 𝕜 x univ := fun _ _ _ _ _ _ _ => trivial

theorem StarConvex.inter (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 x t) : StarConvex 𝕜 x (s ∩ t) :=
  fun _ hy _ _ ha hb hab => ⟨hs hy.left ha hb hab, ht hy.right ha hb hab⟩

theorem starConvex_sInter {S : Set (Set E)} (h : ∀ s ∈ S, StarConvex 𝕜 x s) :
    StarConvex 𝕜 x (⋂₀ S) := fun _ hy _ _ ha hb hab s hs => h s hs (hy s hs) ha hb hab

theorem starConvex_iInter {ι : Sort*} {s : ι → Set E} (h : ∀ i, StarConvex 𝕜 x (s i)) :
    StarConvex 𝕜 x (⋂ i, s i) :=
  sInter_range s ▸ starConvex_sInter <| forall_mem_range.2 h

theorem starConvex_iInter₂ {ι : Sort*} {κ : ι → Sort*} {s : (i : ι) → κ i → Set E}
    (h : ∀ i j, StarConvex 𝕜 x (s i j)) : StarConvex 𝕜 x (⋂ (i) (j), s i j) :=
  starConvex_iInter fun i => starConvex_iInter (h i)

theorem StarConvex.union (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 x t) :
    StarConvex 𝕜 x (s ∪ t) := by
  rintro y (hy | hy) a b ha hb hab
  · exact Or.inl (hs hy ha hb hab)
  · exact Or.inr (ht hy ha hb hab)

theorem starConvex_iUnion {ι : Sort*} {s : ι → Set E} (hs : ∀ i, StarConvex 𝕜 x (s i)) :
    StarConvex 𝕜 x (⋃ i, s i) := by
  rintro y hy a b ha hb hab
  rw [mem_iUnion] at hy ⊢
  obtain ⟨i, hy⟩ := hy
  exact ⟨i, hs i hy ha hb hab⟩

theorem starConvex_iUnion₂ {ι : Sort*} {κ : ι → Sort*} {s : (i : ι) → κ i → Set E}
    (h : ∀ i j, StarConvex 𝕜 x (s i j)) : StarConvex 𝕜 x (⋃ (i) (j), s i j) :=
  starConvex_iUnion fun i => starConvex_iUnion (h i)

theorem starConvex_sUnion {S : Set (Set E)} (hS : ∀ s ∈ S, StarConvex 𝕜 x s) :
    StarConvex 𝕜 x (⋃₀ S) := by
  rw [sUnion_eq_iUnion]
  exact starConvex_iUnion fun s => hS _ s.2

theorem StarConvex.prod {y : F} {s : Set E} {t : Set F} (hs : StarConvex 𝕜 x s)
    (ht : StarConvex 𝕜 y t) : StarConvex 𝕜 (x, y) (s ×ˢ t) := fun _ hy _ _ ha hb hab =>
  ⟨hs hy.1 ha hb hab, ht hy.2 ha hb hab⟩

theorem starConvex_pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommMonoid (E i)] [∀ i, SMul 𝕜 (E i)]
    {x : ∀ i, E i} {s : Set ι} {t : ∀ i, Set (E i)} (ht : ∀ ⦃i⦄, i ∈ s → StarConvex 𝕜 (x i) (t i)) :
    StarConvex 𝕜 x (s.pi t) := fun _ hy _ _ ha hb hab i hi => ht hi (hy i hi) ha hb hab

end SMul

section Module

variable [Module 𝕜 E] [Module 𝕜 F] {x y z : E} {s : Set E}

theorem StarConvex.mem [ZeroLEOneClass 𝕜] (hs : StarConvex 𝕜 x s) (h : s.Nonempty) : x ∈ s := by
  obtain ⟨y, hy⟩ := h
  convert hs hy zero_le_one le_rfl (add_zero 1)
  rw [one_smul, zero_smul, add_zero]

theorem starConvex_iff_forall_pos (hx : x ∈ s) : StarConvex 𝕜 x s ↔
    ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s := by
  refine ⟨fun h y hy a b ha hb hab => h hy ha.le hb.le hab, ?_⟩
  intro h y hy a b ha hb hab
  obtain rfl | ha := ha.eq_or_lt
  · rw [zero_add] at hab
    rwa [hab, one_smul, zero_smul, zero_add]
  obtain rfl | hb := hb.eq_or_lt
  · rw [add_zero] at hab
    rwa [hab, one_smul, zero_smul, add_zero]
  exact h hy ha hb hab

theorem starConvex_iff_forall_ne_pos (hx : x ∈ s) :
    StarConvex 𝕜 x s ↔
      ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s := by
  refine ⟨fun h y hy _ a b ha hb hab => h hy ha.le hb.le hab, ?_⟩
  intro h y hy a b ha hb hab
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_add] at hab
    rwa [hab, zero_smul, one_smul, zero_add]
  obtain rfl | hb' := hb.eq_or_lt
  · rw [add_zero] at hab
    rwa [hab, zero_smul, one_smul, add_zero]
  obtain rfl | hxy := eq_or_ne x y
  · rwa [Convex.combo_self hab]
  exact h hy hxy ha' hb' hab

theorem starConvex_iff_openSegment_subset [ZeroLEOneClass 𝕜] (hx : x ∈ s) :
    StarConvex 𝕜 x s ↔ ∀ ⦃y⦄, y ∈ s → openSegment 𝕜 x y ⊆ s :=
  starConvex_iff_segment_subset.trans <|
    forall₂_congr fun _ hy => (openSegment_subset_iff_segment_subset hx hy).symm

theorem starConvex_singleton (x : E) : StarConvex 𝕜 x {x} := by
  rintro y (rfl : y = x) a b _ _ hab
  exact Convex.combo_self hab _

theorem StarConvex.linear_image (hs : StarConvex 𝕜 x s) (f : E →ₗ[𝕜] F) :
    StarConvex 𝕜 (f x) (f '' s) := by
  rintro _ ⟨y, hy, rfl⟩ a b ha hb hab
  exact ⟨a • x + b • y, hs hy ha hb hab, by rw [f.map_add, f.map_smul, f.map_smul]⟩

theorem StarConvex.is_linear_image (hs : StarConvex 𝕜 x s) {f : E → F} (hf : IsLinearMap 𝕜 f) :
    StarConvex 𝕜 (f x) (f '' s) :=
  hs.linear_image <| hf.mk' f

theorem StarConvex.linear_preimage {s : Set F} (f : E →ₗ[𝕜] F) (hs : StarConvex 𝕜 (f x) s) :
    StarConvex 𝕜 x (f ⁻¹' s) := by
  intro y hy a b ha hb hab
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul]
  exact hs hy ha hb hab

theorem StarConvex.is_linear_preimage {s : Set F} {f : E → F} (hs : StarConvex 𝕜 (f x) s)
    (hf : IsLinearMap 𝕜 f) : StarConvex 𝕜 x (preimage f s) :=
  hs.linear_preimage <| hf.mk' f

theorem StarConvex.add {t : Set E} (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t) :
    StarConvex 𝕜 (x + y) (s + t) := by
  rw [← add_image_prod]
  exact (hs.prod ht).is_linear_image IsLinearMap.isLinearMap_add

theorem StarConvex.add_left (hs : StarConvex 𝕜 x s) (z : E) :
    StarConvex 𝕜 (z + x) ((fun x => z + x) '' s) := by
  intro y hy a b ha hb hab
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨a • x + b • y', hs hy' ha hb hab, ?_⟩
  match_scalars <;> simp [hab]

theorem StarConvex.add_right (hs : StarConvex 𝕜 x s) (z : E) :
    StarConvex 𝕜 (x + z) ((fun x => x + z) '' s) := by
  intro y hy a b ha hb hab
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨a • x + b • y', hs hy' ha hb hab, ?_⟩
  match_scalars <;> simp [hab]

/-- The translation of a star-convex set is also star-convex. -/
theorem StarConvex.preimage_add_right (hs : StarConvex 𝕜 (z + x) s) :
    StarConvex 𝕜 x ((fun x => z + x) ⁻¹' s) := by
  intro y hy a b ha hb hab
  have h := hs hy ha hb hab
  rwa [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul] at h

/-- The translation of a star-convex set is also star-convex. -/
theorem StarConvex.preimage_add_left (hs : StarConvex 𝕜 (x + z) s) :
    StarConvex 𝕜 x ((fun x => x + z) ⁻¹' s) := by
  rw [add_comm] at hs
  simpa only [add_comm] using hs.preimage_add_right

end Module

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup E] [Module 𝕜 E] {x y : E}

theorem StarConvex.sub' {s : Set (E × E)} (hs : StarConvex 𝕜 (x, y) s) :
    StarConvex 𝕜 (x - y) ((fun x : E × E => x.1 - x.2) '' s) :=
  hs.is_linear_image IsLinearMap.isLinearMap_sub

end AddCommGroup

end OrderedSemiring

section OrderedCommSemiring

variable [CommSemiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F] {x : E} {s : Set E}

theorem StarConvex.smul (hs : StarConvex 𝕜 x s) (c : 𝕜) : StarConvex 𝕜 (c • x) (c • s) :=
  hs.linear_image <| LinearMap.lsmul _ _ c

theorem StarConvex.zero_smul (hs : StarConvex 𝕜 0 s) (c : 𝕜) : StarConvex 𝕜 0 (c • s) := by
  simpa using hs.smul c

theorem StarConvex.preimage_smul {c : 𝕜} (hs : StarConvex 𝕜 (c • x) s) :
    StarConvex 𝕜 x ((fun z => c • z) ⁻¹' s) :=
  hs.linear_preimage (LinearMap.lsmul _ _ c)

theorem StarConvex.affinity (hs : StarConvex 𝕜 x s) (z : E) (c : 𝕜) :
    StarConvex 𝕜 (z + c • x) ((fun x => z + c • x) '' s) := by
  have h := (hs.smul c).add_left z
  rwa [← image_smul, image_image] at h

end AddCommMonoid

end OrderedCommSemiring

section OrderedRing

variable [Ring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddRightMono 𝕜] [AddCommMonoid E] [SMulWithZero 𝕜 E] {s : Set E}

theorem starConvex_zero_iff :
    StarConvex 𝕜 0 s ↔ ∀ ⦃x : E⦄, x ∈ s → ∀ ⦃a : 𝕜⦄, 0 ≤ a → a ≤ 1 → a • x ∈ s := by
  refine
    forall_congr' fun x => forall_congr' fun _ => ⟨fun h a ha₀ ha₁ => ?_, fun h a b ha hb hab => ?_⟩
  · simpa only [sub_add_cancel, eq_self_iff_true, forall_true_left, zero_add, smul_zero] using
      h (sub_nonneg_of_le ha₁) ha₀
  · rw [smul_zero, zero_add]
    exact h hb (by rw [← hab]; exact le_add_of_nonneg_left ha)

end AddCommMonoid

section AddCommGroup

section AddRightMono

variable [AddRightMono 𝕜] [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]
  {x y : E} {s t : Set E}

theorem StarConvex.add_smul_mem (hs : StarConvex 𝕜 x s) (hy : x + y ∈ s) {t : 𝕜} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) : x + t • y ∈ s := by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by
    rw [smul_add, ← add_assoc, ← add_smul, sub_add_cancel, one_smul]
  rw [h]
  exact hs hy (sub_nonneg_of_le ht₁) ht₀ (sub_add_cancel _ _)

theorem StarConvex.smul_mem (hs : StarConvex 𝕜 0 s) (hx : x ∈ s) {t : 𝕜} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) : t • x ∈ s := by simpa using hs.add_smul_mem (by simpa using hx) ht₀ ht₁

theorem StarConvex.add_smul_sub_mem (hs : StarConvex 𝕜 x s) (hy : y ∈ s) {t : 𝕜} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) : x + t • (y - x) ∈ s := by
  apply hs.segment_subset hy
  rw [segment_eq_image']
  exact mem_image_of_mem _ ⟨ht₀, ht₁⟩

end AddRightMono

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {x y : E} {s t : Set E}

/-- The preimage of a star-convex set under an affine map is star-convex. -/
theorem StarConvex.affine_preimage (f : E →ᵃ[𝕜] F) {s : Set F} (hs : StarConvex 𝕜 (f x) s) :
    StarConvex 𝕜 x (f ⁻¹' s) := by
  intro y hy a b ha hb hab
  rw [mem_preimage, Convex.combo_affine_apply hab]
  exact hs hy ha hb hab

/-- The image of a star-convex set under an affine map is star-convex. -/
theorem StarConvex.affine_image (f : E →ᵃ[𝕜] F) {s : Set E} (hs : StarConvex 𝕜 x s) :
    StarConvex 𝕜 (f x) (f '' s) := by
  rintro y ⟨y', ⟨hy', hy'f⟩⟩ a b ha hb hab
  refine ⟨a • x + b • y', ⟨hs hy' ha hb hab, ?_⟩⟩
  rw [Convex.combo_affine_apply hab, hy'f]

theorem StarConvex.neg (hs : StarConvex 𝕜 x s) : StarConvex 𝕜 (-x) (-s) := by
  rw [← image_neg_eq_neg]
  exact hs.is_linear_image IsLinearMap.isLinearMap_neg

theorem StarConvex.sub (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t) :
    StarConvex 𝕜 (x - y) (s - t) := by
  simp_rw [sub_eq_add_neg]
  exact hs.add ht.neg

end AddCommGroup

section OrderedAddCommGroup

variable [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E]
  [IsStrictOrderedModule 𝕜 E] [PosSMulReflectLT 𝕜 E] {x y : E}

/-- If `x < y`, then `(Set.Iic x)ᶜ` is star convex at `y`. -/
lemma starConvex_compl_Iic (h : x < y) : StarConvex 𝕜 y (Iic x)ᶜ := by
  refine (starConvex_iff_forall_pos <| by simp [h.not_ge]).mpr fun z hz a b ha hb hab ↦ ?_
  rw [mem_compl_iff, mem_Iic] at hz ⊢
  contrapose hz
  refine (lt_of_smul_lt_smul_of_nonneg_left ?_ hb.le).le
  calc
    b • z ≤ (a + b) • x - a • y := by rwa [le_sub_iff_add_le', hab, one_smul]
    _ < b • x := by
      rw [add_smul, sub_lt_iff_lt_add']
      gcongr

/-- If `x < y`, then `(Set.Ici y)ᶜ` is star convex at `x`. -/
lemma starConvex_compl_Ici (h : x < y) : StarConvex 𝕜 x (Ici y)ᶜ :=
  starConvex_compl_Iic (E := Eᵒᵈ) h

end OrderedAddCommGroup

end OrderedRing

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

section AddCommGroup

variable [AddCommGroup E] [Module 𝕜 E] {x : E} {s : Set E}

/-- Alternative definition of star-convexity, using division. -/
theorem starConvex_iff_div : StarConvex 𝕜 x s ↔ ∀ ⦃y⦄, y ∈ s →
    ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → 0 < a + b → (a / (a + b)) • x + (b / (a + b)) • y ∈ s :=
  ⟨fun h y hy a b ha hb hab => by
    apply h hy
    · positivity
    · positivity
    · rw [← add_div]
      exact div_self hab.ne',
  fun h y hy a b ha hb hab => by
    have h' := h hy ha hb
    rw [hab, div_one, div_one] at h'
    exact h' zero_lt_one⟩

theorem StarConvex.mem_smul (hs : StarConvex 𝕜 0 s) (hx : x ∈ s) {t : 𝕜} (ht : 1 ≤ t) :
    x ∈ t • s := by
  rw [mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans_le ht).ne']
  exact hs.smul_mem hx (by positivity) (inv_le_one_of_one_le₀ ht)

end AddCommGroup

end LinearOrderedField

/-!
#### Star-convex sets in an ordered space

Relates `starConvex` and `Set.ordConnected`.
-/

section OrdConnected

/-- If `s` is an order-connected set in an ordered module over an ordered semiring
and all elements of `s` are comparable with `x ∈ s`, then `s` is `StarConvex` at `x`. -/
theorem Set.OrdConnected.starConvex [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E] {x : E} {s : Set E} (hs : s.OrdConnected)
    (hx : x ∈ s) (h : ∀ y ∈ s, x ≤ y ∨ y ≤ x) : StarConvex 𝕜 x s := by
  intro y hy a b ha hb hab
  obtain hxy | hyx := h _ hy
  · refine hs.out hx hy (mem_Icc.2 ⟨?_, ?_⟩)
    · calc
        x = a • x + b • x := (Convex.combo_self hab _).symm
        _ ≤ a • x + b • y := by gcongr
    calc
      a • x + b • y ≤ a • y + b • y := by gcongr
      _ = y := Convex.combo_self hab _
  · refine hs.out hy hx (mem_Icc.2 ⟨?_, ?_⟩)
    · calc
        y = a • y + b • y := (Convex.combo_self hab _).symm
        _ ≤ a • x + b • y := by gcongr
    calc
      a • x + b • y ≤ a • x + b • x := by gcongr
      _ = x := Convex.combo_self hab _

theorem starConvex_iff_ordConnected [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {x : 𝕜} {s : Set 𝕜} (hx : x ∈ s) :
    StarConvex 𝕜 x s ↔ s.OrdConnected := by
  simp_rw [ordConnected_iff_uIcc_subset_left hx, starConvex_iff_segment_subset, segment_eq_uIcc]

alias ⟨StarConvex.ordConnected, _⟩ := starConvex_iff_ordConnected

end OrdConnected
