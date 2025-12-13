/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Ring.Action.Pointwise.Set
public import Mathlib.Analysis.Convex.Star
public import Mathlib.Tactic.Field
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.Tactic.NoncommRing

/-!
# Convex sets

In a 𝕜-vector space, we define the following property:
* `Convex 𝕜 s`: A set `s` is convex if for any two points `x y ∈ s` it includes `segment 𝕜 x y`.

We provide various equivalent versions, and prove that some specific sets are convex.

## TODO

Generalize all this file to affine spaces.
-/

@[expose] public section


variable {𝕜 E F β : Type*}

open LinearMap Set

open scoped Convex Pointwise

/-! ### Convexity of sets -/


section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section SMul

variable (𝕜) [SMul 𝕜 E] [SMul 𝕜 F] (s : Set E) {x : E}

/-- Convexity of sets. -/
def Convex : Prop :=
  ∀ ⦃x : E⦄, x ∈ s → StarConvex 𝕜 x s

variable {𝕜 s}

theorem Convex.starConvex (hs : Convex 𝕜 s) (hx : x ∈ s) : StarConvex 𝕜 x s :=
  hs hx

theorem convex_iff_segment_subset : Convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → [x -[𝕜] y] ⊆ s :=
  forall₂_congr fun _ _ => starConvex_iff_segment_subset

theorem Convex.segment_subset (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    [x -[𝕜] y] ⊆ s :=
  convex_iff_segment_subset.1 h hx hy

theorem Convex.openSegment_subset (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    openSegment 𝕜 x y ⊆ s :=
  (openSegment_subset_segment 𝕜 x y).trans (h.segment_subset hx hy)

theorem convex_iff_add_mem : Convex 𝕜 s ↔
    ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s := by
  simp_rw [convex_iff_segment_subset, segment_subset_iff]

/-- Alternative definition of set convexity, in terms of pointwise set operations. -/
theorem convex_iff_pointwise_add_subset :
    Convex 𝕜 s ↔ ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • s + b • s ⊆ s :=
  Iff.intro
    (by
      rintro hA a b ha hb hab w ⟨au, ⟨u, hu, rfl⟩, bv, ⟨v, hv, rfl⟩, rfl⟩
      exact hA hu hv ha hb hab)
    fun h _ hx _ hy _ _ ha hb hab => (h ha hb hab) (Set.add_mem_add ⟨_, hx, rfl⟩ ⟨_, hy, rfl⟩)

alias ⟨Convex.set_combo_subset, _⟩ := convex_iff_pointwise_add_subset

theorem convex_empty : Convex 𝕜 (∅ : Set E) := fun _ => False.elim

theorem convex_univ : Convex 𝕜 (Set.univ : Set E) := fun _ _ => starConvex_univ _

theorem Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s ∩ t) :=
  fun _ hx => (hs hx.1).inter (ht hx.2)

theorem convex_sInter {S : Set (Set E)} (h : ∀ s ∈ S, Convex 𝕜 s) : Convex 𝕜 (⋂₀ S) := fun _ hx =>
  starConvex_sInter fun _ hs => h _ hs <| hx _ hs

theorem convex_iInter {ι : Sort*} {s : ι → Set E} (h : ∀ i, Convex 𝕜 (s i)) :
    Convex 𝕜 (⋂ i, s i) :=
  sInter_range s ▸ convex_sInter <| forall_mem_range.2 h

theorem convex_iInter₂ {ι : Sort*} {κ : ι → Sort*} {s : (i : ι) → κ i → Set E}
    (h : ∀ i j, Convex 𝕜 (s i j)) : Convex 𝕜 (⋂ (i) (j), s i j) :=
  convex_iInter fun i => convex_iInter <| h i

theorem Convex.prod {s : Set E} {t : Set F} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) :
    Convex 𝕜 (s ×ˢ t) := fun _ hx => (hs hx.1).prod (ht hx.2)

theorem convex_pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommMonoid (E i)] [∀ i, SMul 𝕜 (E i)]
    {s : Set ι} {t : ∀ i, Set (E i)} (ht : ∀ ⦃i⦄, i ∈ s → Convex 𝕜 (t i)) : Convex 𝕜 (s.pi t) :=
  fun _ hx => starConvex_pi fun _ hi => ht hi <| hx _ hi

theorem Directed.convex_iUnion {ι : Sort*} {s : ι → Set E} (hdir : Directed (· ⊆ ·) s)
    (hc : ∀ ⦃i : ι⦄, Convex 𝕜 (s i)) : Convex 𝕜 (⋃ i, s i) := by
  rintro x hx y hy a b ha hb hab
  rw [mem_iUnion] at hx hy ⊢
  obtain ⟨i, hx⟩ := hx
  obtain ⟨j, hy⟩ := hy
  obtain ⟨k, hik, hjk⟩ := hdir i j
  exact ⟨k, hc (hik hx) (hjk hy) ha hb hab⟩

theorem DirectedOn.convex_sUnion {c : Set (Set E)} (hdir : DirectedOn (· ⊆ ·) c)
    (hc : ∀ ⦃A : Set E⦄, A ∈ c → Convex 𝕜 A) : Convex 𝕜 (⋃₀ c) := by
  rw [sUnion_eq_iUnion]
  exact (directedOn_iff_directed.1 hdir).convex_iUnion fun A => hc A.2

theorem Convex.setOf_const_imp {P : Prop} (hs : Convex 𝕜 s) : Convex 𝕜 {x | P → x ∈ s} := by
  by_cases hP : P <;> simp [hP, hs, convex_univ]

end SMul

section Module

variable [Module 𝕜 E] [Module 𝕜 F] {s : Set E} {x : E}

theorem convex_iff_openSegment_subset [ZeroLEOneClass 𝕜] :
    Convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → openSegment 𝕜 x y ⊆ s :=
  forall₂_congr fun _ => starConvex_iff_openSegment_subset

theorem convex_iff_forall_pos :
    Convex 𝕜 s ↔
      ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s :=
  forall₂_congr fun _ => starConvex_iff_forall_pos

theorem convex_iff_pairwise_pos : Convex 𝕜 s ↔
    s.Pairwise fun x y => ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s := by
  refine convex_iff_forall_pos.trans ⟨fun h x hx y hy _ => h hx hy, ?_⟩
  intro h x hx y hy a b ha hb hab
  obtain rfl | hxy := eq_or_ne x y
  · rwa [Convex.combo_self hab]
  · exact h hx hy hxy ha hb hab

theorem Convex.starConvex_iff [ZeroLEOneClass 𝕜] (hs : Convex 𝕜 s) (h : s.Nonempty) :
    StarConvex 𝕜 x s ↔ x ∈ s :=
  ⟨fun hxs => hxs.mem h, hs.starConvex⟩

protected theorem Set.Subsingleton.convex {s : Set E} (h : s.Subsingleton) : Convex 𝕜 s :=
  convex_iff_pairwise_pos.mpr (h.pairwise _)

@[simp] theorem convex_singleton (c : E) : Convex 𝕜 ({c} : Set E) :=
  subsingleton_singleton.convex

theorem convex_zero : Convex 𝕜 (0 : Set E) :=
  convex_singleton _

theorem convex_segment [IsOrderedRing 𝕜] (x y : E) : Convex 𝕜 [x -[𝕜] y] := by
  rintro p ⟨ap, bp, hap, hbp, habp, rfl⟩ q ⟨aq, bq, haq, hbq, habq, rfl⟩ a b ha hb hab
  refine
    ⟨a * ap + b * aq, a * bp + b * bq, add_nonneg (mul_nonneg ha hap) (mul_nonneg hb haq),
      add_nonneg (mul_nonneg ha hbp) (mul_nonneg hb hbq), ?_, ?_⟩
  · rw [add_add_add_comm, ← mul_add, ← mul_add, habp, habq, mul_one, mul_one, hab]
  · match_scalars <;> noncomm_ring

/-- See `Convex.semilinear_image` for a version for semilinar maps, but requiring that `𝕜` be a
  linear order, instead of just a partial order. -/
theorem Convex.linear_image (hs : Convex 𝕜 s) (f : E →ₗ[𝕜] F) : Convex 𝕜 (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  exact ⟨a • x + b • y, hs hx hy ha hb hab, by rw [f.map_add, f.map_smul, f.map_smul]⟩

theorem Convex.is_linear_image (hs : Convex 𝕜 s) {f : E → F} (hf : IsLinearMap 𝕜 f) :
    Convex 𝕜 (f '' s) :=
  hs.linear_image <| hf.mk' f

theorem Convex.linear_preimage {s : Set F} (hs : Convex 𝕜 s) (f : E →ₗ[𝕜] F) : Convex 𝕜 (f ⁻¹' s) :=
  fun x hx y hy a b ha hb hab => by
    rw [mem_preimage, f.map_add, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]
    exact hs hx hy ha hb hab

theorem Convex.is_linear_preimage {s : Set F} (hs : Convex 𝕜 s) {f : E → F} (hf : IsLinearMap 𝕜 f) :
    Convex 𝕜 (f ⁻¹' s) := hs.linear_preimage <| hf.mk' f

theorem Convex.add {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s + t) := by
  rw [← add_image_prod]
  exact (hs.prod ht).is_linear_image IsLinearMap.isLinearMap_add

variable (𝕜 E)

/-- The convex sets form an additive submonoid under pointwise addition. -/
noncomputable def convexAddSubmonoid : AddSubmonoid (Set E) where
  carrier := {s : Set E | Convex 𝕜 s}
  zero_mem' := convex_zero
  add_mem' := Convex.add

@[simp, norm_cast]
theorem coe_convexAddSubmonoid : ↑(convexAddSubmonoid 𝕜 E) = {s : Set E | Convex 𝕜 s} :=
  rfl

variable {𝕜 E}

@[simp]
theorem mem_convexAddSubmonoid {s : Set E} : s ∈ convexAddSubmonoid 𝕜 E ↔ Convex 𝕜 s :=
  Iff.rfl

theorem convex_list_sum {l : List (Set E)} (h : ∀ i ∈ l, Convex 𝕜 i) : Convex 𝕜 l.sum :=
  (convexAddSubmonoid 𝕜 E).list_sum_mem h

theorem convex_multiset_sum {s : Multiset (Set E)} (h : ∀ i ∈ s, Convex 𝕜 i) : Convex 𝕜 s.sum :=
  (convexAddSubmonoid 𝕜 E).multiset_sum_mem _ h

theorem convex_sum {ι} {s : Finset ι} (t : ι → Set E) (h : ∀ i ∈ s, Convex 𝕜 (t i)) :
    Convex 𝕜 (∑ i ∈ s, t i) :=
  (convexAddSubmonoid 𝕜 E).sum_mem h

theorem Convex.vadd (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 (z +ᵥ s) := by
  simp_rw [← image_vadd, vadd_eq_add, ← singleton_add]
  exact (convex_singleton _).add hs

theorem Convex.translate (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 ((fun x => z + x) '' s) :=
  hs.vadd _

/-- The translation of a convex set is also convex. -/
theorem Convex.translate_preimage_right (hs : Convex 𝕜 s) (z : E) :
    Convex 𝕜 ((fun x => z + x) ⁻¹' s) := by
  intro x hx y hy a b ha hb hab
  have h := hs hx hy ha hb hab
  rwa [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul] at h

/-- The translation of a convex set is also convex. -/
theorem Convex.translate_preimage_left (hs : Convex 𝕜 s) (z : E) :
    Convex 𝕜 ((fun x => x + z) ⁻¹' s) := by
  simpa only [add_comm] using hs.translate_preimage_right z

section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β] [Module 𝕜 β] [PosSMulMono 𝕜 β]

theorem convex_Iic (r : β) : Convex 𝕜 (Iic r) := fun x hx y hy a b ha hb hab =>
  calc
    a • x + b • y ≤ a • r + b • r :=
      add_le_add (smul_le_smul_of_nonneg_left hx ha) (smul_le_smul_of_nonneg_left hy hb)
    _ = r := Convex.combo_self hab _

theorem convex_Ici (r : β) : Convex 𝕜 (Ici r) :=
  convex_Iic (β := βᵒᵈ) r

theorem convex_Icc (r s : β) : Convex 𝕜 (Icc r s) :=
  Ici_inter_Iic.subst ((convex_Ici r).inter <| convex_Iic s)

theorem convex_halfSpace_le {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w ≤ r } :=
  (convex_Iic r).is_linear_preimage h
theorem convex_halfSpace_ge {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | r ≤ f w } :=
  (convex_Ici r).is_linear_preimage h
theorem convex_hyperplane {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w = r } := by
  simp_rw [le_antisymm_iff]
  exact (convex_halfSpace_le h r).inter (convex_halfSpace_ge h r)

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedCancelAddMonoid β]
  [Module 𝕜 β] [PosSMulStrictMono 𝕜 β]

theorem convex_Iio (r : β) : Convex 𝕜 (Iio r) := by
  intro x hx y hy a b ha hb hab
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_add] at hab
    rwa [zero_smul, zero_add, hab, one_smul]
  rw [mem_Iio] at hx hy
  calc
    a • x + b • y < a • r + b • r := add_lt_add_of_lt_of_le
        (smul_lt_smul_of_pos_left hx ha') (smul_le_smul_of_nonneg_left hy.le hb)
    _ = r := Convex.combo_self hab _

theorem convex_Ioi (r : β) : Convex 𝕜 (Ioi r) :=
  convex_Iio (β := βᵒᵈ) r

theorem convex_Ioo (r s : β) : Convex 𝕜 (Ioo r s) :=
  Ioi_inter_Iio.subst ((convex_Ioi r).inter <| convex_Iio s)

theorem convex_Ico (r s : β) : Convex 𝕜 (Ico r s) :=
  Ici_inter_Iio.subst ((convex_Ici r).inter <| convex_Iio s)

theorem convex_Ioc (r s : β) : Convex 𝕜 (Ioc r s) :=
  Ioi_inter_Iic.subst ((convex_Ioi r).inter <| convex_Iic s)

theorem convex_halfSpace_lt {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w < r } :=
  (convex_Iio r).is_linear_preimage h
theorem convex_halfSpace_gt {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | r < f w } :=
  (convex_Ioi r).is_linear_preimage h
end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β] [Module 𝕜 β] [PosSMulMono 𝕜 β]

theorem convex_uIcc (r s : β) : Convex 𝕜 (uIcc r s) :=
  convex_Icc _ _

end LinearOrderedAddCommMonoid

end Module

section IsScalarTower

variable [ZeroLEOneClass 𝕜] [Module 𝕜 E]
variable (R : Type*) [Semiring R] [PartialOrder R] [Module R E]
variable [Module R 𝕜] [IsScalarTower R 𝕜 E]

/-- Lift the convexity of a set up through a scalar tower. -/
theorem Convex.lift [SMulPosMono R 𝕜] {s : Set E} (hs : Convex 𝕜 s) : Convex R s := by
  intro x hx y hy a b ha hb hab
  suffices (a • (1 : 𝕜)) • x + (b • (1 : 𝕜)) • y ∈ s by simpa using this
  refine hs hx hy ?_ ?_ (by simpa [add_smul] using congr($(hab) • (1 : 𝕜)))
  all_goals exact zero_smul R (1 : 𝕜) ▸ smul_le_smul_of_nonneg_right ‹_› zero_le_one

end IsScalarTower

end AddCommMonoid

section LinearOrderedAddCommMonoid

variable [AddCommMonoid E] [LinearOrder E] [IsOrderedAddMonoid E]
  [PartialOrder β] [Module 𝕜 E] [PosSMulMono 𝕜 E]
  {s : Set E} {f : E → β}

theorem MonotoneOn.convex_le (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | f x ≤ r }) := fun x hx y hy _ _ ha hb hab =>
  ⟨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' s hx.1 hy.1) (Convex.combo_le_max x y ha hb hab)).trans
      (max_rec' { x | f x ≤ r } hx.2 hy.2)⟩

theorem MonotoneOn.convex_lt (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | f x < r }) := fun x hx y hy _ _ ha hb hab =>
  ⟨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' s hx.1 hy.1)
          (Convex.combo_le_max x y ha hb hab)).trans_lt
      (max_rec' { x | f x < r } hx.2 hy.2)⟩

theorem MonotoneOn.convex_ge (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | r ≤ f x }) :=
  MonotoneOn.convex_le (E := Eᵒᵈ) (β := βᵒᵈ) hf.dual hs r

theorem MonotoneOn.convex_gt (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | r < f x }) :=
  MonotoneOn.convex_lt (E := Eᵒᵈ) (β := βᵒᵈ) hf.dual hs r

theorem AntitoneOn.convex_le (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | f x ≤ r }) :=
  MonotoneOn.convex_ge (β := βᵒᵈ) hf hs r

theorem AntitoneOn.convex_lt (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | f x < r }) :=
  MonotoneOn.convex_gt (β := βᵒᵈ) hf hs r

theorem AntitoneOn.convex_ge (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | r ≤ f x }) :=
  MonotoneOn.convex_le (β := βᵒᵈ) hf hs r

theorem AntitoneOn.convex_gt (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | r < f x }) :=
  MonotoneOn.convex_lt (β := βᵒᵈ)  hf hs r

theorem Monotone.convex_le (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)

theorem Monotone.convex_lt (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)

theorem Monotone.convex_ge (hf : Monotone f) (r : β) : Convex 𝕜 { x | r ≤ f x } :=
  Set.sep_univ.subst ((hf.monotoneOn univ).convex_ge convex_univ r)

theorem Monotone.convex_gt (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)

theorem Antitone.convex_le (hf : Antitone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.antitoneOn univ).convex_le convex_univ r)

theorem Antitone.convex_lt (hf : Antitone f) (r : β) : Convex 𝕜 { x | f x < r } :=
  Set.sep_univ.subst ((hf.antitoneOn univ).convex_lt convex_univ r)

theorem Antitone.convex_ge (hf : Antitone f) (r : β) : Convex 𝕜 { x | r ≤ f x } :=
  Set.sep_univ.subst ((hf.antitoneOn univ).convex_ge convex_univ r)

theorem Antitone.convex_gt (hf : Antitone f) (r : β) : Convex 𝕜 { x | r < f x } :=
  Set.sep_univ.subst ((hf.antitoneOn univ).convex_gt convex_univ r)

end LinearOrderedAddCommMonoid

end OrderedSemiring

section OrderedCommSemiring

variable [CommSemiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

theorem Convex.smul (hs : Convex 𝕜 s) (c : 𝕜) : Convex 𝕜 (c • s) :=
  hs.linear_image (LinearMap.lsmul _ _ c)

theorem Convex.smul_preimage (hs : Convex 𝕜 s) (c : 𝕜) : Convex 𝕜 ((fun z => c • z) ⁻¹' s) :=
  hs.linear_preimage (LinearMap.lsmul _ _ c)

theorem Convex.affinity (hs : Convex 𝕜 s) (z : E) (c : 𝕜) :
    Convex 𝕜 ((fun x => z + c • x) '' s) := by
  simpa only [← image_smul, ← image_vadd, image_image] using (hs.smul c).vadd z

end AddCommMonoid

end OrderedCommSemiring

section StrictOrderedCommSemiring

variable [CommSemiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

theorem convex_openSegment (a b : E) : Convex 𝕜 (openSegment 𝕜 a b) := by
  rw [convex_iff_openSegment_subset]
  rintro p ⟨ap, bp, hap, hbp, habp, rfl⟩ q ⟨aq, bq, haq, hbq, habq, rfl⟩ z ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨a * ap + b * aq, a * bp + b * bq, by positivity, by positivity, ?_, ?_⟩
  · linear_combination (norm := noncomm_ring) a * habp + b * habq + hab
  · module

end StrictOrderedCommSemiring

section OrderedRing

variable [Ring 𝕜] [PartialOrder 𝕜]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s t : Set E}

@[simp]
theorem convex_vadd (a : E) : Convex 𝕜 (a +ᵥ s) ↔ Convex 𝕜 s :=
  ⟨fun h ↦ by simpa using h.vadd (-a), fun h ↦ h.vadd _⟩

/-- Affine subspaces are convex. -/
theorem AffineSubspace.convex (Q : AffineSubspace 𝕜 E) : Convex 𝕜 (Q : Set E) :=
  fun x hx y hy a b _ _ hab ↦ by simpa [Convex.combo_eq_smul_sub_add hab] using Q.2 _ hy hx hx

/-- The preimage of a convex set under an affine map is convex. -/
theorem Convex.affine_preimage (f : E →ᵃ[𝕜] F) {s : Set F} (hs : Convex 𝕜 s) : Convex 𝕜 (f ⁻¹' s) :=
  fun _ hx => (hs hx).affine_preimage _

/-- The image of a convex set under an affine map is convex. -/
theorem Convex.affine_image (f : E →ᵃ[𝕜] F) (hs : Convex 𝕜 s) : Convex 𝕜 (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  exact (hs hx).affine_image _

theorem Convex.neg (hs : Convex 𝕜 s) : Convex 𝕜 (-s) :=
  hs.is_linear_preimage IsLinearMap.isLinearMap_neg

theorem Convex.sub (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s - t) := by
  rw [sub_eq_add_neg]
  exact hs.add ht.neg

variable [AddRightMono 𝕜]

theorem Convex.add_smul_mem (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : x + y ∈ s) {t : 𝕜}
    (ht : t ∈ Icc (0 : 𝕜) 1) : x + t • y ∈ s := by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by match_scalars <;> noncomm_ring
  rw [h]
  exact hs hx hy (sub_nonneg_of_le ht.2) ht.1 (sub_add_cancel _ _)

theorem Convex.smul_mem_of_zero_mem (hs : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) ∈ s) (hx : x ∈ s)
    {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) : t • x ∈ s := by
  simpa using hs.add_smul_mem zero_mem (by simpa using hx) ht

theorem Convex.mapsTo_lineMap (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    MapsTo (AffineMap.lineMap x y) (Icc (0 : 𝕜) 1) s := by
  simpa only [mapsTo_iff_image_subset, segment_eq_image_lineMap] using h.segment_subset hx hy

theorem Convex.lineMap_mem (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {t : 𝕜}
    (ht : t ∈ Icc 0 1) : AffineMap.lineMap x y t ∈ s :=
  h.mapsTo_lineMap hx hy ht

theorem Convex.add_smul_sub_mem (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {t : 𝕜}
    (ht : t ∈ Icc (0 : 𝕜) 1) : x + t • (y - x) ∈ s := by
  rw [add_comm]
  exact h.lineMap_mem hx hy ht

end AddCommGroup

end OrderedRing

section LinearOrder

variable [Semiring 𝕜] [AddCommMonoid E]
section SemilinearMap

variable [PartialOrder 𝕜]
variable {𝕜' : Type*} [Semiring 𝕜'] [PartialOrder 𝕜']
variable {σ : 𝕜 →+* 𝕜'} [RingHomSurjective σ]
variable {F' : Type*} [AddCommMonoid F'] [Module 𝕜' F'] [Module 𝕜 E]

theorem Convex.semilinear_image {s : Set E} (hs : Convex 𝕜 s) (hσ : ∀ {s t}, σ s ≤ σ t ↔ s ≤ t)
    (f : E →ₛₗ[σ] F') : Convex 𝕜' (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  obtain ⟨r, rfl⟩ : ∃ r : 𝕜, σ r = a := RingHomSurjective.is_surjective ..
  obtain ⟨t, rfl⟩ : ∃ t : 𝕜, σ t = b := RingHomSurjective.is_surjective ..
  refine ⟨r • x + t • y, hs hx hy (by simp_all [(@hσ 0 r).mp]) (by simp_all [(@hσ 0 t).mp])
    ?_, by simp⟩
  apply_fun σ using injective_of_le_imp_le _ hσ.mp
  simpa

end SemilinearMap

variable [LinearOrder 𝕜] [IsOrderedRing 𝕜]

theorem Convex_subadditive_le [SMul 𝕜 E] {f : E → 𝕜} (hf1 : ∀ x y, f (x + y) ≤ (f x) + (f y))
    (hf2 : ∀ ⦃c⦄ x, 0 ≤ c → f (c • x) ≤ c * f x) (B : 𝕜) :
    Convex 𝕜 { x | f x ≤ B } := by
  rw [convex_iff_segment_subset]
  rintro x hx y hy z ⟨a, b, ha, hb, hs, rfl⟩
  calc
    _ ≤ a • (f x) + b • (f y) := le_trans (hf1 _ _) (add_le_add (hf2 x ha) (hf2 y hb))
    _ ≤ a • B + b • B := by gcongr <;> assumption
    _ ≤ B := by rw [← add_smul, hs, one_smul]

end LinearOrder

theorem Convex.midpoint_mem [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Invertible (2 : 𝕜)] {s : Set E} {x y : E}
    (h : Convex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s) : midpoint 𝕜 x y ∈ s :=
  h.segment_subset hx hy <| midpoint_mem_segment x y

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

/-- Alternative definition of set convexity, using division. -/
theorem convex_iff_div :
    Convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
      ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → 0 < a + b → (a / (a + b)) • x + (b / (a + b)) • y ∈ s :=
  forall₂_congr fun _ _ => starConvex_iff_div

theorem Convex.mem_smul_of_zero_mem (h : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) ∈ s) (hx : x ∈ s)
    {t : 𝕜} (ht : 1 ≤ t) : x ∈ t • s := by
  rw [mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans_le ht).ne']
  exact h.smul_mem_of_zero_mem zero_mem hx
    ⟨inv_nonneg.2 (zero_le_one.trans ht), inv_le_one_of_one_le₀ ht⟩

theorem Convex.exists_mem_add_smul_eq (h : Convex 𝕜 s) {x y : E} {p q : 𝕜} (hx : x ∈ s) (hy : y ∈ s)
    (hp : 0 ≤ p) (hq : 0 ≤ q) : ∃ z ∈ s, (p + q) • z = p • x + q • y := by
  rcases _root_.em (p = 0 ∧ q = 0) with (⟨rfl, rfl⟩ | hpq)
  · use x, hx
    simp
  · replace hpq : 0 < p + q :=
      (add_nonneg hp hq).lt_of_ne' (mt (add_eq_zero_iff_of_nonneg hp hq).1 hpq)
    refine ⟨_, convex_iff_div.1 h hx hy hp hq hpq, ?_⟩
    match_scalars <;> field

protected theorem Convex.add_smul (h_conv : Convex 𝕜 s) {p q : 𝕜} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (p + q) • s = p • s + q • s := (add_smul_subset _ _ _).antisymm <| by
  rintro _ ⟨_, ⟨v₁, h₁, rfl⟩, _, ⟨v₂, h₂, rfl⟩, rfl⟩
  exact h_conv.exists_mem_add_smul_eq h₁ h₂ hp hq

end AddCommGroup

end LinearOrderedField

/-!
#### Convex sets in an ordered space
Relates `Convex` and `OrdConnected`.
-/


section

theorem Set.OrdConnected.convex_of_chain [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
    [PartialOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E] {s : Set E}
    (hs : s.OrdConnected) (h : IsChain (· ≤ ·) s) : Convex 𝕜 s := by
  refine convex_iff_segment_subset.mpr fun x hx y hy => ?_
  obtain hxy | hyx := h.total hx hy
  · exact (segment_subset_Icc hxy).trans (hs.out hx hy)
  · rw [segment_symm]
    exact (segment_subset_Icc hyx).trans (hs.out hy hx)

theorem Set.OrdConnected.convex [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [LinearOrder E]
    [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E] {s : Set E} (hs : s.OrdConnected) :
    Convex 𝕜 s :=
  hs.convex_of_chain <| isChain_of_trichotomous s

theorem convex_iff_ordConnected [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜} :
    Convex 𝕜 s ↔ s.OrdConnected := by
  simp_rw [convex_iff_segment_subset, segment_eq_uIcc, ordConnected_iff_uIcc_subset]

alias ⟨Convex.ordConnected, _⟩ := convex_iff_ordConnected

end

/-! #### Convexity of submodules/subspaces -/


namespace Submodule

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]

protected theorem convex (K : Submodule 𝕜 E) : Convex 𝕜 (↑K : Set E) := by
  repeat' intro
  refine add_mem (smul_mem _ _ ?_) (smul_mem _ _ ?_) <;> assumption

protected theorem starConvex (K : Submodule 𝕜 E) : StarConvex 𝕜 (0 : E) K :=
  K.convex K.zero_mem

theorem Convex.semilinear_range {𝕜' : Type*} [Semiring 𝕜'] {σ : 𝕜' →+* 𝕜}
    [RingHomSurjective σ] {F' : Type*} [AddCommMonoid F'] [Module 𝕜' F']
    (f : F' →ₛₗ[σ] E) : Convex 𝕜 (LinearMap.range f : Set E) := Submodule.convex ..

end Submodule

section CommSemiring

variable {R : Type*} [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A]
variable {M : Type*} [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]
variable [PartialOrder R] [PartialOrder A]

lemma convex_of_nonneg_surjective_algebraMap [FaithfulSMul R A] {s : Set M}
    (halg : Set.Ici 0 ⊆ algebraMap R A '' Set.Ici 0) (hs : Convex R s) :
    Convex A s := by
  simp only [Convex, StarConvex] at hs ⊢
  intro u hu v hv a b ha hb hab
  obtain ⟨c, hc1, hc2⟩ := halg ha
  obtain ⟨d, hd1, hd2⟩ := halg hb
  convert hs hu hv hc1 hd1 _ using 2
  · rw [← hc2, algebraMap_smul]
  · rw [← hd2, algebraMap_smul]
  rw [← hc2, ← hd2, ← algebraMap.coe_add] at hab
  exact (FaithfulSMul.algebraMap_eq_one_iff R A).mp hab

end CommSemiring
