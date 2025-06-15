/-
Copyright (c) 2021 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection

/-!
# Convex cones in inner product spaces

We define `Set.innerDualCone` to be the cone consisting of all points `y` such that for
all points `x` in a given set `0 ≤ ⟪ x, y ⟫`.

## Main statements

We prove the following theorems:
* `ConvexCone.innerDualCone_of_innerDualCone_eq_self`:
  The `innerDualCone` of the `innerDualCone` of a nonempty, closed, convex cone is itself.
* `ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem`:
  This variant of the
  [hyperplane separation theorem](https://en.wikipedia.org/wiki/Hyperplane_separation_theorem)
  states that given a nonempty, closed, convex cone `K` in a complete, real inner product space `H`
  and a point `b` disjoint from it, there is a vector `y` which separates `b` from `K` in the sense
  that for all points `x` in `K`, `0 ≤ ⟪x, y⟫_ℝ` and `⟪y, b⟫_ℝ < 0`. This is also a geometric
  interpretation of the
  [Farkas lemma](https://en.wikipedia.org/wiki/Farkas%27_lemma#Geometric_interpretation).
-/

open Set LinearMap Pointwise

/-! ### The dual cone -/


section Dual

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (s t : Set H)

open RealInnerProductSpace

/-- The dual cone is the cone consisting of all points `y` such that for
all points `x` in a given set `0 ≤ ⟪ x, y ⟫`. -/
def Set.innerDualCone (s : Set H) : ConvexCone ℝ H where
  carrier := { y | ∀ x ∈ s, 0 ≤ ⟪x, y⟫ }
  smul_mem' c hc y hy x hx := by
    rw [real_inner_smul_right]
    exact mul_nonneg hc.le (hy x hx)
  add_mem' u hu v hv x hx := by
    rw [inner_add_right]
    exact add_nonneg (hu x hx) (hv x hx)

@[simp]
theorem mem_innerDualCone (y : H) (s : Set H) : y ∈ s.innerDualCone ↔ ∀ x ∈ s, 0 ≤ ⟪x, y⟫ :=
  Iff.rfl

@[simp]
theorem innerDualCone_empty : (∅ : Set H).innerDualCone = ⊤ :=
  eq_top_iff.mpr fun _ _ _ => False.elim

/-- Dual cone of the convex cone {0} is the total space. -/
@[simp]
theorem innerDualCone_zero : (0 : Set H).innerDualCone = ⊤ :=
  eq_top_iff.mpr fun _ _ y (hy : y = 0) => hy.symm ▸ (inner_zero_left _).ge

/-- Dual cone of the total space is the convex cone {0}. -/
@[simp]
theorem innerDualCone_univ : (univ : Set H).innerDualCone = 0 := by
  suffices ∀ x : H, x ∈ (univ : Set H).innerDualCone → x = 0 by
    apply SetLike.coe_injective
    exact eq_singleton_iff_unique_mem.mpr ⟨fun x _ => (inner_zero_right _).ge, this⟩
  exact fun x hx => by simpa [← real_inner_self_nonpos] using hx (-x) (mem_univ _)

variable {s t} in
@[gcongr]
theorem innerDualCone_le_innerDualCone (h : t ⊆ s) : s.innerDualCone ≤ t.innerDualCone :=
  fun _ hy x hx => hy x (h hx)

theorem pointed_innerDualCone : s.innerDualCone.Pointed := fun x _ => by rw [inner_zero_right]

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `fun y ↦ ⟪x, y⟫`. -/
theorem innerDualCone_singleton (x : H) :
    ({x} : Set H).innerDualCone = (ConvexCone.positive ℝ ℝ).comap (innerₛₗ ℝ x) :=
  ConvexCone.ext fun _ => forall_eq

theorem innerDualCone_union (s t : Set H) :
    (s ∪ t).innerDualCone = s.innerDualCone ⊓ t.innerDualCone :=
  le_antisymm (le_inf (fun _ hx _ hy => hx _ <| Or.inl hy) fun _ hx _ hy => hx _ <| Or.inr hy)
    fun _ hx _ => Or.rec (hx.1 _) (hx.2 _)

theorem innerDualCone_insert (x : H) (s : Set H) :
    (insert x s).innerDualCone = Set.innerDualCone {x} ⊓ s.innerDualCone := by
  rw [insert_eq, innerDualCone_union]

theorem innerDualCone_iUnion {ι : Sort*} (f : ι → Set H) :
    (⋃ i, f i).innerDualCone = ⨅ i, (f i).innerDualCone := by
  refine le_antisymm (le_iInf fun i x hx y hy => hx _ <| mem_iUnion_of_mem _ hy) ?_
  intro x hx y hy
  rw [ConvexCone.mem_iInf] at hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hy
  exact hx _ _ hj

theorem innerDualCone_sUnion (S : Set (Set H)) :
    (⋃₀ S).innerDualCone = sInf (Set.innerDualCone '' S) := by
  simp_rw [sInf_image, sUnion_eq_biUnion, innerDualCone_iUnion]

/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
theorem innerDualCone_eq_iInter_innerDualCone_singleton :
    (s.innerDualCone : Set H) = ⋂ i : s, (({↑i} : Set H).innerDualCone : Set H) := by
  rw [← ConvexCone.coe_iInf, ← innerDualCone_iUnion, iUnion_of_singleton_coe]

theorem isClosed_innerDualCone : IsClosed (s.innerDualCone : Set H) := by
  -- reduce the problem to showing that dual cone of a singleton `{x}` is closed
  rw [innerDualCone_eq_iInter_innerDualCone_singleton]
  apply isClosed_iInter
  intro x
  -- the dual cone of a singleton `{x}` is the preimage of `[0, ∞)` under `inner x`
  have h : ({↑x} : Set H).innerDualCone = (inner ℝ (x : H)) ⁻¹' Set.Ici 0 := by
    rw [innerDualCone_singleton, ConvexCone.coe_comap, ConvexCone.coe_positive, innerₛₗ_apply_coe]
  -- the preimage is closed as `inner x` is continuous and `[0, ∞)` is closed
  rw [h]
  exact isClosed_Ici.preimage (continuous_const.inner continuous_id')

theorem ConvexCone.pointed_of_nonempty_of_isClosed (K : ConvexCone ℝ H) (ne : (K : Set H).Nonempty)
    (hc : IsClosed (K : Set H)) : K.Pointed := by
  obtain ⟨x, hx⟩ := ne
  let f : ℝ → H := (· • x)
  -- f (0, ∞) is a subset of K
  have fI : f '' Set.Ioi 0 ⊆ (K : Set H) := by
    rintro _ ⟨_, h, rfl⟩
    exact K.smul_mem (Set.mem_Ioi.1 h) hx
  -- closure of f (0, ∞) is a subset of K
  have clf : closure (f '' Set.Ioi 0) ⊆ (K : Set H) := hc.closure_subset_iff.2 fI
  -- f is continuous at 0 from the right
  have fc : ContinuousWithinAt f (Set.Ioi (0 : ℝ)) 0 :=
    (continuous_id.smul continuous_const).continuousWithinAt
  -- 0 belongs to the closure of the f (0, ∞)
  have mem₀ := fc.mem_closure_image (by rw [closure_Ioi (0 : ℝ), mem_Ici])
  -- as 0 ∈ closure f (0, ∞) and closure f (0, ∞) ⊆ K, 0 ∈ K.
  have f₀ : f 0 = 0 := zero_smul ℝ x
  simpa only [f₀, ConvexCone.Pointed, ← SetLike.mem_coe] using mem_of_subset_of_mem clf mem₀

namespace PointedCone

/-- The inner dual cone of a pointed cone is a pointed cone. -/
def dual (C : PointedCone ℝ H) : PointedCone ℝ H :=
  ((C : Set H).innerDualCone).toPointedCone <| pointed_innerDualCone (C : Set H)

@[simp, norm_cast]
lemma toConvexCone_dual (C : PointedCone ℝ H) : ↑(dual C) = (C : Set H).innerDualCone := rfl

open InnerProductSpace in
@[simp]
lemma mem_dual {C : PointedCone ℝ H} {y : H} : y ∈ dual C ↔ ∀ ⦃x⦄, x ∈ C → 0 ≤ ⟪x, y⟫_ℝ := .rfl

end PointedCone

namespace ProperCone

/-- The inner dual cone of a proper cone is a proper cone. -/
def dual (C : ProperCone ℝ H) : ProperCone ℝ H where
  toSubmodule := PointedCone.dual (C : PointedCone ℝ H)
  isClosed' := isClosed_innerDualCone _

@[simp, norm_cast]
lemma coe_dual (C : ProperCone ℝ H) : C.dual = (C : Set H).innerDualCone := rfl

open scoped InnerProductSpace in
@[simp]
lemma mem_dual {C : ProperCone ℝ H} {y : H} : y ∈ dual C ↔ ∀ ⦃x⦄, x ∈ C → 0 ≤ ⟪x, y⟫_ℝ := .rfl

end ProperCone

section CompleteSpace

variable [CompleteSpace H]

open scoped InnerProductSpace in
/-- This is a stronger version of the Hahn-Banach separation theorem for closed convex cones. This
is also the geometric interpretation of Farkas' lemma. -/
theorem ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem (K : ConvexCone ℝ H)
    (ne : (K : Set H).Nonempty) (hc : IsClosed (K : Set H)) {b : H} (disj : b ∉ K) :
    ∃ y : H, (∀ x : H, x ∈ K → 0 ≤ ⟪x, y⟫_ℝ) ∧ ⟪y, b⟫_ℝ < 0 := by
  -- let `z` be the point in `K` closest to `b`
  obtain ⟨z, hzK, infi⟩ := exists_norm_eq_iInf_of_complete_convex ne hc.isComplete K.convex b
  -- for any `w` in `K`, we have `⟪b - z, w - z⟫_ℝ ≤ 0`
  have hinner := (norm_eq_iInf_iff_real_inner_le_zero K.convex hzK).1 infi
  -- set `y := z - b`
  use z - b
  constructor
  · -- the rest of the proof is a straightforward calculation
    rintro x hxK
    specialize hinner _ (K.add_mem hxK hzK)
    rwa [add_sub_cancel_right, real_inner_comm, ← neg_nonneg, neg_eq_neg_one_mul,
      ← real_inner_smul_right, neg_smul, one_smul, neg_sub] at hinner
  · -- as `K` is closed and non-empty, it is pointed
    have hinner₀ := hinner 0 (K.pointed_of_nonempty_of_isClosed ne hc)
    -- the rest of the proof is a straightforward calculation
    rw [zero_sub, inner_neg_right, Right.neg_nonpos_iff] at hinner₀
    have hbz : b - z ≠ 0 := by
      rw [sub_ne_zero]
      contrapose! hzK
      rwa [← hzK]
    rw [← neg_zero, lt_neg, ← neg_one_mul, ← real_inner_smul_left, smul_sub, neg_smul, one_smul,
      neg_smul, neg_sub_neg, one_smul]
    calc
      0 < ⟪b - z, b - z⟫_ℝ := lt_of_not_ge ((Iff.not real_inner_self_nonpos).2 hbz)
      _ = ⟪b - z, b - z⟫_ℝ + 0 := (add_zero _).symm
      _ ≤ ⟪b - z, b - z⟫_ℝ + ⟪b - z, z⟫_ℝ := add_le_add rfl.ge hinner₀
      _ = ⟪b - z, b - z + z⟫_ℝ := (inner_add_right _ _ _).symm
      _ = ⟪b - z, b⟫_ℝ := by rw [sub_add_cancel]

@[deprecated (since := "2025-05-24")]
alias ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_nmem :=
  ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem

/-- The inner dual of inner dual of a non-empty, closed convex cone is itself. -/
theorem ConvexCone.innerDualCone_of_innerDualCone_eq_self (K : ConvexCone ℝ H)
    (ne : (K : Set H).Nonempty) (hc : IsClosed (K : Set H)) :
    ((K : Set H).innerDualCone : Set H).innerDualCone = K := by
  ext x
  constructor
  · rw [mem_innerDualCone, ← SetLike.mem_coe]
    contrapose!
    exact K.hyperplane_separation_of_nonempty_of_isClosed_of_notMem ne hc
  · rintro hxK y h
    specialize h x hxK
    rwa [real_inner_comm]

namespace ProperCone
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The dual of the dual of a proper cone is itself. -/
@[simp]
theorem dual_dual (K : ProperCone ℝ H) : K.dual.dual = K :=
  ProperCone.toPointedCone_injective <| PointedCone.toConvexCone_injective <|
    (K : ConvexCone ℝ H).innerDualCone_of_innerDualCone_eq_self K.nonempty K.isClosed

variable [CompleteSpace F]

open scoped InnerProductSpace

/-- This is a relative version of
`ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem`, which we recover by setting
`f` to be the identity map. This is also a geometric interpretation of the Farkas' lemma
stated using proper cones. -/
theorem hyperplane_separation (K : ProperCone ℝ H) {f : H →L[ℝ] F} {b : F} :
    b ∈ K.map f ↔ ∀ y : F, f.adjoint y ∈ K.dual → 0 ≤ ⟪y, b⟫_ℝ where
  mp := by
    -- suppose `b ∈ K.map f`
    simp only [mem_map, PointedCone.mem_closure, PointedCone.coe_map, ContinuousLinearMap.coe_coe,
      mem_closure_iff_seq_limit, mem_image, SetLike.mem_coe, mem_dual,
      ContinuousLinearMap.adjoint_inner_right, forall_exists_index, and_imp]
    -- there is a sequence `seq : ℕ → F` in the image of `f` that converges to `b`
    rintro seq hmem htends y hinner
    suffices h : ∀ n, 0 ≤ ⟪y, seq n⟫_ℝ from
      ge_of_tendsto' (Continuous.seqContinuous (Continuous.inner (@continuous_const _ _ _ _ y)
        continuous_id) htends) h
    intro n
    obtain ⟨_, h, hseq⟩ := hmem n
    simpa only [← hseq, real_inner_comm] using hinner h
  mpr := by
    -- proof by contradiction
    -- suppose `b ∉ K.map f`
    intro h
    contrapose! h
    -- as `b ∉ K.map f`, there is a hyperplane `y` separating `b` from `K.map f`
    let C := PointedCone.toConvexCone (𝕜 := ℝ) (E := F) (K.map f)
    obtain ⟨y, hxy, hyb⟩ :=
      @ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem
      _ _ _ _ C (K.map f).nonempty (K.map f).isClosed b h
    -- the rest of the proof is a straightforward algebraic manipulation
    refine ⟨y, ?_, hyb⟩
    simp only [mem_dual, ContinuousLinearMap.adjoint_inner_right]
    intro x hxK
    exact hxy (f x) <| subset_closure <| Set.mem_image_of_mem _ hxK

theorem hyperplane_separation_of_notMem (K : ProperCone ℝ H) {f : H →L[ℝ] F} {b : F}
    (disj : b ∉ K.map f) : ∃ y : F, ContinuousLinearMap.adjoint f y ∈ K.dual ∧ ⟪y, b⟫_ℝ < 0 := by
  contrapose! disj; rwa [K.hyperplane_separation]

@[deprecated (since := "2025-05-24")]
alias hyperplane_separation_of_nmem := hyperplane_separation_of_notMem

end ProperCone

end CompleteSpace

end Dual
