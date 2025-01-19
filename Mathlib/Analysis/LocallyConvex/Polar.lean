/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Kalle Kytölä
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.LinearAlgebra.SesquilinearForm
import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual

/-!
# Polar set

In this file we define the polar set. There are different notions of the polar, we will define the
*absolute polar*. The advantage over the real polar is that we can define the absolute polar for
any bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, where `𝕜` is a normed commutative ring and
`E` and `F` are modules over `𝕜`.

## Main definitions

* `LinearMap.polar`: The polar of a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`.

## Main statements

* `LinearMap.polar_eq_iInter`: The polar as an intersection.
* `LinearMap.subset_bipolar`: The polar is a subset of the bipolar.
* `LinearMap.polar_weak_closed`: The polar is closed in the weak topology induced by `B.flip`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

polar
-/

variable {𝕜 E F : Type*}

open Topology

namespace LinearMap

section NormedRing

variable [NormedCommRing 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]


variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- The (absolute) polar of `s : Set E` is given by the set of all `y : F` such that `‖B x y‖ ≤ 1`
for all `x ∈ s`. -/
def polar (s : Set E) : Set F :=
  { y : F | ∀ x ∈ s, ‖B x y‖ ≤ 1 }

theorem polar_mem_iff (s : Set E) (y : F) : y ∈ B.polar s ↔ ∀ x ∈ s, ‖B x y‖ ≤ 1 :=
  Iff.rfl

theorem polar_mem (s : Set E) (y : F) (hy : y ∈ B.polar s) : ∀ x ∈ s, ‖B x y‖ ≤ 1 :=
  hy

theorem polar_preimage (s : Set E) :
    B.polar s = ⋂ x ∈ s, ((B x) ⁻¹' Metric.closedBall (0 : 𝕜) 1) := by aesop

theorem polar_closed (s : Set E) : IsClosed (X :=  WeakBilin B.flip) (B.polar s) := by
  rw [polar_preimage]
  exact isClosed_biInter
    (fun _ _ => IsClosed.preimage (WeakBilin.eval_continuous B.flip _) Metric.isClosed_ball)

theorem bipolar_closed (s : Set E) : IsClosed (X :=  WeakBilin B) (B.flip.polar (B.polar s)) :=
  polar_closed _ _

@[simp]
theorem zero_mem_polar (s : Set E) : (0 : F) ∈ B.polar s := fun _ _ => by
  simp only [map_zero, norm_zero, zero_le_one]

theorem polar_nonempty (s : Set E) : Set.Nonempty (B.polar s) := by
  use 0
  exact zero_mem_polar B s

theorem polar_eq_iInter {s : Set E} : B.polar s = ⋂ x ∈ s, { y : F | ‖B x y‖ ≤ 1 } := by
  ext
  simp only [polar_mem_iff, Set.mem_iInter, Set.mem_setOf_eq]

theorem polar_balanced (s : Set E) : Balanced 𝕜 (B.polar s) := fun a ha y ⟨z,⟨hz₁,hz₂⟩⟩ x hx => by
  rw [← hz₂, map_smul, smul_eq_mul, ← mul_one 1]
  exact le_trans (norm_mul_le _ _)
    (mul_le_mul ha (hz₁ x hx) (norm_nonneg ((B x) z)) (zero_le_one' ℝ))

theorem bipolar_balanced (s : Set E) : Balanced 𝕜 (B.flip.polar (B.polar s)) :=
  polar_balanced B.flip (B.polar s)

/-- The map `B.polar : Set E → Set F` forms an order-reversing Galois connection with
`B.flip.polar : Set F → Set E`. We use `OrderDual.toDual` and `OrderDual.ofDual` to express
that `polar` is order-reversing. -/
theorem polar_gc :
    GaloisConnection (OrderDual.toDual ∘ B.polar) (B.flip.polar ∘ OrderDual.ofDual) := fun _ _ =>
  ⟨fun h _ hx _ hy => h hy _ hx, fun h _ hx _ hy => h hy _ hx⟩

@[simp]
theorem polar_iUnion {ι} {s : ι → Set E} : B.polar (⋃ i, s i) = ⋂ i, B.polar (s i) :=
  B.polar_gc.l_iSup

@[simp]
theorem polar_union {s t : Set E} : B.polar (s ∪ t) = B.polar s ∩ B.polar t :=
  B.polar_gc.l_sup

theorem polar_antitone : Antitone (B.polar : Set E → Set F) :=
  B.polar_gc.monotone_l

@[simp]
theorem polar_empty : B.polar ∅ = Set.univ :=
  B.polar_gc.l_bot

@[simp]
theorem polar_singleton {a : E} : B.polar {a} = { y | ‖B a y‖ ≤ 1 } := le_antisymm
  (fun _ hy => hy _ rfl)
  (fun y hy => (polar_mem_iff _ _ _).mp (fun _ hb => by rw [Set.mem_singleton_iff.mp hb]; exact hy))

theorem mem_polar_singleton {x : E} (y : F) : y ∈ B.polar {x} ↔ ‖B x y‖ ≤ 1 := by
  simp only [polar_singleton, Set.mem_setOf_eq]

theorem polar_zero : B.polar ({0} : Set E) = Set.univ := by
  simp only [polar_singleton, map_zero, zero_apply, norm_zero, zero_le_one, Set.setOf_true]

theorem subset_bipolar (s : Set E) : s ⊆ B.flip.polar (B.polar s) := fun x hx y hy => by
  rw [B.flip_apply]
  exact hy x hx

@[simp]
theorem tripolar_eq_polar (s : Set E) : B.polar (B.flip.polar (B.polar s)) = B.polar s :=
  (B.polar_antitone (B.subset_bipolar s)).antisymm (subset_bipolar B.flip (B.polar s))

/-- The polar set is closed in the weak topology induced by `B.flip`. -/
theorem polar_weak_closed (s : Set E) : IsClosed[WeakBilin.instTopologicalSpace B.flip]
    (B.polar s) := by
  rw [polar_eq_iInter]
  refine isClosed_iInter fun x => isClosed_iInter fun _ => ?_
  exact isClosed_le (WeakBilin.eval_continuous B.flip x).norm continuous_const

theorem sInter_polar_finite_subset_eq_polar (s : Set E) :
    ⋂₀ (B.polar '' { F | F.Finite ∧ F ⊆ s }) = B.polar s := by
  ext x
  simp only [Set.sInter_image, Set.mem_setOf_eq, Set.mem_iInter, and_imp]
  refine ⟨fun hx a ha ↦ ?_, fun hx F _ hF₂ => polar_antitone _ hF₂ hx⟩
  simpa [mem_polar_singleton] using hx _ (Set.finite_singleton a) (Set.singleton_subset_iff.mpr ha)

end NormedRing

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]


variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

theorem polar_univ (h : SeparatingRight B) : B.polar Set.univ = {(0 : F)} := by
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨by simp only [zero_mem_polar], fun y hy => h _ fun x => ?_⟩
  refine norm_le_zero_iff.mp (le_of_forall_le_of_dense fun ε hε => ?_)
  rcases NormedField.exists_norm_lt 𝕜 hε with ⟨c, hc, hcε⟩
  calc
    ‖B x y‖ = ‖c‖ * ‖B (c⁻¹ • x) y‖ := by
      rw [B.map_smul, LinearMap.smul_apply, Algebra.id.smul_eq_mul, norm_mul, norm_inv,
        mul_inv_cancel_left₀ hc.ne']
    _ ≤ ε * 1 := by gcongr; exact hy _ trivial
    _ = ε := mul_one _

theorem polar_subMulAction {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) :
    B.polar m = { y | ∀ x ∈ m, B x y = 0 } := by
  ext y
  constructor
  · intro hy x hx
    obtain ⟨r, hr⟩ := NormedField.exists_lt_norm 𝕜 ‖B x y‖⁻¹
    contrapose! hr
    rw [← one_div, le_div_iff₀ (norm_pos_iff.2 hr)]
    simpa using hy _ (SMulMemClass.smul_mem r hx)
  · intro h x hx
    simp [h x hx]

/-- The polar of a set closed under scalar multiplication as a submodule -/
def polarSubmodule {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) : Submodule 𝕜 F :=
  .copy (⨅ x ∈ m, LinearMap.ker (B x)) (B.polar m) <| by ext; simp [polar_subMulAction]

end NontriviallyNormedField


section polar_convex

variable [RCLike 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (s : Set E)

variable [Module ℝ F] [IsScalarTower ℝ 𝕜 F]

theorem polar_real_convex : Convex ℝ (B.polar s) := fun  x hx y hy a b ha hb hab e he => by
  rw [← hab, map_add, map_smul_of_tower, map_smul_of_tower]
  apply norm_add_le_of_le
  · rw [norm_smul, (Real.norm_of_nonneg ha)]
    exact mul_le_of_le_one_right ha (hx e he)
  · rw [norm_smul, (Real.norm_of_nonneg hb)]
    exact mul_le_of_le_one_right hb (hy e he)

theorem polar_AbsConvex : AbsConvex 𝕜 (B.polar s) := ⟨B.polar_balanced s, polar_real_convex s⟩

end polar_convex

section Bipolar

variable [RCLike 𝕜] [AddCommGroup E] [AddCommGroup F]
variable [Module 𝕜 E] [Module 𝕜 F] [Module ℝ E]

lemma absConvexHull_zero_mem (s : Set E) [Nonempty s] : 0 ∈ absConvexHull 𝕜 s := by
  rename_i inst_3
  simp_all only [nonempty_subtype]
  obtain ⟨w, h⟩ := inst_3
  have e1 : w ∈ (absConvexHull 𝕜 s) := mem_absConvexHull_iff.mpr fun t a a_1 ↦ a h
  have e3 : Balanced 𝕜 (absConvexHull 𝕜 s) := by exact balanced_absConvexHull
  have e2 : -w ∈ (absConvexHull 𝕜 s) := by
    rw [Balanced.neg_mem_iff e3]
    exact e1
  have e4 : (1/2 : ℝ) • w + (1/2 : ℝ) • (-w) ∈ (absConvexHull 𝕜 s) := by
    apply convex_absConvexHull e1 e2
    simp only [one_div, inv_nonneg, Nat.ofNat_nonneg]
    simp only [one_div, inv_nonneg, Nat.ofNat_nonneg]
    exact add_halves 1
  simp at e4
  exact e4

variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (s : Set E)
variable  [IsScalarTower ℝ 𝕜 E]

theorem bipolar_convex : Convex ℝ (B.flip.polar (B.polar s)) :=
  polar_real_convex (B.polar s)

theorem bipolar_absConvex : AbsConvex 𝕜 (B.flip.polar (B.polar s)) :=
  polar_AbsConvex (B.polar s)



open scoped ComplexOrder
theorem Bipolar {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {s : Set E} [Nonempty s] :
    B.flip.polar (B.polar s) = closedAbsConvexHull (E := WeakBilin B) 𝕜 s := by
  apply le_antisymm
  · simp only [Set.le_eq_subset]
    rw [← Set.compl_subset_compl]
    intro x hx
    rw [Set.mem_compl_iff] at hx
    have e1 : Convex ℝ (closedAbsConvexHull (E := WeakBilin B) 𝕜 s) := absConvex_convexClosedHull.2
    have e2 : IsClosed (closedAbsConvexHull (E := WeakBilin B) 𝕜 s) := isClosed_closedAbsConvexHull
    obtain ⟨f,⟨u,⟨hf₁,hf₂⟩⟩⟩ :=
      RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) (E := WeakBilin B) e1 e2 hx
    have e3 : RCLike.re (f 0) < u := by
      apply (hf₁ 0)
      apply absConvexHull_subset_closedAbsConvexHull
      exact absConvexHull_zero_mem s
    simp at e3
    let g := (1/u : ℝ) • f
    have fg : g = (1/u : ℝ) • f := rfl
    have hg₁ : ∀ a ∈ (closedAbsConvexHull (E := WeakBilin B) 𝕜) s, RCLike.re (g a) < 1 := by
      intro a ha
      rw [fg]
      simp only [ ContinuousLinearMap.coe_smul', Pi.smul_apply]
      rw [RCLike.smul_re]
      have t1 : RCLike.re (f a) < u := by exact hf₁ a ha
      simp [t1]
      have u0 : u ≠ 0 := by
        simp [e3]
        rename_i inst_7
        simp_all only [nonempty_subtype, one_div, g]
        obtain ⟨w, h⟩ := inst_7
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        subst a_1
        simp_all only [lt_self_iff_false]
      have u1 : u⁻¹ * u = 1 := by
        simp_all only [nonempty_subtype, one_div, ne_eq, not_false_eq_true, inv_mul_cancel₀, g]
      rw [← u1]
      apply mul_lt_mul_of_pos_left
      apply (hf₁ a)
      exact ha


      sorry
    sorry

  · exact closedAbsConvexHull_min (subset_bipolar B s) (bipolar_absConvex s) (bipolar_closed B s)

end Bipolar

end LinearMap
